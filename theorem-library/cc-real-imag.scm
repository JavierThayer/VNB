;;; cc-real-imag.scm -- the real and imaginary parts of a complex number.
;;;
;;; WHAT WAS MISSING.  `real-part' and `imag-part' were REGISTERED HEADS WITH NO
;;; AXIOM AT ALL: wff.scm:366 lists them among the term-form heads,
;;; interactive.scm:1690 advertises them as "CC -> RR", arith-eval.scm:111-118
;;; evaluates them on ground literals -- and the theory said nothing whatever
;;; about them.  A symbolic `real-part(z)' was an uninterpreted application: not
;;; unsound, inert.  Nothing could be proved about it, in either direction.
;;;
;;; number-systems.scm now carries the two DEFINITIONS
;;;
;;;     real-part(z)  ==  (z + conj z) * recip 2
;;;     imag-part(z)  ==  (z - conj z) * recip (2i)
;;;
;;; which need no new assumption: the CC layer was already pinned by
;;; cc-generated-by-rr (every complex is x + y i with x, y real) together with
;;; cc-conjugate-add / -mul / -fixes-rr / -i (which determine conjugation on all
;;; of CC).  This file proves what a user needs from them.
;;;
;;; THE MECHANISM.  All three proofs share ONE driver, `ci-decompose!', which is
;;; the whole content of the file:
;;;
;;;   * cc-generated-by-rr gives z = x + y i for eigenvariables x, y in RR;
;;;   * conjugation is COMPUTED at that form -- conj(x + y i) = x + y(-i) -- by
;;;     five rewrites, each one an axiom instance (add, mul, fixes-rr twice, i);
;;;   * hence z + conj z = 2x and z - conj z = (2i) y, both by `crs';
;;;   * and the two recip cancellations, (2x)(recip 2) = x and ((2i)y)(recip 2i)
;;;     = y, each by `crs' on the associativity plus rr-/cc-recip-inverse.
;;;
;;; It returns the equations `real-part(z) unfolded = x' and `... = y', so each
;;; theorem below is that driver, one `mac' of the definition, one `subst' and
;;; an `ass'.
;;;
;;; TWO TRAPS worth recording, both of which cost a run:
;;;
;;;   * `crs' certifies its generators from the CONTEXT, and reads `(IN x CC)',
;;;     not `(AND (IN x CC) (IN y CC))'.  A conjunctive typing hypothesis has to
;;;     be `ai'-ed apart first or the oracle reports "not a provable
;;;     commutative-ring identity" about a goal that is one.  (It does know the
;;;     imaginary unit: `+i' is an exact Scheme complex to cvnb->poly, so
;;;     y*i + y*(-i) cancels in the coefficient arithmetic.)
;;;   * `rfl' will NOT close (= t t) for an arithmetic t -- `=' is partial, so
;;;     `t = t' IS the definedness assertion, and pi-reflexivity! demands either
;;;     a syntactically total term or a context typing.  Hence the three closure
;;;     citations that type x + y(-i) in CC before the conjugate equation is
;;;     established.

;;; --------------------------------------------------------------------
;;; File-local driver helpers (the `ci-' prefix).

;;; Peel the whole FORALL/IMPLIES prefix -- and STOP there.  `di' is greedy, and
;;; the next call on the AND goal of cc-re-im-of would SPLIT it, running the
;;; computation in one branch only.
(define (ci-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (ci-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 12)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (ci-fvs) (apply append (map free-vars (dk-asms))))

;;; Eliminate the existential ALREADY in context and return its eigenvariable,
;;; named by free-variable difference -- `obtain' (sketch.scm) does the same job
;;; but only for an existential its LANE just landed, and cc-generated-by-rr is
;;; a nested pair of them: the second is in context before the second call.
(define (ci-obtain-here!)
  (let ((ex  (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (dk-asms)))
        (fv0 (ci-fvs)))
    (if (not ex) (error "ci-obtain-here!: no existential in context"))
    (ai ex)
    (ci-split!)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (ci-fvs))))
      (if (null? fresh) (error "ci-obtain-here!: no eigenvariable appeared"))
      (car fresh))))

;;; THE COMPUTATION.  Requires (IN z CC), (IN CX RR), (IN CY RR) and
;;; (= z (+ CX (* CY +i))) in context; lands (= real-part(z) CX) and
;;; (= imag-part(z) CY) and returns them.
(define (ci-core! cx cy)
  (let* ((zeq   (list '= 'z (list '+ cx (list '* cy '+i))))
         (cjz   (list '= '(conjugate z) (list '+ cx (list '* cy '(- +i)))))
         (sum   (list '= '(+ z (conjugate z)) (list '* 2 cx)))
         (dif   (list '= '(- z (conjugate z)) (list '* '(* 2 +i) cy)))
         (re    (list '= '(* (+ z (conjugate z)) (recip 2)) cx))
         (im    (list '= '(* (- z (conjugate z)) (recip (* 2 +i))) cy)))
    ;; the pieces of z, typed in CC
    (fact 'rr-subset-cc cx)
    (fact 'rr-subset-cc cy)
    (fact 'cc-i-in)
    (have! (list 'AND (list 'IN cy 'CC) '(IN +i CC)))
    (fact 'cc-mul-closed cy '+i)
    (have! (list 'AND (list 'IN cx 'CC) (list 'IN (list '* cy '+i) 'CC)))
    ;; ... and the conjugate's value, which `rfl' needs typed (partial `=')
    (fact 'cc-neg-closed '+i)
    (have! (list 'AND (list 'IN cy 'CC) '(IN (- +i) CC)))
    (fact 'cc-mul-closed cy '(- +i))
    (have! (list 'AND (list 'IN cx 'CC) (list 'IN (list '* cy '(- +i)) 'CC)))
    (fact 'cc-add-closed cx (list '* cy '(- +i)))
    ;; conjugation COMPUTED at x + y i: five axiom instances, five rewrites.
    (fact 'cc-conjugate-add cx (list '* cy '+i))
    (fact 'cc-conjugate-mul cy '+i)
    (fact 'cc-conjugate-fixes-rr cx)
    (fact 'cc-conjugate-fixes-rr cy)
    (fact 'cc-conjugate-i)
    (have! cjz
      (lambda ()
        (subst zeq)
        (subst (list '= (list 'conjugate (list '+ cx (list '* cy '+i)))
                        (list '+ (list 'conjugate cx) (list 'conjugate (list '* cy '+i)))))
        (subst (list '= (list 'conjugate (list '* cy '+i))
                        (list '* (list 'conjugate cy) '(conjugate +i))))
        (subst (list '= (list 'conjugate cx) cx))
        (subst (list '= (list 'conjugate cy) cy))
        (subst '(= (conjugate +i) (- +i)))
        (rfl)))
    ;; z + conj z = 2x  and  z - conj z = (2i) y
    (have! sum (lambda () (subst cjz) (subst zeq) (crs)))
    (have! dif (lambda () (subst cjz) (subst zeq) (crs)))
    ;; the two units to divide by, and their inverses
    (have! '(IN 2 RR))
    (have! '(NOT (= 2 0)) (lambda () (arith)))
    (have! '(AND (IN 2 RR) (NOT (= 2 0))))
    (fact 'rr-recip-inverse 2)
    (fact 'rr-recip-closed 2)
    (have! '(IN (* 2 +i) CC) (lambda () (arith)))
    (have! '(NOT (= (* 2 +i) 0)) (lambda () (arith)))
    (have! '(AND (IN (* 2 +i) CC) (NOT (= (* 2 +i) 0))))
    (fact 'cc-recip-inverse '(* 2 +i))
    (fact 'cc-recip-closed '(* 2 +i))
    ;; ... hence the two projection values
    (have! re
      (lambda ()
        (subst sum)
        (let ((assoc-eq (list '= (list '* (list '* 2 cx) '(recip 2))
                                 (list '* cx '(* 2 (recip 2))))))
          (have! assoc-eq (lambda () (crs)))
          (subst assoc-eq))
        (subst '(= (* 2 (recip 2)) 1))
        (crs)))
    (have! im
      (lambda ()
        (subst dif)
        (let ((assoc-eq (list '= (list '* (list '* '(* 2 +i) cy) '(recip (* 2 +i)))
                                 (list '* cy '(* (* 2 +i) (recip (* 2 +i)))))))
          (have! assoc-eq (lambda () (crs)))
          (subst assoc-eq))
        (subst '(= (* (* 2 +i) (recip (* 2 +i))) 1))
        (crs)))
    ;; ... which are the projections, once the definitions are unfolded
    (let ((reval (list '= '(real-part z) cx))
          (imval (list '= '(imag-part z) cy)))
      (have! reval (lambda () (mac 'real-part-def) (subst re) (rfl)))
      (have! imval (lambda () (mac 'imag-part-def) (subst im) (rfl)))
      (list reval imval))))

;;; Requires (IN z CC).  Produces the coordinates from cc-generated-by-rr and
;;; lands (= real-part(z) X), (= imag-part(z) Y); returns (list X Y).
(define (ci-witnesses!)
  (fact 'cc-generated-by-rr 'z)
  (let* ((cx (ci-obtain-here!))
         (cy (ci-obtain-here!)))
    (fact 'cc-re-im-of 'z cx cy)
    (ci-split!)
    (list cx cy)))

;;; --------------------------------------------------------------------
;;; THE UNIQUENESS LEMMA -- the whole content of the file.
;;;
;;; cc-generated-by-rr says the coordinates EXIST; this says the two definitions
;;; RECOVER them, which is what makes them the real and imaginary parts rather
;;; than two arbitrary maps.  Everything else here, and every magnitude fact in
;;; theorem-library/cc-magnitude.scm, is this lemma at a particular z: at a sum,
;;; at a product, at a negation, at a real number.
;;;
;;; Stated CURRIED (four separate guards, no AND antecedent) so `fact' discharges
;;; each from context in one call.

(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
     (FORALL a (IMPLIES (IN a RR)
     (FORALL b (IMPLIES (IN b RR)
       (IMPLIES (= z (+ a (* b +i)))
                (AND (= (real-part z) a) (= (imag-part z) b)))))))))))
(ci-peel!)
(ci-core! 'a 'b)
(for-each (lambda (k) (dk-focus! k) (ass)) (dk-opened (lambda () (di))))
(qed 'cc-re-im-of)
(topic! 'cc-re-im-of 'algebra)

;;; --------------------------------------------------------------------
;;; The projections are REAL.  This is the statement interactive.scm has been
;;; advertising as the type of the two heads ("CC -> RR") with nothing behind it.
;;;
;;; Both proofs are the same three moves: cc-generated-by-rr produces the
;;; coordinates, cc-re-im-of identifies the projection with one of them, and the
;;; typing comes off that coordinate.

(sp (make-wff '(FORALL z (IMPLIES (IN z CC) (IN (real-part z) RR)))))
(di)
(let ((cx (ci-witnesses!)))
  (subst (list '= '(real-part z) (car cx)))
  (ass))
(qed 'real-part-in-rr)
(topic! 'real-part-in-rr 'algebra)

(sp (make-wff '(FORALL z (IMPLIES (IN z CC) (IN (imag-part z) RR)))))
(di)
(let ((cx (ci-witnesses!)))
  (subst (list '= '(imag-part z) (cadr cx)))
  (ass))
(qed 'imag-part-in-rr)
(topic! 'imag-part-in-rr 'algebra)

;;; --------------------------------------------------------------------
;;; ... and they DECOMPOSE z.

(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
      (= z (+ (real-part z) (* +i (imag-part z))))))))
(di)
(let* ((w  (ci-witnesses!))
       (cx (car w)) (cy (cadr w)))
  (subst (list '= '(real-part z) cx))
  (subst (list '= '(imag-part z) cy))
  (subst (list '= 'z (list '+ cx (list '* cy '+i))))
  (crs))
(qed 'cc-re-im-decompose)
(topic! 'cc-re-im-decompose 'algebra)

;;; --------------------------------------------------------------------
;;; TWO CONSEQUENCES THE INNER-PRODUCT INEQUALITIES NEED (added 2026-08-18).
;;;
;;; theorem-library/inner-product-inequalities.scm has to get from the COMPLEX
;;; cross term <x,y> + conj<x,y> of an expanded ||x+y||^2 to something the real
;;; order calculus can handle.  Both facts below do that, and both are stated so
;;; that what survives is `real-part', whose realness IS a theorem
;;; (real-part-in-rr above) -- which matters because `ineq' certifies an atom
;;; only from an (IN t RR) in context (ineq-atom-rr-ok?, ineq-oracle.scm:112).
;;; Written as z + conj z, the cross term decomposes into the two atoms z and
;;; conj z, NEITHER of which is real, and the oracle refuses the whole call.
;;;
;;; Both proofs are ci-core! at the coordinates and one substitution: the
;;; equations z + conj z = 2x and conj z = x + y(-i) are what that driver lands
;;; on its way to the projections, so nothing new is computed here.

;;; The 1-based index of a context formula, which is what `ineq' wants: a bare
;;; (ineq) names NO premises at all (cmd-ineq passes idxs through unchanged,
;;; proof-commands.scm:717) and so closes only goals true outright.
(define (ci-idx-of f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ci-idx-of: not in context" f))
          ((equal? (car l) f) i)
          (else (loop (cdr l) (+ i 1))))))

;;; z + conj z = 2 Re(z).
(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
      (= (+ z (conjugate z)) (* 2 (real-part z)))))))
(di)
(fact 'cc-generated-by-rr 'z)
(let* ((cx (ci-obtain-here!)) (cy (ci-obtain-here!)))
  (let ((r (ci-core! cx cy)))
    (subst (car r))
    (ass)))
(qed 'cc-plus-conj-is-2re)
(topic! 'cc-plus-conj-is-2re 'algebra)
(alias! 'cc-plus-conj-is-2re "a complex number plus its conjugate is twice its real part")

;;; Re(z)^2 <= z conj z.  (The right side is |z|^2; stating it as the product
;;; keeps the fact independent of `magnitude', hence of SQRT.)
(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
      (<= (* (real-part z) (real-part z)) (* z (conjugate z)))))))
(di)
(fact 'cc-generated-by-rr 'z)
(let* ((cx (ci-obtain-here!)) (cy (ci-obtain-here!)))
  (let ((r    (ci-core! cx cy))
        (zeq  (list '= 'z (list '+ cx (list '* cy '+i))))
        (cjz  (list '= '(conjugate z) (list '+ cx (list '* cy '(- +i)))))
        (modq (list '= '(* z (conjugate z))
                    (list '+ (list '* cx cx) (list '* cy cy)))))
    (have! modq (lambda () (subst cjz) (subst zeq) (crs)))
    (have! (list 'AND (list 'IN cx 'RR) (list 'IN cx 'RR)))
    (fact 'rr-mul-closed cx cx)
    (have! (list 'AND (list 'IN cy 'RR) (list 'IN cy 'RR)))
    (fact 'rr-mul-closed cy cy)
    (fact 'rr-sq-nonneg cy)
    (subst (car r))
    (subst modq)
    (ineq (ci-idx-of (list '<= 0 (list '* cy cy))))))
(qed 'cc-re-sq-le-mod-sq)
(topic! 'cc-re-sq-le-mod-sq 'inequalities)
(alias! 'cc-re-sq-le-mod-sq "the square of the real part is at most the squared modulus")
