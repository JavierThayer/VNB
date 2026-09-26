;;; cc-complete-proof.scm -- CC IS A COMPLETE METRIC SPACE.
;;;
;;;     IS-COMPLETE(CC-MS)
;;;
;;; This was a bare `add-axiom!' in structure-library/complex.scm with no
;;; `warrant!' of any kind, i.e. `trust: none' -- the weakest report a bill can
;;; carry -- for a fact that is two coordinates of `rr-complete'
;;; (theorem-library/rr-complete-proof.scm), which has been PROVEN since
;;; 2026-08-02.  The reals' completeness was earned and the complexes' was
;;; assumed.
;;;
;;; THE ROUTE.  Coordinatewise, and nothing else:
;;;
;;;   1. |Re w| <= |w| and |Im w| <= |w|          (cc-abs-re/im-le-magnitude)
;;;   2. Re(z - w) = Re z - Re w, likewise Im     (cc-re-sub, cc-im-sub)
;;;   3. so the real and imaginary parts of a Cauchy sequence are Cauchy in RR,
;;;      each converges by rr-complete, and
;;;   4. |w| <= |Re w| + |Im w|                   (cc-magnitude-le-re-im)
;;;      turns the two real estimates at eps/2 into the complex one at eps.
;;;
;;; WHAT WAS MISSING.  All five facts above.  The tree had `cc-re-sq-le-mod-sq'
;;; (Re(z)^2 <= z conj z, stated without `magnitude' so as not to drag in SQRT)
;;; and nothing else relating a coordinate to the modulus; and it had no
;;; additivity for `real-part' / `imag-part' at all.  The two-sided bound in (1)
;;; and (4) is one `sqrt-mono' each: |Re w| = SQRT(x^2) <= SQRT(x^2 + y^2) = |w|,
;;; and |w| = SQRT(x^2+y^2) <= SQRT((|x|+|y|)^2) = |x|+|y|.  (2) is `crs' on the
;;; unfolded definitions once conjugation is known to be additive
;;; (cc-conjugate-add / -neg, both already in the tree).
;;;
;;; THE TWO TRANSFER LEMMAS.  `cc-cauchy-of-dominated' and
;;; `cc-converges-of-coords' are stated in TRANSFER form -- the caller supplies
;;; a sequence agreeing pointwise with the coordinate, rather than the theorem
;;; concluding about a lambda it built itself.  Same reason as
;;; dominated-convergence.scm's design note 3 and continuity-transfer.scm: a
;;; conclusion about a literal VNB-LAMBDA can only ever be applied to that
;;; lambda, and every use then owes a beta-reduction under a binder.  Here it
;;; also means the eps/N bookkeeping is written ONCE and used twice (real part,
;;; imaginary part) instead of being copied.
;;;
;;; WHAT IT COSTS.  `cc-complete''s bill IS `rr-complete''s bill, leaf for leaf
;;; -- the completeness of CC costs what the completeness of RR costs and
;;; nothing more.  That is the durable statement; the snapshot moved under this
;;; file on the day it was written.  Both read `modulo {nn-add-succ}',
;;; `trust: reference' at 15:13 on 2026-08-24 and `modulo 0' at 15:52, when the
;;; NN-order work stamped `nn-add-succ' definitional.  The seven
;;; lemmas below are all `modulo 0'.  NOTHING ELSE IN THE LIBRARY MOVED: measured
;;; over all bills before and after, the only change is the eight new rows, and
;;; that is because NO PROOF IN THE TREE CITED `cc-complete' -- the axiom had sat
;;; there since the CC layer was written with not one consumer.  The value is
;;; entirely prospective (the ell^p / complex-series arc), and that is worth
;;; saying plainly rather than dressing up as a repair that moved something.
;;;
;;; ONE TRAP, and it is silent.  `forall-guarded' nests BOTH binders first and
;;; BOTH guards after; the surface `forall([m_ in nn, n_ in nn], ...)' that
;;; `make-wff' reads INTERLEAVES them.  The two formulas are equivalent and are
;;; NOT alpha-variants, so a `have!' built with the wrong one is not detached by
;;; `fact' -- which lands the IMPLICATION instead, says nothing, and leaves the
;;; next `inst+' instantiating a hypothesis that was never discharged.  The main
;;; proof builds its two-binder hypotheses with `cx-forall-in' for this reason.
;;;
;;; Loads after theorem-library/dominated-convergence (cc-ms-dist), which is the
;;; only reason it sits this late; everything else it cites -- cc-magnitude,
;;; cc-real-imag, cc-metric-space-proof, rr-complete-proof, rr-ms-dist,
;;; rr-abs-basics, binary-minus-laws, sqrt-defined, fun-apply-type-proof,
;;; nn-order-basics -- is far above.

;;; ---- file-local driver helpers (the `cx-' prefix) --------------------

;;; Peel the whole FORALL/IMPLIES prefix and STOP: `di' is greedy and the next
;;; call on an AND goal would SPLIT it.
(define (cx-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (cx-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; The atoms `ineq' would abstract a term to, mirroring vnb->linear; and the
;;; premises it can actually use -- order-shaped, every atom certified in RR.
;;; An `=' is arithmetic in SHAPE, so one complex equation in the context is
;;; accepted by the oracle and then fails its own atom test, killing the whole
;;; call.  Copy of cm-idx (cc-magnitude.scm) for the same reason it is a copy
;;; of contra.scm's: the files load in the wrong order to share it.
(define (cx-atoms t acc)
  (cond ((number? t) acc)
        ((not (pair? t)) (if (member t acc) acc (cons t acc)))
        ((memq (car t) '(+ - binplus binneg))
         (let lp ((as (cdr t)) (acc acc))
           (if (null? as) acc (lp (cdr as) (cx-atoms (car as) acc)))))
        ((memq (car t) '(* bintimes))
         (let ((nonnum (filter (lambda (a) (not (number? a))) (cdr t))))
           (cond ((null? nonnum) acc)
                 ((null? (cdr nonnum)) (cx-atoms (car nonnum) acc))
                 (else (if (member t acc) acc (cons t acc))))))
        (else (if (member t acc) acc (cons t acc)))))

(define (cx-idx)
  (let* ((sqn  (proof-state-focus *ps*))
         (asms (sequent-node-assumptions sqn)))
    (let loop ((as asms) (k 1) (acc '()))
      (if (null? as)
          (reverse acc)
          (let ((f (wff-formula (car as))))
            (loop (cdr as) (+ k 1)
                  (if (and (pair? f) (= (length f) 3)
                           (memq (car f) '(< <= =))
                           (let allok ((vs (cx-atoms (caddr f) (cx-atoms (cadr f) '()))))
                             (or (null? vs)
                                 (and (ineq-atom-rr-ok? (car vs) asms '())
                                      (allok (cdr vs))))))
                      (cons k acc)
                      acc)))))))
(define (cx-ineq!) (apply ineq (cx-idx)))

;;; ... and the NAMED-premise form, for a context where the sweep above would
;;; hand `ineq' more than it can carry.
(define (cx-at form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cx-at: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (cx-ineq . forms) (apply ineq (map cx-at forms)))

;;; `have!' of a formula ALREADY in context (up to alpha) is a silent SELF-LOOP
;;; (dg-post! hash-conses by alpha-equivalence), and the conjunctive typings the
;;; closure citations want are landed repeatedly -- so guard every one.
(define (cx-and! a b)
  (let ((f (list 'AND a b)))
    (if (not (any-pred (lambda (g) (alpha-equiv? g f)) (dk-asms)))
        (have! f))))

;;; Select a hypothesis by CONTENT, and ERROR on a miss.
(define (cx-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cx-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cx-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT -- `obtain' sees only what its
;;; own lane landed.  The eigenvariable is read off by free-variable difference.
(define (cx-skolem! ex)
  (let* ((fv0 (cx-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (cx-fvs (dk-asms)))))
      (if (null? fresh) (error "cx-skolem!: nothing appeared" ex) (car fresh)))))

;;; `di' until an ASSUMPTION lands: an UNGUARDED universal peels the quantifier
;;; and lands nothing, so loop on the LANDING, never on a `di' count.
(define (cx-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "cx-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (cx-di-landed-1!)
  (let ((new (cx-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "cx-di-landed-1!: expected 1" (map expression->string new)))))

;;; (IN x RR) and (0 <= x) from (POS-RR x), each on a SIDE branch: `mac-h' is
;;; destructive and the main branch still wants POS-RR for later detachments.
(define (cx-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; Split an AND goal to exhaustion and run CLOSER on each atomic leaf.
(define (cx-and-goal! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cx-and-goal! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; The coordinate typings and squares of ZZ, which every estimate below needs
;;; before `ineq' will certify an atom.  Returns (x y x^2 y^2 x^2+y^2).
(define (cx-coord-facts! zz)
  (let* ((x (list 'real-part zz)) (y (list 'imag-part zz))
         (sx (list '* x x)) (sy (list '* y y)) (p (list '+ sx sy)))
    (fact 'real-part-in-rr zz)
    (fact 'imag-part-in-rr zz)
    (cx-and! (list 'IN x 'RR) (list 'IN x 'RR))
    (fact 'rr-mul-closed x x)
    (cx-and! (list 'IN y 'RR) (list 'IN y 'RR))
    (fact 'rr-mul-closed y y)
    (fact 'rr-sq-nonneg x)
    (fact 'rr-sq-nonneg y)
    (cx-and! (list 'IN sx 'RR) (list 'IN sy 'RR))
    (fact 'rr-add-closed sx sy)
    (list x y sx sy p)))

;;; =====================================================================
;;; L1.  THE PROJECTIONS ARE ADDITIVE.  Re(z - w) = Re z - Re w, and the same
;;; for Im.  Both are one `crs' once the definitions are unfolded and
;;; conjugation is pushed through the difference; `cc-conjugate-add' and
;;; `cc-conjugate-neg' do the pushing, and the binary difference is rewritten
;;; to z + (-w) first because those two are stated at a SUM.
;;; =====================================================================

(define (cx-conj-sub-facts!)
  (fact 'cc-sub-in-cc 'z_ 'w_)
  (fact 'cc-neg-closed 'w_)
  (fact 'cc-conjugate-closed 'z_)
  (fact 'cc-conjugate-closed 'w_)
  (fact 'cc-conjugate-neg 'w_)
  (have! '(AND (IN z_ CC) (IN (- w_) CC)))
  (fact 'cc-conjugate-add 'z_ '(- w_))
  (have! '(= (- z_ w_) (+ z_ (- w_))) (lambda () (crs)))
  (subst '(= (- z_ w_) (+ z_ (- w_)))))

(define (cx-conj-push!)
  (subst '(= (conjugate (+ z_ (- w_))) (+ (conjugate z_) (conjugate (- w_)))))
  (subst '(= (conjugate (- w_)) (- (conjugate w_)))))

(sp (make-wff (forall-guarded '(z_ w_) '((IN z_ CC) (IN w_ CC))
      '(= (real-part (- z_ w_)) (- (real-part z_) (real-part w_))))))
(cx-peel!)
(cx-conj-sub-facts!)
;; recip 2 is a GENERATOR of the ring identity `crs' has to certify, so it is
;; typed in CC like the others.
(have! '(IN 2 RR))
(have! '(NOT (= 2 0)) (lambda () (arith)))
(have! '(AND (IN 2 RR) (NOT (= 2 0))))
(fact 'rr-recip-closed 2)
(fact 'rr-subset-cc '(recip 2))
(mac 'real-part-def)
(cx-conj-push!)
(crs)
(qed 'cc-re-sub)
(topic! 'cc-re-sub 'algebra)
(alias! 'cc-re-sub "the real part of a difference is the difference of the real parts")

(sp (make-wff (forall-guarded '(z_ w_) '((IN z_ CC) (IN w_ CC))
      '(= (imag-part (- z_ w_)) (- (imag-part z_) (imag-part w_))))))
(cx-peel!)
(cx-conj-sub-facts!)
(have! '(IN (* 2 +i) CC) (lambda () (arith)))
(have! '(NOT (= (* 2 +i) 0)) (lambda () (arith)))
(have! '(AND (IN (* 2 +i) CC) (NOT (= (* 2 +i) 0))))
(fact 'cc-recip-closed '(* 2 +i))
(mac 'imag-part-def)
(cx-conj-push!)
(crs)
(qed 'cc-im-sub)
(topic! 'cc-im-sub 'algebra)
(alias! 'cc-im-sub "the imaginary part of a difference is the difference of the imaginary parts")

;;; =====================================================================
;;; L2.  A COORDINATE IS DOMINATED BY THE MODULUS:  |Re z| <= |z|, |Im z| <= |z|.
;;;
;;; The tree had NEITHER.  What it had was `cc-re-sq-le-mod-sq' -- Re(z)^2 <=
;;; z conj z -- deliberately stated without `magnitude' so as to keep SQRT out
;;; of the inner-product inequalities.  That is the same inequality one square
;;; root away, but the square root is exactly the step, and nothing performed it.
;;;
;;; |Re z| = SQRT(x^2) <= SQRT(x^2 + y^2) = |z|: one `sqrt-mono', with
;;; `sqrt-of-sq' turning the abs into a root and `magnitude-def' turning the
;;; modulus into one.  No case split on the sign; that is what abs is for.
;;; =====================================================================

(define (cx-coord-le! zz which)
  (let* ((w  (cx-coord-facts! zz))
         (x  (car w)) (y (cadr w)) (sx (caddr w)) (sy (cadddr w))
         (p  (list-ref w 4))
         (u  (if (eq? which 'real-part) x y))
         (su (if (eq? which 'real-part) sx sy)))
    (have! (list '<= su p) (lambda () (cx-ineq!)))
    (cx-and! (list 'IN su 'RR) (list '<= 0 su))
    (cx-and! (list 'IN p 'RR) (list '<= su p))
    (fact 'sqrt-mono su p)
    (fact 'sqrt-of-sq-rev u)
    (mac 'magnitude-def)
    (subst (list '= (list 'abs u) (list 'SQRT su)))
    (ass)))

(sp (make-wff '(FORALL z_ (IMPLIES (IN z_ CC) (<= (abs (real-part z_)) (magnitude z_))))))
(cx-peel!)
(cx-coord-le! 'z_ 'real-part)
(qed 'cc-abs-re-le-magnitude)
(topic! 'cc-abs-re-le-magnitude 'inequalities)
(alias! 'cc-abs-re-le-magnitude "the real part is bounded by the modulus")

(sp (make-wff '(FORALL z_ (IMPLIES (IN z_ CC) (<= (abs (imag-part z_)) (magnitude z_))))))
(cx-peel!)
(cx-coord-le! 'z_ 'imag-part)
(qed 'cc-abs-im-le-magnitude)
(topic! 'cc-abs-im-le-magnitude 'inequalities)
(alias! 'cc-abs-im-le-magnitude "the imaginary part is bounded by the modulus")

;;; =====================================================================
;;; L3.  ... AND DOMINATES IT JOINTLY:  |z| <= |Re z| + |Im z|.
;;;
;;; SQRT(x^2 + y^2) <= SQRT((|x| + |y|)^2) = | |x| + |y| | = |x| + |y|, the
;;; middle step being `sqrt-mono' again and the inner comparison
;;; x^2 + y^2 <= (|x|+|y|)^2 = |x|^2 + |y|^2 + 2|x||y| a linear consequence of
;;; |x||y| >= 0 once |x|^2 = x^2 is known (rr-abs-mult at (x,x), plus
;;; rr-abs-of-nonneg on the square).  The cross term is the whole content and
;;; it is nonnegative, which is why the triangle inequality on CC is not needed.
;;; =====================================================================

(sp (make-wff '(FORALL z_ (IMPLIES (IN z_ CC)
      (<= (magnitude z_) (+ (abs (real-part z_)) (abs (imag-part z_))))))))
(cx-peel!)
(let* ((w  (cx-coord-facts! 'z_))
       (x  (car w)) (y (cadr w)) (sx (caddr w)) (sy (cadddr w)) (p (list-ref w 4))
       (ax (list 'abs x)) (ay (list 'abs y))
       (s  (list '+ ax ay))
       (ss (list '* s s)))
  (fact 'rr-abs-closed x)
  (fact 'rr-abs-closed y)
  (fact 'rr-abs-nonneg x)
  (fact 'rr-abs-nonneg y)
  (cx-and! (list 'IN ax 'RR) (list 'IN ay 'RR))
  (fact 'rr-add-closed ax ay)
  (have! (list '<= 0 s) (lambda () (cx-ineq!)))
  (fact 'rr-abs-closed s)
  (fact 'rr-abs-of-nonneg s)
  (cx-and! (list 'IN s 'RR) (list 'IN s 'RR))
  (fact 'rr-mul-closed s s)
  (fact 'rr-sq-nonneg s)
  (cx-and! (list 'IN ax 'RR) (list 'IN ax 'RR))
  (fact 'rr-mul-closed ax ax)
  (cx-and! (list 'IN ay 'RR) (list 'IN ay 'RR))
  (fact 'rr-mul-closed ay ay)
  (fact 'rr-mul-closed ax ay)
  (cx-and! (list 'IN x 'RR) (list 'IN x 'RR))
  (fact 'rr-abs-mult x x)
  (cx-and! (list 'IN y 'RR) (list 'IN y 'RR))
  (fact 'rr-abs-mult y y)
  (fact 'rr-abs-of-nonneg sx)
  (fact 'rr-abs-of-nonneg sy)
  (cx-and! (list '<= 0 ax) (list '<= 0 ay))
  (fact 'rr-leq-mul-nonneg ax ay)
  (have! (list '= ss (list '+ (list '+ (list '* ax ax) (list '* ay ay))
                              (list '+ (list '* ax ay) (list '* ax ay))))
         (lambda () (crs)))
  (have! (list '<= p ss) (lambda () (cx-ineq!)))
  (have! (list '<= 0 p) (lambda () (cx-ineq!)))
  (cx-and! (list 'IN p 'RR) (list '<= 0 p))
  (fact 'sqrt-nonneg p)
  (cx-split!)
  (cx-and! (list 'IN ss 'RR) (list '<= 0 ss))
  (fact 'sqrt-nonneg ss)
  (cx-split!)
  ;; sqrt-mono's two guards LAST: `cx-split!' consumes the context ANDs, so a
  ;; conjunctive guard landed before it is no longer there to be detached.
  (cx-and! (list 'IN p 'RR) (list '<= 0 p))
  (cx-and! (list 'IN ss 'RR) (list '<= p ss))
  (fact 'sqrt-mono p ss)
  (fact 'sqrt-of-sq s)
  (mac 'magnitude-def)
  (cx-ineq!))
(qed 'cc-magnitude-le-re-im)
(topic! 'cc-magnitude-le-re-im 'inequalities)
(alias! 'cc-magnitude-le-re-im "the modulus is at most the sum of the coordinate moduli")

;;; =====================================================================
;;; L4.  THE COORDINATE OF A CAUCHY SEQUENCE IS CAUCHY, in TRANSFER form: any
;;; REAL sequence p whose increments are dominated by the CC-MS distance of a
;;; Cauchy f is itself Cauchy.  Stated this way -- rather than about
;;; VNB-LAMBDA n. real-part(f n) -- the eps/N bookkeeping is written once and
;;; spent twice, at the real part and at the imaginary part.
;;;
;;; The whole proof is: unfold the CC hypothesis, take its threshold at the SAME
;;; eps, and chain  |p(m) - p(n)| <= |f(m) - f(n)| = dist_CC(f m, f n) <= eps.
;;; Both distances are brought to the surface as MACETES (`rr-ms-dist' on the
;;; goal, `cc-ms-dist' on the hypothesis) and both are GUARDED, so every
;;; argument is typed BEFORE the rewrite -- on the goal an untyped `mac' does
;;; not fire at all, it only warns, and the driver would sail on rewriting
;;; nothing.
;;; =====================================================================
(sp (make-wff "forall([f in fun(nn,cc), p in fun(nn,rr)],
     is-cauchy-seq(cc-ms, f) implies
     forall([m_ in nn, n_ in nn], abs(p(m_) - p(n_)) <= magnitude(f(m_) - f(n_))) implies
     is-cauchy-seq(rr-ms, p))"))
(cx-peel!)
(define cd-dom (cx-find 'domination
   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'magnitude)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'is-cauchy-seq '(IS-CAUCHY-SEQ CC-MS f)))
                           (lambda (a) (eq? (car a) 'AND))))
(define cd-tail (cx-find 'cc-tail
   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))
(mac 'is-cauchy-seq)
(cx-and-goal!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
           ((eq? (car gl) 'IN) (slot 'PTS) (ass))
           (else
            (let* ((eps (cadr (cx-di-landed-1!)))
                   (ex  (dk-deepest (lambda () (inst+ cd-tail eps))))
                   (bigN (cx-skolem! ex))
                   (inner (cx-find 'inner
                            (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                             (dk-contains? a bigN)
                                             (dk-contains? a 'DIST))))))
              (ew bigN)
              (cx-and-goal!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (begin
                      ;; ONE `di' lands BOTH index typings, so the eigenvariables
                      ;; are read off the GOAL, never off the landing order:
                      ;; dk-asms order is not the peel order.
                      (cx-di-landed!)
                     (let* ((dd (cadr (caddr (dk-goal))))   ; ((DIST RR-MS) (p mm) (p nx))
                            (mm (cadr (cadr dd)))
                            (nx (cadr (caddr dd))))
                       (cx-di-landed!)   ; the (bigN <= mm and bigN <= nx) AND
                       ;; `inst+' lands the whole instantiation chain, so take the
                       ;; landing no other landing contains (dk-deepest), twice.
                       (let ((l2 (dk-deepest
                                  (lambda ()
                                    (inst+ (dk-deepest (lambda () (inst+ inner mm))) nx)))))
                         (let* ((d2 (dk-deepest
                                     (lambda ()
                                       (inst+ (dk-deepest (lambda () (inst+ cd-dom mm))) nx))))
                                (fm (list 'f mm)) (fn (list 'f nx))
                                (pm (list 'p mm)) (pn (list 'p nx))
                                (du (list '- fm fn)) (dv (list '- pm pn)))
                           (fact 'fun-apply-type-c 'f 'NN 'CC mm)
                           (fact 'fun-apply-type-c 'f 'NN 'CC nx)
                           (fact 'fun-apply-type-c 'p 'NN 'RR mm)
                           (fact 'fun-apply-type-c 'p 'NN 'RR nx)
                           (fact 'cc-sub-in-cc fm fn)
                           (fact 'cc-magnitude-closed du)
                           (fact 'rr-sub-in-rr pm pn)
                           (fact 'rr-abs-closed dv)
                           (cx-pos-in-rr! eps)
                           (mac 'rr-ms-dist)
                           (mac-h 'cc-ms-dist l2)

                           (cx-ineq d2 (list '<= (list 'magnitude du) eps)))))))))))))))
(qed 'cc-cauchy-of-dominated)

;;; =====================================================================
;;; L5.  ... AND COORDINATEWISE CONVERGENCE IS CONVERGENCE.  Transfer form
;;; again: g and q_ agree pointwise with the two coordinates of f and converge
;;; in RR-MS to the two coordinates of a complex lv.
;;;
;;; eps is halved once (rr-pos-halvable), the two real thresholds are merged by
;;; MAX, and L3 turns the two real estimates into the complex one:
;;;
;;;   |f(n) - lv| <= |Re(f(n) - lv)| + |Im(f(n) - lv)|
;;;               =  |g(n) - Re lv| + |q_(n) - Im lv|  <=  d + d  =  eps,
;;;
;;; the middle equality being L1 plus the pointwise hypotheses.  Those
;;; hypotheses are stated `real-part(f(n_)) = g(n_)' and not the other way
;;; round because `subst' rewrites LEFT to RIGHT: the orientation is what makes
;;; the two `have!' lanes below one line each.
;;; =====================================================================
(sp (make-wff "forall([f in fun(nn,cc), g in fun(nn,rr), q_ in fun(nn,rr), lv in cc],
     forall([n_ in nn], real-part(f(n_)) = g(n_)) implies
     forall([n_ in nn], imag-part(f(n_)) = q_(n_)) implies
     converges-to(rr-ms, g, real-part(lv)) implies
     converges-to(rr-ms, q_, imag-part(lv)) implies
     converges-to(cc-ms, f, lv))"))
(cx-peel!)
(define cv-re (cx-find 're (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a 'real-part)))))
(define cv-im (cx-find 'im (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a 'imag-part)))))

(dk-split! (dk-landed-find
            (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS g (real-part lv))))
            (lambda (a) (eq? (car a) 'AND))))
(define cv-tg (cx-find 'tail-g (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                (dk-contains? a 'POS-RR)
                                                (dk-contains? a 'g)))))
(dk-split! (dk-landed-find
            (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS q_ (imag-part lv))))
            (lambda (a) (eq? (car a) 'AND))))
(define cv-tq (cx-find 'tail-q (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                (dk-contains? a 'POS-RR)
                                                (dk-contains? a 'q_)))))

(mac 'converges-to)
(cx-and-goal!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'cc-is-metric-space) (ass))
           ((eq? (car gl) 'IN) (slot 'PTS) (ass))
           (else
            (let* ((eps (cadr (cx-di-landed-1!)))
                   (hex (dk-fact! 'rr-pos-halvable eps))
                   (d   (cx-skolem! hex))
                   (exg (dk-deepest (lambda () (inst+ cv-tg d))))
                   (ng  (cx-skolem! exg))
                   (ing (cx-find 'inner-g
                          (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                           (dk-contains? a ng) (dk-contains? a 'g)))))
                   (exq (dk-deepest (lambda () (inst+ cv-tq d))))
                   (nq  (cx-skolem! exq))
                   (inq (cx-find 'inner-q
                          (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                           (dk-contains? a nq) (dk-contains? a 'q_)))))
                   (bnd (list 'MAX ng nq)))
              (fact 'nn-max-closed ng nq)
              (ew bnd)
              (cx-and-goal!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (let* ((nx (cadr (cx-di-landed-1!))))
                       (cx-di-landed!)                    ; (bnd <= nx)
                       (fact 'nn-in-rr ng) (fact 'nn-in-rr nq)
                       (fact 'nn-in-rr bnd) (fact 'nn-in-rr nx)
                       (fact 'rr-le-max-left ng nq)
                       (fact 'rr-le-max-right ng nq)
                       (have! (list '<= ng nx)
                         (lambda () (cx-ineq (list '<= ng bnd) (list '<= bnd nx))))
                       (have! (list '<= nq nx)
                         (lambda () (cx-ineq (list '<= nq bnd) (list '<= bnd nx))))
                       (let* ((fn  (list 'f nx))
                              (du  (list '- fn 'lv))
                              (rdu (list 'real-part du))
                              (idu (list 'imag-part du)))
                         (inst+ ing nx)
                         (inst+ inq nx)
                         (inst+ cv-re nx)
                         (inst+ cv-im nx)
                         (fact 'fun-apply-type-c 'f 'NN 'CC nx)
                         (fact 'fun-apply-type-c 'g 'NN 'RR nx)
                         (fact 'fun-apply-type-c 'q_ 'NN 'RR nx)
                         (fact 'real-part-in-rr 'lv)
                         (fact 'imag-part-in-rr 'lv)
                         (cx-pos-in-rr! eps)
                         (cx-pos-in-rr! d)
                         (mac-h 'rr-ms-dist
                           (list '<= (list (list 'DIST 'RR-MS) (list 'g nx) '(real-part lv)) d))
                         (mac-h 'rr-ms-dist
                           (list '<= (list (list 'DIST 'RR-MS) (list 'q_ nx) '(imag-part lv)) d))

                         (fact 'cc-sub-in-cc fn 'lv)
                         (fact 'cc-magnitude-closed du)
                         (fact 'real-part-in-rr du)
                         (fact 'imag-part-in-rr du)
                         (fact 'rr-abs-closed rdu)
                         (fact 'rr-abs-closed idu)
                         (fact 'cc-re-sub fn 'lv)
                         (fact 'cc-im-sub fn 'lv)
                         (have! (list '<= (list 'abs rdu) d)
                           (lambda ()
                             (subst (list '= rdu (list '- (list 'real-part fn) '(real-part lv))))
                             (subst (list '= (list 'real-part fn) (list 'g nx)))
                             (ass)))
                         (have! (list '<= (list 'abs idu) d)
                           (lambda ()
                             (subst (list '= idu (list '- (list 'imag-part fn) '(imag-part lv))))
                             (subst (list '= (list 'imag-part fn) (list 'q_ nx)))
                             (ass)))
                         (fact 'cc-magnitude-le-re-im du)
                         (mac 'cc-ms-dist)

                         (cx-ineq (list '<= (list 'magnitude du)
                                            (list '+ (list 'abs rdu) (list 'abs idu)))
                                  (list '<= (list 'abs rdu) d)
                                  (list '<= (list 'abs idu) d)
                                  (list '= (list '+ d d) eps))
                         )))))))))))
(qed 'cc-converges-of-coords)


;;; =====================================================================
;;; THE THEOREM.  IS-COMPLETE(CC-MS).
;;;
;;; Given a Cauchy f, the two coordinate sequences are built as VNB-LAMBDAs,
;;; typed by `dk-lam-t!' (which pays the (IN NN SET) obligation lam-t opens
;;; beside the pointwise typing), identified with the coordinates pointwise by
;;; one `lam-b' each, shown Cauchy by L4, converged by `rr-complete', and
;;; reassembled by L5 at lv = Lr + Li i, whose coordinates are Lr and Li by
;;; `cc-re-im-of'.
;;;
;;; The bill is exactly rr-complete's, leaf for leaf; both are `modulo 0'.
;;; =====================================================================
(define cc-G '(VNB-LAMBDA k_ NN (real-part (f k_))))
(define cc-H '(VNB-LAMBDA k_ NN (imag-part (f k_))))

(sp (make-wff '(IS-COMPLETE CC-MS)))
(mac 'is-complete)
(di)
(fact 'cc-is-metric-space)
(ass)
(di)
(di)
;; `mac-h' REPLACES the assumption it unfolds, and cc-cauchy-of-dominated needs
;; IS-CAUCHY-SEQ(CC-MS, f) itself -- so read the typing off it on a SIDE branch.
(have! '(IN f (FUN NN CC))
  (lambda ()
    (dk-split! (dk-landed-find
                (lambda () (mac-h 'is-cauchy-seq '(IS-CAUCHY-SEQ CC-MS f)))
                (lambda (a) (eq? (car a) 'AND))))
    (slot-h 'PTS '(IN f (FUN NN (PTS CC-MS))))
    (ass)))
(define (cc-type-lam! L)
  (have! (list 'IN L '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let ((k (cadr (cx-di-landed-1!))))
        (fact 'fun-apply-type-c 'f 'NN 'CC k)
        (fact 'real-part-in-rr (list 'f k))
        (fact 'imag-part-in-rr (list 'f k))
        (ass)))))
(cc-type-lam! cc-G)
(cc-type-lam! cc-H)
;; the pointwise identifications, oriented as cc-converges-of-coords wants them
(define (cc-ptwise! L which)
  (let ((fm (forall-guarded '(n_) (list '(IN n_ NN))
              (list '= (list which '(f n_)) (list L 'n_)))))
    (have! fm
      (lambda ()
        (cx-di-landed!)
        (fact 'fun-apply-type-c 'f 'NN 'CC 'n_)
        (fact 'real-part-in-rr '(f n_))
        (fact 'imag-part-in-rr '(f n_))
        (lam-b)
        (rfl)))
    fm))
(define cc-pt-re (cc-ptwise! cc-G 'real-part))
(define cc-pt-im (cc-ptwise! cc-H 'imag-part))
(define (cc-has-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA)) #t)
        (else (any-pred cc-has-redex? e))))
(define (cc-beta!)
  (let lp ((n 0)) (if (and (< n 6) (cc-has-redex? (dk-goal))) (begin (lam-b) (lp (+ n 1))))))
;; INTERLEAVED binder/guard nesting -- what the surface `forall([m_ in nn, n_ in
;; nn], ...)' of cc-cauchy-of-dominated expands to.  `forall-guarded' puts BOTH
;; binders first and BOTH guards after, which is an equivalent formula and NOT
;; an alpha-variant, so `fact' would decline to detach it and land the
;; implication instead -- silently.
(define (cx-forall-in bs body)
  (if (null? bs) body
      (list 'FORALL (caar bs)
            (list 'IMPLIES (list 'IN (caar bs) (cdar bs))
                  (cx-forall-in (cdr bs) body)))))
(define (cc-dom! L which-rev bound-lemma)
  (let ((fm (cx-forall-in '((m_ . NN) (n_ . NN))
              (list '<= (list 'abs (list '- (list L 'm_) (list L 'n_)))
                        (list 'magnitude '(- (f m_) (f n_)))))))
    (have! fm
      (lambda ()
        (cx-peel!)
        (fact 'fun-apply-type-c 'f 'NN 'CC 'm_)
        (fact 'fun-apply-type-c 'f 'NN 'CC 'n_)
        (fact 'real-part-in-rr '(f m_))
        (fact 'real-part-in-rr '(f n_))
        (fact 'imag-part-in-rr '(f m_))
        (fact 'imag-part-in-rr '(f n_))
        (cc-beta!)
        (fact 'cc-sub-in-cc '(f m_) '(f n_))
        (fact which-rev '(f m_) '(f n_))
        (fact bound-lemma '(- (f m_) (f n_)))
        (subst (list '= (list '- (list (if (eq? which-rev 'cc-re-sub-rev) 'real-part 'imag-part) '(f m_))
                                 (list (if (eq? which-rev 'cc-re-sub-rev) 'real-part 'imag-part) '(f n_)))
                        (list (if (eq? which-rev 'cc-re-sub-rev) 'real-part 'imag-part) '(- (f m_) (f n_)))))
        (ass)))
    fm))
(define cc-dom-re (cc-dom! cc-G 'cc-re-sub-rev 'cc-abs-re-le-magnitude))
(define cc-dom-im (cc-dom! cc-H 'cc-im-sub-rev 'cc-abs-im-le-magnitude))
(define cc-cd1 (dk-fact! 'cc-cauchy-of-dominated 'f cc-G))
(define cc-cd2 (dk-fact! 'cc-cauchy-of-dominated 'f cc-H))
(fact 'rr-complete)
(dk-split! (dk-landed-find (lambda () (mac-h 'is-complete '(IS-COMPLETE RR-MS)))
                           (lambda (a) (eq? (car a) 'AND))))
(define cc-univ (cx-find 'rr-univ
  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'IS-CAUCHY-SEQ)))))
(define cvG (dk-deepest (lambda () (inst+ cc-univ cc-G))))
(define cvH (dk-deepest (lambda () (inst+ cc-univ cc-H))))
(define (cc-limit! cv L)
  (let* ((ex (dk-landed-find (lambda () (mac-h 'converges cv))
                             (lambda (a) (eq? (car a) 'FORSOME))))
         (lim (cx-skolem! ex)))
    (have! (list 'IN lim 'RR)
      (lambda ()
        (dk-split! (dk-landed-find
                    (lambda () (mac-h 'converges-to (list 'CONVERGES-TO 'RR-MS L lim)))
                    (lambda (a) (eq? (car a) 'AND))))
        (slot-h 'PTS (list 'IN lim '(PTS RR-MS)))
        (ass)))
    lim))
(define cc-Lr (cc-limit! cvG cc-G))
(define cc-Li (cc-limit! cvH cc-H))
(define cc-lv (list '+ cc-Lr (list '* cc-Li '+i)))
(fact 'rr-subset-cc cc-Lr)
(fact 'rr-subset-cc cc-Li)
(fact 'cc-i-in)
(cx-and! (list 'IN cc-Li 'CC) '(IN +i CC))
(fact 'cc-mul-closed cc-Li '+i)
(cx-and! (list 'IN cc-Lr 'CC) (list 'IN (list '* cc-Li '+i) 'CC))
(fact 'cc-add-closed cc-Lr (list '* cc-Li '+i))
(have! (list '= cc-lv cc-lv) (lambda () (rfl)))
(fact 'cc-re-im-of cc-lv cc-Lr cc-Li)
(dk-split! (list 'AND (list '= (list 'real-part cc-lv) cc-Lr)
                      (list '= (list 'imag-part cc-lv) cc-Li)))
(have! (list 'CONVERGES-TO 'RR-MS cc-G (list 'real-part cc-lv))
  (lambda () (subst (list '= (list 'real-part cc-lv) cc-Lr)) (ass)))
(have! (list 'CONVERGES-TO 'RR-MS cc-H (list 'imag-part cc-lv))
  (lambda () (subst (list '= (list 'imag-part cc-lv) cc-Li)) (ass)))
(fact 'cc-converges-of-coords 'f cc-G cc-H cc-lv)
(mac 'converges)
(ew cc-lv)
(ass)
(qed 'cc-complete)
(topic! 'cc-complete 'analysis)
(alias! 'cc-complete "the complex numbers are a complete metric space")
