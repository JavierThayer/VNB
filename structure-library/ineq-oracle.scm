;;; ineq-oracle.scm -- the (ineq) decision procedure: close a linear-inequality
;;; goal over RR from NAMED assumptions, crs-style, via the Fourier-Motzkin /
;;; Farkas engine in linear-arith.scm.
;;;
;;; Usage (post-di, so the linear premises are assumptions):
;;;   (ineq i j k ...)   ; i,j,k = 1-based indices of the assumptions to use as
;;;                      ;         linear premises (predictable: no auto-scan).
;;; Goal and premises must be <=, <, or = between linear RR expressions.
;;;
;;; ATOM ABSTRACTION (decision #2): a term is linearized over +, -, * (and the
;;; binplus/binneg/bintimes aliases) and numeric literals; every MAXIMAL non-
;;; arithmetic subterm is treated as an opaque real variable -- exactly how crs
;;; treats compound generators.  So  d(x,y) <= d(x,z) + d(z,y)  is linear in the
;;; three distance atoms, and  3 + f(x) <= 1 + f(x) + 2  is linear in f(x).
;;;
;;; SOUNDNESS: linear-combination + positive-rational scaling is valid only over
;;; an ordered field, so every atom must be certified in RR (an (IN atom RR)
;;; assumption, an abs(.) term by rr-abs-closed, or an RR-typed goal binder).
;;; Uncertified atoms => refuse.  Trusted oracle; warrant 'ineq below, and each
;;; success prints its Farkas certificate (the nonneg combo that yields 0<0).
;;;
;;; Dependencies: linear-arith.scm (make-con, la-*, fm-prove), kernel
;;; (sequent-node-*, dg-apply-rule!, sqn-dg, wff-formula), warrants.

;;; -----------------------------------------------------------------------
;;; Linear forms over RR atoms:  (coeffs . const), coeffs an alist (atom . rat).

(define (lin-zero)        (cons '() 0))
(define (lin-const k)     (cons '() k))
(define (lin-atom t)      (cons (list (cons t 1)) 0))
(define (lin-coeffs L)    (car L))
(define (lin-const-of L)  (cdr L))
(define (lin-pure-const? L) (null? (car L)))
(define (lin-add L1 L2)   (cons (la-add (car L1) (car L2)) (+ (cdr L1) (cdr L2))))
(define (lin-scale L k)   (cons (la-scale (car L) k) (* k (cdr L))))
(define (lin-neg L)       (lin-scale L -1))

(define (lin-mul L1 L2)   ; product is linear only if a factor is constant; else #f
  (cond ((lin-pure-const? L1) (lin-scale L2 (lin-const-of L1)))
        ((lin-pure-const? L2) (lin-scale L1 (lin-const-of L2)))
        (else #f)))

(define la-plus-ops  '(+ binplus))
(define la-minus-ops '(- binneg))
(define la-times-ops '(* bintimes))

;;; CONSTANT DENOMINATORS, 2026-08-22, on the user's call.
;;;
;;; `recip(2)' and `eps / 2' used to become opaque ATOMS, so the commonest step
;;; in analysis -- halve the epsilon -- fell outside the oracle.  Measured, same
;;; goal three ways:
;;;
;;;     0.5*eps + 0.5*eps <= eps                 CLOSES
;;;     eps*recip(2) + eps*recip(2) <= eps       open
;;;     (eps/2) + (eps/2) <= eps                 open
;;;
;;; and with opaque atoms, which is the real shape of an eps/2 argument:
;;;
;;;     a <= 0.5*e, b <= 0.5*e, c <= a+b  |-  c <= e     CLOSES, Farkas 1/2 each
;;;     ... the same with e*recip(2)                     open
;;;
;;; So the whole obstacle was that the coefficient was SPELLED `recip(2)' rather
;;; than `0.5'.  Folding it is not a widening of what the oracle ACCEPTS -- no
;;; new premise shape is admitted, no atom goes uncertified -- it is evaluation
;;; of a closed arithmetic term, which `arith' already does.
;;;
;;; SOUNDNESS, and why the guards are exactly these.  For a nonzero exact
;;; rational literal c, `recip(c)' denotes 1/c in RR: `rr-recip-inverse' gives
;;; c * recip(c) = 1, and an inverse in a field is unique.  So replacing the
;;; term by the constant preserves the denotation.  The guards:
;;;
;;;   NONZERO   -- recip(0) is undefined; folding it would invent a value.
;;;   EXACT     -- an inexact literal is not a rational the theory names, and
;;;                arith-eval.scm's sound-arith gate rejects inexactness for the
;;;                same reason.  Since parser.scm reads every literal with #e,
;;;                anything inexact here was hand-built and is refused.
;;;   LITERAL   -- `recip(x)' for a variable or compound x stays an ATOM exactly
;;;                as before.  Nothing is assumed about its sign or definedness.
;;;
;;; `/' gets the same treatment for its DENOMINATOR only: (/ a c) is a * recip(c)
;;; (binary-divide-def), so a constant c scales a's linear form and a
;;; non-constant one leaves the whole quotient an atom.
(define (la-const-denominator? c)
  (and (number? c) (exact? c) (rational? c) (not (= c 0))))

;; vnb->linear : VNB term -> linear form.  Non-arithmetic subterms become atoms.
(define (vnb->linear t)
  (cond
    ((number? t) (lin-const t))
    ((not (pair? t)) (lin-atom t))                 ; bare symbol = variable atom
    (else
     (let ((op (car t)) (args (cdr t)))
       (cond
         ((and (memq op la-plus-ops) (pair? args))
          (fold-left lin-add (lin-zero) (map vnb->linear args)))
         ((and (memq op la-minus-ops) (= (length args) 1))
          (lin-neg (vnb->linear (car args))))
         ((and (memq op la-minus-ops) (= (length args) 2))
          (lin-add (vnb->linear (car args)) (lin-neg (vnb->linear (cadr args)))))
         ((and (memq op la-times-ops) (pair? args))
          (let loop ((as (cdr args)) (acc (vnb->linear (car args))))
            (cond ((not acc) (lin-atom t))         ; nonlinear product => atom
                  ((null? as) acc)
                  (else (loop (cdr as) (lin-mul acc (vnb->linear (car as))))))))
         ;; recip / divide by a CONSTANT -- see the note above la-const-denominator?
         ((and (eq? op 'recip) (= (length args) 1)
               (la-const-denominator? (car args)))
          (lin-const (/ 1 (car args))))
         ((and (eq? op '/) (= (length args) 2)
               (la-const-denominator? (cadr args)))
          (lin-scale (vnb->linear (car args)) (/ 1 (cadr args))))
         (else (lin-atom t)))))))                  ; any other head => maximal atom

;;; The atoms a term is BUILT from, before any cancellation.  `vnb->linear' adds coefficients,
;;; so an atom that cancels (t - t, or the same t on both sides of the relation) leaves no
;;; trace in the linear form -- and until 2026-09-20 was therefore never certified real:
;;;    forall u. abs(u) <= abs(u) + 1      closed with u untyped.
;;; The order and ring laws the oracle stands for are guarded on RR, so EVERY atom of the goal
;;; and of a used premise has to be certified, cancelled or not.  Same case analysis as
;;; vnb->linear, collecting instead of adding.
(define (ineq-source-atoms t)
  (cond
    ((number? t) '())
    ((not (pair? t)) (list t))
    (else
     (let ((op (car t)) (args (cdr t)))
       (cond
         ((and (memq op la-plus-ops) (pair? args))
          (apply append (map ineq-source-atoms args)))
         ((and (memq op la-minus-ops) (or (= (length args) 1) (= (length args) 2)))
          (apply append (map ineq-source-atoms args)))
         ((and (memq op la-times-ops) (pair? args))
          ;; a product vnb->linear can read as linear contributes its factors' atoms;
          ;; a nonlinear product is ONE atom, exactly as vnb->linear treats it
          (let ((L (vnb->linear t)))
            (if (and (pair? (lin-coeffs L)) (null? (cdr (lin-coeffs L)))
                     (equal? (car (car (lin-coeffs L))) t))
                (list t)
                (apply append (map ineq-source-atoms args)))))
         ((and (eq? op 'recip) (= (length args) 1) (la-const-denominator? (car args))) '())
         ((and (eq? op '/) (= (length args) 2) (la-const-denominator? (cadr args)))
          (ineq-source-atoms (car args)))
         (else (list t)))))))

(define (ineq-formula-source-atoms f)
  (if (and (pair? f) (= (length f) 3))
      (append (ineq-source-atoms (cadr f)) (ineq-source-atoms (caddr f)))
      '()))

;;; -----------------------------------------------------------------------
;;; Formula -> (linform . rel), where linform is lhs-rhs and rel in {le,lt,eq}.

(define (ineq-rel-of head)
  (cond ((eq? head '<=) 'le) ((eq? head '<) 'lt) ((eq? head '=) 'eq) (else #f)))

(define (formula->lin+rel f)
  (and (pair? f) (= (length f) 3)
       (let ((rel (ineq-rel-of (car f))))
         (and rel
              (cons (lin-add (vnb->linear (cadr f))
                             (lin-neg (vnb->linear (caddr f))))
                    rel)))))

;; A hypothesis at index i -> engine constraint(s).  Equality splits into the
;; two <= directions, with ids hI and hI-rev so the certificate distinguishes
;; them; le/lt give one constraint with id hI.
(define (ineq-hyp-constraints i L rel)
  (let ((hid (string->symbol (string-append "h" (number->string i)))))
    (cond
      ((eq? rel 'eq)
       (let ((hidr (string->symbol (string-append "h" (number->string i) "-rev"))))
         (list (make-con (lin-coeffs L) (lin-const-of L) 'le (list (cons hid 1)))
               (make-con (la-scale (lin-coeffs L) -1) (- (lin-const-of L)) 'le
                         (list (cons hidr 1))))))
      (else
       (list (make-con (lin-coeffs L) (lin-const-of L) rel (list (cons hid 1))))))))

;;; -----------------------------------------------------------------------
;;; RR certification of atoms.

;; Peel RR-typed universal binders off a goal: (FORALL v (IMPLIES (IN v RR) ..)).
(define (ineq-peel-rr-foralls g)
  (let loop ((g g) (vs '()))
    (if (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3))
        (let ((v (cadr g)) (body (caddr g)))
          (if (and (pair? body) (eq? (car body) 'IMPLIES)
                   (let ((a (cadr body)))
                     (and (pair? a) (eq? (car a) 'IN)
                          (eq? (cadr a) v) (equal? (caddr a) 'RR))))
              (loop (caddr body) (cons v vs))
              (cons g vs)))
        (cons g vs))))

(define (ineq-atom-rr-ok? v asms rr-qvars)
  (or (member v rr-qvars)
      ;; rr-abs-closed is  forall a in RR. abs(a) in RR : abs(t) is real only when t is.
      ;; Until 2026-09-20 ANY abs(.) was accepted as a real atom, whatever its argument
      ;; (found by the independent checker, batch 10-D).  Now t must read as a linear
      ;; form whose own atoms are certified, by this same test.
      (and (pair? v) (eq? (car v) 'abs) (= (length v) 2)
           (let allok ((as (ineq-source-atoms (cadr v))))
             (or (null? as)
                 (and (ineq-atom-rr-ok? (car as) asms rr-qvars)
                      (allok (cdr as))))))
      (let scan ((as asms))
        (and (pair? as)
             (or (let ((f (wff-formula (car as))))
                   (and (pair? f) (= (length f) 3) (eq? (car f) 'IN)
                        (equal? (cadr f) v) (equal? (caddr f) 'RR)))
                 (scan (cdr as)))))))

;;; -----------------------------------------------------------------------
;;; The primitive inference.

(define (ineq-report cert)
  (display ";; ineq: closed by Farkas certificate ") (write cert) (newline))

(define (pi-ineq! sqn idxs)
  (let* ((goal0 (wff-formula (sequent-node-assertion sqn)))
         (peel  (ineq-peel-rr-foralls goal0))
         (goal  (car peel))
         (rrqv  (cdr peel))
         (asms  (sequent-node-assumptions sqn))
         (dg    (sqn-dg sqn))
         (nasm  (length asms))
         (gpr   (formula->lin+rel goal)))
    (and gpr
         ;; THE EIGENVARIABLE CONDITION (2026-09-20).  `ineq-peel-rr-foralls' strips the
         ;; goal's leading  forall v in RR  and from then on treats v as an atom -- the SAME
         ;; atom as a free v in a premise.  Without this test the sequent
         ;;      x in RR,  x <= 0   |-   forall x in RR. x <= 0
         ;; was closed, the false theorem
         ;;      forall x in RR. (x <= 0 implies forall x in RR. x <= 0)
         ;; installed `modulo 0', and 1 <= 0 followed (reproduced on the band the day it was
         ;; found, by batch 10-D's independent checker).  A variable bound by a peeled
         ;; quantifier must not occur free in ANY assumption of the node: decline otherwise.
         (let fresh? ((vs rrqv))
           (or (null? vs)
               (and (let scan ((as asms))
                      (or (null? as)
                          (and (not (memq (car vs) (free-vars (wff-formula (car as)))))
                               (scan (cdr as)))))
                    (fresh? (cdr vs)))))
         (let ((hyp-cons '()) (used-forms '()) (ok #t))
           ;; A named assumption that is NOT arithmetic is SKIPPED, not fatal
           ;; (2026-08-15).  It used to set ok := #f and abandon the call, so
           ;; naming one harmless extra premise killed the whole thing:
           ;;
           ;;   (ineq 1)    with  1. u <= 0,  2. u in rr   |-  u <= 1   CLOSES
           ;;   (ineq 1 2)  -- same premises plus the RR typing --       REFUSES
           ;;
           ;; and the message said "goal not a linear-RR consequence", pointing
           ;; at the goal when the fault was in the premise list.  In practice
           ;; every real context mixes typings and memberships with the order
           ;; facts, so a caller could not simply name everything; and an
           ;; AUTOMATIC caller -- the copilot probing "is this context
           ;; inconsistent?" -- has no way to know which subset to name.
           ;;
           ;; Skipping is soundness-preserving BY CONSTRUCTION: dropping a
           ;; premise can only make Fourier-Motzkin prove less, never more.  An
           ;; out-of-range index is still fatal -- that is a caller error, not a
           ;; premise the procedure has an opinion about.
           (for-each
             (lambda (i)
               (if (and (integer? i) (>= i 1) (<= i nasm))
                   (let ((hpr (formula->lin+rel (wff-formula (list-ref asms (- i 1))))))
                     (if hpr
                         (begin
                           (set! used-forms
                                 (cons (wff-formula (list-ref asms (- i 1))) used-forms))
                           (set! hyp-cons
                             (append hyp-cons
                               (ineq-hyp-constraints i (car hpr) (cdr hpr)))))
                         #f))                    ; not arithmetic -- ignore it
                   (set! ok #f)))
             idxs)
           (and ok
                (let* ((gcoeffs (lin-coeffs (car gpr)))
                       ;; SOURCE atoms (2026-09-20): every atom the goal and the used premises
                       ;; are built from, including those that cancel in the linear forms.
                       (atoms (la-uniq
                               (append (ineq-formula-source-atoms goal)
                                       (apply append
                                         (map ineq-formula-source-atoms used-forms))))))
                  (and (let allok ((vs atoms))
                         (or (null? vs)
                             (and (ineq-atom-rr-ok? (car vs) asms rrqv)
                                  (allok (cdr vs)))))
                       (let ((cert (fm-prove hyp-cons gcoeffs
                                             (lin-const-of (car gpr)) (cdr gpr))))
                         (and cert
                              (begin
                                (ineq-report cert)
                                ;; THE RECORDED TAG CARRIES THE CERTIFICATE
                                ;; (2026-09-20).  `ineq' stays the head -- the
                                ;; ledger, *kernel-rule-tags* and the kernel map
                                ;; all go by head -- and the argument is the
                                ;; Farkas certificate exactly as fm-prove
                                ;; returned it and ineq-report just printed it:
                                ;; an alist (id . multiplier) over the premise
                                ;; ids hI / hI-rev and the negated goal `goal',
                                ;; or a PAIR of two such alists when the goal is
                                ;; an equation (one per direction).  It is what
                                ;; the rule checker (rule-checkers-oracle.scm)
                                ;; verifies by plain arithmetic; without it an
                                ;; `ineq' inference could only be re-decided by
                                ;; running the oracle again, which is no check.
                                (dg-apply-rule! dg (list 'ineq cert) '() sqn)))))))))))

(warrant! 'ineq 'well-known
  "Decision procedure for linear arithmetic over the ordered field RR.  The goal
   and the named premise assumptions are each read as a linear (in)equality in
   their maximal non-arithmetic subterms (atoms, all certified in RR); Fourier-
   Motzkin elimination on premises + negated goal seeks an infeasibility, whose
   Farkas certificate is a nonnegative combination of the premises and the
   negated goal summing to 0<0.  Sound and complete for linear real arithmetic;
   computed in Scheme.  Each closure prints its certificate.")
