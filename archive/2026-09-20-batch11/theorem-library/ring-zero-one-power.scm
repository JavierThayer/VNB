;;; ring-zero-one-power.scm -- four ring facts that were asserted, PROVEN.
;;;
;;;   ring-one-in          forall s. IS-RING(s) => ONE(s) in CARR(s)
;;;   bt-one-in-carr       the same statement verbatim, under binomial.scm's name
;;;   ring-mul-zero-left   forall s. IS-RING(s) => forall a in CARR(s). 0*a = 0
;;;   ring-mul-zero-right  forall s. IS-RING(s) => forall a in CARR(s). a*0 = 0
;;;   ring-power-zero      forall R, x.  RING-POWER(R,x,0) == ONE(R)
;;;
;;; ONE-IN.  (IN (ONE s) (CARR s)) is a literal conjunct of the generated IS-RING
;;; iff -- the `(constant ONE CARR)' clause -- so the proof is the projection
;;; shape of subtype-laws.scm's stl--project!: peel, unfold IS-RING in the
;;; hypothesis, split the conjunction, `ass'.  bt-one-in-carr (binomial.scm) is
;;; the same statement with the ring named R instead of s; it is proved here by
;;; the same driver so that both supports can be retired together.
;;;
;;; MUL-ZERO.  Lang, Algebra II.1, in four rewrites:
;;;     0*a = (0+0)*a = 0*a + 0*a          (ring-add-left-id, ring-right-dist)
;;; so 0*a is additively idempotent, and an idempotent of an abelian group is
;;; its identity -- abelian-group-idempotent-is-id-ring-additive-ag, the RING
;;; specialisation cancellation.scm builds, already in ADD/ZERO form.  The
;;; typing 0*a in CARR(s) is ring-carrier-closed-mul (op-typing.scm) at
;;; ring-zero-in.  The right-hand law mirrors it with ring-left-dist.
;;;
;;; POWER-ZERO.  RING-POWER is a functoid over MPOW through the view
;;; COMMUTATIVE-RING-MULTIPLICATIVE-CM; `mac' unfolds it in the goal, mpow-zero
;;; (the base equation def-by-nn-recursion installed, unguarded, `==') reduces
;;; MPOW(_,x,0) to IDEN of the view.  A `def-functor' view has NO precomputed
;;; slot projections (those come only from def-constructed-functor, via
;;; install-functor-projections!), so `slot' falls back to the GLOBAL IDEN
;;; accessor macete and lands NTH(3, view) -- the last-write-wins accessor
;;; index (matrix.scm:697).  The tuple is then opened by unfolding the view's
;;; own functoid, (LIST (CARR R) (MUL R) (ONE R)), and `nth-r' reads the third
;;; component: the fin-subset-monoid.scm pattern (fsm-iden).  The index is
;;; CHECKED, not trusted: the driver errors unless the goal after nth-r is
;;; literally ONE(R) == ONE(R), so a drifted global index cannot close this
;;; proof with the wrong component.  The statement is `==', so qrfl closes
;;; with no definedness owed.
;;;
;;; LOAD WINDOW.  Must load AFTER theorem-library/cancellation (which installs
;;; abelian-group-idempotent-is-id-ring-additive-ag via view-as-auto-specialize!)
;;; and after theorem-library/op-typing (ring-carrier-closed-mul); the other
;;; citations are structure-library axioms/definitions.  Must load BEFORE the
;;; earliest citer of any of the five: theorem-library/monalg-laws /
;;; euclidean-ideal-generator-proof / matunit-shift-proof / elem-actions-proof /
;;; elem-inverses-proof (see the report).  The slot directly after cancellation
;;; satisfies both.
;;;
;;; Helper prefix: rzp-.

(define (rzp-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (rzp-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** ring-zero-one-power: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w))) (newline))
                              (sequent-node-assumptions l)))
                  (proof-open-goals *ps*))
        (error "ring-zero-one-power: unfinished" name))))

;;; ---- ONE in the carrier: a conjunct of the definition -------------------

(define (rzp-prove-one-in! name var)
  (sp (make-wff `(FORALL ,var (IMPLIES (IS-RING ,var) (IN (ONE ,var) (CARR ,var))))))
  (rzp-peel!)
  (mac-h 'is-ring (list 'IS-RING var))
  (dk-split! (car (dk-asms)))
  (ass)
  (rzp-qed! name))

(rzp-prove-one-in! 'ring-one-in 's)
(topic! 'ring-one-in 'algebra)
(rzp-prove-one-in! 'bt-one-in-carr 'R)
(topic! 'bt-one-in-carr 'algebra)

;;; ---- 0*a = 0 and a*0 = 0 ---------------------------------------------------

;; SIDE is 'left (0*a) or 'right (a*0).
(define (rzp-prove-mul-zero! name side)
  (let* ((z    '(ZERO s))
         (prod (if (eq? side 'left) `((MUL s) ,z a) `((MUL s) a ,z)))
         (zz   `((ADD s) ,z ,z))
         (prod-zz (if (eq? side 'left) `((MUL s) ,zz a) `((MUL s) a ,zz)))
         (sum  `((ADD s) ,prod ,prod)))
    (sp (make-wff `(FORALL s (IMPLIES (IS-RING s)
                     (FORALL a (IMPLIES (IN a (CARR s))
                       (= ,prod ,z)))))))
    (rzp-peel!)
    (fact 'ring-zero-in 's)                             ; 0 in CARR(s)
    (if (eq? side 'left)
        (fact 'ring-carrier-closed-mul 's z 'a)         ; 0*a in CARR(s)
        (fact 'ring-carrier-closed-mul 's 'a z))        ; a*0 in CARR(s)
    (fact 'ring-add-left-id 's z)                       ; 0+0 = 0
    (if (eq? side 'left)
        (fact 'ring-right-dist 's z z 'a)               ; (0+0)*a = 0*a + 0*a
        (fact 'ring-left-dist 's 'a z z))               ; a*(0+0) = a*0 + a*0
    ;; prod + prod = prod
    (cut `(= ,sum ,prod))
    (subst `(= ,sum ,prod-zz))                          ; distributivity, reversed
    (subst `(= ,zz ,z))                                 ; 0+0 -> 0
    (rfl)                                               ; prod in CARR(s) witnesses definedness
    ;; an additive idempotent is the zero
    (fact 'abelian-group-idempotent-is-id-ring-additive-ag 's prod)
    (ass)
    (rzp-qed! name)))

(rzp-prove-mul-zero! 'ring-mul-zero-left 'left)
(topic! 'ring-mul-zero-left 'algebra)
(rzp-prove-mul-zero! 'ring-mul-zero-right 'right)
(topic! 'ring-mul-zero-right 'algebra)

;;; ---- x^0 = 1 ---------------------------------------------------------------

(sp (make-wff '(FORALL R (FORALL x (== (RING-POWER R x 0) (ONE R))))))
(rzp-peel!)
(mac 'RING-POWER)          ; MPOW(COMMUTATIVE-RING-MULTIPLICATIVE-CM R, x, 0) == ONE R
(mac 'mpow-zero)           ; IDEN(COMMUTATIVE-RING-MULTIPLICATIVE-CM R) == ONE R
(slot 'IDEN)               ; NTH(3, COMMUTATIVE-RING-MULTIPLICATIVE-CM R) == ONE R
(mac 'commutative-ring-multiplicative-cm)   ; NTH(3, LIST(CARR R, MUL R, ONE R)) == ONE R
(nth-r)                    ; ONE R == ONE R
(if (not (equal? (dk-goal) '(== (ONE R) (ONE R))))
    (error "ring-power-zero: the IDEN accessor index did not select ONE; goal is"
           (expression->string (dk-goal))))
(qrfl)
(rzp-qed! 'ring-power-zero)
(topic! 'ring-power-zero 'algebra)
