;;; rake-det-small.scm -- the small determinants, PROVEN (rake batch 5b-C, 2026-09-18).
;;;
;;; WHAT IS HERE -- eleven theorems, every one `proven modulo 0'.
;;;   interval-1-1      [1,1] = {1}                                  (new brick)
;;;   rmm-op            OPR(RING-MULTIPLICATIVE-MONOID R)  = MUL(R)  (view read-off)
;;;   rmm-iden          IDEN(RING-MULTIPLICATIVE-MONOID R) = ONE(R)  (view read-off)
;;;   ring-mpow-one     MPOW(RING-MULTIPLICATIVE-MONOID R, x, 1) = x (new brick)
;;;   minor-entry       the ENTRY read-off of MINOR                  (new brick)
;;;   det-1x1           structure-library/determinant.scm:86         RETIRE
;;;   det-2x2           structure-library/determinant.scm:95         RETIRE
;;;   identmat-minor    MINOR(I_{succ n},1,1,n) = I_n                (new brick)
;;;   mat-ring-one      structure-library/matrix.scm:566             RETIRE
;;;   det-identity-ind  det-identity with the NN binder outermost    (AUX)
;;;   det-identity      structure-library/determinant.scm:106        RETIRE
;;;
;;; THE NUMERAL <-> succ BRIDGE IS NOT THE OBSTACLE, and determinant.scm's header
;;; (the "COMPUTE-PHASE OBSTACLE" paragraph, :23) is STALE.  `det-cofactor' is keyed
;;; on DET(R, succ n, A), and one line
;;;     (have! '(= 1 (succ 0)) (lambda () (arith))) (subst '(= 1 (succ 0)))
;;; puts the goal in the shape the macete matches -- `arith' decides `succ' on a
;;; numeral.  What is left after the unfold is the SINGLETON SUM
;;;     FINSUM(RING-ADDITIVE-AG R, j |-> (-1)^(1+j) A(1,j) DET(R,0,MINOR(A,1,j,0)),
;;;            INTERVAL(1, succ 0))  =  A(1,1)
;;; and THAT wanted the bricks: `interval-1-1' (so the index set is the PAIR that
;;; `finsum-singleton' is stated over) and, for 2x2 and the identity, `minor-entry'
;;; (the value of an entry of a MINOR).
;;;
;;; THE SUMMAND'S DOMAIN IS WHY `finsum-congruence-q' APPEARS.  A VNB-LAMBDA carries
;;; its domain, so the cofactor summand over [1, succ n] is NOT a member of
;;; FUN(PAIR(1,1), CARR ag) and `finsum-singleton' cannot be cited at it directly.
;;; `finsum-congruence-q' has NO typing hypothesis at all, so it moves the sum onto a
;;; CONSTANT family with the right domain for one pointwise computation.  det-identity
;;; needs no such move: `finsum-single-support' takes the family it is given.
;;;
;;; MONOID-LEVEL `mpow-one' WAS MEASURED AND DECLINED.  It is one line from
;;; `monoid-right-id' -- and monoid.scm carries no warrant and no provenance wrap at
;;; all, so `monoid-assoc' / `monoid-left-id' / `monoid-right-id' are UNWARRANTED
;;; axioms: the proof came back `modulo {monoid-right-id} [trust: none]'.  The
;;; ring-level `ring-mpow-one' below reads OPR/IDEN through the view first and uses
;;; `ring-mul-right-id', which ring.scm stamps `definitional', so it is `modulo 0'.
;;;
;;; LOAD WINDOW [252, 345).
;;;   lo = 252, immediately after theorem-library/rake-mat-typing (251), the LATEST
;;;        citation: `minor-type', `det-in-carrier' and `rmm-carr' live there.  Next
;;;        are identmat-type (mat-typing-bundle, 250), finsum-singleton
;;;        (rake-finsum-core, 248), finsum-interval-peel (rake-finsum-laws2, 247),
;;;        finsum-congruence-q (rake-finsum-laws, 246), interval-card-in-nn (245),
;;;        entry-of-matof (tuple-tabulation, 240), matrix-entry-extensionality
;;;        (tuple-extensionality, 239), ring-neg-neg / ring-neg-mul-left / mpow-type
;;;        (rake-algebra2, 229), nn-le-antisym (nn-order-proof, 227), nn-succ-inj
;;;        (nn-parity-proof, 214), ring-one-in / ring-mul-zero-* (ring-zero-one-power,
;;;        212), finsum-single-support (203), op-typing (201), entry-in-carrier (173),
;;;        one-in-interval-1 (171), ag-view-read-offs (160).
;;;   hi = 345: theorem-library/mat-ring-proof cites `mat-ring-one' as a MACETE
;;;        (:143, :178), so this file must load before it if that support is retired.
;;;        Nothing cites det-1x1, det-2x2 or det-identity, and the four new bricks
;;;        are cited nowhere else in the tree.
;;;
;;; WHY THE IDENTMAT ENTRY READ-OFF IS INLINE.  `entry-of-identmat',
;;; `identmat-entry-diag' and `identmat-entry-off' are PROVEN, in
;;; theorem-library/elem-entry-readoffs (346) -- BELOW mat-ring-proof (345).  Citing
;;; them would push lo to 347 and strand the `mat-ring-one' retirement.  So
;;; `r6c-identmat-entry!' derives the entry equation inline from `entry-of-matof',
;;; which is rake-identmat.scm's `rkd-identmat-entry!' and its reason, verbatim.
;;; If the integrator moves elem-entry-readoffs into [235, 332) -- that file's own
;;; report says it can -- the lane collapses to one citation.
;;;
;;; Helper prefix: r6c-.

;;; ---- the file's own kit ------------------------------------------------
;;; The IF resolver is rake-mat-typing.scm's rkm- kit, copied (it is file-local
;;; there; it belongs in driver-kit.scm -- see the report).

(define (r6c-if-branch! true? ifterm thunk)
  (let* ((c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "r6c-if-branch!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (ass)
    (dk-focus! (car mains))
    (subst (list '= ifterm val))
    (thunk)))

(define (r6c-case-if! ifterm k)
  (let ((c (cadr ifterm)))
    (use-em c
      (lambda () (r6c-if-branch! #t  ifterm (lambda () (k (caddr  ifterm)))))
      (lambda () (r6c-if-branch! #f ifterm (lambda () (k (cadddr ifterm))))))))

(define (r6c-widen! i lo hi)
  (fact 'interval-elt-in-nn 1 lo i)
  (fact 'interval-lo 1 lo i)
  (fact 'interval-hi 1 lo i)
  (fact 'nn-le-trans-guarded i lo hi)
  (fact 'interval-mem-intro 1 hi i))

(define (r6c-succ-widen! i b)
  (fact 'interval-elt-in-nn 1 b i)
  (fact 'interval-lo 1 b i)
  (fact 'interval-hi 1 b i)
  (fact 'nn-succ-closed i)
  (fact 'nn-succ-closed b)
  (fact 'nn-one-le-succ i)
  (fact 'nn-succ-mono i b)
  (fact 'interval-mem-intro 1 (list 'succ b) (list 'succ i)))

(define (r6c-skip-widen! v i n)
  (if (equal? v (list 'succ i))
      (r6c-succ-widen! i n)
      (begin (fact 'nn-succ-closed n)
             (fact 'nn-le-succ n)
             (r6c-widen! v n (list 'succ n)))))

;; lam-t opens TWO leaves (the domain's sethood and the pointwise typing);
;; close the first by `ass' and hand the second to THUNK.
(define (r6c-lam-t! thunk)
  (let* ((opened (dk-opened (lambda () (lam-t))))
         (sets   (filter (lambda (l) (let ((g (dk-goal-of l)))
                                       (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
                         opened))
         (typs   (filter (lambda (l) (not (memq l sets))) opened)))
    (if (not (and (= 1 (length sets)) (= 1 (length typs))))
        (error "r6c-lam-t!: lam-t opened"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car sets)) (ass)
    (dk-focus! (car typs))
    (thunk)))

(define r6c-ag   '(RING-ADDITIVE-AG R))
(define r6c-mm   '(RING-MULTIPLICATIVE-MONOID R))
(define r6c-sign '((NEG R) (ONE R)))

;; (-1)(-1) = 1, rewritten in the goal.  Needs ONE(R) and (NEG R)(ONE R) typed.
(define (r6c-sign-square!)
  (fact 'ring-neg-mul-left 'R '(ONE R) r6c-sign)
  (subst (list '= (list '(MUL R) r6c-sign r6c-sign)
               (list '(NEG R) (list '(MUL R) '(ONE R) r6c-sign))))
  (fact 'ring-mul-left-id 'R r6c-sign)
  (subst (list '= (list '(MUL R) '(ONE R) r6c-sign) r6c-sign))
  (fact 'ring-neg-neg 'R '(ONE R))
  (subst (list '= (list '(NEG R) r6c-sign) '(ONE R))))


;; (r6c-close-in!) -- goal (IN (IF c a b) SET) with c undecided: split on c,
;; resolve the IF on each side, and close from the context.
(define (r6c-close-in!)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'IF))
        (r6c-case-if! (cadr g) (lambda (v) (r6c-close-in!)))
        (ass))))

;; (r6c-identmat-entry! RNG DIM I J) -- land
;;     ENTRY(IDENTMAT(RNG,DIM), I, J) = IF (I = J) then ONE(RNG) else ZERO(RNG)
;; with (IN DIM NN), (IN I (INTERVAL 1 DIM)), (IN J (INTERVAL 1 DIM)),
;; ONE(RNG) and ZERO(RNG) typed, in context.
;;
;; This is `entry-of-identmat' (theorem-library/elem-entry-readoffs.scm:878)
;; INLINE, and the reason is load order, exactly as rake-identmat.scm's
;; `rkd-identmat-entry!' has it: elem-entry-readoffs sits at position 346,
;; BELOW mat-ring-proof (345) -- so a file that cites it cannot also retire
;; `mat-ring-one', which mat-ring-proof uses as a macete.  Citing the three
;; read-offs would push this file's lo from 252 to 347 and strand that
;; retirement.  IDENTMAT is a MATOF, so entry-of-matof plus one `lam-b-h'
;; gives the equation directly.
(define (r6c-identmat-entry! rng dim i j)
  (let ((tgt (list '= (list 'ENTRY (list 'IDENTMAT rng dim) i j)
                   (list 'IF (list '= i j) (list 'ONE rng) (list 'ZERO rng)))))
    (if (not (dk-asm? tgt))
        (begin
          (have! tgt
            (lambda ()
              (mac 'IDENTMAT)
              (let* ((e   (cadr (dk-goal)))
                     (mf  (cadr e))
                     (lam (cadddr mf)))
                (if (not (and (pair? mf) (eq? (car mf) 'MATOF)))
                    (error "r6c-identmat-entry!: IDENTMAT did not unfold to a MATOF"
                           (expression->string (dk-goal))))
                (have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ (list 'INTERVAL 1 dim))
                         (list 'FORALL 'v_ (list 'IMPLIES (list 'IN 'v_ (list 'INTERVAL 1 dim))
                           (list 'IN (list lam 'u_ 'v_) 'SET)))))
                  (lambda ()
                    (dk-peel!)
                    (fact 'membership-implies-sethood (list 'ONE rng) (list 'CARR rng))
                    (fact 'membership-implies-sethood (list 'ZERO rng) (list 'CARR rng))
                    (lam-b)
                    (r6c-close-in!)))
                (lam-b-h (dk-fact! 'entry-of-matof dim dim lam i j))
                (ass))))
          (dk-focus-having! tgt)))
    tgt))

(define (r6c-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** rake-det-small: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))))
  (qed name))

;;; =====================================================================
;;; (1) interval-1-1 -- INTERVAL(1,1) = PAIR(1,1).
;;; Class-extensionality over the membership iff, exactly as
;;; interval-1-0-empty (theorem-library/mat-basics.scm:480) does it: forward,
;;; 1 <= x <= 1 and nn-le-antisym give x = 1; backward, pairing-membership
;;; gives x = 1 and one-in-interval-1 puts it back.
;;; =====================================================================
(sp (make-wff '(= (INTERVAL 1 1) (PAIR 1 1))))
(fact 'nn-one-in)
(fact 'membership-implies-sethood 1 'NN)
(have! '(AND (IN 1 SET) (IN 1 SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'pairing 1 1)
(have! '(FORALL x_ (IFF (IN x_ (INTERVAL 1 1)) (IN x_ (PAIR 1 1))))
  (lambda ()
    (di)
    (for-each
     (lambda (l)
       (dk-focus! l)
       (if (equal? (dk-goal) '(IN x_ (PAIR 1 1)))
           (begin
             (fact 'interval-elt-in-nn 1 1 'x_)
             (fact 'interval-lo 1 1 'x_)
             (fact 'interval-hi 1 1 'x_)
             (fact 'nn-le-antisym 'x_ 1)
             (fact 'pairing-membership 1 1 'x_)
             (prop))
           (begin
             (fact 'pairing-membership 1 1 'x_)
             (have! '(= x_ 1) (lambda () (prop)))
             (subst '(= x_ 1))
             (fact 'one-in-interval-1)
             (ass))))
     (dk-opened (lambda () (di))))))
(fact 'class-extensionality '(INTERVAL 1 1) '(PAIR 1 1))
(ass)
(r6c-done! 'interval-1-1)
(gloss! 'interval-1-1
  "The index interval [1,1] is the singleton {1}.  The companion of
   interval-1-0-empty, and what lets a one-term FINSUM over [1,1] be read by
   finsum-singleton, which is stated over PAIR(x,x).")
(topic! 'interval-1-1 'plumbing)

;;; =====================================================================
;;; (2) the RING-MULTIPLICATIVE-MONOID view read-offs.  `rmm-carr' is proven
;;; in theorem-library/rake-mat-typing.scm; OPR and IDEN were missing.  Driver:
;;; ag-view-read-offs.scm's `avr-read-off!' (the source accessor's name differs
;;; from the target's, so the right-hand side is untouched and the typing
;;; conjunct closes `rfl' directly).
;;; =====================================================================
(sp (make-wff '(FORALL R (IMPLIES (IS-RING R)
                 (= (OPR (RING-MULTIPLICATIVE-MONOID R)) (MUL R))))))
(di) (di)
(mac-h 'is-ring '(IS-RING R))
(dk-split-all!)
(slot 'OPR) (mac 'RING-MULTIPLICATIVE-MONOID) (nth-r) (rfl)
(r6c-done! 'rmm-op)
(topic! 'rmm-op 'plumbing)

(sp (make-wff '(FORALL R (IMPLIES (IS-RING R)
                 (= (IDEN (RING-MULTIPLICATIVE-MONOID R)) (ONE R))))))
(di) (di)
(mac-h 'is-ring '(IS-RING R))
(dk-split-all!)
(slot 'IDEN) (mac 'RING-MULTIPLICATIVE-MONOID) (nth-r) (rfl)
(r6c-done! 'rmm-iden)
(topic! 'rmm-iden 'plumbing)

;;; =====================================================================
;;; (3) ring-mpow-one -- x^1 = x in a ring's multiplicative monoid.
;;; mpow-succ at 0, mpow-zero, and the ring's right identity read through the
;;; view.  (The monoid-level `mpow-one' is an asserted axiom and stays: see the
;;; header.)
;;; =====================================================================
(sp (make-wff '(FORALL R (IMPLIES (IS-RING R)
                 (FORALL x (IMPLIES (IN x (CARR R))
                   (= (MPOW (RING-MULTIPLICATIVE-MONOID R) x 1) x)))))))
(dk-peel!)
(fact 'nn-zero-in)
(have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(mac 'mpow-succ)
(mac 'mpow-zero)
(fact 'rmm-op 'R)
(fact 'rmm-iden 'R)
(subst '(= (OPR (RING-MULTIPLICATIVE-MONOID R)) (MUL R)))
(subst '(= (IDEN (RING-MULTIPLICATIVE-MONOID R)) (ONE R)))
(fact 'ring-mul-right-id 'R 'x)
(ass)
(r6c-done! 'ring-mpow-one)
(topic! 'ring-mpow-one 'algebra)

;;; =====================================================================
;;; (4) minor-entry -- the ENTRY read-off of MINOR:
;;;       ENTRY(MINOR(S,p,q,n), u, v) = ENTRY(S, skip(u,p), skip(v,q))
;;; with skip(u,p) = u if u < p else succ u.  The FORWARD route of
;;; elem-entry-readoffs.scm: `entry-of-matof' is cited and its equation is
;;; beta-reduced in the HYPOTHESIS (`lam-b-h'), so no definedness is owed --
;;; the goal-side route would leave `t = t' with t a tabulated entry, which
;;; `rfl' refuses.  entry-of-matof's pointwise-sethood side condition is
;;; minor-type's IF-tower argument, run here over SET instead of CARR(R).
;;; The outer index binders are u_ / v_: the MINOR functoid's own lambda binds
;;; i and j, and entry-of-matof-guarded spells its indices u_ / v_ for the same
;;; reason.
;;; =====================================================================
(define r6c-minor-entry-stmt
  (forall-guarded '(R S p q n u_ v_)
    (list '(IS-RING R) '(IN n NN) '(IN S (MAT (succ n) (succ n) (CARR R)))
          '(IN u_ (INTERVAL 1 n)) '(IN v_ (INTERVAL 1 n)))
    '(= (ENTRY (MINOR S p q n) u_ v_)
        (ENTRY S (IF (< u_ p) u_ (succ u_))
                 (IF (< v_ q) v_ (succ v_))))))
(sp (make-wff r6c-minor-entry-stmt))
(dk-peel!)
(mac 'MINOR)
(let* ((gl (dk-goal))
       (mf (cadr gl))                     ; (ENTRY (MATOF n n G) u_ v_)
       (mt (cadr mf))                     ; (MATOF n n G)
       (gg (cadddr mt)))
  (have! (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ (INTERVAL 1 n))
           (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ (INTERVAL 1 n))
             (list 'IN (list gg 'i_ 'j_) 'SET)))))
    (lambda ()
      (dk-peel!)
      (lam-b)
      (let* ((e   (cadr (dk-goal)))
             (rif (caddr e))
             (i0  (caddr rif)))
        (r6c-case-if! rif
          (lambda (ri)
            (let* ((cif2 (cadddr (cadr (dk-goal))))
                   (j0   (caddr cif2)))
              (r6c-case-if! cif2
                (lambda (ci)
                  (r6c-skip-widen! ri i0 'n)
                  (r6c-skip-widen! ci j0 'n)
                  (fact 'entry-in-carrier '(succ n) '(succ n) '(CARR R) 'S ri ci)
                  (fact 'membership-implies-sethood (list 'ENTRY 'S ri ci) '(CARR R))
                  (ass)))))))))
  (fact 'entry-of-matof 'n 'n gg 'u_ 'v_)
  (lam-b-h (list '= (list 'ENTRY mt 'u_ 'v_) (list gg 'u_ 'v_)))
  (ass))
(r6c-done! 'minor-entry)
(gloss! 'minor-entry
  "The entries of MINOR(S,p,q,n): deleting row p and column q re-indexes by
   u |-> u if u < p else succ u, and likewise for the column.  The read-off
   companion of minor-type.")
(topic! 'minor-entry 'algebra)

;;; =====================================================================
;;; (5) det-1x1 -- structure-library/determinant.scm:86, copied literally.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(R A)
    (list '(IS-RING R) '(IN A (MAT 1 1 (CARR R))))
    '(= (DET R 1 A) (ENTRY A 1 1)))))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'nn-succ-closed 0)
(fact 'nn-one-in)
(have! '(= 1 (succ 0)) (lambda () (arith)))
(fact 'eq-sym 1 '(succ 0))
(have! '(IN A (MAT (succ 0) (succ 0) (CARR R)))
       (lambda () (subst '(= (succ 0) 1)) (ass)))
(fact 'membership-implies-sethood 1 'NN)
(have! '(AND (IN 1 SET) (IN 1 SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'pairing 1 1)
(fact 'card-singleton 1)
(have! '(IN (CARD (PAIR 1 1)) NN)
       (lambda () (subst '(= (CARD (PAIR 1 1)) (succ 0))) (ass)))
(fact 'ring-additive-ag-is-abelian-group 'R)
(fact 'ring-multiplicative-monoid-is-monoid 'R)
(fact 'ras-carr 'R)
(fact 'rmm-op 'R)
(fact 'rmm-iden 'R)
(fact 'ring-one-in 'R)
(fact 'ring-neg-in-carr 'R '(ONE R))
(fact 'nn-le-refl '(succ 0))
(fact 'nn-one-le-succ 0)
(fact 'interval-mem-intro 1 '(succ 0) '(succ 0))
(fact 'entry-in-carrier '(succ 0) '(succ 0) '(CARR R) 'A '(succ 0) '(succ 0))
(fact 'minor-type 'R 'A '(succ 0) '(succ 0) 0)
(have! '(IN (ENTRY A 1 1) (CARR R))
       (lambda () (subst '(= 1 (succ 0))) (ass)))
(fact 'interval-1-1)

(subst '(= 1 (succ 0)))
(mac 'det-cofactor)
(subst '(= (succ 0) 1))
(subst '(= (INTERVAL 1 1) (PAIR 1 1)))

(let* ((gl    (dk-goal))
       (fs    (cadr gl))                       ; (FINSUM ag lam pr)
       (lam   (caddr fs))
       (const (list 'VNB-LAMBDA 'j '(PAIR 1 1) '(ENTRY A 1 1))))
  ;; the summand agrees with the constant family on {1}
  (have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ (PAIR 1 1))
                                 (list '= (list lam 'z_) (list const 'z_))))
    (lambda ()
      (di)
      (lam-b)
      (have! '(= z_ 1) (lambda () (fact 'pairing-membership 1 1 'z_) (prop)))
      (have! '(= z_ (succ 0)) (lambda () (subst '(= z_ 1)) (ass)))
      (subst '(= z_ (succ 0)))
      (subst '(= 1 (succ 0)))
      (mac 'mpow-succ)
      (mac 'mpow-succ)
      (mac 'mpow-zero)
      (subst (list '= (list 'OPR r6c-mm) '(MUL R)))
      (subst (list '= (list 'IDEN r6c-mm) '(ONE R)))
      (fact 'det-zero 'R '(MINOR A (succ 0) (succ 0) 0))
      (subst '(== (DET R 0 (MINOR A (succ 0) (succ 0) 0)) (ONE R)))
      (fact 'ring-mul-right-id 'R '(ENTRY A (succ 0) (succ 0)))
      (subst '(= ((MUL R) (ENTRY A (succ 0) (succ 0)) (ONE R)) (ENTRY A (succ 0) (succ 0))))
      (fact 'ring-mul-right-id 'R r6c-sign)
      (subst (list '= (list '(MUL R) r6c-sign '(ONE R)) r6c-sign))
      (r6c-sign-square!)
      (fact 'ring-mul-left-id 'R '(ENTRY A (succ 0) (succ 0)))
      (subst '(= ((MUL R) (ONE R) (ENTRY A (succ 0) (succ 0))) (ENTRY A (succ 0) (succ 0))))
      (rfl)))

  (fact 'finsum-congruence-q r6c-ag '(PAIR 1 1) lam const)
  (subst (list '== (list 'FINSUM r6c-ag lam '(PAIR 1 1))
               (list 'FINSUM r6c-ag const '(PAIR 1 1))))

  (have! (list 'IN const (list 'FUN '(PAIR 1 1) (list 'CARR r6c-ag)))
    (lambda ()
      (r6c-lam-t!
       (lambda ()
         (dk-peel!)
         (subst (list '= (list 'CARR r6c-ag) '(CARR R)))
         (ass)))))

  (fact 'finsum-singleton r6c-ag 1 const)
  (subst (list '= (list 'FINSUM r6c-ag const '(PAIR 1 1)) (list const 1)))
  (fact 'one-in-interval-1)
  (have! '(IN 1 (PAIR 1 1)) (lambda () (subst '(= (PAIR 1 1) (INTERVAL 1 1))) (ass)))
  (lam-b)
  (rfl))
(r6c-done! 'det-1x1)
(topic! 'det-1x1 'algebra)

;;; =====================================================================
;;; (6) det-2x2 -- structure-library/determinant.scm:95, copied literally.
;;;
;;; DET(R,2,A) = A(1,1)A(2,2) - A(1,2)A(2,1).  Two levels of the recursion:
;;; det-cofactor at n = 1 gives a FINSUM over [1, succ 1]; finsum-interval-peel
;;; splits it into the sum over [1,1] and the j = succ 1 term.  The [1,1] sum
;;; goes through interval-1-1 + finsum-congruence-q + finsum-singleton as in
;;; det-1x1; each term's inner determinant is det-1x1 at the MINOR, whose entry
;;; is read by minor-entry with both IF conditions decided by `arith'.
;;; Signs: (-1)^2 = 1 on the first term, (-1)^3 = -1 on the second.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(R A)
    (list '(IS-RING R) '(IN A (MAT 2 2 (CARR R))))
    '(= (DET R 2 A)
        ((ADD R) ((MUL R) (ENTRY A 1 1) (ENTRY A 2 2))
                 ((NEG R) ((MUL R) (ENTRY A 1 2) (ENTRY A 2 1))))))))
(dk-peel!)

;; --- numerals, bridges, and the plumbing every lane below inherits
(fact 'nn-zero-in)
(fact 'nn-one-in)
(fact 'nn-succ-closed 1)
(have! '(= 2 (succ 1)) (lambda () (arith)))
(fact 'eq-sym 2 '(succ 1))
(have! '(IN A (MAT (succ 1) (succ 1) (CARR R)))
       (lambda () (subst '(= (succ 1) 2)) (ass)))
(have! '(NOT (< 1 1)) (lambda () (arith)))
(have! '(< 1 2) (lambda () (arith)))
(have! '(< 1 (succ 1)) (lambda () (subst '(= (succ 1) 2)) (ass)))
(fact 'membership-implies-sethood 1 'NN)
(have! '(AND (IN 1 SET) (IN 1 SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'pairing 1 1)
(fact 'card-singleton 1)
(fact 'nn-zero-in)
(fact 'nn-succ-closed 0)
(have! '(= 1 (succ 0)) (lambda () (arith)))
(have! '(IN (CARD (PAIR 1 1)) NN)
       (lambda () (subst '(= (CARD (PAIR 1 1)) (succ 0))) (ass)))
(fact 'ring-additive-ag-is-abelian-group 'R)
(fact 'ring-multiplicative-monoid-is-monoid 'R)
(fact 'ras-carr 'R)
(fact 'ras-op 'R)
(fact 'rmm-op 'R)
(fact 'rmm-iden 'R)
(fact 'rmm-carr 'R)
(fact 'eq-sym (list 'CARR r6c-mm) '(CARR R))
(fact 'ring-one-in 'R)
(fact 'ring-neg-in-carr 'R '(ONE R))
(have! (list 'IN r6c-sign (list 'CARR r6c-mm))
       (lambda () (subst (list '= (list 'CARR r6c-mm) '(CARR R))) (ass)))
(fact 'nn-le-refl 1)
(fact 'nn-le-refl '(succ 1))
(fact 'nn-one-le-succ 1)
(fact 'interval-mem-intro 1 '(succ 1) 1)
(fact 'interval-mem-intro 1 '(succ 1) '(succ 1))
(fact 'interval-in-set 1 '(succ 1))
(fact 'interval-card-in-nn 1 '(succ 1))
(fact 'interval-1-1)
(fact 'one-in-interval-1)                     ; minor-entry's two index guards

;; --- the cofactor expansion at n = 1
(subst '(= 2 (succ 1)))
(mac 'det-cofactor)

(let* ((gl   (dk-goal))
       (fs   (cadr gl))
       (lam2 (caddr fs))
       (v1   '((MUL R) (ENTRY A 1 1) (ENTRY A (succ 1) (succ 1))))
       (w2   '((MUL R) (ENTRY A 1 (succ 1)) (ENTRY A (succ 1) 1)))
       (k1   (list 'VNB-LAMBDA 'j '(PAIR 1 1) v1)))

  ;; (a) the summand is a function [1, succ 1] -> CARR(ag)
  (have! (list 'IN lam2 (list 'FUN '(INTERVAL 1 (succ 1)) (list 'CARR r6c-ag)))
    (lambda ()
      (r6c-lam-t!
       (lambda ()
         (let ((j (dk-di-var!)))
           (fact 'interval-elt-in-nn 1 '(succ 1) j)
           (fact 'nn-succ-closed j)
           (fact 'mpow-type r6c-mm r6c-sign (list 'succ j))
           (have! (list 'IN (list 'MPOW r6c-mm r6c-sign (list 'succ j)) '(CARR R))
             (lambda () (subst (list '= '(CARR R) (list 'CARR r6c-mm))) (ass)))
           (dk-focus-having! (list 'IN (list 'MPOW r6c-mm r6c-sign (list 'succ j)) '(CARR R)))
           (fact 'entry-in-carrier '(succ 1) '(succ 1) '(CARR R) 'A 1 j)
           (fact 'minor-type 'R 'A 1 j 1)
           (fact 'det-in-carrier 'R 1 (list 'MINOR 'A 1 j 1))
           (fact 'ring-carrier-closed-mul 'R (list 'ENTRY 'A 1 j)
                 (list 'DET 'R 1 (list 'MINOR 'A 1 j 1)))
           (fact 'ring-carrier-closed-mul 'R (list 'MPOW r6c-mm r6c-sign (list 'succ j))
                 (list '(MUL R) (list 'ENTRY 'A 1 j)
                       (list 'DET 'R 1 (list 'MINOR 'A 1 j 1))))
           (subst (list '= (list 'CARR r6c-ag) '(CARR R)))
           (ass))))))
  (dk-focus-having! (list 'IN lam2 (list 'FUN '(INTERVAL 1 (succ 1)) (list 'CARR r6c-ag))))

  ;; (b) peel the top index
  (fact 'finsum-interval-peel r6c-ag 1 lam2)
  (subst (list '= (list 'FINSUM r6c-ag lam2 '(INTERVAL 1 (succ 1)))
               (list (list 'OPR r6c-ag)
                     (list 'FINSUM r6c-ag lam2 '(INTERVAL 1 1))
                     (list lam2 '(succ 1)))))

  ;; (c) the j = 1 term, through the singleton sum
  (subst '(= (INTERVAL 1 1) (PAIR 1 1)))
  (have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ (PAIR 1 1))
                                 (list '= (list lam2 'z_) (list k1 'z_))))
    (lambda ()
      (di)
      ;; lam2's domain is [1, succ 1] and z_ is typed only in {1}, so the beta
      ;; would OWE (IN z_ [1, succ 1]).  Land it first (CLAUDE.md: peel and type,
      ;; THEN beta).
      (have! '(= z_ 1) (lambda () (fact 'pairing-membership 1 1 'z_) (prop)))
      (have! '(IN z_ (INTERVAL 1 (succ 1)))
             (lambda () (subst '(= z_ 1)) (ass)))
      (lam-b)
      (subst '(= z_ 1))
      ;; (-1)^(1+1)
      (mac 'mpow-succ)
      (fact 'ring-mpow-one 'R r6c-sign)
      (subst (list '= (list 'MPOW r6c-mm r6c-sign 1) r6c-sign))
      (subst (list '= (list 'OPR r6c-mm) '(MUL R)))
      ;; the inner 1x1 determinant and its entry
      (fact 'minor-type 'R 'A 1 1 1)
      (fact 'det-1x1 'R '(MINOR A 1 1 1))
      (subst '(= (DET R 1 (MINOR A 1 1 1)) (ENTRY (MINOR A 1 1 1) 1 1)))
      (fact 'minor-entry 'R 'A 1 1 1 1 1)
      (subst '(= (ENTRY (MINOR A 1 1 1) 1 1)
                 (ENTRY A (IF (< 1 1) 1 (succ 1)) (IF (< 1 1) 1 (succ 1)))))
      (r6c-if-branch! #f '(IF (< 1 1) 1 (succ 1))
        (lambda ()
          (r6c-sign-square!)
          (fact 'entry-in-carrier '(succ 1) '(succ 1) '(CARR R) 'A 1 1)
          (fact 'entry-in-carrier '(succ 1) '(succ 1) '(CARR R) 'A '(succ 1) '(succ 1))
          (fact 'ring-carrier-closed-mul 'R '(ENTRY A 1 1) '(ENTRY A (succ 1) (succ 1)))
          (fact 'ring-mul-left-id 'R v1)
          (subst (list '= (list '(MUL R) '(ONE R) v1) v1))
          (rfl)))))
  (dk-focus-having! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ (PAIR 1 1))
                                            (list '= (list lam2 'z_) (list k1 'z_)))))
  (fact 'finsum-congruence-q r6c-ag '(PAIR 1 1) lam2 k1)
  (subst (list '== (list 'FINSUM r6c-ag lam2 '(PAIR 1 1))
               (list 'FINSUM r6c-ag k1 '(PAIR 1 1))))
  (fact 'entry-in-carrier '(succ 1) '(succ 1) '(CARR R) 'A 1 1)
  (fact 'entry-in-carrier '(succ 1) '(succ 1) '(CARR R) 'A '(succ 1) '(succ 1))
  (fact 'ring-carrier-closed-mul 'R '(ENTRY A 1 1) '(ENTRY A (succ 1) (succ 1)))
  (have! (list 'IN k1 (list 'FUN '(PAIR 1 1) (list 'CARR r6c-ag)))
    (lambda ()
      (r6c-lam-t!
       (lambda ()
         (dk-peel!)
         (subst (list '= (list 'CARR r6c-ag) '(CARR R)))
         (ass)))))
  (dk-focus-having! (list 'IN k1 (list 'FUN '(PAIR 1 1) (list 'CARR r6c-ag))))
  (fact 'finsum-singleton r6c-ag 1 k1)
  (subst (list '= (list 'FINSUM r6c-ag k1 '(PAIR 1 1)) (list k1 1)))
  (fact 'one-in-interval-1)
  (have! '(IN 1 (PAIR 1 1)) (lambda () (subst '(= (PAIR 1 1) (INTERVAL 1 1))) (ass)))
  (lam-b)

  ;; (d) the j = succ 1 term.  The `lam-b' above already reduced lam2(succ 1)
  ;; too -- one beta step takes every licensed redex in the goal.
  (mac 'mpow-succ)
  (mac 'mpow-succ)
  (fact 'ring-mpow-one 'R r6c-sign)
  (subst (list '= (list 'MPOW r6c-mm r6c-sign 1) r6c-sign))
  (subst (list '= (list 'OPR r6c-mm) '(MUL R)))
  (fact 'minor-type 'R 'A 1 '(succ 1) 1)
  (fact 'det-1x1 'R '(MINOR A 1 (succ 1) 1))
  (subst '(= (DET R 1 (MINOR A 1 (succ 1) 1)) (ENTRY (MINOR A 1 (succ 1) 1) 1 1)))
  (fact 'minor-entry 'R 'A 1 '(succ 1) 1 1 1)
  (subst '(= (ENTRY (MINOR A 1 (succ 1) 1) 1 1)
             (ENTRY A (IF (< 1 1) 1 (succ 1)) (IF (< 1 (succ 1)) 1 (succ 1)))))
  (r6c-if-branch! #f '(IF (< 1 1) 1 (succ 1))
    (lambda ()
      (r6c-if-branch! #t '(IF (< 1 (succ 1)) 1 (succ 1))
        (lambda ()
          (r6c-sign-square!)
          (fact 'entry-in-carrier '(succ 1) '(succ 1) '(CARR R) 'A 1 '(succ 1))
          (fact 'entry-in-carrier '(succ 1) '(succ 1) '(CARR R) 'A '(succ 1) 1)
          (fact 'ring-carrier-closed-mul 'R '(ENTRY A 1 (succ 1)) '(ENTRY A (succ 1) 1))
          (fact 'ring-mul-right-id 'R r6c-sign)
          (subst (list '= (list '(MUL R) r6c-sign '(ONE R)) r6c-sign))
          (fact 'ring-neg-mul-left 'R '(ONE R) w2)
          (subst (list '= (list '(MUL R) r6c-sign w2)
                       (list '(NEG R) (list '(MUL R) '(ONE R) w2))))
          (fact 'ring-mul-left-id 'R w2)
          (subst (list '= (list '(MUL R) '(ONE R) w2) w2))
          ;; (e) the outer OPR is the ring's ADD.  `rfl' is the definedness
          ;; predicate, so the sum has to be TYPED before it will certify t = t.
          (subst (list '= (list 'OPR r6c-ag) '(ADD R)))
          (fact 'ring-neg-in-carr 'R w2)
          (fact 'ring-add-closed 'R v1 (list '(NEG R) w2))
          (rfl))))))
(r6c-done! 'det-2x2)
(topic! 'det-2x2 'algebra)

;;; 1 <= v on NN makes v < 1 impossible: `<' is the def-predicate
;;; (AND (<= x y) (NOT (= x y))), so its unfold plus nn-le-antisym closes it.
(define (r6c-not-lt-one! v)
  (have! (list 'NOT (list '< v 1))
    (lambda ()
      (di)
      (fact '< v 1)
      (have! (list '<= v 1) (lambda () (prop)))
      (fact 'nn-le-antisym v 1)
      (have! (list 'NOT (list '= v 1)) (lambda () (prop)))
      (ai (list 'NOT (list '= v 1))))))

;;; ---- identmat-minor ----------------------------------------------------
(define r6c-idm-sn '(IDENTMAT R (succ n)))
(define r6c-idm-n  '(IDENTMAT R n))
(define r6c-min    '(MINOR (IDENTMAT R (succ n)) 1 1 n))

(sp (make-wff
  (forall-guarded '(R n)
    (list '(IS-RING R) '(IN n NN))
    '(= (MINOR (IDENTMAT R (succ n)) 1 1 n) (IDENTMAT R n)))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)
(fact 'ring-one-in 'R)
(fact 'ring-zero-in 'R)
(fact 'identmat-type 'R '(succ n))
(fact 'identmat-type 'R 'n)
(fact 'minor-type 'R r6c-idm-sn 1 1 'n)

(have! (list 'FORALL 'i (list 'IMPLIES '(IN i (INTERVAL 1 n))
         (list 'FORALL 'j (list 'IMPLIES '(IN j (INTERVAL 1 n))
           (list '= (list 'ENTRY r6c-min 'i 'j)
                    (list 'ENTRY r6c-idm-n 'i 'j))))))
  (lambda ()
    (dk-peel!)
    (fact 'interval-elt-in-nn 1 'n 'i)
    (fact 'interval-elt-in-nn 1 'n 'j)
    (fact 'interval-lo 1 'n 'i)
    (fact 'interval-lo 1 'n 'j)
    (r6c-not-lt-one! 'i)
    (r6c-not-lt-one! 'j)
    (r6c-succ-widen! 'i 'n)
    (r6c-succ-widen! 'j 'n)
    (fact 'minor-entry 'R r6c-idm-sn 1 1 'n 'i 'j)
    (subst (list '= (list 'ENTRY r6c-min 'i 'j)
                 (list 'ENTRY r6c-idm-sn '(IF (< i 1) i (succ i)) '(IF (< j 1) j (succ j)))))
    (r6c-if-branch! #f '(IF (< i 1) i (succ i))
      (lambda ()
        (r6c-if-branch! #f '(IF (< j 1) j (succ j))
          (lambda ()
            (r6c-identmat-entry! 'R '(succ n) '(succ i) '(succ j))
            (r6c-identmat-entry! 'R 'n 'i 'j)
            (subst (list '= (list 'ENTRY r6c-idm-sn '(succ i) '(succ j))
                         '(IF (= (succ i) (succ j)) (ONE R) (ZERO R))))
            (subst (list '= (list 'ENTRY r6c-idm-n 'i 'j)
                         '(IF (= i j) (ONE R) (ZERO R))))
            (use-em '(= i j)
              (lambda ()
                (have! '(= (succ i) (succ j)) (lambda () (subst '(= i j)) (rfl)))
                (r6c-if-branch! #t '(IF (= (succ i) (succ j)) (ONE R) (ZERO R))
                  (lambda ()
                    (r6c-if-branch! #t '(IF (= i j) (ONE R) (ZERO R))
                      (lambda () (rfl))))))
              (lambda ()
                (have! '(NOT (= (succ i) (succ j)))
                       (lambda () (di) (fact 'nn-succ-inj 'i 'j) (ai '(NOT (= i j)))))
                (r6c-if-branch! #f '(IF (= (succ i) (succ j)) (ONE R) (ZERO R))
                  (lambda ()
                    (r6c-if-branch! #f '(IF (= i j) (ONE R) (ZERO R))
                      (lambda () (rfl)))))))))))))
(dk-focus-having! (list 'FORALL 'i (list 'IMPLIES '(IN i (INTERVAL 1 n))
         (list 'FORALL 'j (list 'IMPLIES '(IN j (INTERVAL 1 n))
           (list '= (list 'ENTRY r6c-min 'i 'j)
                    (list 'ENTRY r6c-idm-n 'i 'j)))))))
(fact 'matrix-entry-extensionality 'n 'n '(CARR R) r6c-min r6c-idm-n)
(ass)
(r6c-done! 'identmat-minor)
(gloss! 'identmat-minor
  "Deleting row 1 and column 1 of the (succ n)-by-(succ n) identity matrix leaves
   the n-by-n identity matrix.  What the cofactor recursion needs to descend on
   IDENTMAT.")
(topic! 'identmat-minor 'algebra)

;;; ---- mat-ring-one (structure-library/matrix.scm:566, copied literally) --
(sp (make-wff
  '(FORALL a (FORALL n (IMPLIES (IS-RING a) (IMPLIES (IN n NN)
     (= (ONE (MAT-RING a n)) (IDENTMAT a n))))))))
(dk-peel!)
(fact 'identmat-type 'a 'n)
(slot 'ONE)
(mac 'MAT-RING)
(nth-r)
(rfl)
(r6c-done! 'mat-ring-one)
(topic! 'mat-ring-one 'plumbing)

;;; ---- det-identity-ind ---------------------------------------------------
(sp (make-wff
  '(FORALL R (IMPLIES (IS-RING R)
     (FORALL n (IMPLIES (IN n NN)
       (= (DET R n (IDENTMAT R n)) (ONE R))))))))
(di) (di)
(fact 'ring-one-in 'R)
(fact 'ring-zero-in 'R)
(fact 'ring-neg-in-carr 'R '(ONE R))
(fact 'ring-additive-ag-is-abelian-group 'R)
(fact 'ring-multiplicative-monoid-is-monoid 'R)
(fact 'ras-carr 'R)
(fact 'ras-id 'R)
(fact 'rmm-op 'R)
(fact 'rmm-iden 'R)
(fact 'rmm-carr 'R)
(fact 'eq-sym (list 'CARR r6c-mm) '(CARR R))
(have! (list 'IN r6c-sign (list 'CARR r6c-mm))
       (lambda () (subst (list '= (list 'CARR r6c-mm) '(CARR R))) (ass)))
(fact 'nn-one-in)
(fact 'nn-le-refl 1)
(define r6c-ind (use-induction))

;; ---- base: DET(R,0,-) = ONE(R) by det-zero
(dk-focus! (cdr (assq 'base r6c-ind)))
;; IDENTMAT is a MATOF, i.e. an IOTA, which the definedness certificate never
;; accepts -- so the instantiation would OWE `IDENTMAT(R,0) = IDENTMAT(R,0)'.
;; Type the term first (CLAUDE.md, "UNIVERSAL INSTANTIATION OWES DEFINEDNESS").
(fact 'nn-zero-in)
(fact 'identmat-type 'R 0)
(fact 'det-zero 'R '(IDENTMAT R 0))
(subst '(== (DET R 0 (IDENTMAT R 0)) (ONE R)))
(rfl)

;; ---- step
(dk-focus! (cdr (assq 'step r6c-ind)))
(let ((ih (cdr (assq 'ih r6c-ind))))
  (display ";; IH = ") (display (expression->string ih)) (newline)
  (fact 'nn-succ-closed 'n)
  (fact 'identmat-type 'R '(succ n))
  (fact 'identmat-type 'R 'n)
  (fact 'nn-one-le-succ 'n)
  (fact 'interval-mem-intro 1 '(succ n) 1)
  (fact 'interval-in-set 1 '(succ n))
  (fact 'interval-card-in-nn 1 '(succ n))
  (fact 'identmat-minor 'R 'n)
  (mac 'det-cofactor)
  (let* ((gl   (dk-goal))
         (fs   (cadr gl))
         (lamI (caddr fs))
         (idm  '(IDENTMAT R (succ n))))

    ;; (a) the summand is a function into the carrier
    (have! (list 'IN lamI (list 'FUN '(INTERVAL 1 (succ n)) (list 'CARR r6c-ag)))
      (lambda ()
        (r6c-lam-t!
         (lambda ()
           (let ((j (dk-di-var!)))
             (fact 'interval-elt-in-nn 1 '(succ n) j)
             (fact 'nn-succ-closed j)
             (fact 'mpow-type r6c-mm r6c-sign (list 'succ j))
             (have! (list 'IN (list 'MPOW r6c-mm r6c-sign (list 'succ j)) '(CARR R))
               (lambda () (subst (list '= '(CARR R) (list 'CARR r6c-mm))) (ass)))
             (dk-focus-having! (list 'IN (list 'MPOW r6c-mm r6c-sign (list 'succ j)) '(CARR R)))
             (fact 'entry-in-carrier '(succ n) '(succ n) '(CARR R) idm 1 j)
             (fact 'minor-type 'R idm 1 j 'n)
             (fact 'det-in-carrier 'R 'n (list 'MINOR idm 1 j 'n))
             (fact 'ring-carrier-closed-mul 'R (list 'ENTRY idm 1 j)
                   (list 'DET 'R 'n (list 'MINOR idm 1 j 'n)))
             (fact 'ring-carrier-closed-mul 'R (list 'MPOW r6c-mm r6c-sign (list 'succ j))
                   (list '(MUL R) (list 'ENTRY idm 1 j)
                         (list 'DET 'R 'n (list 'MINOR idm 1 j 'n))))
             (subst (list '= (list 'CARR r6c-ag) '(CARR R)))
             (ass))))))
    (dk-focus-having! (list 'IN lamI (list 'FUN '(INTERVAL 1 (succ n)) (list 'CARR r6c-ag))))

    ;; (b) every off-diagonal term is the group identity
    (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ (INTERVAL 1 (succ n)))
             (list 'IMPLIES (list 'NOT (list '= 'j_ 1))
                   (list '= (list lamI 'j_) (list 'IDEN r6c-ag)))))
      (lambda ()
        (di) (di)
        (lam-b)
        (fact 'neq-sym 'j_ 1)
        (fact 'interval-elt-in-nn 1 '(succ n) 'j_)
        (fact 'nn-succ-closed 'j_)
        (r6c-identmat-entry! 'R '(succ n) 1 'j_)
        (subst (list '= (list 'ENTRY idm 1 'j_)
                     (list 'IF (list '= 1 'j_) '(ONE R) '(ZERO R))))
        (r6c-if-branch! #f (list 'IF (list '= 1 'j_) '(ONE R) '(ZERO R))
         (lambda ()
        (fact 'minor-type 'R idm 1 'j_ 'n)
        (fact 'det-in-carrier 'R 'n (list 'MINOR idm 1 'j_ 'n))
        (fact 'ring-mul-zero-left 'R (list 'DET 'R 'n (list 'MINOR idm 1 'j_ 'n)))
        (subst (list '= (list '(MUL R) '(ZERO R)
                             (list 'DET 'R 'n (list 'MINOR idm 1 'j_ 'n)))
                     '(ZERO R)))
        (fact 'mpow-type r6c-mm r6c-sign (list 'succ 'j_))
        (have! (list 'IN (list 'MPOW r6c-mm r6c-sign '(succ j_)) '(CARR R))
          (lambda () (subst (list '= '(CARR R) (list 'CARR r6c-mm))) (ass)))
        (dk-focus-having! (list 'IN (list 'MPOW r6c-mm r6c-sign '(succ j_)) '(CARR R)))
        (fact 'ring-mul-zero-right 'R (list 'MPOW r6c-mm r6c-sign '(succ j_)))
        (subst (list '= (list '(MUL R) (list 'MPOW r6c-mm r6c-sign '(succ j_)) '(ZERO R))
                     '(ZERO R)))
        (subst (list '= (list 'IDEN r6c-ag) '(ZERO R)))
        (rfl)))))
    (dk-focus-having! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ (INTERVAL 1 (succ n)))
             (list 'IMPLIES (list 'NOT (list '= 'j_ 1))
                   (list '= (list lamI 'j_) (list 'IDEN r6c-ag))))))

    ;; (c) the sum collapses to its j = 1 term
    (fact 'finsum-single-support r6c-ag '(INTERVAL 1 (succ n)) lamI 1)
    (subst (list '= (list 'FINSUM r6c-ag lamI '(INTERVAL 1 (succ n))) (list lamI 1)))

    ;; (d) compute that term
    (lam-b)
    (mac 'mpow-succ)
    (fact 'ring-mpow-one 'R r6c-sign)
    (subst (list '= (list 'MPOW r6c-mm r6c-sign 1) r6c-sign))
    (subst (list '= (list 'OPR r6c-mm) '(MUL R)))
    (r6c-sign-square!)
    (r6c-identmat-entry! 'R '(succ n) 1 1)
    (subst (list '= (list 'ENTRY idm 1 1) '(IF (= 1 1) (ONE R) (ZERO R))))
    (have! '(= 1 1) (lambda () (rfl)))
    (r6c-if-branch! #t '(IF (= 1 1) (ONE R) (ZERO R))
     (lambda ()
       (subst '(= (MINOR (IDENTMAT R (succ n)) 1 1 n) (IDENTMAT R n)))
       (subst (list '= (list 'DET 'R 'n '(IDENTMAT R n)) '(ONE R)))
       (fact 'ring-mul-left-id 'R '(ONE R))
       (subst '(= ((MUL R) (ONE R) (ONE R)) (ONE R)))
       (subst '(= ((MUL R) (ONE R) (ONE R)) (ONE R)))
       (rfl)))))
(r6c-done! 'det-identity-ind)
(topic! 'det-identity-ind 'algebra)

;;; ---- det-identity (structure-library/determinant.scm:106, copied literally)
(sp (make-wff
  (forall-guarded '(R n)
    (list '(IS-RING R) '(IN n NN))
    '(= (DET R n (ONE (MAT-RING R n))) (ONE R)))))
(dk-peel!)
(fact 'mat-ring-one 'R 'n)
(subst '(= (ONE (MAT-RING R n)) (IDENTMAT R n)))
(fact 'det-identity-ind 'R 'n)
(ass)
(r6c-done! 'det-identity)
(topic! 'det-identity 'algebra)
