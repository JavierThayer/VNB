;;; rake-smith-leaves.scm -- finsum-interval-shift, PROVEN.
;;;
;;; SEPARATE FILE from rake-border-siblings.scm (the other four leaves of this
;;; bundle) because its window is 84 slots tighter and its citations are a
;;; different layer entirely: the finsum / reindex machinery of
;;; theorem-library/monalg-is-ring.scm, which has nothing to do with the BORDER
;;; entry read-offs.  It must load AFTER rake-border-siblings.scm: it cites
;;; succ-nn-minus-1, which that file proves.
;;;
;;; THE STATEMENT (theorem-library/finsum-additive.scm:230, copied literally):
;;; the FRONT-peel of a finite sum over [1, succ n] --
;;;     FINSUM(ag, f, [1, succ n])
;;;       = f(1) (+) FINSUM(ag, z in [1,n] |-> f(succ z), [1,n]).
;;;
;;; AUDIT (CLAUDE.md, "the species of FALSE or underdetermined support").  The
;;; strict `=' is licensed: n is typed in NN, f is typed as a FUN on the WHOLE
;;; index set [1, succ n], 1 lies in that set (one-in-interval) and succ z lies
;;; in it for z in [1,n] (succ-in-interval), so every application occurring in
;;; the equation denotes, and both FINSUMs are over sets of finite cardinal
;;; (interval-card-in-nn).  n = 0 is covered and is not degenerate: the left
;;; sum is over [1,1], the right is over the EMPTY [1,0] and contributes the
;;; identity.  Nothing is under-guarded; the statement is proved unchanged.
;;;
;;; THE ROUTE.  The back-peel twin (finsum-interval-peel) can use
;;; `interval-succ-insert' ([1,succ n] = [1,n] u {succ n}) and needs no
;;; reindexing.  The FRONT peel has no such interval identity -- and does not
;;; need one: `remove-restore' (theorem-library/rake-finsum-union.scm) gives
;;;     (I \ {1}) u {1} = I     for 1 in I,
;;; so the peeled-off index set is X := DIFFERENCE([1,succ n], {1}), and the
;;; four bricks rake-intervals.scm proved are EXACTLY the maps between X and
;;; [1,n]:  succ-in-interval + succ-not-one send [1,n] into X, pred-in-interval
;;; sends X into [1,n], and the two round trips are nn-minus-succ-1 and
;;; succ-nn-minus-1.  So no new set identity and no new order lemma is needed.
;;;
;;;   1. remove-restore at 1:            U := (I \ {1}) u {1} = I
;;;   2. finsum-insert-ag at X, k := 1:  FINSUM(f, U) = FINSUM(f, X) (+) f(1)
;;;   3. finsum-reindex-inverse-ptwise with phi := (z_ in [1,n] |-> succ z_)
;;;      and psi := (w_ in X |-> w_ - 1):
;;;                                      FINSUM(f, X) = FINSUM(z |-> f(phi z), [1,n])
;;;      (the -inverse- form is what lets the bijection be given as a pair of
;;;      maps; no BIJECTION term has to be built)
;;;   4. finsum-congruence-q:            ... = FINSUM(z |-> f(succ z), [1,n])
;;;   5. abelian-group-opr-comm:         swaps the two operands into the
;;;                                      statement's order.
;;;
;;; LOAD WINDOW [332, 381).
;;;   lo = 332: the latest citations are `finsum-reindex-inverse-ptwise',
;;;             `lambda-compose-value' and `bijection-from-inverse''s file,
;;;             theorem-library/monalg-is-ring (331).  Then
;;;             rake-finsum-union (270, remove-restore), rake-finsum-laws
;;;             (253, finsum-congruence-q / finsum-type-ptwise),
;;;             interval-card-in-nn (252), finsum-insert (237,
;;;             finsum-insert-ag), nn-pos-is-succ (229), rake-intervals (225,
;;;             succ-in-interval / succ-not-one / pred-in-interval /
;;;             nn-minus-succ-1), card-subset-nn, difference-laws,
;;;             interval-basics (149), fun-apply-type-proof, equality-basics,
;;;             structure-library/subtype-laws (abelian-group-opr-comm), plus
;;;             rake-border-siblings.scm (succ-nn-minus-1), which the
;;;             integrator wires anywhere in [230, 332).
;;;   hi = 381: theorem-library/border-mult-proof is the earliest citer.
;;;   (0-based indices over load.scm's file entries, md5 51d4a35c, 2026-09-19;
;;;    recompute at integration -- load.scm gained an entry while this ran.)
;;;
;;; Helper prefix: rsl-.

(define rsl-I  '(INTERVAL 1 (succ n)))
(define rsl-T  '(INTERVAL 1 n))
(define rsl-P1 '(PAIR 1 1))
(define rsl-X  '(DIFFERENCE (INTERVAL 1 (succ n)) (PAIR 1 1)))
(define rsl-U  '(UNION (DIFFERENCE (INTERVAL 1 (succ n)) (PAIR 1 1)) (PAIR 1 1)))
(define rsl-CA '(CARR ag))
(define rsl-phi '(VNB-LAMBDA z_ (INTERVAL 1 n) (succ z_)))
(define rsl-psi '(VNB-LAMBDA w_ (DIFFERENCE (INTERVAL 1 (succ n)) (PAIR 1 1))
                   (NN-MINUS w_ 1)))
;; the summand the reindex produces, and the one the statement asks for
(define rsl-lam1 (list 'VNB-LAMBDA 'z rsl-T (list 'f (list rsl-phi 'z))))
(define rsl-lam2 (list 'VNB-LAMBDA 'z rsl-T '(f (succ z))))

;;; `dk-only!' can leave the focus leaf GROUNDED, and focus then falls to the
;;; MAIN branch (a known driver-kit defect, CLAUDE.md "KNOWN DEFECTS not yet
;;; fixed").  A bare `prop' after it therefore fires on the file's own theorem
;;; and no-ops with a "does not follow propositionally" warning.  Weaken and
;;; close in ONE helper, which props only if focus is still on the goal it was
;;; aimed at.
(define (rsl-only-prop! keepers)
  (let ((g (dk-goal)))
    (apply dk-only! keepers)
    (if (alpha-equiv? (dk-goal) g) (prop))))

(define (rsl-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'combinatorial))
      (begin
        (display "\n*** rake-smith-leaves: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-smith-leaves: unfinished" name))))

;;; From (IN tm X) in context, land (IN tm I) and (NOT (= tm 1)).  X is a
;;; DIFFERENCE, so both come off difference-membership; the singleton side
;;; wants pairing-membership and the ground (= 1 1), which `prop' treats as an
;;; opaque atom and therefore has to be GIVEN.
(define (rsl-x-facts! tm)
  (let ((dm (dk-fact! 'difference-membership rsl-I rsl-P1 tm))
        (pm (dk-fact! 'pairing-membership 1 1 tm)))
    (have! (list 'IN tm rsl-I)
           (lambda () (rsl-only-prop! (list dm (list 'IN tm rsl-X)))))
    (have! (list 'NOT (list '= tm 1))
           (lambda () (rsl-only-prop! (list dm pm (list 'IN tm rsl-X) '(= 1 1)))))))

;;; The converse, as a GOAL CLOSER: with (IN tm I) and (NOT (= tm 1)) in
;;; context, close the focus goal (IN tm X).
(define (rsl-into-x-close! tm)
  (let ((dm (dk-fact! 'difference-membership rsl-I rsl-P1 tm))
        (pm (dk-fact! 'pairing-membership 1 1 tm)))
    (rsl-only-prop! (list dm pm (list 'IN tm rsl-I) (list 'NOT (list '= tm 1)) '(= 1 1)))))

;;; ... and as a LANE, for the places where (IN tm X) is wanted beside another
;;; goal.  (Both forms are needed: `have!' of a claim equal to the focus goal
;;; has no main branch and ERRORS -- CLAUDE.md, "cut / have! of a formula
;;; already in context".)
(define (rsl-into-x! tm)
  (have! (list 'IN tm rsl-X) (lambda () (rsl-into-x-close! tm))))

;;; ---- finsum-interval-shift ---------------------------------------------
;;; Statement copied from theorem-library/finsum-additive.scm:230, unchanged.
(sp (make-wff
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL n (IMPLIES (IN n NN)
       (FORALL f (IMPLIES (IN f (FUN (INTERVAL 1 (succ n)) (CARR ag)))
         (= (FINSUM ag f (INTERVAL 1 (succ n)))
            ((OPR ag) (f 1) (FINSUM ag (VNB-LAMBDA z (INTERVAL 1 n) (f (succ z))) (INTERVAL 1 n))))))))))))
(dk-peel!)

;;; ---- the plumbing: sethood, cardinals, the ground (= 1 1) ---------------
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)                                   ; 1 in NN
(fact 'membership-implies-sethood 1 'NN)            ; 1 in SET
(have! '(= 1 1) (lambda () (rfl)))
;; the explicit closer is not decoration: `from-context!' routes ANY goal
;; (IN <number> A) to `arith', so the default closer fails on (IN 1 SET) even
;; though it is in context verbatim (driver-kit.scm, from-context!).
(have! '(AND (IN 1 SET) (IN 1 SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'one-in-interval 'n)                          ; 1 in I
(fact 'interval-in-set 1 '(succ n))                 ; I in SET
(fact 'interval-in-set 1 'n)                        ; T in SET
(fact 'interval-card-in-nn 1 '(succ n))             ; CARD I in NN
(fact 'interval-card-in-nn 1 'n)                    ; CARD T in NN
(fact 'difference-set rsl-I rsl-P1)                 ; X in SET

;;; CARD X in NN: X is a subset of I, whose cardinal is a natural.
(define rsl-sub
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ rsl-X) (list 'IN 'z_ rsl-I))))
(have! rsl-sub
  (lambda ()
    (let ((zv (dk-di-var!)))
      (let ((dm (dk-fact! 'difference-membership rsl-I rsl-P1 zv)))
        (rsl-only-prop! (list dm (list 'IN zv rsl-X)))))))
(have! (list 'AND (list 'IN rsl-I 'SET) (list 'IN (list 'CARD rsl-I) 'NN)))
(have! (list 'AND (list 'IN rsl-X 'SET) rsl-sub))
(fact 'card-subset-nn rsl-I rsl-X)                  ; CARD X in NN

;;; 1 is not in X = I \ {1}.
(have! (list 'NOT (list 'IN 1 rsl-X))
  (lambda ()
    (let ((dm (dk-fact! 'difference-membership rsl-I rsl-P1 1))
          (pm (dk-fact! 'pairing-membership 1 1 1)))
      (rsl-only-prop! (list dm pm '(= 1 1))))))

;;; ---- 1. remove-restore:  U = I ------------------------------------------
(fact 'remove-restore rsl-I 1)                      ; (= U I)
(fact 'eq-sym rsl-U rsl-I)                          ; (= I U)

;;; ---- 2. finsum-insert-ag at X, k := 1 -----------------------------------
(have! (list 'IN 'f (list 'FUN rsl-U rsl-CA))
  (lambda () (subst (list '= rsl-U rsl-I)) (ass)))
(define rsl-h-insert
  (list '= (list 'FINSUM 'ag 'f rsl-U)
        (list '(OPR ag) (list 'FINSUM 'ag 'f rsl-X) '(f 1))))
(fact 'finsum-insert-ag 'ag rsl-X 1 'f)

;;; ---- 3. the reindex ------------------------------------------------------
;;; phi : [1,n] -> X by succ, psi : X -> [1,n] by monus 1.
(have! (list 'IN rsl-phi (list 'FUN rsl-T rsl-X))
  (lambda ()
    (dk-lam-t!)
    (let ((zv (dk-di-var!)))
      (fact 'succ-in-interval 'n zv)                ; succ zv in I
      (fact 'succ-not-one 'n zv)                    ; succ zv /= 1
      (rsl-into-x-close! (list 'succ zv)))))
(have! (list 'IN rsl-psi (list 'FUN rsl-X rsl-T))
  (lambda ()
    (dk-lam-t!)
    (let ((wv (dk-di-var!)))
      (rsl-x-facts! wv)
      (fact 'pred-in-interval 'n wv)                ; NN-MINUS(wv,1) in T
      (ass))))
;; psi(phi u) = u on [1,n]
(have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ rsl-T)
         (list '= (list rsl-psi (list rsl-phi 'u_)) 'u_)))
  (lambda ()
    (let ((uv (dk-di-var!)))
      (fact 'succ-in-interval 'n uv)
      (fact 'succ-not-one 'n uv)
      (rsl-into-x! (list 'succ uv))
      (lam-b)
      (fact 'interval-elt-in-nn 1 'n uv)
      (fact 'nn-minus-succ-1 uv)
      (subst (list '= (list 'NN-MINUS (list 'succ uv) 1) uv))
      (rfl))))
;; phi(psi v) = v on X
(have! (list 'FORALL 'v_ (list 'IMPLIES (list 'IN 'v_ rsl-X)
         (list '= (list rsl-phi (list rsl-psi 'v_)) 'v_)))
  (lambda ()
    (let ((vv (dk-di-var!)))
      (rsl-x-facts! vv)
      (fact 'pred-in-interval 'n vv)
      (lam-b)
      (fact 'interval-elt-in-nn 1 '(succ n) vv)
      (fact 'interval-lo 1 '(succ n) vv)            ; 1 <= vv
      (fact 'succ-nn-minus-1 vv)
      (subst (list '= (list 'succ (list 'NN-MINUS vv 1)) vv))
      (rfl))))
;; f is typed pointwise on X
(have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ rsl-X)
         (list 'IN '(f z_) rsl-CA)))
  (lambda ()
    (let ((zv (dk-di-var!)))
      (rsl-x-facts! zv)
      (fact 'fun-apply-type-c 'f rsl-I rsl-CA zv)
      (ass))))
(have! (list 'AND (list 'IN rsl-T 'SET) (list 'IN (list 'CARD rsl-T) 'NN)))
(fact 'finsum-reindex-inverse-ptwise 'ag rsl-X rsl-T rsl-phi rsl-psi 'f)

;;; ---- 4. the congruence:  f(phi z) = f(succ z) on [1,n] ------------------
(have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ rsl-T)
         (list '= (list rsl-lam1 'z_) (list rsl-lam2 'z_))))
  (lambda ()
    (let ((zv (dk-di-var!)))
      (fact 'succ-in-interval 'n zv)
      (fact 'fun-apply-type-c 'f rsl-I rsl-CA (list 'succ zv))
      (lam-b)
      (rfl))))
(fact 'finsum-congruence-q 'ag rsl-T rsl-lam1 rsl-lam2)

;;; ---- 5. the swap, and the close ------------------------------------------
(have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ rsl-T)
         (list 'IN (list rsl-lam2 'z_) rsl-CA)))
  (lambda ()
    (let ((zv (dk-di-var!)))
      (fact 'succ-in-interval 'n zv)
      (fact 'fun-apply-type-c 'f rsl-I rsl-CA (list 'succ zv))
      (lam-b)
      (ass))))
(fact 'finsum-type-ptwise 'ag rsl-T rsl-lam2)       ; the right sum is in CARR ag
(fact 'fun-apply-type-c 'f rsl-I rsl-CA 1)          ; f(1) is in CARR ag
(fact 'abelian-group-opr-comm 'ag (list 'FINSUM 'ag rsl-lam2 rsl-T) '(f 1))

(subst (list '= rsl-I rsl-U))
(subst rsl-h-insert)
(subst (list '= (list 'FINSUM 'ag 'f rsl-X) (list 'FINSUM 'ag rsl-lam1 rsl-T)))
(subst (list '== (list 'FINSUM 'ag rsl-lam1 rsl-T) (list 'FINSUM 'ag rsl-lam2 rsl-T)))
(subst (list '= (list '(OPR ag) (list 'FINSUM 'ag rsl-lam2 rsl-T) '(f 1))
             (list '(OPR ag) '(f 1) (list 'FINSUM 'ag rsl-lam2 rsl-T))))
(rfl)
(rsl-qed! 'finsum-interval-shift)
