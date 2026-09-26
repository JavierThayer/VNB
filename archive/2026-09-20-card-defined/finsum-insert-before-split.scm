;;; theorem-library/finsum-insert.scm -- the insertion recurrence for FINSUM.
;;;
;;;     finsum-insert     (comm-monoid)   FINSUM(m, f, X u {k}) = (OPR m)(FINSUM(m, f, X), f k)
;;;     finsum-insert-ag  (abelian group) the same with IS-ABELIAN-GROUP ag and CURRIED
;;;                                       k-guards (the statement of finsum-additive.scm)
;;;
;;; for X finite (X in SET, CARD X in NN), k a set not in X, f in FUN(X u {k}, CARR).
;;; Both statements are copied LITERALLY from their support sites
;;; (theorem-library/prod-of-sums.scm `finsum-insert', theorem-library/finsum-additive.scm
;;; `finsum-insert-ag' with tf/tfin expanded).
;;;
;;; THE ARGUMENT.  FINSUM(m,f,S) is DEFINED as SUM-AG(m, ENUM-FAM(m,f,FIN-ENUM S,|S|), |S|)
;;; with FIN-ENUM S = CHOICE(BIJECTION(OS |S|, S)) (structure-library/finsum.scm).  Nothing
;;; about the CHOSEN enumeration of X u {k} puts k last, so the peel has to go through
;;; enumeration-independence:  FINSUM(m,f,S) = SUM-AG(m, ENUM-FAM(m,f,enm,|S|), |S|) for EVERY
;;; bijection enm : OS(|S|) -> S.  That is `finsum-comm-monoid-well-defined' (resp.
;;; `finsum-well-defined'), an ASSERTED support (informal; its 2026-05 mechanised proof is
;;; archived and predates the E->IDEN rename).  It is the one leaf this proof owes and it is
;;; unavoidable: without it FINSUM over X u {k} says nothing about k's position.
;;;
;;;   1. enm := FIN-ENUM X is a bijection OS(n) -> X, n = CARD X   (fin-enum-is-bijection,
;;;      re-proven here: mac FIN-ENUM + choice-axiom + card-finite-bij).
;;;   2. psi := lambda i in OS(succ n). IF i in OS(n) THEN enm(i) ELSE k   is a bijection
;;;      OS(succ n) -> X u {k}                                          (enum-append-is-bijection).
;;;      NOTE: this is NOT the functoid INSERT-LAST of finsum.scm.  INSERT-LAST's lambda has
;;;      domain NN, and `lam-t' (pi-lambda-type!) types a lambda only into a FUN whose domain
;;;      is the lambda's OWN domain -- FUN(A) means "defined exactly on A"
;;;      (fun-domain-apply-def) -- so INSERT-LAST(phi,x,n) is in FUN(NN, _) and can never be
;;;      in BIJECTION(OS(succ n), _).  scratch/scratch-fs3.scm's `insert-last-is-bijection'
;;;      is unprovable as stated for that reason; the lambda here carries the right domain.
;;;   3. CARD(X u {k}) = succ n                    (card-insert, ord-succ-nn), hence in NN.
;;;   4. well-definedness at psi:  FINSUM(m,f,X u {k}) = SUM-AG(m, F*, CARD(X u {k})) with
;;;      F* = ENUM-FAM(m,f,psi*,CARD(X u {k})), psi* = psi with its domain spelled
;;;      OS(CARD(X u {k})).
;;;   5. sum-ag-succ (definitional):  SUM-AG(m,F,succ n) = (OPR m)(SUM-AG(m,F,n), F n).
;;;   6. F n = f k:   unfold ENUM-FAM, beta, IF-true (n in OS(succ n)), beta psi, IF-false
;;;      (n not in OS n: ord-segment-self, re-proven here from ord-segment-membership +
;;;      ord-lt-iff).
;;;   7. SUM-AG(m,F,n) = SUM-AG(m,G,n) with G = ENUM-FAM(m,f,FIN-ENUM X,n) = FINSUM(m,f,X)
;;;      unfolded, because F and G AGREE on OS(n) (three IF reductions) and SUM-AG reads only
;;;      the indices below n:  `sum-ag-segment-congruence', NEW, by `ni' over
;;;      sum-ag-zero/succ, modulo 0.  No typing of the summand and no monoid law is used --
;;;      the whole peel is definitional once the enumeration is right.
;;;
;;; Steps 5-7 are the lemma `finsum-insert-from-enum', stated for an enumeration VARIABLE
;;; enm (why it must be, and the beta trap it dodges, is at its definition).  Its goal is
;;; driven by `subst' from the right-hand side towards the shape the enumeration-independence
;;; equation has (each `subst' needs its equation IN CONTEXT, so every step is a `have!' or a
;;; `fact' first): f k -> F n; FINSUM(m,f,X) -> SUM-AG(m,F,n); the OPR term ->
;;; SUM-AG(m,F,succ n); succ n -> CARD(X u {k}) (one rewrite, `subst' hits every occurrence);
;;; then `ass'.  The two main theorems instantiate it at psi* and discharge psi*(n) == k and
;;; the agreement below n, each a top-level beta plus one IF reduction.
;;;
;;; RESULT (probe on the band, 2026-09-15, 20 s):
;;;   ord-segment-self, fin-enum-is-bijection, sum-ag-segment-congruence,
;;;   enum-append-is-bijection, finsum-insert-from-enum        -- proven modulo 0
;;;   finsum-insert     -- proven modulo {finsum-comm-monoid-well-defined} [trust: informal]
;;;   finsum-insert-ag  -- proven modulo {finsum-well-defined}             [trust: informal]
;;;
;;; CITATIONS (load position, 0-based over load.scm's prover-load entries):
;;;   base theory (theory.scm, primitive): choice-axiom, pairing, pairing-membership,
;;;     union-set-closure, union-membership, fun-apply-type (theorem-library/axioms, 15)
;;;   structure-library/ordinals (77, primitive): nn-subset-ord, ord-lt-iff, ord-succ-nn,
;;;     ord-segment-is-set, ord-segment-membership
;;;   structure-library/bijection (81, definitional): bijection-membership-iff
;;;   structure-library/cardinality (82, primitive): card-insert, card-finite-bij
;;;   number-systems (primitive): nn-succ-closed
;;;   structure-library/sequences (92, definitional): sum-ag-zero, sum-ag-succ
;;;   structure-library/finsum (93, functoid unfolds): FIN-ENUM, ENUM-FAM, FINSUM
;;;   theorem-library/finsum-well-defined (113) and finsum-comm-monoid (118): the two
;;;     enumeration-independence supports -- ASSERTED (informal); the bill of each theorem
;;;     is exactly one of them
;;;   theorem-library/ord-segment-nn-succ-proof (154), ord-segment-nn-subset-proof (155):
;;;     ord-segment-nn-succ, ord-segment-nn-subset -- proven; the LATEST citations, so
;;;
;;; LOAD WINDOW [156, end): lo = the slot after ord-segment-nn-subset-proof (155); hi is
;;; unconstrained -- no proven theorem cites finsum-insert or finsum-insert-ag today (they
;;; are named only in warrants).  fun-apply-type-c (163) is deliberately NOT cited (the
;;; axiom fun-apply-type is used with a `have!'d AND) so lo stays at 156.
;;;
;;; ALSO PROVEN HERE, under their own names, because both were asserted supports with no
;;; proven citer and both are needed:  ord-segment-self (theorem-library/ord-segment-self.scm,
;;; pos 110, informal) and fin-enum-is-bijection (theorem-library/fin-enum-is-bijection.scm,
;;; pos 112, informal).  On the band this re-installs the same statements.
;;;
;;; Helper prefix: fsi-.

;;; ---------------------------------------------------------------------------
;;; helpers

(define (fsi-goal) (dk-goal))

(define (fsi-grounded! node who)
  (if (not (sequent-node-grounded? node))
      (error "fsi: leaf left open at" who (expression->string (dk-goal-of node)))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (fsi-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "fsi-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "fsi-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;; The first (IF c a b) subterm of EXPR, in pre-order, whose condition satisfies PRED.
(define (fsi-find-if expr pred)
  (cond ((not (pair? expr)) #f)
        ((and (eq? (car expr) 'IF) (= (length expr) 4) (pred (cadr expr))) expr)
        (#t (let loop ((es expr))
              (cond ((null? es) #f)
                    ((not (pair? es)) #f)
                    (#t (or (fsi-find-if (car es) pred) (loop (cdr es)))))))))

;; `if-true' / `if-false' on the conditional term IFT.  The kernel rule spawns the
;; condition (resp. its negation) as a SIDE leaf and lands (= IFT branch) in the MAIN
;; branch.  CLOSER closes the side leaf (default `ass'); focus is left on the main branch.
;; Returns the landed equation.
(define (fsi-if-land! which ift . opt)
  (let* ((closer (if (pair? opt) (car opt) ass))
         (p      (cadr ift))
         (want   (if (eq? which 'true) p (list 'NOT p)))
         (val    (if (eq? which 'true) (caddr ift) (cadddr ift)))
         (new    (dk-opened (lambda () (if (eq? which 'true) (if-true ift) (if-false ift)))))
         (side   (fsi-leaf new (lambda (g) (alpha-equiv? g want)) "if side condition"))
         (main   (fsi-leaf new (lambda (g) (not (alpha-equiv? g want))) "if main branch")))
    (dk-focus! side) (closer) (fsi-grounded! side 'fsi-if-land!)
    (dk-focus! main)
    (list '= ift val)))

;; Reduce, IN THE GOAL, the first IF whose condition satisfies PRED, then substitute the
;; landed equation into the goal.
(define (fsi-reduce-if! which pred . opt)
  (let ((ift (or (fsi-find-if (fsi-goal) pred)
                 (error "fsi-reduce-if!: no IF with the wanted condition in"
                        (expression->string (fsi-goal))))))
    (subst (apply fsi-if-land! which ift opt))))

;; mac-h that also closes the side-condition leaves a GUARDED macete spawns (by `ass'),
;; and errors if the rewrite did nothing.
(define (fsi-mac-h! name hyp)
  (let* ((g0    (fsi-goal))
         (new   (dk-opened (lambda () (mac-h name hyp))))
         (sides (filter (lambda (l) (not (alpha-equiv? (dk-goal-of l) g0))) new))
         (mains (filter (lambda (l) (alpha-equiv? (dk-goal-of l) g0)) new)))
    (for-each (lambda (s) (dk-focus! s) (ass) (fsi-grounded! s (list 'fsi-mac-h! name))) sides)
    (if (null? mains) (error "fsi-mac-h!: no main branch after" name (expression->string hyp)))
    (dk-focus! (car mains))))

(define (fsi-check-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; fsi: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "fsi: proof not complete" name))))

;;; ---------------------------------------------------------------------------
;;; ord-segment-self, fin-enum-is-bijection and sum-ag-segment-congruence were proven
;;; HERE until 2026-09-17; they are now proven in theorem-library/rake-inverse-bij.scm
;;; (the first two) and rake-finsum-welldef.scm (the third), which load BEFORE this
;;; file since it moved below them (it cites finsum-well-defined, proven there).  The
;;; three blocks are in archive/retired-2026-09-17/finsum-insert-three-blocks.scm.

;;; ---------------------------------------------------------------------------
;;; enum-append-is-bijection:  given a bijection enm : OS(n) -> sg and a set pt not in sg,
;;;
;;;   psi = lambda i in OS(succ n). IF i in OS(n) THEN enm(i) ELSE pt
;;;
;;; is a bijection OS(succ n) -> sg u {pt}.  Guards curried so `fact' detaches them.

(define (fsi-psi enm pt n)
  `(VNB-LAMBDA i (ORD-SEGMENT (succ ,n)) (IF (IN i (ORD-SEGMENT ,n)) (,enm i) ,pt)))

(define fsi-append-stmt
  `(FORALL n (IMPLIES (IN n NN)
     (FORALL sg (IMPLIES (IN sg SET)
     (FORALL pt (IMPLIES (IN pt SET) (IMPLIES (NOT (IN pt sg))
     (FORALL enm (IMPLIES (IN enm (BIJECTION (ORD-SEGMENT n) sg))
       (IN ,(fsi-psi 'enm 'pt 'n)
           (BIJECTION (ORD-SEGMENT (succ n)) (UNION sg (PAIR pt pt))))))))))))))

(sp (make-wff fsi-append-stmt))
(let* ((landed (dk-peel!))
       (bij  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                       (pair? (caddr f)) (eq? (car (caddr f)) 'BIJECTION)))
                      "enm in BIJECTION"))
       (enm  (cadr bij))
       (osn  (cadr (caddr bij)))                        ; (ORD-SEGMENT n)
       (nv   (cadr osn))
       (sg   (caddr (caddr bij)))
       (pt   (cadr (cadr (dk-pick (dk-head? 'NOT) "pt not in sg"))))
       (uu   `(UNION ,sg (PAIR ,pt ,pt)))
       (osn1 `(ORD-SEGMENT (succ ,nv))))
  ;; unpack enm's bijection: FUN typing, injectivity, surjectivity
  (fsi-mac-h! 'bijection-membership-iff bij)
  (let* ((conjs (dk-split! (dk-pick (dk-head? 'AND) "unfolded bijection")))
         (ante-class (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                      (caddr (cadr (caddr f))))))
         (inj  (or (find-first (lambda (f) (equal? (ante-class f) osn)) conjs)
                   (error "fsi: injectivity conjunct not found")))
         (surj (or (find-first (lambda (f) (equal? (ante-class f) sg)) conjs)
                   (error "fsi: surjectivity conjunct not found"))))
    ;; unfold the goal and split it into its three parts
    (mac 'bijection-membership-iff)
    (let* ((l1 (dk-opened (lambda () (di))))
           (fun-leaf (fsi-leaf l1 (dk-head? 'IN) "FUN leaf"))
           (rest     (fsi-leaf l1 (dk-head? 'AND) "inj/surj leaf")))
      (dk-focus! rest)
      (let* ((l2 (dk-opened (lambda () (di))))
             (inj-leaf  (fsi-leaf l2 (lambda (g) (equal? (caddr (cadr (caddr g))) osn1)) "inj leaf"))
             (surj-leaf (fsi-leaf l2 (lambda (g) (equal? (caddr (cadr (caddr g))) uu)) "surj leaf")))

        ;; ---- FUN: psi in FUN(OS(succ n), sg u {pt}) ----
        (dk-focus! fun-leaf)
        (let* ((l3 (dk-opened (lambda () (lam-t))))
               (set-leaf (fsi-leaf l3 (lambda (g) (eq? (caddr g) 'SET)) "domain sethood"))
               (typ-leaf (fsi-leaf l3 (lambda (g) (not (eq? (caddr g) 'SET))) "pointwise typing")))
          (dk-focus! set-leaf)
          (dk-fact! 'nn-succ-closed nv)
          (dk-fact! 'nn-subset-ord `(succ ,nv))
          (dk-fact! 'ord-segment-is-set `(succ ,nv))
          (ass)
          (fsi-grounded! set-leaf 'domain-sethood)
          (dk-focus! typ-leaf)
          (let* ((iv (dk-di-var!)))                     ; lands (IN i OS(succ n))
            (fsi-mac-h! 'ord-segment-nn-succ `(IN ,iv ,osn1))
            (use-cases `(OR (IN ,iv ,osn) (= ,iv ,nv))
              (lambda ()                                ; i in OS(n): the value is enm(i) in sg
                (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,iv ,osn))))
                (mac 'union-membership) (oi-l)
                (have! `(AND (IN ,enm (FUN ,osn ,sg)) (IN ,iv ,osn)))
                (dk-fact! 'fun-apply-type enm osn sg iv)
                (ass))
              (lambda ()                                ; i = n: the value is pt
                (fsi-reduce-if! 'false (lambda (c) (equal? c `(IN ,iv ,osn)))
                  (lambda () (subst `(= ,iv ,nv)) (dk-fact! 'ord-segment-self nv) (ass)))
                (mac 'union-membership) (oi-r)
                (have! `(AND (IN ,pt SET) (IN ,pt SET)))
                (mac 'pairing-membership) (oi-l) (rfl)))))
        (fsi-grounded! fun-leaf 'FUN-part)

        ;; ---- INJ ----
        (dk-focus! inj-leaf)
        (let* ((landed (dk-peel!))                      ; (IN a OS1) (IN b OS1) (= (psi a) (psi b))
               (eqn (dk-pick (dk-head? '=) "psi a = psi b"))
               (av  (cadr (cadr eqn)))
               (bv  (cadr (caddr eqn)))
               (eqn2 (dk-landed-1 (lambda () (lam-b-h eqn))))   ; (= IFa IFb)
               (ifa (cadr eqn2))
               (ifb (caddr eqn2))
               (via-enm! (lambda (v)                    ; (IN (enm v) sg) for v in OS(n)
                           (have! `(AND (IN ,enm (FUN ,osn ,sg)) (IN ,v ,osn)))
                           (dk-fact! 'fun-apply-type enm osn sg v)))
               (n-side (lambda (v)                      ; closes (NOT (IN v OS(n))) when v = n
                         (lambda () (subst `(= ,v ,nv)) (dk-fact! 'ord-segment-self nv) (ass)))))
          (fsi-mac-h! 'ord-segment-nn-succ `(IN ,av ,osn1))
          (fsi-mac-h! 'ord-segment-nn-succ `(IN ,bv ,osn1))
          (use-cases `(OR (IN ,av ,osn) (= ,av ,nv))
            (lambda ()
              (use-cases `(OR (IN ,bv ,osn) (= ,bv ,nv))
                (lambda ()                              ; a, b in OS(n): enm a = enm b, enm injective
                  (fsi-if-land! 'true ifa)
                  (fsi-if-land! 'true ifb)
                  (have! `(= (,enm ,av) (,enm ,bv))
                         (lambda () (subst `(= (,enm ,av) ,ifa)) (subst `(= (,enm ,bv) ,ifb)) (ass)))
                  (dk-apply! inj av bv)
                  (ass))
                (lambda ()                              ; a in OS(n), b = n: enm a = pt in sg, absurd
                  (fsi-if-land! 'true ifa)
                  (fsi-if-land! 'false ifb (n-side bv))
                  (via-enm! av)
                  (have! `(IN ,pt ,sg)
                         (lambda () (subst `(= ,pt ,ifb)) (subst `(= ,ifb ,ifa))
                                    (subst `(= ,ifa (,enm ,av))) (ass)))
                  (ai `(NOT (IN ,pt ,sg))))))
            (lambda ()
              (use-cases `(OR (IN ,bv ,osn) (= ,bv ,nv))
                (lambda ()                              ; a = n, b in OS(n): mirror image
                  (fsi-if-land! 'false ifa (n-side av))
                  (fsi-if-land! 'true ifb)
                  (via-enm! bv)
                  (have! `(IN ,pt ,sg)
                         (lambda () (subst `(= ,pt ,ifa)) (subst `(= ,ifa ,ifb))
                                    (subst `(= ,ifb (,enm ,bv))) (ass)))
                  (ai `(NOT (IN ,pt ,sg))))
                (lambda ()                              ; a = n = b
                  (subst `(= ,av ,nv)) (subst `(= ,bv ,nv)) (rfl))))))
        (fsi-grounded! inj-leaf 'INJ-part)

        ;; ---- SURJ ----
        (dk-focus! surj-leaf)
        (let* ((landed (dk-peel!))                      ; (IN w sg u {pt})
               (wv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) uu)))
                                  "w in the union"))))
          (fsi-mac-h! 'union-membership `(IN ,wv ,uu))
          (use-cases `(OR (IN ,wv ,sg) (IN ,wv (PAIR ,pt ,pt)))
            (lambda ()                                  ; w in sg: its enm-preimage z
              (let* ((ex (dk-apply! surj wv))           ; (FORSOME z (AND (IN z OS(n)) (= (enm z) w)))
                     (zv (dk-skolem! ex)))
                (have! `(IN ,zv ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                (ew zv)
                (dk-conj-close!
                  (lambda ()
                    (if (eq? (car (fsi-goal)) 'IN)
                        (ass)
                        (begin
                          (lam-b)
                          (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,zv ,osn))))
                          (ass)))))))
            (lambda ()                                  ; w = pt: preimage n
              (have! `(AND (IN ,pt SET) (IN ,pt SET)))
              (fsi-mac-h! 'pairing-membership `(IN ,wv (PAIR ,pt ,pt)))
              (have! `(= ,wv ,pt) (lambda () (prop)))
              (have! `(IN ,nv ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
              (ew nv)
              (dk-conj-close!
                (lambda ()
                  (if (eq? (car (fsi-goal)) 'IN)
                      (ass)
                      (begin
                        (lam-b)
                        (fsi-reduce-if! 'false (lambda (c) (equal? c `(IN ,nv ,osn)))
                          (lambda () (dk-fact! 'ord-segment-self nv) (ass)))
                        (subst `(= ,wv ,pt))
                        (rfl))))))))
        (fsi-grounded! surj-leaf 'SURJ-part)))))
(fsi-check-done! 'enum-append-is-bijection)
(qed 'enum-append-is-bijection)

;;; ---------------------------------------------------------------------------
;;; finsum-insert-from-enum:  the peel, with the enumeration a VARIABLE.
;;;
;;; For ANY enm with enm(n) == k (n = CARD X) and enm agreeing with FIN-ENUM X on OS(n),
;;; the enumeration-independence equation
;;;     FINSUM(m,f,X u {k}) = SUM-AG(m, ENUM-FAM(m,f,enm,CARD(X u {k})), CARD(X u {k}))
;;; together with CARD(X u {k}) = succ n yields the recurrence.  Structure-free and
;;; definitional throughout (sum-ag-succ, the ENUM-FAM / FINSUM unfolds, the congruence).
;;;
;;; WHY A SEPARATE LEMMA.  With enm the appended LAMBDA psi, `mac ENUM-FAM' exposes
;;; (psi i) as a redex UNDER the ENUM-FAM lambda's own binder i; `lam-b' reduces every
;;; redex in the goal, licenses that one against the binder's scope (i in NN, not
;;; i in OS(succ n)) and posts (IN i OS(succ n)) as an obligation in the OUTER context,
;;; where i is free -- the unprovable owed leaf CLAUDE.md warns about (2026-08-17).
;;; Quantifying the enumeration keeps (enm i) inert; the two facts psi must satisfy are
;;; then discharged in the main proof, where each (psi t) is a TOP-LEVEL redex whose
;;; licence is in context.

(define fsi-peel-stmt
  '(FORALL m (FORALL f (FORALL x (FORALL k (FORALL enm
     (IMPLIES (IN (CARD x) NN)
     (IMPLIES (= (CARD (UNION x (PAIR k k))) (succ (CARD x)))
     (IMPLIES (== (enm (CARD x)) k)
     (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT (CARD x)))
                                 (== (enm i) ((FIN-ENUM x) i))))
     (IMPLIES (= (FINSUM m f (UNION x (PAIR k k)))
                 (SUM-AG m (ENUM-FAM m f enm (CARD (UNION x (PAIR k k))))
                           (CARD (UNION x (PAIR k k)))))
       (= (FINSUM m f (UNION x (PAIR k k)))
          ((OPR m) (FINSUM m f x) (f k))))))))))))))

(sp (make-wff fsi-peel-stmt))
(let* ((landed (dk-peel!))
       (wd  (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '=)
                                      (pair? (cadr h)) (eq? (car (cadr h)) 'FINSUM)))
                     "the enumeration-independence equation"))
       (mv  (cadr (cadr wd)))
       (fv  (caddr (cadr wd)))
       (uu  (cadddr (cadr wd)))                         ; (UNION x (PAIR k k))
       (xv  (cadr uu))
       (kv  (cadr (caddr uu)))
       (enm (cadddr (caddr (caddr wd))))               ; off (ENUM-FAM m f enm _)
       (n    `(CARD ,xv))
       (osn  `(ORD-SEGMENT ,n))
       (osn1 `(ORD-SEGMENT (succ ,n)))
       (fe   `(FIN-ENUM ,xv))
       (agree (dk-pick (dk-head? 'FORALL) "the agreement hypothesis"))
       (ff   `(ENUM-FAM ,mv ,fv ,enm (succ ,n)))
       (gg   `(ENUM-FAM ,mv ,fv ,fe ,n)))
  ;; 2026-09-18 (LUTINS instantiation).  `sum-ag-segment-congruence' is cited
  ;; at G = ENUM-FAM(m,f,FIN-ENUM x,CARD x), whose THIRD argument is a CHOICE
  ;; and so is never certified defined -- although the functoid's own body is a
  ;; VNB-LAMBDA over NN, which denotes whatever the arguments are.  Landing the
  ;; definedness once, by unfolding to that lambda, certifies G for every later
  ;; instantiation (a `(= t t)' hypothesis is what `asm-establishes-defined?'
  ;; reads).  See the CERTIFICATE GAP note in the report: the functoid clause of
  ;; `pi--defined?' demands defined ARGUMENTS as well as a defined body.
  (have! `(= ,gg ,gg) (lambda () (mac 'ENUM-FAM) (rfl)))
  (have! `(IN ,n ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
  ;; the top term is f k
  (have! `(== (,ff ,n) (,fv ,kv))
         (lambda ()
           (mac 'ENUM-FAM)
           (lam-b)
           (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,n ,osn1))))
           (subst `(== (,enm ,n) ,kv))
           (qrfl)))
  ;; below n the family agrees with X's own
  (have! `(FORALL i (IMPLIES (IN i ,osn) (== (,gg i) (,ff i))))
         (lambda ()
           (let ((iv (dk-di-var!)))
             (dk-fact! 'ord-segment-nn-subset n iv)      ; (IN i NN)
             (have! `(IN ,iv ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
             (mac 'ENUM-FAM)
             (lam-b)
             (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,iv ,osn))))
             (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,iv ,osn1))))
             (dk-apply! agree iv)                        ; (== (enm i) (fe i))
             (subst `(== (,enm ,iv) (,fe ,iv)))
             (qrfl))))
  (have! `(== (FINSUM ,mv ,fv ,xv) (SUM-AG ,mv ,ff ,n))
         (lambda ()
           (mac 'FINSUM)
           (dk-fact! 'sum-ag-segment-congruence n mv gg ff)
           (ass)))
  ;; drive the goal to the shape of the equation in context
  (subst `(== (FINSUM ,mv ,fv ,xv) (SUM-AG ,mv ,ff ,n)))
  (subst `(== (,fv ,kv) (,ff ,n)))
  (dk-fact! 'sum-ag-succ mv ff n)
  (subst `(== ((OPR ,mv) (SUM-AG ,mv ,ff ,n) (,ff ,n)) (SUM-AG ,mv ,ff (succ ,n))))
  (subst `(= (succ ,n) (CARD ,uu)))
  (ass))
(fsi-check-done! 'finsum-insert-from-enum)
(qed 'finsum-insert-from-enum)

;;; ---------------------------------------------------------------------------
;;; The insertion recurrence.  WD names the enumeration-independence support for the
;;; structure class at hand.  Run with the goal freshly `sp'd.

(define (fsi-insert-core! wd)
  (let* ((landed (dk-peel!))
         (split  (dk-split-all!))
         (ftyp (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                         (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)))
                        "the summand's typing"))
         (fv   (cadr ftyp))
         (uu   (cadr (caddr ftyp)))                     ; (UNION X (PAIR k k))
         (mv   (cadr (caddr (caddr ftyp))))             ; the structure, off (CARR m)
         (xv   (cadr uu))
         (kv   (cadr (caddr uu)))
         (n    `(CARD ,xv))
         (osn  `(ORD-SEGMENT ,n))
         (osn1 `(ORD-SEGMENT (succ ,n)))
         (osu  `(ORD-SEGMENT (CARD ,uu)))
         (fe   `(FIN-ENUM ,xv))
         (psi  (fsi-psi fe kv n))
         (psi* `(VNB-LAMBDA i ,osu (IF (IN i ,osn) (,fe i) ,kv))))
    ;; 1-2. the enumeration of X, and X u {k} enumerated with k last
    (dk-fact! 'fin-enum-is-bijection xv)                ; (IN fe (BIJECTION OS(n) X))
    (dk-fact! 'enum-append-is-bijection n xv kv fe)     ; (IN psi (BIJECTION OS(succ n) X u {k}))
    ;; 3. cardinal and sethood bookkeeping
    (have! `(AND (IN ,kv SET) (NOT (IN ,kv ,xv))))
    (dk-fact! 'card-insert xv kv)                       ; (= (CARD U) (succ_ORD n))
    (dk-fact! 'ord-succ-nn n)                           ; (= (succ_ORD n) (succ n))
    (have! `(= (CARD ,uu) (succ ,n))
           (lambda () (subst `(= (succ ,n) (succ_ORD ,n))) (ass)))
    (dk-fact! 'nn-succ-closed n)
    (have! `(IN (CARD ,uu) NN) (lambda () (subst `(= (CARD ,uu) (succ ,n))) (ass)))
    (have! `(AND (IN ,kv SET) (IN ,kv SET)))
    (dk-fact! 'pairing kv kv)
    (have! `(AND (IN ,xv SET) (IN (PAIR ,kv ,kv) SET)))
    (dk-fact! 'union-set-closure xv `(PAIR ,kv ,kv))    ; (IN U SET)
    (have! `(IN ,psi* (BIJECTION ,osu ,uu))
           (lambda () (subst `(= (CARD ,uu) (succ ,n))) (ass)))
    ;; 4. enumeration-independence at psi*
    (dk-fact! wd uu mv fv psi*)
    ;; 5. psi* puts k at index n ...
    (have! `(IN ,n ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (have! `(IN ,n ,osu) (lambda () (subst `(= (CARD ,uu) (succ ,n))) (ass)))
    (have! `(== (,psi* ,n) ,kv)
           (lambda ()
             (lam-b)
             (fsi-reduce-if! 'false (lambda (c) (equal? c `(IN ,n ,osn)))
               (lambda () (dk-fact! 'ord-segment-self n) (ass)))
             (qrfl)))
    ;; ... and agrees with FIN-ENUM X below n
    (have! `(FORALL i (IMPLIES (IN i ,osn) (== (,psi* i) (,fe i))))
           (lambda ()
             (let ((iv (dk-di-var!)))
               (have! `(IN ,iv ,osn1) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (have! `(IN ,iv ,osu) (lambda () (subst `(= (CARD ,uu) (succ ,n))) (ass)))
               (lam-b)
               (fsi-reduce-if! 'true (lambda (c) (equal? c `(IN ,iv ,osn))))
               (qrfl))))
    ;; 6. the peel
    (dk-fact! 'finsum-insert-from-enum mv fv xv kv psi*)
    (ass)))

;;; finsum-insert -- statement copied from theorem-library/prod-of-sums.scm.
(sp (make-wff
  '(FORALL m (IMPLIES (IS-COMM-MONOID m)
      (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL k (IMPLIES (AND (IN k SET) (NOT (IN k X)))
      (FORALL f (IMPLIES (IN f (FUN (UNION X (PAIR k k)) (CARR m)))
        (= (FINSUM m f (UNION X (PAIR k k)))
           ((OPR m) (FINSUM m f X) (f k)))))))))))))
(fsi-insert-core! 'finsum-comm-monoid-well-defined)
(fsi-check-done! 'finsum-insert)
(qed 'finsum-insert)

;;; finsum-insert-ag -- statement of theorem-library/finsum-additive.scm with tf/tfin expanded.
(sp (make-wff
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL X (IMPLIES (IN X SET) (IMPLIES (IN (CARD X) NN)
     (FORALL k (IMPLIES (IN k SET) (IMPLIES (NOT (IN k X))
     (FORALL f (IMPLIES (IN f (FUN (UNION X (PAIR k k)) (CARR ag)))
       (= (FINSUM ag f (UNION X (PAIR k k)))
          ((OPR ag) (FINSUM ag f X) (f k)))))))))))))))
(fsi-insert-core! 'finsum-well-defined)
(fsi-check-done! 'finsum-insert-ag)
(qed 'finsum-insert-ag)

;;; ---------------------------------------------------------------------------
;;; finsum-empty:  FINSUM over EMPTY-SET is the identity.
;;;
;;; An asserted support (theorem-library/finsum-empty.scm, PSS-promoted
;;; 2026-05-27, warranted `informal') until 2026-09-16, when it became the leaf
;;; the n = 0 case of the LINCOMB span arc billed.  The warrant WAS the proof:
;;; unfold FINSUM, card-empty (primitive) turns CARD(EMPTY-SET) into 0, and
;;; sum-ag-zero (definitional) collapses the empty fold.  No citer loads between
;;; the old support and this file.

(sp (make-wff '(FORALL ag (FORALL f (== (FINSUM ag f EMPTY-SET) (IDEN ag))))))
(dk-peel!)
(mac 'FINSUM)
(fact 'card-empty)
(subst '(= (CARD EMPTY-SET) 0))
(mac 'sum-ag-zero)
(qrfl)
(fsi-check-done! 'finsum-empty)
(qed 'finsum-empty)
