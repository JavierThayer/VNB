;;; nn-nested-subset-chain-proof.scm -- a descending NN-indexed family is a chain.
;;;
;;;   fam(succ k) subset fam(k) for every k   =>   k <= j  =>  fam(j) subset fam(k)
;;;
;;; This was L2 of theorem-library/diagonalization-lemmas.scm, asserted
;;; `well-known' with the note that its mechanical proof is "a routine
;;; NN-induction with no library payoff to grind out".  The estimate was right
;;; about the shape and wrong about the cost: the whole thing is forty lines and
;;; took three attempts, so it is now proven and the assertion is gone.
;;;
;;; TWO STATEMENTS, and the reason is mechanical rather than mathematical.  The
;;; induction is on j, and `di' is greedy -- one call takes the whole leading
;;; FORALL/IMPLIES prefix, so there is no way to introduce k alone and leave a
;;; `forall j' for use-induction to see.  So the induction is done on the
;;; j-outermost form, and the original binder order is recovered from it in
;;; three lines.  Downstream citations (diagonalization.scm) name the second.
;;;
;;; Ingredients, all already in the library: use-induction (driver-kit),
;;; nn-le-zero-is-zero (PROVEN, nn-order-proof), nn-le-succ-cases (order-lemmas),
;;; subset-trans (PROVEN, subset-lemmas), subset-def (the macete, for
;;; reflexivity inline).

;;; ---- the induction, j outermost ----
(sp (make-wff
  '(FORALL fam
     (IMPLIES
       (FORALL k (IMPLIES (IN k NN) (SUBSET (fam (succ k)) (fam k))))
       (FORALL j (IMPLIES (IN j NN)
         (FORALL k (IMPLIES (IN k NN)
           (IMPLIES (<= k j) (SUBSET (fam j) (fam k)))))))))))

(di)                                              ; fam
(define NC-STEP (dk-landed-1 (lambda () (di))))   ; the descending hypothesis
(define NC-BR (use-induction))                    ; induct on j

;;; base:  forall k in NN.  k <= 0  =>  fam(0) subset fam(k)
;;; k <= 0 forces k = 0, and then both sides are the same class.
(dk-focus! (cdr (assq 'base NC-BR)))
(dk-peel-to! 'SUBSET)                  ; peel k, (IN k NN), (<= k 0) -- never count di's
(fact 'nn-le-zero-is-zero 'k)
(subst '(= k 0))
(mac 'subset-def) (di) (ass)           ; reflexivity, inline (no named subset-refl)

;;; step:  forall k in NN.  k <= succ j  =>  fam(succ j) subset fam(k)
;;; k <= succ j splits: either k <= j, where the IH gives fam(j) subset fam(k)
;;; and one more step of the hypothesis composes on the left, or k = succ j,
;;; where the two sides coincide.
(dk-focus! (cdr (assq 'step NC-BR)))
(define NC-JV (cdr (assq 'var NC-BR)))
(define NC-IH (cdr (assq 'ih  NC-BR)))
(dk-peel-to! 'SUBSET)                  ; k, (IN k NN), (<= k (succ j))
(fact 'nn-le-succ-cases NC-JV 'k)      ; -> (OR (<= k j) (= k (succ j)))
(use-cases
  (list (list '<= 'k NC-JV) (list '= 'k (list 'succ NC-JV)))
  (lambda ()                                              ; k <= j
    (inst+ NC-IH 'k)                                      ; fam(j) subset fam(k)
    (inst+ NC-STEP NC-JV)                                 ; fam(succ j) subset fam(j)
    ;; 2026-09-18 (LUTINS instantiation): `fact subset-trans' is cited at
    ;; fam(succ j), fam(j) and fam(k) -- applications of the VARIABLE fam, and
    ;; SUBSET is not one of the strict relations, so nothing in the context
    ;; certifies any of them.  Transitivity unfolded instead: `mac'/`mac-h' on
    ;; subset-def are REWRITES (no instantiation), the goal's own peel lands
    ;; (IN z fam(succ j)), and each unfolded universal is then instantiated at
    ;; the VARIABLE z, which owes nothing.
    (mac 'subset-def)
    (let ((zv (dk-di-var!)))
      (inst*! (dk-landed-1
               (lambda () (mac-h 'subset-def
                                 (list 'SUBSET (list 'fam (list 'succ NC-JV))
                                               (list 'fam NC-JV)))))
              zv)
      (inst*! (dk-landed-1
               (lambda () (mac-h 'subset-def
                                 (list 'SUBSET (list 'fam NC-JV) (list 'fam 'k)))))
              zv)
      (ass)))
  (lambda ()                                              ; k = succ j
    (subst (list '= 'k (list 'succ NC-JV)))
    (mac 'subset-def) (di) (ass)))

(qed 'nn-nested-subset-chain-j)
(topic! 'nn-nested-subset-chain-j 'combinatorial)

;;; ---- the original binder order, k before j ----
(sp (make-wff
  '(FORALL T
     (IMPLIES
       (FORALL k (IMPLIES (IN k NN) (SUBSET (T (succ k)) (T k))))
       (FORALL k (IMPLIES (IN k NN)
         (FORALL j (IMPLIES (IN j NN)
           (IMPLIES (<= k j) (SUBSET (T j) (T k)))))))))))
(dk-peel-to! 'SUBSET)
(fact 'nn-nested-subset-chain-j 'T 'j 'k)   ; fam, then j, then k -- `fact' peels
(ass)                                       ; only the universals it is given
(qed 'nn-nested-subset-chain)
(topic! 'nn-nested-subset-chain 'combinatorial)
