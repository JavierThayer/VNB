;;; nn-infinite.scm -- NN is infinite, and the two leaves that hang on it.
;;;
;;;   inf-subsets-unfold       forall a_.  INF-SUBSETS(a_) == SEP S (POWER a_) (NOT (IN (CARD S) NN))
;;;   nn-not-finite            NOT (IN (CARD NN) NN)
;;;   nn-in-inf-subsets        NN in INF-SUBSETS(NN)                        [retires a support]
;;;   inf-subset-nn-unbounded  forall T in INF-SUBSETS(NN), u in NN.
;;;                              forsome y.  y in NN and y in T and u < y   [retires a support]
;;;
;;; THE CONTENT is `nn-not-finite', which nothing in the tree stated before
;;; (scratchpad/triage/arith-order-card.md, item 4).  Suppose CARD(NN) in NN.
;;; ORD-SEGMENT(succ CARD(NN)) is a subset of NN (ord-segment-nn-subset), so
;;; card-subset-mono at B = NN gives CARD(ORD-SEGMENT(succ CARD(NN))) <= CARD(NN),
;;; and card-segment reads the left side as succ CARD(NN).  So succ n <= n for
;;; n = CARD(NN), and nn-le-imp-neq-succ (j <= k => j /= succ k, at j = succ n,
;;; k = n) denies succ n = succ n, which `rfl' has (succ n is typed in context).
;;;
;;; nn-in-inf-subsets is then `mac' the functoid, `sep-mi', power-set-membership
;;; and nn-not-finite.  inf-subset-nn-unbounded is the classical argument: deny
;;; the witness, push the negation through (push-not-h), and every z in T is
;;; then <= u, so T lies in ORD-SEGMENT(succ u) (seg-mem-lt plus the NN order
;;; bricks -- seg-mem-succ-le and nn-not-lt-le are avoided, both billing the
;;; unguarded co-le-trans), a finite set, and card-subset-nn makes CARD(T) in
;;; NN -- against T in
;;; INF-SUBSETS(NN), read apart by `mac-h' of inf-subsets-unfold + `sep-me'
;;; (the functoid trap: `mac-h' cannot unfold INF-SUBSETS by its own name).
;;;
;;; LOAD WINDOW.  lo: theorem-library/card-inequalities (card-subset-mono,
;;; load.scm:1011) -- the latest citation; card-subset-nn (:991),
;;; ord-segment-arith (seg-mem-lt, :902), nn-order-basics (nn-le-trans-guarded,
;;; nn-le-refl, :675), nn-not-le-succ-le (:669), nn-order-ord (nn-le-succ,
;;; nn-le-imp-neq-succ, :668), equality-basics (neq-sym, :590),
;;; ord-segment-nn-subset (:409) and push-not all sit above it.  hi: theorem-library/diagonalization
;;; (load.scm:1097), the earliest citer of inf-subset-nn-unbounded;
;;; block-family-combinatorial-proof (:1103) is the earliest citer of
;;; nn-in-inf-subsets.  So the slot is anywhere in [card-inequalities,
;;; diagonalization); immediately after card-inequalities is the natural one.
;;;
;;; CHAINS TO ord-segment-nn-subset (theorem-library/ord-segment-nn-subset.scm:9,
;;; asserted `informal', a leaf of the same wave): it is the only way in the
;;; tree to say that a member of ORD-SEGMENT(m), m in NN, is a natural.
;;;
;;; Helper prefix: nni-.

;;; ---------------------------------------------------------------------
;;; inf-subsets-unfold -- the functoid's defining equation as a THEOREM, so
;;; that `mac-h' can rewrite a hypothesis (CLAUDE.md, "Where a definition
;;; lives").  `==', not `=': a bare SEP term is not syntactically defined.
(sp (make-wff '(FORALL a_ (== (INF-SUBSETS a_)
                              (SEP S (POWER a_) (NOT (IN (CARD S) NN)))))))
(di)
(mac 'INF-SUBSETS)
(qrfl)
(qed 'inf-subsets-unfold)
(gloss! 'inf-subsets-unfold
  "INF-SUBSETS(A) is the separation { S in POWER(A) : CARD(S) not in NN },
   as a citable equation.")
(topic! 'inf-subsets-unfold 'plumbing)

;;; ---------------------------------------------------------------------
;;; nn-not-finite -- CARD(NN) is not a natural number.
(sp (make-wff '(NOT (IN (CARD NN) NN))))
(di)                                          ; assume (IN (CARD NN) NN); goal FALSITY
(fact 'nn-is-set)
(fact 'nn-succ-closed '(CARD NN))             ; succ CARD(NN) in NN
;; ORD-SEGMENT(succ CARD(NN)) subset NN, elementwise
(have! '(SUBSET (ORD-SEGMENT (succ (CARD NN))) NN)
       (lambda ()
         (mac 'subset-def)
         (let* ((landed (dk-landed-1 (lambda () (di))))   ; (IN x (ORD-SEGMENT ...))
                (x      (cadr landed)))
           (fact 'ord-segment-nn-subset '(succ (CARD NN)) x)
           (ass))))
;; CARD(ORD-SEGMENT(succ CARD(NN))) <= CARD(NN), and the left side is succ CARD(NN)
(fact 'card-subset-mono 'NN '(ORD-SEGMENT (succ (CARD NN))))
(fact 'card-segment '(succ (CARD NN)))
(have! '(<= (succ (CARD NN)) (CARD NN))
       (lambda ()
         (subst '(= (succ (CARD NN)) (CARD (ORD-SEGMENT (succ (CARD NN))))))
         (ass)))
;; succ n <= n denies succ n = succ n
(fact 'nn-le-imp-neq-succ '(CARD NN) '(succ (CARD NN)))
(have! '(= (succ (CARD NN)) (succ (CARD NN))) (lambda () (rfl)))
(ai '(NOT (= (succ (CARD NN)) (succ (CARD NN)))))
(qed 'nn-not-finite)
(gloss! 'nn-not-finite
  "NN is infinite: its cardinal is not a natural number.  From card-subset-mono
   on ORD-SEGMENT(succ CARD(NN)) subset NN.")
(topic! 'nn-not-finite 'combinatorial)

;;; ---------------------------------------------------------------------
;;; nn-in-inf-subsets -- statement copied from structure-library/inf-subsets.scm:34.
(sp (make-wff '(IN NN (INF-SUBSETS NN))))
(mac 'INF-SUBSETS)                            ; (IN NN (SEP S (POWER NN) ...))
(for-each
 (lambda (l)
   (dk-focus! l)
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'NOT)                     ; (NOT (IN (CARD NN) NN))
        (fact 'nn-not-finite)
        (ass))
       (else                                   ; (IN NN (POWER NN))
        (mac 'power-set-membership)            ; (AND (IN NN SET) (FORALL z ...))
        (for-each
         (lambda (m)
           (dk-focus! m)
           (if (eq? (car (dk-goal)) 'FORALL)
               (begin (di) (ass))              ; z in NN => z in NN
               (begin (fact 'nn-is-set) (ass))))
         (dk-opened (lambda () (di))))))))
 (dk-opened (lambda () (sep-mi))))
(qed 'nn-in-inf-subsets)
(topic! 'nn-in-inf-subsets 'plumbing)

;;; ---------------------------------------------------------------------
;;; inf-subset-nn-unbounded -- statement copied from
;;; theorem-library/diagonalization-lemmas.scm:58-62.
(sp (make-wff
  '(FORALL T
     (IMPLIES (IN T (INF-SUBSETS NN))
       (FORALL u (IMPLIES (IN u NN)
         (FORSOME y (AND (IN y NN) (AND (IN y T) (< u y))))))))))
(dk-peel!)
(define nni-T
  (cadr (dk-pick (lambda (f) (and ((dk-head? 'IN) f) (pair? (caddr f))
                                  (eq? (car (caddr f)) 'INF-SUBSETS)))
                 "the INF-SUBSETS typing of T")))
(define nni-u
  (cadr (dk-pick (lambda (f) (and ((dk-head? 'IN) f) (eq? (caddr f) 'NN)))
                 "the NN typing of u")))
;; deny the witness, and push the negation through the existential:
;;   (FORALL y (IMPLIES (IN y NN) (NOT (AND (IN y T) (< u y)))))
(define nni-neg (dk-landed-1 (lambda () (pbc))))
(define nni-all (dk-landed-find (lambda () (push-not-h nni-neg)) (dk-head? 'FORALL)))
;; read T's membership apart: T in SET, T subset NN (elementwise), CARD(T) not in NN
(define nni-sep
  (dk-landed-find (lambda () (mac-h 'inf-subsets-unfold (list 'IN nni-T '(INF-SUBSETS NN))))
                  (lambda (f) (and ((dk-head? 'IN) f) (pair? (caddr f))
                                   (eq? (car (caddr f)) 'SEP)))))
(sep-me nni-sep)
(define nni-pow-parts
  (dk-split! (dk-landed-1 (lambda () (mac-h 'power-set-membership
                                            (list 'IN nni-T '(POWER NN)))))))
(define nni-sub
  (car (filter (lambda (f) (and ((dk-head? 'FORALL) f) (not (equal? f nni-all))))
               nni-pow-parts)))
;; ORD-SEGMENT(succ u) is a finite set
(fact 'nn-succ-closed nni-u)
(fact 'nn-subset-ord (list 'succ nni-u))
(fact 'ord-segment-is-set (list 'succ nni-u))
(fact 'card-segment (list 'succ nni-u))
(have! (list 'IN (list 'CARD (list 'ORD-SEGMENT (list 'succ nni-u))) 'NN)
       (lambda ()
         (subst (list '= (list 'CARD (list 'ORD-SEGMENT (list 'succ nni-u)))
                         (list 'succ nni-u)))
         (ass)))
(have! (list 'AND (list 'IN (list 'ORD-SEGMENT (list 'succ nni-u)) 'SET)
                  (list 'IN (list 'CARD (list 'ORD-SEGMENT (list 'succ nni-u))) 'NN)))
;; T subset ORD-SEGMENT(succ u): every z in T is a natural with NOT (u < z),
;; hence z <= u (totality, run as nn-not-lt-le runs it but on
;; nn-le-trans-guarded), hence z in the segment -- the backward half of
;; seg-mem-succ-le, inlined as interval-card-in-nn.scm does: seg-mem-succ-le
;; and nn-not-lt-le both bill the unguarded co-le-trans, and every brick of
;; the half needed here is proven modulo 0.
(define nni-incl
  (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z nni-T)
                         (list 'IN 'z (list 'ORD-SEGMENT (list 'succ nni-u))))))
(have! nni-incl
       (lambda ()
         (let* ((zin (dk-landed-1 (lambda () (di))))      ; (IN z T)
                (z   (cadr zin))
                (u   nni-u)
                (sz  (list 'succ z))
                (su  (list 'succ u)))
           (dk-apply! nni-sub z)                          ; (IN z NN)
           (let ((nand (dk-apply! nni-all z)))            ; (NOT (AND (IN z T) (< u z)))
             (have! (list 'NOT (list '< u z))
                    (lambda ()
                      (di)                                ; assume u < z; goal FALSITY
                      (have! (list 'AND zin (list '< u z)))
                      (ai nand))))
           ;; z <= u
           (have! (list '<= z u)
                  (lambda ()
                    (use-em (list '= z u)
                      (lambda ()
                        (subst (list '= z u))
                        (fact 'nn-le-refl u)
                        (ass))
                      (lambda ()
                        (fact 'neq-sym z u)                       ; (NOT (= u z))
                        (have! (list 'NOT (list '<= u z))
                               (lambda ()
                                 (di)                             ; assume u <= z
                                 (have! (list '< u z)
                                        (lambda () (mac '<) (from-context!)))
                                 (ai (list 'NOT (list '< u z)))))
                        (fact 'nn-not-le-succ-le u z)             ; (<= (succ z) u)
                        (fact 'nn-succ-closed z)
                        (fact 'nn-le-succ z)                      ; (<= z (succ z))
                        (fact 'nn-le-trans-guarded z sz u)        ; (<= z u)
                        (ass)))))
           ;; z in ORD-SEGMENT(succ u): z < succ u, i.e. z <= succ u and z /= succ u
           (mac 'seg-mem-lt)                                  ; goal (< z (succ u))
           (mac '<)                                           ; (AND (<= z su) (NOT (= z su)))
           (fact 'nn-le-succ u)                               ; (<= u (succ u))
           (fact 'nn-le-trans-guarded z u su)                 ; (<= z (succ u))
           (fact 'nn-le-imp-neq-succ u z)                     ; (NOT (= z (succ u)))
           (from-context!))))
(have! (list 'AND (list 'IN nni-T 'SET) nni-incl))
(fact 'card-subset-nn (list 'ORD-SEGMENT (list 'succ nni-u)) nni-T)   ; (IN (CARD T) NN)
(ai (list 'NOT (list 'IN (list 'CARD nni-T) 'NN)))
(qed 'inf-subset-nn-unbounded)
(topic! 'inf-subset-nn-unbounded 'combinatorial)
