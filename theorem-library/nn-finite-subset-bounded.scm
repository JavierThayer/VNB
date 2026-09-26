;;; nn-finite-subset-bounded.scm -- a finite subset of NN is bounded.
;;;
;;;     nn-finite-subset-bounded:
;;;       forall T.  T subset NN  =>  CARD(T) in NN  =>
;;;         forsome N.  N in NN  and  forall y in NN.  N <= y  =>  not (y in T)
;;;
;;; Statement UNCHANGED from the support it retires
;;; (theorem-library/subsequence-principle.scm:150, warranted `well-known').
;;;
;;; THE PROOF is `finite-set-induction' (structure-library/cardinality.scm:108,
;;; primitive) on T, with the class instantiated to the COMP
;;;
;;;     D = { t_ | t_ subset NN  =>
;;;                forsome n_. n_ in NN and forall y_ in NN. n_ <= y_ => not (y_ in t_) }
;;;
;;; The inclusion guard is INSIDE the class property: the step of the induction
;;; inserts an arbitrary SET x, and only under UNION(S,{x}) subset NN is x a
;;; natural number that a bound can be compared with.  Second firing of
;;; finite-set-induction and second COMP in the tree (card-subset-nn.scm is the
;;; first; the driver shape is copied from there).
;;;
;;;   BASE  EMPTY-SET in D: bound 0 (nn-zero-in), nothing is in EMPTY-SET.
;;;   STEP  S in SET, CARD S in NN, S in D, x in SET, x not in S,
;;;         UNION(S,{x}) subset NN  =>  bounded.  S subset NN and x in NN
;;;         (union-membership + subset-mem-fwd), so the hypothesis gives a bound
;;;         N for S; nn-pair-upper-bound (nn-order-basics.scm) gives c in NN
;;;         with succ x <= c and N <= c, and c bounds the union: for y in NN
;;;         with c <= y, y in S is refuted through N <= y (nn-le-trans-guarded)
;;;         and y = x through succ x <= y, i.e. succ x <= x, which
;;;         nn-le-imp-neq-succ (nn-order-ord.scm) refutes.
;;;   END   T subset NN and NN in SET make T a set (subclass-of-set-is-set,
;;;         subset-lemmas.scm), so T in D, and the class property at T is the
;;;         statement.
;;;
;;; LOAD WINDOW [subset-lemmas, subsequence-principle).  lo is forced by
;;; subclass-of-set-is-set (theorem-library/subset-lemmas, table position 147;
;;; nn-pair-upper-bound / nn-le-trans-guarded at 136 and nn-le-imp-neq-succ /
;;; nn-le-succ at 135 are below it); hi by the earliest real citer,
;;; subsequence-principle.scm itself (table position 208, line 221 -- the
;;; support is defined at its line 150).  Everything else cited is primitive.
;;;
;;; Helper prefix: nfb-.  The peel / split / pick / only / apply / di-var kit
;;; this file shared verbatim with card-subset-nn.scm is in driver-kit.scm since
;;; 2026-09-14 (dk-peel!, dk-split-all!, dk-pick, dk-only!, dk-apply!,
;;; dk-di-var!, dk-conj-close!).

;;; --- file-local helpers (nfb- prefix) -----------------------------------

(define nfb-bound
  '(FORSOME n_ (AND (IN n_ NN)
                    (FORALL y_ (IMPLIES (IN y_ NN)
                                 (IMPLIES (<= n_ y_) (NOT (IN y_ t_))))))))
(define nfb-prop  (list 'IMPLIES '(SUBSET t_ NN) nfb-bound))
(define nfb-class (list 'COMP 't_ nfb-prop))

;; Split an AND goal to its leaves and run the handler on each goal.
(define (nfb-each-conjunct! handler)
  (dk-conj-close! (lambda () (handler (dk-goal)))))

;; x in PAIR(x, x), for x in SET.  pairing-membership plus reflexivity, the
;; propositional residue decided by (prop).
(define (nfb-in-own-pair! x)
  (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
  (let* ((pm  (dk-fact! 'pairing-membership x x))
         (pmx (inst*! pm x))
         (eqx (list '= x x)))
    (have! eqx (lambda () (rfl)))
    (dk-only! pmx eqx)
    (prop)))

;;; -----------------------------------------------------------------------
;;; BASE:  EMPTY-SET in D, bound 0.

(define (nfb-base!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (cond
       ((equal? (dk-goal) '(in empty-set set))
        (fact 'empty-set-is-set) (ass))
       (else
        (dk-peel!)                              ; assume EMPTY-SET subset NN
        (ew 0)
        (nfb-each-conjunct!
         (lambda (g)
           (if (eq? (car g) 'in)
               (begin (fact 'nn-zero-in) (ass))
               (begin
                 (dk-peel!)                     ; goal (not (in y EMPTY-SET))
                 (let ((y (cadr (cadr (dk-goal)))))
                   (fact 'empty-set-has-no-members y)
                   (ass)))))))))
   (dk-opened (lambda () (comp-mi)))))

;;; -----------------------------------------------------------------------
;;; STEP.

(define nfb-step-formula
  `(FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (IN S ,nfb-class)))
     (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x S)))
       (IN (UNION S (PAIR x x)) ,nfb-class))))))

(define (nfb-step!)
  (let* ((landed (dk-peel!))
         (g      (dk-goal))                       ; (in (union S (pair x x)) D)
         (S      (cadr (cadr g)))
         (x      (cadr (caddr (cadr g))))
         (U      (list 'UNION S (list 'PAIR x x))))
    (dk-split-all! landed)
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN S nfb-class)))
                              (dk-head? 'implies))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (equal? (dk-goal) (list 'in U 'set))
             (nfb-step-sethood! S x)
             (nfb-step-bound! S x U ih)))
       (dk-opened (lambda () (comp-mi)))))))

(define (nfb-step-sethood! S x)
  (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
  (fact 'pairing x x)
  (have! (list 'AND (list 'IN S 'SET) (list 'IN (list 'PAIR x x) 'SET)))
  (fact 'union-set-closure S (list 'PAIR x x))
  (ass))

;; goal: U subset NN  =>  forsome n_. n_ in NN and forall y_ in NN. n_ <= y_ => not (y_ in U)
(define (nfb-step-bound! S x U ih)
  (dk-peel!)                                     ; assume (SUBSET U NN)
  ;; S subset NN, so the hypothesis yields a bound N for S
  (have! (list 'SUBSET S 'NN)
    (lambda ()
      (mac 'subset-def)
      (let ((v (dk-di-var! (lambda (g) (cadr g)))))   ; goal (in v nn)
        (have! (list 'IN v U) (lambda () (mac 'union-membership) (oi-l) (ass)))
        (fact 'subset-mem-fwd U 'NN v)
        (ass))))
  ;; x in NN too
  (have! (list 'IN x U)
    (lambda () (mac 'union-membership) (oi-r) (nfb-in-own-pair! x)))
  (fact 'subset-mem-fwd U 'NN x)
  (let* ((ex    (dk-apply! ih))                  ; the bound for S, existential
         (atoms (dk-split! ex))
         (N     (cadr (dk-pick (lambda (f) (and (memq f atoms)
                                                  ((dk-head? 'in) f)
                                                  (eq? (caddr f) 'nn)))
                                "the bound N of S")))
         (ihy   (dk-pick (lambda (f) (and (memq f atoms) ((dk-head? 'forall) f)))
                          "the bounding universal of S")))
    ;; c in NN with succ x <= c and N <= c
    (fact 'nn-succ-closed x)
    (let* ((cx    (dk-fact! 'nn-pair-upper-bound (list 'succ x) N))
           (catoms (dk-split! cx))
           (c     (caddr (dk-pick (lambda (f) (and (memq f catoms)
                                                     ((dk-head? '<=) f)
                                                     (equal? (cadr f) (list 'succ x))))
                                   "succ x <= c"))))
      (ew c)
      (nfb-each-conjunct!
       (lambda (g)
         (if (eq? (car g) 'in)
             (ass)                                ; (in c nn)
             (nfb-step-excludes! S x U N c ihy)))))))

;; goal: forall y_ in NN. c <= y_ => not (y_ in U)
(define (nfb-step-excludes! S x U N c ihy)
  (dk-peel!)                                     ; (in y nn), (<= c y); goal (not (in y U))
  (let ((y (cadr (cadr (dk-goal)))))
    (di)                                          ; assume (in y U); goal FALSITY
    (let ((cases (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN y U))))))
      (use-cases cases
        ;; y in S: then N <= y, and the bound for S refutes it
        (lambda ()
          (fact 'nn-le-trans-guarded N c y)
          (ai (dk-apply! ihy y)))
        ;; y in {x}: then y = x, so succ x <= x
        (lambda ()
          (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
          (let* ((pm  (dk-fact! 'pairing-membership x x))
                 (pmy (inst*! pm y))
                 (eqy (list '= y x)))
            (have! eqy (lambda () (dk-only! pmy (list 'IN y (list 'PAIR x x))) (prop)))
            (fact 'nn-le-trans-guarded (list 'succ x) c y)
            (let ((neq (dk-fact! 'nn-le-imp-neq-succ y (list 'succ x))))
              (have! (list '= (list 'succ x) (list 'succ y))
                     (lambda () (subst eqy) (rfl)))
              (ai neq))))))))

;;; -----------------------------------------------------------------------
;;; THE THEOREM.

(quietly (lambda ()
  (sp (make-wff '(FORALL T
     (IMPLIES (SUBSET T NN)
       (IMPLIES (IN (CARD T) NN)
         (FORSOME N (AND (IN N NN)
                         (FORALL y (IMPLIES (IN y NN)
                                     (IMPLIES (<= N y) (NOT (IN y T))))))))))))
  (have! (list 'IN 'EMPTY-SET nfb-class) nfb-base!)
  (have! nfb-step-formula nfb-step!)
  (have! (list 'AND (list 'IN 'EMPTY-SET nfb-class) nfb-step-formula))
  (let ((ind (dk-fact! 'finite-set-induction nfb-class)))
    (let* ((landed (dk-peel!))
           (T      (cadr (dk-pick (lambda (f) (and (memq f landed) ((dk-head? 'subset) f)))
                                   "T subset NN"))))
      (fact 'nn-is-set)
      (fact 'subclass-of-set-is-set T 'NN)
      (have! (list 'AND (list 'IN T 'SET) (list 'IN (list 'CARD T) 'NN)))
      (let* ((inT (dk-apply! ind T))
             (pT  (dk-landed-find (lambda () (comp-me inT)) (dk-head? 'implies))))
        (dk-apply! pT)
        (ass))))))
(qed 'nn-finite-subset-bounded)
(topic! 'nn-finite-subset-bounded 'combinatorial)
