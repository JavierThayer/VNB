;;; card-subset-nn.scm -- a subset of a finite set is finite.
;;;
;;;     card-subset-nn:
;;;       forall X.  X in SET and CARD(X) in NN  =>
;;;         forall S.  S in SET and (forall z in S. z in X)  =>  CARD(S) in NN
;;;
;;; Statement UNCHANGED from the support it retires
;;; (theorem-library/prod-of-sums.scm:73, warranted `well-known').
;;;
;;; THE PROOF is `finite-set-induction' (structure-library/cardinality.scm:108,
;;; primitive) on X, with the class instantiated to the COMP
;;;
;;;     C = { x_ | forall s_. s_ in SET and (forall z_ in s_. z_ in x_)
;;;                            =>  CARD(s_) in NN }
;;;
;;; This is the first firing of finite-set-induction in the tree and the first
;;; COMP instantiated by any library proof (CLAUDE.md: COMP entered the
;;; expression walkers on 2026-08-15; no installed formula holds one).  The two
;;; COMP rules used are the surface `comp-mi' (goal (IN y (COMP x p)) opens
;;; (IN y SET) and p[x:=y]) and `comp-me' (the same on an assumption).
;;;
;;; SHAPE.  The two induction premises are established as closed formulas by
;;; `have!' BEFORE the theorem's own binders are peeled, so every lane runs in
;;; an empty context and `di' keeps the binder names it finds.  Then `fact'
;;; auto-detaches the conjoined premise, `comp-me' reads the class property off
;;; (IN X C), and one instantiation at S closes the goal.
;;;
;;;   BASE  (IN EMPTY-SET C):  a subclass s of EMPTY-SET is EMPTY-SET
;;;         (class-extensionality; the backward direction is
;;;         empty-set-has-no-members), and card-empty gives CARD = 0.
;;;   STEP  S in SET, CARD S in NN, S in C, x in SET, x not in S
;;;         =>  UNION(S, {x}) in C.  Sethood is union-set-closure + pairing.
;;;         For t subset S u {x} the case split is `use-em' on x in t:
;;;           x in t:      t = UNION({x}, INTERSECTION(t, S)) by extensionality;
;;;                        INTERSECTION(t, S) is a subset of S, so finite by the
;;;                        induction hypothesis, and card-union-singleton-bound
;;;                        (makeset-card-bound.scm) finishes.
;;;           x not in t:  t subset S outright, and the hypothesis applies.
;;;
;;; LOAD WINDOW [makeset-card-bound, card-inequalities) -- one slot.  lo is
;;; forced by card-union-singleton-bound (theorem-library/makeset-card-bound,
;;; table position 173); hi by the earliest real citer, card-inequalities.scm
;;; (table position 174; `card-subset-mono' cites this theorem three times).
;;; Everything else cited is primitive (library.scm base axioms, cardinality.scm,
;;; number-systems.scm).
;;;
;;; Helper prefix: csn-.  The peel / split / pick / only / apply / di-var kit this
;;; file was written with moved into driver-kit.scm on 2026-09-14 (dk-peel!,
;;; dk-split-all!, dk-pick, dk-only!, dk-apply!, dk-di-var!); the calls below are
;;; the dk- ones.

;;; --- file-local helpers (csn- prefix) -----------------------------------

;; The class property, x_ free, and the class itself.
(define csn-prop
  '(FORALL s_ (IMPLIES (AND (IN s_ SET)
                            (FORALL z_ (IMPLIES (IN z_ s_) (IN z_ x_))))
                       (IN (CARD s_) NN))))
(define csn-class (list 'COMP 'x_ csn-prop))

;;; -----------------------------------------------------------------------
;;; BASE:  EMPTY-SET in C.

(define (csn-base!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (let ((g (dk-goal)))
       (cond
         ((equal? g '(in empty-set set))
          (fact 'empty-set-is-set) (ass))
         (else
          ;; goal: forall s_. s_ in SET and (forall z_ in s_. z_ in EMPTY-SET)
          ;;         => CARD(s_) in NN
          (let* ((landed (dk-peel!))
                 (s      (cadr (cadr (dk-goal)))))       ; (in (card s) nn)
            (dk-split-all! landed)
            (let ((sub (dk-pick (dk-head? 'forall) "the inclusion s subset EMPTY-SET")))
              (have! (list '= s 'EMPTY-SET)
                (lambda ()
                  (bc* 'class-extensionality)
                  (let ((v (dk-di-var! (lambda (g) (cadr (cadr g))))))
                    (inst*! sub v)
                    (fact 'empty-set-has-no-members v)
                    (prop))))
              (subst (list '= s 'EMPTY-SET))
              (mac 'card-empty)
              (fact 'nn-zero-in)
              (ass)))))))
   (dk-opened (lambda () (comp-mi)))))

;;; -----------------------------------------------------------------------
;;; STEP:  S in SET, CARD S in NN, S in C, x in SET, x not in S
;;;          =>  UNION(S, PAIR(x, x)) in C.

;; The step premise of finite-set-induction with C := csn-class, spelled so
;; that `fact' finds it in context up to alpha.
(define csn-step-formula
  `(FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (IN S ,csn-class)))
     (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x S)))
       (IN (UNION S (PAIR x x)) ,csn-class))))))

(define (csn-step!)
  (let* ((landed (dk-peel!))
         (g      (dk-goal))                       ; (in (union S (pair x x)) C)
         (S      (cadr (cadr g)))
         (x      (cadr (caddr (cadr g))))
         (U      (list 'UNION S (list 'PAIR x x))))
    (dk-split-all! landed)
    ;; the induction hypothesis: the class property at S
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN S csn-class)))
                              (dk-head? 'forall))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (equal? (dk-goal) (list 'in U 'set))
             (csn-step-sethood! S x)
             (csn-step-property! S x U ih)))
       (dk-opened (lambda () (comp-mi)))))))

(define (csn-step-sethood! S x)
  (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
  (fact 'pairing x x)
  (have! (list 'AND (list 'IN S 'SET) (list 'IN (list 'PAIR x x) 'SET)))
  (fact 'union-set-closure S (list 'PAIR x x))
  (ass))

;; goal: forall s_. s_ in SET and (forall z_ in s_. z_ in U) => CARD(s_) in NN
(define (csn-step-property! S x U ih)
  (let* ((landed (dk-peel!))
         (t      (cadr (cadr (dk-goal))))
         (I      (list 'INTERSECTION t S)))
    (dk-split-all! landed)
    (let ((sub (dk-pick (lambda (f) (and ((dk-head? 'forall) f)
                                          (not (eq? f ih))
                                          (dk-contains? f U)))
                         "the inclusion t subset U")))
      ;; {x}-membership, for both branches
      (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
      (let ((pm (dk-fact! 'pairing-membership x x)))
        (use-em (list 'IN x t)
          ;; x in t:  t = UNION({x}, INTERSECTION(t, S))
          (lambda ()
            (have! (list '= t (list 'UNION (list 'PAIR x x) I))
              (lambda ()
                (bc* 'class-extensionality)
                (let ((v (dk-di-var! (lambda (g) (cadr (cadr g))))))
                  (mac 'union-membership)
                  (mac 'intersection-membership)
                  (let* ((pmv  (inst*! pm v))
                         (subi (inst*! sub v))
                         (subv (dk-landed-1
                                (lambda () (mac-h 'union-membership subi))))
                         (eqv  (list 'IMPLIES (list '= v x) (list 'IN v t))))
                    (have! eqv (lambda () (di) (subst (list '= v x)) (ass)))
                    (dk-only! pmv subv eqv (list 'IN x t))
                    (prop)))))
            (subst (list '= t (list 'UNION (list 'PAIR x x) I)))
            ;; INTERSECTION(t, S) is a set and a subset of S ...
            (have! (list 'OR (list 'IN t 'SET) (list 'IN S 'SET))
                   (lambda () (oi-l) (ass)))
            (fact 'intersection-set-closure t S)
            (let ((incl (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ I) (list 'IN 'z_ S)))))
              (have! incl
                (lambda ()
                  (let* ((v (dk-di-var! (lambda (g) (cadr g))))
                         (both (dk-landed-1
                                (lambda ()
                                  (mac-h 'intersection-membership (list 'IN v I))))))
                    (dk-split! both)
                    (ass))))
              ;; ... so it is finite by the induction hypothesis ...
              (have! (list 'AND (list 'IN I 'SET) incl))
              (dk-apply! ih I))
            ;; ... and inserting x keeps it finite.
            (dk-split! (dk-fact! 'card-union-singleton-bound I x))
            (ass))
          ;; x not in t:  t subset S, and the hypothesis applies directly.
          (lambda ()
            (let ((incl (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ t) (list 'IN 'z_ S)))))
              (have! incl
                (lambda ()
                  (let* ((v    (dk-di-var! (lambda (g) (cadr g))))
                         (subi (inst*! sub v))
                         (subv (dk-landed-1
                                (lambda () (mac-h 'union-membership subi))))
                         (pmv  (inst*! pm v))
                         (eqv  (list 'IMPLIES (list '= v x) (list 'IN x t))))
                    (have! eqv (lambda () (di) (subst (list '= x v)) (ass)))
                    (dk-only! subv pmv eqv (list 'IN v t) (list 'NOT (list 'IN x t)))
                    (prop))))
              (have! (list 'AND (list 'IN t 'SET) incl))
              (dk-apply! ih t)
              (ass))))))))

;;; -----------------------------------------------------------------------
;;; THE THEOREM.

(quietly (lambda ()
  (sp (make-wff '(FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL S (IMPLIES (AND (IN S SET)
                              (FORALL z (IMPLIES (IN z S) (IN z X))))
                 (IN (CARD S) NN)))))))
  ;; the two induction premises, as closed formulas
  (have! (list 'IN 'EMPTY-SET csn-class) csn-base!)
  (have! csn-step-formula csn-step!)
  (have! (list 'AND (list 'IN 'EMPTY-SET csn-class) csn-step-formula))
  ;; finite-set-induction at C: every finite set is in C
  (let ((ind (dk-fact! 'finite-set-induction csn-class)))
    (let* ((landed (dk-peel!))
           (g      (dk-goal))                    ; (in (card S) nn)
           (S      (cadr (cadr g)))
           (X      (let ((f (dk-pick (lambda (f) (and ((dk-head? 'and) f)
                                                       (pair? (caddr f))
                                                       (eq? (car (caddr f)) 'in)
                                                       (pair? (cadr (caddr f)))
                                                       (eq? (car (cadr (caddr f))) 'card)))
                                      "the typing of X")))
                     (cadr (cadr f)))))
      ;; X in C, hence the class property at X, hence at S
      (let* ((inx  (dk-apply! ind X))
             (px   (dk-landed-find (lambda () (comp-me inx)) (dk-head? 'forall))))
        (dk-apply! px S)
        (ass))))))
(qed 'card-subset-nn)
(topic! 'card-subset-nn 'combinatorial)
