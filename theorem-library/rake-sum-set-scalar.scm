;;; rake-sum-set-scalar.scm -- the two scalar pull-outs for SUM-SET, PROVEN.
;;;
;;;   sum-set-left-scalar    a * (sum_{z in X} f z)  =  sum_{z in X} (a * f z)
;;;   sum-set-right-scalar   (sum_{z in X} f z) * b  =  sum_{z in X} (f z * b)
;;;
;;; Statements copied LITERALLY from theorem-library/sum-set-left-scalar.scm:16
;;; and theorem-library/sum-set-right-scalar.scm:15 (the supports this file
;;; retires).  Both are guarded on (IN X SET) and (IN (CARD X) NN), so the index
;;; set is FINITE and the four SUM-SET axioms decide it; see the note below.
;;;
;;; WHAT THE STATEMENTS ASSERT ABOUT THE INDEX SET.  SUM-SET is axiomatised by
;;; sum-set-empty / sum-set-singleton / sum-set-disjoint-union / sum-set-type
;;; (structure-library/sequences.scm) and NONE of those carries a finiteness
;;; guard -- SUM-SET(r, S, f) is an uninterpreted term for an infinite S, and a
;;; statement quantifying over ALL sets S would be underdetermined.  These two
;;; are not: the binder X carries (IN (CARD X) NN) beside (IN X SET), which is
;;; exactly the hypothesis finite-set-induction (cardinality.scm:108, primitive)
;;; consumes, and f is typed (IN f (FUN X (CARR s))) on that same X.  So the
;;; quantification is over finite sets only and every SUM-SET term in the
;;; statement is reachable from the axioms.  Nothing else about the statements
;;; is loose: s is guarded IS-RING and the scalar is in CARR(s).
;;;
;;; THE PROOF is finite-set-induction with the CLASS
;;;
;;;     C = { t_ | t_ subset X  =>  a * SUM-SET(s, t_, f) = SUM-SET(s, t_, LAM) }
;;;
;;; where LAM is the summand lambda of the STATEMENT, read off the goal --
;;; domain X, the whole index set, NOT t_.  That is the point of the shape: f
;;; and LAM stay typed on the FIXED superset X throughout the induction, and the
;;; class property is the statement RELATIVISED to subsets of X.  The induction
;;; then runs over the subsets of X and is applied at X itself (subset-refl).
;;;
;;; This is what the 2026-09-18 relaxation of `sum-set-disjoint-union' buys.  The
;;; earlier form demanded (IN f (FUN (UNION S1 S2) (CARR r))) -- the exact union
;;; as f's domain -- so the split of T u {x} produced an f typed on T u {x} that
;;; the induction hypothesis (about an f typed on T) could not accept, and
;;; SUM-SET has neither a congruence nor a restriction law to move f back.  The
;;; relaxed form takes any superset X, so BOTH sides of the split are read with
;;; the ONE typing (IN f (FUN X (CARR s))) the theorem already has.  See
;;; theorem-library/rake-algebra3.scm:405-420, where the obstacle was written up.
;;;
;;;   BASE  EMPTY-SET in C: sum-set-empty on both sides, then ring-mul-zero-right
;;;         (left form) / ring-mul-zero-left (right form).
;;;   STEP  S in SET, CARD S in NN, S in C, x in SET, x not in S  =>  S u {x} in C.
;;;         Sethood is pairing + union-set-closure.  For the property: S subset
;;;         S u {x} subset X (subset-trans), x in X (subset-mem-fwd), and
;;;         INTERSECTION(S, {x}) = EMPTY-SET from x not in S by
;;;         class-extensionality.  Then sum-set-disjoint-union splits BOTH sums
;;;         (f and LAM) over the same superset X, sum-set-singleton reads the
;;;         one-point sums, `lam-b' betas LAM at x (x in X is in context first),
;;;         ring-left-dist / ring-right-dist distributes, and the induction
;;;         hypothesis closes it.
;;;
;;; CITATIONS and where they load (0-based over the file names in load.scm):
;;;   theory.scm (11, primitive): subset-def, class-extensionality, pairing,
;;;     pairing-membership, union-membership, union-set-closure,
;;;     intersection-membership, empty-set-has-no-members, empty-set-is-set
;;;   structure-library/cardinality.scm (82): finite-set-induction
;;;   structure-library/sequences.scm (92): sum-set-empty, sum-set-singleton,
;;;     sum-set-disjoint-union, sum-set-type
;;;   structure-library/ring.scm (23): ring-left-dist, ring-right-dist
;;;   theorem-library/fun-apply-type-proof.scm (162): fun-apply-type-c
;;;   theorem-library/subset-lemmas.scm (192): subset-mem-fwd, subset-trans
;;;   theorem-library/discrete-space.scm (198): subset-refl
;;;   theorem-library/op-typing.scm (201): ring-carrier-closed-mul
;;;   theorem-library/ring-zero-one-power.scm (212): ring-mul-zero-left/right
;;;
;;; LOAD WINDOW [213, end).  lo = 213, forced by ring-zero-one-power (212); no
;;; proven theorem cites either support, so nothing forces hi.
;;;
;;; THE BILL is {sum-set-empty, sum-set-type, sum-set-disjoint-union,
;;; sum-set-singleton}, trust: none -- the four SUM-SET axioms of sequences.scm
;;; carry no `warrant!' and no provenance stamp.  They ARE the axiomatisation of
;;; SUM-SET (there is no definition beside them), so no proof of a SUM-SET fact
;;; can do better until they are stamped or warranted.  That is a decision for
;;; the user, not something this file can mend.
;;;
;;; Helper prefix: r6i-.

;;; --- file-local helpers (r6i-) -----------------------------------------

(define (r6i-sum? t) (and (pair? t) (eq? (car t) 'SUM-SET)))

;; Read the shape off the GOAL -- never reconstructed, so the same driver runs
;; both sides.  Returns (LEFT? MUL S SCALAR X F LAM).
(define (r6i-ctx g)
  (let* ((lhs   (cadr g))
         (rhs   (caddr g))
         (mul   (car lhs))
         (u1    (cadr lhs))
         (u2    (caddr lhs))
         (left? (not (r6i-sum? u1)))
         (scal  (if left? u1 u2))
         (sum   (if left? u2 u1)))
    (list left? mul (cadr mul) scal (caddr sum) (cadddr sum) (cadddr rhs))))

(define (r6i-left? c) (list-ref c 0))
(define (r6i-mul   c) (list-ref c 1))
(define (r6i-s     c) (list-ref c 2))
(define (r6i-scal  c) (list-ref c 3))
(define (r6i-big   c) (list-ref c 4))
(define (r6i-f     c) (list-ref c 5))
(define (r6i-lam   c) (list-ref c 6))

;; The statement's equation, with the index set replaced by T.
(define (r6i-eqn c t)
  (let ((s (r6i-s c)) (mul (r6i-mul c)) (scal (r6i-scal c)))
    (list '= (if (r6i-left? c)
                 (list mul scal (list 'SUM-SET s t (r6i-f c)))
                 (list mul (list 'SUM-SET s t (r6i-f c)) scal))
             (list 'SUM-SET s t (r6i-lam c)))))

;; The induction class.  Binder t_: not a class name, and no other binder in
;; this file differs from it by case.
(define (r6i-class c)
  (list 'COMP 't_
        (list 'IMPLIES (list 'SUBSET 't_ (r6i-big c)) (r6i-eqn c 't_))))

;; The step premise of finite-set-induction at that class, spelled with binders
;; q_ / y_ so that neither captures the eigenvariables s, a, x, f the class
;; mentions free; `fact' finds it in context up to alpha.
(define (r6i-step-formula c)
  (let ((cls (r6i-class c)))
    (list 'FORALL 'q_
      (list 'IMPLIES (list 'AND (list 'IN 'q_ 'SET)
                           (list 'AND (list 'IN (list 'CARD 'q_) 'NN)
                                      (list 'IN 'q_ cls)))
        (list 'FORALL 'y_
          (list 'IMPLIES (list 'AND (list 'IN 'y_ 'SET)
                               (list 'NOT (list 'IN 'y_ 'q_)))
            (list 'IN (list 'UNION 'q_ (list 'PAIR 'y_ 'y_)) cls)))))))

;;; --- small lanes -------------------------------------------------------

;; goal (IN x (PAIR x x)); (AND (IN x SET) (IN x SET)) must be in context.
(define (r6i-in-pair! x)
  (let ((pm (dk-fact! 'pairing-membership x x x)))
    (have! (list '= x x) (lambda () (rfl)))
    (dk-only! pm (list '= x x))
    (prop)))

;; goal (= (INTERSECTION S (PAIR x x)) EMPTY-SET), from (NOT (IN x S)).
(define (r6i-disjoint! s-set x)
  (let ((p (list 'PAIR x x)))
    (bc* 'class-extensionality)
    (let ((v (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (let* ((pm  (dk-fact! 'pairing-membership x x v))
             (nem (dk-fact! 'empty-set-has-no-members v)))
        (mac 'intersection-membership)
        (let ((imp (list 'IMPLIES (list '= v x)
                         (list 'NOT (list 'IN v s-set)))))
          (have! imp (lambda () (di) (subst (list '= v x)) (ass)))
          (dk-only! pm nem imp)
          (prop))))))

;; (IN (SUM-SET s S g) (CARR s)) from sum-set-type over the superset X.
(define (r6i-sum-type! s big sub g)
  (have! (list 'AND (list 'IS-RING s)
               (list 'AND (list 'IN big 'SET)
                     (list 'AND (list 'SUBSET sub big)
                           (list 'AND (list 'IN g (list 'FUN big (list 'CARR s)))
                                      (list 'IN (list 'CARD sub) 'NN))))))
  (fact 'sum-set-type-defined s big sub g))

;; (= (SUM-SET s (UNION S P) g) ((ADD s) (SUM-SET s S g) (SUM-SET s P g)))
(define (r6i-split! s big sub p g)
  (have! (list 'AND (list 'IN big 'SET)
               (list 'AND (list 'IN sub 'SET)
                     (list 'AND (list 'IN p 'SET)
                           (list 'AND (list '= (list 'INTERSECTION sub p) 'EMPTY-SET)
                                 (list 'AND (list 'SUBSET (list 'UNION sub p) big)
                                       (list 'AND (list 'IN g (list 'FUN big (list 'CARR s)))
                                             (list 'AND (list 'IN (list 'CARD sub) 'NN)
                                                        (list 'IN (list 'CARD p) 'NN)))))))))
  (fact 'sum-set-disjoint-union-defined s big sub p g))

;;; --- the summand lambda is a function on X -----------------------------

(define (r6i-lam-type! c)
  (let ((s (r6i-s c)) (big (r6i-big c)) (f (r6i-f c)))
    (dk-lam-t!)
    (dk-peel!)
    (let* ((g   (dk-goal))
           (t   (cadr g))
           (a1  (cadr t))
           (a2  (caddr t))
           (app (if (and (pair? a1) (eq? (car a1) f)) a1 a2))
           (z   (cadr app)))
      (fact 'fun-apply-type-c f big (list 'CARR s) z)
      (fact 'ring-carrier-closed-mul s a1 a2)
      (ass))))

;;; --- BASE:  EMPTY-SET in C ---------------------------------------------

(define (r6i-base! c)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (let ((g (dk-goal)))
       (if (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))
           (begin (fact 'empty-set-is-set) (ass))
           (begin
             (dk-peel!)
             (mac 'sum-set-empty)
             (if (r6i-left? c)
                 (fact 'ring-mul-zero-right (r6i-s c) (r6i-scal c))
                 (fact 'ring-mul-zero-left  (r6i-s c) (r6i-scal c)))
             (ass)))))
   (dk-opened (lambda () (comp-mi)))))

;;; --- STEP --------------------------------------------------------------

(define (r6i-sethood! sub x p)
  (have! (list 'AND (list 'IN sub 'SET) (list 'IN p 'SET)))
  (fact 'union-set-closure sub p)
  (ass))

(define (r6i-property! c sub x p u ih)
  (let* ((s     (r6i-s c))
         (big   (r6i-big c))
         (f     (r6i-f c))
         (lam   (r6i-lam c))
         (scal  (r6i-scal c))
         (mul   (r6i-mul c))
         (add   (list 'ADD s))
         (sumuf (list 'SUM-SET s u f))
         (sumul (list 'SUM-SET s u lam))
         (sumsf (list 'SUM-SET s sub f))
         (sumsl (list 'SUM-SET s sub lam))
         (sumpf (list 'SUM-SET s p f))
         (sumpl (list 'SUM-SET s p lam))
         (fx    (list f x)))
    (dk-peel!)                                        ; lands (SUBSET u X)
    ;; x lives in u, hence in X; S is included in u, hence in X
    (have! (list 'IN x u)
           (lambda () (mac 'union-membership) (oi-r) (r6i-in-pair! x)))
    (fact 'subset-mem-fwd u big x)
    (have! (list 'SUBSET sub u)
           (lambda () (mac 'subset-def)
                      (dk-di-var!)
                      (mac 'union-membership) (oi-l) (ass)))
    (fact 'subset-trans sub u big)
    (dk-apply! ih)                                    ; the induction hypothesis
    ;; the two parts of u are disjoint
    (have! (list '= (list 'INTERSECTION sub p) 'EMPTY-SET)
           (lambda () (r6i-disjoint! sub x)))
    ;; typings
    (fact 'fun-apply-type-c f big (list 'CARR s) x)
    (r6i-sum-type! s big sub f)
    (r6i-sum-type! s big sub lam)
    (if (r6i-left? c)
        (fact 'ring-carrier-closed-mul s scal fx)
        (fact 'ring-carrier-closed-mul s fx scal))
    ;; split both sums and read the one-point sums
    (r6i-split! s big sub p f)
    (r6i-split! s big sub p lam)
    (have! (list 'IN (list lam x) (list 'CARR s))
           (lambda () (lam-b) (ass)))
    (fact 'sum-set-singleton-defined s x f)
    (fact 'sum-set-singleton-defined s x lam)
    ;; rewrite the goal down to the induction hypothesis
    (subst (list '= sumuf (list add sumsf sumpf)))
    (subst (list '= sumul (list add sumsl sumpl)))
    (subst (list '= sumpf fx))
    (subst (list '= sumpl (list lam x)))
    (lam-b)
    (if (r6i-left? c)
        (begin
          (fact 'ring-left-dist s scal sumsf fx)
          (subst (list '= (list mul scal (list add sumsf fx))
                          (list add (list mul scal sumsf) (list mul scal fx)))))
        (begin
          (fact 'ring-right-dist s sumsf fx scal)
          (subst (list '= (list mul (list add sumsf fx) scal)
                          (list add (list mul sumsf scal) (list mul fx scal))))))
    (subst (r6i-eqn c sub))
    (rfl)))

(define (r6i-step! c)
  (let* ((landed (dk-peel!))
         (g      (dk-goal))                           ; (IN (UNION S (PAIR x x)) C)
         (u      (cadr g))
         (sub    (cadr u))
         (p      (caddr u))
         (x      (cadr p)))
    (dk-split-all! landed)
    (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
    (fact 'pairing x x)
    (fact 'card-singleton x)
    (fact 'nn-zero-in)
    (fact 'nn-succ-closed 0)
    (have! (list 'IN (list 'CARD p) 'NN)
           (lambda () (subst (list '= (list 'CARD p) '(succ 0))) (ass)))
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN sub (r6i-class c))))
                              (dk-head? 'IMPLIES))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (let ((gg (dk-goal)))
           (if (and (pair? gg) (eq? (car gg) 'IN) (eq? (caddr gg) 'SET))
               (r6i-sethood! sub x p)
               (r6i-property! c sub x p u ih))))
       (dk-opened (lambda () (comp-mi)))))))

;;; --- the theorem -------------------------------------------------------

(define (r6i-prove! name stmt)
  (sp (make-wff stmt))
  (dk-split-all! (dk-peel!))
  (let* ((c   (r6i-ctx (dk-goal)))
         (s   (r6i-s c))
         (big (r6i-big c))
         (lam (r6i-lam c))
         (cls (r6i-class c))
         (stp (r6i-step-formula c)))
    (have! (list 'IN lam (list 'FUN big (list 'CARR s)))
           (lambda () (r6i-lam-type! c)))
    (have! (list 'IN 'EMPTY-SET cls) (lambda () (r6i-base! c)))
    (have! stp (lambda () (r6i-step! c)))
    (have! (list 'AND (list 'IN 'EMPTY-SET cls) stp))
    (let ((ind (dk-fact! 'finite-set-induction cls)))
      (have! (list 'AND (list 'IN big 'SET) (list 'IN (list 'CARD big) 'NN)))
      (let* ((inx (dk-apply! ind big))
             (px  (dk-landed-find (lambda () (comp-me inx)) (dk-head? 'IMPLIES))))
        (fact 'subset-refl big)
        (dk-apply! px)
        (ass))))
  (qed name))

(r6i-prove! 'sum-set-left-scalar
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL f (IMPLIES (IN f (FUN X (CARR s)))
       (= ((MUL s) a (SUM-SET s X f))
          (SUM-SET s X (VNB-LAMBDA z X ((MUL s) a (f z))))))))))))))
(topic! 'sum-set-left-scalar 'algebra)

(r6i-prove! 'sum-set-right-scalar
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL b (IMPLIES (IN b (CARR s))
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL f (IMPLIES (IN f (FUN X (CARR s)))
       (= ((MUL s) (SUM-SET s X f) b)
          (SUM-SET s X (VNB-LAMBDA z X ((MUL s) (f z) b)))))))))))))
(topic! 'sum-set-right-scalar 'algebra)
