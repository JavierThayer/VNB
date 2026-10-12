;;; rake-asm-2.scm -- RAKE-ASM agent RA-2 (2026-10-12): elementary laws that stood as
;;; ASSUMPTIONS (add-axiom! / support), each proven here under its EXACT name and
;;; statement (copied character for character from its definition site).
;;;
;;;   mpow-mult              structure-library/monoid-power.scm
;;;   prod-ord-type          structure-library/sequences.scm
;;;   prod-ord-singleton     structure-library/sequences.scm
;;;   sum-type               structure-library/sequences.scm
;;;   sum-singleton          structure-library/sequences.scm
;;;   sum-ag-singleton       structure-library/sequences.scm
;;;   sum-ag-as-reduce       structure-library/sequences.scm
;;;   sum-left-scalar        structure-library/sequences.scm
;;;   ring-prod-n-is-ring    structure-library/sequences.scm
;;;   zz-act-distrib         structure-library/zz-action.scm
;;;   zz-act-assoc           structure-library/zz-action.scm
;;;   choose-times-factorial structure-library/injection.scm
;;;   mul-defined-factors    structure-library/order-lemmas.scm  (group C; trivially
;;;                          true: its conclusion is about VARIABLES, which always
;;;                          denote, so `rfl' closes it without the hypothesis)
;;;
;;; Auxiliary theorems (new names): prod-ord-type-ind, sum-type-ind,
;;; sum-ag-as-reduce-ind, mpow-mult-ind, sum-left-scalar-ind,
;;; ring-prod-n-is-ring-ind, zz-act-distrib-nn, zz-act-assoc-nn,
;;; falling-zero-succ, falling-succ-succ, choose-times-factorial-all.
;;;
;;; Every NN induction runs on a COMPANION statement with the induction variable
;;; outermost (`ni' tests the literal shape), then one `fact'.
;;; Helper prefix `ra2-'.  All helpers are file-local.
;;;
;;; LOAD WINDOW, by file name (positions are load.scm LINE numbers on 2026-10-12):
;;;   lo: after theorem-library/rake-finsum-typing-nn (line 2272: falling-in-nn,
;;;       cited by choose-times-factorial only).  The next-latest citations:
;;;       rake-choose-succ (1366: choose-succ), rake-combinatorics2 (1364:
;;;       choose-in-nn), rake-combinatorics (1362: choose-n-0, choose-0-succ),
;;;       rake-finsum-core (1309: comm-monoid-opr-interchange, comm-monoid-left-id),
;;;       rake-finsum-laws (1303: abelian-group-opr-interchange), rake-finsum-typing
;;;       (1197), rake-zz-act (1190: zz-act-add/-zero/-one/-type/-neg-sign,
;;;       abelian-group-inv-opr), rake-monoid-laws (1187), rake-algebra2 (1185:
;;;       mpow-type, monoid-carrier-closed-opr, monoid-identity-in), nn-pos-is-succ
;;;       (1169), ring-zero-one-power (1115), cancellation (1114), finsum-type-proof
;;;       (1055: sum-ag-type), op-typing (1049), subtype-laws (1038).
;;;       Without choose-times-factorial the file could sit at lo = 1367.
;;;   hi: theorem-library/pss-topics (line 3661: topic! 'choose-times-factorial).
;;;       No proof in the tree cites any of the twelve names (grep of
;;;       structure-library/, theorem-library/, calculus/; test-suite.scm only
;;;       looks ring-prod-n-is-ring up by name).
;;;   ring-prod-n-is-ring cites zero-ring-is-ring and ring-prod-is-ring, RA-1's
;;;   targets (structure-library/ring.scm): modulo 0 once RA-1's file, loading
;;;   before this one, proves them.

(define (ra2-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; ra2: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (f)
                                (display ";;      | ")
                                (display (expression->string f)) (newline))
                              (list-head (dk-asms-of l) (min 12 (length (dk-asms-of l))))))
                  (proof-leaves))
        (error "ra2: proof not complete" name))))

;;; the three parts of use-induction's answer
(define (ra2-ind!)
  (let ((br (use-induction)))
    (list (cdr (assq 'base br)) (cdr (assq 'step br))
          (cdr (assq 'ih br)) (cdr (assq 'var br)))))

;;; dk-have! of a conjunction closed by prop (for a conjunctive antecedent)
(define (ra2-and! . fs)
  (let ((conj (let build ((l fs))
                (if (null? (cdr l)) (car l) (list 'AND (car l) (build (cdr l)))))))
    (dk-have! conj (lambda () (prop)))
    conj))

;;; =====================================================================
;;; prod-ord-singleton
;;; =====================================================================
(sp (make-wff
 '(FORALL m
      (IMPLIES (IS-MONOID m)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR m)))
                          (= (PROD-ORD m f 1) (f 0))))))))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'NN '(CARR m) 0)
(dk-have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(fact 'prod-ord-succ 'm 'f 0)
(subst '(== (PROD-ORD m f (succ 0)) ((OPR m) (PROD-ORD m f 0) (f 0))))
(fact 'prod-ord-zero 'm 'f)
(subst '(== (PROD-ORD m f 0) (IDEN m)))
(fact 'monoid-left-id 'm '(f 0))
(ass)
(ra2-check! 'prod-ord-singleton)
(qed 'prod-ord-singleton)

;;; =====================================================================
;;; sum-singleton
;;; =====================================================================
(sp (make-wff
 '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR r)))
                          (= (SUM r f 1) (f 0))))))))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'NN '(CARR r) 0)
(dk-have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(fact 'sum-succ 'r 'f 0)
(subst '(== (SUM r f (succ 0)) ((ADD r) (SUM r f 0) (f 0))))
(fact 'sum-zero 'r 'f)
(subst '(== (SUM r f 0) (ZERO r)))
(fact 'ring-add-left-id 'r '(f 0))
(ass)
(ra2-check! 'sum-singleton)
(qed 'sum-singleton)

;;; =====================================================================
;;; sum-ag-singleton
;;; =====================================================================
(sp (make-wff
 '(FORALL ag
      (IMPLIES (IS-ABELIAN-GROUP ag)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR ag)))
                          (= (SUM-AG ag f 1) (f 0))))))))
(dk-peel!)
(fact 'abelian-group-is-group 'ag)
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'NN '(CARR ag) 0)
(dk-have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(fact 'sum-ag-succ 'ag 'f 0)
(subst '(== (SUM-AG ag f (succ 0)) ((OPR ag) (SUM-AG ag f 0) (f 0))))
(fact 'sum-ag-zero 'ag 'f)
(subst '(== (SUM-AG ag f 0) (IDEN ag)))
(fact 'group-left-id 'ag '(f 0))
(ass)
(ra2-check! 'sum-ag-singleton)
(qed 'sum-ag-singleton)

;;; =====================================================================
;;; prod-ord-type, through prod-ord-type-ind (n outermost)
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL m (IMPLIES (IS-MONOID m)
      (FORALL f (IMPLIES (IN f (FUN NN (CARR m)))
        (IN (PROD-ORD m f n) (CARR m))))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  (dk-focus! base)
  (dk-peel!)
  (fact 'prod-ord-zero 'm 'f)
  (subst '(== (PROD-ORD m f 0) (IDEN m)))
  (fact 'monoid-identity-in 'm)
  (ass)
  (dk-focus! step)
  (dk-peel!)
  (let ((p (list 'PROD-ORD 'm 'f v)) (fv (list 'f v)))
    (fact 'prod-ord-succ 'm 'f v)
    (subst (list '== (list 'PROD-ORD 'm 'f (list 'succ v)) (list '(OPR m) p fv)))
    (dk-apply! ih 'm 'f)
    (fact 'fun-apply-type-c 'f 'NN '(CARR m) v)
    (ra2-and! '(IS-MONOID m) (list 'IN p '(CARR m)) (list 'IN fv '(CARR m)))
    (fact 'monoid-carrier-closed-opr 'm p fv)
    (ass)))
(ra2-check! 'prod-ord-type-ind)
(qed 'prod-ord-type-ind)

(sp (make-wff
 '(FORALL m
      (IMPLIES (IS-MONOID m)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR m)))
                          (FORALL n
                            (IMPLIES (IN n NN)
                                     (IN (PROD-ORD m f n) (CARR m))))))))))
(dk-peel!)
(fact 'prod-ord-type-ind 'n 'm 'f)
(ass)
(ra2-check! 'prod-ord-type)
(qed 'prod-ord-type)

;;; =====================================================================
;;; sum-type, through sum-type-ind (n outermost)
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL r (IMPLIES (IS-RING r)
      (FORALL f (IMPLIES (IN f (FUN NN (CARR r)))
        (IN (SUM r f n) (CARR r))))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  (dk-focus! base)
  (dk-peel!)
  (fact 'sum-zero 'r 'f)
  (subst '(== (SUM r f 0) (ZERO r)))
  (fact 'ring-zero-in 'r)
  (ass)
  (dk-focus! step)
  (dk-peel!)
  (let ((p (list 'SUM 'r 'f v)) (fv (list 'f v)))
    (fact 'sum-succ 'r 'f v)
    (subst (list '== (list 'SUM 'r 'f (list 'succ v)) (list '(ADD r) p fv)))
    (dk-apply! ih 'r 'f)
    (fact 'fun-apply-type-c 'f 'NN '(CARR r) v)
    (fact 'ring-add-closed 'r p fv)
    (ass)))
(ra2-check! 'sum-type-ind)
(qed 'sum-type-ind)

(sp (make-wff
 '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR r)))
                          (FORALL n
                            (IMPLIES (IN n NN)
                                     (IN (SUM r f n) (CARR r))))))))))
(dk-peel!)
(fact 'sum-type-ind 'n 'r 'f)
(ass)
(ra2-check! 'sum-type)
(qed 'sum-type)

;;; =====================================================================
;;; sum-ag-as-reduce, through sum-ag-as-reduce-ind (k outermost, at succ k)
;;; =====================================================================
(sp (make-wff
 '(FORALL k (IMPLIES (IN k NN)
    (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
      (FORALL f (IMPLIES (IN f (FUN NN (CARR ag)))
        (= (SUM-AG ag f (succ k)) (REDUCE (OPR ag) f (succ k)))))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  ;; ---- base: SUM-AG(ag,f,1) = e * f(0) = f(0) = REDUCE(op,f,1)
  (dk-focus! base)
  (dk-peel!)
  (fact 'abelian-group-is-group 'ag)
  (fact 'nn-zero-in)
  (fact 'fun-apply-type-c 'f 'NN '(CARR ag) 0)
  (fact 'sum-ag-succ 'ag 'f 0)
  (subst '(== (SUM-AG ag f (succ 0)) ((OPR ag) (SUM-AG ag f 0) (f 0))))
  (fact 'sum-ag-zero 'ag 'f)
  (subst '(== (SUM-AG ag f 0) (IDEN ag)))
  (fact 'group-left-id 'ag '(f 0))
  (subst '(= ((OPR ag) (IDEN ag) (f 0)) (f 0)))
  (dk-have! '(= (succ 0) 1) (lambda () (arith)))
  (subst '(= (succ 0) 1))
  (fact 'reduce-one '(OPR ag) 'f)
  (subst '(== (REDUCE (OPR ag) f 1) (f 0)))
  (rfl)
  ;; ---- step
  (dk-focus! step)
  (dk-peel!)
  (let* ((sv (list 'succ v)) (ssv (list 'succ sv))
         (s1 (list 'SUM-AG 'ag 'f sv)) (r1 (list 'REDUCE '(OPR ag) 'f sv))
         (fsv (list 'f sv)))
    (fact 'abelian-group-is-group 'ag)
    (fact 'nn-succ-closed v)
    (fact 'fun-apply-type-c 'f 'NN '(CARR ag) sv)
    (fact 'sum-ag-type 'ag 'f sv)
    (fact 'sum-ag-succ 'ag 'f sv)
    (subst (list '== (list 'SUM-AG 'ag 'f ssv) (list '(OPR ag) s1 fsv)))
    (fact 'nn-one-le-succ v)
    (ra2-and! (list 'IN sv 'NN) (list '<= 1 sv))
    (fact 'reduce-succ '(OPR ag) 'f sv)
    (subst (list '== (list 'REDUCE '(OPR ag) 'f ssv) (list '(OPR ag) r1 fsv)))
    (dk-apply! ih 'ag 'f)
    (subst (list '= r1 s1))
    (fact 'group-carrier-closed-opr 'ag s1 fsv)
    (rfl)))
(ra2-check! 'sum-ag-as-reduce-ind)
(qed 'sum-ag-as-reduce-ind)

(sp (make-wff
 '(FORALL ag
      (IMPLIES (IS-ABELIAN-GROUP ag)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR ag)))
                          (FORALL n
                            (IMPLIES (AND (IN n NN) (<= 1 n))
                                     (= (SUM-AG ag f n)
                                        (REDUCE (OPR ag) f n))))))))))
(dk-split-all! (dk-peel!))
(let* ((ex (dk-fact! 'nn-pos-is-succ 'n))
       (q  (dk-skolem! ex)))
  (dk-split-all!)
  (subst (list '= 'n (list 'succ q)))
  (fact 'sum-ag-as-reduce-ind q 'ag 'f)
  (ass))
(ra2-check! 'sum-ag-as-reduce)
(qed 'sum-ag-as-reduce)

;;; =====================================================================
;;; mpow-mult, through mpow-mult-ind (n outermost).
;;;   (xy)^(n+1) = (xy)(xy)^n = (xy)(x^n y^n) = (x x^n)(y y^n)   [interchange]
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL m (IMPLIES (IS-COMM-MONOID m)
      (FORALL x (IMPLIES (IN x (CARR m))
        (FORALL y (IMPLIES (IN y (CARR m))
          (= (MPOW m ((OPR m) x y) n)
             ((OPR m) (MPOW m x n) (MPOW m y n)))))))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  (dk-focus! base)
  (dk-peel!)
  (fact 'comm-monoid-is-monoid 'm)
  (fact 'comm-monoid-identity-in-carr 'm)
  (fact 'comm-monoid-carrier-closed-opr 'm 'x 'y)
  (fact 'mpow-zero 'm '((OPR m) x y))
  (subst '(== (MPOW m ((OPR m) x y) 0) (IDEN m)))
  (fact 'mpow-zero 'm 'x)
  (subst '(== (MPOW m x 0) (IDEN m)))
  (fact 'mpow-zero 'm 'y)
  (subst '(== (MPOW m y 0) (IDEN m)))
  (fact 'comm-monoid-left-id 'm '(IDEN m))
  (subst '(= ((OPR m) (IDEN m) (IDEN m)) (IDEN m)))
  (rfl)
  (dk-focus! step)
  (dk-peel!)
  (let* ((xy '((OPR m) x y))
         (pw (lambda (b e) (list 'MPOW 'm b e)))
         (op (lambda (u w) (list '(OPR m) u w)))
         (sv (list 'succ v)))
    (fact 'comm-monoid-is-monoid 'm)
    (fact 'comm-monoid-carrier-closed-opr 'm 'x 'y)
    (fact 'mpow-succ 'm xy v)
    (subst (list '== (pw xy sv) (op xy (pw xy v))))
    (fact 'mpow-succ 'm 'x v)
    (subst (list '== (pw 'x sv) (op 'x (pw 'x v))))
    (fact 'mpow-succ 'm 'y v)
    (subst (list '== (pw 'y sv) (op 'y (pw 'y v))))
    (dk-apply! ih 'm 'x 'y)
    (subst (list '= (pw xy v) (op (pw 'x v) (pw 'y v))))
    (fact 'mpow-type 'm 'x v)
    (fact 'mpow-type 'm 'y v)
    (fact 'comm-monoid-opr-interchange 'm 'x 'y (pw 'x v) (pw 'y v))
    (ass)))
(ra2-check! 'mpow-mult-ind)
(qed 'mpow-mult-ind)

(sp (make-wff
 '(FORALL m
     (IMPLIES (IS-COMM-MONOID m)
       (FORALL x (IMPLIES (IN x (CARR m))
         (FORALL y (IMPLIES (IN y (CARR m))
           (FORALL n (IMPLIES (IN n NN)
             (= (MPOW m ((OPR m) x y) n)
                ((OPR m) (MPOW m x n) (MPOW m y n)))))))))))))
(dk-peel!)
(fact 'mpow-mult-ind 'n 'm 'x 'y)
(ass)
(ra2-check! 'mpow-mult)
(qed 'mpow-mult)

;;; =====================================================================
;;; sum-left-scalar, through sum-left-scalar-ind (n outermost).
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL r (IMPLIES (IS-RING r)
      (FORALL a (IMPLIES (IN a (CARR r))
        (FORALL f (IMPLIES (IN f (FUN NN (CARR r)))
          (= (SUM r (VNB-LAMBDA i NN ((MUL r) a (f i))) n)
             ((MUL r) a (SUM r f n)))))))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br))
       (lam '(VNB-LAMBDA i NN ((MUL r) a (f i)))))
  (dk-focus! base)
  (dk-peel!)
  (fact 'sum-zero 'r lam)
  (subst (list '== (list 'SUM 'r lam 0) '(ZERO r)))
  (fact 'sum-zero 'r 'f)
  (subst '(== (SUM r f 0) (ZERO r)))
  (fact 'ring-mul-zero-right 'r 'a)
  (subst '(= ((MUL r) a (ZERO r)) (ZERO r)))
  (rfl)
  (dk-focus! step)
  (dk-peel!)
  (let* ((sv (list 'succ v))
         (sl (list 'SUM 'r lam v)) (sf (list 'SUM 'r 'f v)) (fv (list 'f v))
         (mul (lambda (u w) (list '(MUL r) u w)))
         (add (lambda (u w) (list '(ADD r) u w))))
    (fact 'fun-apply-type-c 'f 'NN '(CARR r) v)
    (fact 'sum-type 'r 'f v)
    (fact 'sum-succ 'r lam v)
    (subst (list '== (list 'SUM 'r lam sv) (add sl (list lam v))))
    (dk-lam-b!)
    (fact 'sum-succ 'r 'f v)
    (subst (list '== (list 'SUM 'r 'f sv) (add sf fv)))
    (dk-apply! ih 'r 'a 'f)
    (subst (list '= sl (mul 'a sf)))
    (fact 'ring-left-dist 'r 'a sf fv)
    (subst (list '= (mul 'a (add sf fv)) (add (mul 'a sf) (mul 'a fv))))
    (fact 'ring-carrier-closed-mul 'r 'a sf)
    (fact 'ring-carrier-closed-mul 'r 'a fv)
    (fact 'ring-add-closed 'r (mul 'a sf) (mul 'a fv))
    (rfl)))
(ra2-check! 'sum-left-scalar-ind)
(qed 'sum-left-scalar-ind)

(sp (make-wff
 '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL a
                 (IMPLIES (IN a (CARR r))
                          (FORALL f
                            (IMPLIES (IN f (FUN NN (CARR r)))
                                     (FORALL n
                                       (IMPLIES (IN n NN)
                                         (= (SUM r (VNB-LAMBDA i NN ((MUL r) a (f i))) n)
                                            ((MUL r) a (SUM r f n)))))))))))))
(dk-peel!)
(fact 'sum-left-scalar-ind 'n 'r 'a 'f)
(ass)
(ra2-check! 'sum-left-scalar)
(qed 'sum-left-scalar)

;;; ring-prod-n-is-ring (and ring-prod-n-is-ring-ind) MOVED 2026-10-12 to theorem-library/rake-asm-1.scm,
;;; which loads after zero-ring-is-ring and ring-prod-is-ring are proven there.
;;; =====================================================================
;;; ZZ-ACT laws.  Both go through the laws proven in rake-zz-act.scm
;;; (zz-act-add, -zero, -one, -type, -neg-sign); no MPOW is opened.
;;; =====================================================================

;;; every integer is a natural or the negative of one; POS / NEG run on the two
;;; branches and are handed the eigenvariable dk-skolem! minted.
(define (ra2-zz-cases! kv pos neg)
  (let* ((ex (dk-fact! 'zz-generated-by-nn kv))
         (n  (dk-skolem! ex)))
    (fact 'nn-in-rr n)
    (fact 'nn-subset-zz n)
    (use-cases (list (list '= kv n) (list '= kv (list '- n)))
      (lambda () (pos n))
      (lambda () (neg n)))
    n))

(define (ra2-op u w) (list '(OPR g) u w))
(define (ra2-inv u) (list '(INV g) u))
(define (ra2-za k u) (list 'ZZ-ACT 'g k u))

;;; zz-act-distrib-nn: k.(a b) = (k.a)(k.b) for k in NN, by induction on k.
;;;   (k+1).(ab) = k.(ab) (ab) = ((k.a)(k.b))(ab) = ((k.a) a)((k.b) b)   [interchange]
(sp (make-wff
 '(FORALL k (IMPLIES (IN k NN)
    (FORALL g (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL a (IMPLIES (IN a (CARR g))
        (FORALL b (IMPLIES (IN b (CARR g))
          (= (ZZ-ACT g k ((OPR g) a b))
             ((OPR g) (ZZ-ACT g k a) (ZZ-ACT g k b)))))))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br))
       (ab (ra2-op 'a 'b)))
  (dk-focus! base)
  (dk-peel!)
  (fact 'abelian-group-is-group 'g)
  (fact 'group-carrier-closed-opr 'g 'a 'b)
  (fact 'group-identity-in 'g)
  (fact 'zz-act-zero 'g ab)
  (subst (list '= (ra2-za 0 ab) '(IDEN g)))
  (fact 'zz-act-zero 'g 'a)
  (subst (list '= (ra2-za 0 'a) '(IDEN g)))
  (fact 'zz-act-zero 'g 'b)
  (subst (list '= (ra2-za 0 'b) '(IDEN g)))
  (fact 'group-left-id 'g '(IDEN g))
  (subst '(= ((OPR g) (IDEN g) (IDEN g)) (IDEN g)))
  (rfl)
  (dk-focus! step)
  (dk-peel!)
  (let ((v1 (list '+ v 1)))
    (fact 'abelian-group-is-group 'g)
    (fact 'group-carrier-closed-opr 'g 'a 'b)
    (fact 'nn-subset-zz v)
    (fact 'zz-one-in)
    (fact 'nn-succ-plus-one v)
    (subst (list '= (list 'succ v) v1))
    (fact 'zz-act-add 'g v 1 ab)
    (subst (list '= (ra2-za v1 ab) (ra2-op (ra2-za v ab) (ra2-za 1 ab))))
    (fact 'zz-act-add 'g v 1 'a)
    (subst (list '= (ra2-za v1 'a) (ra2-op (ra2-za v 'a) (ra2-za 1 'a))))
    (fact 'zz-act-add 'g v 1 'b)
    (subst (list '= (ra2-za v1 'b) (ra2-op (ra2-za v 'b) (ra2-za 1 'b))))
    (fact 'zz-act-one 'g ab)
    (subst (list '= (ra2-za 1 ab) ab))
    (fact 'zz-act-one 'g 'a)
    (subst (list '= (ra2-za 1 'a) 'a))
    (fact 'zz-act-one 'g 'b)
    (subst (list '= (ra2-za 1 'b) 'b))
    (dk-apply! ih 'g 'a 'b)
    (subst (list '= (ra2-za v ab) (ra2-op (ra2-za v 'a) (ra2-za v 'b))))
    (fact 'zz-act-type 'g v 'a)
    (fact 'zz-act-type 'g v 'b)
    (fact 'abelian-group-opr-interchange 'g (ra2-za v 'a) (ra2-za v 'b) 'a 'b)
    (ass)))
(ra2-check! 'zz-act-distrib-nn)
(qed 'zz-act-distrib-nn)

(sp (make-wff
 '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL k (IMPLIES (IN k ZZ)
         (FORALL a (IMPLIES (IN a (CARR g))
           (FORALL b (IMPLIES (IN b (CARR g))
             (= (ZZ-ACT g k ((OPR g) a b))
                ((OPR g) (ZZ-ACT g k a) (ZZ-ACT g k b)))))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 'g)
(fact 'group-carrier-closed-opr 'g 'a 'b)
(ra2-zz-cases! 'k
  (lambda (n)
    (subst (list '= 'k n))
    (fact 'zz-act-distrib-nn n 'g 'a 'b)
    (ass))
  (lambda (n)
    (let ((ab (ra2-op 'a 'b)) (mn (list '- n)))
      (subst (list '= 'k mn))
      (fact 'zz-act-neg-sign 'g n ab)
      (subst (list '= (ra2-za mn ab) (ra2-inv (ra2-za n ab))))
      (fact 'zz-act-distrib-nn n 'g 'a 'b)
      (subst (list '= (ra2-za n ab) (ra2-op (ra2-za n 'a) (ra2-za n 'b))))
      (fact 'zz-act-type 'g n 'a)
      (fact 'zz-act-type 'g n 'b)
      (fact 'abelian-group-inv-opr 'g (ra2-za n 'a) (ra2-za n 'b))
      (subst (list '= (ra2-inv (ra2-op (ra2-za n 'a) (ra2-za n 'b)))
                      (ra2-op (ra2-inv (ra2-za n 'a)) (ra2-inv (ra2-za n 'b)))))
      (fact 'zz-act-neg-sign 'g n 'a)
      (subst (list '= (ra2-za mn 'a) (ra2-inv (ra2-za n 'a))))
      (fact 'zz-act-neg-sign 'g n 'b)
      (subst (list '= (ra2-za mn 'b) (ra2-inv (ra2-za n 'b))))
      (fact 'group-inv-in 'g (ra2-za n 'a))
      (fact 'group-inv-in 'g (ra2-za n 'b))
      (fact 'group-carrier-closed-opr 'g (ra2-inv (ra2-za n 'a)) (ra2-inv (ra2-za n 'b)))
      (rfl))))
(ra2-check! 'zz-act-distrib)
(qed 'zz-act-distrib)

;;; zz-act-assoc-nn: (j k).a = j.(k.a) for j in NN, k in ZZ, by induction on j.
;;;   ((j+1) k).a = (j k + k).a = (j k).a (k.a) = j.(k.a) (k.a) = (j+1).(k.a)
(sp (make-wff
 '(FORALL j (IMPLIES (IN j NN)
    (FORALL g (IMPLIES (IS-ABELIAN-GROUP g)
      (FORALL k (IMPLIES (IN k ZZ)
        (FORALL a (IMPLIES (IN a (CARR g))
          (= (ZZ-ACT g (* j k) a)
             (ZZ-ACT g j (ZZ-ACT g k a)))))))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br))
       (ka '(ZZ-ACT g k a)))
  (dk-focus! base)
  (dk-peel!)
  (fact 'zz-in-rr 'k)
  (fact 'zz-act-type 'g 'k 'a)
  (dk-have! '(= (* 0 k) 0) (lambda () (crs)))
  (subst '(= (* 0 k) 0))
  (fact 'zz-act-zero 'g 'a)
  (subst '(= (ZZ-ACT g 0 a) (IDEN g)))
  (fact 'zz-act-zero 'g ka)
  (subst (list '= (ra2-za 0 ka) '(IDEN g)))
  (rfl)
  (dk-focus! step)
  (dk-peel!)
  (let* ((v1 (list '+ v 1)) (vk (list '* v 'k)))
    (fact 'abelian-group-is-group 'g)
    (fact 'nn-in-rr v)
    (fact 'zz-in-rr 'k)
    (fact 'nn-subset-zz v)
    (fact 'zz-one-in)
    (fact 'zz-act-type 'g 'k 'a)
    (fact 'nn-succ-plus-one v)
    (subst (list '= (list 'succ v) v1))
    (dk-have! (list '= (list '* v1 'k) (list '+ vk 'k)) (lambda () (crs)))
    (subst (list '= (list '* v1 'k) (list '+ vk 'k)))
    (ra2-and! (list 'IN v 'ZZ) '(IN k ZZ))
    (fact 'zz-mul-closed v 'k)
    (fact 'zz-act-add 'g vk 'k 'a)
    (subst (list '= (ra2-za (list '+ vk 'k) 'a) (ra2-op (ra2-za vk 'a) ka)))
    (fact 'zz-act-add 'g v 1 ka)
    (subst (list '= (ra2-za v1 ka) (ra2-op (ra2-za v ka) (ra2-za 1 ka))))
    (fact 'zz-act-one 'g ka)
    (subst (list '= (ra2-za 1 ka) ka))
    (dk-apply! ih 'g 'k 'a)
    (subst (list '= (ra2-za vk 'a) (ra2-za v ka)))
    (fact 'zz-act-type 'g v ka)
    (fact 'group-carrier-closed-opr 'g (ra2-za v ka) ka)
    (rfl)))
(ra2-check! 'zz-act-assoc-nn)
(qed 'zz-act-assoc-nn)

(sp (make-wff
 '(FORALL g
     (IMPLIES (IS-ABELIAN-GROUP g)
       (FORALL j (IMPLIES (IN j ZZ)
         (FORALL k (IMPLIES (IN k ZZ)
           (FORALL a (IMPLIES (IN a (CARR g))
             (= (ZZ-ACT g (* j k) a)
                (ZZ-ACT g j (ZZ-ACT g k a)))))))))))))
(dk-peel!)
(fact 'abelian-group-is-group 'g)
(fact 'zz-in-rr 'k)
(fact 'zz-act-type 'g 'k 'a)
(ra2-zz-cases! 'j
  (lambda (m)
    (subst (list '= 'j m))
    (fact 'zz-act-assoc-nn m 'g 'k 'a)
    (ass))
  (lambda (m)
    (let* ((mm (list '- m)) (mk (list '* m 'k)) (ka '(ZZ-ACT g k a)))
      (subst (list '= 'j mm))
      (dk-have! (list '= (list '* mm 'k) (list '- mk)) (lambda () (crs)))
      (subst (list '= (list '* mm 'k) (list '- mk)))
      (ra2-and! (list 'IN m 'ZZ) '(IN k ZZ))
      (fact 'zz-mul-closed m 'k)
      (fact 'zz-act-neg-sign 'g mk 'a)
      (subst (list '= (ra2-za (list '- mk) 'a) (ra2-inv (ra2-za mk 'a))))
      (fact 'zz-act-assoc-nn m 'g 'k 'a)
      (subst (list '= (ra2-za mk 'a) (ra2-za m ka)))
      (fact 'zz-act-neg-sign 'g m ka)
      (subst (list '= (ra2-za mm ka) (ra2-inv (ra2-za m ka))))
      (fact 'zz-act-type 'g m ka)
      (fact 'group-inv-in 'g (ra2-za m ka))
      (rfl))))
(ra2-check! 'zz-act-assoc)
(qed 'zz-act-assoc)

;;; =====================================================================
;;; choose-times-factorial.  Proven ALGEBRAICALLY, by Pascal's rule (choose-succ),
;;; not by the injection count the warrant sketches (that route is blocked by the
;;; missing SEP over triples).  The companion drops the guard m <= n: for m > n
;;; both sides are 0 (CHOOSE n m = 0 by choose-0-succ at the base; FALLING n m = 0
;;; because the factor n - n vanishes), which is what lets the step use the IH at
;;; succ q without a case split on q < n.
;;;   C(v+1,q+1)(q+1)! = C(v,q)(q+1)q! + C(v,q+1)(q+1)!
;;;                    = (q+1)F(v,q) + F(v,q+1) = (q+1)F(v,q) + (v-q)F(v,q)
;;;                    = (v+1)F(v,q) = F(v+1,q+1).
;;; =====================================================================

;;; m = 0 or m = succ q.  ZERO runs on the first branch, SUCC on the second with q.
(define (ra2-nn-cases! mv zero succ-body)
  (let ((orf (dk-fact! 'nn-zero-or-succ mv)))
    (use-cases orf
      (lambda () (zero))
      (lambda ()
        (let ((q (dk-skolem! (caddr orf))))
          (dk-split-all!)
          (succ-body q))))))

(define (ra2-one!)
  (dk-have! '(= (succ 0) 1) (lambda () (arith)))
  (subst '(= (succ 0) 1)))

;;; FALLING(0, succ k) = 0
(sp (make-wff
 '(FORALL k (IMPLIES (IN k NN) (= (FALLING 0 (succ k)) 0)))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  (dk-focus! base)
  (fact 'nn-zero-in)
  (fact 'falling-succ 0 0)
  (subst '(== (FALLING 0 (succ 0)) (* (- 0 0) (FALLING 0 0))))
  (fact 'falling-zero 0)
  (subst '(== (FALLING 0 0) (succ 0)))
  (ra2-one!)
  (crs)
  (dk-focus! step)
  (let ((sv (list 'succ v)))
    (fact 'nn-succ-closed v)
    (fact 'nn-in-rr sv)
    (fact 'falling-succ 0 sv)
    (subst (list '== (list 'FALLING 0 (list 'succ sv)) (list '* (list '- 0 sv) (list 'FALLING 0 sv))))
    (subst ih)
    (crs)))
(ra2-check! 'falling-zero-succ)
(qed 'falling-zero-succ)

;;; FALLING(succ n, succ k) = (succ n) FALLING(n, k)
(sp (make-wff
 '(FORALL k (IMPLIES (IN k NN)
    (FORALL n (IMPLIES (IN n NN)
      (= (FALLING (succ n) (succ k)) (* (succ n) (FALLING n k)))))))))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  (dk-focus! base)
  (dk-peel!)
  (fact 'nn-zero-in)
  (fact 'nn-in-rr 'n)
  (fact 'nn-succ-closed 'n)
  (fact 'falling-succ '(succ n) 0)
  (subst '(== (FALLING (succ n) (succ 0)) (* (- (succ n) 0) (FALLING (succ n) 0))))
  (fact 'falling-zero '(succ n))
  (subst '(== (FALLING (succ n) 0) (succ 0)))
  (fact 'falling-zero 'n)
  (subst '(== (FALLING n 0) (succ 0)))
  (fact 'nn-succ-plus-one 'n)
  (subst '(= (succ n) (+ n 1)))
  (ra2-one!)
  (crs)
  (dk-focus! step)
  (dk-peel!)
  (let* ((sv (list 'succ v)) (fnv (list 'FALLING 'n v)))
    (fact 'nn-in-rr 'n)
    (fact 'nn-in-rr v)
    (fact 'nn-succ-closed 'n)
    (fact 'nn-succ-closed v)
    (fact 'falling-in-nn 'n v)
    (fact 'nn-in-rr fnv)
    (fact 'falling-succ '(succ n) sv)
    (subst (list '== (list 'FALLING '(succ n) (list 'succ sv))
                 (list '* (list '- '(succ n) sv) (list 'FALLING '(succ n) sv))))
    (dk-apply! ih 'n)
    (subst (list '= (list 'FALLING '(succ n) sv) (list '* '(succ n) fnv)))
    (fact 'falling-succ 'n v)
    (subst (list '== (list 'FALLING 'n sv) (list '* (list '- 'n v) fnv)))
    (fact 'nn-succ-plus-one 'n)
    (subst '(= (succ n) (+ n 1)))
    (fact 'nn-succ-plus-one v)
    (subst (list '= sv (list '+ v 1)))
    (crs)))
(ra2-check! 'falling-succ-succ)
(qed 'falling-succ-succ)

;;; the unguarded companion
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL m (IMPLIES (IN m NN)
      (= (* (CHOOSE n m) (FACTORIAL m)) (FALLING n m))))))))
(define (ra2-ctf-zero! nv)
  ;; goal C(nv,0) 0! = F(nv,0) with m already replaced by 0
  (fact 'choose-n-0 nv)
  (subst (list '= (list 'CHOOSE nv 0) '(succ 0)))
  (fact 'factorial-zero)
  (subst '(= (FACTORIAL 0) (succ 0)))
  (fact 'falling-zero nv)
  (subst (list '== (list 'FALLING nv 0) '(succ 0)))
  (ra2-one!)
  (crs))
(let* ((br (ra2-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  ;; ---- base n = 0
  (dk-focus! base)
  (dk-peel!)
  (fact 'nn-zero-in)
  (ra2-nn-cases! 'm
    (lambda ()
      (subst '(= m 0))
      (ra2-ctf-zero! 0))
    (lambda (q)
      (let ((sq (list 'succ q)))
        (subst (list '= 'm sq))
        (fact 'nn-succ-closed q)
        (fact 'factorial-in-nn sq)
        (fact 'nn-in-rr (list 'FACTORIAL sq))
        (fact 'choose-0-succ q)
        (subst (list '= (list 'CHOOSE 0 sq) 0))
        (fact 'falling-zero-succ q)
        (subst (list '= (list 'FALLING 0 sq) 0))
        (crs))))
  ;; ---- step n -> succ v
  (dk-focus! step)
  (dk-peel!)
  (fact 'nn-succ-closed v)
  (ra2-nn-cases! 'm
    (lambda ()
      (subst '(= m 0))
      (ra2-ctf-zero! (list 'succ v)))
    (lambda (q)
      (let* ((sv (list 'succ v)) (sq (list 'succ q))
             (c1 (list 'CHOOSE v q)) (c2 (list 'CHOOSE v sq))
             (fs (list 'FACTORIAL sq)) (fq (list 'FACTORIAL q))
             (fvq (list 'FALLING v q)))
        (subst (list '= 'm sq))
        (fact 'nn-succ-closed q)
        (fact 'nn-in-rr v)
        (fact 'nn-in-rr q)
        (fact 'nn-in-rr sq)
        (fact 'choose-in-nn v q)
        (fact 'nn-in-rr c1)
        (fact 'choose-in-nn v sq)
        (fact 'nn-in-rr c2)
        (fact 'factorial-in-nn q)
        (fact 'nn-in-rr fq)
        (fact 'factorial-in-nn sq)
        (fact 'nn-in-rr fs)
        (fact 'falling-in-nn v q)
        (fact 'nn-in-rr fvq)
        (fact 'choose-succ v q)
        (subst (list '= (list 'CHOOSE sv sq) (list '+ c1 c2)))
        (fact 'falling-succ-succ q v)
        (subst (list '= (list 'FALLING sv sq) (list '* sv fvq)))
        (dk-have! (list '= (list '* (list '+ c1 c2) fs) (list '+ (list '* c1 fs) (list '* c2 fs)))
                  (lambda () (crs)))
        (subst (list '= (list '* (list '+ c1 c2) fs) (list '+ (list '* c1 fs) (list '* c2 fs))))
        (dk-apply! ih sq)
        (subst (list '= (list '* c2 fs) (list 'FALLING v sq)))
        (fact 'falling-succ v q)
        (subst (list '== (list 'FALLING v sq) (list '* (list '- v q) fvq)))
        (fact 'factorial-succ q)
        (subst (list '= fs (list '* sq fq)))
        (dk-have! (list '= (list '* c1 (list '* sq fq)) (list '* sq (list '* c1 fq)))
                  (lambda () (crs)))
        (subst (list '= (list '* c1 (list '* sq fq)) (list '* sq (list '* c1 fq))))
        (dk-apply! ih q)
        (subst (list '= (list '* c1 fq) fvq))
        (fact 'nn-succ-plus-one q)
        (subst (list '= sq (list '+ q 1)))
        (fact 'nn-succ-plus-one v)
        (subst (list '= sv (list '+ v 1)))
        (crs)))))
(ra2-check! 'choose-times-factorial-all)
(qed 'choose-times-factorial-all)

(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
     (FORALL m (IMPLIES (AND (IN m NN) (<= m n))
       (= (* (CHOOSE n m) (FACTORIAL m)) (FALLING n m))))))))
(dk-split-all! (dk-peel!))
(fact 'choose-times-factorial-all 'n 'm)
(ass)
(ra2-check! 'choose-times-factorial)
(qed 'choose-times-factorial)

;;; =====================================================================
;;; Four of the names had view companions built by the unrestricted
;;; (view-as-auto-specialize! 'RING-ADDITIVE-AG) in theorem-library/cancellation.scm,
;;; which ran while they were axioms.  Proving them here moves them past that
;;; specializer, so the companions are rebuilt, RESTRICTED to the four names (the
;;; rake-zz-act precedent).  No file in the tree cites any of the four companions.
;;; =====================================================================
(view-as-auto-specialize! 'RING-ADDITIVE-AG 'sum-ag-singleton)
(view-as-auto-specialize! 'RING-ADDITIVE-AG 'sum-ag-as-reduce)
(view-as-auto-specialize! 'RING-ADDITIVE-AG 'zz-act-distrib)
(view-as-auto-specialize! 'RING-ADDITIVE-AG 'zz-act-assoc)

(display ";; ra2 qed failures: ") (display *vnb-qed-failures*) (newline)
