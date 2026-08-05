;;; finite-surgery.scm -- the finite-surgery kit, first member: COLLAPSE-AT.
;;;
;;;     COLLAPSE-AT(k)  ==  lam j in NN.  IF (< k j) (pred j) j
;;;
;;; "strictly above k, drop by one; otherwise unchanged" -- the CODOMAIN
;;; surgery the induction step of finite pigeonhole needs, and the one
;;; `delete-at' (bijection.scm) does not do: delete-at removes a point of a
;;; function's DOMAIN, and only for a permutation of S(succ n) that sends the
;;; removed index to n.
;;;
;;; THREE DECISIONS, all deliberate.
;;;
;;; (1) NO BOUND IN THE TERM.  The map does not carry the segment bound n; the
;;; bound lives in the theorems ("for every n and every k <= n, it takes
;;; S(succ n) minus {k} into S(n), injectively").  With n in the term,
;;; COLLAPSE-AT(n,k) and COLLAPSE-AT(m,k) would be DIFFERENT TERMS that happen
;;; to agree, and nothing proved about one would transfer to the other -- which
;;; the pigeonhole step needs, since it composes collapses at two bounds.
;;;
;;; (2) THE CONDITION IS THE OTHER WAY ROUND from the design sketch, and must
;;; be.  Written (IF (< j k) j (pred j)) the body would evaluate pred(0) at
;;; j = k = 0, and pred(0) is undefined (nn-pred.scm) -- so the VNB-LAMBDA
;;; would not be defined on all of its declared domain, and could not be typed.
;;; As written, pred is reached only when k < j, hence only when j /= 0, and
;;; the map is total on NN.
;;;
;;; (3) THE VALUE AT j = k IS JUNK (it is k), and no theorem below mentions it:
;;; k is the point the surgery deletes.
;;;
;;; It is DEFINITIONAL -- a `def-functoid', so its unfolding macete carries no
;;; debt.  What the bills below carry is the NN order supports the arithmetic
;;; cites, nothing about the construction itself.

;;; --------------------------------------------------------------------
;;; Two discreteness read-offs, general facts about NN that the kit needs and
;;; the library did not have in this shape.  (order-lemmas has the neighbours:
;;; nn-not-le-succ-le, nn-le-succ-cases, nn-le-succ.)
;;; --------------------------------------------------------------------

;;; NOT (k < j)  =>  j <= k.  Totality, read off the definition of `<'.
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IMPLIES (NOT (< k_ j_)) (<= j_ k_))))))))
(di) (di)
(use-em '(= j_ k_)
  (lambda ()
    (subst '(= j_ k_))
    (fact 'nn-le-refl 'k_)
    (ass))
  (lambda ()
    (fact 'neq-sym 'j_ 'k_)
    (have! '(NOT (<= k_ j_))
           (lambda ()
             (di)
             (have! '(< k_ j_) (lambda () (mac '<) (from-context!)))
             (ai '(NOT (< k_ j_)))))
    (fact 'nn-not-le-succ-le 'k_ 'j_)
    (fact 'nn-le-succ 'j_)
    (fact 'co-le-trans 'j_ '(succ j_) 'k_)
    (ass)))
(qed 'nn-not-lt-le)
(category! 'nn-not-lt-le 'inequalities)

;;; k < j  =>  succ k <= j.  Discreteness; the strict order has no room.
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IMPLIES (< k_ j_) (<= (succ k_) j_))))))))
(di) (di)
(mac-h '< '(< k_ j_))
(dk-split! '(AND (<= k_ j_) (NOT (= k_ j_))))
(have! '(NOT (<= j_ k_))
       (lambda ()
         (di)
         (fact 'nn-in-rr 'j_)
         (fact 'nn-in-rr 'k_)
         (have! '(AND (IN k_ RR) (IN j_ RR)))
         (have! '(AND (<= k_ j_) (<= j_ k_)))
         (fact 'rr-leq-antisymmetric 'k_ 'j_)
         (ai '(NOT (= k_ j_)))))
(fact 'nn-not-le-succ-le 'j_ 'k_)
(ass)
(qed 'nn-lt-succ-le)
(category! 'nn-lt-succ-le 'inequalities)

;;; --------------------------------------------------------------------
;;; The map.
;;; --------------------------------------------------------------------

(def-functoid 'COLLAPSE-AT '(k_)
  '(VNB-LAMBDA z_ NN (IF (< k_ z_) (PRED z_) z_)))
(notation! 'COLLAPSE-AT 'kind 'functoid 'arity 1
           'english "the collapse of NN at $1")

(define co-if '(IF (< k_ j_) (PRED j_) j_))

;;; the two computation rules.  `lam-b' fires cleanly because the argument's
;;; typing (IN j_ NN) is in context before the reduction, and `if-false' /
;;; `if-true' spawn the branch condition, which is the hypothesis.
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IMPLIES (NOT (< k_ j_))
                     (= ((COLLAPSE-AT k_) j_) j_))))))))
(di)
(mac 'collapse-at)
(lam-b)
(di)
(for-each (lambda (l)
            (dk-focus! l)
            (if (eq? (car (dk-goal)) 'NOT)
                (ass)
                (begin (subst (list '= co-if 'j_)) (rfl))))
          (dk-opened (lambda () (if-false co-if))))
(qed 'collapse-at-lo)
(category! 'collapse-at-lo 'combinatorial)

(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IMPLIES (< k_ j_)
                     (= ((COLLAPSE-AT k_) j_) (PRED j_)))))))))
(di)
(mac 'collapse-at)
(lam-b)
(di)
(for-each (lambda (l)
            (dk-focus! l)
            (if (eq? (car (dk-goal)) '<)
                (ass)
                (begin (subst (list '= co-if '(PRED j_))) (rfl))))
          (dk-opened (lambda () (if-true co-if))))
(qed 'collapse-at-hi)
(category! 'collapse-at-hi 'combinatorial)

;;; the value is a natural, at every k and every j -- including j = k, where it
;;; is k.  Above the cut this needs j /= 0, which k < j supplies.
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN)
                 (FORALL j_ (IMPLIES (IN j_ NN)
                   (IN ((COLLAPSE-AT k_) j_) NN)))))))
(di)
(use-em '(< k_ j_)
  (lambda ()
    (fact 'collapse-at-hi 'k_ 'j_)
    (subst '(= ((COLLAPSE-AT k_) j_) (PRED j_)))
    (fact 'nn-zero-le 'k_)
    (fact 'co-le-lt-trans 0 'k_ 'j_)
    (mac-h '< '(< 0 j_))
    (dk-split! '(AND (<= 0 j_) (NOT (= 0 j_))))
    (fact 'neq-sym 0 'j_)
    (fact 'pred-in-nn 'j_)
    (ass))
  (lambda ()
    (fact 'collapse-at-lo 'k_ 'j_)
    (subst '(= ((COLLAPSE-AT k_) j_) j_))
    (ass)))
(qed 'collapse-at-in-nn)
(category! 'collapse-at-in-nn 'combinatorial)

;;; --------------------------------------------------------------------
;;; What the surgery is FOR: it drops the bound by one, and it is injective
;;; away from the deleted point.  Both are arithmetic once `pred' is turned
;;; into its successor equation (pred-succ) and `succ' into +1
;;; (nn-succ-plus-one) -- from there `ineq' closes each case, including the two
;;; mixed cases of injectivity, where the premises are infeasible.
;;; --------------------------------------------------------------------

(define (co-idx form)                    ; 1-based context position, for `ineq'
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "co-idx: not in context" form))
          ((equal? (car as) form) i)
          (else (loop (cdr as) (+ i 1))))))
(define (co-ineq! . forms) (apply ineq (map co-idx forms)))

(define (co-peel!)
  (let loop ()
    (let ((h (car (dk-goal))))
      (if (memq h '(FORALL IMPLIES)) (begin (di) (loop))))))

;;; k <= n, j <= n, j /= k  =>  COLLAPSE-AT(k)(j) < n.
(sp (make-wff (forall-guarded '(n_ k_ j_)
                (list '(IN n_ NN) '(IN k_ NN) '(IN j_ NN))
                '(IMPLIES (<= k_ n_)
                   (IMPLIES (<= j_ n_)
                     (IMPLIES (NOT (= j_ k_))
                              (< ((COLLAPSE-AT k_) j_) n_)))))))
(co-peel!)
(fact 'nn-in-rr 'k_) (fact 'nn-in-rr 'j_) (fact 'nn-in-rr 'n_)
(use-em '(< k_ j_)
  (lambda ()                             ; value pred(j), and pred(j) + 1 = j <= n
    (fact 'collapse-at-hi 'k_ 'j_)
    (subst '(= ((COLLAPSE-AT k_) j_) (PRED j_)))
    (fact 'nn-zero-le 'k_)
    (fact 'co-le-lt-trans 0 'k_ 'j_)
    (mac-h '< '(< 0 j_))
    (dk-split! '(AND (<= 0 j_) (NOT (= 0 j_))))
    (fact 'neq-sym 0 'j_)
    (fact 'pred-in-nn 'j_)
    (fact 'pred-succ 'j_)
    (mac-h 'nn-succ-plus-one '(= (succ (PRED j_)) j_))
    (fact 'nn-in-rr '(PRED j_))
    (co-ineq! '(= (+ (PRED j_) 1) j_) '(<= j_ n_)))
  (lambda ()                             ; value j, and j + 1 <= k <= n
    (fact 'collapse-at-lo 'k_ 'j_)
    (subst '(= ((COLLAPSE-AT k_) j_) j_))
    (fact 'nn-not-lt-le 'k_ 'j_)
    (have! '(< j_ k_) (lambda () (mac '<) (from-context!)))
    (fact 'nn-lt-succ-le 'j_ 'k_)
    (mac-h 'nn-succ-plus-one '(<= (succ j_) k_))
    (co-ineq! '(<= (+ j_ 1) k_) '(<= k_ n_))))
(qed 'collapse-at-lt)
(category! 'collapse-at-lt 'combinatorial)

;;; injectivity away from k.  Four cases; the two mixed ones close because
;;; k < a and b < k and pred(a) = b cannot hold together.
(sp (make-wff (forall-guarded '(k_ a_ b_)
                (list '(IN k_ NN) '(IN a_ NN) '(IN b_ NN))
                '(IMPLIES (NOT (= a_ k_))
                   (IMPLIES (NOT (= b_ k_))
                     (IMPLIES (= ((COLLAPSE-AT k_) a_) ((COLLAPSE-AT k_) b_))
                              (= a_ b_)))))))
(define (co-hi! v)                       ; k_ < v: value is pred v, and k_+1 <= v
  (fact 'collapse-at-hi 'k_ v)
  (fact 'nn-zero-le 'k_)
  (fact 'co-le-lt-trans 0 'k_ v)
  (mac-h '< (list '< 0 v))
  (dk-split! (list 'AND (list '<= 0 v) (list 'NOT (list '= 0 v))))
  (fact 'neq-sym 0 v)
  (fact 'pred-in-nn v)
  (fact 'pred-succ v)
  (mac-h 'nn-succ-plus-one (list '= (list 'succ (list 'PRED v)) v))
  (fact 'nn-in-rr (list 'PRED v))
  (fact 'nn-lt-succ-le 'k_ v)
  (mac-h 'nn-succ-plus-one (list '<= (list 'succ 'k_) v)))
(define (co-lo! v)                       ; not(k_ < v), v /= k_: value is v, v+1 <= k_
  (fact 'collapse-at-lo 'k_ v)
  (fact 'nn-not-lt-le 'k_ v)
  (have! (list '< v 'k_) (lambda () (mac '<) (from-context!)))
  (fact 'nn-lt-succ-le v 'k_)
  (mac-h 'nn-succ-plus-one (list '<= (list 'succ v) 'k_)))
(define (co-val v) (list (list 'COLLAPSE-AT 'k_) v))
(define (co-eq! s t)                     ; read the value equation at (s,t)
  (have! (list '= s t)
         (lambda ()
           (subst (list '= s (co-val 'a_)))
           (subst (list '= t (co-val 'b_)))
           (ass))))
(co-peel!)
(fact 'nn-in-rr 'k_) (fact 'nn-in-rr 'a_) (fact 'nn-in-rr 'b_)
(use-em '(< k_ a_)
  (lambda ()
    (co-hi! 'a_)
    (use-em '(< k_ b_)
      (lambda ()                                        ; both above
        (co-hi! 'b_)
        (co-eq! '(PRED a_) '(PRED b_))
        (co-ineq! '(= (+ (PRED a_) 1) a_) '(= (+ (PRED b_) 1) b_)
                  '(= (PRED a_) (PRED b_))))
      (lambda ()                                        ; a above, b below
        (co-lo! 'b_)
        (co-eq! '(PRED a_) 'b_)
        (co-ineq! '(= (+ (PRED a_) 1) a_) '(= (PRED a_) b_)
                  '(<= (+ k_ 1) a_) '(<= (+ b_ 1) k_)))))
  (lambda ()
    (co-lo! 'a_)
    (use-em '(< k_ b_)
      (lambda ()                                        ; a below, b above
        (co-hi! 'b_)
        (co-eq! 'a_ '(PRED b_))
        (co-ineq! '(= (+ (PRED b_) 1) b_) '(= a_ (PRED b_))
                  '(<= (+ k_ 1) b_) '(<= (+ a_ 1) k_)))
      (lambda ()                                        ; both below
        (co-lo! 'b_)
        ;; here the claim IS the goal, so `have!' would have no main branch:
        ;; rewrite the goal into the value equation instead.
        (subst (list '= 'a_ (co-val 'a_)))
        (subst (list '= 'b_ (co-val 'b_)))
        (ass)))))
(qed 'collapse-at-inj)
(category! 'collapse-at-inj 'combinatorial)

;;; --------------------------------------------------------------------
;;; The segment face, which is the form the pigeonhole step consumes:
;;; the collapse at a point of S(succ n) takes the REST of S(succ n) into S(n).
;;; Nothing new -- seg-mem-succ-le turns both memberships into <= and
;;; seg-mem-lt turns the conclusion back into membership.
(sp (make-wff (forall-guarded '(n_ k_ j_)
                (list '(IN n_ NN) '(IN k_ NN) '(IN j_ NN))
                '(IMPLIES (IN k_ (ORD-SEGMENT (succ n_)))
                   (IMPLIES (IN j_ (ORD-SEGMENT (succ n_)))
                     (IMPLIES (NOT (= j_ k_))
                              (IN ((COLLAPSE-AT k_) j_) (ORD-SEGMENT n_))))))))
(co-peel!)
(mac-h 'seg-mem-succ-le '(IN k_ (ORD-SEGMENT (succ n_))))
(mac-h 'seg-mem-succ-le '(IN j_ (ORD-SEGMENT (succ n_))))
(fact 'collapse-at-in-nn 'k_ 'j_)
(mac 'seg-mem-lt)
(fact 'collapse-at-lt 'n_ 'k_ 'j_)
(ass)
(qed 'collapse-at-in-seg)
(category! 'collapse-at-in-seg 'combinatorial)
