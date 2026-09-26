;;; zero-deriv-off-countable.scm -- CONSTANCY AND THE MEAN VALUE INEQUALITY
;;; WITH A COUNTABLE EXCEPTIONAL SET (batch 20-A, 2026-09-23).
;;;
;;; THE SOURCE.  Dieudonne, Foundations of Modern Analysis:
;;;
;;;   (8.5.2)  "If there is a denumerable subset D of I such that, for each
;;;            xi in I - D, f has at xi a derivative with respect to I such that
;;;            ||f'(xi)|| <= M, then ||f(beta) - f(alpha)|| <= M(beta - alpha)."
;;;   (8.5.3)  (first part, real-valued) m(beta-alpha) <= phi(beta)-phi(alpha)
;;;            <= M(beta-alpha) when m <= phi'(xi) <= M off D.
;;;   Remark after (8.6.1): "if E = R and A is an interval in R, it is only
;;;            necessary to assume that the derivative of f exists and is 0
;;;            except at the points of a denumerable set."
;;;
;;; THE STATEMENTS PROVED HERE (the headline last):
;;;
;;;   nn-antitone-step-implies-le     the mirror of nn-monotone-step-implies-le
;;;   rr-nested-intervals             nested closed intervals have a common point
;;;   rr-interval-avoids-sequence     no sequence of reals fills an open interval
;;;   countable-image-avoids-interval the image of a countable set misses a point
;;;                                   of every open interval
;;;   neg-deriv-off-countable-nonincreasing
;;;                                   h continuous on [u,v], h' < 0 on (u,v) off a
;;;                                   countable D  =>  h(v) <= h(u)
;;;   mvi-off-countable               h' <= M off D => h(v) - h(u) <= M (v - u)
;;;                                   (8.5.3, upper half; h on the line)
;;;   mvi-abs-off-countable           |h'| <= M off D => |h(v) - h(u)| <= M (v - u)
;;;                                   (8.5.2; h on the line)
;;;   zero-deriv-off-countable        the generalisation of
;;;                                   pw-zero-deriv-off-finite-set: same argument
;;;                                   order (S, h, u, v), "CARD(S) in NN" replaced
;;;                                   by IS-COUNTABLE(S) and S subset RR
;;;   mvi-abs-off-countable-on-interval   (8.5.2) for f ON [a,b], derivative
;;;                                   HAS-DERIV-AT at the interior points off D
;;;   zero-deriv-off-countable-constant   THE HEADLINE: g ON [a,b], continuous,
;;;                                   g' = 0 on (a,b) off a countable D subset
;;;                                   [a,b]  =>  g(s) = g(w) for s, w in [a,b]
;;;
;;; THE ROUTE, AND WHY IT IS NOT DIEUDONNE'S.  Dieudonne proves (8.5.1) by a
;;; least upper bound argument carrying the weights eps * sum_{d_n < xi} 2^-n.
;;; That sum is a series over an index set that depends on xi; the tree would
;;; need the series, its monotonicity in xi and its bound 2 before the argument
;;; starts.  This file uses the other classical route, which needs no series:
;;;
;;;   (a) an open interval is not countable (nested intervals, built by
;;;       dependent choice -- `dc-on-nn-pred', the model is rake-baire-2.scm --
;;;       and the least upper bound of the left ends);
;;;   (b) hence, if h(u) < h(v), some level y in (h(u), h(v)) is taken by h at
;;;       NO point of D;
;;;   (c) the LAST CROSSING of y is found by `ccint-creep' on
;;;          G = { x in [u,v] : h < y on [u,x] }:
;;;       at a point t with h(t) < y continuity extends G to the right; at a
;;;       point with h(t) > y continuity forbids G from reaching t; at a point
;;;       with h(t) = y, t is interior and not in D (h(t) = y is not a value of
;;;       h on D), so h'(t) < 0 and the Caratheodory slope makes h > y just
;;;       left of t -- G cannot reach t either.  So v is in G and h(v) < y,
;;;       against y < h(v).
;;;   (d) the mean value inequality from (c) applied to h(x) - (M + e) x,
;;;       e -> 0 (`rr-le-of-le-add-all-pos'); the absolute form applies it to
;;;       h and to -h; constancy is M = 0.
;;;   (e) a function ON [a,b] is carried to the line by EXTEND-CONST, which
;;;       keeps continuity and the interior derivatives
;;;       (interval-calculus-laws.scm).
;;;
;;; IS-COUNTABLE is 20-D's (structure-library/regulated-primitive.scm): D is a
;;; set, empty or the image of a function on NN.  Nothing here uses more.
;;;
;;; LOAD WINDOW.  lo: the latest citation is `pw-lt-ne'
;;; (theorem-library/pw-antiderivative-laws); IS-COUNTABLE needs
;;; structure-library/regulated-primitive before it.  hi: nothing cites this
;;; file yet (wave 2 will, from the path-integral block).  Slot: immediately
;;; after "theorem-library/pw-antiderivative-laws".
;;;
;;; Helper prefix: zdc-.  Binders: z..._ throughout (none folds onto a class
;;; name or a registered constant).
;;; ---- file-local driver helpers (prefix zdc-) --------------------------

(define (zdc-head? f h) (and (pair? f) (eq? (car f) h)))

;;; the typing (IN (F X) B) from F in FUN(A, B) and X in A, both in context.
(define (zdc-app! f a b x) (fact 'fun-apply-type-c f a b x))

;;; close the focus goal from contradictory LINEAR premises, named by formula:
;;; `ineq' proves 0 < 0 from them, `rr-lt-irrefl' denies it, NOT-elim closes.
(define (zdc-absurd! . prems)
  (fact 'rr-zero-in)
  (dk-have! '(< 0 0) (lambda () (apply dk-ineq! prems)))
  (fact 'rr-lt-irrefl 0)
  (ai '(NOT (< 0 0))))

;;; =====================================================================
;;; (0) `pw-lt-ne': a strict inequality denies both orientations of the equation.
;;; Moved here 2026-09-23 from pw-antiderivative-laws.scm (batch 21), which now loads AFTER this
;;; file and cites `zero-deriv-off-countable'; this file cites `pw-lt-ne'.
;;; The step of the finite-set induction there needs it to say that a point strictly inside a
;;; half is not the point that was just inserted, and the tree has no
;;; `rr-lt-ne': it is taken from `rr-pos-ne-zero' on the difference.
;;; =====================================================================
(sp (make-wff "forall([pcu_ in rr, pcv_ in rr], pcu_ < pcv_ implies
   not(pcu_ = pcv_) and not(pcv_ = pcu_))"))
(dk-peel!)
(fact 'rr-zero-in)
(fact 'rr-sub-in-rr 'pcv_ 'pcu_)
(dk-have! '(< 0 (- pcv_ pcu_))
  (lambda () (dk-ineq! '(IN pcu_ RR) '(IN pcv_ RR) '(< pcu_ pcv_))))
(fact 'rr-pos-ne-zero '(- pcv_ pcu_))
(dk-conj-close!
 (lambda ()
   (let ((e (car (dk-landed* (lambda () (di))))))
     (dk-have! '(= (- pcv_ pcu_) 0) (lambda () (subst e) (crs)))
     (ai '(NOT (= (- pcv_ pcu_) 0))))))
(qed 'pw-lt-ne)
(topic! 'pw-lt-ne 'inequalities)
(alias! 'pw-lt-ne "a strict inequality denies the equation")

;;; =====================================================================
;;; (1) THE MIRROR OF nn-monotone-step-implies-le.
;;; =====================================================================
(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f (succ k)) (f k))))
       (FORALL n (IMPLIES (IN n NN)
         (FORALL m (IMPLIES (IN m NN)
           (IMPLIES (<= m n) (<= (f n) (f m))))))))))))
(define zdc1-typ  (dk-landed-1 (lambda () (di))))
(define zdc1-f    (cadr zdc1-typ))
(define zdc1-step (dk-landed-1 (lambda () (di))))
(fact 'nn-zero-in)
(zdc-app! zdc1-f 'NN 'RR 0)
(define zdc1-br (use-induction))
(dk-focus! (cdr (assq 'base zdc1-br)))
(dk-peel-to! '<=)
(let ((m (caddr (dk-goal))))
  (let ((m (cadr m)))
    (fact 'nn-zero-le m)
    (fact 'nn-in-rr m)
    (fact 'nn-in-rr 0)
    (have! (list 'AND (list 'IN m 'RR) '(IN 0 RR)))
    (have! (list 'AND (list '<= m 0) (list '<= 0 m)))
    (fact 'rr-leq-antisymmetric m 0)
    (subst (list '= m 0))))
(fact 'rr-leq-reflexive (list zdc1-f 0))
(ass)
(dk-focus! (cdr (assq 'step zdc1-br)))
(define zdc1-n  (cdr (assq 'var zdc1-br)))
(define zdc1-ih (cdr (assq 'ih  zdc1-br)))
(dk-peel-to! '<=)
(define zdc1-m (cadr (caddr (dk-goal))))
(fact 'nn-succ-closed zdc1-n)
(zdc-app! zdc1-f 'NN 'RR zdc1-m)
(zdc-app! zdc1-f 'NN 'RR zdc1-n)
(zdc-app! zdc1-f 'NN 'RR (list 'succ zdc1-n))
(fact 'nn-le-succ-cases zdc1-n zdc1-m)
(use-cases (list (list '<= zdc1-m zdc1-n) (list '= zdc1-m (list 'succ zdc1-n)))
  (lambda ()
    (inst+ zdc1-ih zdc1-m)
    (inst+ zdc1-step zdc1-n)
    (dk-ineq! (list 'IN (list zdc1-f zdc1-m) 'RR)
              (list 'IN (list zdc1-f zdc1-n) 'RR)
              (list 'IN (list zdc1-f (list 'succ zdc1-n)) 'RR)
              (list '<= (list zdc1-f zdc1-n) (list zdc1-f zdc1-m))
              (list '<= (list zdc1-f (list 'succ zdc1-n)) (list zdc1-f zdc1-n))))
  (lambda ()
    (subst (list '= zdc1-m (list 'succ zdc1-n)))
    (fact 'rr-leq-reflexive (list zdc1-f (list 'succ zdc1-n)))
    (ass)))
(qed 'nn-antitone-step-implies-le)
(topic! 'nn-antitone-step-implies-le 'analysis)
(alias! 'nn-antitone-step-implies-le
        "a sequence that decreases at each step is nonincreasing")

;;; =====================================================================
;;; (2) NESTED INTERVALS (Cantor).
;;; =====================================================================
(define zdc2-s
  '(SEP zsv_ RR (FORSOME zsk_ (AND (IN zsk_ NN) (= zsv_ (zlo_ zsk_))))))

(sp (make-wff "forall([zlo_ in fun(nn, rr), zhi_ in fun(nn, rr)],
   forall([k in nn], zlo_(k) <= zlo_(succ(k))) implies
   forall([k in nn], zhi_(succ(k)) <= zhi_(k)) implies
   forall([k in nn], zlo_(k) <= zhi_(k)) implies
   forsome([zy_ in rr], forall([n in nn], zlo_(n) <= zy_ and zy_ <= zhi_(n))))"))
(dk-peel!)
(define zdc2-bnd
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL)
                            (equal? (caddr (caddr f)) '(<= (zlo_ k) (zhi_ k)))))
           "the interval bound"))
(define zdc2-monl (dk-fact! 'nn-monotone-step-implies-le 'zlo_))
(define zdc2-monr (dk-fact! 'nn-antitone-step-implies-le 'zhi_))
;; every left end lies below every right end
(dk-have! '(FORALL zm_ (IMPLIES (IN zm_ NN) (FORALL zn_ (IMPLIES (IN zn_ NN)
             (<= (zlo_ zm_) (zhi_ zn_))))))
  (lambda ()
    (dk-peel!)
    (let* ((g (dk-goal)) (m (cadr (cadr g))) (n (cadr (caddr g))))
      (fact 'nn-in-rr m)
      (fact 'nn-in-rr n)
      (zdc-app! 'zlo_ 'NN 'RR m) (zdc-app! 'zlo_ 'NN 'RR n)
      (zdc-app! 'zhi_ 'NN 'RR m) (zdc-app! 'zhi_ 'NN 'RR n)
      (have! (list 'AND (list 'IN m 'RR) (list 'IN n 'RR)))
      (fact 'rr-leq-total m n)
      (use-cases (list (list '<= m n) (list '<= n m))
        (lambda ()
          (dk-apply! zdc2-monl n m)
          (dk-apply! zdc2-bnd n)
          (dk-ineq! (list 'IN (list 'zlo_ m) 'RR) (list 'IN (list 'zlo_ n) 'RR)
                    (list 'IN (list 'zhi_ n) 'RR)
                    (list '<= (list 'zlo_ m) (list 'zlo_ n))
                    (list '<= (list 'zlo_ n) (list 'zhi_ n))))
        (lambda ()
          (dk-apply! zdc2-monr m n)
          (dk-apply! zdc2-bnd m)
          (dk-ineq! (list 'IN (list 'zlo_ m) 'RR) (list 'IN (list 'zhi_ m) 'RR)
                    (list 'IN (list 'zhi_ n) 'RR)
                    (list '<= (list 'zhi_ m) (list 'zhi_ n))
                    (list '<= (list 'zlo_ m) (list 'zhi_ m))))))))
(define zdc2-key
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (eq? (cadr f) 'zm_))) "the key bound"))
;; (IN (zlo_ k) S)
(define (zdc2-in-s! k)
  (zdc-app! 'zlo_ 'NN 'RR k)
  (dk-have! (list 'IN (list 'zlo_ k) zdc2-s)
    (lambda ()
      (in-sep! (lambda () (ass))
               (lambda () (ew k) (dk-conj-close! (lambda ()
                                   (if (zdc-head? (dk-goal) 'IN) (ass) (rfl)))))))))
;; RR-UPPER-BOUND(S, zhi_(n))
(define (zdc2-ub! n)
  (zdc-app! 'zhi_ 'NN 'RR n)
  (dk-have! (list 'RR-UPPER-BOUND zdc2-s (list 'zhi_ n))
    (lambda ()
      (mac 'rr-upper-bound)
      (dk-conj-close!
       (lambda ()
         (if (zdc-head? (dk-goal) 'IN)
             (ass)
             (let* ((mem (dk-landed-1 (lambda () (di))))
                    (x (cadr mem)))
               (dk-split-all! (dk-landed (lambda () (sep-me mem))))
               (let ((k (dk-skolem! (dk-pick (lambda (f) (and (zdc-head? f 'FORSOME)
                                                              (dk-contains? f x)))
                                             "the index of x"))))
                 (subst (list '= x (list 'zlo_ k)))
                 (dk-apply! zdc2-key k n)
                 (ass)))))))))
(have! (list 'SUBSET zdc2-s 'RR)
  (lambda () (mac 'subset-def) (let ((m (dk-landed-1 (lambda () (di))))) (sep-me m) (ass))))
(fact 'nn-zero-in)
(zdc2-in-s! 0)
(have! (list 'FORSOME 'x_ (list 'IN 'x_ zdc2-s)) (lambda () (ew '(zlo_ 0)) (ass)))
(zdc2-ub! 0)
(have! (list 'RR-BOUNDED-ABOVE zdc2-s)
  (lambda () (mac 'rr-bounded-above) (ew '(zhi_ 0)) (ass)))
(fact 'rr-sup-in zdc2-s)
(define zdc2-sup (list 'SUP zdc2-s))
(define zdc2-upper
  (let ((ub (dk-fact! 'rr-sup-upper zdc2-s)))
    (dk-split-all! (dk-landed (lambda () (mac-h 'rr-upper-bound ub))))
    (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f zdc2-sup)
                              (not (dk-contains? f 'RR-UPPER-BOUND))))
             "the sup's upper-bound universal")))
(define zdc2-least (dk-fact! 'rr-sup-least zdc2-s))
(ew zdc2-sup)
(dk-conj-close!
 (lambda ()
   (if (zdc-head? (dk-goal) 'IN)
       (ass)
       (let ((n (dk-di-var!)))
         (dk-conj-close!
          (lambda ()
            (if (equal? (caddr (dk-goal)) zdc2-sup)
                (begin (zdc2-in-s! n) (dk-apply! zdc2-upper (list 'zlo_ n)) (ass))
                (begin (zdc2-ub! n) (dk-apply! zdc2-least (list 'zhi_ n)) (ass)))))))))
(qed 'rr-nested-intervals)
(topic! 'rr-nested-intervals 'analysis)
(alias! 'rr-nested-intervals "nested interval theorem"
        "nested closed intervals have a common point")

;;; =====================================================================
;;; (3) NO SEQUENCE FILLS AN INTERVAL.
;;; =====================================================================
(define zdc3-cart '(CARTESIAN RR RR))
(define zdc3-xs '(SEP zpv_ (CARTESIAN RR RR) (< (NTH 1 zpv_) (NTH 2 zpv_))))
(define zdc3-nxt
  (list 'VNB-LAMBDA '(LIST zkv_ zuv_) (list 'CARTESIAN 'NN zdc3-xs)
    (list 'SEP 'zyv_ zdc3-xs
      '(AND (<= (NTH 1 zuv_) (NTH 1 zyv_))
         (AND (<= (NTH 2 zyv_) (NTH 2 zuv_))
              (OR (< (zse_ zkv_) (NTH 1 zyv_)) (< (NTH 2 zyv_) (zse_ zkv_))))))))

;;; reduce every (NTH i (LIST ...)) in the goal
(define (zdc-nth-r!)
  (let loop ((n 0))
    (if (and (< n 6)
             (let scan ((e (dk-goal)))
               (and (pair? e)
                    (or (and (eq? (car e) 'NTH) (pair? (cddr e))
                             (zdc-head? (caddr e) 'LIST))
                        (any-pred scan e)))))
        (begin (nth-r) (loop (+ n 1))))))

;;; (IN T XS) in context -> both projections typed and ordered
(define (zdc3-parts! t)
  (dk-have! (list 'IN t zdc3-cart) (lambda () (sep-me (list 'IN t zdc3-xs)) (ass)))
  (dk-have! (list '< (list 'NTH 1 t) (list 'NTH 2 t))
            (lambda () (sep-me (list 'IN t zdc3-xs)) (ass)))
  (if (not (dk-asm? (list 'IN (list 'NTH 2 t) 'RR)))
      (dk-split! (dk-fact! 'cartesian-nth t 'RR 'RR))))

;;; goal (IN (LIST A B) XS), with A, B typed and A < B in context
(define (zdc3-pair-in! a b)
  (fact 'pair-in-cartesian 'RR 'RR a b)
  (in-sep! (lambda () (ass)) (lambda () (zdc-nth-r!) (ass))))

(sp (make-wff "forall([zse_ in fun(nn, rr), zp_ in rr, zq_ in rr], zp_ < zq_ implies
   forsome([zy_ in rr], zp_ < zy_ and zy_ < zq_ and
     forall([n in nn], not(zse_(n) = zy_))))"))
(dk-peel!)
(define zdc3-m  (dk-skolem! (dk-fact! 'rr-midpoint-between 'zp_ 'zq_)))
(define zdc3-p1 (dk-skolem! (dk-fact! 'rr-midpoint-between 'zp_ zdc3-m)))
(define zdc3-q1 (dk-skolem! (dk-fact! 'rr-midpoint-between zdc3-m 'zq_)))
(define zdc3-a0 (list 'LIST zdc3-p1 zdc3-q1))
;; the state space is a set and holds the start
(fact 'rr-is-set)
(have! (list 'IN zdc3-cart 'SET)
       (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass)))))
(have! (list 'SUBSET zdc3-xs zdc3-cart)
       (lambda () (mac 'subset-def)
                  (let ((m (dk-landed-1 (lambda () (di))))) (sep-me m) (ass))))
(fact 'subclass-of-set-is-set zdc3-xs zdc3-cart)
(dk-have! (list '< zdc3-p1 zdc3-q1)
  (lambda () (dk-ineq! (list 'IN zdc3-p1 'RR) (list 'IN zdc3-q1 'RR) (list 'IN zdc3-m 'RR)
                       (list '< zdc3-p1 zdc3-m) (list '< zdc3-m zdc3-q1))))
(dk-have! (list 'IN zdc3-a0 zdc3-xs) (lambda () (zdc3-pair-in! zdc3-p1 zdc3-q1)))
;; the step is total on the whole state space
(define (zdc3-offer! k u v)
  (ew v)
  (dk-conj-close!
   (lambda ()
     (if (equal? (dk-goal) (list 'IN v zdc3-xs))
         (zdc3-pair-in! (cadr v) (caddr v))
         (begin
           (fact 'pair-in-cartesian 'NN zdc3-xs k u)
           (dk-lam-b!)
           (in-sep! (lambda () (zdc3-pair-in! (cadr v) (caddr v)))
                    (lambda ()
                      (zdc-nth-r!)
                      (dk-conj-close!
                       (lambda ()
                         (if (zdc-head? (dk-goal) 'OR)
                             (let ((l (cadr (dk-goal))))
                               (if (dk-asm? l) (begin (oi-l) (ass)) (begin (oi-r) (ass))))
                             (if (dk-asm? (dk-goal)) (ass)
                                 (dk-ineq! (list 'IN (list 'NTH 1 u) 'RR)
                                           (list 'IN (list 'NTH 2 u) 'RR)
                                           (list 'IN (cadr v) 'RR) (list 'IN (caddr v) 'RR)
                                           (list '< (cadr v) (caddr v))))))))))))))
(dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
            (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u zdc3-xs)
              (list 'FORSOME 'y (list 'AND (list 'IN 'y zdc3-xs)
                                      (list 'IN 'y (list zdc3-nxt 'k 'u))))))))
  (lambda ()
    (let* ((ls (dk-peel!))
           (k (cadr (find-first (lambda (f) (and (zdc-head? f 'IN) (eq? (caddr f) 'NN))) ls)))
           (u (cadr (find-first (lambda (f) (and (zdc-head? f 'IN) (equal? (caddr f) zdc3-xs))) ls)))
           (l (list 'NTH 1 u)) (r (list 'NTH 2 u)) (z (list 'zse_ k)))
      (zdc3-parts! u)
      (zdc-app! 'zse_ 'NN 'RR k)
      (let ((w1 (dk-skolem! (dk-fact! 'rr-midpoint-between l r))))
        (have! (list 'AND (list 'IN z 'RR) (list 'IN w1 'RR)))
        (fact 'rr-leq-total z w1)
        (use-cases (list (list '<= z w1) (list '<= w1 z))
          (lambda ()
            (let ((w2 (dk-skolem! (dk-fact! 'rr-midpoint-between w1 r))))
              (dk-have! (list '< z w2)
                (lambda () (dk-ineq! (list 'IN z 'RR) (list 'IN w1 'RR) (list 'IN w2 'RR)
                                     (list '<= z w1) (list '< w1 w2))))
              (dk-have! (list '< w2 r)
                (lambda () (ass)))
              (dk-have! (list '<= l w2)
                (lambda () (dk-ineq! (list 'IN l 'RR) (list 'IN w1 'RR) (list 'IN w2 'RR)
                                     (list '< l w1) (list '< w1 w2))))
              (fact 'rr-leq-reflexive r)
              (zdc3-offer! k u (list 'LIST w2 r))))
          (lambda ()
            (let ((w0 (dk-skolem! (dk-fact! 'rr-midpoint-between l w1))))
              (dk-have! (list '< w0 z)
                (lambda () (dk-ineq! (list 'IN z 'RR) (list 'IN w1 'RR) (list 'IN w0 'RR)
                                     (list '<= w1 z) (list '< w0 w1))))
              (dk-have! (list '<= w0 r)
                (lambda () (dk-ineq! (list 'IN r 'RR) (list 'IN w1 'RR) (list 'IN w0 'RR)
                                     (list '< w1 r) (list '< w0 w1))))
              (fact 'rr-leq-reflexive l)
              (zdc3-offer! k u (list 'LIST l w0)))))))))
;; the recursion
(define zdc3-f (dk-skolem! (dk-fact! 'dc-on-nn-pred zdc3-xs zdc3-a0 zdc3-nxt)))
(define zdc3-stp
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f zdc3-f)
                            (dk-contains? f 'succ)))
           "the per-stage step"))
(define zdc3-lo (list 'VNB-LAMBDA 'zn_ 'NN (list 'NTH 1 (list zdc3-f 'zn_))))
(define zdc3-hi (list 'VNB-LAMBDA 'zn_ 'NN (list 'NTH 2 (list zdc3-f 'zn_))))
;; type stage KV and its successor, open the step there: the three conditions land.
(define (zdc3-stage! kv)
  (fact 'nn-succ-closed kv)
  (zdc-app! zdc3-f 'NN zdc3-xs kv)
  (zdc-app! zdc3-f 'NN zdc3-xs (list 'succ kv))
  (zdc3-parts! (list zdc3-f kv))
  (zdc3-parts! (list zdc3-f (list 'succ kv)))
  (fact 'pair-in-cartesian 'NN zdc3-xs kv (list zdc3-f kv))
  (let* ((inst (dk-apply! zdc3-stp kv))
         (red  (car (dk-landed (lambda () (lam-b-h inst))))))
    (dk-split-all! (dk-landed (lambda () (sep-me red))))))
(define (zdc3-typed! lam)
  (dk-have! (list 'IN lam '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let ((kv (dk-di-var!)))
        (zdc-app! zdc3-f 'NN zdc3-xs kv)
        (zdc3-parts! (list zdc3-f kv))
        (ass)))))
(zdc3-typed! zdc3-lo)
(zdc3-typed! zdc3-hi)
(dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
            (list '<= (list zdc3-lo 'k) (list zdc3-lo '(succ k)))))
  (lambda () (let ((kv (dk-di-var!))) (zdc3-stage! kv) (dk-lam-b!) (ass))))
(dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
            (list '<= (list zdc3-hi '(succ k)) (list zdc3-hi 'k))))
  (lambda () (let ((kv (dk-di-var!))) (zdc3-stage! kv) (dk-lam-b!) (ass))))
(dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
            (list '<= (list zdc3-lo 'k) (list zdc3-hi 'k))))
  (lambda ()
    (let ((kv (dk-di-var!)))
      (zdc-app! zdc3-f 'NN zdc3-xs kv)
      (zdc3-parts! (list zdc3-f kv))
      (dk-lam-b!)
      (fact 'rr-lt-implies-le (list 'NTH 1 (list zdc3-f kv)) (list 'NTH 2 (list zdc3-f kv)))
      (ass))))
(define zdc3-y (dk-skolem! (dk-fact! 'rr-nested-intervals zdc3-lo zdc3-hi)))
(define zdc3-in
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f zdc3-y)
                            (dk-contains? f zdc3-lo)))
           "the common-point universal"))
;; land NTH 1 (f n) <= y <= NTH 2 (f n), reduced
(define (zdc3-at! n)
  (zdc-app! zdc3-f 'NN zdc3-xs n)
  (zdc3-parts! (list zdc3-f n))
  (for-each (lambda (c) (lam-b-h c))
            (dk-split! (dk-apply! zdc3-in n))))
(fact 'nn-zero-in)
(zdc3-at! 0)
(let ((lo (list 'NTH 1 (list zdc3-f 0))) (hi (list 'NTH 2 (list zdc3-f 0))))
  (dk-have! (list '= lo zdc3-p1)
    (lambda () (subst (list '= (list zdc3-f 0) zdc3-a0)) (zdc-nth-r!) (rfl)))
  (dk-have! (list '= hi zdc3-q1)
    (lambda () (subst (list '= (list zdc3-f 0) zdc3-a0)) (zdc-nth-r!) (rfl))))
(ew zdc3-y)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((zdc-head? g 'IN) (ass))
       ((zdc-head? g 'FORALL)
        (let ((n (dk-di-var!)))
          (zdc3-stage! n)
          (zdc3-at! (list 'succ n))
          (zdc-app! 'zse_ 'NN 'RR n)
          (let ((z (list 'zse_ n))
                (lo (list 'NTH 1 (list zdc3-f (list 'succ n))))
                (hi (list 'NTH 2 (list zdc3-f (list 'succ n)))))
            (use-cases (list (list '< z lo) (list '< hi z))
              (lambda ()
                (dk-have! (list '< z zdc3-y)
                  (lambda () (dk-ineq! (list 'IN z 'RR) (list 'IN lo 'RR) (list 'IN zdc3-y 'RR)
                                       (list '< z lo) (list '<= lo zdc3-y))))
                (dk-split! (dk-fact! 'pw-lt-ne z zdc3-y))
                (ass))
              (lambda ()
                (dk-have! (list '< zdc3-y z)
                  (lambda () (dk-ineq! (list 'IN z 'RR) (list 'IN hi 'RR) (list 'IN zdc3-y 'RR)
                                       (list '< hi z) (list '<= zdc3-y hi))))
                (dk-split! (dk-fact! 'pw-lt-ne zdc3-y z))
                (ass))))))
       (#t
        ;; zp_ < y or y < zq_: through stage 0, where f(0) = [p1, q1]
        (let ((lo (list 'NTH 1 (list zdc3-f 0))) (hi (list 'NTH 2 (list zdc3-f 0))))
          (dk-ineq! '(IN zp_ RR) '(IN zq_ RR) (list 'IN zdc3-y 'RR)
                    (list 'IN zdc3-p1 'RR) (list 'IN zdc3-q1 'RR)
                    (list 'IN lo 'RR) (list 'IN hi 'RR)
                    (list '< 'zp_ zdc3-p1) (list '< zdc3-q1 'zq_)
                    (list '= lo zdc3-p1) (list '= hi zdc3-q1)
                    (list '<= lo zdc3-y) (list '<= zdc3-y hi))))))))
(qed 'rr-interval-avoids-sequence)
(topic! 'rr-interval-avoids-sequence 'analysis)
(alias! 'rr-interval-avoids-sequence "an interval is not countable"
        "no sequence of reals fills an open interval")

;;; =====================================================================
;;; (4) A COUNTABLE SET HAS A COUNTABLE IMAGE: SOME VALUE IN (p,q) IS MISSED.
;;; =====================================================================
(sp (make-wff "forall([zc_, zdm_, zph_], is-countable(zc_) implies zc_ subset zdm_ implies
   zph_ in fun(zdm_, rr) implies
   forall([zp_ in rr, zq_ in rr], zp_ < zq_ implies
     forsome([zy_ in rr], zp_ < zy_ and zy_ < zq_ and
       forall([zx_ in zc_], not(zph_(zx_) = zy_)))))"))
(dk-peel!)
(dk-split-all! (dk-landed (lambda () (mac-h 'is-countable '(IS-COUNTABLE zc_)))))
(define zdc4-or (dk-pick (dk-head? 'OR) "the countability disjunction"))
(use-cases zdc4-or
  ;; D empty: any point of (p,q) will do
  (lambda ()
    (let ((w (dk-skolem! (dk-fact! 'rr-midpoint-between 'zp_ 'zq_))))
      (ew w)
      (dk-conj-close!
       (lambda ()
         (if (zdc-head? (dk-goal) 'FORALL)
             (let ((x (dk-di-var!)))
               (di)
               (dk-have! (list 'IN x 'EMPTY-SET)
                 (lambda () (subst '(= EMPTY-SET zc_)) (ass)))
               (fact 'empty-set-has-no-members x)
               (ai (list 'NOT (list 'IN x 'EMPTY-SET))))
             (ass))))))
  ;; D = e(NN): the image sequence n |-> phi(e(n)) misses a point of (p,q)
  (lambda ()
    (let* ((e (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the enumeration")))
           (cov (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f e)))
                         "the covering universal"))
           (sq (list 'VNB-LAMBDA 'zsn_ 'NN (list 'zph_ (list e 'zsn_)))))
      (dk-have! (list 'IN sq '(FUN NN RR))
        (lambda ()
          (dk-lam-t!)
          (let ((kv (dk-di-var!)))
            (zdc-app! e 'NN 'zc_ kv)
            (fact 'subset-mem-fwd 'zc_ 'zdm_ (list e kv))
            (zdc-app! 'zph_ 'zdm_ 'RR (list e kv))
            (ass))))
      (let* ((y (dk-skolem! (dk-fact! 'rr-interval-avoids-sequence sq 'zp_ 'zq_)))
             (av (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f sq)))
                          "the avoidance universal")))
        (ew y)
        (dk-conj-close!
         (lambda ()
           (if (zdc-head? (dk-goal) 'FORALL)
               (let* ((x (dk-di-var!))
                      (n (dk-skolem! (dk-apply! cov x)))
                      (ne (dk-apply! av n)))
                 (lam-b-h ne)
                 (subst (list '= x (list e n)))
                 (ass))
               (ass))))))))
(qed 'countable-image-avoids-interval)
(topic! 'countable-image-avoids-interval 'analysis)
(alias! 'countable-image-avoids-interval
        "the image of a countable set misses a point of every open interval")

;;; =====================================================================
;;; (5) THE LAST CROSSING: a negative derivative off a countable set.
;;; =====================================================================

;;; unfold IS-CONTINUOUS-AT(RR-MS, RR-MS, F, T) (destroying it) and take the
;;; delta at EPS (POS-RR EPS in context).  Returns (delta . delta-universal).
(define (zdc-cont! f t e)
  (dk-split-all! (dk-landed (lambda ()
    (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS f t)))))
  (let* ((eu (dk-pick (lambda (fm) (and (zdc-head? fm 'FORALL) (dk-contains? fm 'POS-RR)
                                        (dk-contains? fm (list f t))))
                      "the eps universal"))
         (d  (dk-skolem! (dk-apply! eu e)))
         (du (dk-pick (lambda (fm) (and (zdc-head? fm 'FORALL) (dk-contains? fm d)
                                        (dk-contains? fm 'DIST)))
                      "the delta universal")))
    (fact 'rr-pos-rr-in-rr d)
    (fact 'rr-lt-of-pos-rr d)
    (cons d du)))

(define (zdc-in-pts! z)
  (dk-have! (list 'IN z '(PTS RR-MS)) (lambda () (slot 'PTS) (ass))))

;;; d(A,B) <= R from the linear PREMS
(define (zdc-dist-le! a b r . prems)
  (fact 'rr-sub-in-rr a b)
  (dk-have! (list '<= (list '(DIST RR-MS) a b) r)
    (lambda () (mac 'rr-ms-dist) (mac 'rr-abs-bound)
               (dk-conj-close! (lambda () (apply dk-ineq! prems))))))

;;; d(A,B) <= R in context -> -R <= A - B and A - B <= R
(define (zdc-unpack! a b r)
  (fact 'rr-sub-in-rr a b)
  (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) a b) r))
  (mac-h 'rr-abs-bound (list '<= (list 'abs (list '- a b)) r))
  (dk-split! (list 'AND (list '<= (list '- r) (list '- a b)) (list '<= (list '- a b) r))))

;;; POS-RR of a positive difference, halved: returns e with e + e = X
(define (zdc-half-of! x prems)
  (dk-have! (list '< 0 x) (lambda () (apply dk-ineq! prems)))
  (fact 'rr-pos-rr-of-lt x)
  (dk-halve! x))

(define zdc5-stmt "forall([zh_ in fun(rr, rr), zu_ in rr, zv_ in rr, zc_], zu_ < zv_ implies
   forall([zx_ in ccint(zu_, zv_)], is-continuous-at(rr-ms, rr-ms, zh_, zx_)) implies
   is-countable(zc_) implies zc_ subset rr implies
   forall([zt_ in ooint(zu_, zv_)], not(zt_ in zc_) implies
     forsome([zl_], is-diff-at(zh_, zt_, zl_) and zl_ < 0)) implies
   zh_(zv_) <= zh_(zu_))")

(define zdc5-y #f)     ; the level avoided by h(D)
(define zdc5-g #f)     ; the creeping set
(define zdc5-av #f)    ; forall x in D. h(x) /= y

(define (zdc5-g-of y)
  (list 'SEP 'zgx_ 'RR
    (list 'AND '(AND (<= zu_ zgx_) (<= zgx_ zv_))
      (list 'FORALL 'zgz_ (list 'IMPLIES '(IN zgz_ (CCINT zu_ zgx_))
                                (list '< '(zh_ zgz_) y))))))

(define (zdc5-local g)
  (list 'FORALL 't_
    (list 'IMPLIES '(IN t_ (CCINT zu_ zv_))
      (list 'FORSOME 'd_
        (list 'AND '(IN d_ RR)
          (list 'AND '(< 0 d_)
            (list 'IMPLIES
              (list 'FORSOME 'w_ (list 'AND (list 'IN 'w_ g) '(< (- t_ d_) w_)))
              (list 'FORALL 'y_
                (list 'IMPLIES (list 'AND '(IN y_ (CCINT zu_ zv_)) '(<= y_ (+ t_ d_)))
                      (list 'IN 'y_ g))))))))))

;;; (IN W G) in context: open it; land W in RR, u <= W, W <= v, and
;;; h(W) < y (W is in [u, W]); return the "below y on [u, W]" universal.
(define (zdc5-g-open! w)
  (sep-me (list 'IN w zdc5-g))
  (dk-split-all!)
  (let ((gu (dk-pick (lambda (f) (and (zdc-head? f 'FORALL)
                                      (zdc-head? (caddr f) 'IMPLIES)
                                      (zdc-head? (cadr (caddr f)) 'IN)
                                      (equal? (caddr (cadr (caddr f))) (list 'CCINT 'zu_ w))
                                      (zdc-head? (caddr (caddr f)) '<)))
                     "the below-y universal")))
    (fact 'rr-leq-reflexive w)
    (zdc5-below! gu w w)
    gu))

;;; h(Z) < y from Z in RR, u <= Z, Z <= W and GU = G's universal at W
(define (zdc5-below! gu z w)
  (zdc-app! 'zh_ 'RR 'RR z)
  (dk-have! (list 'IN z (list 'CCINT 'zu_ w))
    (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
  (dk-apply! gu z))

;;; the three membership facts of Z in CCINT(LO, HI), from the membership MEM
(define (zdc-ccint-parts! z lo hi)
  (let ((mem (list 'IN z (list 'CCINT lo hi))))
    (fact 'ccint-elt-in-rr lo hi z)
    (dk-have! (list '<= lo z)
      (lambda () (dk-split-all! (dk-landed (lambda () (mac-h 'ccint-membership mem)))) (ass)))
    (dk-have! (list '<= z hi)
      (lambda () (dk-split-all! (dk-landed (lambda () (mac-h 'ccint-membership mem)))) (ass)))))

;;; case A: h(t) < y.  Continuity gives a window where h < y, and it creeps.
(define (zdc5-case-a! t)
  (let* ((ht (list 'zh_ t))
         (x  (list '- zdc5-y ht)))
    (fact 'rr-sub-in-rr zdc5-y ht)
    (let* ((e  (zdc-half-of! x (list (list 'IN zdc5-y 'RR) (list 'IN ht 'RR)
                                     (list '< ht zdc5-y))))
           (dd (zdc-cont! 'zh_ t e))
           (d  (car dd)) (du (cdr dd)))
      (ew d)
      (dk-conj-close!
       (lambda ()
         (if (not (zdc-head? (dk-goal) 'IMPLIES))
             (ass)
             (let* ((ex (dk-landed-1 (lambda () (di))))
                    (w  (dk-skolem! ex))
                    (gu (zdc5-g-open! w))
                    (ls (dk-peel!))
                    (ls (append ls (dk-split-all! ls)))
                    (yy (cadr (find-first (lambda (f) (and (zdc-head? f 'IN)
                                                            (equal? (caddr f) '(CCINT zu_ zv_))))
                                          ls))))
               (zdc-ccint-parts! yy 'zu_ 'zv_)
               (in-sep!
                (lambda () (ass))
                (lambda ()
                  (dk-conj-close!
                   (lambda ()
                     (if (not (zdc-head? (dk-goal) 'FORALL))
                         (ass)
                         (let ((z (dk-di-var!)))
                           (zdc-ccint-parts! z 'zu_ yy)
                           (zdc-app! 'zh_ 'RR 'RR z)
                           (have! (list 'AND (list 'IN z 'RR) (list 'IN w 'RR)))
                           (fact 'rr-leq-total z w)
                           (use-cases (list (list '<= z w) (list '<= w z))
                             (lambda () (zdc5-below! gu z w) (ass))
                             (lambda ()
                               (zdc-dist-le! t z d
                                 (list 'IN t 'RR) (list 'IN z 'RR) (list 'IN d 'RR)
                                 (list 'IN w 'RR) (list 'IN yy 'RR)
                                 (list '< (list '- t d) w) (list '<= w z)
                                 (list '<= z yy) (list '<= yy (list '+ t d)))
                               (zdc-in-pts! z)
                               (dk-apply! du z)
                               (zdc-unpack! ht (list 'zh_ z) e)
                               (dk-ineq! (list 'IN ht 'RR) (list 'IN (list 'zh_ z) 'RR)
                                         (list 'IN e 'RR) (list 'IN zdc5-y 'RR)
                                         (list '<= (list '- e) (list '- ht (list 'zh_ z)))
                                         (list '= (list '+ e e) x) (list '< 0 e)))))))))))))))))

;;; cases B and C end the same way: W in G with t - d < W is impossible.
;;; LEFT! is called when W <= t, W /= t is NOT known; it closes the goal.
(define (zdc5-vacuous! t d at-or-right! left!)
  (let* ((ex (dk-landed-1 (lambda () (di))))
         (w  (dk-skolem! ex))
         (gu (zdc5-g-open! w)))
    (have! (list 'AND (list 'IN t 'RR) (list 'IN w 'RR)))
    (fact 'rr-leq-total t w)
    (use-cases (list (list '<= t w) (list '<= w t))
      (lambda () (zdc5-below! gu t w) (at-or-right!))
      (lambda () (left! w)))))

;;; case B: y < h(t).
(define (zdc5-case-b! t)
  (let* ((ht (list 'zh_ t))
         (x  (list '- ht zdc5-y)))
    (fact 'rr-sub-in-rr ht zdc5-y)
    (let* ((e  (zdc-half-of! x (list (list 'IN zdc5-y 'RR) (list 'IN ht 'RR)
                                     (list '< zdc5-y ht))))
           (dd (zdc-cont! 'zh_ t e))
           (d  (car dd)) (du (cdr dd)))
      (ew d)
      (dk-conj-close!
       (lambda ()
         (if (not (zdc-head? (dk-goal) 'IMPLIES))
             (ass)
             (zdc5-vacuous! t d
               (lambda ()
                 (zdc-absurd! (list 'IN ht 'RR) (list 'IN zdc5-y 'RR)
                              (list '< ht zdc5-y) (list '< zdc5-y ht)))
               (lambda (w)
                 (let ((hw (list 'zh_ w)))
                   (zdc-dist-le! t w d
                     (list 'IN t 'RR) (list 'IN w 'RR) (list 'IN d 'RR)
                     (list '< (list '- t d) w) (list '<= w t))
                   (zdc-in-pts! w)
                   (dk-apply! du w)
                   (zdc-unpack! ht hw e)
                   (zdc-absurd! (list 'IN ht 'RR) (list 'IN hw 'RR)
                                (list 'IN e 'RR) (list 'IN zdc5-y 'RR)
                                (list '<= (list '- ht hw) e)
                                (list '= (list '+ e e) x) (list '< 0 e)
                                (list '< hw zdc5-y)))))))))))

;;; case C: h(t) = y.  Then t is interior, off D, and the derivative there is
;;; negative: h is above y just to the left of t.
(define (zdc5-case-c! t der)
  (let* ((ht (list 'zh_ t))
         (eqy (list '= ht zdc5-y)))
    (dk-have! (list 'NOT (list 'IN t 'zc_))
      (lambda ()
        (di)
        (dk-apply! zdc5-av t)
        (ai (list 'NOT eqy))))
    (dk-have! (list 'NOT (list '= 'zu_ t))
      (lambda ()
        (di)
        (dk-have! (list '< ht zdc5-y) (lambda () (subst (list '= t 'zu_)) (ass)))
        (zdc-absurd! (list 'IN ht 'RR) (list 'IN zdc5-y 'RR) (list '< ht zdc5-y) eqy)))
    (dk-have! (list 'NOT (list '= t 'zv_))
      (lambda ()
        (di)
        (dk-have! (list '< zdc5-y ht) (lambda () (subst (list '= t 'zv_)) (ass)))
        (zdc-absurd! (list 'IN ht 'RR) (list 'IN zdc5-y 'RR) (list '< zdc5-y ht) eqy)))
    (have! (list 'AND (list '<= 'zu_ t) (list 'NOT (list '= 'zu_ t))))
    (fact 'rr-le-ne-lt 'zu_ t)
    (have! (list 'AND (list '<= t 'zv_) (list 'NOT (list '= t 'zv_))))
    (fact 'rr-le-ne-lt t 'zv_)
    (dk-have! (list 'IN t '(OOINT zu_ zv_))
      (lambda () (mac 'ooint-membership) (dk-conj-close! (lambda () (ass)))))
    (let* ((l (dk-skolem! (dk-apply! der t))))
      (dk-split-all! (dk-landed (lambda () (mac-h 'is-diff-at (list 'IS-DIFF-AT 'zh_ t l)))))
      (let* ((phi (dk-skolem! (dk-pick (lambda (f) (and (zdc-head? f 'FORSOME)
                                                        (dk-contains? f 'IS-CONTINUOUS-AT)))
                                       "the slope function")))
             (deq (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f phi)
                                            (dk-contains? f '*)))
                           "the difference equation"))
             (pt (list phi t)))
        (fact 'rr-zero-in)
        (fact 'rr-sub-in-rr 0 l)
        (zdc-app! phi 'RR 'RR t)
        (let* ((e  (zdc-half-of! (list '- 0 l) (list (list 'IN l 'RR) (list '< l 0))))
               (dd (zdc-cont! phi t e))
               (d  (car dd)) (du (cdr dd)))
          (ew d)
          (dk-conj-close!
           (lambda ()
             (if (not (zdc-head? (dk-goal) 'IMPLIES))
                 (ass)
                 (zdc5-vacuous! t d
                   (lambda ()
                     (zdc-absurd! (list 'IN ht 'RR) (list 'IN zdc5-y 'RR)
                                  (list '< ht zdc5-y) eqy))
                   (lambda (w)
                     (let ((hw (list 'zh_ w)))
                       (use-em (list '= w t)
                         (lambda ()
                           (dk-have! (list '= hw zdc5-y)
                             (lambda () (subst (list '= w t)) (ass)))
                           (zdc-absurd! (list 'IN hw 'RR) (list 'IN zdc5-y 'RR)
                                        (list '< hw zdc5-y) (list '= hw zdc5-y)))
                         (lambda ()
                           (have! (list 'AND (list '<= w t) (list 'NOT (list '= w t))))
                           (fact 'rr-le-ne-lt w t)
                           (zdc-dist-le! t w d
                             (list 'IN t 'RR) (list 'IN w 'RR) (list 'IN d 'RR)
                             (list '< (list '- t d) w) (list '< w t))
                           (zdc-in-pts! w)
                           (dk-apply! du w)
                           (zdc-app! phi 'RR 'RR w)
                           (zdc-unpack! pt (list phi w) e)
                           (dk-have! (list '< (list phi w) 0)
                             (lambda ()
                               (dk-ineq! (list 'IN pt 'RR) (list 'IN (list phi w) 'RR)
                                         (list 'IN e 'RR) (list 'IN l 'RR)
                                         (list '<= (list '- e) (list '- pt (list phi w)))
                                         (list '= pt l)
                                         (list '= (list '+ e e) (list '- 0 l))
                                         (list '< 0 e))))
                           (fact 'rr-sub-in-rr w t)
                           (dk-have! (list '< (list '- w t) 0)
                             (lambda () (dk-ineq! (list 'IN w 'RR) (list 'IN t 'RR)
                                                  (list '< w t))))
                           (let ((prod (list '* (list phi w) (list '- w t))))
                             (fact 'rr-mul-neg-neg-pos (list phi w) (list '- w t))
                             (dk-apply! deq w)
                             (fact 'rr-sub-in-rr hw ht)
                             (dk-have! (list '< 0 (list '- hw ht))
                               (lambda () (subst (list '= (list '- hw ht) prod)) (ass)))
                             (zdc-absurd! (list 'IN hw 'RR) (list 'IN ht 'RR)
                                          (list 'IN zdc5-y 'RR)
                                          (list '< 0 (list '- hw ht)) eqy
                                          (list '< hw zdc5-y))))))))))))))))

(sp (make-wff zdc5-stmt))
(dk-peel!)
(define zdc5-cont
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-CONTINUOUS-AT)))
           "the continuity hypothesis"))
(define zdc5-der
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-DIFF-AT)))
           "the derivative hypothesis"))
(zdc-app! 'zh_ 'RR 'RR 'zu_)
(zdc-app! 'zh_ 'RR 'RR 'zv_)
(fact 'rr-lt-implies-le 'zu_ 'zv_)
(fact 'rr-leq-reflexive 'zu_)
(fact 'rr-leq-reflexive 'zv_)
(have! '(AND (IN (zh_ zv_) RR) (IN (zh_ zu_) RR)))
(fact 'rr-leq-total '(zh_ zv_) '(zh_ zu_))

(define (zdc5-main!)
  (set! zdc5-y (dk-skolem! (dk-fact! 'countable-image-avoids-interval
                                     'zc_ 'RR 'zh_ '(zh_ zu_) '(zh_ zv_))))
  (set! zdc5-av (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f zdc5-y)
                                          (dk-contains? f 'zc_)))
                         "the avoidance universal"))
  (set! zdc5-g (zdc5-g-of zdc5-y))
  (have! (list 'SUBSET zdc5-g 'RR)
    (lambda () (mac 'subset-def)
               (let ((m (dk-landed-1 (lambda () (di))))) (sep-me m) (ass))))
  ;; u is in G: [u,u] = {u}
  (dk-have! (list 'IN 'zu_ zdc5-g)
    (lambda ()
      (in-sep! (lambda () (ass))
        (lambda ()
          (dk-conj-close!
           (lambda ()
             (if (not (zdc-head? (dk-goal) 'FORALL))
                 (ass)
                 (let ((z (dk-di-var!)))
                   (zdc-ccint-parts! z 'zu_ 'zu_)
                   (have! (list 'AND (list 'IN z 'RR) '(IN zu_ RR)))
                   (have! (list 'AND (list '<= z 'zu_) (list '<= 'zu_ z)))
                   (fact 'rr-leq-antisymmetric z 'zu_)
                   (subst (list '= z 'zu_))
                   (ass)))))))))
  ;; v bounds G
  (dk-have! (list 'RR-UPPER-BOUND zdc5-g 'zv_)
    (lambda ()
      (mac 'rr-upper-bound)
      (dk-conj-close!
       (lambda ()
         (if (zdc-head? (dk-goal) 'IN)
             (ass)
             (let ((m (dk-landed-1 (lambda () (di)))))
               (dk-split-all! (dk-landed (lambda () (sep-me m))))
               (ass)))))))
  ;; the local step
  (dk-have! (zdc5-local zdc5-g)
    (lambda ()
      (let* ((mem (dk-landed-1 (lambda () (di))))
             (t (cadr mem)))
        (dk-apply! zdc5-cont t)
        (zdc-ccint-parts! t 'zu_ 'zv_)
        (zdc-app! 'zh_ 'RR 'RR t)
        (use-em (list '= (list 'zh_ t) zdc5-y)
          (lambda () (zdc5-case-c! t zdc5-der))
          (lambda ()
            (use-em (list '<= (list 'zh_ t) zdc5-y)
              (lambda ()
                (have! (list 'AND (list '<= (list 'zh_ t) zdc5-y)
                                  (list 'NOT (list '= (list 'zh_ t) zdc5-y))))
                (fact 'rr-le-ne-lt (list 'zh_ t) zdc5-y)
                (zdc5-case-a! t))
              (lambda ()
                (fact 'rr-not-le-lt (list 'zh_ t) zdc5-y)
                (zdc5-case-b! t))))))))
  ;; creep to v, and read h(v) < y off the membership
  (let ((at-v (dk-fact! 'ccint-creep 'zu_ 'zv_ zdc5-g)))
    (let ((gu (zdc5-g-open! 'zv_)))
      (zdc-absurd! '(IN (zh_ zv_) RR) (list 'IN zdc5-y 'RR)
                   (list '< '(zh_ zv_) zdc5-y) (list '< zdc5-y '(zh_ zv_))))))

(use-cases '((<= (zh_ zv_) (zh_ zu_)) (<= (zh_ zu_) (zh_ zv_)))
  (lambda () (ass))
  (lambda ()
    (use-em '(= (zh_ zu_) (zh_ zv_))
      (lambda () (dk-ineq! '(IN (zh_ zu_) RR) '(IN (zh_ zv_) RR) '(= (zh_ zu_) (zh_ zv_))))
      (lambda ()
        (have! '(AND (<= (zh_ zu_) (zh_ zv_)) (NOT (= (zh_ zu_) (zh_ zv_)))))
        (fact 'rr-le-ne-lt '(zh_ zu_) '(zh_ zv_))
        (zdc5-main!)))))
(qed 'neg-deriv-off-countable-nonincreasing)
(topic! 'neg-deriv-off-countable-nonincreasing 'analysis)
(alias! 'neg-deriv-off-countable-nonincreasing
        "a continuous function with negative derivative off a countable set does not increase")

;;; =====================================================================
;;; (6) THE MEAN VALUE INEQUALITY OFF A COUNTABLE SET (Dieudonne 8.5.3, upper half).
;;; =====================================================================

;;; beta-reduce the hypothesis F to a fixpoint; return the reduced formula
(define (zdc-beta-h! f)
  (let loop ((f f) (n 0))
    (if (and (< n 6) (dk--redex? f))
        (loop (car (dk-landed (lambda () (lam-b-h f)))) (+ n 1))
        f)))

;;; IN T RR and the Caratheodory slope's value L in RR, read off
;;; IS-DIFF-AT(F, T, L) in a lane (the hypothesis survives)
(define (zdc-diff-typed! f t l)
  (dk-have! (list 'AND (list 'IN t 'RR) (list 'IN l 'RR))
    (lambda ()
      (dk-split-all! (dk-landed (lambda () (mac-h 'is-diff-at (list 'IS-DIFF-AT f t l)))))
      (dk-conj-close! (lambda () (ass)))))
  (dk-split-all!))

(define zdc6-n '(- zv_ zu_))

(sp (make-wff "forall([zh_ in fun(rr, rr), zm_ in rr, zu_ in rr, zv_ in rr, zc_], zu_ < zv_ implies
   forall([zx_ in ccint(zu_, zv_)], is-continuous-at(rr-ms, rr-ms, zh_, zx_)) implies
   is-countable(zc_) implies zc_ subset rr implies
   forall([zt_ in ooint(zu_, zv_)], not(zt_ in zc_) implies
     forsome([zl_], is-diff-at(zh_, zt_, zl_) and zl_ <= zm_)) implies
   zh_(zv_) - zh_(zu_) <= zm_ * (zv_ - zu_))"))
(dk-peel!)
(define zdc6-cont
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-CONTINUOUS-AT)))
           "the continuity hypothesis"))
(define zdc6-der
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-DIFF-AT)))
           "the derivative hypothesis"))
(fact 'rr-zero-in)
(zdc-app! 'zh_ 'RR 'RR 'zu_)
(zdc-app! 'zh_ 'RR 'RR 'zv_)
(fact 'rr-sub-in-rr 'zv_ 'zu_)
(fact 'rr-sub-in-rr '(zh_ zv_) '(zh_ zu_))
(fact 'rr-mul-in-rr 'zm_ zdc6-n)
(dk-have! (list '< 0 zdc6-n) (lambda () (dk-ineq! '(IN zu_ RR) '(IN zv_ RR) '(< zu_ zv_))))
(dk-split! (dk-fact! 'pw-lt-ne 0 zdc6-n))
(have! (list 'AND (list 'IN zdc6-n 'RR) (list 'NOT (list '= zdc6-n 0))))
(fact 'rr-recip-closed zdc6-n)
(fact 'rr-recip-pos zdc6-n)
(dk-have! (list 'FORALL 'd_ (list 'IMPLIES '(POS-RR d_)
            (list '<= '(- (zh_ zv_) (zh_ zu_)) (list '+ (list '* 'zm_ zdc6-n) 'd_))))
  (lambda ()
    (dk-peel!)
    (let* ((d  (caddr (caddr (dk-goal))))
           (rn (list 'recip zdc6-n))
           (e0 (list '* d rn)))
      (fact 'rr-pos-rr-in-rr d)
      (fact 'rr-lt-of-pos-rr d)
      (fact 'rr-mul-in-rr d rn)
      (fact 'rr-mul-pos d rn)
      (fact 'rr-recip-cancel-right d zdc6-n)
      ;; e > 0 with e (v - u) = d, as an ATOM (crs declines recip)
      (dk-have! (list 'FORSOME 'ze_ (list 'AND '(IN ze_ RR)
                   (list 'AND '(< 0 ze_) (list '= (list '* 'ze_ zdc6-n) d))))
        (lambda ()
          (ew e0)
          (dk-conj-close!
           (lambda ()
             (cond ((equal? (dk-goal) (list '= (list '* e0 zdc6-n) d))
                    (subst (list '= (list '* e0 zdc6-n) d)) (rfl))
                   ((dk-asm? (dk-goal)) (ass)))))))
      (let* ((e (dk-skolem! (dk-pick (lambda (f) (and (zdc-head? f 'FORSOME) (dk-contains? f 'ze_)))
                                     "the step")))
             (k (list '+ 'zm_ e))
             (af (list 'VNB-LAMBDA 'zax_ 'RR (list '+ 0 (list '* k 'zax_))))
             (hh (list 'VNB-LAMBDA 'zqx_ 'RR (list '- '(zh_ zqx_) (list af 'zqx_)))))
        (fact 'rr-add-in-rr 'zm_ e)
        (dk-have! (list 'IN hh '(FUN RR RR))
          (lambda ()
            (dk-lam-t!)
            (let ((x (dk-di-var!)))
              (zdc-app! 'zh_ 'RR 'RR x)
              (fact 'rr-mul-in-rr k x)
              (fact 'rr-add-in-rr 0 (list '* k x))
              (fact 'rr-sub-in-rr (list 'zh_ x) (list '+ 0 (list '* k x)))
              (dk-lam-b!) (if (dk-asm? (dk-goal)) (ass)))))
        (dk-have! (list 'FORALL 'zx_ (list 'IMPLIES '(IN zx_ (CCINT zu_ zv_))
                    (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS hh 'zx_)))
          (lambda ()
            (let ((x (dk-di-var!)))
              (fact 'ccint-elt-in-rr 'zu_ 'zv_ x)
              (dk-apply! zdc6-cont x)
              (have! (list 'AND '(IN 0 RR) (list 'AND (list 'IN k 'RR) (list 'IN x 'RR))))
              (fact 'affine-continuous-at 0 k x)
              (fact 'sub-continuous-at 'zh_ af x)
              (ass))))
        (dk-have! (list 'FORALL 'zt_ (list 'IMPLIES '(IN zt_ (OOINT zu_ zv_))
                    (list 'IMPLIES '(NOT (IN zt_ zc_))
                      (list 'FORSOME 'zl_ (list 'AND (list 'IS-DIFF-AT hh 'zt_ 'zl_)
                                                '(< zl_ 0))))))
          (lambda ()
            (let* ((ls (dk-peel!))
                   (t (cadr (find-first (lambda (f) (and (zdc-head? f 'IN)
                                                         (equal? (caddr f) '(OOINT zu_ zv_))))
                                        ls)))
                   (l0 (dk-skolem! (dk-apply! zdc6-der t))))
              (zdc-diff-typed! 'zh_ t l0)
              (have! (list 'AND '(IN 0 RR) (list 'AND (list 'IN k 'RR) (list 'IN t 'RR))))
              (fact 'deriv-affine 0 k t)
              (fact 'deriv-difference 'zh_ af t l0 k)
              (ew (list '- l0 k))
              (dk-conj-close!
               (lambda ()
                 (if (zdc-head? (dk-goal) '<)
                     (dk-ineq! (list 'IN l0 'RR) '(IN zm_ RR) (list 'IN e 'RR)
                               (list '<= l0 'zm_) (list '< 0 e))
                     (ass)))))))
        (let* ((r0 (zdc-beta-h! (dk-fact! 'neg-deriv-off-countable-nonincreasing
                                          hh 'zu_ 'zv_ 'zc_)))
               (zkv (list '* k 'zv_)) (zku (list '* k 'zu_))
               (zmn (list '* 'zm_ zdc6-n)) (zen (list '* e zdc6-n)))
          (fact 'rr-mul-in-rr k 'zv_)
          (fact 'rr-mul-in-rr k 'zu_)
          (fact 'rr-mul-in-rr e zdc6-n)
          (dk-have! (list '= (list '- zkv zku) (list '+ zmn zen)) (lambda () (crs)))
          (dk-ineq! '(IN (zh_ zv_) RR) '(IN (zh_ zu_) RR) (list 'IN zkv 'RR) (list 'IN zku 'RR)
                    (list 'IN zmn 'RR) (list 'IN zen 'RR) (list 'IN d 'RR)
                    r0 (list '= (list '- zkv zku) (list '+ zmn zen)) (list '= zen d)))))))
(fact 'rr-le-of-le-add-all-pos '(- (zh_ zv_) (zh_ zu_)) (list '* 'zm_ zdc6-n))
(ass)
(qed 'mvi-off-countable)
(topic! 'mvi-off-countable 'analysis)
(alias! 'mvi-off-countable "mean value inequality off a countable set"
        "Dieudonne (8.5.3)")

;;; =====================================================================
;;; (7) THE MEAN VALUE INEQUALITY WITH |f'| <= M (Dieudonne 8.5.2), on the line.
;;; =====================================================================
(sp (make-wff "forall([zh_ in fun(rr, rr), zm_ in rr, zu_ in rr, zv_ in rr, zc_], zu_ < zv_ implies
   forall([zx_ in ccint(zu_, zv_)], is-continuous-at(rr-ms, rr-ms, zh_, zx_)) implies
   is-countable(zc_) implies zc_ subset rr implies
   forall([zt_ in ooint(zu_, zv_)], not(zt_ in zc_) implies
     forsome([zl_], is-diff-at(zh_, zt_, zl_) and abs(zl_) <= zm_)) implies
   abs(zh_(zv_) - zh_(zu_)) <= zm_ * (zv_ - zu_))"))
(dk-peel!)
(define zdc7-cont
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-CONTINUOUS-AT)))
           "the continuity hypothesis"))
(define zdc7-der
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-DIFF-AT)))
           "the derivative hypothesis"))
(define zdc7-neg (list 'VNB-LAMBDA 'zqx_ 'RR (list '* -1 '(zh_ zqx_))))
(fact 'rr-zero-in)
(dk-have! '(IN -1 RR) (lambda () (arith)))
(zdc-app! 'zh_ 'RR 'RR 'zu_)
(zdc-app! 'zh_ 'RR 'RR 'zv_)
;; the derivative universal with the bound read as SIGN (+1 or -1) * l <= M
(define (zdc7-der-for! f sgn)
  (dk-have! (list 'FORALL 'zt_ (list 'IMPLIES '(IN zt_ (OOINT zu_ zv_))
              (list 'IMPLIES '(NOT (IN zt_ zc_))
                (list 'FORSOME 'zl_ (list 'AND (list 'IS-DIFF-AT f 'zt_ 'zl_)
                                          '(<= zl_ zm_))))))
    (lambda ()
      (let* ((ls (dk-peel!))
             (t (cadr (find-first (lambda (f) (and (zdc-head? f 'IN)
                                                   (equal? (caddr f) '(OOINT zu_ zv_))))
                                  ls)))
             (l (dk-skolem! (dk-apply! zdc7-der t))))
        (zdc-diff-typed! 'zh_ t l)
        (dk-split-all! (dk-landed (lambda () (mac-h 'rr-abs-bound (list '<= (list 'abs l) 'zm_)))))
        (if (= sgn 1)
            (begin (ew l) (dk-conj-close! (lambda () (ass))))
            (begin
              (fact 'deriv-scalar-mult -1 'zh_ t l)
              (fact 'rr-mul-in-rr -1 l)
              (ew (list '* -1 l))
              (dk-conj-close!
               (lambda ()
                 (if (zdc-head? (dk-goal) '<=)
                     (dk-ineq! (list 'IN l 'RR) '(IN zm_ RR)
                               (list '<= (list '- 'zm_) l))
                     (ass))))))))))
(zdc7-der-for! 'zh_ 1)
(define zdc7-up (dk-fact! 'mvi-off-countable 'zh_ 'zm_ 'zu_ 'zv_ 'zc_))
;; the same for -h
(dk-have! (list 'IN zdc7-neg '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((x (dk-di-var!)))
      (zdc-app! 'zh_ 'RR 'RR x)
      (fact 'rr-mul-in-rr -1 (list 'zh_ x))
      (if (dk--redex? (dk-goal)) (dk-lam-b!)) (if (dk-asm? (dk-goal)) (ass)))))
(dk-have! (list 'FORALL 'zx_ (list 'IMPLIES '(IN zx_ (CCINT zu_ zv_))
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS zdc7-neg 'zx_)))
  (lambda ()
    (let ((x (dk-di-var!)))
      (dk-apply! zdc7-cont x)
      (fact 'scale-continuous-at -1 'zh_ x)
      (ass))))
(zdc7-der-for! zdc7-neg -1)
(define zdc7-dn
  (zdc-beta-h! (dk-fact! 'mvi-off-countable zdc7-neg 'zm_ 'zu_ 'zv_ 'zc_)))
(fact 'rr-sub-in-rr 'zv_ 'zu_)
(fact 'rr-sub-in-rr '(zh_ zv_) '(zh_ zu_))
(fact 'rr-mul-in-rr 'zm_ '(- zv_ zu_))
(fact 'rr-mul-in-rr -1 '(zh_ zv_))
(fact 'rr-mul-in-rr -1 '(zh_ zu_))
(mac 'rr-abs-bound)
(dk-conj-close!
 (lambda ()
   (dk-ineq! '(IN (zh_ zv_) RR) '(IN (zh_ zu_) RR) '(IN (* zm_ (- zv_ zu_)) RR)
             zdc7-up zdc7-dn)))
(qed 'mvi-abs-off-countable)
(topic! 'mvi-abs-off-countable 'analysis)
(alias! 'mvi-abs-off-countable "mean value inequality off a countable set"
        "Dieudonne (8.5.2)")

;;; =====================================================================
;;; (8) CONSTANCY OFF A COUNTABLE SET, on the line: the generalisation of
;;;     pw-zero-deriv-off-finite-set (argument order S, h, u, v kept).
;;; =====================================================================
(sp (make-wff "forall([zs_], is-countable(zs_) implies zs_ subset rr implies
   forall([zh_ in fun(rr, rr)], forall([zx_ in rr], is-continuous-at(rr-ms, rr-ms, zh_, zx_)) implies
     forall([zu_ in rr, zv_ in rr], zu_ < zv_ implies
       forall([zt_ in ooint(zu_, zv_)], not(zt_ in zs_) implies is-diff-at(zh_, zt_, 0)) implies
       zh_(zu_) = zh_(zv_))))"))
(dk-peel!)
(define zdc8-cont
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-CONTINUOUS-AT)))
           "the continuity hypothesis"))
(define zdc8-der
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'IS-DIFF-AT)))
           "the derivative hypothesis"))
(fact 'rr-zero-in)
(dk-have! '(FORALL zx_ (IMPLIES (IN zx_ (CCINT zu_ zv_)) (IS-CONTINUOUS-AT RR-MS RR-MS zh_ zx_)))
  (lambda ()
    (let ((x (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'zu_ 'zv_ x)
      (dk-apply! zdc8-cont x)
      (ass))))
(dk-have! '(FORALL zt_ (IMPLIES (IN zt_ (OOINT zu_ zv_)) (IMPLIES (NOT (IN zt_ zs_))
             (FORSOME zl_ (AND (IS-DIFF-AT zh_ zt_ zl_) (<= (abs zl_) 0))))))
  (lambda ()
    (let* ((ls (dk-peel!))
           (t (cadr (find-first (lambda (f) (and (zdc-head? f 'IN)
                                                 (equal? (caddr f) '(OOINT zu_ zv_))))
                                ls))))
      (dk-apply! zdc8-der t)
      (ew 0)
      (dk-conj-close!
       (lambda ()
         (if (zdc-head? (dk-goal) '<=)
             (begin (mac 'rr-abs-bound) (dk-conj-close! (lambda () (dk-ineq!))))
             (ass)))))))
(define zdc8-ab (dk-fact! 'mvi-abs-off-countable 'zh_ 0 'zu_ 'zv_ 'zs_))
(zdc-app! 'zh_ 'RR 'RR 'zu_)
(zdc-app! 'zh_ 'RR 'RR 'zv_)
(fact 'rr-sub-in-rr 'zv_ 'zu_)
(fact 'rr-sub-in-rr '(zh_ zv_) '(zh_ zu_))
(fact 'rr-mul-in-rr 0 '(- zv_ zu_))
(dk-split-all! (dk-landed (lambda () (mac-h 'rr-abs-bound zdc8-ab))))
(dk-have! '(= (* 0 (- zv_ zu_)) 0) (lambda () (crs)))
(define (zdc8-le! a b)
  (dk-have! (list '<= a b)
    (lambda ()
      (apply dk-ineq! (append (list '(IN (zh_ zv_) RR) '(IN (zh_ zu_) RR)
                                    '(IN (* 0 (- zv_ zu_)) RR) '(= (* 0 (- zv_ zu_)) 0))
                              (filter (lambda (f) (and (zdc-head? f '<=)
                                                       (dk-contains? f '(* 0 (- zv_ zu_)))))
                                      (dk-asms)))))))
(zdc8-le! '(zh_ zu_) '(zh_ zv_))
(zdc8-le! '(zh_ zv_) '(zh_ zu_))
(have! '(AND (IN (zh_ zu_) RR) (IN (zh_ zv_) RR)))
(have! '(AND (<= (zh_ zu_) (zh_ zv_)) (<= (zh_ zv_) (zh_ zu_))))
(fact 'rr-leq-antisymmetric '(zh_ zu_) '(zh_ zv_))
(ass)
(qed 'zero-deriv-off-countable)
(topic! 'zero-deriv-off-countable 'analysis)
(alias! 'zero-deriv-off-countable
        "a function whose derivative vanishes off a countable set is constant")

;;; =====================================================================
;;; (9) ON THE INTERVAL: Dieudonne (8.5.2) and the remark after (8.6.1).
;;; =====================================================================
(define zdc9-e '(EXTEND-CONST zf_ a b))

(sp (make-wff "forall([a in rr, b in rr, zm_ in rr], a < b implies
   forall([zf_ in fun(ccint(a, b), rr)], is-continuous-on(zf_, ccint(a, b)) implies
     forall([zd_], is-countable(zd_) implies zd_ subset ccint(a, b) implies
       forall([zt_ in ooint(a, b)], not(zt_ in zd_) implies
         forsome([zl_], has-deriv-at(zf_, zt_, zl_) and abs(zl_) <= zm_)) implies
       abs(zf_(b) - zf_(a)) <= zm_ * (b - a))))"))
(dk-peel!)
(define zdc9-der
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'HAS-DERIV-AT)))
           "the derivative hypothesis"))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(fact 'extend-const-in-fun 'a 'b 'zf_)
(dk-have! (list 'FORALL 'zx_ (list 'IMPLIES '(IN zx_ (CCINT a b))
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS zdc9-e 'zx_)))
  (lambda ()
    (let ((x (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b x)
      (fact 'extend-const-continuous-at 'a 'b 'zf_ x)
      (ass))))
(fact 'ccint-subset-rr 'a 'b)
(fact 'subset-trans 'zd_ '(CCINT a b) 'RR)
(dk-have! (list 'FORALL 'zt_ (list 'IMPLIES '(IN zt_ (OOINT a b))
            (list 'IMPLIES '(NOT (IN zt_ zd_))
              (list 'FORSOME 'zl_ (list 'AND (list 'IS-DIFF-AT zdc9-e 'zt_ 'zl_)
                                        '(<= (abs zl_) zm_))))))
  (lambda ()
    (let* ((ls (dk-peel!))
           (t (cadr (find-first (lambda (f) (and (zdc-head? f 'IN)
                                                 (equal? (caddr f) '(OOINT a b))))
                                ls)))
           (l (dk-skolem! (dk-apply! zdc9-der t))))
      (fact 'extend-const-deriv-fwd 'a 'b 'zf_ t l)
      (ew l)
      (dk-conj-close! (lambda () (ass))))))
(dk-fact! 'mvi-abs-off-countable zdc9-e 'zm_ 'a 'b 'zd_)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'extend-const-fixes 'a 'b 'a 'zf_)
(fact 'extend-const-fixes 'a 'b 'b 'zf_)
(subst (list '= '(zf_ b) (list zdc9-e 'b)))
(subst (list '= '(zf_ a) (list zdc9-e 'a)))
(ass)
(qed 'mvi-abs-off-countable-on-interval)
(topic! 'mvi-abs-off-countable-on-interval 'analysis)
(alias! 'mvi-abs-off-countable-on-interval "Dieudonne (8.5.2)"
        "mean value inequality with a countable exceptional set, on an interval")

;;; THE HEADLINE: constancy off a countable set, for a function ON [a, b].
(define zdc10-e '(EXTEND-CONST g a b))
(sp (make-wff "forall([a in rr, b in rr], a < b implies
   forall([g], g in fun(ccint(a, b), rr) implies is-continuous-on(g, ccint(a, b)) implies
     forall([zd_], is-countable(zd_) implies zd_ subset ccint(a, b) implies
       forall([zt_ in ooint(a, b)], not(zt_ in zd_) implies has-deriv-at(g, zt_, 0)) implies
       forall([zs_ in ccint(a, b), zw_ in ccint(a, b)], g(zs_) = g(zw_)))))"))
(dk-peel!)
(define zdc10-der
  (dk-pick (lambda (f) (and (zdc-head? f 'FORALL) (dk-contains? f 'HAS-DERIV-AT)))
           "the derivative hypothesis"))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(fact 'extend-const-in-fun 'a 'b 'g)
(dk-have! (list 'FORALL 'zx_ (list 'IMPLIES '(IN zx_ RR)
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS zdc10-e 'zx_)))
  (lambda ()
    (let ((x (dk-di-var!)))
      (fact 'extend-const-continuous-at 'a 'b 'g x)
      (ass))))
(fact 'ccint-subset-rr 'a 'b)
(fact 'subset-trans 'zd_ '(CCINT a b) 'RR)
(define zdc10-z7 (dk-fact! 'zero-deriv-off-countable 'zd_ zdc10-e))
;; E(p) = E(q) for a <= p < q <= b
(define (zdc10-eq! p q)
  (dk-have! (list 'FORALL 'zt_ (list 'IMPLIES (list 'IN 'zt_ (list 'OOINT p q))
              (list 'IMPLIES '(NOT (IN zt_ zd_)) (list 'IS-DIFF-AT zdc10-e 'zt_ 0))))
    (lambda ()
      (let* ((ls (dk-peel!))
             (t (cadr (find-first (lambda (f) (and (zdc-head? f 'IN)
                                                   (equal? (caddr f) (list 'OOINT p q))))
                                  ls))))
        (fact 'ooint-elt-in-rr p q t)
        (dk-have! (list 'AND (list '< p t) (list '< t q))
          (lambda ()
            (dk-split-all! (dk-landed (lambda () (mac-h 'ooint-membership (list 'IN t (list 'OOINT p q))))))
            (dk-conj-close! (lambda () (ass)))))
        (dk-split-all!)
        (dk-have! (list 'IN t '(OOINT a b))
          (lambda ()
            (mac 'ooint-membership)
            (dk-conj-close!
             (lambda ()
               (if (dk-asm? (dk-goal)) (ass)
                   (dk-ineq! '(IN a RR) '(IN b RR) (list 'IN p 'RR) (list 'IN q 'RR)
                             (list 'IN t 'RR) (list '<= 'a p) (list '<= q 'b)
                             (list '< p t) (list '< t q)))))))
        (dk-apply! zdc10-der t)
        (fact 'extend-const-deriv-fwd 'a 'b 'g t 0)
        (ass))))
  (dk-apply! zdc10-z7 p q))
(let* ((g0 (dk-goal))
       (s (cadr (cadr g0)))
       (w (cadr (caddr g0)))
       (es (list zdc10-e s))
       (zdc-ew (list zdc10-e w)))
  (zdc-ccint-parts! s 'a 'b)
  (zdc-ccint-parts! w 'a 'b)
  (fact 'extend-const-fixes 'a 'b s 'g)
  (fact 'extend-const-fixes 'a 'b w 'g)
  (zdc-app! zdc10-e 'RR 'RR s)
  (zdc-app! zdc10-e 'RR 'RR w)
  (use-em (list '= s w)
    (lambda ()
      (subst (list '= s w))
      (zdc-app! 'g '(CCINT a b) 'RR w)
      (rfl))
    (lambda ()
      (have! (list 'AND (list 'IN s 'RR) (list 'IN w 'RR)))
      (fact 'rr-leq-total s w)
      (use-cases (list (list '<= s w) (list '<= w s))
        (lambda ()
          (have! (list 'AND (list '<= s w) (list 'NOT (list '= s w))))
          (fact 'rr-le-ne-lt s w)
          (zdc10-eq! s w)
          (subst (list '= (list 'g s) es))
          (subst (list '= (list 'g w) zdc-ew))
          (ass))
        (lambda ()
          (dk-have! (list 'NOT (list '= w s))
            (lambda ()
              (di)
              (dk-have! (list '= s w) (lambda () (subst (list '= s w)) (rfl)))
              (ai (list 'NOT (list '= s w)))))
          (have! (list 'AND (list '<= w s) (list 'NOT (list '= w s))))
          (fact 'rr-le-ne-lt w s)
          (zdc10-eq! w s)
          (subst (list '= (list 'g s) es))
          (subst (list '= (list 'g w) zdc-ew))
          (subst (list '= es zdc-ew))
          (rfl))))))
(qed 'zero-deriv-off-countable-constant)
(topic! 'zero-deriv-off-countable-constant 'analysis)
(alias! 'zero-deriv-off-countable-constant
        "a continuous function on [a,b] whose derivative vanishes off a countable set is constant"
        "Dieudonne, remark after (8.6.1)")
