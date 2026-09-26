;;; vector-taylor-proof.scm -- vector-valued Taylor with a norm remainder bound,
;;; REDUCED TO THE SCALAR CASE via a norm-attaining functional (Hahn-Banach payoff).
;;;
;;; For a curve f : RR -> VEC(m) into a finite-dimensional real NVS m, the Taylor
;;; remainder R = f(x) (-) TAYLOR-POLY-V(f,a,x,n) is a VECTOR.  There is no single
;;; mean-value theta for a vector (the vector MVT fails), so the result is an
;;; INEQUALITY, not an equality:
;;;   there is theta in (a,x) with
;;;     (n+1)! * ||R||  <=  ||f^(n+1)(theta)|| * (x-a)^(n+1).
;;;
;;; REDUCTION: pick (norm-attained-by-functional) a bounded g, ||g||<=1, g(R)=||R||.
;;; Then g o f is a scalar curve, g commutes with the Caratheodory derivative and
;;; the Taylor sum, so g(R) is the scalar Taylor remainder of g o f; scalar
;;; taylor-lagrange supplies theta and the equality
;;;   (n+1)! g(R) = (g o f)^(n+1)(theta) (x-a)^(n+1) = g(f^(n+1)(theta)) (x-a)^(n+1),
;;; and norm-bounded-by-functionals gives g(f^(n+1)(theta)) <= ||f^(n+1)(theta)||.
;;; Multiplying by (x-a)^(n+1) >= 0 clears to the bound.  Loads after
;;; norm-as-sup-proof (norm-attained/bounded) and taylor-proof (scalar Taylor).
;;; ====================================================================
;;; RETIRED 2026-09-14 (proven): nth-deriv-v-in-vec -- GUARDED and proven in the spliced block below (was theorem-library/vector-taylor-guarded.scm)

;;; ====================================================================
;;; vocabulary
;;; ====================================================================

;;; The metric induced by the norm: d(x,y) = ||x (-) y|| on VEC(m).
;;; (Mirrors NF-METRIC-SPACE for a normed field.)
(def-functoid 'NVS-METRIC-SPACE '(m)
  '(LIST (VEC m)
         (VNB-LAMBDA (LIST x y) (CARTESIAN (VEC m) (VEC m)) ((VNRM m) ((VADD m) x ((VNEG m) y))))))

;;; Vector Caratheodory derivative: f'(a) = L, witnessed by phi : RR -> VEC(m)
;;; continuous at a (in the norm metric) with phi(a)=L and
;;;    f(x) (-) f(a) = (x - a) . phi(x).
(def-predicate 'IS-DIFF-AT-V '(m f a L)
  '(AND (IS-NORMED-VECTOR-SPACE m)
   (AND (IN f (FUN RR (VEC m)))
   (AND (IN a RR)
   (AND (IN L (VEC m))
        (FORSOME phi
          (AND (IN phi (FUN RR (VEC m)))
          (AND (IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) phi a)
          (AND (= (phi a) L)
               (FORALL x_ (IMPLIES (IN x_ RR)
                 (= ((VADD m) (f x_) ((VNEG m) (f a)))
                    ((ACT m) (- x_ a) (phi x_))))))))))))))

;;; DERIV-V(m,f,a) = the unique vector derivative value.
(def-functoid 'DERIV-V '(m f a)
  '(IOTA L (IS-DIFF-AT-V m f a L)))

;;; f^(n) as a function RR -> VEC(m):  f^(0)=f, f^(succ n)= x |-> DERIV-V(m,f^(n),x).
(def-by-nn-recursion 'NTH-DERIV-V '(m f)
  'f
  '(n val)
  '(VNB-LAMBDA x RR (DERIV-V m val x)))

;;; Vector Taylor polynomial  Sum_{k=0}^{n} ((x-a)^k / k!) . f^(k)(a), by
;;; recursion on n (vector addition VADD, scalar action ACT -- no AG-tuple needed).
(def-by-nn-recursion 'TAYLOR-POLY-V '(m f a x)
  '((ACT m) (* (power (- x a) 0) (recip (FACTORIAL 0))) ((NTH-DERIV-V m f 0) a))
  '(n val)
  '((VADD m) val
     ((ACT m) (* (power (- x a) (succ n)) (recip (FACTORIAL (succ n))))
              ((NTH-DERIV-V m f (succ n)) a))))

;;; TAYLOR-DIFFERENTIABLE-V: f^(k) (k<=n) norm-continuous on [a,x] and vector-
;;; differentiable on (a,x) with derivative f^(k+1).  (Mirrors the scalar predicate.)
(def-predicate 'TAYLOR-DIFFERENTIABLE-V '(m f a x n)
  '(AND
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (IN t (CCINT a x))
           (IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) (NTH-DERIV-V m f k) t)))))
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (AND (< a t) (< t x))
           (IS-DIFF-AT-V m (NTH-DERIV-V m f k) t ((NTH-DERIV-V m f (succ k)) t))))))))

;;; the remainder vector R = f(x) (-) TAYLOR-POLY-V(f,a,x,n)
(define REMV '((VADD m) (f x) ((VNEG m) (TAYLOR-POLY-V m f a x n))))

;;; =====================================================================
;;; BEGIN spliced block (2026-09-14): nth-deriv-v-in-vec GUARDED and PROVEN, with
;;; nvs-ms-pts, diff-v-value-in-vec, taylor-v-derivs-in-fun, dfun-v-mono and
;;; taylor-v-deriv-in-vec (the order-(n+1) fact the citers use).  Here because
;;; it unfolds the definitions above and is cited below (same reason as
;;; taylor-proof.scm's blocks).  Was theorem-library/vector-taylor-guarded.scm.
;;; =====================================================================
;;; theorem-library/vector-taylor-guarded.scm -- the typing facts of the
;;; VECTOR Taylor arc, GUARDED and PROVEN.  The vector twin of the scalar
;;; spliced block in taylor-proof.scm ("BEGIN spliced block", 2026-09-14).
;;;
;;; SPLICE POINT.  Its window is INSIDE theorem-library/vector-taylor-proof.scm:
;;; it cites that file's definitions (NVS-METRIC-SPACE, IS-DIFF-AT-V,
;;; NTH-DERIV-V and its recursion axioms, TAYLOR-DIFFERENTIABLE-V) and is cited
;;; by vector-taylor-remainder-bound at the END of the same file -- and a
;;; theorem-library file's helpers are invisible to another file.  So, as with
;;; the scalar block, the integrator SPLICES this body into
;;; vector-taylor-proof.scm AFTER the `REMV' define (the end of the vocabulary
;;; section, before "warranted cores") and BEFORE the `(sp ...)' of
;;; vector-taylor-remainder-bound, retiring the `nth-deriv-v-in-vec' support
;;; (vector-taylor-proof.scm:105-114) at the same time.
;;;
;;; THE LEAF, and why it was false.  `nth-deriv-v-in-vec' read
;;;
;;;   forall m f k t.  NVS(m), f in FUN(RR,VEC m), k in NN, t in RR
;;;                    =>  (NTH-DERIV-V m f k)(t) in VEC(m)
;;;
;;; and NTH-DERIV-V(m,f,succ k) = lambda x in RR. DERIV-V(m, f^(k), x), where
;;; DERIV-V is IOTA L. IS-DIFF-AT-V(m, f^(k), x, L) -- undefined wherever f^(k)
;;; is not differentiable, and nothing in the hypotheses said it was.  The
;;; user's decision for the scalar arc, extended here: add the guard, prove
;;; the guarded statement.  The guard is the vector twin of the scalar DFUN:
;;;
;;;   DFUN-V(m,f,n)  :=  forall j_. j_ in NN and j_ <= n
;;;                                =>  NTH-DERIV-V(m,f,j_) in FUN(RR, VEC m)
;;;
;;; and TAYLOR-DIFFERENTIABLE-V implies it (`taylor-v-derivs-in-fun' below,
;;; through the FUN(PTS,PTS) conjunct of IS-CONTINUOUS-AT at the point a of
;;; [a,x]) -- the same route as `taylor-derivs-in-fun'.  The binder of the
;;; guard is j_, not k, because `nth-deriv-v-in-vec' has k as an OUTER binder
;;; and the guard is instantiated at n := k there: a guard spelled with k would
;;; capture (the simultaneous-substitution disease, CLAUDE.md).
;;;
;;; Statements installed here (guards are the only change to the leaf; its
;;; binders and body are byte-identical to vector-taylor-proof.scm:106-113):
;;;
;;;   nvs-ms-pts             forall m. PTS(NVS-METRIC-SPACE m) == VEC(m)
;;;   diff-v-value-in-vec    IS-DIFF-AT-V(m,f,a,L)  =>  L in VEC(m)
;;;   taylor-v-derivs-in-fun TD-V(m,f,a,x,n), a,x in RR, a < x  =>  DFUN-V(m,f,n)
;;;   dfun-v-mono            DFUN-V(m,f,n), n in NN, k in NN, k <= n  =>  DFUN-V(m,f,k)
;;;   nth-deriv-v-in-vec     + DFUN-V(m,f,k)                      (THE LEAF)
;;;   taylor-v-deriv-in-vec  TD-V(m,f,a,x,n), a < t < x, n in NN
;;;                            =>  (NTH-DERIV-V m f (succ n))(t) in VEC(m)
;;;
;;; The last one is what the two CITERS actually use: both
;;; vector-taylor-remainder-bound (vector-taylor-proof.scm) and
;;; nvs-taylor-remainder-bound (nvs-taylor-proof.scm:179) cite
;;; nth-deriv-v-in-vec at ORDER succ n, at a point theta of (a,x) -- and
;;; DFUN-V(m,f,n), all TD-V yields, says nothing about order n+1.  The
;;; (n+1)-st derivative at theta is a vector because it is the L of the
;;; IS-DIFF-AT-V conjunct of TD-V at (n, theta), and that is the scalar
;;; `taylor-deriv-real' recipe.  Each citer changes ONE line:
;;;
;;;   vector-taylor-proof.scm:288
;;;     (quietly (lambda () (fact 'nth-deriv-v-in-vec 'm 'f '(succ n) THETA)))
;;;     -->  (quietly (lambda () (fact 'taylor-v-deriv-in-vec 'm 'f 'a 'x 'n THETA)))
;;;   nvs-taylor-proof.scm:179
;;;     (fact 'nth-deriv-v-in-vec 'cm nt-phi '(succ n) nt-theta)
;;;     -->  (have! (list 'IN (list (list 'NTH-DERIV-V 'cm nt-phi '(succ n)) nt-theta) '(VEC cm))
;;;                 (lambda () (fact 'taylor-v-deriv-in-vec 'cm nt-phi 0 1 'n nt-theta) (ass)))
;;;
;;; (every antecedent -- TD-V, a < theta, theta < x, n in NN -- is in each
;;; citer's context at that line, so `fact' detaches to the typing).  The
;;; nvs-taylor citer wants the have! LANE, not the bare fact: its closing
;;; `prop' has an atom cap of 12, and the six-term instantiation chain of the
;;; new fact (versus the four-term one it replaces) pushed the context to 34
;;; atoms -- "34 distinct atoms, over the cap" -- and the proof stopped one
;;; step short.  The lane lands the one typing formula and nothing else.
;;; Both citers verified on the band (2026-09-14): each `qed's with a bill
;;; identical to the control's minus `nth-deriv-v-in-vec'.
;;;
;;; NOT PROVEN HERE -- gof-nth-deriv and g-of-remainder -- see the block of
;;; comments at the END of this file for their honest guarded statements and
;;; the two machinery gaps that block them (a missing lemma, and a missing
;;; IOTA-definedness rule).
;;;
;;; LOAD WINDOW.  lo: theorem-library/vector-taylor-proof (its own
;;; definitions; everything else cited -- ccint-membership (ccint-basics),
;;; nn-le-refl / nn-le-trans-guarded (nn-order-basics), rr-leq-reflexive,
;;; rr-lt-implies-le (rr-order-basics), fun-apply-type-c
;;; (fun-apply-type-proof), the IS-CONTINUOUS-AT / IS-DIFF-AT-V /
;;; TAYLOR-DIFFERENTIABLE-V unfolds and the PTS projection -- loads well
;;; before it).  hi: vector-taylor-remainder-bound in the SAME file.  Hence
;;; the splice.
;;;
;;; Helper prefix: vtg-.

;;; ---- file-local shapes ----
;;; DFUN-V(m,f,n)
(define (vtg-dfun-v m f n)
  (list 'FORALL 'j_ (list 'IMPLIES (list 'AND '(IN j_ NN) (list '<= 'j_ n))
                          (list 'IN (list 'NTH-DERIV-V m f 'j_) (list 'FUN 'RR (list 'VEC m))))))

(define (vtg-mentions? sym form)
  (cond ((eq? form sym) #t)
        ((pair? form) (or (vtg-mentions? sym (car form)) (vtg-mentions? sym (cdr form))))
        (#t #f)))
(define (vtg-pick pred what)
  (or (find-first pred (dk-asms)) (error "vector-taylor-guarded: no assumption" what)))

;;; =====================================================================
;;; (0) PTS(NVS-METRIC-SPACE m) == VEC(m).  NVS-METRIC-SPACE is a def-functoid
;;; LIST, so `slot-h' has no projection for it; this equation is the macete
;;; that reads the carrier off (bdd-metric-carrier's recipe).
;;; =====================================================================
(sp (make-wff '(FORALL m (== (PTS (NVS-METRIC-SPACE m)) (VEC m)))))
(di)
(mac 'NVS-METRIC-SPACE)   ; (== (PTS (LIST (VEC m) (VNB-LAMBDA ...))) (VEC m))
(slot 'PTS)               ; (== (nth 1 (LIST (VEC m) ...)) (VEC m))
(nth-r)                   ; (== (VEC m) (VEC m))
(qrfl)
(qed 'nvs-ms-pts)
(topic! 'nvs-ms-pts 'analysis)
(alias! 'nvs-ms-pts "the points of the norm metric space are the vectors")

;;; =====================================================================
;;; (1) the derivative value of IS-DIFF-AT-V is a vector: its 4th conjunct.
;;; =====================================================================
(sp (make-wff '(FORALL m (FORALL f (FORALL a (FORALL L
       (IMPLIES (IS-DIFF-AT-V m f a L) (IN L (VEC m)))))))))
(dk-peel-to! 'IN)
(let ((h (vtg-pick (dk-head? 'IS-DIFF-AT-V) "IS-DIFF-AT-V")))
  (dk-split! (dk-landed-1 (lambda () (mac-h 'is-diff-at-v h))))
  (ass))
(qed 'diff-v-value-in-vec)
(topic! 'diff-v-value-in-vec 'analysis)

;;; =====================================================================
;;; (2) TAYLOR-DIFFERENTIABLE-V(m,f,a,x,n), a < x  =>  DFUN-V(m,f,n).
;;; The continuity conjunct at the point a of [a,x] carries the typing
;;; NTH-DERIV-V(m,f,j_) in FUN(PTS RR-MS, PTS (NVS-METRIC-SPACE m)).
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
    (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE-V m f a x n)
    (list 'IMPLIES '(IN a RR) (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(< a x)
      (vtg-dfun-v 'm 'f 'n))))))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                        ; (IN (NTH-DERIV-V m f j_) (FUN RR (VEC m)))
       (nd  (cadr g))
       (m   (cadr nd))
       (k   (cadddr nd))
       (td  (vtg-pick (dk-head? 'TAYLOR-DIFFERENTIABLE-V) "TAYLOR-DIFFERENTIABLE-V"))
       (a   (cadddr td))
       (x   (car (cddddr td)))
       (mem (list 'AND (list 'IN a 'RR) (list 'AND (list '<= a a) (list '<= a x)))))
  ;; a in CCINT(a,x)
  (fact 'rr-leq-reflexive a)
  (fact 'rr-lt-implies-le a x)
  (have! mem)
  (fact 'ccint-membership a x a)
  (ai (list 'IFF (list 'IN a (list 'CCINT a x)) mem))
  (detach! (list 'IMPLIES mem (list 'IN a (list 'CCINT a x))))
  ;; unfold the hypothesis; the continuity conjunct at j_, at the point a
  (let* ((parts (dk-split! (dk-landed-1 (lambda () (mac-h 'taylor-differentiable-v td)))))
         (cont  (or (find-first (lambda (p) (vtg-mentions? 'IS-CONTINUOUS-AT p)) parts)
                    (error "vector-taylor-guarded: no continuity conjunct")))
         (u1    (dk-deepest (lambda () (inst+ cont k))))
         (u2    (dk-deepest (lambda () (inst+ u1 a)))))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous-at u2))))
    ;; (IN nd (FUN (PTS RR-MS) (PTS (NVS-METRIC-SPACE m)))): slot-h reads the
    ;; declared instance RR-MS; the functoid-built space needs the macete (0).
    (let* ((typ (list 'IN nd (list 'FUN '(PTS RR-MS) (list 'PTS (list 'NVS-METRIC-SPACE m))))))
      (if (not (dk-asm? typ)) (error "vector-taylor-guarded: FUN(PTS,PTS) typing not landed"))
      (let ((h1 (dk-landed-1 (lambda () (slot-h 'PTS typ)))))
        (mac-h 'nvs-ms-pts h1)
        (ass)))))
(qed 'taylor-v-derivs-in-fun)
(topic! 'taylor-v-derivs-in-fun 'analysis)
(alias! 'taylor-v-derivs-in-fun
        "a Taylor-differentiable curve has total vector derivatives up to order n")

;;; =====================================================================
;;; (3) DFUN-V is monotone in the order: DFUN-V(m,f,n), n,k in NN, k <= n => DFUN-V(m,f,k).
;;; What lets a citer holding DFUN-V(m,f,n) discharge nth-deriv-v-in-vec's
;;; guard at any k <= n in one `fact'.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'n (list 'FORALL 'k
    (list 'IMPLIES (vtg-dfun-v 'm 'f 'n)
    (list 'IMPLIES '(IN n NN) (list 'IMPLIES '(IN k NN) (list 'IMPLIES '(<= k n)
      (vtg-dfun-v 'm 'f 'k)))))))))))
(dk-peel-to! 'IN)
(let* ((g    (dk-goal))                       ; (IN (NTH-DERIV-V m f j_) (FUN RR (VEC m)))
       (nd   (cadr g))
       (j    (cadddr nd))
       (le   (vtg-pick (lambda (u) (and (pair? u) (eq? (car u) '<=) (symbol? (cadr u))
                                        (symbol? (caddr u)) (not (eq? (cadr u) j))))
                       "k <= n"))
       (k    (cadr le))
       (n    (caddr le))
       (dfun (vtg-pick (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (vtg-mentions? 'FUN u)
                                        (vtg-mentions? n u)))
                       "DFUN-V(m,f,n)"))
       (grd  (vtg-pick (lambda (u) (and (pair? u) (eq? (car u) 'AND) (vtg-mentions? j u)))
                       "(AND (IN j_ NN) (<= j_ k))")))
  (dk-split! grd)
  (fact 'nn-le-trans-guarded j k n)                       ; j_ <= n
  (have! (list 'AND (list 'IN j 'NN) (list '<= j n)))
  (dk-deepest (lambda () (inst+ dfun j)))
  (ass))
(qed 'dfun-v-mono)
(topic! 'dfun-v-mono 'analysis)

;;; =====================================================================
;;; (4) THE LEAF, guarded: nth-deriv-v-in-vec + DFUN-V(m,f,k).
;;; Binders m f k t and the body are byte-identical to the support
;;; (vector-taylor-proof.scm:106-113); the guard is the innermost antecedent.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'k (list 'FORALL 't
     (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
     (list 'IMPLIES '(IN f (FUN RR (VEC m)))
     (list 'IMPLIES '(IN k NN) (list 'IMPLIES '(IN t RR)
     (list 'IMPLIES (vtg-dfun-v 'm 'f 'k)
       '(IN ((NTH-DERIV-V m f k) t) (VEC m)))))))))))))
(dk-peel-to! 'IN)
(let* ((g    (dk-goal))                       ; (IN ((NTH-DERIV-V m f k) t) (VEC m))
       (app  (cadr g))
       (nd   (car app))
       (t    (cadr app))
       (m    (cadr nd))
       (k    (cadddr nd))
       (dfun (vtg-pick (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (vtg-mentions? 'FUN u)))
                       "DFUN-V(m,f,k)")))
  (fact 'nn-le-refl k)
  (have! (list 'AND (list 'IN k 'NN) (list '<= k k)))
  (dk-deepest (lambda () (inst+ dfun k)))                 ; nd in FUN(RR, VEC m)
  (fact 'fun-apply-type-c nd 'RR (list 'VEC m) t)
  (ass))
(qed 'nth-deriv-v-in-vec)
(topic! 'nth-deriv-v-in-vec 'analysis)

;;; =====================================================================
;;; (5) taylor-v-deriv-in-vec: f^(n+1)(t) is the L that IS-DIFF-AT-V carries
;;; for f^(n) at t in (a,x), hence a vector.  The citers' fact.
;;; =====================================================================
(sp (make-wff
  '(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
     (IMPLIES (< a t) (IMPLIES (< t x) (IMPLIES (IN n NN)
       (IN ((NTH-DERIV-V m f (succ n)) t) (VEC m))))))))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                        ; (IN ((NTH-DERIV-V m f (succ n)) t) (VEC m))
       (app (cadr g))
       (t   (cadr app))
       (nd  (car app))
       (n   (cadr (cadddr nd)))
       (td  (vtg-pick (dk-head? 'TAYLOR-DIFFERENTIABLE-V) "TAYLOR-DIFFERENTIABLE-V"))
       (a   (cadddr td))
       (x   (car (cddddr td))))
  (fact 'nn-le-refl n)
  (have! (list 'AND (list 'IN n 'NN) (list '<= n n)))
  (have! (list 'AND (list '< a t) (list '< t x)))
  (let* ((parts (dk-split! (dk-landed-1 (lambda () (mac-h 'taylor-differentiable-v td)))))
         (dcon  (or (find-first (lambda (p) (vtg-mentions? 'IS-DIFF-AT-V p)) parts)
                    (error "vector-taylor-guarded: no differentiability conjunct")))
         (u1    (dk-deepest (lambda () (inst+ dcon n))))
         (u2    (dk-deepest (lambda () (inst+ u1 t)))))  ; IS-DIFF-AT-V m f^(n) t f^(n+1)(t)
    ;; LUTINS instantiation (2026-09-18): `diff-v-value-in-vec' was cited AT
    ;; NTH-DERIV-V(m,f,n) and at f^(n+1)(t), neither of which the certificate
    ;; accepts (an IOTA, and an application of one).  The fourth conjunct of u2
    ;; IS the goal, so unfold it instead -- a rewrite owes nothing.  u2 is not
    ;; needed after this, so the unfold can be destructive.
    (mac-h 'IS-DIFF-AT-V u2)
    (let loop ((k 0))
      (let ((tgt (any-pred (lambda (aa) (and (pair? aa) (memq (car aa) '(AND FORSOME))))
                           (dk-asms))))
        (if (and tgt (< k 20)) (begin (ai tgt) (loop (+ k 1))))))
    (ass)))
(qed 'taylor-v-deriv-in-vec)
(topic! 'taylor-v-deriv-in-vec 'analysis)
(alias! 'taylor-v-deriv-in-vec
        "the (n+1)-st vector derivative at an interior point is a vector")

;;; =====================================================================
;;; NOT PROVEN: gof-nth-deriv, g-of-remainder.  Their honest guarded
;;; statements, and what blocks them.
;;;
;;; gof-nth-deriv (vector-taylor-proof.scm:169) claims, for a bounded linear
;;; functional g, (g o f)^(n+1)(t) = g(f^(n+1)(t)) at EVERY real t.  With the
;;; leaf's binders m f g n t kept, the guard it needs is TWO-part, because the
;;; proof is an induction on the order and each step differentiates on ALL of
;;; RR: (g o f)^(k+1)(x) = DERIV((g o f)^(k), x) = g(DERIV-V(m, f^(k), x)) at
;;; every real x, for every k < n, and then once more at the given t:
;;;
;;;   (FORALL m (FORALL f (FORALL g (FORALL n (FORALL t
;;;     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
;;;     (IMPLIES (IN f (FUN RR (VEC m)))
;;;     (IMPLIES (IN n NN) (IMPLIES (IN t RR)
;;;     (IMPLIES (FORALL j_ (IMPLIES (AND (IN j_ NN) (< j_ n))
;;;                (FORALL t_ (IMPLIES (IN t_ RR)
;;;                  (IS-DIFF-AT-V m (NTH-DERIV-V m f j_) t_ ((NTH-DERIV-V m f (succ j_)) t_))))))
;;;     (IMPLIES (IS-DIFF-AT-V m (NTH-DERIV-V m f n) t ((NTH-DERIV-V m f (succ n)) t))
;;;       (= ((NTH-DERIV (COMPOSE g f) (succ n)) t)
;;;          (g ((NTH-DERIV-V m f (succ n)) t)))))))))))))
;;;
;;; g-of-remainder (vector-taylor-proof.scm:154) needs the same first guard at
;;; j_ < n (it evaluates (g o f)^(k)(a) = g(f^(k)(a)) for k <= n) and no
;;; pointwise one.
;;;
;;; TWO GAPS, either of which stops the proof:
;;;
;;; (G1) THE STEP LEMMA IS MISSING.  Nothing in the tree carries a bounded
;;;      linear functional through the Caratheodory derivative.  Its statement:
;;;
;;;   (FORALL m (FORALL g (FORALL h (FORALL t (FORALL L
;;;     (IMPLIES (IS-NORMED-VECTOR-SPACE m)
;;;     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
;;;     (IMPLIES (IS-DIFF-AT-V m h t L)
;;;       (IS-DIFF-AT (COMPOSE g h) t (g L))))))))))
;;;
;;;      Its proof needs three bricks the tree also lacks: (a) a bounded linear
;;;      functional is continuous at every vector in the norm metric
;;;      (IS-CONTINUOUS-AT (NVS-METRIC-SPACE m) RR-MS g v -- eps/delta from the
;;;      bound, delta := eps/(c+1); rests on `nvs-metric-is-ms', itself an
;;;      asserted leaf of this file); (b) composition of continuity across
;;;      DIFFERENT metric spaces (the proven `compose-continuous-at' is stated
;;;      at RR-MS/RR-MS only; here the middle space is NVS-METRIC-SPACE m);
;;;      (c) g(u (-) v) = g(u) - g(v), i.e. g(VNEG v) = -g(v), from
;;;      homogeneity at r = -1 and ACT(-1, v) = VNEG(v) -- no NVS/module lemma
;;;      states the latter.  With those, the factor is g o phi and the identity
;;;      (g o h)(x) - (g o h)(t) = g(h(x) (-) h(t)) = g((x-t).phi(x)) =
;;;      (x-t) g(phi(x)) is linearity twice.
;;;
;;; (G2) THE CITER CANNOT DISCHARGE THE GUARD -- an IOTA-definedness gap.
;;;      vector-taylor-remainder-bound holds TAYLOR-DIFFERENTIABLE-V(m,f,a,x,n),
;;;      whose continuity conjunct gives f^(k) in FUN(RR, VEC m) for k <= n,
;;;      i.e. DERIV-V(m, f^(k-1), x) = IOTA L. IS-DIFF-AT-V(...) DENOTES at
;;;      every real x.  Semantically that is exactly "f^(k-1) is differentiable
;;;      at every x" (an IOTA denotes iff its property has a unique satisfier),
;;;      which is the first guard above.  But the kernel has no rule from the
;;;      definedness of an IOTA to its property: `iota-d' (pi-iota-def!,
;;;      primitive-inferences.scm) goes the OTHER way -- it posts the
;;;      existence-and-uniqueness obligation and only then grants the property
;;;      -- and no theorem or axiom bridges (IN (IOTA x p) X) to p[(IOTA x p)].
;;;      So from TD-V nothing in the tree reaches
;;;      IS-DIFF-AT-V(m, f^(k), x, f^(k+1)(x)) off the open interval (a,x),
;;;      and the induction cannot start.  The same gap is latent in
;;;      `gof-taylor-diff' (the triage's "obstacle 2"): TAYLOR-DIFFERENTIABLE
;;;      of g o f demands (g o f)^(k) in FUN(RR,RR), which is differentiability
;;;      of (g o f)^(k-1) on ALL of RR, and TD-V supplies it only through the
;;;      same IOTA reading.  The missing principle, as a kernel rule or a
;;;      base axiom (schema in p):
;;;
;;;        (IN (IOTA x p) X)  =>  p[x := (IOTA x p)]      (iota-in-elim)
;;;
;;;      With it, TD-V => the first guard is a two-line lemma (nth-deriv-v-succ,
;;;      lam-b, the rule), and the induction for gof-nth-deriv goes through
;;;      modulo (G1).
;;; =====================================================================

;;; ===== END spliced block =====
;;; BEGIN spliced block (2026-09-17, rake batch H): gof-in-fun, vtaylor-poly-in-vec and
;;; vtaylor-remainder-in-vec PROVEN modulo 0.  The last two were add-to-pss supports
;;; here and were UNDERDETERMINED as stated (f a total map and n natural, but
;;; TAYLOR-POLY-V applies ACT to NTH-DERIV-V(m,f,succ k)(a), an IOTA with no
;;; satisfier for a non-differentiable f, e.g. f = abs at a = 0, n = 1 -- the
;;; defect of nth-deriv-v-in-vec, 2026-09-14); each gained DFUN-V(m,f,n) as its
;;; innermost antecedent.  Spliced here because the proofs unfold this file's
;;; definitions and cite its file-local theorems; the original is
;;; scratchpad/surgery/orig-0917/rake-analysis-typing.scm.
;;; SECTION B -- gof-in-fun.   (SPLICE into vector-taylor-proof.scm.)
;;;
;;; COMPOSE(g,f) is VNB-LAMBDA z_ in DOM(f). g(f(z_)), so the domain is DOM(f)
;;; and not RR: `dom-of-fun' supplies (= (DOM f) RR) from f in FUN(RR) and
;;; RR in SET, and one `subst' puts the goal in the shape `lam-t' wants.
;;; The two `have!' LANES are lanes because `mac-h' is destructive and the
;;; IS-BOUNDED-LINEAR-FUNCTIONAL hypothesis is wanted intact.
;;; =====================================================================
(sp (make-wff '(FORALL m (FORALL f (FORALL g
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
       (IN (COMPOSE g f) (FUN RR RR)))))))))
(dk-peel!)
(fact 'rr-is-set)
(have! '(IN f (FUN RR))
       (lambda ()
         (dk-split-all!
          (dk-landed (lambda () (mac-h 'fun-codomain-iff '(IN f (FUN RR (VEC m)))))))
         (ass)))
(have! '(IN g (FUN (VEC m) RR))
       (lambda ()
         (dk-split-all! (dk-landed (lambda () (mac-h 'IS-BOUNDED-LINEAR-FUNCTIONAL
                                                     '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)))))
         (dk-split-all! (dk-landed (lambda () (mac-h 'IS-LINEAR-FUNCTIONAL
                                                     '(IS-LINEAR-FUNCTIONAL m g)))))
         (ass)))
(have! '(AND (IN f (FUN RR)) (IN RR SET)))
(dk-split! (dk-fact! 'dom-of-fun 'RR 'f))
(mac 'COMPOSE)
(subst '(= (DOM f) RR))
(dk-lam-t!)
(let ((rkt-z (dk-di-var!)))
  (fact 'fun-apply-type-c 'f 'RR '(VEC m) rkt-z)
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list 'f rkt-z))
  (ass))
(qed 'gof-in-fun)
(topic! 'gof-in-fun 'analysis)

;;; =====================================================================
;;; SECTION C -- vtaylor-poly-in-vec, GUARDED.   (SPLICE; needs nvs-act-laws
;;; moved above vector-taylor-proof in load.scm.)
;;;
;;; The induction is on n and TAYLOR-POLY-V is a def-by-nn-recursion, so the
;;; two recursion axioms `taylor-poly-v-zero' / `taylor-poly-v-succ' (both
;;; `definitional') are the whole of the unfolding.  `ni' wants the NN variable
;;; OUTERMOST, and the support quantifies m f a x first, so the induction is a
;;; COMPANION statement with the binders swapped and the leaf derived from it
;;; (rake-algebra's strictly-mono-ge-id-ind shape).
;;;
;;; In the step the induction hypothesis wants DFUN-V(m,f,n) while the context
;;; carries DFUN-V(m,f,succ n): `dfun-v-mono' (proven in the spliced block
;;; above) is exactly that descent.
;;; =====================================================================
;;; formula builders (sections C and D only)
(define (rkt-imps ants concl) (fold-right (lambda (aa gg) (list 'IMPLIES aa gg)) concl ants))
(define (rkt-alls vs body)    (fold-right (lambda (vv gg) (list 'FORALL vv gg)) body vs))
(define (rkt-dfun-v m f n)
  (list 'FORALL 'j_ (list 'IMPLIES (list 'AND '(IN j_ NN) (list '<= 'j_ n))
                          (list 'IN (list 'NTH-DERIV-V m f 'j_) (list 'FUN 'RR (list 'VEC m))))))
;;; the coefficient (x-a)^k / k! of the k-th Taylor term
(define (rkt-coef k) (list '* (list 'power '(- x a) k) (list 'recip (list 'FACTORIAL k))))
(define (rkt-coeff-real! k)
  (fact 'rr-sub-in-rr 'x 'a)
  (fact 'power-closed-at k '(- x a))
  (fact 'recip-factorial-in-rr k)
  (have! (list 'AND (list 'IN (list 'power '(- x a) k) 'RR)
                    (list 'IN (list 'recip (list 'FACTORIAL k)) 'RR)))
  (fact 'rr-mul-closed (list 'power '(- x a) k) (list 'recip (list 'FACTORIAL k))))
;;; the k-th Taylor term ((x-a)^k/k!) . f^(k)(a) is a vector.  The DFUN-V guard
;;; at order k must already be in context: it is what types f^(k)(a).
(define (rkt-term-in-vec! k)
  (rkt-coeff-real! k)
  (fact 'nth-deriv-v-in-vec 'm 'f k 'a)
  (fact 'nvs-act-in-vec 'm (rkt-coef k) (list (list 'NTH-DERIV-V 'm 'f k) 'a)))

(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (rkt-alls '(m f a x)
      (rkt-imps (list '(IS-NORMED-VECTOR-SPACE m) '(IN f (FUN RR (VEC m)))
                      '(IN a RR) '(IN x RR) (rkt-dfun-v 'm 'f 'n))
                '(IN (TAYLOR-POLY-V m f a x n) (VEC m))))))))
(define rkt-br (use-induction))
(define rkt-n  (cdr (assq 'var rkt-br)))
(define rkt-ih (cdr (assq 'ih  rkt-br)))

;;; base: TAYLOR-POLY-V(m,f,a,x,0) = ((x-a)^0/0!) . f^(0)(a)
(dk-focus! (cdr (assq 'base rkt-br)))
(dk-peel-to! 'IN)
(mac 'taylor-poly-v-zero)
(fact 'nn-zero-in)
(rkt-term-in-vec! 0)
(ass)

;;; step: TAYLOR-POLY-V(...,succ n) = TAYLOR-POLY-V(...,n) (+) term(succ n)
(dk-focus! (cdr (assq 'step rkt-br)))
(dk-peel-to! 'IN)
(mac 'taylor-poly-v-succ)
(let ((rkt-sn (list 'succ rkt-n)))
  (fact 'nn-succ-closed rkt-n)
  (fact 'nn-le-succ rkt-n)
  (fact 'dfun-v-mono 'm 'f rkt-sn rkt-n)        ; DFUN-V(m,f,succ n) => DFUN-V(m,f,n)
  (let* ((i1 (dk-deepest (lambda () (inst+ rkt-ih 'm))))
         (i2 (dk-deepest (lambda () (inst+ i1 'f))))
         (i3 (dk-deepest (lambda () (inst+ i2 'a)))))
    (dk-deepest (lambda () (inst+ i3 'x))))     ; TAYLOR-POLY-V(m,f,a,x,n) in VEC(m)
  (rkt-term-in-vec! rkt-sn)
  (fact 'nvs-vadd-in-vec 'm (list 'TAYLOR-POLY-V 'm 'f 'a 'x rkt-n)
        (list (list 'ACT 'm) (rkt-coef rkt-sn) (list (list 'NTH-DERIV-V 'm 'f rkt-sn) 'a)))
  (ass))
(qed 'rkt-vtaylor-poly-in-vec-ind)
(topic! 'rkt-vtaylor-poly-in-vec-ind 'analysis)

;;; the leaf's own binder order, guard innermost
(sp (make-wff
  (rkt-alls '(m f a x n)
    (rkt-imps (list '(IS-NORMED-VECTOR-SPACE m) '(IN f (FUN RR (VEC m)))
                    '(IN a RR) '(IN x RR) '(IN n NN) (rkt-dfun-v 'm 'f 'n))
              '(IN (TAYLOR-POLY-V m f a x n) (VEC m))))))
(dk-peel-to! 'IN)
(fact 'rkt-vtaylor-poly-in-vec-ind 'n 'm 'f 'a 'x)
(ass)
(qed 'vtaylor-poly-in-vec)
(topic! 'vtaylor-poly-in-vec 'analysis)
(alias! 'vtaylor-poly-in-vec
        "the vector Taylor polynomial is a vector when the derivatives are total")

;;; =====================================================================
;;; SECTION D -- vtaylor-remainder-in-vec, GUARDED.   (SPLICE.)
;;;
;;; R = f(x) (+) VNEG(TAYLOR-POLY-V(m,f,a,x,n)).  The tree has no VNEG typing
;;; fact for a normed vector space (op-typing.scm proves VADD and VNRM only),
;;; so the `op VNEG VEC VEC' conjunct of the IS-NORMED-VECTOR-SPACE unfold is
;;; projected here first.
;;; =====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (FORALL v_ (IMPLIES (IN v_ (VEC m)) (IN ((VNEG m) v_) (VEC m))))))))
(dk-peel!)
(dk-split-all!
 (dk-landed (lambda () (mac-h 'is-normed-vector-space '(IS-NORMED-VECTOR-SPACE m)))))
(fact 'fun-apply-type-c '(VNEG m) '(VEC m) '(VEC m) 'v_)
(ass)
(qed 'rkt-nvs-vneg-in-vec)
(topic! 'rkt-nvs-vneg-in-vec 'analysis)
(alias! 'rkt-nvs-vneg-in-vec "the negative of a vector is a vector")

(sp (make-wff
  (rkt-alls '(m f a x n)
    (rkt-imps (list '(IS-NORMED-VECTOR-SPACE m) '(IN f (FUN RR (VEC m)))
                    '(IN a RR) '(IN x RR) '(IN n NN) (rkt-dfun-v 'm 'f 'n))
              '(IN ((VADD m) (f x) ((VNEG m) (TAYLOR-POLY-V m f a x n))) (VEC m))))))
(dk-peel-to! 'IN)
(fact 'fun-apply-type-c 'f 'RR '(VEC m) 'x)
(fact 'vtaylor-poly-in-vec 'm 'f 'a 'x 'n)
(fact 'rkt-nvs-vneg-in-vec 'm '(TAYLOR-POLY-V m f a x n))
(fact 'nvs-vadd-in-vec 'm '(f x) '((VNEG m) (TAYLOR-POLY-V m f a x n)))
(ass)
(qed 'vtaylor-remainder-in-vec)
(topic! 'vtaylor-remainder-in-vec 'analysis)
(alias! 'vtaylor-remainder-in-vec
        "the vector Taylor remainder is a vector when the derivatives are total")
;;; ===== END spliced block (2026-09-17) =====

;;; ====================================================================
;;; warranted cores
;;; ====================================================================

;;; the norm metric is a metric space.
;;; nvs-metric-is-ms RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-norm-metrics.scm

;;; the vector Taylor polynomial is a vector.

;;; the remainder is a vector.
;;; g o f is a real function when g is a bounded linear functional on m.
;;; KEY commutation 1: g o f inherits the scalar Taylor-differentiability.
(add-to-pss 'gof-taylor-diff
  '(FORALL m (FORALL f (FORALL g (FORALL a (FORALL x (FORALL n
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
       (TAYLOR-DIFFERENTIABLE (COMPOSE g f) a x n)))))))))))
(warrant! 'gof-taylor-diff 'reference
  "A bounded linear functional g is linear and continuous, so it commutes with the
   Caratheodory derivative: if f^(k) is norm-continuous / vector-differentiable
   with factor phi, then (g o f)^(k) = g o f^(k) is continuous / differentiable
   with factor g o phi.  Hence g o f is scalar-Taylor-differentiable to order n.")
(topic! 'gof-taylor-diff 'analysis)

;;; KEY commutation 2: g of the remainder = the scalar remainder of g o f.
(add-to-pss 'g-of-remainder
  `(FORALL m (FORALL f (FORALL g (FORALL a (FORALL x (FORALL n
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (IN a RR) (IMPLIES (IN x RR) (IMPLIES (IN n NN)
       (= (g ,REMV)
          (- ((COMPOSE g f) x) (TAYLOR-POLY (COMPOSE g f) a n x)))))))))))))))
(warrant! 'g-of-remainder 'reference
  "g linear: g(f(x) (-) p) = g(f(x)) - g(p) = (g o f)(x) - g(TAYLOR-POLY-V).  g
   commutes with the finite VADD/ACT sum and with f^(k)(a), so
   g(TAYLOR-POLY-V(f,a,x,n)) = Sum ((x-a)^k/k!) g(f^(k)(a))
   = Sum ((x-a)^k/k!) (g o f)^(k)(a) = TAYLOR-POLY(g o f, a, n, x).")
(topic! 'g-of-remainder 'analysis)

;;; KEY commutation 3: the (n+1)-st derivative of g o f is g of f^(n+1).
(add-to-pss 'gof-nth-deriv
  '(FORALL m (FORALL f (FORALL g (FORALL n (FORALL t
     (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
     (IMPLIES (IN f (FUN RR (VEC m)))
     (IMPLIES (IN n NN) (IMPLIES (IN t RR)
       (= ((NTH-DERIV (COMPOSE g f) (succ n)) t)
          (g ((NTH-DERIV-V m f (succ n)) t)))))))))))))
(warrant! 'gof-nth-deriv 'reference
  "By induction on k using commutation 1's factor identity, (g o f)^(k) = g o f^(k)
   as functions; evaluating the (n+1)-st at t gives (g o f)^(n+1)(t) = g(f^(n+1)(t)).")
(topic! 'gof-nth-deriv 'analysis)

;;; g(v) <= |g(v)| RETIRED 2026-08-17.  `rr-le-abs-self' was declared here, with
;;; add-to-pss and a `well-known' warrant, and was the VERBATIM statement of
;;; `rr-le-abs' -- a support in order-lemmas.scm since long before.  Both are now
;;; PROVEN `modulo 0' as rr-le-abs in theorem-library/rr-abs-basics.scm, from the
;;; definition of abs; the citation below names that theorem.

;;; the elementary clearing step: from an equality and a monotone bound with a
;;; nonnegative multiplier, get the remainder-norm inequality.
;;;   (n+1)! rR = gv * pw,   gv <= nv,   0 <= pw   =>   (n+1)! rR <= nv * pw.
;;; vtaylor-clear RETIRED 2026-09-18: DEGENERATE (binder rR folds onto the class RR); the intended statement is proven as vtaylor-clear in theorem-library/rake-series.scm

;;; g(v) is a real for a bounded linear functional g and a vector v.
;;; blf-app-real RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-hb-leaves.scm

;;; right-monotonicity of multiplication by a nonnegative factor.
;;; rr-mul-le-right RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-hb-leaves.scm

;;; ====================================================================
;;; THEOREM: vector-taylor-remainder-bound
;;;   (n+1)! ||f(x) (-) TAYLOR-POLY-V(f,a,x,n)||  <=  ||f^(n+1)(theta)|| (x-a)^(n+1)
;;; for some theta in (a,x).  The reduction to scalar via a norm-attaining g.
;;; ====================================================================
(sp `(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (AND (IS-NORMED-VECTOR-SPACE m)
               (AND (IS-FINITE-DIMENSIONAL (NORMED-VECTOR-SPACE-AS-MODULE m))
               (AND (IN f (FUN RR (VEC m)))
               (AND (IN a RR) (AND (IN x RR) (AND (IN n NN) (< a x)))))))
     (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
       (FORSOME theta (AND (IN theta RR) (AND (< a theta) (AND (< theta x)
         (<= (* (FACTORIAL (succ n)) ((VNRM m) ,REMV))
             (* ((VNRM m) ((NTH-DERIV-V m f (succ n)) theta))
                (power (- x a) (succ n))))))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))   ; m,f,a,x,n ; ANT1
(dc-split)
(quietly (lambda () (di)))                        ; TAYLOR-DIFFERENTIABLE-V
(define GOAL (dc-gf))

;; R is a vector
;; the guarded vtaylor-remainder-in-vec (2026-09-17) owes DFUN-V(m,f,n): taylor-v-derivs-in-fun supplies it
(quietly (lambda () (fact 'taylor-v-derivs-in-fun 'm 'f 'a 'x 'n)))
(quietly (lambda () (fact 'vtaylor-remainder-in-vec 'm 'f 'a 'x 'n)))

;; norm-attained: g bounded, ||g||<=1, g(R) = ||R||
(define NAANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    '(IS-FINITE-DIMENSIONAL (NORMED-VECTOR-SPACE-AS-MODULE m))
                                    (list 'IN REMV '(VEC m)))))
(cut NAANT) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'norm-attained-by-functional 'm REMV)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-bounded-linear-functional z) (dc-ment? 'vnrm z)))))
(dc-split)
(define G (caddr (dc-find (lambda (z) ((dc-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL) z)))))
(define GOF (list 'COMPOSE G 'f))

;; g o f is a real function, and scalar-Taylor-differentiable
(quietly (lambda () (fact 'gof-in-fun 'm 'f G)))
(quietly (lambda () (fact 'gof-taylor-diff 'm 'f G 'a 'x 'n)))

;; scalar Taylor (Lagrange) on g o f : theta and the cleared equality
(define TLANT (conjuncts->and (list (list 'IN GOF '(FUN RR RR))
                                    '(IN a RR) '(IN x RR) '(IN n NN) '(< a x))))
(cut TLANT) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'taylor-lagrange GOF 'a 'x 'n)))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'taylor-poly z) (dc-ment? 'nth-deriv z)))))
(dc-split)
(define THETA (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'x)))))))))
;; --- names for the endgame ---
(define SF '(FACTORIAL (succ n)))
(define PW '(power (- x a) (succ n)))
(define SR (list '- (list GOF 'x) (list 'TAYLOR-POLY GOF 'a 'n 'x)))
(define NTHGOF (list (list 'NTH-DERIV GOF '(succ n)) THETA))
(define FN1 (list (list 'NTH-DERIV-V 'm 'f '(succ n)) THETA))
(define NR (list (list 'VNRM 'm) REMV))
(define NFN1 (list (list 'VNRM 'm) FN1))
(define GRr (list G REMV))
(define GFN1 (list G FN1))

;; theta in RR ; (succ n) in NN
;; (IN theta RR) came out of the taylor-lagrange existential with the rest of its body.
(quietly (lambda () (fact 'nn-succ-closed 'n)))

;; commutation facts:  g(R) = scalar remainder ;  (g o f)^(n+1)(theta) = g(f^(n+1)(theta))
(quietly (lambda () (fact 'g-of-remainder 'm 'f G 'a 'x 'n)))    ; (= GRr SR)
(quietly (lambda () (fact 'gof-nth-deriv 'm 'f G 'n THETA)))     ; (= NTHGOF GFN1)

;; typings
(quietly (lambda () (fact 'taylor-v-deriv-in-vec 'm 'f 'a 'x 'n THETA)))  ; IN FN1 (VEC m) -- order n+1 at theta in (a,x), from TD-V (2026-09-14)
(quietly (lambda () (fact 'vnrm-real 'm REMV)))                  ; IN NR RR
(quietly (lambda () (fact 'vnrm-real 'm FN1)))                   ; IN NFN1 RR
(quietly (lambda () (fact 'blf-app-real 'm G FN1)))             ; IN GFN1 RR

;; EQ1 :  (n+1)! ||R|| = g(fn1) * pw   -- rewrite the scalar Taylor equality
(quietly (lambda () (fact 'eq-sym GRr NR)))            ; (= NR GRr)  [from gReq (= GRr NR)]
(cut (list '= NR SR))                                  ; ||R|| = SR
(subst (list '= NR GRr)) (quietly (lambda () (ass)))   ; -> (= GRr SR) = g-of-remainder
(dc-focus! GOAL)
(quietly (lambda () (fact 'eq-sym NTHGOF GFN1)))       ; (= GFN1 NTHGOF)  [from gof-nth-deriv]
(cut (list '= (list '* SF NR) (list '* GFN1 PW)))      ; EQ1
(subst (list '= NR SR))                                ; NR -> SR
(subst (list '= GFN1 NTHGOF))                          ; g(fn1) -> (g o f)^(n+1)(theta)
(quietly (lambda () (ass)))                            ; = the taylor-lagrange equality
(dc-focus! GOAL)

;; LE1 :  g(fn1) <= ||fn1||   (norm-bounded-by-functionals + g <= |g|)
(define NBANT (conjuncts->and (list '(IS-NORMED-VECTOR-SPACE m)
                                    (list 'IS-BOUNDED-LINEAR-FUNCTIONAL 'm G)
                                    (list 'IN FN1 '(VEC m))
                                    (list '<= (list 'DUAL-NORM 'm G) 1))))
(cut NBANT) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'norm-bounded-by-functionals 'm G FN1)))  ; (<= (abs GFN1) NFN1)
(quietly (lambda () (fact 'bdd-linfun-abs-real 'm G FN1)))          ; IN (abs GFN1) RR
(quietly (lambda () (fact 'rr-le-abs GFN1)))                   ; (<= GFN1 (abs GFN1))
(quietly (lambda () (fact 'rr-le-trans-c GFN1 (list 'abs GFN1) NFN1)))  ; (<= GFN1 NFN1)

;; pw in RR and 0 <= pw
(quietly (lambda () (fact 'rr-zero-in)))                           ; IN 0 RR
(dc-have! '(IN (- x a) RR) GOAL)                                   ; IN (x-a) RR
(quietly (lambda () (fact 'power-in-rr '(- x a) '(succ n))))       ; IN pw RR
(quietly (lambda () (fact 'rr-lt-diff-pos 'a 'x)))                  ; (< 0 (- x a))
(quietly (lambda () (fact 'rr-power-pos '(- x a) '(succ n))))       ; (< 0 pw)
(quietly (lambda () (fact 'rr-lt-implies-le 0 PW)))                 ; (<= 0 pw)

;; clear :  (n+1)! ||R|| <= ||fn1|| * pw.  Rewrite (n+1)!||R|| = g(fn1)*pw (EQ1),
;; then g(fn1)*pw <= ||fn1||*pw by right-monotonicity (LE1, 0<=pw).
(cut (list '<= (list '* SF NR) (list '* NFN1 PW)))
(subst (list '= (list '* SF NR) (list '* GFN1 PW)))     ; (n+1)!||R|| -> g(fn1)*pw
(quietly (lambda () (fact 'rr-mul-le-right GFN1 NFN1 PW)))   ; g(fn1)*pw <= ||fn1||*pw
(quietly (lambda () (ass)))
(dc-focus! GOAL)

;; witness theta, close the three conjuncts
(ew THETA)
(quietly (lambda () (dc-grind!) (ass-all)))
(qed 'vector-taylor-remainder-bound)
(topic! 'vector-taylor-remainder-bound 'analysis)

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-DIFF-AT-V 'kind 'predicate 'arity 4
           'english "$2 is differentiable at $3 with derivative $4, as a curve in $1")
(notation! 'TAYLOR-DIFFERENTIABLE-V 'kind 'predicate 'arity 5
           'english "$2 is $5 times differentiable from $3 to $4, as a curve in $1")
