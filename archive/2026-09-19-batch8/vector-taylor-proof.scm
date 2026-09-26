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
;;; gof-nth-deriv, g-of-remainder and gof-taylor-diff are PROVEN (guarded) in
;;; the 2026-09-19 block below; the note this comment used to point at, and the
;;; two gaps it named, are superseded there.
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
;;; THE 2026-09-14 NOTE THAT STOOD HERE IS SUPERSEDED (2026-09-19, rake 7-E).
;;; It gave the honest guarded statements of gof-nth-deriv and g-of-remainder
;;; and named two blockers.  Both are gone:
;;;   (G1) "nothing carries a bounded linear functional through the
;;;        Caratheodory derivative" -- now `r8e-blf-diff-commute', PROVEN
;;;        modulo 0 in the 2026-09-19 block below, with the eps/delta
;;;        continuity of g (`r8e-blf-compose-continuous'), (-1).u = -u and
;;;        g(u-v) = g(u)-g(v) as its bricks.
;;;   (G2) "no rule from the definedness of an IOTA to its property" -- STALE
;;;        THE DAY IT WAS WRITTEN: `iota-e' (pi-iota-in-elim!) was added
;;;        2026-09-15.  `r8e-nth-deriv-v-diff' below is the two-line bridge.
;;; The guarded statements actually adopted are the three `-dfun' theorems in
;;; that block, and their guards are weaker than the note predicted: DFUN-V
;;; (totality up to order n), which the citer already holds at :707.
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

;;; ===== BEGIN spliced block (2026-09-19, rake batch 7-E): the three
;;; Taylor-side commutation leaves, PROVEN modulo 0 in their guarded forms.
;;; The original free-standing file is scratchpad/r8e/rake-gof-deriv.scm; it
;;; is spliced because its window is EMPTY (it cites this file's own
;;; definitions and is cited from this file at :723/:750/:751).
;;; =====================================================================

;;; rake-gof-deriv.scm -- rake batch 7-E: a bounded linear functional commutes
;;; with the vector Caratheodory derivative, and the Taylor-side leaves of
;;; theorem-library/vector-taylor-proof.scm that follow from it:
;;;   gof-taylor-diff (:627-632)  PROVEN here, guarded, as gof-taylor-diff-dfun
;;;   g-of-remainder  (:641-647)  PROVEN here, guarded, as g-of-remainder-dfun
;;;   gof-nth-deriv   (:656-662)  PROVEN here, guarded, as gof-nth-deriv-dfun
;;;
;;; ALL THREE LEAVES ARE UNDERDETERMINED AS STATED.  Each is a strict `=' (or a
;;; predicate whose unfold demands a FUN typing) at terms built from DERIV-V,
;;; an IOTA that need not denote, with NO differentiability hypothesis: for
;;; f(t) = |t| . v, a = 0, n = 0 and g /= 0 both sides of gof-nth-deriv are
;;; undefined, and a strict `=' between two undefined terms is FALSE.  It is
;;; the defect vtaylor-poly-in-vec and vtaylor-remainder-in-vec were repaired
;;; for on 2026-09-17, and the repair here is the same: DFUN-V(m,f,n) (plus,
;;; for the pointwise leaf, the IS-DIFF-AT-V that TAYLOR-DIFFERENTIABLE-V
;;; already carries at the interior point).  Every added antecedent is in the
;;; citer's context at vector-taylor-proof.scm:723/750/751 -- DFUN-V(m,f,n) is
;;; landed there at :707 by `taylor-v-derivs-in-fun'.
;;;
;;; WHAT THE ARC NEEDED, and what the note at vector-taylor-proof.scm:367-449
;;; said was missing:
;;;   (G1) "nothing in the tree carries a bounded linear functional through the
;;;        Caratheodory derivative" -- section (6), r8e-blf-diff-commute, with
;;;        its three bricks: (-1).u = -u (2), g(u-v) = g(u)-g(v) (3), and the
;;;        eps/delta continuity of g (6a).  A general three-space
;;;        `compose-continuous-at' is NOT needed and is still absent.
;;;   (G2) "no rule from the definedness of an IOTA to its property" -- STALE:
;;;        `iota-e' (pi-iota-in-elim!) was added 2026-09-15, one day after that
;;;        note was written.  Section (7) is the two-line bridge it makes
;;;        possible, and section (8) the induction (g o f)^(k) = g o f^(k).
;;;
;;; WINDOW.  EMPTY: this file cites NVS-METRIC-SPACE, IS-DIFF-AT-V, DERIV-V,
;;; NTH-DERIV-V and four theorems of vector-taylor-proof.scm (gof-in-fun,
;;; dfun-v-mono, diff-v-value-in-vec, rkt-nvs-vneg-in-vec), all at load
;;; position 486, and is cited from the same file at line 723.  It is a SPLICE
;;; into vector-taylor-proof.scm between line 613 (the end of the 2026-09-17
;;; block) and line 615 (`warranted cores').
;;;
;;; Helper prefix: `r8e-'.

;;; ---- file-local driver helpers ---------------------------------------

(define (r8e-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space '(IS-NORMED-VECTOR-SPACE m))
  (dk-split-all!))

(define (r8e-check! name)
  (if (not (proof-done? *ps*))
      (error "rake-gof-deriv: proof did not close" name (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

;;; `ineq' by FORMULA (rake-hb-leaves.scm's rhb-ineq!): the oracle's indices are
;;; 1-based into the context, which no driver can count after a few `fact's.
(define (r8e-ineq! . r8e-forms)
  (let ((r8e-as (dk-asms)))
    (apply ineq
           (map (lambda (f)
                  (let loop ((l r8e-as) (i 1))
                    (cond ((null? l) (error "r8e-ineq!: not in context" f))
                          ((equal? (car l) f) i)
                          (#t (loop (cdr l) (+ i 1))))))
                r8e-forms))))

;;; unfold IS-BOUNDED-LINEAR-FUNCTIONAL m g down to atoms (destructive)
(define (r8e-blf-split! . r8e-opt)
  (let ((r8e-m (if (pair? r8e-opt) (car r8e-opt) 'm))
        (r8e-g (if (pair? r8e-opt) (cadr r8e-opt) 'g)))
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'IS-BOUNDED-LINEAR-FUNCTIONAL
                                  (list 'IS-BOUNDED-LINEAR-FUNCTIONAL r8e-m r8e-g)))))
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'IS-LINEAR-FUNCTIONAL
                                  (list 'IS-LINEAR-FUNCTIONAL r8e-m r8e-g)))))))

;;; DFUN-V(m,f,n): f^(j) is a TOTAL map RR -> VEC(m) for every j <= n.  The
;;; guard vector-taylor-proof.scm's own spliced theorems carry (rkt-dfun-v
;;; there); repeated here because that helper is file-local.
(define (r8e-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "r8e-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "r8e-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

(define (r8e-dfun-v m f n)
  (list 'FORALL 'j_ (list 'IMPLIES (list 'AND '(IN j_ NN) (list '<= 'j_ n))
                          (list 'IN (list 'NTH-DERIV-V m f 'j_) (list 'FUN 'RR (list 'VEC m))))))

;;; the two laws of IS-LINEAR-FUNCTIONAL, named by what their consequent
;;; MENTIONS.  The IS-DIFF-AT-V factor identity is a FORALL mentioning BOTH
;;; VADD and ACT, so each test excludes the other operation.
(define (r8e-additivity)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'VADD) (not (dk-contains? f 'ACT))))
           "the additivity law of g"))
(define (r8e-homogeneity)
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'ACT) (not (dk-contains? f 'VADD))))
           "the homogeneity law of g"))

(define r8e-lin-hom
  '(FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= (g ((ACT m) r_ x_)) (* r_ (g x_))))))))
(define r8e-lin-add
  '(FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= (g ((VADD m) x_ y_)) (+ (g x_) (g y_))))))))
(define r8e-bnd
  '(FORSOME c_ (AND (IN c_ RR)
               (AND (<= 0 c_)
                    (FORALL x_ (IMPLIES (IN x_ (VEC m))
                      (<= (abs (g x_)) (* c_ ((VNRM m) x_)))))))))

;;; the fully detached beta law of COMPOSE for the inner map F: the FORALL that
;;; mentions COMPOSE and F and no longer carries a FUN typing.
(define (r8e-capply f)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'COMPOSE)
                             (dk-contains? fm f)
                             (not (dk-contains? fm 'FUN))))
           "the COMPOSE beta law"))

;;; =====================================================================
;;; (1) TWO PROJECTIONS OF THE IS-NORMED-VECTOR-SPACE UNFOLD.
;;; theorem-library/nvs-act-laws.scm projects the RIGHT identity law
;;; (nvs-vzero-right); the LEFT one and the inverse law are needed here.
;;; =====================================================================

;; vzero + u = u
(r8e-open!
 '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
    (FORALL u_ (IMPLIES (IN u_ (VEC m))
      (= ((VADD m) (VZERO m) u_) u_))))))
(let* ((law (dk-landed-1
             (lambda () (mac-h 'is-identity '(IS-IDENTITY (VADD m) (VZERO m) (VEC m))))))
       (both (dk-apply! law 'u_)))
  (dk-split! both)
  (ass))
(r8e-check! 'r8e-vzero-left)

;; (-u) + u = vzero
(r8e-open!
 '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
    (FORALL u_ (IMPLIES (IN u_ (VEC m))
      (= ((VADD m) ((VNEG m) u_) u_) (VZERO m)))))))
(let* ((law (dk-landed-1
             (lambda () (mac-h 'has-inverses
                               '(HAS-INVERSES (VADD m) (VZERO m) (VNEG m) (VEC m))))))
       (both (dk-apply! law 'u_)))
  (dk-split! both)
  (ass))
(r8e-check! 'r8e-vneg-inv)

;;; =====================================================================
;;; (2) (-1) . u = -u.   The module fact the Hahn-Banach triage records as
;;; missing ("no NVS/module lemma states ACT(-1,v) = VNEG(v)").  From the
;;; three action laws of nvs-act-laws.scm at the base point y := -u:
;;;   (-u + 1.u) + (-1).u = -u + (1 + -1).u = -u + 0.u = -u
;;; and the left side is (-u + u) + (-1).u = vzero + (-1).u = (-1).u.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
          (= ((ACT m) (- 0 1) u_) ((VNEG m) u_))))))))
(dk-peel!)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 0 1)
(fact 'rkt-nvs-vneg-in-vec 'm 'u_)
(fact 'nvs-act-in-vec 'm '(- 0 1) 'u_)
(fact 'r8e-vzero-left 'm '((ACT m) (- 0 1) u_))
(subst '(= ((ACT m) (- 0 1) u_) ((VADD m) (VZERO m) ((ACT m) (- 0 1) u_))))
(fact 'r8e-vneg-inv 'm 'u_)
(subst '(= (VZERO m) ((VADD m) ((VNEG m) u_) u_)))
(fact 'nvs-act-one 'm 'u_ '((VNEG m) u_))
(subst '(= ((VADD m) ((VNEG m) u_) u_) ((VADD m) ((VNEG m) u_) ((ACT m) 1 u_))))
(fact 'nvs-act-collect 'm 1 '(- 0 1) 'u_ '((VNEG m) u_))
(subst '(= ((VADD m) ((VADD m) ((VNEG m) u_) ((ACT m) 1 u_)) ((ACT m) (- 0 1) u_))
           ((VADD m) ((VNEG m) u_) ((ACT m) (+ 1 (- 0 1)) u_))))
(have! '(= (+ 1 (- 0 1)) 0) (lambda () (arith)))
(subst '(= (+ 1 (- 0 1)) 0))
(fact 'nvs-act-zero 'm 'u_ '((VNEG m) u_))
(ass)
(r8e-check! 'r8e-act-neg-one)

;;; =====================================================================
;;; (3) g(-u) = -g(u)  and  g(u + (-v)) = g(u) - g(v), for a bounded linear g.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL g (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
          (= (g ((VNEG m) u_)) (- 0 (g u_)))))))))))
(dk-peel!)
(fact 'r8e-act-neg-one 'm 'u_)
(r8e-blf-split!)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR 'u_)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 0 1)
(subst '(= ((VNEG m) u_) ((ACT m) (- 0 1) u_)))
(subst (dk-apply! (r8e-homogeneity) '(- 0 1) 'u_))
(crs)
(r8e-check! 'r8e-blf-vneg)

(sp (make-wff
     '(FORALL m (FORALL g (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
        (FORALL v_ (IMPLIES (IN v_ (VEC m))
          (= (g ((VADD m) u_ ((VNEG m) v_))) (- (g u_) (g v_)))))))))))))
(dk-peel!)
(fact 'r8e-blf-vneg 'm 'g 'v_)
(fact 'rkt-nvs-vneg-in-vec 'm 'v_)
(r8e-blf-split!)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR 'u_)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR 'v_)
(subst (dk-apply! (r8e-additivity) 'u_ '((VNEG m) v_)))
(subst '(= (g ((VNEG m) v_)) (- 0 (g v_))))
(crs)
(r8e-check! 'r8e-blf-sub)

;;; =====================================================================
;;; (4) the distance of NVS-METRIC-SPACE, read off.  NVS-METRIC-SPACE is a
;;; def-functoid LIST, so `slot' has no projection for it: unfold, slot,
;;; nth-r -- nvs-ms-pts' recipe (vector-taylor-proof.scm:196) one storey
;;; down -- then beta at the pair.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
        (FORALL v_ (IMPLIES (IN v_ (VEC m))
          (== ((DIST (NVS-METRIC-SPACE m)) u_ v_)
              ((VNRM m) ((VADD m) u_ ((VNEG m) v_))))))))))))
(dk-peel!)
(fact 'pair-in-cartesian '(VEC m) '(VEC m) 'u_ 'v_)
(mac 'NVS-METRIC-SPACE)
(slot 'DIST)
(nth-r)
(lam-b)
(qrfl)
(r8e-check! 'r8e-nvs-dist)

;;; =====================================================================
;;; (5) THE EPSILON/(c+1) STEP, as a lemma: for c >= 0 and eps > 0 there is a
;;; positive d with c*z <= eps for every z <= d.  This is the arithmetic every
;;; "a bounded linear map is continuous" proof needs, and the tree has it
;;; nowhere (rr-pos-halvable is the c = 2 case of the same shape).
;;; =====================================================================
(define r8e-K '(+ 1 c_))
(define r8e-R '(recip (+ 1 c_)))
(define r8e-D '(* e_ (recip (+ 1 c_))))

(sp (make-wff
     '(FORALL c_ (IMPLIES (IN c_ RR) (IMPLIES (<= 0 c_)
        (FORALL e_ (IMPLIES (POS-RR e_)
          (FORSOME d_ (AND (POS-RR d_)
            (FORALL z_ (IMPLIES (IN z_ RR) (IMPLIES (<= z_ d_)
              (<= (* c_ z_) e_)))))))))))))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'e_)
(fact 'rr-lt-of-pos-rr 'e_)
(fact 'rr-one-in)
(have! (list 'AND '(IN 1 RR) '(IN c_ RR)))
(fact 'rr-add-closed 1 'c_)
(fact 'rr-one-plus-nonneg-pos 'c_)
(fact 'rr-pos-ne-zero r8e-K)
(have! (list 'AND (list 'IN r8e-K 'RR) (list 'NOT (list '= r8e-K 0))))
(fact 'rr-recip-closed r8e-K)
(fact 'rr-recip-inverse r8e-K)
(fact 'rr-recip-pos r8e-K)
(have! (list 'AND '(IN e_ RR) (list 'IN r8e-R 'RR)))
(fact 'rr-mul-closed 'e_ r8e-R)
(fact 'rr-mul-pos 'e_ r8e-R)
(mac-h '< (list '< 0 r8e-D))
(dk-split! (list 'AND (list '<= 0 r8e-D) (list 'NOT (list '= 0 r8e-D))))
(have! (list '<= 'c_ r8e-K) (lambda () (r8e-ineq! '(IN c_ RR))))
;; (1+c).(e.recip(1+c)) = e -- a ring identity in e and the opaque recip, then
;; the reciprocal law.
(have! (list '= (list '* r8e-K r8e-D) 'e_)
       (lambda ()
         (have! (list '= (list '* r8e-K r8e-D) (list '* 'e_ (list '* r8e-K r8e-R)))
                (lambda () (crs)))
         (subst (list '= (list '* r8e-K r8e-D) (list '* 'e_ (list '* r8e-K r8e-R))))
         (subst (list '= (list '* r8e-K r8e-R) 1))
         (crs)))
(ew r8e-D)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'POS-RR)
       (begin (mac 'pos-rr) (from-context!))
       (begin
         ;; dk-peel!, not di: the guarded binder and the `z <= d' antecedent are
         ;; two di's, and the eigenvariable is read off the GOAL (* c_ z_) <= e_
         (dk-peel!)
         (let ((r8e-z (caddr (cadr (dk-goal)))))
           (have! (list 'AND (list 'IN r8e-z 'RR) '(IN c_ RR)))
           (fact 'rr-mul-closed r8e-z 'c_)
           (have! (list 'AND (list 'IN r8e-D 'RR) '(IN c_ RR)))
           (fact 'rr-mul-closed r8e-D 'c_)
           (have! (list 'AND '(IN c_ RR) (list 'IN r8e-D 'RR)))
           (fact 'rr-mul-closed 'c_ r8e-D)
           (have! (list 'AND (list 'IN r8e-K 'RR) (list 'IN r8e-D 'RR)))
           (fact 'rr-mul-closed r8e-K r8e-D)
           ;; c.z = z.c, so the monotone step can put the multiplier on the right
           (have! (list '= (list '* 'c_ r8e-z) (list '* r8e-z 'c_)) (lambda () (crs)))
           (subst (list '= (list '* 'c_ r8e-z) (list '* r8e-z 'c_)))
           (fact 'rr-mul-le-right r8e-z r8e-D 'c_)
           (have! (list '<= (list '* r8e-D 'c_) 'e_)
                  (lambda ()
                    (have! (list '= (list '* r8e-D 'c_) (list '* 'c_ r8e-D))
                           (lambda () (crs)))
                    (subst (list '= (list '* r8e-D 'c_) (list '* 'c_ r8e-D)))
                    (fact 'rr-mul-le-right 'c_ r8e-K r8e-D)
                    (have! (list '<= (list '* r8e-K r8e-D) 'e_)
                           (lambda ()
                             (subst (list '= (list '* r8e-K r8e-D) 'e_))
                             (fact 'rr-leq-reflexive 'e_)
                             (ass)))
                    (fact 'rr-le-trans-c (list '* 'c_ r8e-D) (list '* r8e-K r8e-D) 'e_)
                    (ass)))
           (fact 'rr-le-trans-c (list '* r8e-z 'c_) (list '* r8e-D 'c_) 'e_)
           (ass))))))
(r8e-check! 'r8e-eps-over)

;;; =====================================================================
;;; (6a) A BOUNDED LINEAR FUNCTIONAL CARRIES CONTINUITY INTO THE REALS:
;;;      h continuous at t into the NORM metric  =>  g o h continuous at t.
;;; The one analytic step of the arc.  Given eps, r8e-eps-over turns the bound
;;; c into a tolerance d on the norm, h's own continuity supplies a delta for
;;; d, and |g(h t) - g(h b)| = |g(h t - h b)| <= c*||h t - h b|| =
;;; c*dist(h t, h b) <= eps.  The tree's `compose-continuous-at' is stated at
;;; RR-MS/RR-MS only, so no composition theorem applies here.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL g (FORALL h (FORALL t
        (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (IMPLIES (IN h (FUN RR (VEC m)))
        (IMPLIES (IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) h t)
          (IS-CONTINUOUS-AT RR-MS RR-MS (COMPOSE g h) t)))))))))))
(dk-peel!)
(have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
(have! r8e-bnd                   (lambda () (r8e-blf-split!) (ass)))
(have! '(== RR (PTS RR-MS)) (lambda () (slot 'PTS) (qrfl)))
(let* ((r8e-hv 'h)
       (r8e-gh '(COMPOSE g h))
       (r8e-cv (dk-skolem! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                     (dk-contains? f 'VNRM)))
                                    "the boundedness existential")))
       (r8e-bound (lambda () (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'VNRM)
                                                       (dk-contains? f 'abs)))
                                      "the bound universal"))))
  (dk-split-all!
   (dk-landed (lambda () (mac-h 'is-continuous-at
                                '(IS-CONTINUOUS-AT RR-MS (NVS-METRIC-SPACE m) h t)))))
  (fact 'rr-is-set)
  (fact 'gof-in-fun 'm 'h 'g)
  (have! '(IN t RR) (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
  (fact 'fun-apply-type-c 'h 'RR '(VEC m) 't)
  (have! (list 'AND (list 'IN 'h '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g 'h)
     (mac 'is-continuous-at)
     (dk-conj-close!
      (lambda ()
        (let ((r8e-g3 (dk-goal)))
          (cond
           ((eq? (car r8e-g3) 'IS-METRIC-SPACE) (ass))
           ((eq? (car r8e-g3) 'IN) (subst '(== (PTS RR-MS) RR)) (ass))
           (#t                                   ; the eps universal
            (dk-peel!)
            (let* ((r8e-eps (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)))
                                           "the eps typing")))
                   (r8e-dd (begin
                             (fact 'r8e-eps-over r8e-cv r8e-eps)
                             (dk-skolem!
                              (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                        (not (dk-contains? f 'DIST))))
                                       "the eps-over witness"))))
                   (r8e-epsu (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'POS-RR)
                                                       (dk-contains? f 'DIST)))
                                      "phi's eps universal"))
                   (r8e-del (begin
                              (dk-apply! r8e-epsu r8e-dd)
                              (dk-skolem!
                               (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                         (dk-contains? f 'DIST)))
                                        "phi's delta")))))
              (ew r8e-del)
              (dk-conj-close!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'POS-RR)
                     (ass)
                     (begin
                       (dk-peel!)
                       (let* ((r8e-b (cadr (caddr (cadr (dk-goal)))))
                              (r8e-w (list '(VADD m) (list r8e-hv 't)
                                           (list '(VNEG m) (list r8e-hv r8e-b)))))
                         (have! (list 'IN r8e-b 'RR)
                                (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
                         (fact 'fun-apply-type-c r8e-hv 'RR '(VEC m) r8e-b)
                         (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hv 't))
                         (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hv r8e-b))
                         (fact 'rkt-nvs-vneg-in-vec 'm (list r8e-hv r8e-b))
                         (fact 'nvs-vadd-in-vec 'm (list r8e-hv 't)
                               (list '(VNEG m) (list r8e-hv r8e-b)))
                         (fact 'vnrm-real 'm r8e-w)
                         ;; the two composite values
                         (let ((r8e-cva (r8e-capply r8e-hv)))
                           (dk-apply! r8e-cva 't)
                           (dk-apply! r8e-cva r8e-b))
                         (subst (list '= (list r8e-gh 't) (list 'g (list r8e-hv 't))))
                         (subst (list '= (list r8e-gh r8e-b) (list 'g (list r8e-hv r8e-b))))
                         ;; dist on RR is abs of the difference
                         (fact 'rr-ms-dist (list 'g (list r8e-hv 't))
                               (list 'g (list r8e-hv r8e-b)))
                         (subst (list '== (list '(DIST RR-MS)
                                                (list 'g (list r8e-hv 't))
                                                (list 'g (list r8e-hv r8e-b)))
                                      (list 'abs (list '- (list 'g (list r8e-hv 't))
                                                       (list 'g (list r8e-hv r8e-b))))))
                         ;; g(u) - g(v) = g(u - v)
                         (fact 'r8e-blf-sub 'm 'g (list r8e-hv 't) (list r8e-hv r8e-b))
                         (subst (list '= (list '- (list 'g (list r8e-hv 't))
                                               (list 'g (list r8e-hv r8e-b)))
                                      (list 'g r8e-w)))
                         ;; |g(w)| <= c ||w||,  ||w|| = dist(phi t, phi b) <= dd
                         (dk-apply! (r8e-bound) r8e-w)
                         (fact 'r8e-nvs-dist 'm (list r8e-hv 't) (list r8e-hv r8e-b))
                         ;; phi's delta universal AT b: dist(phi t, phi b) <= dd
                         (dk-apply! (dk-pick (lambda (f)
                                               (and (pair? f) (eq? (car f) 'FORALL)
                                                    (dk-contains? f 'DIST)
                                                    (dk-contains? f r8e-del)))
                                             "phi's delta universal")
                                    r8e-b)
                         (have! (list '<= (list '(VNRM m) r8e-w) r8e-dd)
                                (lambda ()
                                  (subst (list '== (list '(VNRM m) r8e-w)
                                               (list '(DIST (NVS-METRIC-SPACE m))
                                                     (list r8e-hv 't) (list r8e-hv r8e-b))))
                                  (ass)))
                         (dk-apply! (dk-pick (lambda (f)
                                               (and (pair? f) (eq? (car f) 'FORALL)
                                                    (dk-contains? f r8e-dd)
                                                    (not (dk-contains? f 'DIST))))
                                             "the eps-over universal")
                                    (list '(VNRM m) r8e-w))
                         ;; |g(w)| <= c ||w|| <= eps
                         (fact 'fun-apply-type-c 'g '(VEC m) 'RR r8e-w)
                         (fact 'rr-abs-closed (list 'g r8e-w))
                         (have! (list 'AND (list 'IN r8e-cv 'RR)
                                      (list 'IN (list '(VNRM m) r8e-w) 'RR)))
                         (fact 'rr-mul-closed r8e-cv (list '(VNRM m) r8e-w))
                         (fact 'rr-pos-rr-in-rr r8e-eps)
                         (fact 'rr-le-trans-c (list 'abs (list 'g r8e-w))
                               (list '* r8e-cv (list '(VNRM m) r8e-w)) r8e-eps)
                         (ass)))))))))))))
(r8e-check! 'r8e-blf-compose-continuous)

;;; =====================================================================
;;; (6) THE STEP LEMMA (the Hahn-Banach triage's gap (G1)): a bounded linear
;;; functional carries the vector Caratheodory derivative to the scalar one.
;;;
;;;   is-blf(m,g),  IS-DIFF-AT-V(m,h,t,L)   =>   IS-DIFF-AT(g o h, t, g(L))
;;;
;;; The factor is g o phi: its value at t is g(L); the identity is linearity
;;; twice (r8e-blf-sub on the left, homogeneity on the right); and its
;;; continuity at t is the ONE analytic step -- given eps, r8e-eps-over turns
;;; the bound c into a tolerance d on the norm, phi's own continuity supplies a
;;; delta for d, and |g(phi t) - g(phi b)| = |g(phi t - phi b)| <= c*||phi t -
;;; phi b|| = c*dist(phi t, phi b) <= eps.  No general three-space
;;; `compose-continuous-at' is needed (the tree's is RR-MS/RR-MS only).
;;;
;;; TWO DRIVER POINTS.
;;; * IS-BOUNDED-LINEAR-FUNCTIONAL is opened in have! LANES, not in the main
;;;   branch: `mac-h' is destructive and `gof-in-fun' / `r8e-blf-sub' are cited
;;;   below with the hypothesis itself as their antecedent.
;;; * the three hard conjuncts of the goal are proved as LANES before the
;;;   unfold, so the assembly after `ew' is four `ass'es.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL g (FORALL h (FORALL t (FORALL bl
        (IMPLIES (IS-BOUNDED-LINEAR-FUNCTIONAL m g)
        (IMPLIES (IS-DIFF-AT-V m h t bl)
          (IS-DIFF-AT (COMPOSE g h) t (g bl)))))))))))
(dk-peel!)
(have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
(have! r8e-lin-hom               (lambda () (r8e-blf-split!) (ass)))
(have! r8e-bnd                   (lambda () (r8e-blf-split!) (ass)))
(dk-split-all!
 (dk-landed (lambda () (mac-h 'IS-DIFF-AT-V '(IS-DIFF-AT-V m h t bl)))))
(have! '(== RR (PTS RR-MS)) (lambda () (slot 'PTS) (qrfl)))

(let* ((r8e-c   (dk-skolem! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                      (dk-contains? f 'VNRM)))
                                     "the boundedness existential")))
       (r8e-phi (dk-skolem! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                      (dk-contains? f 'IS-CONTINUOUS-AT)))
                                     "the Caratheodory factor")))
       (r8e-gph (list 'COMPOSE 'g r8e-phi))
       (r8e-gh  '(COMPOSE g h))
       ;; the bound at a vector:  abs(g w) <= c * ||w||
       (r8e-bound (lambda () (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'VNRM)
                                                       (dk-contains? f 'abs)))
                                      "the bound universal")))
       ;; the Caratheodory identity: the FORALL mentioning BOTH VADD and ACT
       (r8e-ident (lambda () (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                       (dk-contains? f 'VADD)
                                                       (dk-contains? f 'ACT)))
                                      "the Caratheodory identity"))))
  (dk-split-all!)
  ;; phi's continuity is NOT unfolded here: (6a) is cited with it whole.
  ;; typings and the two beta laws, landed once for the whole proof
  (fact 'rr-is-set)
  (fact 'gof-in-fun 'm 'h 'g)
  (fact 'gof-in-fun 'm r8e-phi 'g)
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR 'bl)
  (fact 'fun-apply-type-c 'h 'RR '(VEC m) 't)
  (fact 'fun-apply-type-c r8e-phi 'RR '(VEC m) 't)
  (have! (list 'AND (list 'IN 'h '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g 'h)
  (have! (list 'AND (list 'IN r8e-phi '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g r8e-phi)

  ;; ---- LANE 1: g o phi is continuous at t (section 6a) ----------------
  (have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS r8e-gph 't)
         (lambda ()
           (fact 'r8e-blf-compose-continuous 'm 'g r8e-phi 't)
           (ass)))

  ;; ---- LANE 2: (g o phi)(t) = g(L) ------------------------------------
  (have! (list '= (list r8e-gph 't) '(g bl))
   (lambda ()
     (dk-apply! (r8e-capply r8e-phi) 't)
     (subst (list '= (list r8e-gph 't) (list 'g (list r8e-phi 't))))
     (subst (list '= (list r8e-phi 't) 'bl))
     (rfl)))

  ;; ---- LANE 3: the Caratheodory identity for g o h ---------------------
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
           (list '= (list '- (list r8e-gh 'x_) (list r8e-gh 't))
                 (list '* (list r8e-gph 'x_) (list '- 'x_ 't)))))
   (lambda ()
     (dk-peel!)
     (let ((r8e-x (cadr (cadr (cadr (dk-goal))))))
       (fact 'fun-apply-type-c 'h 'RR '(VEC m) r8e-x)
       (fact 'fun-apply-type-c r8e-phi 'RR '(VEC m) r8e-x)
       (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list 'h r8e-x))
       (fact 'fun-apply-type-c 'g '(VEC m) 'RR '(h t))
       (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-phi r8e-x))
       (fact 'rr-sub-in-rr r8e-x 't)
       (let ((r8e-cah (r8e-capply 'h))
             (r8e-cap (r8e-capply r8e-phi)))
         (dk-apply! r8e-cah r8e-x)
         (dk-apply! r8e-cah 't)
         (dk-apply! r8e-cap r8e-x))
       (subst (list '= (list r8e-gh r8e-x) (list 'g (list 'h r8e-x))))
       (subst (list '= (list r8e-gh 't) '(g (h t))))
       (subst (list '= (list r8e-gph r8e-x) (list 'g (list r8e-phi r8e-x))))
       (fact 'r8e-blf-sub 'm 'g (list 'h r8e-x) '(h t))
       (subst (list '= (list '- (list 'g (list 'h r8e-x)) '(g (h t)))
                    (list 'g (list '(VADD m) (list 'h r8e-x) '((VNEG m) (h t))))))
       (subst (dk-apply! (r8e-ident) r8e-x))
       (subst (dk-apply! (r8e-homogeneity) (list '- r8e-x 't) (list r8e-phi r8e-x)))
       (crs))))

  ;; ---- the assembly ---------------------------------------------------
  (mac 'IS-DIFF-AT)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'FORSOME)
         (begin (ew r8e-gph) (dk-conj-close! (lambda () (ass))))
         (ass)))))
(r8e-check! 'r8e-blf-diff-commute)

;;; =====================================================================
;;; (7) FROM TOTALITY TO DIFFERENTIABILITY -- what closes the triage's gap
;;; (G2).  f^(j) and f^(j+1) total means DERIV-V(m, f^(j), x) DENOTES at every
;;; real x, and `iota-e' (pi-iota-in-elim!, ADDED 2026-09-15, one day after the
;;; note at vector-taylor-proof.scm:410 declared the principle missing) turns
;;; that into the defining property.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL f (FORALL j_ (FORALL x_
        (IMPLIES (IN j_ NN) (IMPLIES (IN x_ RR)
        (IMPLIES (IN (NTH-DERIV-V m f j_) (FUN RR (VEC m)))
        (IMPLIES (IN (NTH-DERIV-V m f (succ j_)) (FUN RR (VEC m)))
          (IS-DIFF-AT-V m (NTH-DERIV-V m f j_) x_
                        ((NTH-DERIV-V m f (succ j_)) x_))))))))))))
(dk-peel!)
(let* ((r8e-hj '(NTH-DERIV-V m f j_))
       (r8e-hs '(NTH-DERIV-V m f (succ j_)))
       (r8e-dv (list 'DERIV-V 'm r8e-hj 'x_))
       (r8e-io (list 'IOTA 'L (list 'IS-DIFF-AT-V 'm r8e-hj 'x_ 'L))))
  (fact 'fun-apply-type-c r8e-hs 'RR '(VEC m) 'x_)
  (have! (list '== (list r8e-hs 'x_) r8e-dv)
         (lambda () (mac 'nth-deriv-v-succ) (lam-b) (qrfl)))
  (have! (list '== r8e-dv r8e-io) (lambda () (mac 'DERIV-V) (qrfl)))
  (have! (list 'IN r8e-io '(VEC m))
         (lambda ()
           (subst (list '== r8e-io r8e-dv))
           (subst (list '== r8e-dv (list r8e-hs 'x_)))
           (ass)))
  (iota-e r8e-io)
  (subst (list '== (list r8e-hs 'x_) r8e-dv))
  (subst (list '== r8e-dv r8e-io))
  (ass))
(r8e-check! 'r8e-nth-deriv-v-diff)

;;; =====================================================================
;;; (8) THE COMMUTATION, as an identity of FUNCTIONS, by induction on k:
;;;        (g o f)^(k)  =  g o f^(k)
;;; The induction variable is OUTERMOST (`ni' tests the literal shape).  The
;;; step is: the IH rewrites (g o f)^(k) to g o f^(k) under the recursion
;;; axiom, (7) + (6) + `deriv-of-is-diff-at' compute its derivative at every
;;; point as g(f^(k+1)(x)), and `fun-domain-extensionality' closes.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
       (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g
         (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
         (list 'IMPLIES '(IN f (FUN RR (VEC m)))
         (list 'IMPLIES (r8e-dfun-v 'm 'f 'k)
           '(= (NTH-DERIV (COMPOSE g f) k)
               (COMPOSE g (NTH-DERIV-V m f k)))))))))))))
(let* ((r8e-lv (dk-opened (lambda () (ni))))
       (r8e-base (r8e-leaf r8e-lv (lambda (g) (not (dk-contains? g 'succ))) "the base"))
       (r8e-step (r8e-leaf r8e-lv (lambda (g) (dk-contains? g 'succ)) "the step")))
  ;; ---- base: (g o f)^(0) = g o f ------------------------------------
  (dk-focus! r8e-base)
  (dk-peel!)
  (fact 'gof-in-fun 'm 'f 'g)
  (mac 'nth-deriv-zero)
  (mac 'nth-deriv-v-zero)
  (rfl)
  ;; ---- step ---------------------------------------------------------
  (dk-focus! r8e-step)
  (dk-peel!)
  (let* ((r8e-gl  (dk-goal))
         (r8e-lhs (cadr r8e-gl))
         (r8e-rhs (caddr r8e-gl))
         (r8e-gof (cadr r8e-lhs))
         (r8e-g   (cadr r8e-gof))
         (r8e-f   (caddr r8e-gof))
         (r8e-sk  (caddr r8e-lhs))
         (r8e-k   (cadr r8e-sk))
         (r8e-hs  (caddr r8e-rhs))
         (r8e-m   (cadr r8e-hs))
         (r8e-hk  (list 'NTH-DERIV-V r8e-m r8e-f r8e-k))
         (r8e-ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                            (dk-contains? f 'NTH-DERIV)))
                           "the induction hypothesis"))
         (r8e-df  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                            (dk-contains? f 'NTH-DERIV-V)
                                            (dk-contains? f 'FUN)))
                           "DFUN-V(m,f,succ k)")))
    (fact 'nn-succ-closed r8e-k)
    (fact 'nn-le-succ r8e-k)
    (fact 'nn-le-refl r8e-sk)
    ;; the two typings out of DFUN-V(m,f,succ k)
    (have! (list 'AND (list 'IN r8e-k 'NN) (list '<= r8e-k r8e-sk)))
    (dk-apply! r8e-df r8e-k)
    (have! (list 'AND (list 'IN r8e-sk 'NN) (list '<= r8e-sk r8e-sk)))
    (dk-apply! r8e-df r8e-sk)
    ;; the induction hypothesis, at DFUN-V(m,f,k)
    (fact 'dfun-v-mono r8e-m r8e-f r8e-sk r8e-k)
    (let* ((r8e-ek (dk-apply! r8e-ih r8e-m r8e-f r8e-g))
           (r8e-p3 (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                     (list '= (list 'DERIV (list 'COMPOSE r8e-g r8e-hk) 'x_)
                           (list r8e-g (list r8e-hs 'x_)))))))
      (have! (list 'IN r8e-g (list 'FUN (list 'VEC r8e-m) 'RR))
             (lambda () (r8e-blf-split! r8e-m r8e-g) (ass)))
      (fact 'gof-in-fun r8e-m r8e-hs r8e-g)
      (fact 'gof-in-fun r8e-m r8e-hk r8e-g)
      ;; the derivative of g o f^(k) at every point
      (have! r8e-p3
       (lambda ()
         (dk-peel!)
         (let ((r8e-x (caddr (cadr (dk-goal)))))
           (fact 'fun-apply-type-c r8e-hs 'RR (list 'VEC r8e-m) r8e-x)
           (fact 'fun-apply-type-c r8e-g (list 'VEC r8e-m) 'RR (list r8e-hs r8e-x))
           (fact 'r8e-nth-deriv-v-diff r8e-m r8e-f r8e-k r8e-x)
           (fact 'r8e-blf-diff-commute r8e-m r8e-g r8e-hk r8e-x (list r8e-hs r8e-x))
           (fact 'deriv-of-is-diff-at (list 'COMPOSE r8e-g r8e-hk) r8e-x
                 (list r8e-g (list r8e-hs r8e-x)))
           (ass))))
      ;; (g o f)^(succ k) is a total real function
      (have! (list 'IN r8e-lhs '(FUN RR RR))
       (lambda ()
         (mac 'nth-deriv-succ)
         (for-each
          (lambda (r8e-lf)
            (dk-focus! r8e-lf)
            (if (eq? (car (dk-goal)) 'IN)
                (begin (fact 'rr-is-set) (ass))
                (begin
                  (dk-peel!)
                  (let ((r8e-x (caddr (cadr (dk-goal)))))
                    (dk-apply! r8e-p3 r8e-x)
                    (subst r8e-ek)
                    (subst (list '= (list 'DERIV (list 'COMPOSE r8e-g r8e-hk) r8e-x)
                                 (list r8e-g (list r8e-hs r8e-x))))
                    (fact 'fun-apply-type-c r8e-hs 'RR (list 'VEC r8e-m) r8e-x)
                    (fact 'fun-apply-type-c r8e-g (list 'VEC r8e-m) 'RR
                          (list r8e-hs r8e-x))
                    (ass)))))
          (dk-opened (lambda () (lam-t))))))
      ;; both sides are members of FUN(RR), and agree pointwise
      (have! (list 'IN r8e-lhs '(FUN RR))
             (lambda ()
               (dk-split-all!
                (dk-landed (lambda () (mac-h 'fun-codomain-iff
                                             (list 'IN r8e-lhs '(FUN RR RR))))))
               (ass)))
      (have! (list 'IN r8e-rhs '(FUN RR))
             (lambda ()
               (dk-split-all!
                (dk-landed (lambda () (mac-h 'fun-codomain-iff
                                             (list 'IN r8e-rhs '(FUN RR RR))))))
               (ass)))
      (have! (list 'AND (list 'IN r8e-hs (list 'FUN 'RR (list 'VEC r8e-m)))
                   (list 'IN r8e-g (list 'FUN (list 'VEC r8e-m) 'RR))))
      (fact 'compose-apply 'RR (list 'VEC r8e-m) 'RR r8e-g r8e-hs)
      (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                (list '= (list r8e-lhs 'x_) (list r8e-rhs 'x_))))
       (lambda ()
         (dk-peel!)
         (let ((r8e-x (cadr (cadr (dk-goal)))))
           (fact 'fun-apply-type-c r8e-hs 'RR (list 'VEC r8e-m) r8e-x)
           (fact 'fun-apply-type-c r8e-g (list 'VEC r8e-m) 'RR (list r8e-hs r8e-x))
           (dk-apply! r8e-p3 r8e-x)
           (dk-apply! (r8e-capply r8e-hs) r8e-x)
           (mac 'nth-deriv-succ)
           (lam-b)
           (subst r8e-ek)
           (subst (list '= (list 'DERIV (list 'COMPOSE r8e-g r8e-hk) r8e-x)
                        (list r8e-g (list r8e-hs r8e-x))))
           (subst (list '= (list r8e-rhs r8e-x) (list r8e-g (list r8e-hs r8e-x))))
           (rfl))))
      (fact 'fun-domain-extensionality 'RR r8e-lhs r8e-rhs)
      (ass))))
(r8e-check! 'r8e-gof-nth-deriv-fn)

;;; =====================================================================
;;; (9) THE LEAF `gof-nth-deriv', GUARDED.  Binders m f g n t and the body are
;;; the support's (vector-taylor-proof.scm:656-662) unchanged.  The two added
;;; antecedents are exactly what the note at vector-taylor-proof.scm:370
;;; predicted, and BOTH are in the citer's context at :751:
;;;   DFUN-V(m,f,n)      -- taylor-v-derivs-in-fun, already cited at :707;
;;;   IS-DIFF-AT-V(m, f^(n), t, f^(n+1)(t))
;;;                      -- the second conjunct of TAYLOR-DIFFERENTIABLE-V at
;;;                         (n, theta), theta being interior.
;;; Without them f^(n+1)(t) is an IOTA with no satisfier and the support's
;;; strict `=' is FALSE (both sides undefined).
;;;
;;; NOTE the order of the last two steps: `nth-deriv-succ' and `lam-b' FIRST,
;;; so that (g o f)^(n+1)(t) becomes DERIV((g o f)^(n), t) and the commutation
;;; (8) is needed only at n.  f^(n+1) is NOT assumed total -- which matters,
;;; because TAYLOR-DIFFERENTIABLE-V does not make it so.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'n (list 'FORALL 't
       (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
       (list 'IMPLIES '(IN f (FUN RR (VEC m)))
       (list 'IMPLIES '(IN n NN)
       (list 'IMPLIES '(IN t RR)
       (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
       (list 'IMPLIES '(IS-DIFF-AT-V m (NTH-DERIV-V m f n)
                                     t ((NTH-DERIV-V m f (succ n)) t))
         '(= ((NTH-DERIV (COMPOSE g f) (succ n)) t)
             (g ((NTH-DERIV-V m f (succ n)) t))))))))))))))))
(dk-peel!)
(let* ((r8e-hn '(NTH-DERIV-V m f n))
       (r8e-hs '(NTH-DERIV-V m f (succ n)))
       (r8e-gh (list 'COMPOSE 'g r8e-hn)))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (fact 'diff-v-value-in-vec 'm r8e-hn 't (list r8e-hs 't))
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hs 't))
  (fact 'r8e-blf-diff-commute 'm 'g r8e-hn 't (list r8e-hs 't))
  (fact 'deriv-of-is-diff-at r8e-gh 't (list 'g (list r8e-hs 't)))
  (fact 'r8e-gof-nth-deriv-fn 'n 'm 'f 'g)
  (mac 'nth-deriv-succ)
  (lam-b)
  (subst (list '= '(NTH-DERIV (COMPOSE g f) n) r8e-gh))
  (subst (list '= (list 'DERIV r8e-gh 't) (list 'g (list r8e-hs 't))))
  (rfl))
(r8e-check! 'gof-nth-deriv-dfun)
(alias! 'gof-nth-deriv-dfun
        "a bounded linear functional commutes with the (n+1)-st vector derivative")

;;; =====================================================================
;;; (10) THE LEAF `gof-taylor-diff', GUARDED.  Binders m f g a x n and the body
;;; are the support's (vector-taylor-proof.scm:627-632); the added antecedents
;;; are IS-NORMED-VECTOR-SPACE(m) (TAYLOR-DIFFERENTIABLE-V does not carry it,
;;; and the linearity bricks need it), (IN n NN), and DFUN-V(m,f,n) -- which
;;; `taylor-v-derivs-in-fun' gives the citer at :707.
;;;
;;; Each conjunct is (8) at k <= n rewriting (g o f)^(k) to g o f^(k), and then:
;;; the continuity conjunct is (6a) at f^(k); the differentiability conjunct is
;;; `nth-deriv-succ' + `lam-b' + the step lemma (6) at the IS-DIFF-AT-V the
;;; hypothesis already carries, so f^(k+1) is never assumed total.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'a
       (list 'FORALL 'x (list 'FORALL 'n
         (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
         (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
         (list 'IMPLIES '(IN f (FUN RR (VEC m)))
         (list 'IMPLIES '(IN n NN)
         (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE-V m f a x n)
         (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
           '(TAYLOR-DIFFERENTIABLE (COMPOSE g f) a x n)))))))))))))))
(dk-peel!)
(dk-split-all!
 (dk-landed (lambda () (mac-h 'taylor-differentiable-v
                              '(TAYLOR-DIFFERENTIABLE-V m f a x n)))))
(let* ((r8e-cont (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f 'IS-CONTINUOUS-AT)))
                          "the continuity conjunct of TD-V"))
       (r8e-diff (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f 'IS-DIFF-AT-V)))
                          "the differentiability conjunct of TD-V"))
       (r8e-df   (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f 'NTH-DERIV-V)
                                           (dk-contains? f 'FUN)))
                          "DFUN-V(m,f,n)")))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (mac 'TAYLOR-DIFFERENTIABLE)
  (dk-conj-close!
   (lambda ()
     (let ((r8e-cc (dk-contains? (dk-goal) 'IS-CONTINUOUS-AT)))
       (dk-peel!)
       (let* ((r8e-gl (dk-goal))
              (r8e-nd (if r8e-cc (list-ref r8e-gl 3) (cadr r8e-gl)))
              (r8e-k  (caddr r8e-nd))
              (r8e-t  (if r8e-cc (list-ref r8e-gl 4) (caddr r8e-gl)))
              (r8e-hk (list 'NTH-DERIV-V 'm 'f r8e-k))
              (r8e-hs (list 'NTH-DERIV-V 'm 'f (list 'succ r8e-k)))
              (r8e-gh (list 'COMPOSE 'g r8e-hk)))
         (dk-split-all!)
         (fact 'dfun-v-mono 'm 'f 'n r8e-k)
         (have! (list 'AND (list 'IN r8e-k 'NN) (list '<= r8e-k 'n)))
         (dk-apply! r8e-df r8e-k)                    ; f^(k) is total
         (fact 'r8e-gof-nth-deriv-fn r8e-k 'm 'f 'g)
         (if r8e-cc
             (begin                              ; ---- the continuity conjunct
               (subst (list '= r8e-nd r8e-gh))
               (dk-apply! r8e-cont r8e-k r8e-t)
               (fact 'r8e-blf-compose-continuous 'm 'g r8e-hk r8e-t)
               (ass))
             (begin                              ; ---- the differentiability conjunct
               ;; dk-split-all! above broke the interior guard into its two
               ;; halves; TD-V's universal wants it back as ONE conjunction.
               (have! (list 'AND
                            (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '<)
                                                      (equal? (caddr f) r8e-t)))
                                     "a < t")
                            (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '<)
                                                      (equal? (cadr f) r8e-t)))
                                     "t < x")))
               (dk-apply! r8e-diff r8e-k r8e-t)
               (let ((r8e-dv (list 'IS-DIFF-AT-V 'm r8e-hk r8e-t (list r8e-hs r8e-t))))
                 (have! (list 'IN r8e-t 'RR)
                        (lambda ()
                          (dk-split-all!
                           (dk-landed (lambda () (mac-h 'is-diff-at-v r8e-dv))))
                          (ass))))
               (fact 'diff-v-value-in-vec 'm r8e-hk r8e-t (list r8e-hs r8e-t))
               (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hs r8e-t))
               (fact 'r8e-blf-diff-commute 'm 'g r8e-hk r8e-t (list r8e-hs r8e-t))
               (fact 'deriv-of-is-diff-at r8e-gh r8e-t (list 'g (list r8e-hs r8e-t)))
               ;; (g o f)^(k+1)(t) = DERIV((g o f)^(k), t): the commutation is
               ;; then needed only at k.
               (mac 'nth-deriv-succ)
               (lam-b)
               (subst (list '= r8e-nd r8e-gh))
               (subst (list '= (list 'DERIV r8e-gh r8e-t)
                            (list 'g (list r8e-hs r8e-t))))
               (ass))))))))
(r8e-check! 'gof-taylor-diff-dfun)
(alias! 'gof-taylor-diff-dfun
        "a bounded linear functional preserves Taylor differentiability")

;;; =====================================================================
;;; (11) THE PROJECTION THE CITER NEEDS.  gof-nth-deriv-dfun asks for
;;; IS-DIFF-AT-V(m, f^(n), t, f^(n+1)(t)) at the interior point; that is the
;;; second conjunct of TAYLOR-DIFFERENTIABLE-V at (n, t), and nothing in the
;;; tree surfaced it (taylor-v-deriv-in-vec unfolds TD-V for the TYPING only).
;;; With this, the citation at vector-taylor-proof.scm:751 is two lines.
;;; =====================================================================
(sp (make-wff
     '(FORALL m (FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
        (IMPLIES (TAYLOR-DIFFERENTIABLE-V m f a x n)
        (IMPLIES (IN n NN)
        (IMPLIES (< a t) (IMPLIES (< t x)
          (IS-DIFF-AT-V m (NTH-DERIV-V m f n) t
                        ((NTH-DERIV-V m f (succ n)) t))))))))))))))
(dk-peel!)
(dk-split-all!
 (dk-landed (lambda () (mac-h 'taylor-differentiable-v
                              '(TAYLOR-DIFFERENTIABLE-V m f a x n)))))
(fact 'nn-le-refl 'n)
(have! '(AND (IN n NN) (<= n n)))
(have! '(AND (< a t) (< t x)))
(dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                     (dk-contains? f 'IS-DIFF-AT-V)))
                    "the differentiability conjunct of TD-V")
           'n 't)
(ass)
(r8e-check! 'r8e-td-v-diff-at)
(alias! 'r8e-td-v-diff-at
        "a Taylor-differentiable curve is vector-differentiable at an interior point")

;;; =====================================================================
;;; (12) THE LEAF `g-of-remainder', GUARDED.
;;;
;;; Three utilities first: the TAYLOR-POLY unfold as a THEOREM (a def-functoid
;;; installs only a macete, and `subst' needs a named equation to go BACKWARDS
;;; from SERIES-PARTIAL-SUM to TAYLOR-POLY -- CLAUDE.md, "where a definition
;;; lives"), and two arithmetic identities stated with the coefficient
;;; QUANTIFIED, because `crs' declines any goal containing `recip'.
;;; =====================================================================
(sp (make-wff
     '(FORALL ff (FORALL aa (FORALL nd (FORALL xx
        (== (TAYLOR-POLY ff aa nd xx)
            (SERIES-PARTIAL-SUM
              (VNB-LAMBDA k NN (* (* ((NTH-DERIV ff k) aa) (power (- xx aa) k))
                                  (recip (FACTORIAL k))))
              (succ nd)))))))))
(dk-peel!)
(mac 'TAYLOR-POLY)
(qrfl)
(r8e-check! 'r8e-tp-unfold)

(sp (make-wff
     '(FORALL p_ (IMPLIES (IN p_ RR)
        (FORALL q_ (IMPLIES (IN q_ RR)
        (FORALL v_ (IMPLIES (IN v_ RR)
          (= (* (* p_ q_) v_) (* (* v_ p_) q_))))))))))
(dk-peel!)
(crs)
(r8e-check! 'r8e-coef-comm)

(sp (make-wff '(FORALL y_ (IMPLIES (IN y_ RR) (= (+ 0 y_) y_)))))
(dk-peel!)
(crs)
(r8e-check! 'r8e-zero-add)

;;; ---- the coefficient (x-a)^k / k!, and the summand of TAYLOR-POLY -------
(define (r8e-coef k) (list '* (list 'power '(- x a) k) (list 'recip (list 'FACTORIAL k))))
(define (r8e-coef-real! k)
  (fact 'rr-sub-in-rr 'x 'a)
  (fact 'power-closed-at k '(- x a))
  (fact 'recip-factorial-in-rr k)
  (have! (list 'AND (list 'IN (list 'power '(- x a) k) 'RR)
               (list 'IN (list 'recip (list 'FACTORIAL k)) 'RR)))
  (fact 'rr-mul-closed (list 'power '(- x a) k) (list 'recip (list 'FACTORIAL k))))
(define r8e-lam
  '(VNB-LAMBDA k NN (* (* ((NTH-DERIV (COMPOSE g f) k) a) (power (- x a) k))
                       (recip (FACTORIAL k)))))
;;; (IN (g (f^(k)(a))) RR), by the commutation (8) -- the value of the k-th
;;; summand once the derivative has been pushed through g.
(define (r8e-gval k) (list 'g (list (list 'NTH-DERIV-V 'm 'f k) 'a)))
(define (r8e-product-real! u v)
  (have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

;;; =====================================================================
;;; (12a) g of the vector Taylor polynomial IS the scalar Taylor polynomial of
;;; g o f, by induction on n.  n is OUTERMOST (`ni' tests the literal shape);
;;; the leaf's own binder order comes back in (12b) by one `fact'.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
       (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'a
         (list 'FORALL 'x
           (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
           (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
           (list 'IMPLIES '(IN f (FUN RR (VEC m)))
           (list 'IMPLIES '(IN a RR)
           (list 'IMPLIES '(IN x RR)
           (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
             '(= (g (TAYLOR-POLY-V m f a x n))
                 (TAYLOR-POLY (COMPOSE g f) a n x)))))))))))))))))
(define r8e-br (use-induction))
(define r8e-nv (cdr (assq 'var r8e-br)))
(define r8e-ih (cdr (assq 'ih  r8e-br)))

;;; ---- base: n = 0 ------------------------------------------------------
(dk-focus! (cdr (assq 'base r8e-br)))
(dk-peel-to! '=)
(have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
(have! r8e-lin-hom               (lambda () (r8e-blf-split!) (ass)))
(fact 'nn-zero-in)
(fact 'rr-zero-in)
(fact 'gof-in-fun 'm 'f 'g)
(fact 'fun-apply-type-c 'f 'RR '(VEC m) 'a)
(fact 'fun-apply-type-c 'g '(VEC m) 'RR '(f a))
(r8e-coef-real! 0)
(have! '(AND (IN f (FUN RR (VEC m))) (IN g (FUN (VEC m) RR))))
(fact 'compose-apply 'RR '(VEC m) 'RR 'g 'f)
(dk-apply! (r8e-capply 'f) 'a)
(fact 'r8e-tp-unfold '(COMPOSE g f) 'a 0 'x)
(fact 'series-partial-sum-zero r8e-lam)
(have! (list 'IN (list 'SERIES-PARTIAL-SUM r8e-lam 0) 'RR)
       (lambda () (subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam 0) 0)) (ass)))
(have! (list 'IN (list r8e-lam 0) 'RR)
       (lambda ()
         (lam-b)
         (mac 'nth-deriv-zero)
         (subst '(= ((COMPOSE g f) a) (g (f a))))
         (r8e-product-real! '(g (f a)) (list 'power '(- x a) 0))
         (r8e-product-real! (list '* '(g (f a)) (list 'power '(- x a) 0))
                            (list 'recip (list 'FACTORIAL 0)))
         (ass)))
(fact 'series-partial-sum-succ r8e-lam 0)
(mac 'taylor-poly-v-zero)
(mac 'nth-deriv-v-zero)
(subst (dk-apply! r8e-lin-hom (r8e-coef 0) '(f a)))
(subst (list '= '(TAYLOR-POLY (COMPOSE g f) a 0 x)
             (list 'SERIES-PARTIAL-SUM r8e-lam '(succ 0))))
(subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam '(succ 0))
             (list '+ (list 'SERIES-PARTIAL-SUM r8e-lam 0) (list r8e-lam 0))))
(subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam 0) 0))
(lam-b)
(mac 'nth-deriv-zero)
(subst '(= ((COMPOSE g f) a) (g (f a))))
(fact 'r8e-coef-comm (list 'power '(- x a) 0) (list 'recip (list 'FACTORIAL 0)) '(g (f a)))
(subst (list '= (list '* (r8e-coef 0) '(g (f a)))
             (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                   (list 'recip (list 'FACTORIAL 0)))))
(r8e-product-real! '(g (f a)) (list 'power '(- x a) 0))
(r8e-product-real! (list '* '(g (f a)) (list 'power '(- x a) 0))
                   (list 'recip (list 'FACTORIAL 0)))
(fact 'r8e-zero-add (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                          (list 'recip (list 'FACTORIAL 0))))
(subst (list '= (list '+ 0 (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                                  (list 'recip (list 'FACTORIAL 0))))
             (list '* (list '* '(g (f a)) (list 'power '(- x a) 0))
                   (list 'recip (list 'FACTORIAL 0)))))
(rfl)

;;; ---- step -------------------------------------------------------------
(dk-focus! (cdr (assq 'step r8e-br)))
(dk-peel-to! '=)
(let* ((r8e-dfs (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (dk-contains? f 'NTH-DERIV-V)
                                          (dk-contains? f 'FUN)))
                         "DFUN-V(m,f,succ n)"))
       (r8e-sn (list 'succ r8e-nv))
       (r8e-hs (list 'NTH-DERIV-V 'm 'f r8e-sn))
       (r8e-tv (list 'TAYLOR-POLY-V 'm 'f 'a 'x r8e-nv))
       (r8e-cf (r8e-coef r8e-sn))
       (r8e-vl (list 'g (list r8e-hs 'a))))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (have! r8e-lin-hom               (lambda () (r8e-blf-split!) (ass)))
  (have! r8e-lin-add               (lambda () (r8e-blf-split!) (ass)))
  (fact 'nn-succ-closed r8e-nv)
  (fact 'nn-le-succ r8e-nv)
  (fact 'gof-in-fun 'm 'f 'g)
  (fact 'dfun-v-mono 'm 'f r8e-sn r8e-nv)
  ;; the induction hypothesis at this m f g a x
  (let ((r8e-ihi (dk-apply! r8e-ih 'm 'f 'g 'a 'x)))
    ;; typings: the polynomial, the (n+1)-st derivative value, the coefficient
    (fact 'vtaylor-poly-in-vec 'm 'f 'a 'x r8e-nv)
    (fact 'nth-deriv-v-in-vec 'm 'f r8e-sn 'a)
    (r8e-coef-real! r8e-sn)
    (fact 'nvs-act-in-vec 'm r8e-cf (list r8e-hs 'a))
    (fact 'fun-apply-type-c 'g '(VEC m) 'RR r8e-tv)
    (fact 'fun-apply-type-c 'g '(VEC m) 'RR (list r8e-hs 'a))
    ;; the commutation (8) at succ n, and the beta law of g o f^(succ n)
    (fact 'r8e-gof-nth-deriv-fn r8e-sn 'm 'f 'g)
    (fact 'nn-le-refl r8e-sn)
    (have! (list 'AND (list 'IN r8e-sn 'NN) (list '<= r8e-sn r8e-sn)))
    (dk-apply! r8e-dfs r8e-sn)                  ; f^(succ n) is total
    (have! (list 'AND (list 'IN r8e-hs '(FUN RR (VEC m))) '(IN g (FUN (VEC m) RR))))
    (fact 'compose-apply 'RR '(VEC m) 'RR 'g r8e-hs)
    (dk-apply! (r8e-capply r8e-hs) 'a)
    ;; the two unfolds of TAYLOR-POLY, and the partial-sum recurrence
    (fact 'r8e-tp-unfold '(COMPOSE g f) 'a r8e-nv 'x)
    (fact 'r8e-tp-unfold '(COMPOSE g f) 'a r8e-sn 'x)
    (have! (list 'IN (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-nv)) 'RR)
           (lambda ()
             (subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-nv))
                          (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-nv 'x)))
             (subst (list '= (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-nv 'x)
                          (list 'g r8e-tv)))
             (ass)))
    (have! (list 'IN (list r8e-lam r8e-sn) 'RR)
           (lambda ()
             (lam-b)
             (subst (list '= (list 'NTH-DERIV '(COMPOSE g f) r8e-sn)
                          (list 'COMPOSE 'g r8e-hs)))
             (subst (list '= (list (list 'COMPOSE 'g r8e-hs) 'a) r8e-vl))
             (r8e-product-real! r8e-vl (list 'power '(- x a) r8e-sn))
             (r8e-product-real! (list '* r8e-vl (list 'power '(- x a) r8e-sn))
                                (list 'recip (list 'FACTORIAL r8e-sn)))
             (ass)))
    (fact 'series-partial-sum-succ r8e-lam r8e-sn)
    ;; ---- the goal
    (mac 'taylor-poly-v-succ)
    (subst (dk-apply! r8e-lin-add r8e-tv (list (list 'ACT 'm) r8e-cf (list r8e-hs 'a))))
    (subst (dk-apply! r8e-lin-hom r8e-cf (list r8e-hs 'a)))
    (subst r8e-ihi)
    (subst (list '= (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-sn 'x)
                 (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-sn))))
    (subst (list '== (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-sn))
                 (list '+ (list 'SERIES-PARTIAL-SUM r8e-lam r8e-sn)
                       (list r8e-lam r8e-sn))))
    (subst (list '= (list 'TAYLOR-POLY '(COMPOSE g f) 'a r8e-nv 'x)
                 (list 'SERIES-PARTIAL-SUM r8e-lam (list 'succ r8e-nv))))
    (lam-b)
    (subst (list '= (list 'NTH-DERIV '(COMPOSE g f) r8e-sn)
                 (list 'COMPOSE 'g r8e-hs)))
    (subst (list '= (list (list 'COMPOSE 'g r8e-hs) 'a) r8e-vl))
    (fact 'r8e-coef-comm (list 'power '(- x a) r8e-sn)
          (list 'recip (list 'FACTORIAL r8e-sn)) r8e-vl)
    (subst (list '= (list '* r8e-cf r8e-vl)
                 (list '* (list '* r8e-vl (list 'power '(- x a) r8e-sn))
                       (list 'recip (list 'FACTORIAL r8e-sn)))))
    ;; `rfl' is strict: the REDUCED summand must be typed, not just the
    ;; unreduced (LAM (succ n)) the recurrence was cited with.
    (r8e-product-real! r8e-vl (list 'power '(- x a) r8e-sn))
    (r8e-product-real! (list '* r8e-vl (list 'power '(- x a) r8e-sn))
                       (list 'recip (list 'FACTORIAL r8e-sn)))
    (rfl)))
(r8e-check! 'r8e-g-of-poly-ind)

;;; =====================================================================
;;; (12b) THE LEAF `g-of-remainder', GUARDED.  Binders m f g a x n and the body
;;; are the support's (vector-taylor-proof.scm:641-647) unchanged; the added
;;; antecedents are IS-NORMED-VECTOR-SPACE(m) and DFUN-V(m,f,n) -- the latter
;;; is what `vtaylor-poly-in-vec' and (12a) both need, and the citer holds it
;;; at :707.  Without it TAYLOR-POLY-V applies ACT to f^(k)(a), an IOTA with no
;;; satisfier, and the support's strict `=' is FALSE.
;;; =====================================================================
(sp (make-wff
     (list 'FORALL 'm (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'a
       (list 'FORALL 'x (list 'FORALL 'n
         (list 'IMPLIES '(IS-NORMED-VECTOR-SPACE m)
         (list 'IMPLIES '(IS-BOUNDED-LINEAR-FUNCTIONAL m g)
         (list 'IMPLIES '(IN f (FUN RR (VEC m)))
         (list 'IMPLIES '(IN a RR)
         (list 'IMPLIES '(IN x RR)
         (list 'IMPLIES '(IN n NN)
         (list 'IMPLIES (r8e-dfun-v 'm 'f 'n)
           '(= (g ((VADD m) (f x) ((VNEG m) (TAYLOR-POLY-V m f a x n))))
               (- ((COMPOSE g f) x)
                  (TAYLOR-POLY (COMPOSE g f) a n x))))))))))))))))))
(dk-peel!)
(let ((r8e-pv '(TAYLOR-POLY-V m f a x n)))
  (have! '(IN g (FUN (VEC m) RR)) (lambda () (r8e-blf-split!) (ass)))
  (fact 'fun-apply-type-c 'f 'RR '(VEC m) 'x)
  (fact 'vtaylor-poly-in-vec 'm 'f 'a 'x 'n)
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR '(f x))
  (fact 'fun-apply-type-c 'g '(VEC m) 'RR r8e-pv)
  (fact 'gof-in-fun 'm 'f 'g)
  (have! '(AND (IN f (FUN RR (VEC m))) (IN g (FUN (VEC m) RR))))
  (fact 'compose-apply 'RR '(VEC m) 'RR 'g 'f)
  (dk-apply! (r8e-capply 'f) 'x)
  ;; g(f(x) (-) P) = g(f(x)) - g(P)
  (subst (dk-fact! 'r8e-blf-sub 'm 'g '(f x) r8e-pv))
  ;; (g o f)(x) = g(f(x))  and  TAYLOR-POLY(g o f, a, n, x) = g(P)
  (subst '(= ((COMPOSE g f) x) (g (f x))))
  (fact 'r8e-g-of-poly-ind 'n 'm 'f 'g 'a 'x)
  (subst (list '= '(TAYLOR-POLY (COMPOSE g f) a n x) (list 'g r8e-pv)))
  (rfl))
(r8e-check! 'g-of-remainder-dfun)
(alias! 'g-of-remainder-dfun
        "a bounded linear functional turns the vector Taylor remainder into the scalar one")

;;; =====================================================================
;;; WHAT THE THREE CITATIONS IN vector-taylor-proof.scm BECOME
;;;   :723  (fact 'gof-taylor-diff 'm 'f G 'a 'x 'n)
;;;      -> (fact 'gof-taylor-diff-dfun 'm 'f G 'a 'x 'n)
;;;   :750  (fact 'g-of-remainder 'm 'f G 'a 'x 'n)
;;;      -> (fact 'g-of-remainder-dfun 'm 'f G 'a 'x 'n)
;;;   :751  (fact 'gof-nth-deriv 'm 'f G 'n THETA)
;;;      -> (fact 'r8e-td-v-diff-at 'm 'f 'a 'x 'n THETA)   [new line]
;;;         (fact 'gof-nth-deriv-dfun 'm 'f G 'n THETA)
;;; Every antecedent of the three guarded theorems is in that proof's context
;;; at those lines: IS-NORMED-VECTOR-SPACE(m), IS-BOUNDED-LINEAR-FUNCTIONAL(m,G),
;;; f in FUN(RR,VEC m), a, x in RR, n in NN and (< a THETA), (< THETA x) from
;;; ANT1 and the taylor-lagrange existential, and DFUN-V(m,f,n) from the
;;; `taylor-v-derivs-in-fun' citation already at :707.
;;; =====================================================================

;;; ===== END spliced block (2026-09-19) =====

;;; ====================================================================
;;; warranted cores
;;; ====================================================================

;;; the norm metric is a metric space.
;;; nvs-metric-is-ms RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-norm-metrics.scm

;;; the vector Taylor polynomial is a vector.

;;; the remainder is a vector.
;;; g o f is a real function when g is a bounded linear functional on m.
;;; gof-taylor-diff RETIRED 2026-09-19 (rake batch 7-E): FALSE as stated (f(t) = |t|.v, n = 0, t = 0: (g o f)^(1) is not a total real function, so the TAYLOR-DIFFERENTIABLE conjuncts are undefined); proven modulo 0 as `gof-taylor-diff-dfun' in the block above, guarded on IS-NORMED-VECTOR-SPACE(m), (IN n NN) and DFUN-V(m,f,n).

;;; g-of-remainder RETIRED 2026-09-19 (rake batch 7-E): FALSE as stated (f(t) = |t|.v, n = 0, t = 0: both sides are undefined and `=' is strict); proven modulo 0 as `g-of-remainder-dfun' in the block above, guarded on IS-NORMED-VECTOR-SPACE(m) and DFUN-V(m,f,n).

;;; gof-nth-deriv RETIRED 2026-09-19 (rake batch 7-E): FALSE as stated (f(t) = |t|.v, n = 0, t = 0: both sides are undefined and `=' is strict); proven modulo 0 as `gof-nth-deriv-dfun' in the block above, guarded on DFUN-V(m,f,n) and the IS-DIFF-AT-V that TAYLOR-DIFFERENTIABLE-V carries at the interior point.

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
(quietly (lambda () (fact 'gof-taylor-diff-dfun 'm 'f G 'a 'x 'n)))

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
(quietly (lambda () (fact 'g-of-remainder-dfun 'm 'f G 'a 'x 'n)))    ; (= GRr SR)
;; the guarded gof-nth-deriv-dfun also wants the IS-DIFF-AT-V of f^(n) at theta,
;; which is TD-V's second conjunct there (r8e-td-v-diff-at, spliced above).
(quietly (lambda () (fact 'r8e-td-v-diff-at 'm 'f 'a 'x 'n THETA)))
(quietly (lambda () (fact 'gof-nth-deriv-dfun 'm 'f G 'n THETA)))     ; (= NTHGOF GFN1)

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
