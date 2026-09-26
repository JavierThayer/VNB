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
    (fact 'diff-v-value-in-vec (cadr u2) (caddr u2) (cadddr u2) (car (cddddr u2)))
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
