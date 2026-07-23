;;; nvs-taylor-statement.scm -- STATEMENT ONLY (no proof) of Taylor's theorem
;;; with remainder bound for a map between two finite-dimensional real normed
;;; vector spaces.  Warranted to Dieudonné; proof deferred (the user may fill it
;;; in later).  Added 2026-07-22 as a seed of the reference-warranted base.
;;;
;;; MODELLING (user-confirmed): the SEGMENT / directional form.  Rather than
;;; introduce a multilinear-derivative apparatus (D^k f(a) as a k-linear map,
;;; the operator norm, a segment sup), restrict f to the line through a in the
;;; direction h -- the curve
;;;         phi(t) = f( a (+) t.h )   :  RR -> VEC(cm),
;;; already differentiable in the library's curve sense.  Then
;;;         phi^(k)(0) = D^k f(a).h^k,
;;; so TAYLOR-POLY-V(cm, phi, 0, 1, n) IS the genuine multivariable Taylor
;;; polynomial and the whole statement reuses the existing curve vocabulary
;;; (NTH-DERIV-V, TAYLOR-POLY-V, TAYLOR-DIFFERENTIABLE-V) -- no new vocabulary.
;;; This is how multivariable Taylor is usually taught (restrict to a line) and
;;; is Dieudonné's own reduction.  The theta-form (a mean-value point in (0,1))
;;; matches the existing curve theorem vector-taylor-remainder-bound; the sup
;;; form ||R|| <= (1/(n+1)!) sup_{[0,1]} ||phi^(n+1)|| follows.
;;;
;;; Names are case-fold-safe: dm = domain NVS, cm = codomain NVS (NOT E/F -- F
;;; would fold onto the function f).  Loaded after vector-taylor-proof (all the
;;; curve vocabulary it reuses is defined there).
;;; ====================================================================

;;; The directional curve  phi(t) = f(a (+) t.h)  in the DOMAIN's module ops,
;;; valued in VEC(cm).  Spliced (three occurrences) rather than repeated.
(define nt-phi '(VNB-LAMBDA t (f ((VADD dm) a ((ACT dm) t h)))))

;;; The remainder vector  R = f(a (+) h) (-) TAYLOR-POLY-V(cm, phi, 0, 1, n).
;;; We write f(a(+)h) for phi(1) = f(a (+) 1.h); the two are equal by the module
;;; unital law 1.h = h.
(define nt-remainder
  `((VADD cm) (f ((VADD dm) a h))
              ((VNEG cm) (TAYLOR-POLY-V cm ,nt-phi 0 1 n))))

(support 'nvs-taylor-remainder-bound
  (forall-guarded '(dm cm f a h n)
    (list
      '(IS-NORMED-VECTOR-SPACE dm)
      '(IS-FINITE-DIMENSIONAL dm)
      '(IS-NORMED-VECTOR-SPACE cm)
      '(IS-FINITE-DIMENSIONAL cm)
      '(IN f (FUN (VEC dm) (VEC cm)))
      '(IN a (VEC dm))
      '(IN h (VEC dm))
      '(IN n NN)
      `(TAYLOR-DIFFERENTIABLE-V cm ,nt-phi 0 1 n))
    `(FORSOME theta
       (AND (< 0 theta)
       (AND (< theta 1)
         (<= (* (FACTORIAL (succ n)) ((VNRM cm) ,nt-remainder))
             ((VNRM cm) ((NTH-DERIV-V cm ,nt-phi (succ n)) theta))))))))

(warrant! 'nvs-taylor-remainder-bound 'reference
  '(dieudonne "Taylor's formula, 8.14.3"))

;; Verbose content lives in the gloss (the citation stays a terse structured
;; locator).  States the hypotheses, the directional modelling, and the intended
;; proof route.
(gloss! 'nvs-taylor-remainder-bound
  "Taylor's theorem with remainder bound for a map f between two finite-dimensional
   real normed vector spaces dm (domain) and cm (codomain).  For a base point a and
   an increment h in VEC(dm), let phi(t) = f(a (+) t.h) be the restriction of f to
   the segment from a to a (+) h -- a curve RR -> VEC(cm).  Hypothesis: phi is
   (n+1)-times differentiable on [0,1] in the curve sense (TAYLOR-DIFFERENTIABLE-V:
   each phi^(k), k<=n, norm-continuous on [0,1] and vector-differentiable on (0,1)
   with derivative phi^(k+1)).  Conclusion: there is a mean-value point theta in
   (0,1) with (n+1)! * ||R|| <= ||phi^(n+1)(theta)||, where the remainder
   R = f(a (+) h) (-) TAYLOR-POLY-V(cm, phi, 0, 1, n) and the polynomial is
   sum_{k=0}^{n} (1/k!) phi^(k)(0) = sum_{k=0}^{n} (1/k!) D^k f(a).h^k -- the genuine
   multivariable Taylor polynomial, phi^(k)(0) being the k-th directional derivative.
   Dieudonné (Foundations of Modern Analysis, Taylor's formula 8.14.3) proves the
   Banach-space version WITHOUT Hahn-Banach, via the mean-value inequality.  Our
   intended (finite-dimensional, non-constructive) proof instead reduces to the curve
   theorem vector-taylor-remainder-bound applied to phi -- the norm-attaining-
   functional / Hahn-Banach route already in the library -- hence the rests-on below.")

(category! 'nvs-taylor-remainder-bound 'analysis)

;; The intended proof rests on the curve theorem (apply it to phi): declared so
;; the cycle checker keeps the reference base acyclic.  vector-taylor-remainder-
;; bound is itself PROVEN, so this edge just documents the reduction; it can
;; never create a cycle unless that theorem were later re-proved through this one.
(rests-on 'nvs-taylor-remainder-bound '(vector-taylor-remainder-bound))
