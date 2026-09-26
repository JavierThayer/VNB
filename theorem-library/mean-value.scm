;;; mean-value.scm -- the Mean Value Theorem arc (calculus.pdf Ch 2.4-2.5):
;;; interior-extremum => derivative 0 (Prop 2.10), Rolle's lemma (2.12), and
;;; later the MVT itself.  Built on the Extreme Value Theorem (extreme-value.scm)
;;; and IS-DIFF-AT (differentiation.scm).
;;;
;;; All asserted as witness-manufacturing blocks: Rolle's theta comes from EVT's
;;; argmax via Prop 2.10, so a downstream consumer bc*'s rolle and never guesses
;;; theta -- [[automatable-assembly]].
;;; RETIRED 2026-09-14 (proven): continuous-nonpos-right -- theorem-library/continuous-one-sided-sign.scm
;;; RETIRED 2026-09-14 (proven): continuous-nonneg-left -- theorem-library/continuous-one-sided-sign.scm

;;; ===================================================================
;;; Prop 2.10 (interior form): at an interior maximum/minimum of f on [a,b],
;;; if f is differentiable there, its derivative is 0.
;;; ===================================================================

;;; Caratheodory view: f(x)-f(theta) = phi(x)(x-theta), phi continuous at theta,
;;; phi(theta)=L.  At an interior max, f(x)-f(theta) <= 0 on [a,b]; for x>theta
;;; (x-theta>0) phi(x)<=0, for x<theta phi(x)>=0; continuity at theta forces
;;; phi(theta)=L=0.
;;;
;;; interior-max-deriv-zero is now MACHINE-PROVEN from these two continuity
;;; sign-preservation supports (+ product-sign / difference-sign in
;;; order-lemmas.scm) -- see theorem-library/interior-extremum-proof.scm.
;;; The supports are stated with CURRIED antecedents (no AND) so the proof can
;;; apply them FORWARD by `fact` (their conclusion (g th) is higher-order, so
;;; bc* would loop the matcher).


;; interior-min-deriv-zero is MACHINE-PROVEN from interior-max-deriv-zero applied
;; to g = -f (deriv-neg + rr-le-neg + rr-neg-eq-zero) -- see
;; theorem-library/interior-extremum-proof.scm.

;;; ===================================================================
;;; Rolle's lemma (2.12): h continuous on [a,b], differentiable on (a,b), with
;;; h(a)=h(b), has an interior critical point.
;;; ===================================================================
;; rolle is now MACHINE-PROVEN from EVT (extreme-value-max/min) + Fermat
;; (interior-max/min-deriv-zero) + the constant-case midpoint -- see
;; theorem-library/rolle-proof.scm.  generalized-mvt/mvt below still bc* it.

;;; ===================================================================
;;; Generalized MVT (Thm 2.11) -> MVT (Thm 2.13) -> corollaries (2.14, 2.15).
;;; Witnesses (theta) flow from rolle by bc*, so the arc stays assemblable.
;;; Stated with product forms (L*(b-a) = f(b)-f(a)) to avoid division.
;;; ===================================================================

;;; Thm 2.11: generalized MVT (Cauchy MVT).  Now MACHINE-PROVEN in
;;; theorem-library/generalized-mvt-proof.scm (apply Rolle to the auxiliary
;;; h(x)=f(x)(g(b)-g(a))-g(x)(f(b)-f(a)); h(a)=h(b), and h'(theta)=0 is the
;;; stated identity).  The asserted statement is retired from here; the alias!
;;; below stays.

;;; Thm 2.13: MVT.  Now MACHINE-PROVEN in theorem-library/mvt-proof.scm (apply
;;; Rolle to the auxiliary h(z)=f(z)(b-a)-z(f(b)-f(a))); the alias! below stays.

;;; Cor 2.15: derivative identically 0 on (a,b) => f constant on [a,b].
;;; Now MACHINE-PROVEN in theorem-library/deriv-constant-proof.scm (trichotomy
;;; on u,v + MVT on the subinterval [min,max] + derivative-unique); the asserted
;;; statement is retired from here.  The alias! below stays.

;;; Cor 2.14: f' <= M on (a,b) => f(b)-f(a) <= M(b-a)  (and the >= m form).
;;; Both now MACHINE-PROVEN in theorem-library/mvt-bounds-proof.scm (MVT gives
;;; theta with f(b)-f(a)=f'(theta)(b-a); the bound on f'(theta) -- transferred to
;;; the MVT witness via derivative-unique -- scales by (b-a)>=0).  The asserted
;;; statements are retired from here; the alias!s below stay.

;;; Classic textbook names, for (find-theorem "...") lookup.
(alias! 'rolle "Rolle's theorem" "Rolle's lemma")
(alias! 'mvt "Mean Value Theorem" "MVT" "Lagrange Mean Value Theorem")
(alias! 'generalized-mvt "Generalized Mean Value Theorem" "Cauchy Mean Value Theorem")
(alias! 'mvt-upper-bound "Mean Value Theorem (upper bound corollary)")
(alias! 'mvt-lower-bound "Mean Value Theorem (lower bound corollary)")
(alias! 'interior-max-deriv-zero "Fermat's theorem (interior maximum)" "interior extremum theorem")
(alias! 'interior-min-deriv-zero "Fermat's theorem (interior minimum)" "interior extremum theorem")
(alias! 'deriv-zero-implies-constant "constant function theorem (zero derivative)")
