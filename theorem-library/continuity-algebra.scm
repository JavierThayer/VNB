;;; continuity-algebra.scm -- pointwise continuity is an algebra on RR.
;;;
;;; The supporting machinery for differentiation (theorem-library/
;;; differentiation.scm): IS-CONTINUOUS-AT(RR-MS,RR-MS,-,a) holds of the
;;; constant and identity maps and is closed under pointwise sum, product,
;;; difference and composition.
;;;
;;; SIX OF THE SEVEN ARE NOW PROVEN, and have left this file.  On 2026-08-17:
;;; const- and identity-continuous-at to theorem-library/continuity-basics.scm,
;;; sum-continuous-at to theorem-library/continuity-sum.scm and
;;; product-continuous-at to theorem-library/continuity-product.scm.  On
;;; 2026-08-18: cont-transfer-ptwise-eq to
;;; theorem-library/continuity-transfer.scm and sub-continuous-at to
;;; theorem-library/continuity-sub.scm.  Each is `modulo 0' and each carries the
;;; FUN typing of its lambda.  Every one of them had stood here as a `support'
;;; warranted `well-known' whose warrant TEXT was the proof -- the eps-delta
;;; drudgery the PSS was meant to absorb turned out to be a handful of citations
;;; of general lemmas (rr-abs-sum-bound, rr-abs-prod-bound, rr-min-pos,
;;; rr-pos-halvable) and, for the last two, no estimate at all.
;;;
;;; With them, `diff-implies-continuous' (theorem-library/differentiation.scm)
;;; bills `modulo 0'.
;;;
;;; SEVEN OF THE SEVEN algebra facts are now proven: composition left on
;;; 2026-08-23 for theorem-library/continuity-compose.scm, by exactly the route
;;; its warrant proposed (feed the g-at-f(a) delta into the f-at-a delta, no
;;; eps/2 split needed).  The one support that remained, `cont-agree-off-pt'
;;; (not an algebra fact but the statement that RR has no isolated points), is
;;; PROVEN in theorem-library/cont-agree-off-pt.scm, which loads right after
;;; this file; the support was retired from here on 2026-09-16 (until then the
;;; name was installed twice, asserted here and then proven).  No support
;;; remains in this file.

;;; const-continuous-at and identity-continuous-at MOVED 2026-08-17 to
;;; theorem-library/continuity-basics.scm, where both are PROVEN `modulo 0'
;;; (with their FUN typings, const-lam-in-fun / ident-lam-in-fun).  They stood
;;; here as `well-known' supports whose warrant text WAS the proof -- "for any
;;; eps>0 any delta>0 works, since d(c,c)=0<=eps" and "delta=eps works" -- i.e.
;;; a derivation written in prose and then not run, the species of comment that
;;; also hid integral-domain-cancel-zero.  Statements reproduced verbatim there,
;;; so differentiation.scm's five citations are unaffected.

;;; sum-continuous-at MOVED 2026-08-17 to theorem-library/continuity-sum.scm,
;;; where it is PROVEN `modulo 0' (with its FUN typing, sum-lam-in-fun).  Its
;;; warrant here read "given eps, take delta = min of the eps/2-deltas for g and
;;; h" -- again the derivation written in prose and not run.  The eps/2 estimate
;;; it turns on is `rr-abs-sum-bound' (theorem-library/rr-abs-basics.scm) and the
;;; "min of the two deltas" is `rr-min-pos' (theorem-library/rr-order-basics.scm),
;;; both proven; the statement is reproduced verbatim there, so
;;; differentiation.scm's citations are unaffected.

;;; product-continuous-at MOVED 2026-08-17 to
;;; theorem-library/continuity-product.scm, where it is PROVEN `modulo 0' (with
;;; its FUN typing, prod-lam-in-fun).  Its warrant here -- "g is bounded near a
;;; (continuity), and |gh(x)-gh(a)| <= |g(x)||h(x)-h(a)| + |h(a)||g(x)-g(a)|" --
;;; is that proof, written in prose and not run; the estimate is
;;; `rr-abs-prod-bound' (theorem-library/rr-abs-basics.scm) and the bound near a
;;; is one preliminary delta at eps = 1.  Statement reproduced verbatim there.

;;; compose-continuous-at MOVED 2026-08-23 to
;;; theorem-library/continuity-compose.scm, where it is PROVEN.  It stood here
;;; as a `well-known' support whose warrant text WAS the proof -- "given eps,
;;; the g-at-f(a) delta feeds the f-at-a delta" -- i.e. the derivation written
;;; in prose and then not run, the species of comment that also hid
;;; integral-domain-cancel-zero.  It is the block the Caratheodory CHAIN RULE
;;; needs (theorem-library/chain-rule.scm): the factor of g o f is
;;; (phi_g o f)*phi_f, whose first half is continuous at a only by this fact.
;;; The statement is reproduced VERBATIM there.  Its bill is
;;; {compose-type, compose-apply} -- the two COMPOSE laws of
;;; structure-library/compose.scm, both `warrant: proof' -- and NOT zero; see
;;; that file's header for why the sequential route (continuous-at-iff-
;;; sequential) was not taken.

;;; sub-continuous-at MOVED 2026-08-18 to theorem-library/continuity-sub.scm,
;;; where it is PROVEN `modulo 0' (with its FUN typing, sub-lam-in-fun).  Its
;;; warrant here proposed the eps/2 route -- "(g-h)(x) = g(x) + (-1)*h(x); the
;;; eps/2 split for sum-continuous-at, negation being an isometry of RR" -- and
;;; that turned out to be more than the fact costs: neg-continuous-at,
;;; sum-continuous-at and cont-transfer-ptwise-eq compose, and no estimate is
;;; done in the new file at all.  It was, after cont-transfer-ptwise-eq below,
;;; the SOLE unwarranted leaf of `diff-implies-continuous', which now bills
;;; `modulo 0'.  Statement reproduced verbatim there, so differentiation.scm's
;;; citation is unaffected.

;;; cont-transfer-ptwise-eq MOVED 2026-08-18 to
;;; theorem-library/continuity-transfer.scm, where it is PROVEN `modulo 0'.  It
;;; stood here as a `well-known' support whose warrant text WAS the proof --
;;; "continuity reads only the values, and d(f(x),f(a)) = d(g(x),g(a)) at every
;;; x, so the same delta works" -- i.e. the derivation written in prose and then
;;; not run, the species of comment that also hid integral-domain-cancel-zero.
;;; It is the transfer that carries a conclusion from the tidy algebraic
;;; representative back to the function actually in hand, and it was the ONE
;;; unwarranted leaf of `diff-implies-continuous', which now bills `modulo 0'.
;;; Statement reproduced verbatim there, so differentiation.scm's citation is
;;; unaffected.

;;; Two maps continuous at a that agree at every OTHER point agree at a as well.
;;; (a is a limit point of RR, so the value at a is forced by the punctured
;;; values; the crux of uniqueness of the Caratheodory factor, hence of DERIV.)
