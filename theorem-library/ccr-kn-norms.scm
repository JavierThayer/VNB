;;; ccr-kn-norms.scm -- wave of 2026-11-09/10 (agent CCR-1109-E), wired 2026-11-10 from scratchpad/ccr1109e/ccr-kn-norms.scm.
;;; Library: analysis.

;;; ccr-kn-norms.scm -- CCR.pdf Proposition 3.8 for K^n with its unit basis (CCR-1109-E, 2026-11-09).
;;; Prefix ckn-.
;;;
;;;   ccr-3-8-kn  K a local NV field, n in NN, nu1 and nu2 norms on K^n = RING-POW(V, n), V the ring view of K.
;;;               Then c nu1(x) <= nu2(x) <= C nu1(x) for all x, with reals 0 < c, C.
;;;   One citation of ccr-3-8-basis (CCR-1109-B5) at the unit basis RING-UNITS(V, n) (ring-units-type,
;;;   ring-units-generate, ring-units-rel-free of theorem-library/ring-pow.scm).
;;;
;;; Destination theorem-library/ccr-kn-norms.scm.  Library: analysis (IS-LOCAL-NV-FIELD, IS-NORM-ON).
;;; LOAD WINDOW: after theorem-library/ccr-ch3e-norms (ccr-3-8-basis) and theorem-library/ring-pow.

(define ckn-v '(NORMED-FIELD-AS-COMMUTATIVE-RING K))
(define ckn-e `(RING-POW ,ckn-v n))
(define ckn-body
  `(FORSOME cnl (AND (IN cnl RR) (AND (< 0 cnl)
     (FORSOME cnu (AND (IN cnu RR) (AND (< 0 cnu)
       (FORALL cnx (IMPLIES (IN cnx (VEC ,ckn-e))
         (AND (<= (* cnl (nu1 cnx)) (nu2 cnx)) (<= (nu2 cnx) (* cnu (nu1 cnx)))))))))))))

(sp (make-wff `(FORALL K (IMPLIES (IS-LOCAL-NV-FIELD K) (FORALL n (IMPLIES (IN n NN)
  (FORALL nu1 (FORALL nu2 (IMPLIES (IS-NORM-ON K ,ckn-e nu1) (IMPLIES (IS-NORM-ON K ,ckn-e nu2) ,ckn-body))))))))))
(dk-peel!)
(dk-project! '(IS-NV-FIELD K) (lambda () (mac-h 'is-local-nv-field '(IS-LOCAL-NV-FIELD K))))
(dk-cite! 'nv-field-normed 'K)
(dk-cite! 'normed-field-as-commutative-ring-is-commutative-ring 'K)
(dk-cite! 'commutative-ring-is-ring ckn-v)
(dk-cite! 'ring-units-type ckn-v 'n)
(dk-cite! 'ring-units-generate ckn-v 'n)
(dk-cite! 'ring-units-rel-free ckn-v 'n)
(dk-cite! 'ccr-3-8-basis 'K ckn-e 'nu1 'nu2 'n `(RING-UNITS ,ckn-v n))
(if (not (sequent-node-grounded? (proof-state-focus *ps*))) (dk-ass!))
(qed 'ccr-3-8-kn)
(gloss! 'ccr-3-8-kn "Proposition 3.8 for K^n: any two norms on K^n over a local NV field are equivalent.")
