;;; extreme-value.scm -- the closed interval [a,b] and the Extreme Value Theorem
;;; (calculus.pdf Ch 2.5; used in Rolle's lemma): a continuous function on a
;;; closed interval attains its maximum and minimum.
;;;
;;; Stated sequentially / limit-free, so the STATEMENT needs no metric-subspace
;;; or IS-COMPACT-on-subset machinery: "f continuous on [a,b]" is just
;;;   forall x in CCINT(a,b). IS-CONTINUOUS-AT(RR-MS, RR-MS, f, x).
;;; EVT is asserted (the proof is the destination -- continuous image of the
;;; compact [a,b] attains its sup; sequentially, a maximizing sequence has a
;;; convergent subsequence by seq-compactness of [a,b], whose limit attains the
;;; max).  It is a witness-manufacturing block: the argmax c feeds Rolle's lemma
;;; by bc*, so the MVT arc assembles from it -- [[automatable-assembly]].

;;; CCINT(a, b) = the closed interval [a, b] = { x in RR : a <= x <= b }.
(def-functoid 'CCINT '(a b)
  '(SEP x RR (AND (<= a x) (<= x b))))

(add-to-pss 'ccint-membership
  '(FORALL a (FORALL b (FORALL x
     (IFF (IN x (CCINT a b))
          (AND (IN x RR) (AND (<= a x) (<= x b))))))))
(warrant! 'ccint-membership 'proof
  "Separation: x in CCINT(a,b) = SEP(x in RR | a<=x and x<=b) iff x in RR and
   a<=x and x<=b, by the SEP membership kernel rule.")
(category! 'ccint-membership 'topology)

;;; EVT (max): a continuous function on [a,b] (a<=b) attains its maximum.
(add-to-pss 'extreme-value-max
  '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (<= a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
       (FORSOME c (AND (IN c (CCINT a b))
                  (FORALL x (IMPLIES (IN x (CCINT a b))
                    (<= (f x) (f c))))))))))))
(warrant! 'extreme-value-max 'reference
  "Extreme Value Theorem (calculus.pdf Ch 2.5, used in Rolle's lemma): a
   continuous f on the compact [a,b] attains its supremum.  Sequentially: a
   maximizing sequence in [a,b] has a convergent subsequence (seq-compactness of
   [a,b]); its limit c is in [a,b] and f(c) is the max by sequential continuity.")
(category! 'extreme-value-max 'analysis)

;;; EVT (min): a continuous function on [a,b] (a<=b) attains its minimum.
(add-to-pss 'extreme-value-min
  '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (<= a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
       (FORSOME c (AND (IN c (CCINT a b))
                  (FORALL x (IMPLIES (IN x (CCINT a b))
                    (<= (f c) (f x))))))))))))
(warrant! 'extreme-value-min 'reference
  "EVT (min form): apply extreme-value-max to -f; the argmax of -f is the argmin
   of f.")
(category! 'extreme-value-min 'analysis)

;;; Classic textbook names, for (find-theorem "...") lookup.
(alias! 'extreme-value-max "Extreme Value Theorem" "EVT" "Weierstrass extreme value theorem")
(alias! 'extreme-value-min "Extreme Value Theorem" "EVT")
