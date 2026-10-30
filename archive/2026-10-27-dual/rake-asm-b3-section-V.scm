;;; =====================================================================
;;; (V) dual-is-normed-vector-space IS FALSE AS STATED.  DUAL(m)'s scalar slot holds the
;;;     7-tuple RR-NORMED-FIELD (dual-space.scm), while IS-NORMED-VECTOR-SPACE pins
;;;     scal(s) = normed-field-as-commutative-ring(rr-normed-field), a 6-tuple
;;;     (normed-vector-space.scm, the 2026-08-23 repair).  At m = RR-NVS
;;;     (rr-nvs-is-normed-vector-space) the support would give 7 = 6.
;;; =====================================================================
(sp (make-wff '(NOT (FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IS-NORMED-VECTOR-SPACE (DUAL m)))))))
(di)
(dk-cite! 'rr-nvs-is-normed-vector-space)
(rb3-apply! (dk-ctx-form '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IS-NORMED-VECTOR-SPACE (DUAL m))))) 'RR-NVS)
(dk-have! (list '= '(SCAL (DUAL RR-NVS)) rb3-R)
  (lambda () (mac-h 'is-normed-vector-space (dk-ctx-form '(IS-NORMED-VECTOR-SPACE (DUAL RR-NVS)))) (dk-split-all!) (ass)))
(dk-have! '(== (SCAL (DUAL RR-NVS)) RR-NORMED-FIELD)
  (lambda () (mac 'DUAL) (slot 'SCAL) (nth-r) (qrfl)))
(dk-have! '(= (LENGTH RR-NORMED-FIELD) 7)
  (lambda () (dk-cite! 'rr-is-normed-field) (mac-h 'is-normed-field '(IS-NORMED-FIELD RR-NORMED-FIELD)) (dk-split-all!) (ass)))
(dk-have! (list '= (list 'LENGTH rb3-R) 6)
  (lambda () (mac 'NORMED-FIELD-AS-COMMUTATIVE-RING) (len-r) (rfl)))
(dk-have! '(= (LENGTH (SCAL (DUAL RR-NVS))) 7)
  (lambda () (subst '(= (SCAL (DUAL RR-NVS)) RR-NORMED-FIELD)) (ass)))
(dk-have! '(= (LENGTH (SCAL (DUAL RR-NVS))) 6)
  (lambda () (subst (list '= '(SCAL (DUAL RR-NVS)) rb3-R)) (ass)))
(dk-have! '(= 7 6)
  (lambda () (subst '(= 7 (LENGTH (SCAL (DUAL RR-NVS))))) (ass)))
(dk-have! '(NOT (= 7 6)) (lambda () (arith)))
(rb3-prop! '(= 7 6) '(NOT (= 7 6)))
(rb3-qed! 'rb3-dual-is-normed-vector-space-false)
