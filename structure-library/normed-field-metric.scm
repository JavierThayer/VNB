;;; normed-field-metric.scm -- the metric space underlying a normed field.
;;;
;;; This is the structural bridge between the *field* register of RR/CC
;;; (RR-NORMED-FIELD, CC-NORMED-FIELD : NORMED-FIELD) and their *metric* register
;;; (RR-MS, CC-MS : METRIC-SPACE).  It cannot be a def-functor: a view-as
;;; maps slots to slots, but METRIC-SPACE's distance DIST is not a slot of a
;;; normed field -- it is the *constructed* function d(x,y) = FNRM(x - y).
;;; (Same reason views.scm cannot register NORMED-FIELD's multiplicative-
;;; group view.)  So the bridge is a constructor functoid plus its laws.
;;;
;;;   NF-METRIC-SPACE(nf) = [ CARR(nf),  lambda([x,y], FNRM(nf)(x - y)) ]
;;;
;;; where x - y is ADD(nf)(x, NEG(nf)(y)).  Then NF-METRIC-SPACE(nf) is a
;;; metric space whenever nf is a normed field: nonnegativity, point-
;;; separation and symmetry come from is-norm + the additive-group laws,
;;; and the triangle inequality from subadditivity of the norm.
;;;
;;; Concrete realizations (same carrier, same distance on the carrier):
;;;   NF-METRIC-SPACE(RR-NORMED-FIELD)  ~  RR-MS   (FNRM = abs)
;;;   NF-METRIC-SPACE(CC-NORMED-FIELD)  ~  CC-MS   (FNRM = magnitude)
;;; These are stated pointwise (nf-metric-distance), not as raw term
;;; equalities of the structures: the VNB-LAMBDA distance functions agree
;;; on CARR(nf) x CARR(nf) but their off-carrier behaviour is unconstrained, so a
;;; naked (= RR-MS (NF-METRIC-SPACE RR-NORMED-FIELD)) would lean on accidents of the
;;; lambda outside RR -- see [[project-representation-independence]].
;;;
;;; Library-build phase: laws installed as `support' (accepted without
;;; proof), per [[feedback-library-axioms-fine]].  Each is derivable:
;;; nf-metric-distance by functoid-beta + nth-reduce + lambda-beta;
;;; nf-metric-space-is-metric-space by discharging the is-metric clauses
;;; from is-norm + the additive abelian-group laws.
;;;
;;; Dependencies: normed-field.scm (IS-NORMED-FIELD, FNRM/ADD/NEG/CARR),
;;; metric-space.scm (IS-METRIC-SPACE, PTS/DIST).

;;; -----------------------------------------------------------------------
;;; The constructor.

;;; A CONSTRUCTED FUNCTOR, NORMED-FIELD -> METRIC-SPACE.  Not a def-functor: the
;;; distance is not a SLOT of a normed field, it is BUILT from the norm, so no
;;; correspondence of accessors can express this object map.  (The same will be
;;; true of METRIC-SPACE -> TOP-SPACE, whose topology is built from the metric.)
;;;
;;; Being constructed, it gets nothing for free.  It OWES two theorems, and
;;; def-constructed-functor records them rather than asserting them:
;;;   nf-metric-space-is-metric-space : IS-NORMED-FIELD(nf) => IS-METRIC-SPACE(NF-METRIC-SPACE nf)
;;;   nf-metric-space-functorial      : a normed-field hom is an ISOMETRY of the
;;;                                     induced metric spaces
;;; The first is discharged below (a warranted support).  The second is OPEN, and
;;; `functor-obligation-audit' says so at every load: a functor you have not
;;; proved is a functor you do not have.  Its content is real -- f preserves the
;;; norm and the field operations, so ||x - y|| = ||f x - f y|| -- but it needs
;;; the carrier-closure of x - y, so it is a proof, not a rewrite.
(def-constructed-functor 'NF-METRIC-SPACE 'NORMED-FIELD 'METRIC-SPACE '(nf)
  '(LIST (CARR nf)
         (VNB-LAMBDA (LIST x y) (CARTESIAN (CARR nf) (CARR nf))
                    ((FNRM nf) ((ADD nf) x ((NEG nf) y))))))

;;; -----------------------------------------------------------------------
;;; Distance = norm of the difference, on the carrier.

(support 'nf-metric-distance
  '(FORALL nf
     (IMPLIES (IS-NORMED-FIELD nf)
       (FORALL x (IMPLIES (IN x (CARR nf))
         (FORALL y (IMPLIES (IN y (CARR nf))
           (= ((DIST (NF-METRIC-SPACE nf)) x y)
              ((FNRM nf) ((ADD nf) x ((NEG nf) y)))))))))))

;;; -----------------------------------------------------------------------
;;; Every normed field is (carries) a metric space.

(support 'nf-metric-space-is-metric-space
  '(FORALL nf
     (IMPLIES (IS-NORMED-FIELD nf)
       (IS-METRIC-SPACE (NF-METRIC-SPACE nf)))))

;;; -----------------------------------------------------------------------
;;; Carrier of the underlying metric space is the field's carrier.

(support 'nf-metric-carrier
  '(FORALL nf
     (== (PTS (NF-METRIC-SPACE nf)) (CARR nf))))
