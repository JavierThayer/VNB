;;; normed-ag-metric.scm -- the metric space underlying a normed abelian group.
;;;
;;; The structural bridge between a NORMED-AG's *group* register (CARR OPR IDEN INV
;;; + norm NRM) and its *metric* register (METRIC-SPACE : PTS DIST).  Like
;;; NF-METRIC-SPACE for normed fields, it cannot be a def-functor: a view-as
;;; maps slots to slots, but METRIC-SPACE's distance DIST is not a slot of a
;;; normed AG -- it is the *constructed* function d(u,v) = NRM(u - v).  So the
;;; bridge is a constructor functoid plus its laws.
;;;
;;;   NAG-METRIC-SPACE(nag) = [ CARR(nag),  lambda([u,v], NRM(nag)(u . INV(v))) ]
;;;
;;; The group is written multiplicatively, so the "difference" u - v is the
;;; group element  OPR(nag)(u, INV(nag)(v)) = u . v^-1.  Then
;;; NAG-METRIC-SPACE(nag) is a metric space whenever nag is a normed AG:
;;;   nonnegativity    -- norm >= 0;
;;;   point-separation -- d(u,v)=0 iff u.v^-1 = E iff u=v (norm definiteness);
;;;   symmetry         -- d(v,u)=||v.u^-1||=||(u.v^-1)^-1||=||u.v^-1||=d(u,v)
;;;                       (inverse-invariance of the group norm);
;;;   triangle         -- u.w^-1 = (u.v^-1).(v.w^-1), so ||u.w^-1|| <=
;;;                       ||u.v^-1|| + ||v.w^-1|| (norm subadditivity).
;;;
;;; This is what plugs a normed AG into the metric apparatus of
;;; metric-completeness.scm: "the normed AG grp is complete" is then just
;;; IS-COMPLETE(NAG-METRIC-SPACE grp), with IS-CAUCHY-SEQ / CONVERGES taken on
;;; the induced metric -- no separate completeness predicate needed.
;;;
;;; Bound vars u, v, w (NOT a/b/x/d): when this was written the carrier accessor
;;; was `A' and the metric accessors `X'/`D', which case-fold-collide with a/x/d,
;;; so element vars use u/v/w (the inverse-invariance convention) to avoid
;;; capture.  They are `CARR' and `PTS'/`DIST' now; the names are kept.
;;;
;;; Library-build phase: laws installed as `support' (accepted without proof),
;;; per [[feedback-library-axioms-fine]]; each carries an informal warrant.
;;; Derivations: nag-metric-distance by functoid-beta + nth-reduce +
;;; lambda-beta; nag-metric-space-is-metric-space by discharging the is-metric
;;; clauses from is-group-norm + the abelian-group laws (sketch above).
;;;
;;; Dependencies: normed-ag.scm (IS-NORMED-AG, NRM/OPR/INV/CARR), metric-space.scm
;;; (IS-METRIC-SPACE, PTS/DIST).

;;; -----------------------------------------------------------------------
;;; The constructor.

(def-functoid 'NAG-METRIC-SPACE '(nag)
  '(LIST (CARR nag)
         (VNB-LAMBDA (LIST u v) ((NRM nag) ((OPR nag) u ((INV nag) v))))))

;;; -----------------------------------------------------------------------
;;; Distance = norm of the (group) difference, on the carrier.

(support 'nag-metric-distance
  '(FORALL nag
     (IMPLIES (IS-NORMED-AG nag)
       (FORALL u (IMPLIES (IN u (CARR nag))
         (FORALL v (IMPLIES (IN v (CARR nag))
           (= ((DIST (NAG-METRIC-SPACE nag)) u v)
              ((NRM nag) ((OPR nag) u ((INV nag) v)))))))))))

(warrant! 'nag-metric-distance 'informal
  "By functoid-beta NAG-METRIC-SPACE(nag) = [CARR(nag), lambda([u,v],
   NRM(nag)(u . INV(v)))]; its D component is the 2nd list element (nth-reduce)
   and lambda-beta evaluates it at (u,v), giving NRM(nag)(OPR(nag)(u, INV(nag)
   v)) = ||u . v^-1||.")

;;; -----------------------------------------------------------------------
;;; Every normed AG carries a metric space.

(support 'nag-metric-space-is-metric-space
  '(FORALL nag
     (IMPLIES (IS-NORMED-AG nag)
       (IS-METRIC-SPACE (NAG-METRIC-SPACE nag)))))

(warrant! 'nag-metric-space-is-metric-space 'informal
  "The four is-metric clauses for d(u,v) = ||u . v^-1|| follow from
   is-group-norm plus the abelian-group laws: nonnegativity (norm >= 0);
   point-separation (d(u,v)=0 iff u.v^-1=E iff u=v, by norm definiteness);
   symmetry (v.u^-1 = (u.v^-1)^-1, so equal norm by inverse-invariance);
   triangle (u.w^-1 = (u.v^-1).(v.w^-1), so ||u.w^-1|| <= ||u.v^-1|| +
   ||v.w^-1|| by subadditivity).")

;;; -----------------------------------------------------------------------
;;; Carrier of the underlying metric space is the group's carrier.

(support 'nag-metric-carrier
  '(FORALL nag
     (== (PTS (NAG-METRIC-SPACE nag)) (CARR nag))))

(warrant! 'nag-metric-carrier 'informal
  "First component of the LIST constructor: by functoid-beta + nth-reduce,
   PTS(NAG-METRIC-SPACE nag) = CARR(nag).")
