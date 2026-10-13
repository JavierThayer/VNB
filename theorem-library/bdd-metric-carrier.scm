;;; bdd-metric-carrier.scm -- BDD-METRIC keeps the point set, proven.
;;;
;;;     forall s.  PTS(BDD-METRIC(s)) == PTS(s)
;;;
;;; BDD-METRIC(s) is the def-functoid  (LIST (PTS s) (VNB-LAMBDA ...))
;;; (structure-library/bounded-metric.scm:33); its carrier slot is (PTS s)
;;; verbatim, so the statement is a slot read-off.  The support of the same
;;; name (bounded-metric.scm:38) is `well-known'.
;;;
;;; PLAN.  (di) (mac 'BDD-METRIC) (slot 'PTS) (nth-r) (slot 'PTS) (qrfl).
;;; `slot' on a LIST literal falls back to the accessor's own macete, which
;;; rewrites EVERY (PTS _) -- both sides -- to nth(1, _); `nth-r' reduces the
;;; literal side back to (PTS s), and the second `slot' brings that to the
;;; same normal form as the right side (product-metric-distance does the same).
;;;
;;; WINDOW.  Cites only the BDD-METRIC macete (structure-library/bounded-metric)
;;; and the PTS projection; lo = any theorem-library slot after driver-kit /
;;; proof-debt.  hi = theorem-library/bdd-metric-convergence, the earliest
;;; citer.
;;;
;;; Helper prefix: bmc- (none needed).

;;; R4-W2 2026-10-13: GUARDED by IS-METRIC-SPACE(s) (R4 report s.3, species (g),
;;; approved as drafted).  Unguarded the read-off is true but unprovable under the
;;; list doctrine: the tuple [PTS s, lambda] denotes only when PTS(s) is a set, and
;;; the certificate sees that only through a structure hypothesis on s.  With the
;;; guard, IS-METRIC-SPACE(s) certifies PTS(s) and the lambda's domain, so the
;;; `nth-r' below owes nothing.  Every citer works inside IS-METRIC-SPACE(s).
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s) (== (PTS (BDD-METRIC s)) (PTS s))))))
(dk-peel!)
(mac 'BDD-METRIC)         ; goal: (== (PTS (LIST (PTS s) (VNB-LAMBDA ...))) (PTS s))
(slot 'PTS)               ; goal: (== (nth 1 (LIST (PTS s) ...)) (nth 1 s))
(nth-r)                   ; goal: (== (PTS s) (nth 1 s))
(slot 'PTS)               ; goal: (== (nth 1 s) (nth 1 s))
(qrfl)
(qed 'bdd-metric-carrier)
(topic! 'bdd-metric-carrier 'constructions)
