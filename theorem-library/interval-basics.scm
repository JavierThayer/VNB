;;; interval-basics.scm -- INTERVAL's read-offs, PROVEN from its definition.
;;;
;;; INTERVAL(a,b) is a def-functoid (matrix.scm):  { i in NN : a <= i and i <= b }.
;;; Everything here follows by separation, and every one of these was asserted --
;;; interval-in-set with a warrant of kind `proof' that named no file.
;;;
;;; WHY THESE.  They are keystones.  Measured over the 252 bills:
;;;   interval-in-set     60      interval-elt-in-nn  26      interval-lo  25
;;; An asserted leaf cited by sixty proofs is worth sixty times one cited by one.
;;;
;;; THE OBSTACLE, AND THE WAY ROUND IT.  `def-functoid' installs only a rewrite
;;; MACETE, not a theorem.  So `mac' unfolds INTERVAL in a GOAL, but `mac-h'
;;; cannot unfold it in an ASSUMPTION -- it warns, no-ops, and the failure
;;; surfaces later as a sep-me against nothing.  Nor does `mac' reach into an
;;; IFF under a binder, so unfolding before splitting the IFF does not work.
;;;
;;; The way round is to make the definition CITABLE: prove the unfolding
;;; equation once -- the macete does apply to a goal that IS the equation --
;;; then every read-off `subst's its goal from the separation back to INTERVAL,
;;; where the hypothesis matches.  A general recipe for reading members out of
;;; any def-functoid, needing no new axiom.  The memory note on this trap
;;; recommends asserting the membership IFF as `definitional', which is sound
;;; but buys with a stipulation what a proof gets for nothing.

;;; ---- the definition, as a citable equation ----------------------------
;;; Stated `==' and in the SEP-first direction, both deliberately.  `rfl' carries
;;; a DEFINEDNESS side-condition since 2026-06-18, and a bare SEP term is not
;;; syntactically defined, so `= ' would owe a witness it does not need; `=='
;;; is unconditional and `qrfl' closes it.  SEP-first because that is the
;;; direction the read-offs `subst' in, and `subst' is ==-aware.
(sp (make-wff '(FORALL a (FORALL b
   (== (SEP i NN (AND (<= a i) (<= i b))) (INTERVAL a b))))))
(di)
(mac 'INTERVAL)
(qrfl)
(qed 'interval-unfold)
(topic! 'interval-unfold 'plumbing)

;;; ---- sethood: a subclass of NN ----------------------------------------
(sp (make-wff '(FORALL a (FORALL b (IN (INTERVAL a b) SET)))))
(di)
(mac 'INTERVAL)
(sep-set)
(ta 'nn-is-set)
(ass)
(qed 'interval-in-set)
(topic! 'interval-in-set 'plumbing)

;;; ---- the read-offs ----------------------------------------------------
;;; Each: pull the hypothesis across the unfolding equation into the separation,
;;; then sep-me reads both halves off it.
(define (ivl-sep) '(SEP i NN (AND (<= a i) (<= i b))))

(define (ivl-read-off!)
  (fact 'interval-unfold 'a 'b)                       ; (== SEP (INTERVAL a b))
  (have! (list 'IN 'i (ivl-sep))
    (lambda ()
      (subst (list '== (ivl-sep) '(INTERVAL a b)))    ; goal -> (IN i (INTERVAL a b))
      (ass)))
  (sep-me (list 'IN 'i (ivl-sep))))

(sp (make-wff '(FORALL a (FORALL b (FORALL i
   (IMPLIES (IN i (INTERVAL a b)) (IN i NN)))))))
(di) (di)
(ivl-read-off!)
(ass)
(qed 'interval-elt-in-nn)
(topic! 'interval-elt-in-nn 'plumbing)

(sp (make-wff '(FORALL a (FORALL b (FORALL i
   (IMPLIES (IN i (INTERVAL a b)) (<= a i)))))))
(di) (di)
(ivl-read-off!)
(dk-split! '(AND (<= a i) (<= i b)))
(ass)
(qed 'interval-lo)
(topic! 'interval-lo 'inequalities)

(sp (make-wff '(FORALL a (FORALL b (FORALL i
   (IMPLIES (IN i (INTERVAL a b)) (<= i b)))))))
(di) (di)
(ivl-read-off!)
(dk-split! '(AND (<= a i) (<= i b)))
(ass)
(qed 'interval-hi)
(topic! 'interval-hi 'inequalities)

;;; NOT PROVEN HERE: interval-card-in-nn (60 bills).  |INTERVAL(a,b)| in NN is
;;; the FINITENESS of an interval -- a cardinality fact, not a separation
;;; read-off.  It stays asserted, and after this file it is the largest single
;;; keystone left.
