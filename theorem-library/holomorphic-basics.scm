;;; holomorphic-basics.scm -- the COMPLEX side of IS-DIFF-ON / HOLOMORPHIC-ON.
;;;
;;; theorem-library/diff-on-laws.scm did the real line: it proved that RR-MS and
;;; NF-METRIC-SPACE(RR-NORMED-FIELD) have the same points and the same distance
;;; values, and transported IS-OPEN and IS-CONTINUOUS-AT between them with the
;;; generic lemmas `ms-agree-{ball,open,continuous-at}'.  This file does the
;;; same for CC-MS and NF-METRIC-SPACE(CC-NORMED-FIELD), which is what turns
;;; HOLOMORPHIC-ON -- stated, by definition, over the normed field's own metric
;;; space -- into a statement in the CC-MS vocabulary the rest of the complex
;;; library speaks.
;;;
;;; Contents:
;;;   (1) the three missing applied slot equations of CC-NORMED-FIELD
;;;       (cc-nf-add-apply, cc-nf-mul-apply, cc-nf-neg-apply; the FNRM one is
;;;       already in diff-on-laws.scm as `cc-nf-fnrm-apply');
;;;   (2) nf-cc-is-metric-space, nf-cc-agree-pts, nf-cc-agree-dist;
;;;   (3) cc-ms-open-iff -- openness in one space iff in the other.  The header
;;;       of structure-library/diff-on.scm already names this theorem ("and
;;;       `cc-ms-open-iff' turns it into openness in CC-MS in one citation, in
;;;       either direction"); it did not exist until now;
;;;   (4) cc-nf-small-elements -- CC has nonzero elements of arbitrarily small
;;;       modulus.  This is the non-triviality hypothesis `diff-on-unique' needs
;;;       (diff-on.scm:44 names it), and what makes every point of an open set
;;;       a limit point of it;
;;;   (5) holomorphic-on-iff-cc-ms -- HOLOMORPHIC-ON read with IS-OPEN in CC-MS,
;;;       and the one-way read-off holomorphic-on-open-cc-ms.
;;;
;;; NOT HERE: "constants and the identity are holomorphic".  Those are instances
;;; of the derivative laws over a normed field (constants, identity, sum,
;;; product, chain rule), which are agent 13-A's STAGE 2 and are not in the tree
;;; as this is written.  When theorem-library/diff-on-laws-2.scm lands, each is
;;; one citation of the generic law at K = CC-NORMED-FIELD; nothing here has to
;;; change.
;;;
;;; LOAD WINDOW.  Lower bound: theorem-library/diff-on-laws (position 556 --
;;; ms-agree-*, cc-nf-carr, cc-nf-zero, cc-nf-fnrm-apply), which in turn is
;;; below rake-nf-norm (555, nf-metric-space-is-metric-space).  Also needed and
;;; all well below it: theorem-library/cc-normed-field (the new file, slotted
;;; right after cc-magnitude at 455), cc-metric-space-proof (456,
;;; cc-is-metric-space), dominated-convergence (469, cc-ms-dist), cc-magnitude
;;; (455, rr-magnitude-is-abs), rr-abs-basics (189, rr-abs-of-nonneg),
;;; rr-order-basics (186, rr-pos-ne-zero), pos-rr-bridges and rr-halving (for
;;; dk-halve!).  Upper bound: none -- nothing in the tree cites any of these
;;; names yet.  The natural slot is IMMEDIATELY AFTER theorem-library/
;;; diff-on-laws.
;;;
;;; Helper prefix: hbz-.
;;;
;;; Dependencies: structure-library/diff-on.scm, normed-field-metric.scm,
;;; complex.scm (CC-MS), numeric-instances.scm (CC-NORMED-FIELD).

(define (hbz-head e) (and (pair? e) (car e)))

(define hbz-m '(NF-METRIC-SPACE CC-NORMED-FIELD))

;;; The two agreement predicates, spelled exactly as `ms-agree-*' spells them
;;; (diff-on-laws.scm's `dfo-agree-pts' / `dfo-agree-dist'; those are local to
;;; that file's private environment, so they are rebuilt here).  `b' is the
;;; space a fact is wanted IN, `a' the space it is known about.
(define (hbz-agree-pts b a) (list '== (list 'PTS b) (list 'PTS a)))
(define (hbz-agree-dist b a)
  (list 'FORALL 'dfu_
    (list 'IMPLIES (list 'IN 'dfu_ (list 'PTS a))
      (list 'FORALL 'dfv_
        (list 'IMPLIES (list 'IN 'dfv_ (list 'PTS a))
          (list '== (list (list 'DIST b) 'dfu_ 'dfv_)
                    (list (list 'DIST a) 'dfu_ 'dfv_)))))))

;;; =====================================================================
;;; (1) THE APPLIED SLOT EQUATIONS OF CC-NORMED-FIELD.
;;;
;;; Each is the slot equation (through `slot', the one door) plus one beta on
;;; arguments the guard has already typed -- the same three lines
;;; diff-on-laws.scm spends on rr-nf-add-apply and its siblings.
;;; =====================================================================

(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ CC) (IN v_ CC))
                '(== ((ADD CC-NORMED-FIELD) u_ v_) (+ u_ v_)))))
(dk-peel!)
(slot 'ADD)
(lam-b)
(qrfl)
(qed 'cc-nf-add-apply)
(topic! 'cc-nf-add-apply 'algebra)
(alias! 'cc-nf-add-apply "addition in the complex normed field is numeric addition")

(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ CC) (IN v_ CC))
                '(== ((MUL CC-NORMED-FIELD) u_ v_) (* u_ v_)))))
(dk-peel!)
(slot 'MUL)
(lam-b)
(qrfl)
(qed 'cc-nf-mul-apply)
(topic! 'cc-nf-mul-apply 'algebra)
(alias! 'cc-nf-mul-apply "multiplication in the complex normed field is numeric multiplication")

(sp (make-wff (forall-guarded '(u_) '((IN u_ CC))
                '(== ((NEG CC-NORMED-FIELD) u_) (- u_)))))
(dk-peel!)
(slot 'NEG)
(lam-b)
(qrfl)
(qed 'cc-nf-neg-apply)
(topic! 'cc-nf-neg-apply 'algebra)
(alias! 'cc-nf-neg-apply "negation in the complex normed field is numeric negation")

;;; The difference in CC-NORMED-FIELD's operations is the numeric difference.
(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ CC) (IN v_ CC))
                '(== ((ADD CC-NORMED-FIELD) u_ ((NEG CC-NORMED-FIELD) v_)) (- u_ v_)))))
(dk-peel!)
(fact 'cc-nf-neg-apply 'v_)
(fact 'cc-neg-closed 'v_)
(subst '(== ((NEG CC-NORMED-FIELD) v_) (- v_)))
(dk-have! '(AND (IN u_ CC) (IN (- v_) CC)))
(fact 'cc-nf-add-apply 'u_ '(- v_))
(subst '(== ((ADD CC-NORMED-FIELD) u_ (- v_)) (+ u_ (- v_))))
(mac 'binary-minus-def)
(qrfl)
(qed 'cc-nf-sub)
(topic! 'cc-nf-sub 'algebra)
(alias! 'cc-nf-sub "the difference in the complex normed field is the numeric difference")

;;; =====================================================================
;;; (2) THE COMPLEX PLANE IN ITS TWO REGISTERS.
;;;
;;; CC-MS (complex.scm) and NF-METRIC-SPACE(CC-NORMED-FIELD) are NOT the same
;;; term -- CC-MS's distance lambda has the body magnitude(x - y), the normed
;;; field's has FNRM(nf)(ADD(nf)(x, NEG(nf) y)) -- and they must not be asserted
;;; equal: a naked equation between the tuples would lean on the two lambdas
;;; agreeing OFF the carrier, where nothing constrains them.  What is true, and
;;; all that is ever needed, is the same POINTS and the same DISTANCE VALUES on
;;; those points.
;;; =====================================================================

(sp (make-wff (list 'IS-METRIC-SPACE hbz-m)))
(fact 'cc-is-normed-field)
(fact 'nf-metric-space-is-metric-space 'CC-NORMED-FIELD)
(ass)
(qed 'nf-cc-is-metric-space)
(topic! 'nf-cc-is-metric-space 'analysis)
(alias! 'nf-cc-is-metric-space
        "the metric space of the complex normed field is a metric space")

(sp (make-wff (hbz-agree-pts hbz-m 'CC-MS)))
(fact 'nf-metric-carrier 'CC-NORMED-FIELD)
(subst (list '== (list 'PTS hbz-m) '(CARR CC-NORMED-FIELD)))
(slot 'CARR)
(slot 'PTS)
(qrfl)
(qed 'nf-cc-agree-pts)
(topic! 'nf-cc-agree-pts 'analysis)
(alias! 'nf-cc-agree-pts
        "the complex normed field's metric space has the points of CC-MS")

(sp (make-wff (hbz-agree-dist hbz-m 'CC-MS)))
(dk-peel!)
(dk-have! '(== (PTS CC-MS) CC) (lambda () (slot 'PTS) (qrfl)))
(dk-have! '(IN dfu_ CC) (lambda () (subst '(== CC (PTS CC-MS))) (ass)))
(dk-have! '(IN dfv_ CC) (lambda () (subst '(== CC (PTS CC-MS))) (ass)))
(fact 'cc-nf-carr)
(dk-have! '(IN dfu_ (CARR CC-NORMED-FIELD))
          (lambda () (subst '(== (CARR CC-NORMED-FIELD) CC)) (ass)))
(dk-have! '(IN dfv_ (CARR CC-NORMED-FIELD))
          (lambda () (subst '(== (CARR CC-NORMED-FIELD) CC)) (ass)))
(fact 'cc-is-normed-field)
(fact 'nf-metric-distance 'CC-NORMED-FIELD 'dfu_ 'dfv_)
(fact 'cc-neg-closed 'dfv_)
(dk-have! '(AND (IN dfu_ CC) (IN (- dfv_) CC)))
(fact 'cc-add-closed 'dfu_ '(- dfv_))
(fact 'cc-nf-neg-apply 'dfv_)
(fact 'cc-nf-add-apply 'dfu_ '(- dfv_))
(fact 'cc-nf-fnrm-apply '(+ dfu_ (- dfv_)))
(fact 'cc-ms-dist 'dfu_ 'dfv_)
(subst (list '== (list (list 'DIST hbz-m) 'dfu_ 'dfv_)
                 '((FNRM CC-NORMED-FIELD) ((ADD CC-NORMED-FIELD) dfu_ ((NEG CC-NORMED-FIELD) dfv_)))))
(subst '(== ((NEG CC-NORMED-FIELD) dfv_) (- dfv_)))
(subst '(== ((ADD CC-NORMED-FIELD) dfu_ (- dfv_)) (+ dfu_ (- dfv_))))
(subst '(== ((FNRM CC-NORMED-FIELD) (+ dfu_ (- dfv_))) (magnitude (+ dfu_ (- dfv_)))))
(subst '(== ((DIST CC-MS) dfu_ dfv_) (magnitude (- dfu_ dfv_))))
(mac 'binary-minus-def)
(qrfl)
(qed 'nf-cc-agree-dist)
(topic! 'nf-cc-agree-dist 'analysis)
(alias! 'nf-cc-agree-dist
        "the complex normed field's metric agrees with the CC-MS distance")

;;; =====================================================================
;;; (3) OPENNESS, IN EITHER SPACE.
;;; =====================================================================

;;; The four agreement facts, both ways round, as the context wants them.
(define (hbz-agreements!)
  (fact 'nf-cc-agree-pts)
  (fact 'nf-cc-agree-dist)
  (fact 'ms-agree-pts-sym 'CC-MS hbz-m)
  (fact 'ms-agree-dist-sym 'CC-MS hbz-m))

(sp (make-wff (list 'FORALL 'hbw_
     (list 'IFF (list 'IS-OPEN hbz-m 'hbw_) '(IS-OPEN CC-MS hbw_)))))
(di)
(fact 'cc-is-metric-space)
(fact 'nf-cc-is-metric-space)
(hbz-agreements!)
(dk-iff!
 (lambda (g) (equal? (cadr g) 'CC-MS))
 (lambda ()                             ; IS-OPEN(nf) |- IS-OPEN(CC-MS)
   (fact 'ms-agree-open hbz-m 'CC-MS 'hbw_)
   (ass))
 (lambda ()                             ; IS-OPEN(CC-MS) |- IS-OPEN(nf)
   (fact 'ms-agree-open 'CC-MS hbz-m 'hbw_)
   (ass)))
(qed 'cc-ms-open-iff)
(topic! 'cc-ms-open-iff 'topology)
(alias! 'cc-ms-open-iff
        "a set is open in the complex normed field's metric iff it is open in CC-MS")

;;; =====================================================================
;;; (4) CC HAS NONZERO ELEMENTS OF ARBITRARILY SMALL MODULUS.
;;;
;;; The witness is REAL: eps/2, which is in CC by rr-subset-cc and whose
;;; modulus is its absolute value (rr-magnitude-is-abs), i.e. itself.  This is
;;; the non-triviality hypothesis of `diff-on-unique' (diff-on.scm:44) and what
;;; makes every point of an open subset of CC a limit point of it.
;;; =====================================================================

(sp (make-wff '(FORALL eps (IMPLIES (POS-RR eps)
     (FORSOME h (AND (IN h (CARR CC-NORMED-FIELD))
                (AND (NOT (= h (ZERO CC-NORMED-FIELD)))
                     (< ((FNRM CC-NORMED-FIELD) h) eps))))))))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'eps)
(fact 'rr-lt-of-pos-rr 'eps)
(let ((hbz-d (dk-halve! 'eps)))
  (fact 'rr-subset-cc hbz-d)
  (fact 'cc-nf-carr)
  (dk-have! (list 'IN hbz-d '(CARR CC-NORMED-FIELD))
            (lambda () (subst '(== (CARR CC-NORMED-FIELD) CC)) (ass)))
  (fact 'cc-nf-zero)
  (fact 'rr-pos-ne-zero hbz-d)
  (dk-have! (list 'NOT (list '= hbz-d '(ZERO CC-NORMED-FIELD)))
            (lambda () (subst '(== (ZERO CC-NORMED-FIELD) 0)) (ass)))
  (fact 'cc-nf-fnrm-apply hbz-d)
  (fact 'rr-magnitude-is-abs hbz-d)
  (dk-have! (list '<= 0 hbz-d) (lambda () (dk-ineq! (list '< 0 hbz-d))))
  (fact 'rr-abs-of-nonneg hbz-d)
  (dk-have! (list '< (list '(FNRM CC-NORMED-FIELD) hbz-d) 'eps)
            (lambda ()
              (subst (list '== (list '(FNRM CC-NORMED-FIELD) hbz-d)
                               (list 'magnitude hbz-d)))
              (subst (list '== (list 'magnitude hbz-d) (list 'abs hbz-d)))
              (subst (list '== (list 'abs hbz-d) hbz-d))
              (dk-ineq! (list '< 0 hbz-d) (list '= (list '+ hbz-d hbz-d) 'eps))))
  (ew hbz-d))
(dk-conj-close! (lambda () (ass)))
(qed 'cc-nf-small-elements)
(topic! 'cc-nf-small-elements 'analysis)
(alias! 'cc-nf-small-elements
        "the complex numbers have nonzero elements of arbitrarily small modulus")

;;; =====================================================================
;;; (5) HOLOMORPHY, READ IN CC-MS VOCABULARY.
;;;
;;; HOLOMORPHIC-ON states its openness conjunct over NF-METRIC-SPACE(CC-NORMED-
;;; FIELD), because that is the space IS-DIFF-ON itself speaks of.  Every other
;;; complex statement in the library says CC-MS.  These two theorems are the
;;; single citation between them.
;;; =====================================================================

(sp (make-wff '(FORALL U (FORALL f (IMPLIES (HOLOMORPHIC-ON U f)
     (IS-OPEN CC-MS U))))))
(dk-peel!)
(fact 'holomorphic-on-open 'U 'f)
(fact 'cc-ms-open-iff 'U)
(prop)
(qed 'holomorphic-on-open-cc-ms)
(topic! 'holomorphic-on-open-cc-ms 'analysis)
(alias! 'holomorphic-on-open-cc-ms "a holomorphic function's domain is open in CC-MS")

(sp (make-wff '(FORALL U (FORALL f (IFF (HOLOMORPHIC-ON U f)
     (AND (IS-OPEN CC-MS U)
      (AND (IN f (FUN U CC))
           (FORALL a (IMPLIES (IN a U)
             (FORSOME L (IS-DIFF-ON CC-NORMED-FIELD U f a L)))))))))))
(dk-peel!)
(fact 'cc-ms-open-iff 'U)
(dk-iff!
 (lambda (g) (eq? (hbz-head g) 'AND))
 (lambda ()                             ; HOLOMORPHIC-ON |- the CC-MS reading
   (mac-h 'HOLOMORPHIC-ON '(HOLOMORPHIC-ON U f))
   (dk-split-all!)
   (dk-conj-close!
    (lambda ()
      (if (eq? (hbz-head (dk-goal)) 'IS-OPEN) (prop) (ass)))))
 (lambda ()                             ; the CC-MS reading |- HOLOMORPHIC-ON
   (dk-split-all!)
   (mac 'HOLOMORPHIC-ON)
   (dk-conj-close!
    (lambda ()
      (if (eq? (hbz-head (dk-goal)) 'IS-OPEN) (prop) (ass))))))
(qed 'holomorphic-on-iff-cc-ms)
(topic! 'holomorphic-on-iff-cc-ms 'analysis)
(alias! 'holomorphic-on-iff-cc-ms
        "holomorphy, with its domain's openness read in CC-MS")
