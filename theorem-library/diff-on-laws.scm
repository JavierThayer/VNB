;;; diff-on-laws.scm -- the laws of IS-DIFF-ON / DERIV-ON / HOLOMORPHIC-ON
;;; (structure-library/diff-on.scm).  Everything here is PROVEN; the definition
;;; file asserts nothing.
;;;
;;; Helper prefix: dfo-.
;;;
;;; Dependencies: structure-library/diff-on.scm, metric-subspace.scm and
;;; theorem-library/metric-subspace-laws.scm (SUBSPACE-MS and its laws),
;;; normed-field-metric.scm, rake-nf-norm.scm (nf-metric-space-is-metric-space),
;;; rake-open-sets.scm (carrier-is-open), normed-field-ring-view.scm.

;;; ---- file-local driver helpers --------------------------------------

(define (dfo-head e) (and (pair? e) (car e)))

;;; The IS-DIFF-ON hypothesis, as the context spells it.
(define dfo-hyp '(IS-DIFF-ON K U f a L))

;;; A READ-OFF of one conjunct of IS-DIFF-ON.  The unfold is destructive, which
;;; is why each of these is its own theorem: a later proof cites the conjunct it
;;; needs and keeps the hypothesis.
(define (dfo-readoff! name concl)
  (sp (make-wff (list 'FORALL 'K (list 'FORALL 'U (list 'FORALL 'f
                  (list 'FORALL 'a (list 'FORALL 'L
                    (list 'IMPLIES dfo-hyp concl))))))))
  (dk-peel!)
  (mac-h 'IS-DIFF-ON dfo-hyp)
  (dk-split-all!)
  (ass)
  (if (not (proof-done? *ps*))
      (error "dfo-readoff!: proof did not close" name (dk-goal)))
  (qed name))

;;; An INSTANCE slot read-off: ACC(INST) == VAL, by the instance's own value
;;; macete (`slot' is the one door -- CLAUDE.md, "Structures and views").
(define (dfo-slot! name acc inst val)
  (sp (make-wff (list '== (list acc inst) val)))
  (slot acc)
  (qrfl)
  (if (not (proof-done? *ps*))
      (error "dfo-slot!: proof did not close" name (dk-goal)))
  (qed name))

;;; =====================================================================
;;; (1) THE READ-OFFS OF IS-DIFF-ON.
;;; =====================================================================

(dfo-readoff! 'diff-on-normed-field '(IS-NORMED-FIELD K))
(topic! 'diff-on-normed-field 'analysis)
(alias! 'diff-on-normed-field "a derivative on a set is taken over a normed field")

(dfo-readoff! 'diff-on-open '(IS-OPEN (NF-METRIC-SPACE K) U))
(topic! 'diff-on-open 'analysis)
(alias! 'diff-on-open "the domain of a derivative on a set is open")

(dfo-readoff! 'diff-on-in-fun '(IN f (FUN U (CARR K))))
(topic! 'diff-on-in-fun 'analysis)
(alias! 'diff-on-in-fun "a function differentiable on U is a function on U")

(dfo-readoff! 'diff-on-pt-in '(IN a U))
(topic! 'diff-on-pt-in 'analysis)
(alias! 'diff-on-pt-in "the point of differentiation lies in the domain")

(dfo-readoff! 'diff-on-deriv-in-carr '(IN L (CARR K)))
(topic! 'diff-on-deriv-in-carr 'analysis)
(alias! 'diff-on-deriv-in-carr "a derivative is an element of the field")

;;; =====================================================================
;;; (2) THE DOMAIN LIES IN THE CARRIER.  IS-OPEN(M, U) gives SUBSET U (PTS M),
;;; and PTS(NF-METRIC-SPACE K) == CARR K unconditionally (nf-metric-carrier).
;;; =====================================================================
(sp (make-wff '(FORALL K (FORALL U
     (IMPLIES (IS-OPEN (NF-METRIC-SPACE K) U) (SUBSET U (CARR K)))))))
(dk-peel!)
(mac-h 'IS-OPEN '(IS-OPEN (NF-METRIC-SPACE K) U))
(dk-split-all!)
(fact 'nf-metric-carrier 'K)
(subst '(== (CARR K) (PTS (NF-METRIC-SPACE K))))
(ass)
(qed 'nf-open-subset-carr)
(topic! 'nf-open-subset-carr 'analysis)
(alias! 'nf-open-subset-carr "an open set of a normed field lies in its carrier")

;;; =====================================================================
;;; (3) THE VALUE TYPING.  f(x) in CARR K for x in U.
;;; =====================================================================
(sp (make-wff (list 'FORALL 'K (list 'FORALL 'U (list 'FORALL 'f
     (list 'FORALL 'a (list 'FORALL 'L
       (list 'IMPLIES dfo-hyp
         (forall-guarded '(dfx_) '((IN dfx_ U))
                         '(IN (f dfx_) (CARR K)))))))))))
(dk-peel!)
(fact 'diff-on-in-fun 'K 'U 'f 'a 'L)
(fact 'fun-apply-type-c 'f 'U '(CARR K) 'dfx_)
(ass)
(qed 'diff-on-value-in-carr)
(topic! 'diff-on-value-in-carr 'analysis)
(alias! 'diff-on-value-in-carr "a function differentiable on U takes values in the field")

;;; =====================================================================
;;; (4) THE NUMERIC INSTANCES, SLOT BY SLOT.  These are what the bridge
;;; theorem and the two non-triviality lemmas read RR and CC through.
;;; =====================================================================

(dfo-slot! 'rr-nf-carr 'CARR 'RR-NORMED-FIELD 'RR)
(topic! 'rr-nf-carr 'algebra)

(dfo-slot! 'cc-nf-carr 'CARR 'CC-NORMED-FIELD 'CC)
(topic! 'cc-nf-carr 'algebra)

(dfo-slot! 'rr-nf-add 'ADD 'RR-NORMED-FIELD
           '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (+ x_ y_)))
(topic! 'rr-nf-add 'algebra)

(dfo-slot! 'rr-nf-mul 'MUL 'RR-NORMED-FIELD
           '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (* x_ y_)))
(topic! 'rr-nf-mul 'algebra)

(dfo-slot! 'rr-nf-neg 'NEG 'RR-NORMED-FIELD '(VNB-LAMBDA x_ RR (- x_)))
(topic! 'rr-nf-neg 'algebra)

(dfo-slot! 'rr-nf-fnrm 'FNRM 'RR-NORMED-FIELD '(VNB-LAMBDA x_ RR (abs x_)))
(topic! 'rr-nf-fnrm 'algebra)

(dfo-slot! 'cc-nf-fnrm 'FNRM 'CC-NORMED-FIELD '(VNB-LAMBDA x_ CC (magnitude x_)))
(topic! 'cc-nf-fnrm 'algebra)

(dfo-slot! 'cc-nf-zero 'ZERO 'CC-NORMED-FIELD 0)
(topic! 'cc-nf-zero 'algebra)

(dfo-slot! 'rr-nf-zero 'ZERO 'RR-NORMED-FIELD 0)
(topic! 'rr-nf-zero 'algebra)

;;; The applied forms.  Each is the slot equation plus one beta on arguments
;;; already typed by the guard.
(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ RR) (IN v_ RR))
                '(== ((ADD RR-NORMED-FIELD) u_ v_) (+ u_ v_)))))
(dk-peel!)
(slot 'ADD)
(lam-b)
(qrfl)
(qed 'rr-nf-add-apply)
(topic! 'rr-nf-add-apply 'algebra)

(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ RR) (IN v_ RR))
                '(== ((MUL RR-NORMED-FIELD) u_ v_) (* u_ v_)))))
(dk-peel!)
(slot 'MUL)
(lam-b)
(qrfl)
(qed 'rr-nf-mul-apply)
(topic! 'rr-nf-mul-apply 'algebra)

(sp (make-wff (forall-guarded '(u_) '((IN u_ RR))
                '(== ((NEG RR-NORMED-FIELD) u_) (- u_)))))
(dk-peel!)
(slot 'NEG)
(lam-b)
(qrfl)
(qed 'rr-nf-neg-apply)
(topic! 'rr-nf-neg-apply 'algebra)

(sp (make-wff (forall-guarded '(u_) '((IN u_ RR))
                '(== ((FNRM RR-NORMED-FIELD) u_) (abs u_)))))
(dk-peel!)
(slot 'FNRM)
(lam-b)
(qrfl)
(qed 'rr-nf-fnrm-apply)
(topic! 'rr-nf-fnrm-apply 'algebra)

(sp (make-wff (forall-guarded '(u_) '((IN u_ CC))
                '(== ((FNRM CC-NORMED-FIELD) u_) (magnitude u_)))))
(dk-peel!)
(slot 'FNRM)
(lam-b)
(qrfl)
(qed 'cc-nf-fnrm-apply)
(topic! 'cc-nf-fnrm-apply 'algebra)

;;; =====================================================================
;;; (5) TWO METRIC SPACES THAT AGREE.
;;;
;;; The bridge of the design note (s.3.3) needs to move `IS-OPEN' and
;;; `IS-CONTINUOUS-AT' between RR-MS and NF-METRIC-SPACE(RR-NORMED-FIELD).
;;; Those two structures are NOT the same TERM -- RR-MS's distance lambda has
;;; the body abs(x - y) and the normed field's has FNRM(nf)(ADD(nf)(x, NEG(nf)
;;; y)) -- and they must not be asserted equal: a naked equation between the
;;; tuples would lean on the two lambdas agreeing OFF the carrier, where nothing
;;; constrains them (structure-library/normed-field-metric.scm says so).  What
;;; is true, and all that is ever needed, is that they have the SAME POINTS and
;;; the SAME DISTANCE VALUES on those points.
;;;
;;; So the transport is proved once, generically, as three lemmas about a pair
;;; of spaces that agree in that sense.  `msa_' is the space a fact is known
;;; about, `msb_' the space it is wanted in.  The hypotheses are curried, so
;;; `fact' detaches them one at a time (CLAUDE.md: `fact' will not split a
;;; CONJUNCTIVE antecedent).
;;; =====================================================================

;;; The two agreement hypotheses, as the statements spell them.
(define (dfo-agree-pts b a) (list '== (list 'PTS b) (list 'PTS a)))
(define (dfo-agree-dist b a)
  (list 'FORALL 'dfu_
    (list 'IMPLIES (list 'IN 'dfu_ (list 'PTS a))
      (list 'FORALL 'dfv_
        (list 'IMPLIES (list 'IN 'dfv_ (list 'PTS a))
          (list '== (list (list 'DIST b) 'dfu_ 'dfv_)
                    (list (list 'DIST a) 'dfu_ 'dfv_)))))))

;;; (5a) THE BALLS COINCIDE.  `ball-membership' is unguarded, so no
;;; IS-METRIC-SPACE hypothesis is needed here.
(sp (make-wff
     (list 'FORALL 'msa_ (list 'FORALL 'msb_
       (list 'IMPLIES '(IS-METRIC-SPACE msa_)
        (list 'IMPLIES '(IS-METRIC-SPACE msb_)
         (list 'IMPLIES (dfo-agree-pts 'msb_ 'msa_)
          (list 'IMPLIES (dfo-agree-dist 'msb_ 'msa_)
           (list 'FORALL 'dfc_
             (list 'IMPLIES '(IN dfc_ (PTS msa_))
               (list 'FORALL 'dfr_
                 '(= (BALL msb_ dfc_ dfr_) (BALL msa_ dfc_ dfr_)))))))))))))
(dk-peel!)
(fact 'ball-is-set 'msb_ 'dfc_ 'dfr_)
(fact 'ball-is-set 'msa_ 'dfc_ 'dfr_)
(have! '(FORALL dfz_ (IFF (IN dfz_ (BALL msb_ dfc_ dfr_))
                          (IN dfz_ (BALL msa_ dfc_ dfr_))))
  (lambda ()
    (di)
    (mac 'ball-membership)              ; both ball atoms at once
    (subst '(== (PTS msb_) (PTS msa_)))
    (use-em '(IN dfz_ (PTS msa_))
      (lambda ()
        (dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                              (dk-contains? fm 'DIST)))
                            "the distance-agreement universal")
                   'dfc_ 'dfz_)
        (subst '(== ((DIST msb_) dfc_ dfz_) ((DIST msa_) dfc_ dfz_)))
        (prop))
      (lambda () (prop)))))
(fact 'class-extensionality '(BALL msb_ dfc_ dfr_) '(BALL msa_ dfc_ dfr_))
(ass)
(qed 'ms-agree-ball)
(topic! 'ms-agree-ball 'topology)
(alias! 'ms-agree-ball "spaces with the same points and distances have the same balls")

;;; (5b) OPENNESS TRANSFERS.
(sp (make-wff
     (list 'FORALL 'msa_ (list 'FORALL 'msb_
       (list 'IMPLIES '(IS-METRIC-SPACE msb_)
         (list 'IMPLIES (dfo-agree-pts 'msb_ 'msa_)
           (list 'IMPLIES (dfo-agree-dist 'msb_ 'msa_)
             (list 'FORALL 'dfw_
               (list 'IMPLIES '(IS-OPEN msa_ dfw_)
                              '(IS-OPEN msb_ dfw_))))))))))
(dk-peel!)
(mac-h 'IS-OPEN '(IS-OPEN msa_ dfw_))
(dk-split-all!)
(mac 'IS-OPEN)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (dfo-head g) 'IS-METRIC-SPACE) (ass))
       ((eq? (dfo-head g) 'SUBSET) (subst '(== (PTS msb_) (PTS msa_))) (ass))
       (#t
        (let ((y (dk-di-var!)))
          (fact 'subset-mem-fwd 'dfw_ '(PTS msa_) y)
          (let* ((univ (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                  (dk-contains? fm 'POS-RR)))
                                "the open-set ball witness"))
                 (ex   (dk-apply! univ y))
                 (r    (dk-skolem! ex)))
            (ew r)
            (dk-conj-close!
             (lambda ()
               (if (eq? (dfo-head (dk-goal)) 'POS-RR)
                   (ass)
                   (begin
                     (fact 'ms-agree-ball 'msa_ 'msb_ y r)
                     (subst (list '= (list 'BALL 'msb_ y r) (list 'BALL 'msa_ y r)))
                     (ass)))))))))))) 
(qed 'ms-agree-open)
(topic! 'ms-agree-open 'topology)
(alias! 'ms-agree-open "spaces with the same points and distances have the same open sets")

;;; (5c) CONTINUITY AT A POINT TRANSFERS.  Domain and codomain are each replaced
;;; by an agreeing space; the SAME delta serves.
(sp (make-wff
     (list 'FORALL 'msa_ (list 'FORALL 'msb_ (list 'FORALL 'mta_ (list 'FORALL 'mtb_
       (list 'FORALL 'dfg_ (list 'FORALL 'dfp_
         (list 'IMPLIES '(IS-METRIC-SPACE msb_)
           (list 'IMPLIES '(IS-METRIC-SPACE mtb_)
             (list 'IMPLIES (dfo-agree-pts 'msb_ 'msa_)
               (list 'IMPLIES (dfo-agree-pts 'mtb_ 'mta_)
                 (list 'IMPLIES (dfo-agree-dist 'msb_ 'msa_)
                   (list 'IMPLIES (dfo-agree-dist 'mtb_ 'mta_)
                     (list 'IMPLIES '(IS-CONTINUOUS-AT msa_ mta_ dfg_ dfp_)
                                    '(IS-CONTINUOUS-AT msb_ mtb_ dfg_ dfp_))))))))))))))))
(define dfo-c-landed (dk-peel!))
(define dfo-c-dom
  (dk-pick (lambda (fm) (and (member fm dfo-c-landed) (dk-contains? fm 'msb_)
                             (eq? (dfo-head fm) 'FORALL)))
           "the domain distance-agreement universal"))
(define dfo-c-cod
  (dk-pick (lambda (fm) (and (member fm dfo-c-landed) (dk-contains? fm 'mtb_)
                             (eq? (dfo-head fm) 'FORALL)))
           "the codomain distance-agreement universal"))
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT msa_ mta_ dfg_ dfp_))
(dk-split-all!)
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (dfo-head g) 'IS-METRIC-SPACE) (ass))
       ((and (eq? (dfo-head g) 'IN) (pair? (caddr g)) (eq? (car (caddr g)) 'FUN))
        (subst '(== (PTS msb_) (PTS msa_)))
        (subst '(== (PTS mtb_) (PTS mta_)))
        (ass))
       ((eq? (dfo-head g) 'IN) (subst '(== (PTS msb_) (PTS msa_))) (ass))
       (#t
        (let* ((peeled (dk-peel!))
               (eps (cadr (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'POS-RR)
                                                     (member fm peeled)))
                                   "POS-RR eps")))
               (univ (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                (dk-contains? fm 'POS-RR)
                                                (dk-contains? fm 'FORSOME)))
                              "the eps universal"))
               (ex   (dk-apply! univ eps))
               (del  (dk-skolem! ex)))
          (ew del)
          (dk-conj-close!
           (lambda ()
             (if (eq? (dfo-head (dk-goal)) 'POS-RR)
                 (ass)
                 (begin
                   (let* ((landed2 (dk-peel!))
                          (bty (or (find-first
                                    (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN)
                                                      (equal? (caddr fm) '(PTS msb_))))
                                    landed2)
                                   (error "ms-agree-continuous-at: no typing for b")))
                          (b  (cadr bty)))
                     (dk-have! (list 'IN b '(PTS msa_))
                       (lambda () (subst '(== (PTS msa_) (PTS msb_))) (ass)))
                     (dk-apply! dfo-c-dom 'dfp_ b)
                     (dk-have! (list '<= (list '(DIST msa_) 'dfp_ b) del)
                       (lambda ()
                         (subst (list '== (list '(DIST msa_) 'dfp_ b)
                                           (list '(DIST msb_) 'dfp_ b)))
                         (ass)))
                     (dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                           (dk-contains? fm del)))
                                         "the delta universal")
                                b)
                     (fact 'fun-apply-type-c 'dfg_ '(PTS msa_) '(PTS mta_) 'dfp_)
                     (fact 'fun-apply-type-c 'dfg_ '(PTS msa_) '(PTS mta_) b)
                     (dk-apply! dfo-c-cod (list 'dfg_ 'dfp_) (list 'dfg_ b))
                     (subst (list '== (list (list 'DIST 'mtb_) (list 'dfg_ 'dfp_)
                                                               (list 'dfg_ b))
                                       (list (list 'DIST 'mta_) (list 'dfg_ 'dfp_)
                                                               (list 'dfg_ b))))
                     (ass)))))))))))) 
(qed 'ms-agree-continuous-at)
(topic! 'ms-agree-continuous-at 'analysis)
(alias! 'ms-agree-continuous-at
        "continuity transfers between spaces with the same points and distances")

;;; (5d) AGREEMENT IS SYMMETRIC.  Stated as two lemmas because the antecedents
;;; are curried and `fact' detaches them one at a time.
(sp (make-wff
     (list 'FORALL 'msa_ (list 'FORALL 'msb_
       (list 'IMPLIES (dfo-agree-pts 'msb_ 'msa_)
                      (dfo-agree-pts 'msa_ 'msb_))))))
(dk-peel!)
(subst '(== (PTS msa_) (PTS msb_)))
(qrfl)
(qed 'ms-agree-pts-sym)
(topic! 'ms-agree-pts-sym 'topology)

(sp (make-wff
     (list 'FORALL 'msa_ (list 'FORALL 'msb_
       (list 'IMPLIES (dfo-agree-pts 'msb_ 'msa_)
         (list 'IMPLIES (dfo-agree-dist 'msb_ 'msa_)
                        (dfo-agree-dist 'msa_ 'msb_)))))))
(define dfo-s-landed (dk-peel!))
(dk-have! '(IN dfu_ (PTS msa_))
          (lambda () (subst '(== (PTS msa_) (PTS msb_))) (ass)))
(dk-have! '(IN dfv_ (PTS msa_))
          (lambda () (subst '(== (PTS msa_) (PTS msb_))) (ass)))
(dk-apply! (dk-pick (lambda (fm) (and (member fm dfo-s-landed) (eq? (dfo-head fm) 'FORALL)))
                    "the distance-agreement universal")
           'dfu_ 'dfv_)
(subst '(== ((DIST msa_) dfu_ dfv_) ((DIST msb_) dfu_ dfv_)))
(qrfl)
(qed 'ms-agree-dist-sym)
(topic! 'ms-agree-dist-sym 'topology)

;;; =====================================================================
;;; (6) THE REAL LINE, IN ITS TWO REGISTERS.
;;;
;;; RR-MS (numeric-instances.scm) and NF-METRIC-SPACE(RR-NORMED-FIELD) have the
;;; same points and the same distance values; so, by (5), the same open sets and
;;; the same continuous maps.  The same holds of the SUBSPACE of the normed
;;; field's space on all of RR (`subspace-whole').  These six facts are the whole
;;; content of the bridge theorem.
;;; =====================================================================

(define dfo-rr-m '(NF-METRIC-SPACE RR-NORMED-FIELD))
(define dfo-rr-w (list 'SUBSPACE-MS dfo-rr-m 'RR))

(sp (make-wff (list 'IS-METRIC-SPACE dfo-rr-m)))
(fact 'rr-is-normed-field)
(fact 'nf-metric-space-is-metric-space 'RR-NORMED-FIELD)
(ass)
(qed 'nf-rr-is-metric-space)
(topic! 'nf-rr-is-metric-space 'analysis)

(sp (make-wff (dfo-agree-pts dfo-rr-m 'RR-MS)))
(fact 'nf-metric-carrier 'RR-NORMED-FIELD)
(subst (list '== (list 'PTS dfo-rr-m) '(CARR RR-NORMED-FIELD)))
(slot 'CARR)
(slot 'PTS)
(qrfl)
(qed 'nf-rr-agree-pts)
(topic! 'nf-rr-agree-pts 'analysis)

(sp (make-wff (dfo-agree-dist dfo-rr-m 'RR-MS)))
(dk-peel!)
(dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
(dk-have! '(IN dfu_ RR) (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
(dk-have! '(IN dfv_ RR) (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
(fact 'rr-nf-carr)
(dk-have! '(IN dfu_ (CARR RR-NORMED-FIELD))
          (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
(dk-have! '(IN dfv_ (CARR RR-NORMED-FIELD))
          (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
(fact 'rr-is-normed-field)
(fact 'nf-metric-distance 'RR-NORMED-FIELD 'dfu_ 'dfv_)
(fact 'rr-neg-closed 'dfv_)
(fact 'rr-add-in-rr 'dfu_ '(- dfv_))
(fact 'rr-nf-neg-apply 'dfv_)
(fact 'rr-nf-add-apply 'dfu_ '(- dfv_))
(fact 'rr-nf-fnrm-apply '(+ dfu_ (- dfv_)))
(fact 'rr-ms-dist 'dfu_ 'dfv_)
(subst (list '== (list (list 'DIST dfo-rr-m) 'dfu_ 'dfv_)
                 '((FNRM RR-NORMED-FIELD) ((ADD RR-NORMED-FIELD) dfu_ ((NEG RR-NORMED-FIELD) dfv_)))))
(subst '(== ((NEG RR-NORMED-FIELD) dfv_) (- dfv_)))
(subst '(== ((ADD RR-NORMED-FIELD) dfu_ (- dfv_)) (+ dfu_ (- dfv_))))
(subst '(== ((FNRM RR-NORMED-FIELD) (+ dfu_ (- dfv_))) (abs (+ dfu_ (- dfv_)))))
(subst '(== ((DIST RR-MS) dfu_ dfv_) (abs (- dfu_ dfv_))))
(mac 'binary-minus-def)
(qrfl)
(qed 'nf-rr-agree-dist)
(topic! 'nf-rr-agree-dist 'analysis)

;;; RR is open in the normed field's own metric space: it is the whole carrier.
(sp (make-wff (list 'IS-OPEN dfo-rr-m 'RR)))
(fact 'nf-rr-is-metric-space)
(fact 'carrier-is-open dfo-rr-m)
(fact 'nf-rr-agree-pts)
(dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
(subst '(== RR (PTS RR-MS)))
(subst (list '== '(PTS RR-MS) (list 'PTS dfo-rr-m)))
(ass)
(qed 'rr-open-in-nf)
(topic! 'rr-open-in-nf 'analysis)
(alias! 'rr-open-in-nf "the real line is open in its own normed-field metric")

;;; The subspace on all of RR.
(sp (make-wff (list 'SUBSET 'RR (list 'PTS dfo-rr-m))))
(fact 'nf-rr-agree-pts)
(dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
(subst (list '== (list 'PTS dfo-rr-m) '(PTS RR-MS)))
(subst '(== (PTS RR-MS) RR))
(fact 'subset-refl 'RR)
(ass)
(qed 'rr-subset-nf-pts)
(topic! 'rr-subset-nf-pts 'analysis)

(sp (make-wff (list 'IS-METRIC-SPACE dfo-rr-w)))
(fact 'nf-rr-is-metric-space)
(fact 'rr-subset-nf-pts)
(fact 'subspace-is-metric-space dfo-rr-m 'RR)
(ass)
(qed 'sub-rr-is-metric-space)
(topic! 'sub-rr-is-metric-space 'analysis)

(sp (make-wff (dfo-agree-pts dfo-rr-w 'RR-MS)))
(fact 'nf-rr-is-metric-space)
(fact 'subspace-pts dfo-rr-m 'RR)
(subst (list '== (list 'PTS dfo-rr-w) 'RR))
(slot 'PTS)
(qrfl)
(qed 'sub-rr-agree-pts)
(topic! 'sub-rr-agree-pts 'analysis)

(sp (make-wff (dfo-agree-dist dfo-rr-w 'RR-MS)))
(dk-peel!)
(fact 'nf-rr-is-metric-space)
(dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
(dk-have! '(IN dfu_ RR) (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
(dk-have! '(IN dfv_ RR) (lambda () (subst '(== RR (PTS RR-MS))) (ass)))
(fact 'subspace-dist dfo-rr-m 'RR 'dfu_ 'dfv_)
(subst (list '== (list (list 'DIST dfo-rr-w) 'dfu_ 'dfv_)
                 (list (list 'DIST dfo-rr-m) 'dfu_ 'dfv_)))
(fact 'nf-rr-agree-dist)
(dk-apply! (dfo-agree-dist dfo-rr-m 'RR-MS) 'dfu_ 'dfv_)
(ass)
(qed 'sub-rr-agree-dist)
(topic! 'sub-rr-agree-dist 'analysis)

;;; The difference in K's operations, at the reals, is the numeric difference.
(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ RR) (IN v_ RR))
                '(== ((ADD RR-NORMED-FIELD) u_ ((NEG RR-NORMED-FIELD) v_)) (- u_ v_)))))
(dk-peel!)
(fact 'rr-nf-neg-apply 'v_)
(fact 'rr-neg-closed 'v_)
(subst '(== ((NEG RR-NORMED-FIELD) v_) (- v_)))
(fact 'rr-nf-add-apply 'u_ '(- v_))
(subst '(== ((ADD RR-NORMED-FIELD) u_ (- v_)) (+ u_ (- v_))))
(mac 'binary-minus-def)
(qrfl)
(qed 'rr-nf-sub)
(topic! 'rr-nf-sub 'algebra)
(alias! 'rr-nf-sub "the difference in the real normed field is the numeric difference")

;;; The two function classes coincide.
(sp (make-wff '(== (FUN RR (CARR RR-NORMED-FIELD)) (FUN RR RR))))
(fact 'rr-nf-carr)
(subst '(== (CARR RR-NORMED-FIELD) RR))
(qrfl)
(qed 'rr-nf-fun-class)
(topic! 'rr-nf-fun-class 'algebra)

;;; =====================================================================
;;; (7) THE BRIDGE (design note, s.3.3).
;;;
;;;     IS-DIFF-AT(f, a, L)   iff   IS-DIFF-ON(RR-NORMED-FIELD, RR, f, a, L)
;;;
;;; Nothing in the real theory changes: this is how a theorem proved for
;;; IS-DIFF-ON reaches the fifty theorems stated with IS-DIFF-AT, and back.
;;; Both directions are the same three moves -- the continuity is transported by
;;; `ms-agree-continuous-at', the FUN typings by `rr-nf-fun-class', and the
;;; Caratheodory equation by `rr-nf-sub' and `rr-nf-mul-apply'.
;;; =====================================================================

;;; the shared facts, landed once in each direction by this helper.
(define (dfo-bridge-setup!)
  (fact 'rr-is-normed-field)
  (fact 'rr-is-metric-space)
  (fact 'nf-rr-is-metric-space)
  (fact 'sub-rr-is-metric-space)
  (fact 'rr-open-in-nf)
  (fact 'rr-nf-carr)
  (fact 'rr-nf-fun-class)
  (fact 'nf-rr-agree-pts)
  (fact 'nf-rr-agree-dist)
  (fact 'sub-rr-agree-pts)
  (fact 'sub-rr-agree-dist)
  (fact 'ms-agree-pts-sym 'RR-MS dfo-rr-m)
  (fact 'ms-agree-dist-sym 'RR-MS dfo-rr-m)
  (fact 'ms-agree-pts-sym 'RR-MS dfo-rr-w)
  (fact 'ms-agree-dist-sym 'RR-MS dfo-rr-w))

;;; the Caratheodory equation, rewritten from K's operations to the numeric
;;; surface.  TO-NUMERIC? says which way the goal has to move; the three
;;; rewrites are the same equations, fired in the opposite order.
(define (dfo-carath! phi xx to-numeric?)
  (let* ((fx (list 'f xx)) (fa '(f a))
         (px (list phi xx))
         (subK (list '(ADD RR-NORMED-FIELD) fx (list '(NEG RR-NORMED-FIELD) fa)))
         (subN (list '- fx fa))
         (dfK  (list '(ADD RR-NORMED-FIELD) xx '((NEG RR-NORMED-FIELD) a)))
         (dfN  (list '- xx 'a))
         (prM  (list '(MUL RR-NORMED-FIELD) px dfN))
         (prN  (list '* px dfN)))
    (fact 'fun-apply-type-c 'f 'RR 'RR xx)
    (fact 'fun-apply-type-c 'f 'RR 'RR 'a)
    (fact 'fun-apply-type-c phi 'RR 'RR xx)
    (fact 'rr-sub-in-rr xx 'a)
    (fact 'rr-nf-sub fx fa)
    (fact 'rr-nf-sub xx 'a)
    (fact 'rr-nf-mul-apply px dfN)
    (if to-numeric?
        (begin (subst (list '== subK subN))
               (subst (list '== dfK dfN))
               (subst (list '== prM prN)))
        (begin (subst (list '== subN subK))
               (subst (list '== prN prM))
               (subst (list '== dfN dfK))))
    (ass)))

;;; the Caratheodory universal of the skolemized witness.
(define (dfo-cont-pt)
  (list-ref (dk-pick (dk-head? 'IS-CONTINUOUS-AT) "the continuity hypothesis") 4))

(define (dfo-carath-univ phi)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm phi)))
           "the Caratheodory universal"))

(sp (make-wff '(FORALL f (FORALL a (FORALL L
     (IFF (IS-DIFF-AT f a L) (IS-DIFF-ON RR-NORMED-FIELD RR f a L)))))))
(di)
(dk-iff!
 (dk-head? 'IS-DIFF-ON)
 ;; ---- forward: IS-DIFF-AT  =>  IS-DIFF-ON -------------------------------
 (lambda ()
   (dfo-bridge-setup!)
   (mac-h 'IS-DIFF-AT '(IS-DIFF-AT f a L))
   (dk-split-all!)
   (let ((phi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the phi existential"))))
     (dk-split-all!)
     ;; CAPTURE THE CARATHEODORY UNIVERSAL NOW.  `fact' lands its whole
     ;; instantiation chain, and a link of the chain is itself a FORALL
     ;; mentioning phi (CLAUDE.md, "Writing proof drivers"); after the citations
     ;; below a shape-based finder picks the wrong one.
     (define dfo-cara (dfo-carath-univ phi))
     ;; the three typings in the normed field's spelling, landed once
     (dk-have! '(IN f (FUN RR (CARR RR-NORMED-FIELD)))
       (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
     (dk-have! (list 'IN phi '(FUN RR (CARR RR-NORMED-FIELD)))
       (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
     (dk-have! '(IN L (CARR RR-NORMED-FIELD))
       (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
     (fact 'ms-agree-continuous-at 'RR-MS dfo-rr-w 'RR-MS dfo-rr-m phi (dfo-cont-pt))
     (mac 'IS-DIFF-ON)
     (dk-conj-close!
      (lambda ()
        (if (eq? (dfo-head (dk-goal)) 'FORSOME)
            (begin
              (ew phi)
              (dk-conj-close!
               (lambda ()
                 (if (eq? (dfo-head (dk-goal)) 'FORALL)
                     (let ((xx (dk-di-var!)))
                       (dk-apply! dfo-cara xx)
                       (dfo-carath! phi xx #t))
                     (ass)))))
            (ass))))))
 ;; ---- backward: IS-DIFF-ON  =>  IS-DIFF-AT ------------------------------
 (lambda ()
   (dfo-bridge-setup!)
   (mac-h 'IS-DIFF-ON '(IS-DIFF-ON RR-NORMED-FIELD RR f a L))
   (dk-split-all!)
   (let ((phi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the phi existential"))))
     (dk-split-all!)
     (define dfo-cara (dfo-carath-univ phi))
     (dk-have! '(IN f (FUN RR RR))
       (lambda () (subst '(== (FUN RR RR) (FUN RR (CARR RR-NORMED-FIELD)))) (ass)))
     (dk-have! (list 'IN phi '(FUN RR RR))
       (lambda () (subst '(== (FUN RR RR) (FUN RR (CARR RR-NORMED-FIELD)))) (ass)))
     (dk-have! '(IN L RR)
       (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
     (fact 'ms-agree-continuous-at dfo-rr-w 'RR-MS dfo-rr-m 'RR-MS phi (dfo-cont-pt))
     (mac 'IS-DIFF-AT)
     (dk-conj-close!
      (lambda ()
        (if (eq? (dfo-head (dk-goal)) 'FORSOME)
            (begin
              (ew phi)
              (dk-conj-close!
               (lambda ()
                 (if (eq? (dfo-head (dk-goal)) 'FORALL)
                     (let ((xx (dk-di-var!)))
                       (dk-apply! dfo-cara xx)
                       (dfo-carath! phi xx #f))
                     (ass)))))
            (ass)))))))
(qed 'diff-at-iff-diff-on)
(topic! 'diff-at-iff-diff-on 'analysis)
(alias! 'diff-at-iff-diff-on
        "the real derivative is the derivative on RR over the real normed field")

;;; =====================================================================
;;; (8) THE NORMED-FIELD TOOLKIT.
;;;
;;; `is-norm' (operation-properties.scm) is reached only by unfolding
;;; IS-NORMED-FIELD, which is DESTRUCTIVE, and the four facts it carries are
;;; wanted one at a time in every eps-delta argument below.  They are surfaced
;;; here, each as its own theorem, exactly as `rake-nf-norm.scm' surfaced
;;; ||-a|| = ||a||.  Carrier closure goes the same way as there: through
;;; NORMED-FIELD-AS-COMMUTATIVE-RING and the three slot read-offs, a normed
;;; field being a 7-tuple and the ring predicates pinning length 6.
;;; =====================================================================

(define dfo-view '(NORMED-FIELD-AS-COMMUTATIVE-RING K))

;;; unfold IS-NORMED-FIELD(K) and then its `is-norm' conjunct.
(define (dfo-nf-unfold!)
  (dk-split-all! (dk-landed* (lambda () (mac-h 'is-normed-field '(IS-NORMED-FIELD K)))))
  (dk-split-all!
   (dk-landed* (lambda () (mac-h 'is-norm '(is-norm (FNRM K) (ADD K) (MUL K)
                                                    (ZERO K) (CARR K)))))))

;;; the `is-norm' universal, named by its CONSEQUENT (an AND whose first
;;; conjunct is 0 <= ||a||), never by its head.
(define (dfo-norm-univ)
  (dk-pick (lambda (fm)
             (and (pair? fm) (eq? (car fm) 'FORALL)
                  (pair? (caddr fm)) (eq? (car (caddr fm)) 'IMPLIES)
                  (pair? (caddr (caddr fm))) (eq? (car (caddr (caddr fm))) 'AND)
                  (let ((c1 (cadr (caddr (caddr fm)))))
                    (and (pair? c1) (eq? (car c1) '<=) (equal? (cadr c1) 0)))))
           "the is-norm universal"))

(define (dfo-nf-thm! name concl body)
  (sp (make-wff (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K) concl))))
  (dk-peel!)
  (body)
  (if (not (proof-done? *ps*))
      (error "dfo-nf-thm!: proof did not close" name (dk-goal)))
  (qed name))

(dfo-nf-thm! 'nf-norm-in-rr
  (forall-guarded '(u_) '((IN u_ (CARR K))) '(IN ((FNRM K) u_) RR))
  (lambda ()
    (dfo-nf-unfold!)
    (fact 'fun-apply-type-c '(FNRM K) '(CARR K) 'RR 'u_)
    (ass)))
(topic! 'nf-norm-in-rr 'algebra)
(alias! 'nf-norm-in-rr "a norm takes real values")

(dfo-nf-thm! 'nf-norm-nonneg
  (forall-guarded '(u_) '((IN u_ (CARR K))) '(<= 0 ((FNRM K) u_)))
  (lambda ()
    (dfo-nf-unfold!)
    (dk-split! (dk-apply! (dfo-norm-univ) 'u_))
    (ass)))
(topic! 'nf-norm-nonneg 'algebra)
(alias! 'nf-norm-nonneg "a norm is nonnegative")

(dfo-nf-thm! 'nf-norm-mult
  (forall-guarded '(u_ v_) '((IN u_ (CARR K)) (IN v_ (CARR K)))
                  '(= ((FNRM K) ((MUL K) u_ v_)) (* ((FNRM K) u_) ((FNRM K) v_))))
  (lambda ()
    (dfo-nf-unfold!)
    (let* ((atoms (dk-split! (dk-apply! (dfo-norm-univ) 'u_)))
           (inner (or (find-first (dk-head? 'FORALL) atoms)
                      (error "nf-norm-mult: no is-norm b-universal"))))
      (dk-split! (dk-apply! inner 'v_))
      (ass))))
(topic! 'nf-norm-mult 'algebra)
(alias! 'nf-norm-mult "a field norm is multiplicative")

(dfo-nf-thm! 'nf-norm-subadd
  (forall-guarded '(u_ v_) '((IN u_ (CARR K)) (IN v_ (CARR K)))
                  '(<= ((FNRM K) ((ADD K) u_ v_)) (+ ((FNRM K) u_) ((FNRM K) v_))))
  (lambda ()
    (dfo-nf-unfold!)
    (let* ((atoms (dk-split! (dk-apply! (dfo-norm-univ) 'u_)))
           (inner (or (find-first (dk-head? 'FORALL) atoms)
                      (error "nf-norm-subadd: no is-norm b-universal"))))
      (dk-split! (dk-apply! inner 'v_))
      (ass))))
(topic! 'nf-norm-subadd 'algebra)
(alias! 'nf-norm-subadd "a norm is subadditive")

;;; Carrier closure, through the ring view.
(define (dfo-closure! binop-view-thm ring-thm args)
  (fact 'normed-field-as-commutative-ring-is-commutative-ring 'K)
  (fact 'commutative-ring-is-ring dfo-view)
  (fact 'normed-field-ring-view-carr 'K)
  (fact binop-view-thm 'K)
  (for-each (lambda (u)
              (dk-have! (list 'IN u (list 'CARR dfo-view))
                (lambda () (subst (list '== (list 'CARR dfo-view) '(CARR K))) (ass))))
            args))

(dfo-nf-thm! 'nf-add-in-carr
  (forall-guarded '(u_ v_) '((IN u_ (CARR K)) (IN v_ (CARR K)))
                  '(IN ((ADD K) u_ v_) (CARR K)))
  (lambda ()
    (dfo-closure! 'normed-field-ring-view-add 'ring-carrier-closed-add '(u_ v_))
    (subst (list '== '(CARR K) (list 'CARR dfo-view)))
    (subst (list '== '(ADD K) (list 'ADD dfo-view)))
    (have! (list 'AND (list 'IS-RING dfo-view)
                 (list 'AND (list 'IN 'u_ (list 'CARR dfo-view))
                            (list 'IN 'v_ (list 'CARR dfo-view)))))
    (fact 'ring-carrier-closed-add dfo-view 'u_ 'v_)
    (ass)))
(topic! 'nf-add-in-carr 'algebra)

(dfo-nf-thm! 'nf-mul-in-carr
  (forall-guarded '(u_ v_) '((IN u_ (CARR K)) (IN v_ (CARR K)))
                  '(IN ((MUL K) u_ v_) (CARR K)))
  (lambda ()
    (dfo-closure! 'normed-field-ring-view-mul 'ring-carrier-closed-mul '(u_ v_))
    (subst (list '== '(CARR K) (list 'CARR dfo-view)))
    (subst (list '== '(MUL K) (list 'MUL dfo-view)))
    (fact 'ring-carrier-closed-mul dfo-view 'u_ 'v_)
    (ass)))
(topic! 'nf-mul-in-carr 'algebra)

(dfo-nf-thm! 'nf-neg-in-carr
  (forall-guarded '(u_) '((IN u_ (CARR K))) '(IN ((NEG K) u_) (CARR K)))
  (lambda ()
    (dfo-closure! 'normed-field-ring-view-neg 'ring-neg-in-carr '(u_))
    (subst (list '== '(CARR K) (list 'CARR dfo-view)))
    (subst (list '== '(NEG K) (list 'NEG dfo-view)))
    (fact 'ring-neg-in-carr dfo-view 'u_)
    (ass)))
(topic! 'nf-neg-in-carr 'algebra)

;;; (8e) u = (u - v) + v, and the estimate ||u|| <= ||u - v|| + ||v|| that every
;;; "the factor stays bounded near a" argument needs.  The identity is a ring
;;; identity of the VIEW (a normed field is a 7-tuple, the ring predicates pin
;;; length 6), so it is `crs' after the three slot read-offs.
(dfo-nf-thm! 'nf-sub-add-back
  (forall-guarded '(u_ v_) '((IN u_ (CARR K)) (IN v_ (CARR K)))
                  '(= ((ADD K) ((ADD K) u_ ((NEG K) v_)) v_) u_))
  (lambda ()
    (fact 'normed-field-as-commutative-ring-is-commutative-ring 'K)
    (fact 'commutative-ring-is-ring dfo-view)
    (fact 'normed-field-ring-view-carr 'K)
    (fact 'normed-field-ring-view-add 'K)
    (fact 'normed-field-ring-view-neg 'K)
    (for-each (lambda (u)
                (dk-have! (list 'IN u (list 'CARR dfo-view))
                  (lambda () (subst (list '== (list 'CARR dfo-view) '(CARR K))) (ass))))
              '(u_ v_))
    (subst (list '== '(ADD K) (list 'ADD dfo-view)))
    (subst (list '== '(NEG K) (list 'NEG dfo-view)))
    (crs)))
(topic! 'nf-sub-add-back 'algebra)
(alias! 'nf-sub-add-back "adding back the subtrahend")

(dfo-nf-thm! 'nf-norm-le-add
  (forall-guarded '(u_ v_) '((IN u_ (CARR K)) (IN v_ (CARR K)))
                  '(<= ((FNRM K) u_)
                       (+ ((FNRM K) ((ADD K) u_ ((NEG K) v_))) ((FNRM K) v_))))
  (lambda ()
    (fact 'nf-neg-in-carr 'K 'v_)
    (fact 'nf-add-in-carr 'K 'u_ '((NEG K) v_))
    (fact 'nf-norm-subadd 'K '((ADD K) u_ ((NEG K) v_)) 'v_)
    (fact 'nf-sub-add-back 'K 'u_ 'v_)
    (dk-have! '(= ((FNRM K) u_) ((FNRM K) ((ADD K) ((ADD K) u_ ((NEG K) v_)) v_)))
      (lambda () (subst '(= ((ADD K) ((ADD K) u_ ((NEG K) v_)) v_) u_)) (rfl)))
    (subst '(= ((FNRM K) u_) ((FNRM K) ((ADD K) ((ADD K) u_ ((NEG K) v_)) v_))))
    (ass)))
(topic! 'nf-norm-le-add 'algebra)
(alias! 'nf-norm-le-add "the norm of a point is bounded by a difference plus the base")

;;; =====================================================================
;;; (9) DIFFERENTIABLE ON U AT a  =>  CONTINUOUS AT a  (Prop 2.4 over K).
;;;
;;; The real proof (theorem-library/differentiation.scm:118) runs through the
;;; CONTINUITY ALGEBRA -- const + product + sum continuous at a, then transfer
;;; along pointwise equality.  That algebra is stated for RR-MS only, and there
;;; is none over a normed field, still less over a metric SUBSPACE of one; so
;;; this is the eps-delta argument, once:
;;;
;;;   d(f a, f b) = ||f b - f a|| = ||phi b|| . ||b - a||,
;;;
;;; phi is continuous at a so ||phi b|| <= ||L|| + 1 = C on a ball of radius
;;; delta1, and `rr-scale-eps' turns C into a radius d2 with C.t <= eps for
;;; 0 <= t <= d2.  `rr-min-pos' takes the smaller of the two radii -- there is no
;;; MIN on this surface that `ineq' would certify, and the existential form is
;;; what the library already proves.
;;; =====================================================================

(define dfo-M '(NF-METRIC-SPACE K))
(define dfo-W '(SUBSPACE-MS (NF-METRIC-SPACE K) U))
(define (dfo-dM x y) (list (list 'DIST dfo-M) x y))
(define (dfo-dW x y) (list (list 'DIST dfo-W) x y))
(define (dfo-nrm x)  (list '(FNRM K) x))
(define (dfo-sub x y) (list '(ADD K) x (list '(NEG K) y)))

;;; (IN t (PTS M)) from (IN t (CARR K)); and (IN t (PTS W)) from (IN t U).
(define (dfo-in-ptsM! t)
  (dk-have! (list 'IN t (list 'PTS dfo-M))
    (lambda () (subst (list '== (list 'PTS dfo-M) '(CARR K))) (ass))))
(define (dfo-in-ptsW! t)
  (dk-have! (list 'IN t (list 'PTS dfo-W))
    (lambda () (subst (list '== (list 'PTS dfo-W) 'U)) (ass))))


;;; The inner estimate, at one point b of U.  CARA is the Caratheodory
;;; universal, captured before any citation chain was landed; W is the radius
;;; `rr-min-pos' produced, D1 phi's radius at eps' = 1 and D2 `rr-scale-eps''s.
(define (dfo-carath-body! phi b w d1 d2 bigc eps cara)
  (let* ((fa '(f a)) (fb (list 'f b))
         (pa (list phi 'a)) (pb (list phi b))
         (dba (dfo-sub b 'a))
         (nd  (dfo-nrm dba))
         (npb (dfo-nrm pb))
         (dfba (dfo-sub fb fa))
         (dpba (dfo-sub pb pa))
         (prod (list '(MUL K) pb dba)))
    ;; ---- typings
    (fact 'subset-mem-fwd 'U '(CARR K) b)
    (fact 'subset-mem-fwd 'U '(CARR K) 'a)
    (fact 'fun-apply-type-c 'f 'U '(CARR K) b)
    (fact 'fun-apply-type-c 'f 'U '(CARR K) 'a)
    (fact 'fun-apply-type-c phi 'U '(CARR K) b)
    (fact 'fun-apply-type-c phi 'U '(CARR K) 'a)
    (for-each dfo-in-ptsM! (list 'a b fa fb pa pb))
    (dfo-in-ptsW! b)
    (dfo-in-ptsW! 'a)
    (fact 'nf-neg-in-carr 'K 'a)
    (fact 'nf-add-in-carr 'K b '((NEG K) a))
    (fact 'nf-neg-in-carr 'K pa)
    (fact 'nf-add-in-carr 'K pb (list '(NEG K) pa))
    (fact 'nf-norm-in-rr 'K dba)
    (fact 'nf-norm-nonneg 'K dba)
    (fact 'nf-norm-in-rr 'K pb)
    (fact 'nf-norm-in-rr 'K pa)
    (fact 'nf-norm-in-rr 'K dpba)
    (fact 'metric-dist-real dfo-W 'a b)
    (fact 'metric-dist-real dfo-M 'a b)
    ;; ---- the subspace distance is the ambient one, and both are <= w
    (fact 'subspace-dist dfo-M 'U 'a b)
    (dk-have! (list '<= (dfo-dM 'a b) w)
      (lambda () (subst (list '== (dfo-dM 'a b) (dfo-dW 'a b))) (ass)))
    ;; ---- ||b - a|| = d(b,a) = d(a,b) <= w <= d2,  so C.||b - a|| <= eps
    (fact 'nf-metric-distance 'K b 'a)
    (fact 'metric-sym dfo-M 'a b)
    (dk-have! (list '<= nd w)
      (lambda () (subst (list '= nd (dfo-dM b 'a)))
                 (subst (list '= (dfo-dM b 'a) (dfo-dM 'a b)))
                 (ass)))
    (dk-have! (list '<= nd d2)
      (lambda () (dk-ineq! (list '<= nd w) (list '<= w d2)
                           (list 'IN nd 'RR) (list 'IN w 'RR) (list 'IN d2 'RR))))
    (dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                          (dk-contains? fm d2) (dk-contains? fm bigc)))
                        "the rr-scale-eps universal")
               nd)
    ;; ---- ||phi b|| <= ||L|| + 1 on the ball of radius d1
    (dk-have! (list '<= (dfo-dW 'a b) d1)
      (lambda () (dk-ineq! (list '<= (dfo-dW 'a b) w) (list '<= w d1)
                           (list 'IN (dfo-dW 'a b) 'RR) (list 'IN w 'RR)
                           (list 'IN d1 'RR))))
    (dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                          (dk-contains? fm d1) (dk-contains? fm phi)))
                        "phi's delta universal")
               b)
    (fact 'metric-sym dfo-M pa pb)
    (fact 'nf-metric-distance 'K pb pa)
    (dk-have! (list '<= (dfo-nrm dpba) 1)
      (lambda () (subst (list '= (dfo-nrm dpba) (dfo-dM pb pa)))
                 (subst (list '= (dfo-dM pb pa) (dfo-dM pa pb)))
                 (ass)))
    (fact 'nf-norm-le-add 'K pb pa)
    (dk-have! (list '= (dfo-nrm 'L) (dfo-nrm pa))
      (lambda () (subst (list '= pa 'L)) (rfl)))
    (dk-have! (list '<= npb bigc)
      (lambda () (subst (list '= (dfo-nrm 'L) (dfo-nrm pa)))
                 (dk-ineq! (list '<= npb (list '+ (dfo-nrm dpba) (dfo-nrm pa)))
                           (list '<= (dfo-nrm dpba) 1)
                           (list 'IN npb 'RR) (list 'IN (dfo-nrm dpba) 'RR)
                           (list 'IN (dfo-nrm pa) 'RR))))
    ;; ---- the goal
    (fact 'metric-sym dfo-M fa fb)
    (subst (list '= (dfo-dM fa fb) (dfo-dM fb fa)))
    (fact 'nf-metric-distance 'K fb fa)
    (subst (list '= (dfo-dM fb fa) (dfo-nrm dfba)))
    (dk-apply! cara b)
    (subst (list '= dfba prod))
    (fact 'nf-norm-mult 'K pb dba)
    (subst (list '= (dfo-nrm prod) (list '* npb nd)))
    (fact 'rr-mul-le-right npb bigc nd)
    (fact 'rr-mul-in-rr npb nd)
    (fact 'rr-mul-in-rr bigc nd)
    (dk-ineq! (list '<= (list '* npb nd) (list '* bigc nd))
              (list '<= (list '* bigc nd) eps)
              (list 'IN (list '* npb nd) 'RR) (list 'IN (list '* bigc nd) 'RR)
              (list 'IN eps 'RR))))

(sp (make-wff (list 'FORALL 'K (list 'FORALL 'U (list 'FORALL 'f (list 'FORALL 'a
     (list 'FORALL 'L (list 'IMPLIES dfo-hyp
       (list 'IS-CONTINUOUS-AT dfo-W dfo-M 'f 'a)))))))))
(dk-peel!)
;; everything read off IS-DIFF-ON BEFORE `mac-h' destroys it
(fact 'diff-on-normed-field 'K 'U 'f 'a 'L)
(fact 'diff-on-open 'K 'U 'f 'a 'L)
(fact 'diff-on-in-fun 'K 'U 'f 'a 'L)
(fact 'diff-on-pt-in 'K 'U 'f 'a 'L)
(fact 'diff-on-deriv-in-carr 'K 'U 'f 'a 'L)
(fact 'nf-open-subset-carr 'K 'U)
(fact 'nf-metric-carrier 'K)
(fact 'nf-metric-space-is-metric-space 'K)
(dk-have! (list 'SUBSET 'U (list 'PTS dfo-M))
  (lambda () (subst (list '== (list 'PTS dfo-M) '(CARR K))) (ass)))
(fact 'subspace-is-metric-space dfo-M 'U)
(fact 'subspace-pts dfo-M 'U)
(mac-h 'IS-DIFF-ON dfo-hyp)
(dk-split-all!)
(let ((phi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the phi existential"))))
  (dk-split-all!)
  (define dfo-cara (dfo-carath-univ phi))
  (mac 'IS-CONTINUOUS-AT)
  (mac 'subspace-pts)
  (mac 'nf-metric-carrier)
  (dk-conj-close!
   (lambda ()
     (if (not (eq? (dfo-head (dk-goal)) 'FORALL))
         (ass)
         (begin
           (dk-peel!)                           ; eps, POS-RR eps
           (let ((eps (cadr (dk-pick (dk-head? 'POS-RR) "POS-RR eps"))))
             (fact 'rr-pos-rr-in-rr eps)
             (fact 'rr-one-in)
             (fact 'nf-norm-in-rr 'K 'L)
             (fact 'nf-norm-nonneg 'K 'L)
             (fact 'rr-add-in-rr (dfo-nrm 'L) 1)
             (dk-have! '(POS-RR 1)
               (lambda () (dk-have! '(< 0 1) (lambda () (ineq)))
                          (fact 'rr-pos-rr-of-lt 1) (ass)))
             (dk-have! (list '<= 0 (list '+ (dfo-nrm 'L) 1))
               (lambda () (dk-ineq! (list '<= 0 (dfo-nrm 'L))
                                    (list 'IN (dfo-nrm 'L) 'RR))))
             ;; phi's continuity, at eps' = 1
             (mac-h 'IS-CONTINUOUS-AT (list 'IS-CONTINUOUS-AT dfo-W dfo-M phi 'a))
             (dk-split-all!)
             (let* ((cu (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                   (dk-contains? fm 'FORSOME)
                                                   (dk-contains? fm 'POS-RR)))
                                 "phi's eps universal"))
                    (d1 (dk-skolem! (dk-apply! cu 1)))
                    (bigc (list '+ (dfo-nrm 'L) 1))
                    (d2 (dk-skolem! (dk-fact! 'rr-scale-eps bigc eps))))
               (fact 'rr-pos-rr-in-rr d1)
               (fact 'rr-pos-rr-in-rr d2)
               (fact 'rr-lt-of-pos-rr d1)
               (fact 'rr-lt-of-pos-rr d2)
               (let ((w (dk-skolem! (dk-fact! 'rr-min-pos d1 d2))))
                 (ew w)
                 (dk-conj-close!
                  (lambda ()
                    (if (eq? (dfo-head (dk-goal)) 'POS-RR)
                        (begin (fact 'rr-pos-rr-of-lt w) (ass))
                        (begin
                          (dk-peel!)            ; b, (IN b U), the delta bound
                          (let* ((bty (dk-pick (lambda (fm)
                                                 (and (pair? fm) (eq? (car fm) 'IN)
                                                      (eq? (caddr fm) 'U)
                                                      (not (eq? (cadr fm) 'a))))
                                               "the typing of b"))
                                 (b (cadr bty)))
                            (dfo-carath-body! phi b w d1 d2 bigc eps dfo-cara)))))))))))))) 
(qed 'diff-on-implies-continuous)
(topic! 'diff-on-implies-continuous 'analysis)
(alias! 'diff-on-implies-continuous
        "differentiable on an open set implies continuous there")

;;; =====================================================================
;;; (10) DERIV-ON's UNFOLD, AND THE READ-OFFS OF HOLOMORPHIC-ON.
;;;
;;; `def-functoid' installs only a rewrite MACETE, so `mac-h' cannot unfold
;;; DERIV-ON in an ASSUMPTION by the functoid's own name (CLAUDE.md, "Where a
;;; definition lives"); the unfold EQUATION, proved here, is what it can name.
;;; =====================================================================
(sp (make-wff '(FORALL K (FORALL U (FORALL f (FORALL a
     (== (DERIV-ON K U f a) (IOTA L (IS-DIFF-ON K U f a L)))))))))
(di)
(mac 'DERIV-ON)
(qrfl)
(qed 'deriv-on-unfold)
(topic! 'deriv-on-unfold 'analysis)
(alias! 'deriv-on-unfold "the derivative on a set is the unique such L")

(define (dfo-holo! name concl)
  (sp (make-wff (list 'FORALL 'U (list 'FORALL 'f
                  (list 'IMPLIES '(HOLOMORPHIC-ON U f) concl)))))
  (dk-peel!)
  (mac-h 'HOLOMORPHIC-ON '(HOLOMORPHIC-ON U f))
  (dk-split-all!)
  (ass)
  (if (not (proof-done? *ps*))
      (error "dfo-holo!: proof did not close" name (dk-goal)))
  (qed name))

(dfo-holo! 'holomorphic-on-open '(IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) U))
(topic! 'holomorphic-on-open 'analysis)
(alias! 'holomorphic-on-open "the domain of a holomorphic function is open")

(dfo-holo! 'holomorphic-on-in-fun '(IN f (FUN U CC)))
(topic! 'holomorphic-on-in-fun 'analysis)
(alias! 'holomorphic-on-in-fun "a holomorphic function is a function on its domain")

;;; `dk-peel!' goes on into the conclusion's own universal, so this one applies
;;; the landed universal at the eigenvariable rather than closing by `ass'.
(sp (make-wff '(FORALL U (FORALL f (IMPLIES (HOLOMORPHIC-ON U f)
     (FORALL a (IMPLIES (IN a U)
       (FORSOME L (IS-DIFF-ON CC-NORMED-FIELD U f a L)))))))))
(dk-peel!)
(mac-h 'HOLOMORPHIC-ON '(HOLOMORPHIC-ON U f))
(dk-split-all!)
(dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                      (dk-contains? fm 'IS-DIFF-ON)))
                    "the pointwise differentiability universal")
           'a)
(ass)
(qed 'holomorphic-on-diff)
(topic! 'holomorphic-on-diff 'analysis)
(alias! 'holomorphic-on-diff "a holomorphic function is differentiable at each point")
