;;; gauge-is-degree.scm -- the named Euclidean gauge GAUGE(s) is a degree
;;; function, PROVEN, together with the four supports its warrant cites.
;;;
;;; STATEMENTS (all from structure-library/euclidean-ring.scm, unchanged):
;;;
;;;   euclidean-gauges-unfold   EUCLIDEAN-GAUGES(s) == { dg in FUN(CARR s, NN) :
;;;                                                       HAS-DIV-REMAINDER(s, dg) }
;;;                             (new; the citable unfold of the def-functoid)
;;;   euclidean-ring-has-gauge  IS-EUCLIDEAN-RING(s) => forsome dg in FUN(CARR s, NN).
;;;                                                       HAS-DIV-REMAINDER(s, dg)
;;;   gauges-mem-build          dg in FUN(CARR s, NN) => HAS-DIV-REMAINDER(s, dg)
;;;                                                   => dg in EUCLIDEAN-GAUGES(s)
;;;   gauges-in-fun             dg in EUCLIDEAN-GAUGES(s) => dg in FUN(CARR s, NN)
;;;   gauges-spec               dg in EUCLIDEAN-GAUGES(s) => HAS-DIV-REMAINDER(s, dg)
;;;   gauge-is-degree           IS-EUCLIDEAN-RING(s) => GAUGE(s) in FUN(CARR s, NN)
;;;                                                   and HAS-DIV-REMAINDER(s, GAUGE s)
;;;
;;; PLAN.  Port of archive/calculus-pre-rename/gauge-proof.scm (A -> CARR), with
;;; the four supports it cited proven first in the same file, so that none of
;;; them enters the 21 bills that gauge-is-degree is the sole leaf of.
;;;
;;;   * The unfold equation is `(di) (mac 'EUCLIDEAN-GAUGES) (qrfl)' -- the
;;;     def-functoid macete fires on a goal that IS the equation.  The theorem
;;;     is what `mac-h' needs to open a gauge-set membership in a HYPOTHESIS.
;;;   * has-gauge: unfold IS-EUCLIDEAN-RING in the hypothesis
;;;     (is-euclidean-ring-def), split, skolemize the FORSOME, `ew' the
;;;     eigenvariable back in; the HAS-DIV-REMAINDER conjunct is the law's
;;;     division clause verbatim, so `mac' folds the goal onto the hypothesis.
;;;   * mem-build: `mac' the goal to the SEP, `sep-mi', both obligations in
;;;     context.  in-fun / spec: `mac-h' the unfold, `sep-me', `ass'.
;;;   * gauge-is-degree: the gauge set is inhabited (has-gauge + mem-build), so
;;;     `choice-axiom' puts CHOICE(EUCLIDEAN-GAUGES s) in it; in-fun / spec give
;;;     the two conjuncts; `mac 'GAUGE' rewrites the goal onto the CHOICE term.
;;;
;;; LOAD WINDOW [lo, hi): lo = driver-kit / proof-debt (positions 130-131; the
;;; file uses dk-*, have!, qed) -- nothing from theorem-library/ is cited, and
;;; every mathematical citation (is-euclidean-ring-def, HAS-DIV-REMAINDER,
;;; EUCLIDEAN-GAUGES, GAUGE, choice-axiom) is in structure-library/euclidean-ring
;;; (41) or the base theory.  hi = theorem-library/euclidean-ideal-generator-proof
;;; (236), the earliest citer of gauge-is-degree.
;;;
;;; Helper prefix: gd-.

(define (gd-peel!)                      ; di until the goal head changes
  (let loop ((fuel 8))
    (let ((g (dk-goal)))
      (when (and (> fuel 0) (pair? g) (memq (car g) '(forall implies)))
        (di) (loop (- fuel 1))))))

;;; ---------------------------------------------------------------------
;;; 1. The unfold equation.
(sp (make-wff '(FORALL s (== (EUCLIDEAN-GAUGES s)
                             (SEP dg (FUN (CARR s) NN) (HAS-DIV-REMAINDER s dg))))))
(di) (mac 'EUCLIDEAN-GAUGES) (qrfl)
(qed 'euclidean-gauges-unfold)
(gloss! 'euclidean-gauges-unfold
  "EUCLIDEAN-GAUGES(s) is the separation { dg in FUN(CARR s, NN) :
   HAS-DIV-REMAINDER(s, dg) }, as a citable equation.  Cite it with mac-h to
   open a gauge-set membership in a hypothesis.")
(topic! 'euclidean-gauges-unfold 'plumbing)

;;; ---------------------------------------------------------------------
;;; 2. A Euclidean ring has a gauge.
(sp (make-wff '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s)
     (FORSOME dg (AND (IN dg (FUN (CARR s) NN)) (HAS-DIV-REMAINDER s dg)))))))
(gd-peel!)
(let* ((h   (dk-landed-1 (lambda () (mac-h 'is-euclidean-ring-def '(IS-EUCLIDEAN-RING s)))))
       (fs  (any-pred (dk-head? 'forsome) (dk-split! h)))
       (bd  (dk-landed-1 (lambda () (ai fs))))          ; (AND (IN dg_k FUN) (FORALL ...))
       (dgk (cadr (cadr bd))))
  (dk-split! bd)
  (ew dgk)
  (let ((ls (dk-opened (lambda () (di)))))
    (for-each (lambda (n)
                (dk-focus! n)
                (if (eq? (car (dk-goal)) 'has-div-remainder)
                    (mac 'HAS-DIV-REMAINDER))
                (ass))
              ls)))
(qed 'euclidean-ring-has-gauge)

;;; ---------------------------------------------------------------------
;;; 3. SEP-membership, inward.
(sp (make-wff '(FORALL s (FORALL dg (IMPLIES (IN dg (FUN (CARR s) NN))
       (IMPLIES (HAS-DIV-REMAINDER s dg) (IN dg (EUCLIDEAN-GAUGES s))))))))
(gd-peel!)
(mac 'EUCLIDEAN-GAUGES)
(for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi))))
(qed 'gauges-mem-build)

;;; 4/5. SEP-membership, outward: the two slices.
(define (gd-slice! name goal)
  (sp (make-wff (list 'FORALL 's (list 'FORALL 'dg
        (list 'IMPLIES '(IN dg (EUCLIDEAN-GAUGES s)) goal)))))
  (gd-peel!)
  (let ((h (dk-landed-1 (lambda () (mac-h 'euclidean-gauges-unfold '(IN dg (EUCLIDEAN-GAUGES s)))))))
    (sep-me h)
    (ass))
  (qed name))
(gd-slice! 'gauges-in-fun '(IN dg (FUN (CARR s) NN)))
(gd-slice! 'gauges-spec   '(HAS-DIV-REMAINDER s dg))

;;; ---------------------------------------------------------------------
;;; 6. The chosen gauge is a degree function.
(sp (make-wff '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s)
     (AND (IN (GAUGE s) (FUN (CARR s) NN))
          (HAS-DIV-REMAINDER s (GAUGE s)))))))
(gd-peel!)
(let* ((ex  (dk-fact! 'euclidean-ring-has-gauge 's))   ; forsome dg. dg in FUN and HDR
       (bd  (dk-landed-1 (lambda () (ai ex))))
       (dgk (cadr (cadr bd))))
  (dk-split! bd)
  (dk-fact! 'gauges-mem-build 's dgk)                   ; dg_k in EUCLIDEAN-GAUGES(s)
  (have! '(FORSOME x_ (IN x_ (EUCLIDEAN-GAUGES s)))
         (lambda () (ew dgk) (ass)))
  (dk-fact! 'choice-axiom '(EUCLIDEAN-GAUGES s))        ; CHOICE(...) in EUCLIDEAN-GAUGES(s)
  (dk-fact! 'gauges-in-fun 's '(CHOICE (EUCLIDEAN-GAUGES s)))
  (dk-fact! 'gauges-spec   's '(CHOICE (EUCLIDEAN-GAUGES s)))
  (mac 'GAUGE)
  (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (di)))))
(qed 'gauge-is-degree)
