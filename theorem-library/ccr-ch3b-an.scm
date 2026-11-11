;;; ccr-ch3b-an.scm -- wave of 2026-11-09/10 (agent CCR-1109-B2), wired 2026-11-10 from scratchpad/ccr1109b2/ccr-ch3b-an.scm.
;;; Library: analysis.

;;; ccr-ch3b-an.scm -- CCR.pdf chapter 3, second pass, the ANALYSIS: the closed unit ball Z(K) of a LOCAL
;;; NV field is compact (the base case n = 1 of "the closed unit ball of K^n is compact", Section 3.1).
;;; Agent CCR-1109-B2, wave 2026-11-09.  Destination: theorem-library/ccr-ch3b-an.scm.  Library: analysis.
;;; Helper prefix cq5-.
;;;
;;; ROUTE.  nv-integers-compact (theorem-library, ccr2) gives the compactness of Z(K) from a compact closed
;;; ball at 0 of positive radius and an element x0 with 0 < |x0| < 1.  A local NV field supplies both: the
;;; ball from local compactness at 0, the element from NON-DISCRETENESS -- if no element had 0 < |x| < 1,
;;; then every point x would be isolated (ball(x, 1) = {x}, since d(x, y) = |x - y|), and the metric
;;; space of K would be discrete.
;;;
;;; LOAD WINDOW: after the files of nv-integers-compact, is-local-nv-field (ca51 / ccr2 vocabulary) and
;;; nf-metric-distance; no citation of ccr-ch3b-alg.

(define cq5-ms '(NF-METRIC-SPACE K))
(define (cq5-n x) `((FNRM K) ,x))
(define cq5-small '(FORSOME zky_ (AND (IN zky_ (CARR K)) (AND (< 0 ((FNRM K) zky_)) (< ((FNRM K) zky_) 1)))))

(define (cq5-find-zero f)
  (let walk ((t f)) (cond ((equal? t '(ZERO K)) #t) ((pair? t) (or (walk (car t)) (walk (cdr t)))) (#t #f))))
(define (cq5-qed! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; cq5: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (f) (display ";;      | ") (display (expression->string f)) (newline))
                              (let ((a (dk-asms-of l))) (list-head a (min 8 (length a))))))
                  (dk-open-leaves))))
  (qed name))

;; a non-discrete normed field has an element of norm strictly between 0 and 1
(sp (make-wff `(FORALL K (IMPLIES (IS-NORMED-FIELD K) (IMPLIES (NOT (IS-DISCRETE-MS ,cq5-ms)) ,cq5-small)))))
(dk-peel!)
(dk-cite! 'nf-metric-space-is-metric-space 'K)
(dk-cite! 'nf-metric-carrier 'K)
(use-em cq5-small
  (lambda () (dk-ass!))
  (lambda ()
    (dk-have! `(IS-DISCRETE-MS ,cq5-ms)
      (lambda ()
        (mac 'is-discrete-ms)
        (let* ((landed (dk-peel!)) (xv (cadr (car landed))))
          (dk-have! `(IN ,xv (CARR K)) (lambda () (subst `(= (CARR K) (PTS ,cq5-ms))) (dk-ass!)))
          (ew 1)
          (dk-conj-close!
            (lambda ()
              (if (dk-head-is? (dk-goal) 'POS-RR)
                  (begin
                    (mac 'pos-rr)
                    (dk-conj-close!
                      (lambda ()
                        (cond ((dk-head-is? (dk-goal) 'NOT) (di) (dk-have! '(< 0 0) (lambda () (dk-ineq! '(= 0 1)))) (dk-absurd! '(< 0 0)))
                              ((dk-head-is? (dk-goal) 'IN) (arith))
                              (#t (dk-ineq!))))))
                  (let* ((l2 (dk-peel!)) (yv (cadr (car l2)))
                         (bm (dk-cite! 'ball-membership cq5-ms xv 1 yv))
                         (zv `((ADD K) ,xv ((NEG K) ,yv)))
                         (dv `((DIST ,cq5-ms) ,xv ,yv)))
                    (dk-have! `(AND (IN ,yv (PTS ,cq5-ms)) (AND (<= ,dv 1) (NOT (= ,dv 1))))
                      (lambda () (dk-only! (dk-ctx-form `(IFF (IN ,yv (BALL ,cq5-ms ,xv 1)) (AND (IN ,yv (PTS ,cq5-ms)) (AND (<= ,dv 1) (NOT (= ,dv 1))))))
                                           `(IN ,yv (BALL ,cq5-ms ,xv 1)))
                                 (prop)))
                    (dk-split-all!)
                    (dk-have! `(IN ,yv (CARR K)) (lambda () (subst `(= (CARR K) (PTS ,cq5-ms))) (dk-ass!)))
                    (dk-cite! 'nf-metric-distance 'K xv yv)
                    (dk-cite! 'nf-neg-in-carr 'K yv)
                    (dk-cite! 'nf-add-in-carr 'K xv `((NEG K) ,yv))
                    (dk-cite! 'nf-norm-in-rr 'K zv)
                    (dk-cite! 'nf-norm-nonneg 'K zv)
                    (let* ((d1 (dk-rewrite-h! `(<= ,dv 1) dv (cq5-n zv)))
                           (d2 (dk-rewrite-h! `(NOT (= ,dv 1)) dv (cq5-n zv))))
                      (dk-cite! 'nn-in-rr 1)
                      (dk-have! `(AND (<= ,(cq5-n zv) 1) (NOT (= ,(cq5-n zv) 1))) (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
                      (dk-cite! 'rr-le-ne-lt (cq5-n zv) 1)
                      (use-em `(= ,(cq5-n zv) 0)
                        (lambda ()
                          (dk-cite! 'nf-norm-zero-implies 'K zv)
                          (dk-cite! 'nf-sub-zero-eq 'K xv yv)
                          (subst `(= ,xv ,yv))
                          (dk-cite! 'nf-zero-in-carr 'K)
                          (rfl))
                        (lambda ()
                          (dk-have! `(NOT (= 0 ,(cq5-n zv)))
                            (lambda ()
                              (di)
                              (dk-have! `(= ,(cq5-n zv) 0) (lambda () (subst `(= 0 ,(cq5-n zv))) (rfl)))
                              (dk-only! `(= ,(cq5-n zv) 0) `(NOT (= ,(cq5-n zv) 0)))
                              (prop)))
                          (dk-cite! 'nn-in-rr 0)
                          (dk-have! `(AND (<= 0 ,(cq5-n zv)) (NOT (= 0 ,(cq5-n zv)))) (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
                          (dk-cite! 'rr-le-ne-lt 0 (cq5-n zv))
                          (let ((cj `(AND (IN ,zv (CARR K)) (AND (< 0 ,(cq5-n zv)) (< ,(cq5-n zv) 1)))))
                            (dk-have! cq5-small
                              (lambda ()
                                (ew zv)
                                (dk-conj-close! (lambda () (dk-ass!)))))
                            (dk-only! cq5-small `(NOT ,cq5-small))
                            (prop))))))))))))
    (dk-only! `(IS-DISCRETE-MS ,cq5-ms) `(NOT (IS-DISCRETE-MS ,cq5-ms)))
    (prop)))
(cq5-qed! 'cq5-nondiscrete-small)

;; Z(K) is compact for a local NV field
(sp (make-wff `(FORALL K (IMPLIES (IS-LOCAL-NV-FIELD K) (IS-COMPACT (SUBSPACE-MS ,cq5-ms (NV-INTEGERS K)))))))
(dk-peel!)
(let ((h '(IS-LOCAL-NV-FIELD K)))
  (dk-project! '(IS-NV-FIELD K) (lambda () (mac-h 'is-local-nv-field h)))
  (dk-project! `(NOT (IS-DISCRETE-MS ,cq5-ms)) (lambda () (mac-h 'is-local-nv-field h)))
  (dk-project! `(IS-LOCALLY-COMPACT ,cq5-ms) (lambda () (mac-h 'is-local-nv-field h))))
(dk-cite! 'nv-field-normed 'K)
(dk-cite! 'nf-metric-carrier 'K)
(dk-cite! 'nf-zero-in-carr 'K)
(dk-have! `(IN (ZERO K) (PTS ,cq5-ms)) (lambda () (subst `(= (PTS ,cq5-ms) (CARR K))) (dk-ass!)))
(let* ((lcu `(FORALL lca_ (IMPLIES (IN lca_ (PTS ,cq5-ms))
              (FORSOME lcr_ (AND (POS-RR lcr_) (IS-COMPACT (SUBSPACE-MS ,cq5-ms (CLOSED-BALL ,cq5-ms lca_ lcr_)))))))))
  (dk-project! lcu (lambda () (mac-h 'is-locally-compact `(IS-LOCALLY-COMPACT ,cq5-ms))))
  (let* ((ex (dk-apply! (dk-ctx-form lcu) '(ZERO K)))
         (rv (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (cq5-find-zero f))) "ball") #t)))
    (dk-cite! 'rr-pos-rr-in-rr rv)
    (dk-cite! 'rr-lt-of-pos-rr rv)
    (let ((yv (dk-skolem! (dk-cite! 'cq5-nondiscrete-small 'K) #t)))
      (dk-split-all!)
      (dk-cite! 'nv-integers-compact 'K rv yv)
      (dk-ass!))))
(cq5-qed! 'ccr-local-integers-compact)
