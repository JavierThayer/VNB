;;; ccr-ch3d-ultra.scm -- wave of 2026-11-09/10 (agent CCR-1109-B4), wired 2026-11-10 from scratchpad/ccr1109b4/ccr-ch3d-ultra.scm.
;;; Library: analysis.

;;; ccr-ch3d-ultra.scm -- CCR.pdf chapter 3, Proposition 3.6, the ultrametric inequality on the commutant of
;;; an irreducible T WITHOUT the invertibility hypothesis of ccr-3-6-ultra (CCR-1109-B3).  Agent CCR-1109-B4,
;;; wave 2026-11-09.  Destination: theorem-library/ccr-ch3d-ultra.scm.  Library: analysis.  Prefix ce2-.
;;;
;;;   ccr-3-6-ultrametric          K a local NV field, T irreducible, S, R n-by-n commuting with T:
;;;                                |det(S + R)| <= max(|det S|, |det R|)
;;;
;;; Route: the hypothesis "det Y /= 0 implies Y has a two-sided inverse" of ccr-3-6-ultra is discharged by
;;; invertible-iff-det-nonzero (la-det-adjoint, LA-DET 2026-10-18: Cramer's rule over a field) on the ring
;;; view of K, which is a field ring (cq4-view-field-ring, CCR-1109-B2).
;;;
;;; LOAD WINDOW: after theorem-library/ccr-ch3c-pb (CCR-1109-B3: ccr-3-6-ultra), the latest citation;
;;; ccr-ch3b-alg (CCR-1109-B2: cq4-view-field-ring), la-det-adjoint (invertible-iff-det-nonzero) and the
;;; normed-field-ring-view-* equations load earlier.

(define ce2-v '(NORMED-FIELD-AS-COMMUTATIVE-RING K))
(define (ce2-n x) `((FNRM K) ,x))
(define (ce2-mat m n) `(MAT ,m ,n (CARR K)))
(define (ce2-mm a b) `(MATMUL ,ce2-v ,a ,b))
(define ce2-id `(IDENTMAT ,ce2-v n))

(define (ce2-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; ce2: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (f) (display ";;      | ") (display (expression->string f)) (newline))
                              (let ((a (dk-asms-of l))) (list-head a (min 14 (length a))))))
                  (dk-open-leaves))))
  (qed name))

(define (ce2-view!)
  (dk-cite! 'normed-field-as-commutative-ring-is-commutative-ring 'K)
  (dk-cite! 'commutative-ring-is-ring ce2-v)
  (for-each (lambda (r) (dk-cite! r 'K))
            '(normed-field-ring-view-carr normed-field-ring-view-add normed-field-ring-view-mul
              normed-field-ring-view-one normed-field-ring-view-zero normed-field-ring-view-neg)))

;;; ---- Proposition 3.6, ultrametric half, on the commutant of an irreducible T
(define (ce2-inv-hyp a)
  `(IMPLIES (NOT (= (DET ,ce2-v n ,a) (ZERO K)))
     (FORSOME cd8p_ (AND (IN cd8p_ ,(ce2-mat 'n 'n))
       (AND (= ,(ce2-mm 'cd8p_ a) ,ce2-id) (= ,(ce2-mm a 'cd8p_) ,ce2-id))))))

(sp (make-wff `(FORALL K (IMPLIES (IS-LOCAL-NV-FIELD K) (FORALL n (IMPLIES (IN n NN) (FORALL tm
  (IMPLIES (IS-IRREDUCIBLE-MAT K n tm)
  (FORALL sa (IMPLIES (IN sa ,(ce2-mat 'n 'n)) (FORALL ra (IMPLIES (IN ra ,(ce2-mat 'n 'n))
    (IMPLIES (= ,(ce2-mm 'sa 'tm) ,(ce2-mm 'tm 'sa))
    (IMPLIES (= ,(ce2-mm 'ra 'tm) ,(ce2-mm 'tm 'ra))
      (<= ,(ce2-n `(DET ,ce2-v n (MATADD ,ce2-v sa ra)))
          (MAX ,(ce2-n `(DET ,ce2-v n sa)) ,(ce2-n `(DET ,ce2-v n ra))))))))))))))))))
(dk-peel!)
(dk-project! '(IS-NV-FIELD K) (lambda () (mac-h 'is-local-nv-field '(IS-LOCAL-NV-FIELD K))))
(dk-cite! 'nv-field-normed 'K)
(ce2-view!)
(dk-cite! 'cq4-view-field-ring 'K)
(for-each
  (lambda (a)
    (dk-have! `(IN ,a (MAT n n (CARR ,ce2-v))) (lambda () (subst `(= (CARR ,ce2-v) (CARR K))) (dk-ass!)))
    (dk-have! (ce2-inv-hyp a)
      (lambda ()
        (di)
        (dk-have! `(NOT (= (DET ,ce2-v n ,a) (ZERO ,ce2-v)))
          (lambda () (subst `(= (ZERO ,ce2-v) (ZERO K))) (dk-ass!)))
        (let ((iff (dk-cite! 'invertible-iff-det-nonzero ce2-v 'n a)))
          (dk-have! `(IS-INVERTIBLE-MAT ,ce2-v n ,a)
            (lambda () (dk-only! iff `(NOT (= (DET ,ce2-v n ,a) (ZERO ,ce2-v)))) (prop))))
        (let* ((u (dk-landed-1 (lambda () (mac-h 'IS-INVERTIBLE-MAT `(IS-INVERTIBLE-MAT ,ce2-v n ,a)))))
               (pv (dk-skolem! u)))
          (dk-split-all!)
          (ew pv)
          (dk-conj-close!
            (lambda ()
              (if (dk-asm? (dk-goal)) (dk-ass!)
                  (begin (subst `(= (CARR K) (CARR ,ce2-v))) (dk-ass!)))))))))
  '(sa ra))
(dk-fact! 'ccr-3-6-ultra 'K 'n 'tm 'sa 'ra)
(dk-ass!)
(ce2-done! 'ccr-3-6-ultrametric)
(topic! 'ccr-3-6-ultrametric 'analysis)
(gloss! 'ccr-3-6-ultrametric
  "CCR Prop. 3.6 (ultrametric half): on the commutant of an irreducible T over a local NV field,
   |det(S + R)| <= max(|det S|, |det R|).")
