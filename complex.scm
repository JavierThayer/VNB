;;; complex.scm -- CC as a ring and metric space; completeness axiom
;;;
;;; CC-RING = [CC, lambda([x,y], x+y), lambda([x,y], x*y), lambda([x], -x), 0, 1]
;;; CC-MS   = [CC, lambda([x,y], magnitude(x-y))]
;;;
;;; IS-RING(CC-RING) and IS-METRIC-SPACE(CC-MS) are taken as axioms.
;;; Their proofs from the axioms in number-systems.scm are straightforward
;;; but require FUN-typing infrastructure not yet developed.
;;;
;;; Completeness (every Cauchy sequence converges) is taken as an axiom.

;;; -----------------------------------------------------------------------
;;; CC-RING: CC as a ring

(def-constant 'CC-RING
  (list 'cc-ring-def
        '(= CC-RING (LIST CC
                      (VNB-LAMBDA (LIST x y) (+ x y))
                      (VNB-LAMBDA (LIST x y) (* x y))
                      (VNB-LAMBDA (LIST x) (- x))
                      0
                      1))))

(theory-add-axiom! *current-theory* 'cc-ring-def
  '(= CC-RING (LIST CC
                (VNB-LAMBDA (LIST x y) (+ x y))
                (VNB-LAMBDA (LIST x y) (* x y))
                (VNB-LAMBDA (LIST x) (- x))
                0
                1)))

(theory-add-axiom! *current-theory* 'cc-is-ring
  '(IS-RING CC-RING))

;;; -----------------------------------------------------------------------
;;; The structure CC-MS

;;; CC-MS is the list [CC, lambda([x,y], magnitude(x-y))].
;;; The lambda is a VNB functoid: a function from CARTESIAN(CC,CC) to RR.
(def-constant 'CC-MS
  (list 'cc-ms-def
        '(= CC-MS (LIST CC (VNB-LAMBDA (LIST x y) (magnitude (- x y)))))))

(theory-add-axiom! *current-theory* 'cc-ms-def
  '(= CC-MS (LIST CC (VNB-LAMBDA (LIST x y) (magnitude (- x y))))))

;;; -----------------------------------------------------------------------
;;; CC-MS is a metric space

(theory-add-axiom! *current-theory* 'cc-is-metric-space
  '(IS-METRIC-SPACE CC-MS))

;;; -----------------------------------------------------------------------
;;; Completeness of CC-MS
;;;
;;; Every Cauchy sequence in CC converges in CC.
;;; "Cauchy" and "converges" are stated directly in terms of magnitude.
;;;
;;; eps > 0  is written  (IN eps RR) and (<= 0 eps) and (NOT (= eps 0)).

(theory-add-axiom! *current-theory* 'cc-complete
  '(FORALL f
     (IMPLIES
       ;; f : NN -> CC is Cauchy
       (AND (IN f (FUN NN CC))
            (FORALL eps
              (IMPLIES (AND (IN eps RR) (<= 0 eps) (NOT (= eps 0)))
                (FORSOME N (IN N NN)
                  (FORALL m (IMPLIES (IN m NN)
                    (FORALL n (IMPLIES (IN n NN)
                      (IMPLIES (AND (<= N m) (<= N n))
                        (<= (magnitude (- (f m) (f n))) eps))))))))))
       ;; then f converges to some L in CC
       (FORSOME L (IN L CC)
         (FORALL eps
           (IMPLIES (AND (IN eps RR) (<= 0 eps) (NOT (= eps 0)))
             (FORSOME N (IN N NN)
               (FORALL n (IMPLIES (IN n NN)
                 (IMPLIES (<= N n)
                   (<= (magnitude (- (f n) L)) eps)))))))))))
