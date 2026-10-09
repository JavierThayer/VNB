;;; ====================================================================
;;; theorem-library/lebesgue-measure-line.scm -- MEASURE-3 (the join),
;;; 2026-10-09.
;;;
;;; Lebesgue measure on the line, written as the Caratheodory restriction
;;;
;;;     RES(lam*, CARATHEODORY-SETS(RR, lam*)),
;;;     lam* = METHOD-I-OUTER(RR, CLOSED-INTERVALS, ols_ |-> INTERVAL-LENGTH(ols_)),
;;;
;;; with no new name.  For each of the four kinds of interval with real
;;; endpoints a <= b, the interval is a member of CARATHEODORY-SETS(RR, lam*)
;;; and its measure is b - a; a point is a member with measure 0.
;;;
;;; This file joins two others and proves nothing new about either:
;;;   theorem-library/metric-outer-measure.scm  -- lebesgue-intervals-measurable
;;;   theorem-library/lebesgue-interval-length.scm -- lebesgue-outer-{cc,oo,co,oc}int,
;;;                                                   lebesgue-outer-point
;;; together with caratheodory-sets-membership, caratheodory-measurable-sigma-algebra,
;;; caratheodory-null-measurable, res-apply and fun-codomain-iff.
;;;
;;;   lebesgue-measure-ccint, lebesgue-measure-ooint, lebesgue-measure-coint,
;;;   lebesgue-measure-ocint, lebesgue-measure-point
;;; ====================================================================

(define lml-lam '(METHOD-I-OUTER RR CLOSED-INTERVALS (VNB-LAMBDA ols_ CLOSED-INTERVALS (INTERVAL-LENGTH ols_))))
(define lml-cs (list 'CARATHEODORY-SETS 'RR lml-lam))
(define lml-mu (list 'RES lml-lam lml-cs))
(define lml-pw '(POWER RR))

;;; the outer measure, its typing, the sigma-algebra of its measurable sets and
;;; the inclusion of that family in POWER(RR)
(define (lml-setting!)
  (fact 'lebesgue-outer-measure)
  (let ((om (list 'IS-OUTER-MEASURE 'RR lml-lam))
        (ty (list 'IN lml-lam (list 'FUN lml-pw 'RR-POS-STAR))))
    (dk-project! ty 'IS-OUTER-MEASURE om)
    (dk-project! (list 'IN lml-lam (list 'FUN lml-pw)) 'fun-codomain-iff ty)
    (fact 'caratheodory-measurable-sigma-algebra 'RR lml-lam)
    (dk-project! (list 'SUBSET lml-cs lml-pw) 'IS-SIGMA-ALGEBRA (list 'IS-SIGMA-ALGEBRA 'RR lml-cs))))

;;; with (IN X (POWER RR)) and IS-CARATHEODORY-MEASURABLE(RR, lam*, X) in context:
;;; land (IN X C) and ((RES lam* C) X) = (lam* X); return that equation
(define (lml-in-cs-res! x)
  (let* ((iff (dk-cite! 'caratheodory-sets-membership 'RR lml-lam x)))
    (dk-have! (caddr iff) (lambda () (dk-conj-close! dk-ass!)))
    (ai iff)
    (detach! (list 'IMPLIES (caddr iff) (cadr iff)))
    (dk-have! (list 'AND (list 'IN lml-lam (list 'FUN lml-pw))
                    (list 'AND (list 'SUBSET lml-cs lml-pw) (list 'IN x lml-cs)))
              (lambda () (dk-conj-close! dk-ass!)))
    (dk-cite! 'res-apply lml-pw lml-cs lml-lam x)))

;;; the goal (AND (IN X C) (= ((RES lam* C) X) V)) from the res equation and
;;; (= (lam* X) V) in context
(define (lml-close! res)
  (dk-conj-close!
    (lambda ()
      (if (not (dk-ass!))
          (begin (subst res) (ass))))))

;;; the four intervals
(define (lml-interval-proof! iv sub-thm outer-thm name)
  (sp (make-wff (forall-guarded '(a_ b_) '((IN a_ RR) (IN b_ RR) (<= a_ b_))
     (list 'AND (list 'IN iv lml-cs) (list '= (list lml-mu iv) '(- b_ a_))))))
  (dk-peel!)
  (fact 'lebesgue-intervals-measurable 'a_ 'b_)
  (dk-split-all!)
  (lml-setting!)
  (fact sub-thm 'a_ 'b_)
  (fact 'subset-rr-in-power-rr iv)
  (let ((res (lml-in-cs-res! iv)))
    (fact outer-thm 'a_ 'b_)
    (lml-close! res))
  (qed name)
  (topic! name 'set-quotient))

(lml-interval-proof! '(CCINT a_ b_) 'ccint-subset-rr 'lebesgue-outer-ccint 'lebesgue-measure-ccint)
(lml-interval-proof! '(OOINT a_ b_) 'ooint-subset-rr 'lebesgue-outer-ooint 'lebesgue-measure-ooint)
(lml-interval-proof! '(COINT a_ b_) 'coint-subset-rr 'lebesgue-outer-coint 'lebesgue-measure-coint)
(lml-interval-proof! '(OCINT a_ b_) 'ocint-subset-rr 'lebesgue-outer-ocint 'lebesgue-measure-ocint)

;;; a point: null, hence measurable (caratheodory-null-measurable), measure 0
(sp (make-wff (forall-guarded '(x_) '((IN x_ RR))
   (list 'AND (list 'IN '(SINGLETON x_) lml-cs) (list '= (list lml-mu '(SINGLETON x_)) 0)))))
(dk-peel!)
(lml-setting!)
(let ((sx '(SINGLETON x_)))
  (dk-have! (list 'SUBSET sx 'RR)
    (lambda ()
      (mac 'subset-def)
      (let* ((zv (dk-di-var!))
             (iff (dk-cite! 'singleton-membership 'x_ zv)))
        (ai iff) (detach! (list 'IMPLIES (cadr iff) (caddr iff))) (dk-split-all!)
        (subst (list '= zv 'x_))
        (ass))))
  (fact 'subset-rr-in-power-rr sx)
  (fact 'lebesgue-outer-point 'x_)
  (fact 'caratheodory-null-measurable 'RR lml-lam sx)
  (let ((res (lml-in-cs-res! sx)))
    (lml-close! res)))
(qed 'lebesgue-measure-point)
(topic! 'lebesgue-measure-point 'set-quotient)

(gloss! 'lebesgue-measure-ccint
  "Lebesgue measure of a closed interval: [a, b] is Lebesgue measurable and its measure
   (the Caratheodory restriction of Lebesgue outer measure) is b - a.")
(gloss! 'lebesgue-measure-point
  "A point is Lebesgue measurable, of Lebesgue measure 0.")
