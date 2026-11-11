;;; aif-scale-small.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/analytic-from-integral.scm
;;; into library analysis, for the library gate: cited by ccr4d-converge; RR arithmetic.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   aif-scale-small

(dk-skip-links!)   ; as in the source file

;;; ---- helper defines copied from analytic-from-integral.scm ----
(define (aif-real! t) (dk-type! t 'RR))
(define (aif-close!) (if (and (pair? (dk-open-leaves)) (dk-asm? (dk-goal))) (ass)))

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL ail_ (IMPLIES (IN ail_ RR) (IMPLIES (<= 0 ail_)
  (FORALL eps (IMPLIES (POS-RR eps)
    (AND (POS-RR (* eps (recip (+ ail_ 1))))
         (<= (* ail_ (* eps (recip (+ ail_ 1)))) eps)))))))))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'eps)
(fact 'rr-lt-of-pos-rr 'eps)
(aif-real! '(+ ail_ 1))
(dk-have! '(< 0 (+ ail_ 1)) (lambda () (dk-ineq! '(IN ail_ RR) '(<= 0 ail_))))
(dk-have! '(NOT (= (+ ail_ 1) 0))
  (lambda () (di) (dk-absurd! '(IN ail_ RR) '(<= 0 ail_) '(= (+ ail_ 1) 0))))
(dk-have! '(AND (IN (+ ail_ 1) RR) (NOT (= (+ ail_ 1) 0))))
(fact 'rr-recip-closed '(+ ail_ 1))
(fact 'rr-recip-inverse '(+ ail_ 1))
(fact 'rr-recip-pos '(+ ail_ 1))
(define aif-i-v (dk-name! '(recip (+ ail_ 1))))
(subst (list '= '(recip (+ ail_ 1)) aif-i-v))
(dk-have! (list '< 0 aif-i-v) (lambda () (subst (list '= aif-i-v '(recip (+ ail_ 1)))) (ass)))
(define aif-i-ev (list '* 'eps aif-i-v))
(aif-real! aif-i-ev)
(fact 'rr-mul-pos 'eps aif-i-v)
(dk-have! (list '= (list '* '(+ ail_ 1) aif-i-v) 1)
  (lambda () (subst (list '= aif-i-v '(recip (+ ail_ 1)))) (ass)))
(define aif-i-p (begin (aif-real! (list '* 'ail_ aif-i-v)) (dk-name! (list '* 'ail_ aif-i-v))))
(dk-have! (list '= (list '+ aif-i-p aif-i-v) 1)
  (lambda ()
    (subst (list '= aif-i-p (list '* 'ail_ aif-i-v)))
    (dk-have! (list '= (list '+ (list '* 'ail_ aif-i-v) aif-i-v) (list '* '(+ ail_ 1) aif-i-v)) (lambda () (crs)))
    (subst (list '= (list '+ (list '* 'ail_ aif-i-v) aif-i-v) (list '* '(+ ail_ 1) aif-i-v)))
    (aif-close!)))
(dk-have! (list '<= aif-i-p 1)
  (lambda () (dk-ineq! (list 'IN aif-i-p 'RR) (list 'IN aif-i-v 'RR) (list '< 0 aif-i-v)
                       (list '= (list '+ aif-i-p aif-i-v) 1))))
(fact 'rr-one-in)
(dk-have! '(<= 0 eps) (lambda () (dk-ineq! '(IN eps RR) '(< 0 eps))))
(fact 'rr-mul-le-right aif-i-p 1 'eps)
(dk-conj-close!
  (lambda ()
    (if (dk-head-is? (dk-goal) 'POS-RR)
        (begin (fact 'rr-pos-rr-of-lt aif-i-ev) (aif-close!))
        (begin
          (dk-have! (list '= (list '* 'ail_ aif-i-ev) (list '* aif-i-p 'eps))
            (lambda () (subst (list '= aif-i-p (list '* 'ail_ aif-i-v))) (crs)))
          (subst (list '= (list '* 'ail_ aif-i-ev) (list '* aif-i-p 'eps)))
          (aif-real! (list '* aif-i-p 'eps))
          (dk-ineq! '(IN eps RR) (list 'IN (list '* aif-i-p 'eps) 'RR)
                    (list '<= (list '* aif-i-p 'eps) '(* 1 eps)))))))
(qed 'aif-scale-small)

