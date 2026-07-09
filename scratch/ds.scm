(define (ASMS) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (gf) (and *ps* (not (proof-done? *ps*)) (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
;; find Caratheodory factor P from hyp (forall X (implies (in X rr) (= (- (fsym X)(fsym a)) (* (P X) ..))))
(define (factor-hyp fsym)
  (let loop ((as (ASMS)))
    (cond ((null? as) #f)
          ((let ((h (car as)))
             (and (pair? h) (eq? (car h) 'FORALL)
                  (let ((bod (caddr h)))
                    (and (pair? bod) (eq? (car bod) 'IMPLIES)
                         (let ((eq (caddr bod)))
                           (and (pair? eq) (eq? (car eq) '=)
                                (pair? (cadr eq)) (eq? (car (cadr eq)) '-)
                                (pair? (cadr (cadr eq))) (eq? (car (cadr (cadr eq))) fsym)
                                h))))))
           => (lambda (h) h))
          (else (loop (cdr as))))))
(define (factor-phi fsym) (let ((h (factor-hyp fsym))) (car (cadr (caddr (caddr (caddr h)))))))
(support 'rr-fun-sum-closed
  '(FORALL f (FORALL g (FORALL x (IMPLIES (IN f (FUN RR RR)) (IMPLIES (IN g (FUN RR RR)) (IMPLIES (IN x RR)
     (IN (+ (f x) (g x)) RR))))))))
(support 'caratheodory-sum-factor
  '(FORALL u1 (FORALL u2 (FORALL v1 (FORALL v2 (FORALL p (FORALL q (FORALL d
     (IMPLIES (= (- u1 v1) (* p d)) (IMPLIES (= (- u2 v2) (* q d))
       (= (- (+ u1 u2) (+ v1 v2)) (* (+ p q) d))))))))))))
(define REFOLD '(begin (mac 'IS-CONTINUOUS-AT) (grind) (ass-all) (bc* 'rr-is-metric-space) (ass-all)))
(sp '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
     (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT g a M))
              (IS-DIFF-AT (VNB-LAMBDA x (+ (f x) (g x))) a (+ L M)))))))))
(grind)
(define PF (factor-phi 'f)) (define PG (factor-phi 'g))
(define HF (factor-hyp 'f)) (define HG (factor-hyp 'g))
(define W (list 'VNB-LAMBDA 'xw (list '+ (list PF 'xw) (list PG 'xw))))
(display ";; PF=") (write PF) (display " PG=") (write PG) (newline)
(mac 'IS-DIFF-AT)
(di) (lam-t)(di)(di) (bc* 'rr-fun-sum-closed () (ass)(ass)(ass))     ; [1] outer typing
(di) (ass)                                                          ; [2] a in rr
(di) (bc* 'rr-add-closed () (begin (di)(ass-all)))                  ; [3] L+M in rr
(ew W)
(di) (lam-t)(di)(di) (bc* 'rr-fun-sum-closed () (ass)(ass)(ass))     ; [4] W typing
(di) (bc* 'sum-continuous-at ()
        (mac 'IS-CONTINUOUS-AT) (grind)(ass-all)(bc* 'rr-is-metric-space)(ass-all)
        (mac 'IS-CONTINUOUS-AT) (grind)(ass-all)(bc* 'rr-is-metric-space)(ass-all))  ; [5] continuity
(di) (lam-b) (subst (list '= (list PF 'a) 'l)) (subst (list '= (list PG 'a) 'm)) (rfl)  ; [6] phi(a)=L+M
(di)(di) (lam-b)                                                    ; [7] factorization: intro x
(define XV (cadr (cadr (cadr (cadr (gf))))))  ; eigenvar from (= (- (+ (f XV)..)..)..)
(inst+ HF XV) (inst+ HG XV)
(bc* 'caratheodory-sum-factor () (ass)(ass))
(display ";; deriv-sum DONE? ") (display (proof-done? *ps*)) (display "  focus: ") (write (gf)) (newline)
