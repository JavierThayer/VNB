;;; theorem-library/diagonalization.scm
;;;
;;; Diagonalization (classical form), PROVEN to QED.
;;; Matches Remark 3.30 in the analysis notes (calculus.pdf):
;;; given a *nested* family of infinite subsets of NN, extract a single
;;; strictly-monotone sequence whose tail lies inside every member.
;;;
;;; Statement:
;;;
;;;   Given S : NN -> INF-SUBSETS(NN) with S(succ k) subset S(k) for all k,
;;;   there is a strictly monotone f : NN -> NN such that for every k
;;;   and every j >= k, f(j) in S(k).
;;;
;;; The tail-in-S_k property (not just f(k) in S(k)) is the load-bearing
;;; conclusion: it lets compactness arguments conclude that pairs at
;;; indices >= k both lie in S_k, which is what forces the diagonal
;;; sequence to be Cauchy when the S_k are nested r_k-balls with r_k -> 0.
;;; (f(k) in S(k) follows by taking j = k.)
;;;
;;; PROOF (was asserted 'informal during library-build; retired here).
;;; The construction is the standard one, mechanised:
;;;   * build f by dependent recursion on NN (dc-on-nn-pred) with step set
;;;       nxt(k,u) = { x in S(succ k) : u < x };
;;;   * the step set is nonempty because each S(succ k), being an infinite
;;;     subset of NN, is unbounded (inf-subset-nn-unbounded);
;;;   * f(0) is a chosen element of S(0), and f(succ k) in nxt(k, f k)
;;;     gives both f(succ k) in S(succ k) and f(k) < f(succ k);
;;;   * f(j) in S(j) for all j by NN-induction (base f(0); step from the
;;;     step membership);
;;;   * STRICTLY-MONO-NN f from the consecutive increments
;;;     (nn-step-strictly-mono);
;;;   * the descending family is a chain S(j) subset S(k) for k<=j
;;;     (nn-nested-subset-chain), so f(j) in S(j) subset S(k).
;;; Every step is a kernel rule; the three named lemmas above plus
;;; dc-on-nn-pred are the asserted leaves (see the proof bill at qed).
;;;
;;; Loaded after cauchy-subsequence (STRICTLY-MONO-NN) and
;;; diagonalization-lemmas (the three supports).

(define dia-stmt
  '(FORALL S
     (IMPLIES (IN S (FUN NN (INF-SUBSETS NN)))
       (IMPLIES (FORALL k
                  (IMPLIES (IN k NN) (SUBSET (S (succ k)) (S k))))
         (FORSOME f
           (AND (STRICTLY-MONO-NN f)
                (FORALL k
                  (IMPLIES (IN k NN)
                    (FORALL j
                      (IMPLIES (IN j NN)
                        (IMPLIES (<= k j) (IN (f j) (S k)))))))))))))

;;; ---- proof-local helpers (dia- prefixed; top-level per loader convention) ----
(define (dia-sqn) (proof-state-focus *ps*))
(define (dia-goal) (wff-formula (sequent-node-assertion (dia-sqn))))
(define (dia-asms) (map wff-formula (sequent-node-assumptions (dia-sqn))))
(define (dia-any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (dia-head? h) (lambda (f) (and (pair? f) (eq? (car f) h))))
(define (dia-find pred) (dia-any pred (dia-asms)))
(define (dia-leaves)
  (filter (lambda (nd) (and (not (sequent-node-grounded? nd)) (null? (sequent-node-in-arrows nd))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (dia-focus! raw)
  (let loop ((ls (dia-leaves)))
    (cond ((null? ls) (error "diagonalization: no open leaf equals" raw))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) raw)
           (set-proof-state-focus! *ps* (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (dia-new thunk)
  (let ((before (dia-asms))) (thunk)
    (dia-any (lambda (f) (not (member f before))) (dia-asms))))
(define (dia-di*)
  (let loop ()
    (let* ((g (dia-goal)) (h (and (pair? g) (car g))))
      (when (memq h '(FORALL IMPLIES)) (di) (loop)))))

;;; ---- the proof ----
(sp (make-wff dia-stmt))
(di) (di)                                    ; Htype = (IN s (FUN NN (INF-SUBSETS NN))) ; Hnest
(define dia-s
  (cadr (dia-find (lambda (f) (and ((dia-head? 'IN) f)
                                   (equal? (caddr f) '(FUN NN (INF-SUBSETS NN))))))))
(define dia-main (dia-goal))

;; Phase 1 -- base witness a in S(0) (and a in NN), via unboundedness at u=0.
(ta 'nn-zero-in)
(fact 'fun-apply-type-c dia-s 'NN '(INF-SUBSETS NN) 0)        ; (IN (s 0) (INF-SUBSETS NN))
(define dia-Ha (dia-new (lambda () (fact 'inf-subset-nn-unbounded `(,dia-s 0) 0))))
(define dia-a (let ((b (dia-new (lambda () (ai dia-Ha))))) (cadr (cadr b))))
(ai `(AND (IN ,dia-a NN) (AND (IN ,dia-a (,dia-s 0)) (< 0 ,dia-a))))
(ai `(AND (IN ,dia-a (,dia-s 0)) (< 0 ,dia-a)))

;; Phase 2 -- the step set NXT and the dc-on-nn-pred totality hypothesis.
(define dia-NXT (subst-free 's dia-s '(VNB-LAMBDA (LIST kx ux) (SEP xx (s (succ kx)) (< ux xx)))))
(define (dia-app k u) (list dia-NXT k u))
(define dia-TOT
  `(FORALL k (IMPLIES (IN k NN)
     (FORALL u (IMPLIES (IN u NN)
       (FORSOME y (AND (IN y NN) (IN y ,(dia-app 'k 'u)))))))))
(cut dia-TOT)
(dia-focus! dia-TOT)
(dia-di*)                                    ; asm (IN kk NN),(IN uu NN) ; goal FORSOME y ...
(define dia-memb (caddr (caddr (caddr (dia-goal)))))   ; (NXT kk uu)
(define dia-kk (cadr dia-memb))
(define dia-uu (caddr dia-memb))
(fact 'nn-succ-closed dia-kk)                ; (IN (succ kk) NN)
(fact 'fun-apply-type-c dia-s 'NN '(INF-SUBSETS NN) `(succ ,dia-kk))
(define dia-Hy (dia-new (lambda () (fact 'inf-subset-nn-unbounded `(,dia-s (succ ,dia-kk)) dia-uu))))
(define dia-yy (let ((b (dia-new (lambda () (ai dia-Hy))))) (cadr (cadr b))))
(ai `(AND (IN ,dia-yy NN) (AND (IN ,dia-yy (,dia-s (succ ,dia-kk))) (< ,dia-uu ,dia-yy))))
(ai `(AND (IN ,dia-yy (,dia-s (succ ,dia-kk))) (< ,dia-uu ,dia-yy)))
(ew dia-yy)
(di)                                         ; (IN yy NN) ; (IN yy (NXT kk uu))
(dia-focus! `(IN ,dia-yy NN)) (ass)
(dia-focus! `(IN ,dia-yy ,(dia-app dia-kk dia-uu)))
(define dia-SEPy `(SEP xx (,dia-s (succ ,dia-kk)) (< ,dia-uu xx)))
(cut `(== ,(dia-app dia-kk dia-uu) ,dia-SEPy))
(dia-focus! `(== ,(dia-app dia-kk dia-uu) ,dia-SEPy)) (lam-b) (qrfl)
(dia-focus! `(IN ,dia-yy ,(dia-app dia-kk dia-uu)))
(subst `(== ,(dia-app dia-kk dia-uu) ,dia-SEPy))
(sep-mi)
(dia-focus! `(IN ,dia-yy (,dia-s (succ ,dia-kk)))) (ass)
(dia-focus! `(< ,dia-uu ,dia-yy)) (ass)

;; Phase 3 -- apply dc-on-nn-pred; extract f, f(0)=a, and the step membership.
(dia-focus! dia-main)
(ta 'nn-is-set)
(define dia-CONCL (dia-new (lambda () (fact 'dc-on-nn-pred 'NN dia-a dia-NXT))))
(define dia-body (dia-new (lambda () (ai dia-CONCL))))
(define dia-f (cadr (cadr dia-body)))
(ai dia-body)
(define dia-body2 (dia-find (lambda (f) (and ((dia-head? 'AND) f) ((dia-head? '=) (cadr f))))))
(ai dia-body2)
(define dia-Hfun `(IN ,dia-f (FUN NN NN)))
(define dia-Hf0  `(= (,dia-f 0) ,dia-a))
(define dia-Hstep
  (dia-find (lambda (f) (and ((dia-head? 'FORALL) f)
                             (let ((b (caddr f))) (and ((dia-head? 'IMPLIES) b)
                                                       ((dia-head? 'IN) (caddr b))))))))
;; Hstep = (FORALL k (IMPLIES (IN k NN) (IN (f (succ k)) (LAM k (f k)))))
(define dia-LAM (car (caddr (caddr (caddr dia-Hstep)))))

;; Phase 4 -- Hstep' : per k, f(succ k) in S(succ k) AND f(k) < f(succ k).
(define dia-HstepP
  `(FORALL k (IMPLIES (IN k NN)
     (AND (IN (,dia-f (succ k)) (,dia-s (succ k))) (< (,dia-f k) (,dia-f (succ k)))))))
(cut dia-HstepP)
(dia-focus! dia-HstepP)
(di)
(define dia-agoal (dia-goal))
(define dia-kp (cadr (cadr (cadr (cadr dia-agoal)))))
(dia-new (lambda () (inst+ dia-Hstep dia-kp)))     ; H = (IN (f(succ kp)) (LAM kp (f kp)))
(define dia-NXTk (list dia-LAM dia-kp (list dia-f dia-kp)))
(define dia-SEPk `(SEP xx (,dia-s (succ ,dia-kp)) (< (,dia-f ,dia-kp) xx)))
(cut `(== ,dia-NXTk ,dia-SEPk))
(dia-focus! `(== ,dia-NXTk ,dia-SEPk)) (lam-b) (qrfl)
(dia-focus! dia-agoal)
(cut `(IN (,dia-f (succ ,dia-kp)) ,dia-SEPk))
(dia-focus! `(IN (,dia-f (succ ,dia-kp)) ,dia-SEPk)) (subst `(== ,dia-SEPk ,dia-NXTk)) (ass)
(dia-focus! dia-agoal)
(sep-me `(IN (,dia-f (succ ,dia-kp)) ,dia-SEPk))
(di)
(dia-focus! `(IN (,dia-f (succ ,dia-kp)) (,dia-s (succ ,dia-kp)))) (ass)
(dia-focus! `(< (,dia-f ,dia-kp) (,dia-f (succ ,dia-kp)))) (ass)

;; Phase 5 -- witness f := the constructed sequence; split the conjunction.
(dia-focus! dia-main)
(ew dia-f)
(di)
(define dia-Gmono `(STRICTLY-MONO-NN ,dia-f))
(define dia-TAIL `(FORALL k (IMPLIES (IN k NN)
                   (FORALL j (IMPLIES (IN j NN)
                     (IMPLIES (<= k j) (IN (,dia-f j) (,dia-s k))))))))

;; Phase 6 -- strict monotonicity from the consecutive increments.
(dia-focus! dia-Gmono)
(bc* 'nn-step-strictly-mono)
(dia-focus! dia-Hfun) (ass)
(define dia-STEPG `(FORALL k (IMPLIES (IN k NN) (< (,dia-f k) (,dia-f (succ k))))))
(dia-focus! dia-STEPG)
(di)
(define dia-m (cadr (cadr (dia-goal))))
(ai (dia-new (lambda () (inst+ dia-HstepP dia-m))))
(dia-focus! `(< (,dia-f ,dia-m) (,dia-f (succ ,dia-m)))) (ass)

;; Phase 7 -- tail property.  PJ : f(j) in S(j); CHAIN : S(j) subset S(k) for k<=j.
(dia-focus! dia-TAIL)
(define dia-PJ `(FORALL j (IMPLIES (IN j NN) (IN (,dia-f j) (,dia-s j)))))
(cut dia-PJ)
(dia-focus! dia-PJ)
(ni)
(dia-focus! `(IN (,dia-f 0) (,dia-s 0)))
(subst dia-Hf0) (ass)
(let ((pjstep (dia-any (lambda (l) (let ((g (wff-formula (sequent-node-assertion l))))
                                     (and ((dia-head? 'FORALL) g)
                                          (let ((b (caddr g))) (and ((dia-head? 'IMPLIES) b)
                                                                    ((dia-head? 'IMPLIES) (caddr b)))))))
                       (dia-leaves))))
  (set-proof-state-focus! *ps* pjstep))
(dia-di*)                                    ; eigen n ; asm (IN n NN), IH ; goal (IN (f(succ n))(s(succ n)))
(define dia-n (cadr (cadr (cadr (dia-goal)))))
(ai (dia-new (lambda () (inst+ dia-HstepP dia-n))))
(dia-focus! `(IN (,dia-f (succ ,dia-n)) (,dia-s (succ ,dia-n)))) (ass)

(dia-focus! dia-TAIL)
(define dia-CHAIN (dia-new (lambda () (fact 'nn-nested-subset-chain dia-s))))
(dia-di*)                                    ; eigen kt, jt ; asms (IN kt NN)(IN jt NN)(<= kt jt)
(define dia-fg (dia-goal))                   ; (IN (f jt)(s kt))
(define dia-jt (cadr (cadr dia-fg)))
(define dia-kt (cadr (caddr dia-fg)))
(inst+ dia-PJ dia-jt)                        ; (IN (f jt)(s jt))
(inst+ (dia-new (lambda () (inst+ dia-CHAIN dia-kt))) dia-jt)   ; (SUBSET (s jt)(s kt))
(fact 'subset-mem-fwd `(,dia-s ,dia-jt) `(,dia-s ,dia-kt) `(,dia-f ,dia-jt))
(ass)

;;; ---- install ----
(if (proof-done? *ps*)
    (qed 'diagonalization)
    (begin (display ";; diagonalization NOT DONE -- open leaves:\n")
           (for-each (lambda (nd) (display ";;   ")
                       (display (expression->string (sequent-node-assertion nd))) (newline))
                     (dia-leaves))))
