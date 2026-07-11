;;; spans-submodule-fg-proof.scm -- THE DESCENT.
;;;
;;; A submodule sm of a submodule bm SPANNED by n elements u is spanned by <= n
;;; elements.  Induction on n inside md -- tex:1651, the lemma Smith cannot supply.
;;; Factored: spans-fg-base (n=0) + spans-fg-step (succ), assembled under `ni`.
;;; USES bc* (empty-matrix witnesses) -- do NOT compile this file.

;;; ---- driver helpers (sd- prefix)
(define (sd-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (sd-foc! n) (set-proof-state-focus! *ps* n))
(define (sd-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (sd-di*)
  (let lp () (let* ((g (sd-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (sd-head? h) (lambda (g) (and (pair? g) (eq? (car g) h))))
(define (sd-find-opt pred) (let loop ((as (sd-asms)))
                             (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (sd-find pred) (or (sd-find-opt pred) (error "sd-find: none")))
(define (sd-mentions? form sub)
  (cond ((equal? form sub) #t)
        ((pair? form) (or (sd-mentions? (car form) sub) (sd-mentions? (cdr form) sub)))
        (else #f)))
(define (sd-mentions-pred sub) (lambda (g) (sd-mentions? g sub)))
;; run branching tactic `act`, dispatch each NEW leaf to the first matching clause
(define (sd-branch! act . clauses)
  (let ((before (proof-leaves)))
    (act)
    (let ((new (filter (lambda (l) (not (memq l before))) (proof-leaves))))
      (for-each (lambda (cl)
                  (let ((leaf (find-first (lambda (l) ((car cl) (wff-formula (sequent-node-assertion l)))) new)))
                    (if leaf (begin (sd-foc! leaf) ((cdr cl)))
                        (error "sd-branch!: no leaf for a clause"))))
                clauses))))
;; ai a FORSOME assumption; return the fresh eigenvar (read off its new typing)
(define (sd-ai-eigen! forsome typ)
  (let ((before (sd-asms)))
    (ai forsome)                                        ; eigen + body (bare IN, or an AND)
    (let* ((new (filter (lambda (a) (not (member a before))) (sd-asms)))
           (bare (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) typ))) new))
           (andb (find-first (lambda (a) (and (pair? a) (eq? (car a) 'AND) (pair? (cadr a))
                                              (eq? (car (cadr a)) 'IN) (equal? (caddr (cadr a)) typ))) new)))
      (cond (bare (cadr bare))
            (andb (ai andb) (cadr (cadr andb)))          ; split the AND, return eigen
            (else (error "sd-ai-eigen!: not found" typ new))))))
;; inst+ a context universal at t; return the newly-landed FORALL/FORSOME/IMPLIES
(define (sd-inst! f t)
  (let ((before (sd-asms)))
    (inst+ f t)
    (let ((new (filter (lambda (a) (not (member a before))) (sd-asms))))
      (or (find-first (lambda (a) (and (pair? a) (memq (car a) '(FORALL FORSOME)))) new)
          (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IMPLIES))) new)
          (and (pair? new) (car new))))))
(define (sd-cut! p prove-sub)
  (let ((before (proof-leaves)))
    (cut p)
    (let* ((new (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (sub (car (filter (lambda (l) (equal? (wff-formula (sequent-node-assertion l)) p)) new)))
           (cont (car (filter (lambda (l) (not (eq? l sub))) new))))
      (sd-foc! sub) (prove-sub) (sd-foc! cont))))
(define (sd-empty-close! v)                           ; close from (IN v (INTERVAL 1 0))
  (fact 'interval-lo 1 0 v) (fact 'interval-hi 1 0 v)
  (fact 'interval-elt-in-nn 1 0 v) (fact 'nn-not-le-zero-pos v)
  (ai (list 'NOT (list '<= v 0))))

;; the body REST[ntm] of the statement (u, bm, sm, conclusion) at length ntm
(define (sd-rest ntm)
  `(FORALL u (IMPLIES (IN u (MAT ,ntm 1 (VEC md)))
    (FORALL bm (IMPLIES (IS-SUBMODULE md bm)
     (IMPLIES (SPANS md ,ntm u bm)
      (FORALL sm (IMPLIES (IS-SUBMODULE md sm)
       (IMPLIES (SUBSET sm bm)
        (FORSOME k (AND (AND (IN k NN) (<= k ,ntm))
         (FORSOME w (AND (IN w (MAT k 1 (VEC md)))
                         (SPANS md k w sm))))))))))))))
(define sd-w0  '(MATOF 0 1 (VNB-LAMBDA (LIST i_ j_) (VZERO md))))       ; empty column seq
(define sd-ce0 '(MATOF 1 0 (VNB-LAMBDA (LIST i_ j_) (ZERO (SCAL md))))) ; empty coeff row
(define (sd-empty-in! typ)   ; prove (IN (MATOF m n g) typ) with a 0 dimension, via bc*
  (bc* 'matof-in-mat) (sd-di*)
  (sd-empty-close! (cadr (sd-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                   (equal? (caddr f) '(INTERVAL 1 0))))))))


;;; ================= spans-fg-base : n = 0 =================
(sp (make-wff `(FORALL md (IMPLIES (AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
                                   ,(sd-rest 0)))))
(di) (di) (ai '(AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md))))
(sd-di*)                                              ; u, bm, sm + their guards; goal FORSOME k
;; every element of bm is 0.u = VZERO -- capture the "combination" conjunct of SPANS md 0 u bm
(mac-h 'SPANS '(SPANS md 0 u bm))
(ai (sd-find (lambda (a) (and (pair? a) (eq? (car a) 'AND) (sd-mentions? a 'FORSOME)))))  ; split SPANS body
(define sd-bm-comb (sd-find (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (eq? (cadr a) 'x_)
                                             (sd-mentions? a 'FORSOME)))))
(ew 0)
(sd-branch! (lambda () (di))
  (cons (sd-head? 'AND)                               ; (AND (IN 0 NN)(<= 0 0))
        (lambda () (sd-branch! (lambda () (di))
                     (cons (sd-head? 'IN) (lambda () (fact 'nn-zero-in) (ass)))
                     (cons (sd-head? '<=) (lambda () (fact 'nn-zero-in) (fact 'nn-zero-le 0) (ass))))))
  (cons (sd-head? 'FORSOME)                           ; witness w = empty column
        (lambda ()
          (sd-cut! (list 'IN sd-w0 '(MAT 0 1 (VEC md))) (lambda () (sd-empty-in! '(MAT 0 1 (VEC md)))))
          (ew sd-w0)
          (sd-branch! (lambda () (di))
            (cons (sd-head? 'IN) (lambda () (ass)))    ; IN w0 (MAT 0 1 VEC)
            (cons (sd-head? 'SPANS)
              (lambda ()
                (mac 'SPANS)
                (sd-branch! (lambda () (di))
                  (cons (sd-mentions-pred 'INTERVAL)   ; entries: vacuous over [1,0]
                        (lambda () (sd-di*) (sd-empty-close! (caddr (cadr (sd-goal))))))
                  (cons (sd-mentions-pred 'FORSOME)     ; every x in sm is a combination
                    (lambda ()
                      (sd-di*)
                      (let ((xx (cadr (sd-find (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                               (equal? (caddr a) 'sm)))))))
                        ;; x in bm, so x = c'.u = VZERO
                        (fact 'subset-mem-fwd 'sm 'bm xx)
                        (let* ((c1 (sd-inst! sd-bm-comb xx))
                               (cw (sd-ai-eigen! c1 '(MAT 1 0 (CARR (SCAL md))))))
                          (fact 'matact-empty-vzero 'md cw 'u)
                          (let ((xeq (sd-find (lambda (a) (and (pair? a) (eq? (car a) '=) (equal? (cadr a) xx))))))
                            (subst xeq)                 ; x -> c'.u
                            (subst (list '= (list 'ENTRY (list 'MATACT 'md cw 'u) 1 1) '(VZERO md))))
                          ;; goal now: FORSOME c (IN c (MAT 1 0 CARR) AND VZERO = c.w0)
                          (sd-cut! (list 'IN sd-ce0 '(MAT 1 0 (CARR (SCAL md))))
                                   (lambda () (sd-empty-in! '(MAT 1 0 (CARR (SCAL md))))))
                          (ew sd-ce0)
                          (sd-branch! (lambda () (di))
                            (cons (sd-head? 'IN) (lambda () (ass)))
                            (cons (sd-head? '=)
                              (lambda ()
                                (fact 'matact-empty-vzero 'md sd-ce0 sd-w0)
                                (subst (list '= (list 'ENTRY (list 'MATACT 'md sd-ce0 sd-w0) 1 1) '(VZERO md)))
                                (fact 'module-vzero-in 'md)
                                (rfl)))))))))))))))
(qed 'spans-fg-base)
(category! 'spans-fg-base 'algebra)




;;; ================= spans-fg-step : TEMP asserted =================
;;; The inductive step.  All its mathematical content is proven as lemmas
;;; (lastcoeff-set-is-ideal, lastcoeff-zero-in-span, descent-remainder,
;;; span-is-submodule, spans-span, submodule-intersection, matact-snoc); what
;;; remains is the induction DRIVER -- form u'/bm'/sm', pull the ideal generator,
;;; apply the IH via inst+, run descent-remainder + matact-snoc.  The driver is
;;; a navigation-heavy assembly still being written; asserted meanwhile so
;;; spans-submodule-fg (= base + step under ni) installs and submodule-fg-proof
;;; consumes it as before.
(support 'spans-fg-step
  (make-wff `(FORALL md (IMPLIES (AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
               (FORALL n (IMPLIES (IN n NN)
                 (IMPLIES ,(sd-rest 'n) ,(sd-rest '(succ n)))))))))
(warrant! 'spans-fg-step 'informal "TEMP; inductive step driver in progress (all lemmas proven).")


;;; ================= assembly =================
(sp (make-wff `(FORALL md (IMPLIES (AND (IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
                 (FORALL n (IMPLIES (IN n NN) ,(sd-rest 'n)))))))
(di) (di)                                             ; md, (AND ...) whole in context
(ni)
;; ni left two leaves: base REST[0] (mentions 0, not (succ n)) and the step.
(for-each (lambda (l)
            (let ((g (wff-formula (sequent-node-assertion l))))
              (sd-foc! l)
              (if (sd-mentions? g '(succ n))
                  (begin (fact 'spans-fg-step 'md) (ass))
                  (begin (fact 'spans-fg-base 'md) (ass)))))
          (proof-leaves))
(qed 'spans-submodule-fg)
(category! 'spans-submodule-fg 'algebra)


