;;; scratch/in-rr-proto.scm -- prototype of the (in-rr) typing tactic.
;;; Proves a goal (IN <arith-term> D) for a ring domain D in {RR,ZZ,QQ,CC}
;;; by structural recursion: to-binary, then fun-apply-type-c + ci driven
;;; FORWARD via fact (bc on fun-apply-type-c hangs -- higher-order conclusion).
;;; NOT in load.scm.

(define (irr-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (irr-leaves) (proof-leaves))
(define (irr-focus-goal! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw)) (irr-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (irr-focus-asm! raw)
  (let ((s (any-pred (lambda (s) (any-pred (lambda (w) (equal? (wff-formula w) raw))
                                           (sequent-node-assumptions s)))
                     (irr-leaves))))
    (and s (set-proof-state-focus! *ps* s) s)))
(define (irr-in-ctx? raw)
  (any-pred (lambda (w) (equal? (wff-formula w) raw))
            (sequent-node-assumptions (proof-state-focus *ps*))))
(define (irr-find-fun-dom g S)
  ;; find A with (IN g (FUN A S)) among current assumptions; return A or #f
  (let ((a (any-pred (lambda (w)
                       (let ((wf (wff-formula w)))
                         (and (pair? wf) (eq? (car wf) 'IN) (equal? (cadr wf) g)
                              (pair? (caddr wf)) (eq? (car (caddr wf)) 'FUN)
                              (equal? (caddr (caddr wf)) S))))
                     (sequent-node-assumptions (proof-state-focus *ps*)))))
    (and a (cadr (caddr (wff-formula a))))))
(define (irr-op-typ op D)
  (string->symbol (string-append (symbol->string op) "-in-fun-" (symbol->string D))))

;; Establish (IN t S) in the current leaf's context; leave focus on the
;; continuation leaf (which carries it as an assumption).
(define (irr-ensure! t S)
  (let ((mem (list 'IN t S)))
    (if (irr-in-ctx? mem)
        #t
        (begin
          (cut mem)
          (irr-focus-goal! mem)
          (irr-close!)
          (irr-focus-asm! mem)))))

;; Close the current focus goal, assumed to be (IN term S) with term already
;; in binplus/bintimes/binneg/atom form (to-binary done at top level).
(define *irr-depth* 0)
(define (irr-close!)
  (set! *irr-depth* (+ *irr-depth* 1))
  (when (> *irr-depth* 25) (error "irr: depth guard" (irr-goal)))
  (let* ((g (irr-goal)) (term (cadr g)) (S (caddr g)))
    (display ";;;   irr-close! d=")(display *irr-depth*)(display " goal=")(write g)(newline)
    (cond
      ((irr-in-ctx? g) (ass))
      ((symbol? term) (ass))
      ((number? term) (ass))
      ((and (pair? term) (eq? (car term) 'binneg))
       (let ((a (cadr term)))
         (irr-ensure! a S)
         (irr-focus-goal! g)
         (quietly (lambda ()
           (fact (irr-op-typ 'binneg S))
           (fact 'fun-apply-type-c 'binneg S S a)
           (ass)))))
      ((and (pair? term) (memq (car term) '(binplus bintimes)))
       (let* ((op (car term)) (a (cadr term)) (b (caddr term))
              (lst (list 'LIST a b)) (tup (list op lst)) (cart (list 'CARTESIAN S S)))
         (fact 'apply-tupling-2 op a b)
         (subst (list '== (list op a b) tup))
         (irr-ensure! lst cart)
         (irr-focus-goal! (list 'IN tup S))
         (quietly (lambda ()
           (fact (irr-op-typ op S))
           (fact 'fun-apply-type-c op cart S lst)
           (ass)))))
      ((and (pair? term) (eq? (car term) 'LIST))
       ;; (IN (LIST a1 a2 ..) (CARTESIAN S1 S2 ..)) -> ci spawns (IN ai Si).
       ;; Close ONLY those specific component goals (NOT the whole frontier).
       (ci)
       (for-each (lambda (elt fac)
                   (or (irr-focus-goal! (list 'IN elt fac))
                       (error "irr: cannot focus component" (list 'IN elt fac)))
                   (irr-close!))
                 (cdr term) (cdr S)))
      (else
       ;; general unary application (g a) where (IN g (FUN A S)) is in context
       (let ((dom (and (pair? term) (= (length term) 2)
                       (irr-find-fun-dom (car term) S))))
         (if dom
             (let ((gfn (car term)) (a (cadr term)))
               (irr-ensure! a dom)
               (irr-focus-goal! g)
               (quietly (lambda () (fact 'fun-apply-type-c gfn dom S a) (ass))))
             (ass)))))))

(define (in-rr)
  (to-binary)
  (irr-close!)
  (quietly (lambda () (ass-all)))
  (proof-done? *ps*))

;;; ---- tests ----
(define (test name goal)
  (sp goal)
  (let loop ((n 0)) (when (and (< n 6) (pair? (irr-leaves))
                               (let ((g (irr-goal))) (and (pair? g) (memq (car g) '(FORALL IMPLIES)))))
                      (di) (loop (+ n 1))))
  (let ((ok (in-rr)))
    (display ";;; TEST ")(display name)(display " => done?=")(display ok)
    (display "  leaves=")(display (length (irr-leaves)))(newline)))

(test "flat (- u v)"
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR) (IN (- u v) RR))))))
(test "nested (- (- u v) w)"
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR) (FORALL w (IMPLIES (IN w RR)
     (IN (- (- u v) w) RR))))))))
(test "mixed (* u (- v w))"
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR) (FORALL w (IMPLIES (IN w RR)
     (IN (* u (- v w)) RR))))))))
