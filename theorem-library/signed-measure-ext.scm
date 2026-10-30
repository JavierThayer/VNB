;;; signed-measure-ext.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/mf/mf-ext.scm, scratchpad/mf/mf-psum.scm, scratchpad/mf/mf-conv.scm.
;;; Library: measure.

;;; mf-ext.scm -- arithmetic on the extended line [-inf, +inf] for signed measures: EXT-NEG, EXT-ADD.
;;; Agent M-F, 2026-10-29.  DESTINATION: theorem-library/signed-measure-ext.scm.  Library: measure.
;;; Helper prefix: mfe-.  Load window: after structure-library/signed-measure.scm (mf-vocab.scm).

   ; KIT-9 link skipping, opt-in per file (integrator, 2026-10-29)

;; keep the named formulas and run prop -- only on the leaf the keep was written for (when keep
;; finds that sequent already proven it closes the leaf and the focus moves; prop must not follow it)
(dk-skip-links!)   ; KIT-9 link skipping, opt-in per file (wave-2 files were developed with it on)

(define (mfe-keep-prop! . fs)
  (let ((leaf (proof-state-focus *ps*)))
    (apply keep fs)
    (if (not (sequent-node-grounded? leaf)) (prop))))

(define (mfe-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l) (display ";; MFE OPEN ") (display (expression->string (dk-goal-of l))) (newline))
                (dk-open-leaves)))
  (qed name) (topic! name 'analysis))

;; the first IF subterm, outermost first
(define (mfe-find-if x)
  (cond ((not (pair? x)) #f)
        ((eq? (car x) 'IF) x)
        (#t (let loop ((xs x))
              (cond ((null? xs) #f)
                    ((not (pair? xs)) #f)
                    ((mfe-find-if (car xs)) => (lambda (r) r))
                    (#t (loop (cdr xs))))))))

;; close a condition leaf: assumption, else propositional consequence of the context
(define (mfe-cond!)
  (let ((g (dk-goal)))
    (cond ((dk-ass!) #t)
          ((and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl))
          ((and (pair? g) (eq? (car g) 'OR) (pair? (cadr g)) (eq? (car (cadr g)) '=) (equal? (cadr (cadr g)) (caddr (cadr g))))
           (oi-l) (rfl))
          ((and (pair? g) (eq? (car g) 'OR) (pair? (caddr g)) (eq? (car (caddr g)) '=) (equal? (cadr (caddr g)) (caddr (caddr g))))
           (oi-r) (rfl))
          (#t (prop)))))

;; resolve the IFs of the goal, outermost first, by the list of truth values TRUTHS
(define (mfe-ifs! truths finish)
  (if (null? truths)
      (finish)
      (dk-if-branch! (car truths) (mfe-find-if (dk-goal)) mfe-cond!
        (lambda () (mfe-ifs! (cdr truths) finish)))))

;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (NOT (= x POS-INF))))))
(dk-peel!)
(di)
(fact 'pos-inf-not-in-rr)
(dk-rewrite-h! '(IN x RR) 'x 'POS-INF)
(ai '(NOT (IN POS-INF RR)))
(mfe-qed! 'ext-real-not-pos-inf)

(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (NOT (= x NEG-INF))))))
(dk-peel!)
(di)
(fact 'neg-inf-not-in-rr)
(dk-rewrite-h! '(IN x RR) 'x 'NEG-INF)
(ai '(NOT (IN NEG-INF RR)))
(mfe-qed! 'ext-real-not-neg-inf)

;; x in RR: land NOT(x = +inf), NOT(x = -inf)
(define (mfe-real! x)
  (dk-cite! 'ext-real-not-pos-inf x)
  (dk-cite! 'ext-real-not-neg-inf x))

(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (= (EXT-NEG x) (- x))))))
(dk-peel!)
(mfe-real! 'x)
(dk-cite! 'rr-neg-closed 'x)
(mac 'EXT-NEG)
(mfe-ifs! '(#f #f) (lambda () (rfl)))
(mfe-qed! 'ext-neg-real)

(sp (make-wff '(= (EXT-NEG POS-INF) NEG-INF)))
(mac 'EXT-NEG)
(mfe-ifs! '(#t) (lambda () (rfl)))
(mfe-qed! 'ext-neg-pos-inf)

;;; CUT 2026-10-30 (wave-2 integration): `ext-neg-inf-ne-pos-inf' was an accidental duplicate of `neg-inf-neq-pos-inf' (theorem-library/extinf-points.scm), the same
;;; statement up to binder names (proven-duplicate audit); citations renamed to `neg-inf-neq-pos-inf'.

;; NOT(+inf = -inf) is pos-inf-neq-neg-inf (the band)

(sp (make-wff '(= (EXT-NEG NEG-INF) POS-INF)))
(fact 'neg-inf-neq-pos-inf)
(mac 'EXT-NEG)
(mfe-ifs! '(#f #t) (lambda () (rfl)))
(mfe-qed! 'ext-neg-neg-inf)

;; ---------------------------------------------------------------------------
;; EXT-ADD
(sp (make-wff '(FORALL x (FORALL y (IMPLIES (IN x RR) (IMPLIES (IN y RR) (= (EXT-ADD x y) (+ x y))))))))
(dk-peel!)
(mfe-real! 'x) (mfe-real! 'y)
(dk-have-and! '(IN x RR) '(IN y RR))
(dk-cite! 'rr-add-closed 'x 'y)
(mac 'EXT-ADD)
(mfe-ifs! '(#f #f) (lambda () (rfl)))
(mfe-qed! 'ext-add-real)

(sp (make-wff '(FORALL y (= (EXT-ADD POS-INF y) POS-INF))))
(dk-peel!)
(mac 'EXT-ADD)
(mfe-ifs! '(#t) (lambda () (rfl)))
(mfe-qed! 'ext-add-pos-inf-left)

(sp (make-wff '(FORALL y (= (EXT-ADD y POS-INF) POS-INF))))
(dk-peel!)
(mac 'EXT-ADD)
(mfe-ifs! '(#t) (lambda () (rfl)))
(mfe-qed! 'ext-add-pos-inf-right)

(sp (make-wff '(FORALL y (IMPLIES (NOT (= y POS-INF)) (= (EXT-ADD NEG-INF y) NEG-INF)))))
(dk-peel!)
(fact 'neg-inf-neq-pos-inf)
(mac 'EXT-ADD)
(mfe-ifs! '(#f #t) (lambda () (rfl)))
(mfe-qed! 'ext-add-neg-inf-left)

(sp (make-wff '(FORALL y (IMPLIES (NOT (= y POS-INF)) (= (EXT-ADD y NEG-INF) NEG-INF)))))
(dk-peel!)
(fact 'neg-inf-neq-pos-inf)
(mac 'EXT-ADD)
(mfe-ifs! '(#f #t) (lambda () (rfl)))
(mfe-qed! 'ext-add-neg-inf-right)

;; (IN t RR-STAR) in context: split into the three cases, calling (K 'real), (K 'pos), (K 'neg)
;; on the branch where (IN t RR), (= t POS-INF), (= t NEG-INF) is in context.
(define (mfe-star-cases! t k)
  (let ((iff (dk-cite! 'rr-star-membership t)))
    (dk-have! (caddr iff) (lambda () (mfe-keep-prop! iff (list 'IN t 'RR-STAR))))
    (dk-or-each! (dk-ctx-form (caddr iff))
      (lambda (d)
        (cond ((equal? d (list 'IN t 'RR)) (k 'real))
              ((equal? d (list '= t 'POS-INF)) (k 'pos))
              (#t (k 'neg)))))))

(sp (make-wff '(FORALL y (IMPLIES (IN y RR-STAR) (= (EXT-ADD 0 y) y)))))
(dk-peel!)
(fact 'rr-zero-in)
(mfe-star-cases! 'y
  (lambda (c)
    (case c
      ((real) (dk-cite! 'ext-add-real 0 'y) (subst '(= (EXT-ADD 0 y) (+ 0 y)))
              (dk-have! '(= (+ 0 y) y) (lambda () (dk-ineq! '(IN y RR)))) (ass))
      ((pos) (subst '(= y POS-INF)) (dk-cite! 'ext-add-pos-inf-right 0) (ass))
      (else (subst '(= y NEG-INF)) (mfe-real! 0) (dk-cite! 'ext-add-neg-inf-right 0) (ass)))))
(mfe-qed! 'ext-add-zero-left)

(sp (make-wff '(FORALL y (IMPLIES (IN y RR-STAR) (= (EXT-ADD y 0) y)))))
(dk-peel!)
(fact 'rr-zero-in)
(mfe-star-cases! 'y
  (lambda (c)
    (case c
      ((real) (dk-cite! 'ext-add-real 'y 0) (subst '(= (EXT-ADD y 0) (+ y 0)))
              (dk-have! '(= (+ y 0) y) (lambda () (dk-ineq! '(IN y RR)))) (ass))
      ((pos) (subst '(= y POS-INF)) (dk-cite! 'ext-add-pos-inf-left 0) (ass))
      (else (subst '(= y NEG-INF)) (mfe-real! 0) (dk-cite! 'ext-add-neg-inf-left 0) (ass)))))
(mfe-qed! 'ext-add-zero-right)

  

;;; ==================================================================
;;; MERGED 2026-10-30 (wave-2 integration): mf/mf-psum.scm, appended to this file.
;;; ==================================================================

;;; mf-psum.scm -- partial sums of extended series (EXT-PARTIAL-SUM): the recursion and its typing.
;;; Agent M-F, 2026-10-29.  DESTINATION: theorem-library/signed-measure-ext.scm (after mf-ext).  Library: measure.
;;; Helper prefix: mfs-.  Load window: after mf-ext.scm, power-series laws (series-partial-sum-*).

   ; KIT-9 link skipping, opt-in per file (integrator, 2026-10-29)

;; keep the named formulas and run prop -- only on the leaf the keep was written for (when keep
;; finds that sequent already proven it closes the leaf and the focus moves; prop must not follow it)
(define (mfs-keep-prop! . fs)
  (let ((leaf (proof-state-focus *ps*)))
    (apply keep fs)
    (if (not (sequent-node-grounded? leaf)) (prop))))

(define (mfs-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l) (display ";; MFS OPEN ") (display (expression->string (dk-goal-of l))) (newline))
                (dk-open-leaves)))
  (qed name) (topic! name 'analysis))

(define (mfs-find-if x)
  (cond ((not (pair? x)) #f)
        ((eq? (car x) 'IF) x)
        (#t (let loop ((xs x))
              (cond ((null? xs) #f)
                    ((not (pair? xs)) #f)
                    ((mfs-find-if (car xs)) => (lambda (r) r))
                    (#t (loop (cdr xs))))))))
(define (mfs-cond!)
  (let ((g (dk-goal)))
    (cond ((dk-ass!) #t)
          ((and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl))
          (#t (prop)))))
(define (mfs-ifs! truths finish)
  (if (null? truths)
      (finish)
      (dk-if-branch! (car truths) (mfs-find-if (dk-goal)) mfs-cond!
        (lambda () (mfs-ifs! (cdr truths) finish)))))

;; the condition "some term below n equals c"
(define (mfs-some x n c)
  (list 'FORSOME 'k_ (list 'AND '(IN k_ NN) (list 'AND (list '< 'k_ n) (list '= (list x 'k_) c)))))

(sp (make-wff (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES (mfs-some 'x 'n 'POS-INF)
                                                  '(= (EXT-PARTIAL-SUM x n) POS-INF))))))
(dk-peel!)
(mac 'EXT-PARTIAL-SUM)
(mfs-ifs! '(#t) (lambda () (rfl)))
(mfs-qed! 'ext-psum-pos)

(sp (make-wff (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES (list 'NOT (mfs-some 'x 'n 'POS-INF))
                                                  (list 'IMPLIES (mfs-some 'x 'n 'NEG-INF)
                                                    '(= (EXT-PARTIAL-SUM x n) NEG-INF)))))))
(dk-peel!)
(mac 'EXT-PARTIAL-SUM)
(mfs-ifs! '(#f #t) (lambda () (rfl)))
(mfs-qed! 'ext-psum-neg)

(sp (make-wff (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES (list 'NOT (mfs-some 'x 'n 'POS-INF))
                                                  (list 'IMPLIES (list 'NOT (mfs-some 'x 'n 'NEG-INF))
                                                    '(== (EXT-PARTIAL-SUM x n) (SERIES-PARTIAL-SUM x n))))))))
(dk-peel!)
(mac 'EXT-PARTIAL-SUM)
(mfs-ifs! '(#f #f) (lambda () (qrfl)))
(mfs-qed! 'ext-psum-fin)

;; NOT(some term below 0 equals c)
(define (mfs-none-below-zero! x c)
  (let ((f (list 'NOT (mfs-some x 0 c))))
    (dk-have! f
      (lambda ()
        (di)
        (let ((k (dk-skolem! (dk-ctx-form (mfs-some x 0 c)))))
          (dk-nn-absurd! (list '< k 0)))))
    f))

(sp (make-wff '(FORALL x (= (EXT-PARTIAL-SUM x 0) 0))))
(dk-peel!)
(mfs-none-below-zero! 'x 'POS-INF)
(mfs-none-below-zero! 'x 'NEG-INF)
(dk-cite! 'ext-psum-fin 'x 0)
(dk-cite! 'series-partial-sum-zero 'x)
(subst '(== (EXT-PARTIAL-SUM x 0) (SERIES-PARTIAL-SUM x 0)))
(subst '(== (SERIES-PARTIAL-SUM x 0) 0))
(rfl)
(mfs-qed! 'ext-psum-zero)

;; some term below succ(n) equals c  iff  some term below n does, or x(n) = c
(sp (make-wff (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list 'FORALL 'c_
  (list 'IFF (mfs-some 'x '(succ n) 'c_) (list 'OR (mfs-some 'x 'n 'c_) '(= (x n) c_)))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(define (mfs-lt-of-lt-succ! k)
  (dk-have! (list '< k 'n)
    (lambda ()
      (mac '<)
      (dk-conj-close! (lambda () (if (not (dk-ass!))
                                     (begin (dk-cite! 'nn-lt-succ-le k '(succ n))
                                            (dk-nn! (list '<= (list 'succ k) '(succ n))))))))))
(define (mfs-csucc-fwd!)
  (let ((k (dk-skolem! (dk-ctx-form (mfs-some 'x '(succ n) 'c_)))))
    (use-em (list '= k 'n)
      (lambda ()
        (oi-r)
        (dk-rewrite-h! (list '= (list 'x k) 'c_) k 'n)
        (dk-ass!))
      (lambda ()
        (oi-l)
        (ew k)
        (mfs-lt-of-lt-succ! k)
        (dk-conj-close! dk-ass!)))))
(define (mfs-csucc-bwd!)
  (dk-or-each! (dk-ctx-form (list 'OR (mfs-some 'x 'n 'c_) '(= (x n) c_)))
    (lambda (d)
      (if (equal? d '(= (x n) c_))
          (begin
            (ew 'n)
            (dk-have! '(< n (succ n)) (lambda () (dk-nn!)))
            (dk-conj-close! dk-ass!))
          (let ((k (dk-skolem! (dk-ctx-form d))))
            (ew k)
            (dk-have! (list '< k '(succ n)) (lambda () (dk-nn! (list '< k 'n))))
            (dk-conj-close! dk-ass!))))))
(dk-iff! (lambda (g) (dk-head-is? g 'OR)) mfs-csucc-fwd! mfs-csucc-bwd!)
(mfs-qed! 'ext-psum-cond-succ)

;; (IN t RR-STAR), NOT(t = +inf), NOT(t = -inf) in context: land (IN t RR)
(define (mfs-real-of-star! t)
  (let ((iff (dk-cite! 'rr-star-membership t))
        (goal (list 'IN t 'RR)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda () (mfs-keep-prop! iff (list 'IN t 'RR-STAR) (list 'NOT (list '= t 'POS-INF)) (list 'NOT (list '= t 'NEG-INF))))))
    goal))

(define mfs-ptw '(FORALL k_ (IMPLIES (IN k_ NN) (IN (x k_) RR-STAR))))

(sp (make-wff (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list 'IMPLIES mfs-ptw
  (list 'IMPLIES (list 'NOT (mfs-some 'x 'n 'POS-INF)) (list 'IMPLIES (list 'NOT (mfs-some 'x 'n 'NEG-INF))
    '(FORALL j_ (IMPLIES (IN j_ NN) (IMPLIES (< j_ n) (IN (x j_) RR))))))))))))
(dk-peel!)
(dk-apply! mfs-ptw 'j_)
(use-em '(= (x j_) POS-INF)
  (lambda ()
    (dk-have! (mfs-some 'x 'n 'POS-INF) (lambda () (ew 'j_) (dk-conj-close! dk-ass!)))
    (ai (list 'NOT (mfs-some 'x 'n 'POS-INF))))
  (lambda ()
    (use-em '(= (x j_) NEG-INF)
      (lambda ()
        (dk-have! (mfs-some 'x 'n 'NEG-INF) (lambda () (ew 'j_) (dk-conj-close! dk-ass!)))
        (ai (list 'NOT (mfs-some 'x 'n 'NEG-INF))))
      (lambda () (mfs-real-of-star! '(x j_)) (dk-ass!)))))
(mfs-qed! 'ext-psum-real-terms)

;; with NOT A(n), NOT B(n), the pointwise typing and n in NN in context: land psum == SPS and SPS in RR
(define (mfs-fin-real! x n)
  (dk-cite! 'ext-psum-fin x n)
  (let ((rt (dk-cite! 'ext-psum-real-terms x n)))
    (dk-cite! 'series-partial-sum-in-rr-below n x)
    (list 'IN (list 'SERIES-PARTIAL-SUM x n) 'RR)))

(sp (make-wff (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list 'IMPLIES mfs-ptw
  '(IN (EXT-PARTIAL-SUM x n) RR-STAR)))))))
(dk-peel!)
(use-em (mfs-some 'x 'n 'POS-INF)
  (lambda ()
    (dk-cite! 'ext-psum-pos 'x 'n)
    (subst '(= (EXT-PARTIAL-SUM x n) POS-INF))
    (fact 'pos-inf-in-rr-star) (dk-ass!))
  (lambda ()
    (use-em (mfs-some 'x 'n 'NEG-INF)
      (lambda ()
        (dk-cite! 'ext-psum-neg 'x 'n)
        (subst '(= (EXT-PARTIAL-SUM x n) NEG-INF))
        (fact 'neg-inf-in-rr-star) (dk-ass!))
      (lambda ()
        (mfs-fin-real! 'x 'n)
        (subst '(== (EXT-PARTIAL-SUM x n) (SERIES-PARTIAL-SUM x n)))
        (fact 'rr-subset-rr-star)
        (dk-cite! 'subset-mem-fwd 'RR 'RR-STAR '(SERIES-PARTIAL-SUM x n))
        (dk-ass!)))))
(mfs-qed! 'ext-psum-in)

;; propositional consequence of the named context formulas
(define (mfs-prop! claim . fs)
  (if (not (dk-asm? claim))
      (dk-have! claim (lambda () (apply mfs-keep-prop! fs))))
  claim)

(sp (make-wff (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list 'IMPLIES mfs-ptw
  '(= (EXT-PARTIAL-SUM x (succ n)) (EXT-ADD (EXT-PARTIAL-SUM x n) (x n)))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(dk-apply! mfs-ptw 'n)
(dk-cite! 'ext-psum-in 'x 'n)
(let* ((ap (dk-cite! 'ext-psum-cond-succ 'x 'n 'POS-INF))
       (an (dk-cite! 'ext-psum-cond-succ 'x 'n 'NEG-INF))
       (a0 (mfs-some 'x 'n 'POS-INF)) (a1 (mfs-some 'x '(succ n) 'POS-INF))
       (b0 (mfs-some 'x 'n 'NEG-INF)) (b1 (mfs-some 'x '(succ n) 'NEG-INF))
       (p1 '(EXT-PARTIAL-SUM x (succ n))) (p0 '(EXT-PARTIAL-SUM x n)))
  (use-em a0
    (lambda ()
      (mfs-prop! a1 ap a0)
      (dk-cite! 'ext-psum-pos 'x 'n) (dk-cite! 'ext-psum-pos 'x '(succ n))
      (subst (list '= p1 'POS-INF)) (subst (list '= p0 'POS-INF))
      (subst (dk-cite! 'ext-add-pos-inf-left '(x n))) (rfl))
    (lambda ()
      (use-em '(= (x n) POS-INF)
        (lambda ()
          (mfs-prop! a1 ap '(= (x n) POS-INF))
          (dk-cite! 'ext-psum-pos 'x '(succ n))
          (subst (list '= p1 'POS-INF)) (subst '(= (x n) POS-INF))
          (subst (dk-cite! 'ext-add-pos-inf-right p0)) (rfl))
        (lambda ()
          (mfs-prop! (list 'NOT a1) ap (list 'NOT a0) '(NOT (= (x n) POS-INF)))
          (use-em b0
            (lambda ()
              (mfs-prop! b1 an b0)
              (dk-cite! 'ext-psum-neg 'x 'n) (dk-cite! 'ext-psum-neg 'x '(succ n))
              (subst (list '= p1 'NEG-INF)) (subst (list '= p0 'NEG-INF))
              (subst (dk-cite! 'ext-add-neg-inf-left '(x n))) (rfl))
            (lambda ()
              (mfs-fin-real! 'x 'n)
              (subst (list '== p0 '(SERIES-PARTIAL-SUM x n)))
              (use-em '(= (x n) NEG-INF)
                (lambda ()
                  (mfs-prop! b1 an '(= (x n) NEG-INF))
                  (dk-cite! 'ext-psum-neg 'x '(succ n))
                  (subst (list '= p1 'NEG-INF)) (subst '(= (x n) NEG-INF))
                  (dk-cite! 'ext-real-not-pos-inf '(SERIES-PARTIAL-SUM x n))
                  (subst (dk-cite! 'ext-add-neg-inf-right '(SERIES-PARTIAL-SUM x n))) (rfl))
                (lambda ()
                  (mfs-prop! (list 'NOT b1) an (list 'NOT b0) '(NOT (= (x n) NEG-INF)))
                  (mfs-real-of-star! '(x n))
                  (mfs-fin-real! 'x '(succ n))
                  (subst (list '== p1 '(SERIES-PARTIAL-SUM x (succ n))))
                  (dk-cite! 'series-partial-sum-succ 'x 'n)
                  (subst '(== (SERIES-PARTIAL-SUM x (succ n)) (+ (SERIES-PARTIAL-SUM x n) (x n))))
                  (dk-cite! 'ext-add-real '(SERIES-PARTIAL-SUM x n) '(x n))
                  (subst '(= (EXT-ADD (SERIES-PARTIAL-SUM x n) (x n)) (+ (SERIES-PARTIAL-SUM x n) (x n))))
                  (dk-have-and! '(IN (SERIES-PARTIAL-SUM x n) RR) '(IN (x n) RR))
                  (dk-cite! 'rr-add-closed '(SERIES-PARTIAL-SUM x n) '(x n))
                  (rfl))))))))))
(mfs-qed! 'ext-psum-succ)

  

;;; ==================================================================
;;; MERGED 2026-10-30 (wave-2 integration): mf/mf-conv.scm, appended to this file.
;;; ==================================================================

;;; mf-conv.scm -- limits of extended series (EXT-SERIES-CONVERGES-TO): divergence to +-inf, eventually
;;; constant partial sums, bounds.
;;; Agent M-F, 2026-10-29.  DESTINATION: theorem-library/signed-measure-ext.scm (after mf-psum).  Library: measure.
;;; Helper prefix: mfc-.  Load window: after mf-psum.scm.

   ; KIT-9 link skipping, opt-in per file (integrator, 2026-10-29)

;; keep the named formulas and run prop -- only on the leaf the keep was written for (when keep
;; finds that sequent already proven it closes the leaf and the focus moves; prop must not follow it)
(define (mfc-keep-prop! . fs)
  (let ((leaf (proof-state-focus *ps*)))
    (apply keep fs)
    (if (not (sequent-node-grounded? leaf)) (prop))))

(define (mfc-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l) (display ";; MFC OPEN ") (display (expression->string (dk-goal-of l))) (newline))
                (dk-open-leaves)))
  (qed name) (topic! name 'analysis))

(define (mfc-star-cases! t k)
  (let ((iff (dk-cite! 'rr-star-membership t)))
    (dk-have! (caddr iff) (lambda () (mfc-keep-prop! iff (list 'IN t 'RR-STAR))))
    (dk-or-each! (dk-ctx-form (caddr iff))
      (lambda (d)
        (cond ((equal? d (list 'IN t 'RR)) (k 'real))
              ((equal? d (list '= t 'POS-INF)) (k 'pos))
              (#t (k 'neg)))))))

;; the four conjuncts of EXT-SERIES-CONVERGES-TO(x, l), landed (the hypothesis kept)
(define (mfc-esc! x l)
  (dk-iff-parts! (dk-cite! 'ext-series-converges-to x l)))

;; skolemize an existential "some m in NN from which on ..." in context; return (m . U)
(define (mfc-from! ex)
  (let* ((m (dk-skolem! ex))
         (u (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f m))) "the eventual universal")))
    (cons m u)))

;; n0 = m1 + m2 with n0 in NN, m1 <= n0, m2 <= n0
(define (mfc-common! m1 m2)
  (let ((n0 (list '+ m1 m2)))
    (dk-have-and! (list 'IN m1 'NN) (list 'IN m2 'NN))
    (dk-cite! 'nn-add-closed m1 m2)
    (dk-cite! 'nn-le-add-right m2 m1)
    (dk-cite! 'nn-le-add-left m1 m2)
    n0))

;; (< a b) and (<= b a) in context: close the focus goal
(define (mfc-lt-le-absurd! a b)
  (let ((iff (dk-cite! '< a b)))
    (dk-iff-fwd! iff)
    (dk-split-all! (list (dk-cite! 'rr-star-leq-domain a b)))
    (dk-have-and! (list 'IN a 'RR-STAR) (list 'IN b 'RR-STAR))
    (dk-have-and! (list '<= a b) (list '<= b a))
    (dk-cite! 'rr-star-leq-antisymmetric a b)
    (ai (list 'NOT (list '= a b)))))

(define mfc-up '(FORALL cb_ (IMPLIES (IN cb_ RR) (FORSOME m_ (AND (IN m_ NN)
                  (FORALL n_ (IMPLIES (IN n_ NN) (IMPLIES (<= m_ n_) (<= cb_ (EXT-PARTIAL-SUM x n_))))))))))
(define mfc-down '(FORALL cb_ (IMPLIES (IN cb_ RR) (FORSOME m_ (AND (IN m_ NN)
                  (FORALL n_ (IMPLIES (IN n_ NN) (IMPLIES (<= m_ n_) (<= (EXT-PARTIAL-SUM x n_) cb_)))))))))

;; ---------------------------------------------------------------------------
;; partial sums eventually above every real: the limit is +inf
(sp (make-wff (list 'FORALL 'x (list 'FORALL 'l (list 'IMPLIES '(EXT-SERIES-CONVERGES-TO x l)
  (list 'IMPLIES mfc-up '(= l POS-INF)))))))
(dk-peel!)
(let* ((parts (mfc-esc! 'x 'l))
       (ireal (cadr parts)) (ineg (cadddr parts)))
  (mfc-star-cases! 'l
    (lambda (c)
      (case c
        ((pos) (dk-ass!))
        ((real)
         (let* ((ue (dk-apply! ireal)))
           (fact 'rr-one-in) (fact 'rr-zero-lt-one)
           (dk-cite! 'rr-pos-rr-of-lt 1)
           (let* ((p1 (mfc-from! (dk-apply! ue 1)))
                  (l1 '(+ l 1)))
             (dk-have-and! '(IN l RR) '(IN 1 RR))
             (dk-cite! 'rr-add-closed 'l 1)
             (let* ((p2 (mfc-from! (dk-apply! mfc-up l1)))
                    (n0 (mfc-common! (car p1) (car p2)))
                    (ps (list 'EXT-PARTIAL-SUM 'x n0)))
               (dk-split-all! (list (dk-apply! (cdr p1) n0)))
               (dk-apply! (cdr p2) n0)
               (dk-type! (list '- ps 'l) 'RR)
               (dk-split-all! (list (dk-cite! 'rr-abs-lt-parts (list '- ps 'l) 1)))
               (dk-absurd! (list '< (list '- ps 'l) 1) (list '<= l1 ps) (list 'IN ps 'RR) '(IN l RR))))))
        (else
         (let ((ue (dk-apply! ineg)))
           (fact 'rr-zero-in)
           (let* ((p1 (mfc-from! (dk-apply! ue 0)))
                  (p2 (mfc-from! (dk-apply! mfc-up 0)))
                  (n0 (mfc-common! (car p1) (car p2)))
                  (ps (list 'EXT-PARTIAL-SUM 'x n0)))
             (dk-apply! (cdr p1) n0)
             (dk-apply! (cdr p2) n0)
             (mfc-lt-le-absurd! ps 0))))))))
(mfc-qed! 'ext-series-limit-up)

;; partial sums eventually below every real: the limit is -inf
(sp (make-wff (list 'FORALL 'x (list 'FORALL 'l (list 'IMPLIES '(EXT-SERIES-CONVERGES-TO x l)
  (list 'IMPLIES mfc-down '(= l NEG-INF)))))))
(dk-peel!)
(let* ((parts (mfc-esc! 'x 'l))
       (ireal (cadr parts)) (ipos (caddr parts)))
  (mfc-star-cases! 'l
    (lambda (c)
      (case c
        ((neg) (dk-ass!))
        ((real)
         (let* ((ue (dk-apply! ireal)))
           (fact 'rr-one-in) (fact 'rr-zero-lt-one)
           (dk-cite! 'rr-pos-rr-of-lt 1)
           (let* ((p1 (mfc-from! (dk-apply! ue 1)))
                  (l1 '(- l 1)))
             (dk-type! l1 'RR)
             (let* ((p2 (mfc-from! (dk-apply! mfc-down l1)))
                    (n0 (mfc-common! (car p1) (car p2)))
                    (ps (list 'EXT-PARTIAL-SUM 'x n0)))
               (dk-split-all! (list (dk-apply! (cdr p1) n0)))
               (dk-apply! (cdr p2) n0)
               (dk-type! (list '- ps 'l) 'RR)
               (dk-split-all! (list (dk-cite! 'rr-abs-lt-parts (list '- ps 'l) 1)))
               (dk-absurd! (list '< (list '- 1) (list '- ps 'l)) (list '<= ps l1) (list 'IN ps 'RR) '(IN l RR))))))
        (else
         (let ((ue (dk-apply! ipos)))
           (fact 'rr-zero-in)
           (let* ((p1 (mfc-from! (dk-apply! ue 0)))
                  (p2 (mfc-from! (dk-apply! mfc-down 0)))
                  (n0 (mfc-common! (car p1) (car p2)))
                  (ps (list 'EXT-PARTIAL-SUM 'x n0)))
             (dk-apply! (cdr p1) n0)
             (dk-apply! (cdr p2) n0)
             (mfc-lt-le-absurd! 0 ps))))))))
(mfc-qed! 'ext-series-limit-down)

;; eventually constant partial sums: the limit is the constant
(define mfc-evc '(FORSOME m_ (AND (IN m_ NN) (FORALL n_ (IMPLIES (IN n_ NN) (IMPLIES (<= m_ n_) (= (EXT-PARTIAL-SUM x n_) c)))))))
(sp (make-wff (list 'FORALL 'x (list 'FORALL 'l (list 'FORALL 'c (list 'IMPLIES '(EXT-SERIES-CONVERGES-TO x l)
  (list 'IMPLIES '(IN c RR-STAR) (list 'IMPLIES mfc-evc '(= l c)))))))))
(dk-peel!)
(fact 'rr-subset-rr-star)
(let* ((p0 (mfc-from! (dk-ctx-form mfc-evc)))
       (m0 (car p0)) (u0 (cdr p0))
       (parts (mfc-esc! 'x 'l))
       (ireal (cadr parts)) (ipos (caddr parts)) (ineg (cadddr parts))
       (bound! (lambda (want)        ; prove mfc-up / mfc-down from the constant value
                 (dk-have! want
                   (lambda ()
                     (let ((cb (dk-di-var!)))
                       (ew m0)
                       (dk-conj-close!
                         (lambda ()
                           (if (not (dk-ass!))
                               (let* ((nv (dk-di-var!)))
                                 (di)
                                 (dk-apply! u0 nv)
                                 (subst (list '= (list 'EXT-PARTIAL-SUM 'x nv) 'c))
                                 (subst (dk-ctx-form (if (equal? want mfc-up) '(= c POS-INF) '(= c NEG-INF))))
                                 (dk-cite! 'subset-mem-fwd 'RR 'RR-STAR cb)
                                 (if (equal? want mfc-up) (dk-cite! 'pos-inf-upper-bound cb) (dk-cite! 'neg-inf-lower-bound cb))
                                 (dk-ass!)))))))))))
  (mfc-star-cases! 'c
    (lambda (cc_)
      (case cc_
        ((pos) (bound! mfc-up) (dk-cite! 'ext-series-limit-up 'x 'l) (subst '(= c POS-INF)) (dk-ass!))
        ((neg) (bound! mfc-down) (dk-cite! 'ext-series-limit-down 'x 'l) (subst '(= c NEG-INF)) (dk-ass!))
        (else
         (mfc-star-cases! 'l
           (lambda (cl)
             (case cl
               ((pos)
                (let* ((p1 (mfc-from! (dk-apply! (dk-apply! ipos) 'c)))
                       (n0 (mfc-common! (car p1) m0))
                       (ps (list 'EXT-PARTIAL-SUM 'x n0)))
                  (dk-apply! (cdr p1) n0) (dk-apply! u0 n0)
                  (dk-rewrite-h! (list '< 'c ps) ps 'c)
                  (ai (dk-cite! 'rr-lt-irrefl 'c))))
               ((neg)
                (let* ((p1 (mfc-from! (dk-apply! (dk-apply! ineg) 'c)))
                       (n0 (mfc-common! (car p1) m0))
                       (ps (list 'EXT-PARTIAL-SUM 'x n0)))
                  (dk-apply! (cdr p1) n0) (dk-apply! u0 n0)
                  (dk-rewrite-h! (list '< ps 'c) ps 'c)
                  (ai (dk-cite! 'rr-lt-irrefl 'c))))
               (else
                (let ((ue (dk-apply! ireal))
                      (tri (dk-cite! 'rr-lt-trichotomy 'l 'c)))
                  (dk-or-each! tri
                    (lambda (d)
                      (if (equal? d '(= l c))
                          (dk-ass!)
                          (let* ((eps (if (equal? d '(< l c)) '(- c l) '(- l c))))
                            (dk-type! eps 'RR)
                            (dk-have! (list '< 0 eps) (lambda () (dk-ineq! d '(IN l RR) '(IN c RR))))
                            (dk-cite! 'rr-pos-rr-of-lt eps)
                            (let* ((p1 (mfc-from! (dk-apply! ue eps)))
                                   (n0 (mfc-common! (car p1) m0))
                                   (ps (list 'EXT-PARTIAL-SUM 'x n0)))
                              (dk-split-all! (list (dk-apply! (cdr p1) n0)))
                              (dk-apply! u0 n0)
                              (dk-type! (list '- ps 'l) 'RR)
                              (dk-split-all! (list (dk-cite! 'rr-abs-lt-parts (list '- ps 'l) eps)))
                              (dk-absurd! (list '< (list '- eps) (list '- ps 'l)) (list '< (list '- ps 'l) eps)
                                          (list '= ps 'c) d '(IN l RR) '(IN c RR) (list 'IN ps 'RR)))))))))))))))))
(mfc-qed! 'ext-series-limit-const)

;; partial sums bounded by B in [0, +inf]: the limit is at most B
(sp (make-wff '(FORALL x (FORALL l (FORALL b (IMPLIES (EXT-SERIES-CONVERGES-TO x l) (IMPLIES (IN b RR-POS-STAR)
  (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN) (<= (EXT-PARTIAL-SUM x n_) b))) (<= l b)))))))))
(dk-peel!)
(fact 'rr-subset-rr-star)
(let* ((parts (mfc-esc! 'x 'l))
       (ireal (cadr parts)) (ipos (caddr parts))
       (bnd (dk-ctx-form '(FORALL n_ (IMPLIES (IN n_ NN) (<= (EXT-PARTIAL-SUM x n_) b)))))
       (iff (dk-cite! 'rr-pos-star-membership 'b)))
  (dk-iff-fwd! iff)
  (dk-or-each! (dk-ctx-form (caddr iff))
    (lambda (d)
      (if (equal? d '(= b POS-INF))
          (begin (subst '(= b POS-INF)) (dk-cite! 'pos-inf-upper-bound 'l) (dk-ass!))
          (begin
            (dk-split-all! (list d))
            (mfc-star-cases! 'l
              (lambda (cl)
                (case cl
                  ((neg) (subst '(= l NEG-INF)) (dk-cite! 'subset-mem-fwd 'RR 'RR-STAR 'b)
                         (dk-cite! 'neg-inf-lower-bound 'b) (dk-ass!))
                  ((pos)
                   (let* ((p1 (mfc-from! (dk-apply! (dk-apply! ipos) 'b)))
                          (m1 (car p1))
                          (ps (list 'EXT-PARTIAL-SUM 'x m1)))
                     (dk-cite! 'nn-le-refl m1)
                     (dk-apply! (cdr p1) m1) (dk-apply! bnd m1)
                     (mfc-lt-le-absurd! 'b ps)))
                  (else
                   (use-em '(<= l b)
                     (lambda () (dk-ass!))
                     (lambda ()
                       (dk-cite! 'rr-not-le-lt 'l 'b)
                       (let ((eps '(- l b)) (ue (dk-apply! ireal)))
                         (dk-type! eps 'RR)
                         (dk-have! (list '< 0 eps) (lambda () (dk-ineq! '(< b l) '(IN l RR) '(IN b RR))))
                         (dk-cite! 'rr-pos-rr-of-lt eps)
                         (let* ((p1 (mfc-from! (dk-apply! ue eps)))
                                (m1 (car p1))
                                (ps (list 'EXT-PARTIAL-SUM 'x m1)))
                           (dk-cite! 'nn-le-refl m1)
                           (dk-split-all! (list (dk-apply! (cdr p1) m1)))
                           (dk-apply! bnd m1)
                           (dk-type! (list '- ps 'l) 'RR)
                           (dk-split-all! (list (dk-cite! 'rr-abs-lt-parts (list '- ps 'l) eps)))
                           (dk-absurd! (list '< (list '- eps) (list '- ps 'l)) (list '<= ps 'b)
                                       '(IN l RR) '(IN b RR) (list 'IN ps 'RR)))))))))))))))
(mfc-qed! 'ext-series-limit-le)

  
