;;; l2-bridge.scm -- wave of 2026-11-09/10 (agent TH3-L2B), wired 2026-11-10 from scratchpad/th3-1109/l2b/l2b-a.scm.
;;; Library: measure.

;;; l2b-a.scm -- THE L^2 BRIDGE AND NULL SECTIONS (TH3-L2B, 2026-11-09).  Helper prefix: tla-.
;;;
;;; F2 (TH3-L2 report): the L^2 statements live in L2-SET / RINTEGRAL (real-valued); Tonelli
;;; (tonelli-product, l2c-b) lives in INTEGRAL / IS-MEASURABLE-FN ([0, +inf]-valued).  The
;;; bridge: f in L2-SET iff f is real measurable and INTEGRAL(f^2) is finite, and then f^2 is
;;; a [0, +inf]-measurable function with RINTEGRAL(f^2) = INTEGRAL(f^2).  (For a product f g of
;;; two L^2 functions, RINTEGRAL(f g) = INTEGRAL((f g)+) - INTEGRAL((f g)-) is the definition,
;;; rintegral-unfold.)
;;;
;;; F3: a measurable set of product measure 0 has mu-almost every x-section nu-null; a
;;; product-NULL set (IS-NULL-SET: inside a measurable set of measure 0) has a mu-null set of
;;; exceptional x off which its section is nu-null.
;;;
;;; LOAD WINDOW: after theorem-library/sip-c (l2-out, l2-in), theorem-library/real-integral
;;; and theorem-library/product-measure (fubini-sets, product-measure-apply); the L^2 part
;;; needs nothing else.  Library: measure.  No new vocabulary.

(define (tla-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** l2b-a: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "l2b-a: unfinished" name))))

(define (tla-map f l) (let loop ((l l) (acc '())) (if (null? l) (reverse acc) (loop (cdr l) (cons (f (car l)) acc)))))
(define (tla-open?) (not (proof-done? *ps*)))
(define (tla-then-ass! thunk)
  (let ((leaf (proof-state-focus *ps*)))
    (thunk)
    (if (not (sequent-node-grounded? leaf)) (ass))))
(define (tla-lb!) (let loop () (if (dk--redex? (dk-goal)) (begin (dk-lam-b!) (loop)))))
;;; the conjuncts of a predicate's defining iff, landed (hypothesis kept)
(define (tla-parts! pred args)
  (let* ((iff (apply dk-cite! (cons pred args)))
         (cs (let loop ((r (caddr iff)) (acc '()))
               (if (and (pair? r) (eq? (car r) 'AND))
                   (loop (caddr r) (cons (cadr r) acc))
                   (reverse (cons r acc))))))
    (tla-map (lambda (c) (if (dk-asm? c) c
                             (dk-project! c (lambda () (ai iff) (detach! (list 'IMPLIES (cadr iff) (caddr iff))) (dk-split-all!)))))
             cs)))

(define tla-sq '(VNB-LAMBDA lx_ omega (* (f lx_) (f lx_))))
(define tla-zero '(VNB-LAMBDA cx_ omega 0))

;;; ==========================================================================================
;;; (0) a [0, +inf] value that is not positive is 0
;;; ==========================================================================================
(sp (make-wff '(FORALL y (IMPLIES (IN y RR-POS-STAR) (IMPLIES (NOT (< 0 y)) (= y 0))))))
(dk-peel!)
(let ((iff (dk-cite! 'rr-pos-star-membership 'y)))
  (use-em '(IN y RR)
    (lambda ()
      (fact 'rr-pos-star-nonneg 'y)
      (fact 'rr-zero-in)
      (let ((c (dk-cite! 'rr-le-cases 0 'y)))
        (dk-have! '(= 0 y) (lambda () (keep c '(NOT (< 0 y))) (prop)))
        (subst '(= y 0))
        (if (tla-open?) (rfl))))
    (lambda ()
      (dk-have! '(= y POS-INF) (lambda () (keep iff '(IN y RR-POS-STAR) '(NOT (IN y RR))) (prop)))
      (fact 'rr-zero-in)
      (dk-cite! 'rr-lt-pos-inf 0)
      (let ((h (dk-rewrite-h! '(NOT (< 0 y)) 'y 'POS-INF)))
        (keep h '(< 0 POS-INF))
        (prop)))))
(tla-qed! 'rps-not-pos-zero)

;;; ==========================================================================================
;;; (1) F2: THE L^2 BRIDGE
;;; ==========================================================================================
;;; pointwise: f in FUN(omega, RR) in context, w in omega: SQ(w) reduced and nonneg
(define (tla-sq-nonneg!)
  (dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ omega) (list '<= 0 (list tla-sq 'x_))))
    (lambda ()
      (let ((w (dk-di-var!)))
        (fact 'fun-apply-type-c 'f 'omega 'RR w)
        (tla-lb!)
        (if (tla-open?) (tla-then-ass! (lambda () (fact 'rr-sq-nonneg (list 'f w)))))))))
(define (tla-sq-fun!)
  (dk-have! (list 'IN tla-sq '(FUN omega RR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((w (dk-di-var!)))
            (fact 'fun-apply-type-c 'f 'omega 'RR w)
            (tla-then-ass! (lambda () (fact 'rr-mul-in-rr (list 'f w) (list 'f w))))))
        (lambda () (ass))))))

;;; f in L^2: f^2 is [0, +inf]-measurable, its integral is finite, and RINTEGRAL(f^2) = INTEGRAL(f^2)
(sp (make-wff (forall-guarded '(omega cA mu f) '((IS-MEASURE omega cA mu) (IN f (L2-SET omega cA mu)))
   (list 'AND (list 'IS-MEASURABLE-FN 'omega 'cA tla-sq)
         (list 'AND (list 'IN (list 'INTEGRAL 'omega 'cA 'mu tla-sq) 'RR)
               (list '= (list 'RINTEGRAL 'omega 'cA 'mu tla-sq) (list 'INTEGRAL 'omega 'cA 'mu tla-sq)))))))
(dk-peel!)
(dk-split! (dk-cite! 'l2-out 'omega 'cA 'mu 'f))
(tla-parts! 'is-measure '(omega cA mu))
(fact 'sigma-algebra-ambient-set 'omega 'cA)
(tla-sq-nonneg!)
(tla-sq-fun!)
(let* ((ro (dk-split! (dk-cite! 'rintegral-of-nonneg 'omega 'cA 'mu tla-sq)))
       (eq (list '= (list 'RINTEGRAL 'omega 'cA 'mu tla-sq) (list 'INTEGRAL 'omega 'cA 'mu tla-sq))))
  (fact 'rintegral-in-rr 'omega 'cA 'mu tla-sq)
  (dk-have! (list 'IN (list 'INTEGRAL 'omega 'cA 'mu tla-sq) 'RR)
    (lambda () (subst (list '= (list 'INTEGRAL 'omega 'cA 'mu tla-sq) (list 'RINTEGRAL 'omega 'cA 'mu tla-sq))) (ass)))
  (dk-conj-close! dk-ass!))
(tla-qed! 'l2-square-integral)

;;; the converse: a real measurable f with INTEGRAL(f^2) finite is in L^2
(sp (make-wff (forall-guarded '(omega cA mu f)
   (list '(IS-MEASURE omega cA mu) '(IS-REAL-MEASURABLE-FN omega cA f) (list 'IN (list 'INTEGRAL 'omega 'cA 'mu tla-sq) 'RR))
   '(IN f (L2-SET omega cA mu)))))
(dk-peel!)
(tla-parts! 'is-measure '(omega cA mu))
(tla-parts! 'is-real-measurable-fn '(omega cA f))
(fact 'sigma-algebra-ambient-set 'omega 'cA)
(tla-sq-nonneg!)
(tla-sq-fun!)
(fact 'real-measurable-mul 'omega 'cA 'f 'f)
(fact 'real-nonneg-measurable 'omega 'cA tla-sq)
(fact 'zero-in-rr-pos-star)
(fact 'measurable-fn-const 'omega 'cA 0)
(fact 'integral-zero-fn 'omega 'cA 'mu)
(dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ omega) (list 'IN (list tla-sq 'x_) 'RR)))
  (lambda () (let ((w (dk-di-var!))) (fact 'fun-apply-type-c tla-sq 'omega 'RR w) (ass))))
(dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ omega) (list 'IN (list tla-zero 'x_) 'RR)))
  (lambda () (let ((w (dk-di-var!))) (tla-lb!) (if (tla-open?) (begin (fact 'rr-zero-in) (ass))))))
(dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ omega) (list '= (list tla-sq 'x_) (list '- (list tla-sq 'x_) (list tla-zero 'x_)))))
  (lambda () (let ((w (dk-di-var!)))
               (fact 'fun-apply-type-c 'f 'omega 'RR w)
               (tla-lb!)
               (if (tla-open?) (crs)))))
(dk-have! (list 'IN (list 'INTEGRAL 'omega 'cA 'mu tla-zero) 'RR)
  (lambda () (subst (list '= (list 'INTEGRAL 'omega 'cA 'mu tla-zero) 0)) (fact 'rr-zero-in) (ass)))
(let ((dc (dk-split! (dk-cite! 'rintegral-decomposition 'omega 'cA 'mu tla-sq tla-sq tla-zero))))
  (fact 'l2-in 'omega 'cA 'mu 'f)
  (if (tla-open?) (ass)))
(tla-qed! 'l2-in-of-square-integral)

;;; ==========================================================================================
;;; (2) F3: NULL SETS HAVE NULL SECTIONS ALMOST EVERYWHERE
;;; ==========================================================================================
(define tla-xy '(CARTESIAN xs ys))
(define tla-ps '(PRODUCT-SIGMA xs cA ys cB))
(define tla-rho '(PRODUCT-MEASURE xs cA mu ys cB nu))
(define tla-meas2 '((IS-MEASURE xs cA mu) (IS-MEASURE ys cB nu)))
(define tla-sf2 '((IS-SIGMA-FINITE xs cA mu) (IS-SIGMA-FINITE ys cB nu)))
(define (tla-xsm c) (list 'X-SECTION-MEASURE 'xs 'ys 'nu c))
(define (tla-bad c) (list 'SEP 'x_ 'xs (list '< 0 (list (tla-xsm c) 'x_))))

;;; cs measurable with rho(cs) = 0: the x with nu(cs_x) > 0 form a mu-null measurable set
(sp (make-wff (forall-guarded '(xs cA mu ys cB nu cs)
   (append tla-meas2 tla-sf2 (list (list 'IN 'cs tla-ps) (list '= (list tla-rho 'cs) 0)))
   (list 'AND (list 'IN (tla-bad 'cs) 'cA) (list '= (list 'mu (tla-bad 'cs)) 0)))))
(dk-peel!)
(fact 'fubini-sets 'xs 'cA 'mu 'ys 'cB 'nu 'cs)
(let* ((fs (tla-parts! 'is-fubini-set '(xs cA mu ys cB nu cs)))
       (mp (car fs))
       (ms (tla-parts! 'is-measurable-fn (list 'xs 'cA (tla-xsm 'cs))))
       (tail (caddr ms)))
  (fact 'rr-zero-in)
  (dk-apply! tail 0)
  (dk-cite! 'product-measure-apply 'xs 'cA 'mu 'ys 'cB 'nu 'cs)
  (dk-have! (list '= (list 'INTEGRAL 'xs 'cA 'mu (tla-xsm 'cs)) 0)
    (lambda () (subst (list '= (list 'INTEGRAL 'xs 'cA 'mu (tla-xsm 'cs)) (list tla-rho 'cs))) (ass)))
  (fact 'integral-zero-null 'xs 'cA 'mu (tla-xsm 'cs))
  (dk-conj-close! dk-ass!))
(tla-qed! 'null-set-sections)

;;; a product-null set: off a mu-null set of x, its x-section is nu-null
(sp (make-wff (forall-guarded '(xs cA mu ys cB nu ns)
   (append tla-meas2 tla-sf2 (list (list 'IS-NULL-SET tla-xy tla-ps tla-rho 'ns)))
   (list 'FORSOME 'en_
     (list 'AND '(IS-NULL-SET xs cA mu en_)
       (list 'FORALL 'x (list 'IMPLIES '(IN x xs)
         (list 'IMPLIES '(NOT (IN x en_)) '(IS-NULL-SET ys cB nu (X-SECTION ys ns x))))))))))
(dk-peel!)
(tla-parts! 'is-measure '(xs cA mu))
(tla-parts! 'is-measure '(ys cB nu))
(let* ((n2 (dk-skolem! (dk-landed-1 (lambda () (mac-h 'IS-NULL-SET (list 'IS-NULL-SET tla-xy tla-ps tla-rho 'ns))))))
       (bad (tla-bad n2)))
  (dk-split-all!)
  (dk-split! (dk-cite! 'null-set-sections 'xs 'cA 'mu 'ys 'cB 'nu n2))
  (ew bad)
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond
          ((dk-asm? g) (ass))
          ((dk-head-is? g 'IS-NULL-SET)
           (mac 'IS-NULL-SET)
           (ew bad)
           (fact 'subset-refl bad)
           (dk-conj-close! dk-ass!))
          (#t
           (let ((x (dk-di-var!)))
             (di)
             (let ((sec (list 'X-SECTION 'ys n2 x))
                   (val (list (tla-xsm n2) x)))
               (fact 'x-section-measurable 'xs 'cA 'ys 'cB n2 x)
               (fact 'x-section-mono 'ys 'ns n2 x)
               (fact 'fun-apply-type-c 'nu 'cB 'RR-POS-STAR sec)
               (dk-have! (list 'NOT (list '< 0 val))
                 (lambda ()
                   (di)
                   (dk-have! (list 'IN x bad) (lambda () (in-sep! (lambda () (ass)))))
                   (keep (list 'IN x bad) (list 'NOT (list 'IN x bad)))
                   (prop)))
               (dk-cite! 'x-section-measure-apply 'xs 'ys 'nu n2 x)
               (let ((h (dk-rewrite-h! (list 'NOT (list '< 0 val)) val (list 'nu sec))))
                 (fact 'rps-not-pos-zero (list 'nu sec))
                 (mac 'IS-NULL-SET)
                 (ew sec)
                 (dk-conj-close! dk-ass!)))))))))
  (if (tla-open?) (ass)))
(tla-qed! 'null-set-sections-ae)
