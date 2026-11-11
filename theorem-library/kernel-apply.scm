;;; kernel-apply.scm -- wave of 2026-11-09/10 (agent TH3-L2C), wired 2026-11-10 from scratchpad/th3-1109/l2c/kc-a.scm.
;;; Library: measure.

;;; kc-a.scm -- THE REAL KERNEL OPERATOR AS A NAMED FUNCTION: its spec and its linearity
;;; almost everywhere (TH3-L2C, 2026-11-10).  Helper prefix: kca-.
;;;
;;;   * kernel-apply-unfold, kernel-apply-spec: KERNEL-APPLY is TH3-L2B's G, and
;;;     kernel-operator-l2 restated with it;
;;;   * kernel-apply-linear-ae: if h = a u + b w off a nu-null set, then
;;;     K h = a K u + b K w off a mu-null set.  With a = 1, b = 0 this is "K f depends only on
;;;     the class of f".
;;;
;;; LOAD WINDOW: after kc-vocab and TH3-L2B's l2b-e (kernel-operator-l2).  Library: measure.

(define (kca-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** kc-a: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "kc-a: unfinished" name))))

(define (kca-map f l) (let loop ((l l) (acc '())) (if (null? l) (reverse acc) (loop (cdr l) (cons (f (car l)) acc)))))
(define (kca-open?) (not (proof-done? *ps*)))
(define (kca-then-ass! thunk)
  (let ((leaf (proof-state-focus *ps*)))
    (thunk)
    (if (not (sequent-node-grounded? leaf)) (ass))))
(define (kca-lb!) (let loop () (if (dk--redex? (dk-goal)) (begin (dk-lam-b!) (loop)))))
(define (kca-parts! pred args)
  (let* ((iff (apply dk-cite! (cons pred args)))
         (cs (let loop ((r (caddr iff)) (acc '()))
               (if (and (pair? r) (eq? (car r) 'AND))
                   (loop (caddr r) (cons (cadr r) acc))
                   (reverse (cons r acc))))))
    (kca-map (lambda (c) (if (dk-asm? c) c
                             (dk-project! c (lambda () (ai iff) (detach! (list 'IMPLIES (cadr iff) (caddr iff))) (dk-split-all!)))))
             cs)))
(define (kca-ptwise var dom body) (list 'FORALL var (list 'IMPLIES (list 'IN var dom) body)))
(define (kca-off var dom nset body) (kca-ptwise var dom (list 'IMPLIES (list 'NOT (list 'IN var nset)) body)))
;;; skolemise a landed (FORSOME e (AND null off)) and return (e . the off-clause)
(define (kca-sk-off! fs)
  (let* ((e (dk-skolem! fs))
         (find (lambda () (find-first (lambda (q) (and (dk-head-is? q 'FORALL) (dk-contains? q e))) (dk-asms)))))
    (if (not (find))
        (let ((c (find-first (lambda (q) (and (dk-head-is? q 'AND) (dk-contains? q e))) (dk-asms))))
          (if c (dk-split! c))))
    (if (not (find)) (error "kca-sk-off!: no off-clause for" e))
    (cons e (find))))
;;; x not in (UNION a (UNION b ...)): land x not in each piece
(define (kca-not-in-union! x u)
  (if (and (pair? u) (eq? (car u) 'UNION))
      (let ((um (dk-cite! 'union-membership (cadr u) (caddr u) x)))
        (dk-have! (list 'NOT (list 'IN x (cadr u))) (lambda () (keep um (list 'NOT (list 'IN x u))) (prop)))
        (dk-have! (list 'NOT (list 'IN x (caddr u))) (lambda () (keep um (list 'NOT (list 'IN x u))) (prop)))
        (kca-not-in-union! x (cadr u))
        (kca-not-in-union! x (caddr u)))))
;;; a union of a list of null sets, with its null-set fact
(define (kca-union-null! om ca m es)
  (if (null? (cdr es)) (car es)
      (let ((rest (kca-union-null! om ca m (cdr es))))
        (fact 'ae-null-union om ca m (car es) rest)
        (list 'UNION (car es) rest))))

(define kca-xy '(CARTESIAN xs ys))
(define kca-ps '(PRODUCT-SIGMA xs cA ys cB))
(define kca-rho '(PRODUCT-MEASURE xs cA mu ys cB nu))
(define kca-meas2 '((IS-MEASURE xs cA mu) (IS-MEASURE ys cB nu) (IS-SIGMA-FINITE xs cA mu) (IS-SIGMA-FINITE ys cB nu)))
(define kca-l2k (list 'IN 'k (list 'L2-SET kca-xy kca-ps kca-rho)))
(define (kca-G f) (list 'KERNEL-APPLY 'xs 'ys 'cB 'nu 'k f))
(define (kca-p f x) (list 'VNB-LAMBDA 'lx_ 'ys (list '* (list (list 'FN-X-SECTION 'ys 'k x) 'lx_) (list f 'lx_))))
(define (kca-base!)
  (kca-parts! 'is-measure '(xs cA mu))
  (kca-parts! 'is-measure '(ys cB nu))
  (fact 'sigma-algebra-ambient-set 'xs 'cA)
  (fact 'sigma-algebra-ambient-set 'ys 'cB))

;;; ==========================================================================================
;;; (1) KERNEL-APPLY IS G
;;; ==========================================================================================
(define kca-gbody
  (let* ((ff (list 'VNB-LAMBDA 'kpw_ kca-xy '(* (k kpw_) (xi (NTH 2 kpw_)))))
         (u (list 'X-SECTION-INTEGRAL 'xs 'ys 'cB 'nu (list 'POS-PART kca-xy ff)))
         (v (list 'X-SECTION-INTEGRAL 'xs 'ys 'cB 'nu (list 'NEG-PART kca-xy ff))))
    (list 'VNB-LAMBDA 'sgx_ 'xs
          (list '- (list 'IF (list 'IN (list u 'sgx_) 'RR) (list u 'sgx_) 0)
                   (list 'IF (list 'IN (list v 'sgx_) 'RR) (list v 'sgx_) 0)))))
(sp (make-wff (list 'FORALL 'xs (list 'FORALL 'ys (list 'FORALL 'cB (list 'FORALL 'nu (list 'FORALL 'k (list 'FORALL 'xi
   (list '== (kca-G 'xi) kca-gbody)))))))))
(di)
(mac 'KERNEL-APPLY)
(if (kca-open?) (qrfl))
(kca-qed! 'kernel-apply-unfold)

(define kca-xsq '(VNB-LAMBDA lx_ ys (* (xi lx_) (xi lx_))))
(define (kca-sq f om) (list 'VNB-LAMBDA 'lx_ om (list '* (list f 'lx_) (list f 'lx_))))
(sp (make-wff (forall-guarded '(xs cA mu ys cB nu k xi)
   (append kca-meas2 (list kca-l2k '(IN xi (L2-SET ys cB nu))))
   (list 'AND (list 'IN (kca-G 'xi) '(L2-SET xs cA mu))
     (list 'AND (list '<= (list 'INTEGRAL 'xs 'cA 'mu (kca-sq (kca-G 'xi) 'xs))
                      (list '* (list 'INTEGRAL kca-xy kca-ps kca-rho (kca-sq 'k kca-xy)) (list 'INTEGRAL 'ys 'cB 'nu kca-xsq)))
       (list 'FORSOME 'en_
         (list 'AND '(IS-NULL-SET xs cA mu en_)
           (kca-off 'x 'xs 'en_
             (list 'AND (list 'IS-INTEGRABLE 'ys 'cB 'nu (kca-p 'xi 'x))
                        (list '= (list (kca-G 'xi) 'x) (list 'RINTEGRAL 'ys 'cB 'nu (kca-p 'xi 'x))))))))))))
(dk-peel!)
(subst (dk-cite! 'kernel-apply-unfold 'xs 'ys 'cB 'nu 'k 'xi))
(dk-cite! 'kernel-operator-l2 'xs 'cA 'mu 'ys 'cB 'nu 'k 'xi)
(if (kca-open?) (ass))
(kca-qed! 'kernel-apply-spec)

;;; ==========================================================================================
;;; (2) LINEARITY ALMOST EVERYWHERE
;;; ==========================================================================================
(sp (make-wff (forall-guarded '(xs cA mu ys cB nu k u w h a b nb)
   (append kca-meas2
     (list kca-l2k '(IN u (L2-SET ys cB nu)) '(IN w (L2-SET ys cB nu)) '(IN h (L2-SET ys cB nu))
           '(IN a RR) '(IN b RR) '(IS-NULL-SET ys cB nu nb)
           (kca-off 'y 'ys 'nb '(= (h y) (+ (* a (u y)) (* b (w y)))))))
   (list 'FORSOME 'en_
     (list 'AND '(IS-NULL-SET xs cA mu en_)
       (kca-off 'x 'xs 'en_
         (list '= (list (kca-G 'h) 'x)
                  (list '+ (list '* 'a (list (kca-G 'u) 'x)) (list '* 'b (list (kca-G 'w) 'x))))))))))
(dk-peel!)
(kca-base!)
(dk-split! (dk-cite! 'l2-out kca-xy kca-ps kca-rho 'k))
(for-each (lambda (f) (dk-split! (dk-cite! 'l2-out 'ys 'cB 'nu f))) '(u w h))
(let* ((offs (kca-map (lambda (f)
                        (let ((sp (dk-split! (dk-cite! 'kernel-apply-spec 'xs 'cA 'mu 'ys 'cB 'nu 'k f))))
                          (kca-sk-off! (find-first (lambda (q) (dk-head-is? q 'FORSOME)) sp))))
                      '(u w h)))
       (en (kca-union-null! 'xs 'cA 'mu (kca-map car offs)))
       (hyp (kca-off 'y 'ys 'nb '(= (h y) (+ (* a (u y)) (* b (w y)))))))
  (ew en)
  (dk-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal)) (ass)
          (let ((x (dk-di-var!)))
            (di)
            (kca-not-in-union! x en)
            (for-each (lambda (o) (dk-split! (dk-apply! (cdr o) x))) offs)
            (let* ((pu (kca-p 'u x)) (pw (kca-p 'w x)) (ph (kca-p 'h x))
                   (sc1 (dk-split! (dk-cite! 'rintegral-scale 'ys 'cB 'nu pu 'a)))
                   (q (list-ref (find-first (lambda (z) (dk-head-is? z 'IS-INTEGRABLE)) sc1) 4))
                   (sc2 (dk-split! (dk-cite! 'rintegral-scale 'ys 'cB 'nu pw 'b)))
                   (r (list-ref (find-first (lambda (z) (dk-head-is? z 'IS-INTEGRABLE)) sc2) 4))
                   (ad (dk-split! (dk-cite! 'rintegral-add 'ys 'cB 'nu q r)))
                   (s (list-ref (find-first (lambda (z) (dk-head-is? z 'IS-INTEGRABLE)) ad) 4)))
              (kca-parts! 'is-integrable (list 'ys 'cB 'nu ph))
              (dk-have! (kca-off 'tz_ 'ys 'nb (list '= (list s 'tz_) (list ph 'tz_)))
                (lambda ()
                  (let* ((z (dk-di-var!)) (pr (list 'LIST x z)))
                    (di)
                    (dk-apply! hyp z)
                    (fact 'pair-in-cartesian 'xs 'ys x z)
                    (fact 'fun-apply-type-c 'k kca-xy 'RR pr)
                    (for-each (lambda (f) (fact 'fun-apply-type-c f 'ys 'RR z)) '(u w h))
                    (kca-lb!)
                    (subst (dk-cite! 'fn-x-section-apply 'ys 'k x z))
                    (subst (list '= (list 'h z) (list '+ (list '* 'a (list 'u z)) (list '* 'b (list 'w z)))))
                    (if (kca-open?) (crs)))))
              (dk-split! (dk-cite! 'rintegral-ae-eq 'ys 'cB 'nu s ph 'nb))
              (for-each (lambda (f)
                          (dk-split! (dk-cite! 'l2-out 'xs 'cA 'mu (kca-G f)))
                          (fact 'fun-apply-type-c (kca-G f) 'xs 'RR x))
                        '(u w))
              (subst (list '= (list (kca-G 'h) x) (list 'RINTEGRAL 'ys 'cB 'nu ph)))
              (subst (list '= (list 'RINTEGRAL 'ys 'cB 'nu ph) (list 'RINTEGRAL 'ys 'cB 'nu s)))
              (subst (list '= (list 'RINTEGRAL 'ys 'cB 'nu s)
                              (list '+ (list 'RINTEGRAL 'ys 'cB 'nu q) (list 'RINTEGRAL 'ys 'cB 'nu r))))
              (subst (list '= (list 'RINTEGRAL 'ys 'cB 'nu q) (list '* 'a (list 'RINTEGRAL 'ys 'cB 'nu pu))))
              (subst (list '= (list 'RINTEGRAL 'ys 'cB 'nu r) (list '* 'b (list 'RINTEGRAL 'ys 'cB 'nu pw))))
              (subst (list '= (list 'RINTEGRAL 'ys 'cB 'nu pu) (list (kca-G 'u) x)))
              (subst (list '= (list 'RINTEGRAL 'ys 'cB 'nu pw) (list (kca-G 'w) x)))
              (if (kca-open?) (rfl))))))))
(kca-qed! 'kernel-apply-linear-ae)

;;; the class of K f depends only on the class of f: h = u off a nu-null set gives K h = K u
;;; off a mu-null set
(sp (make-wff (forall-guarded '(xs cA mu ys cB nu k u h nb)
   (append kca-meas2
     (list kca-l2k '(IN u (L2-SET ys cB nu)) '(IN h (L2-SET ys cB nu)) '(IS-NULL-SET ys cB nu nb)
           (kca-off 'y 'ys 'nb '(= (h y) (u y)))))
   (list 'FORSOME 'en_
     (list 'AND '(IS-NULL-SET xs cA mu en_)
       (kca-off 'x 'xs 'en_ (list '= (list (kca-G 'h) 'x) (list (kca-G 'u) 'x))))))))
(dk-peel!)
(kca-base!)
(fact 'rr-zero-in) (fact 'rr-one-in)
(dk-have! (kca-off 'y 'ys 'nb '(= (h y) (+ (* 1 (u y)) (* 0 (u y)))))
  (lambda ()
    (let ((y (dk-di-var!)))
      (di)
      (dk-split! (dk-cite! 'l2-out 'ys 'cB 'nu 'u))
      (fact 'fun-apply-type-c 'u 'ys 'RR y)
      (dk-apply! (kca-off 'y 'ys 'nb '(= (h y) (u y))) y)
      (subst (list '= (list 'h y) (list 'u y)))
      (if (kca-open?) (crs)))))
(let ((o (kca-sk-off! (dk-cite! 'kernel-apply-linear-ae 'xs 'cA 'mu 'ys 'cB 'nu 'k 'u 'u 'h 1 0 'nb))))
  (ew (car o))
  (dk-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal)) (ass)
          (let ((x (dk-di-var!)))
            (di)
            (dk-apply! (cdr o) x)
            (dk-split! (dk-cite! 'kernel-apply-spec 'xs 'cA 'mu 'ys 'cB 'nu 'k 'u))
            (dk-split! (dk-cite! 'l2-out 'xs 'cA 'mu (kca-G 'u)))
            (fact 'fun-apply-type-c (kca-G 'u) 'xs 'RR x)
            (subst (list '= (list (kca-G 'h) x) (list '+ (list '* 1 (list (kca-G 'u) x)) (list '* 0 (list (kca-G 'u) x)))))
            (if (kca-open?) (crs)))))))
(kca-qed! 'kernel-apply-ae-eq)
