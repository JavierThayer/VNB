;;; esum-tail.scm -- wave of 2026-11-09/10 (agent TH3-B2), wired 2026-11-10 from scratchpad/th3-1109/b2/tb2-tail.scm.
;;; Library: measure.

;;; ====================================================================
;;; tb2-tail.scm -- TH3-B2, 2026-11-09.  The tails of a finite unordered sum are small
;;; (th-main, proof of Cor. 3.39, first step), for an ARBITRARY index set.
;;;
;;;   esum-tail-small   f : D -> [0, +inf], ESUM f finite, dl > 0: there is a finite t subset of D
;;;                     with  ESUM_{z in D} (IF z in t THEN 0 ELSE f z) < dl.
;;;
;;; The tail is written as a family over D (zero on t), which is the shape the Hilbert-Schmidt
;;; sum of T - T P_t takes; no DIFFERENCE domain is needed.  Route: rb2-esum-approx gives t with
;;; ESUM f < FINSUM_t f + dl; the head g = f 1_t and the tail h = f 1_{D - t} satisfy
;;; eplus(g z, h z) <= f z, so eplus(ESUM g, ESUM h) <= ESUM f (esum-superadditive);
;;; FINSUM_t f <= FINSUM_t g <= ESUM g; all are real, and ESUM h < dl follows by ineq.
;;;
;;; LOAD WINDOW: after BA-ONB3's rb2-esum-approx and TH3-B's esum-superadditive (th3b-esum);
;;; cites the RR-POS-STAR order laws (rake-extended-order, rake-esum-defined, integral-laws).
;;; Library: analysis.
;;; ====================================================================

;;; ---- helper defines COPIED 2026-11-10 (integration) from th3-1109/b2/tb2-hip.scm, th3-1109/b2/tb2-sums.scm:
;;; the probe loaded this chain in ONE environment; load.scm gives each file its own.
(define (tb2-open?) (not (sequent-node-grounded? (proof-state-focus *ps*))))
(define (tb2-and! . ps)
  (let ((f (let build ((l ps)) (if (null? (cdr l)) (car l) (list 'AND (car l) (build (cdr l)))))))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! dk-ass!))))
    f))
(define (tb2-cite! thm . args)
  (let loop ((r (apply dk-cite! thm args)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (if (dk-asm? (caddr r))
            (loop (caddr r))
            (loop (dk-landed-1 (lambda () (detach! r)))))
        r)))
(define (tb2-close!)
  (cond ((not (tb2-open?)) #t)
        ((dk-asm? (dk-goal)) (ass))
        ((dk-head-is? (dk-goal) '==) (qrfl))
        (#t (rfl))))
(define (tb2-ap! f a b x) (if (not (dk-asm? (list 'IN (list f x) b))) (fact 'fun-apply-type-c f a b x)))
(define (tb2-dom! f dd cod)
  (if (not (dk-asm? (list 'IN dd 'SET))) (fact 'fun-domain-in-set dd cod f))
  (if (not (dk-asm? (list '= (list 'DOM f) dd)))
      (begin
        (dk-project! (list 'IN f (list 'FUN dd)) 'fun-codomain-iff (list 'IN f (list 'FUN dd cod)))
        (tb2-and! (list 'IN f (list 'FUN dd)) (list 'IN dd 'SET))
        (fact 'dom-of-fun dd f)
        (let ((x (dk-ctx-form (list 'AND (list 'IN (list 'DOM f) 'SET) (list '= (list 'DOM f) dd)))))
          (if x (dk-split-all! (list x))))))
  (if (not (dk-asm? (list 'IN f (list 'FUN (list 'DOM f) cod))))
      (dk-have! (list 'IN f (list 'FUN (list 'DOM f) cod))
        (lambda () (subst (list '= (list 'DOM f) dd)) (ass)))))
(define (tb2-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; tb2: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l) (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name)
  (topic! name 'analysis))
(define (tb2-rps-of-real! x)
  (if (not (dk-asm? (list 'IN x 'RR-POS-STAR)))
      (dk-have! (list 'IN x 'RR-POS-STAR)
        (lambda ()
          (let ((inst (dk-cite! 'rr-pos-star-membership x)))
            (dk-only! inst (list 'IN x 'RR) (list '<= 0 x))
            (prop))))))
;;; ---- end of copied helpers ----

(define (tb2-tl-fam dd f tt head?)
  (list 'VNB-LAMBDA 'tlz_ dd
        (if head? (list 'IF (list 'IN 'tlz_ tt) (list f 'tlz_) 0)
                  (list 'IF (list 'IN 'tlz_ tt) 0 (list f 'tlz_)))))
(define (tb2-tl-redex? g)          ; (IN ((VNB-LAMBDA ..) k) C) or (<= ...) holding a lambda application
  (let walk ((e g))
    (and (pair? e)
         (or (and (pair? (car e)) (eq? (car (car e)) 'VNB-LAMBDA))
             (any (lambda (x) (and (walk x) #t)) e)))))
(define (tb2-tl-zero!)
  (if (not (dk-asm? '(IN 0 RR-POS-STAR)))
      (begin
        (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
        (if (not (dk-asm? '(<= 0 0))) (dk-have! '(<= 0 0) (lambda () (fact 'rr-leq-reflexive 0) (tb2-close!))))
        (tb2-rps-of-real! 0))))
;;; the family typed in FUN(dd, RR-POS-STAR)
(define (tb2-tl-type! dd f fam)
  (if (not (dk-asm? (list 'IN fam (list 'FUN dd 'RR-POS-STAR))))
      (dk-have! (list 'IN fam (list 'FUN dd 'RR-POS-STAR))
        (lambda ()
          (dk-lam-type!
            (lambda ()
              (let ((k (dk-di-var!)))
                (tb2-ap! f dd 'RR-POS-STAR k)
                (tb2-tl-zero!)
                (if (tb2-tl-redex? (dk-goal)) (dk-lam-b!))
                (let ((ift (cadr (dk-goal))))
                  (dk-case-if! ift (lambda (true? val) (tb2-close!))))))
            (lambda () (ass))))))
  (tb2-dom! fam dd 'RR-POS-STAR))

(sp (make-wff
  '(FORALL dd (FORALL f (IMPLIES (IN f (FUN dd RR-POS-STAR)) (IMPLIES (IN (ESUM f) RR)
     (FORALL dl (IMPLIES (POS-RR dl)
       (FORSOME tq_ (AND (IN tq_ SET) (AND (IN (CARD tq_) NN) (AND (SUBSET tq_ dd)
         (< (ESUM (VNB-LAMBDA tlz_ dd (IF (IN tlz_ tq_) 0 (f tlz_)))) dl)))))))))))))
(dk-peel!)
(tb2-dom! 'f 'dd 'RR-POS-STAR)
(fact 'rr-pos-rr-in-rr 'dl)
(fact 'rr-lt-of-pos-rr 'dl)
(let* ((ap (tb2-cite! 'rb2-esum-approx 'f 'dl))
       (tt (dk-skolem! ap #t))
       (sub (dk-rewrite-h! (list 'SUBSET tt '(DOM f)) '(DOM f) 'dd))
       (gg (tb2-tl-fam 'dd 'f tt #t))
       (hh (tb2-tl-fam 'dd 'f tt #f))
       (ef '(ESUM f)) (eg (list 'ESUM gg)) (eh (list 'ESUM hh))
       (fs (list 'FINSUM 'RR-POS-STAR-ADD-MONOID 'f tt))
       (fg (list 'FINSUM 'RR-POS-STAR-ADD-MONOID gg tt))
       (lt (dk-pick (lambda (q) (and (dk-head-is? q '<) (equal? (cadr q) ef))) "ESUM f < FINSUM + dl")))
  (ew tt)
  (dk-have! (list '< eh 'dl)
    (lambda ()
      (tb2-tl-type! 'dd 'f gg)
      (tb2-tl-type! 'dd 'f hh)
      ;; eplus(g z, h z) <= f z
      (dk-have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ dd)
                  (list '<= (list 'eplus (list gg 'z_) (list hh 'z_)) '(f z_))))
        (lambda ()
          (let* ((z (dk-di-var!)) (fz (list 'f z)))
            (tb2-ap! 'f 'dd 'RR-POS-STAR z)
            (tb2-tl-zero!)
            (dk-lam-b!)
            (let* ((g (dk-goal)) (if1 (cadr (cadr g))) (if2 (caddr (cadr g))))
              (dk-case-if! if1
                (lambda (true? val)
                  (dk-if-branch! true? if2 #f
                    (lambda ()
                      (subst (tb2-cite! (if true? 'eplus-zero-right 'eplus-zero-left) fz))
                      (tb2-cite! 'rr-pos-star-le-refl fz)
                      (tb2-close!)))))))))
      (let ((sup (tb2-cite! 'esum-superadditive 'dd gg hh 'f)))
        (tb2-cite! 'esum-in gg)
        (tb2-cite! 'esum-in hh)
        (tb2-cite! 'esum-in 'f)
        ;; FINSUM_t f <= FINSUM_t g <= ESUM g
        (tb2-and! (list 'IN tt 'SET) (list 'IN (list 'CARD tt) 'NN) (list 'SUBSET tt '(DOM f)))
        (tb2-cite! 'esum-partial-sum-type 'f tt)
        (dk-have! (list 'SUBSET tt (list 'DOM gg)) (lambda () (subst (list '= (list 'DOM gg) 'dd)) (tb2-close!)))
        (tb2-and! (list 'IN tt 'SET) (list 'IN (list 'CARD tt) 'NN) (list 'SUBSET tt (list 'DOM gg)))
        (tb2-cite! 'esum-partial-sum-type gg tt)
        (let ((le-up (tb2-cite! 'esum-upper gg tt)))
          (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ tt) '(IN (f z_) RR-POS-STAR)))
            (lambda () (let ((z (dk-di-var!))) (fact 'subset-mem-fwd tt 'dd z) (tb2-ap! 'f 'dd 'RR-POS-STAR z) (tb2-close!))))
          (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ tt) (list 'IN (list gg 'z_) 'RR-POS-STAR)))
            (lambda () (let ((z (dk-di-var!))) (fact 'subset-mem-fwd tt 'dd z) (tb2-ap! gg 'dd 'RR-POS-STAR z) (tb2-close!))))
          (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ tt) (list '<= '(f z_) (list gg 'z_))))
            (lambda ()
              (let ((z (dk-di-var!)))
                (fact 'subset-mem-fwd tt 'dd z)
                (tb2-ap! 'f 'dd 'RR-POS-STAR z)
                (dk-lam-b!)
                (let ((ift (caddr (dk-goal))))
                  (dk-if-branch! #t ift #f
                    (lambda () (tb2-cite! 'rr-pos-star-le-refl (list 'f z)) (tb2-close!)))))))
          (let* ((le-fs (tb2-cite! 'rps-finsum-le-ptwise tt 'f gg))
                 (ep (list 'eplus eg eh)))
            ;; the four sums are real
            (tb2-and! (list 'IN eg 'RR-POS-STAR) (list 'IN eh 'RR-POS-STAR))
            (tb2-cite! 'eplus-closed eg eh)
            (tb2-cite! 'eplus-le-left eg eh)
            (tb2-and! (list 'IN eg 'RR-POS-STAR) (list 'IN ep 'RR-POS-STAR) (list 'IN ef 'RR-POS-STAR))
            (tb2-and! (list '<= eg ep) (list '<= ep ef))
            (tb2-cite! 'rr-pos-star-le-trans eg ep ef)
            (tb2-and! (list 'IN eg 'RR-POS-STAR) (list 'IN ef 'RR))
            (tb2-cite! 'rr-pos-star-le-real-in-rr eg ef)
            (tb2-and! (list 'IN eg 'RR-POS-STAR) (list 'IN eh 'RR-POS-STAR))
            (tb2-and! (list 'IN eh 'RR-POS-STAR) (list 'IN eg 'RR-POS-STAR))
            (let* ((cm (tb2-cite! 'eplus-comm eh eg))
                   (l1 (tb2-cite! 'eplus-le-left eh eg))
                   (l2 (dk-rewrite-h! l1 (list 'eplus eh eg) ep)))
              (tb2-and! (list 'IN eh 'RR-POS-STAR) (list 'IN ep 'RR-POS-STAR) (list 'IN ef 'RR-POS-STAR))
              (tb2-and! (list '<= eh ep) (list '<= ep ef))
              (tb2-cite! 'rr-pos-star-le-trans eh ep ef))
            (tb2-and! (list 'IN eh 'RR-POS-STAR) (list 'IN ef 'RR))
            (tb2-cite! 'rr-pos-star-le-real-in-rr eh ef)
            (tb2-and! (list 'IN fg 'RR-POS-STAR) (list 'IN eg 'RR))
            (tb2-cite! 'rr-pos-star-le-real-in-rr fg eg)
            (tb2-and! (list 'IN fs 'RR-POS-STAR) (list 'IN fg 'RR))
            (tb2-cite! 'rr-pos-star-le-real-in-rr fs fg)
            (tb2-cite! 'rr-pos-star-nonneg eg)
            (tb2-cite! 'rr-pos-star-nonneg eh)
            (let* ((e (tb2-cite! 'eplus-real-defined eg eh))
                   (sup2 (dk-rewrite-h! sup ep (caddr e))))
              (dk-ineq! sup2 le-up le-fs lt
                        (list 'IN fs 'RR) (list 'IN fg 'RR) (list 'IN eg 'RR) (list 'IN eh 'RR)
                        (list 'IN ef 'RR) '(IN dl RR))))))))
  (dk-have! (list 'SUBSET tt 'dd) (lambda () (tb2-close!)))
  (dk-conj-close! (lambda () (tb2-close!))))
(tb2-done! 'esum-tail-small)
