;;; theorem-library/riesz-markov.scm -- RIESZ-MARKOV, STAGE 3B (RM-3B, 2026-10-10):
;;; the assembly on X, conditional on the positive extension.  Helper prefix: rmk-.
;;; Source: the user's notes-63, form (b).
;;;
;;; THE HEADLINE.
;;;   rmk-riesz-markov-from-k  s (the space X) compact with a dense sequence dseq,
;;;        K = RM-KMS(s, dseq), pi = RM-PI(s, dseq) : K -> s (RM-1); lam a positive
;;;        functional on CONT-FNS(K) and lamx one on CONT-FNS(s) with
;;;        lam(f o pi) = lamx(f) for every f in CONT-FNS(s).  Let MU on SIG be the
;;;        measure RM-2 builds from lam (rmc-k-measure) and NU its push-forward along
;;;        pi to the Borel sets of s.  Then NU is a measure on BOREL-SETS(s), and every
;;;        f in CONT-FNS(s) is NU-integrable with RINTEGRAL(f, NU) = lamx(f).
;;;   ROUTE: pi is continuous (rmm-pi-continuous), hence Borel measurable
;;;   (pfw-continuous-borel-measurable), hence measurable into SIG, which contains the
;;;   Borel sets of K (rmc-k-measure; pfw-measurable-map-enlarge); NU is a measure
;;;   (pfw-push-forward-measure).  For f continuous, f is Borel (its tails are open,
;;;   rmc-gt-set-open, pfw-open-borel), f o pi is continuous (ms-compose-continuous-at),
;;;   so RM-2 (rmc-riesz-markov-k) makes it MU-integrable with integral lam(f o pi);
;;;   the change of variables (pfw-integrable-iff, pfw-change-of-variables-real) carries
;;;   both facts to f and NU.
;;;
;;; The composite f o pi is the lambda (VNB-LAMBDA pwz_ (PTS K) (f (pi pwz_))) of
;;; theorem-library/push-forward.scm.
;;;
;;; LOAD WINDOW: [after theorem-library/push-forward, end); push-forward itself needs
;;; riesz-markov-cantor for nothing, but this file cites rmc- and rmm- theorems.
;;; Library: measure.  No top-level macro: the file may be compiled.

(define rmk-ks '(RM-KMS s dseq))
(define rmk-kp '(PTS (RM-KMS s dseq)))
(define rmk-pi '(RM-PI s dseq))
(define rmk-mu0 (list 'VNB-LAMBDA 'rcu_ (list 'CLOPEN-SETS rmk-ks) (list 'lam (list 'INDICATOR rmk-kp 'rcu_))))
(define rmk-out (list 'METHOD-I-OUTER rmk-kp (list 'CLOPEN-SETS rmk-ks) rmk-mu0))
(define rmk-sig (list 'CARATHEODORY-SETS rmk-kp rmk-out))
(define rmk-mu (list 'RES rmk-out rmk-sig))
(define rmk-nu (list 'PUSH-FORWARD rmk-kp '(BOREL-SETS s) rmk-mu rmk-pi))
(define (rmk-comp f) (list 'VNB-LAMBDA 'pwz_ rmk-kp (list f (list rmk-pi 'pwz_))))

(sp (make-wff (forall-guarded '(s dseq lam lamx)
   (list '(IS-COMPACT s) '(IS-DENSE-SEQ s dseq)
         (list 'IS-POSITIVE-FUNCTIONAL rmk-ks 'lam) '(IS-POSITIVE-FUNCTIONAL s lamx)
         (list 'FORALL 'f (list 'IMPLIES '(IN f (CONT-FNS s)) (list '= (list 'lam (rmk-comp 'f)) '(lamx f)))))
   (list 'AND (list 'IS-MEASURE '(PTS s) '(BOREL-SETS s) rmk-nu)
     (list 'FORALL 'f (list 'IMPLIES '(IN f (CONT-FNS s))
       (list 'AND (list 'IS-INTEGRABLE '(PTS s) '(BOREL-SETS s) rmk-nu 'f)
                  (list '= (list 'RINTEGRAL '(PTS s) '(BOREL-SETS s) rmk-nu 'f) '(lamx f)))))))))
(dk-peel!)
(define rmk-agree
  (dk-pick (lambda (x) (and (dk-head-is? x 'FORALL) (dk-contains? x 'lamx) (dk-contains? x 'CONT-FNS))) "the agreement hypothesis"))
(dk-cite! 'rmm-kms-metric 's 'dseq)
(dk-cite! 'rmm-kms-pts 's 'dseq)
(dk-cite! 'rmm-k-set 's 'dseq)
(dk-have! (list 'IN rmk-kp 'SET) (lambda () (subst (list '== rmk-kp '(RM-K s dseq))) (ass)))
(dk-split-all! (list (dk-cite! 'rmc-k-measure 's 'dseq 'lam)))
(define rmk-kmeas (list 'IS-MEASURE rmk-kp rmk-sig rmk-mu))
(dk-cite! 'rmm-pi-continuous 's 'dseq)
(define rmk-pic (list 'IS-CONTINUOUS rmk-ks 's rmk-pi))
(dk-project! '(IS-METRIC-SPACE s) 'is-continuous rmk-pic)
(dk-project! (list 'IN rmk-pi (list 'FUN rmk-kp '(PTS s))) 'is-continuous rmk-pic)
(define rmk-pi-at
  (dk-project! (list 'FORALL 'a (list 'IMPLIES (list 'IN 'a rmk-kp) (list 'IS-CONTINUOUS-AT rmk-ks 's rmk-pi 'a)))
               'is-continuous rmk-pic))
(dk-cite! 'pfw-continuous-borel-measurable rmk-ks 's rmk-pi)
(dk-project! (list 'IS-SIGMA-ALGEBRA rmk-kp rmk-sig) 'is-measure rmk-kmeas)
(dk-cite! 'pfw-measurable-map-enlarge rmk-kp (list 'BOREL-SETS rmk-ks) '(PTS s) '(BOREL-SETS s) rmk-pi rmk-sig)
(define rmk-map (list 'IS-MEASURABLE-MAP rmk-kp rmk-sig '(PTS s) '(BOREL-SETS s) rmk-pi))
(dk-cite! 'pfw-push-forward-measure rmk-kp rmk-sig rmk-mu '(PTS s) '(BOREL-SETS s) rmk-pi)
(dk-cite! 'pfw-borel-sigma-algebra 's)
(dk-conj-close!
  (lambda ()
    (if (not (dk-ass!))
        (let* ((fv (dk-di-var!))
               (g (rmk-comp fv)))
          (dk-split-all! (list (dk-cite! 'rmc-cont-fns-parts 's fv)))
          (let ((fat (dk-pick (lambda (x) (and (dk-head-is? x 'FORALL) (dk-contains? x 'IS-CONTINUOUS-AT) (dk-contains? x fv)))
                              "the continuity of f")))
            ;; f is real Borel measurable: its tails are open
            (dk-have! (list 'FORALL 'al (list 'IMPLIES '(IN al RR)
                        (list 'IN (list 'SEP 'x_ '(PTS s) (list '< 'al (list fv 'x_))) '(BOREL-SETS s))))
              (lambda ()
                (let ((av (dk-di-var!)))
                  (dk-cite! 'rmc-gt-set-open 's fv av)
                  (dk-cite! 'pfw-open-borel 's (list 'SEP 'x_ '(PTS s) (list '< av (list fv 'x_))))
                  (ass))))
            (dk-cite! 'real-measurable-of-tails '(PTS s) '(BOREL-SETS s) fv)
            ;; f o pi is continuous on K
            (dk-cite! 'pfw-comp-fun rmk-kp '(PTS s) 'RR fv rmk-pi)
            (dk-have! (list 'FORALL 'a (list 'IMPLIES (list 'IN 'a rmk-kp) (list 'IS-CONTINUOUS-AT rmk-ks 'RR-MS g 'a)))
              (lambda ()
                (let ((av (dk-di-var!)))
                  (dk-apply! rmk-pi-at av)
                  (fact 'fun-apply-type-c rmk-pi rmk-kp '(PTS s) av)
                  (dk-apply! fat (list rmk-pi av))
                  (dk-cite! 'ms-compose-continuous-at rmk-ks 's 'RR-MS rmk-pi fv av)
                  (ass))))
            (dk-cite! 'rmc-cont-fns-intro rmk-ks g)
            (dk-split-all! (list (dk-cite! 'rmc-riesz-markov-k 's 'dseq 'lam g)))
            (dk-apply! rmk-agree fv)
            (dk-cite! 'pfw-integrable-iff rmk-kp rmk-sig rmk-mu '(PTS s) '(BOREL-SETS s) rmk-pi fv)
            (dk-have! (list 'IS-INTEGRABLE '(PTS s) '(BOREL-SETS s) rmk-nu fv)
              (lambda ()
                (dk-only! (list 'IFF (list 'IS-INTEGRABLE '(PTS s) '(BOREL-SETS s) rmk-nu fv)
                                     (list 'IS-INTEGRABLE rmk-kp rmk-sig rmk-mu g))
                          (list 'IS-INTEGRABLE rmk-kp rmk-sig rmk-mu g))
                (prop)))
            (dk-split-all! (list (dk-cite! 'pfw-change-of-variables-real rmk-kp rmk-sig rmk-mu '(PTS s) '(BOREL-SETS s) rmk-pi fv)))
            (dk-conj-close!
              (lambda ()
                (if (not (dk-ass!))
                    (begin
                      (subst (list '= (list 'RINTEGRAL '(PTS s) '(BOREL-SETS s) rmk-nu fv) (list 'RINTEGRAL rmk-kp rmk-sig rmk-mu g)))
                      (subst (list '= (list 'RINTEGRAL rmk-kp rmk-sig rmk-mu g) (list 'lam g)))
                      (subst (list '= (list 'lam g) (list 'lamx fv)))
                      (if (not (proof-done? *ps*)) (rfl)))))))))))
(qed 'rmk-riesz-markov-from-k)
