;;; ratio-test-proof.scm -- THE RATIO TEST FOR A REAL POWER SERIES
;;; (ratio-test-converges, structure-library/power-series.scm), PROVEN.
;;; Batch 27-A, 2026-09-24.
;;;
;;; THE STATEMENT (the support, literally): if coef in FUN(NN, RR) never
;;; vanishes, |coef(n+1)/coef(n)| -> L (PS-RATIO-LIMIT) with 0 <= L, and
;;; |x| L < 1, then the power series converges at x (PS-CONVERGES-AT).
;;;
;;; THE ROUTE.  From ratio-test-converges-limsup (theorem-library/limsup-tests.scm,
;;; the notes' Lemma 2.15, first half) applied to theta(n) = |coef(n) x^n|, with
;;; two bridges:
;;;   (a) elimsup-eventually-le: a termwise real non-negative sequence bounded by
;;;       r from some index on has ELIMSUP <= r (the converse of Remark 2.6;
;;;       the tail ESUP is <= r by esup-least, and EINF is below it).  For
;;;       x /= 0 the ratio theta(n+1)/theta(n) is |coef(n+1)/coef(n)| |x|, which
;;;       tends to L|x| (rr-limit-scale), so it is eventually <= r = (L|x|+1)/2
;;;       < 1 (rr-limit-tail-le) and its lim sup is < 1.
;;;   (b) sum theta converges => the series converges (series-abs-converges),
;;;       and PS-CONVERGES-AT is series convergence (ps-converges-as-series).
;;; x = 0 is separate (theta(n) = 0 from n = 1 on: series-eventually-geometric-
;;; converges with q = c = 0): the ratio test needs theta(n) > 0.
;;;
;;; NOTHING asserted.  Helper prefix: rtp-.  Theorem binders rtp..._; the lemma
;;; uses the binders of limsup-tests.scm (f, cpsk_) and of rr-limit-tail-le (k_)
;;; so that instances detach literally.
;;; LOAD WINDOW: lo = theorem-library/ps-series-bridges (ps-abs-term,
;;; ps-converges-as-series), after theorem-library/limsup-tests; hi: none (no
;;; file cites ratio-test-converges).

(define (rtp-head g) (and (pair? g) (car g)))

(define (rtp-detach-all! ch)
  (let loop ((c ch))
    (if (eq? (rtp-head c) 'IMPLIES)
        (loop (detach-with! c (lambda () (dk-conj-close! (lambda () (ass))))))
        c)))

;;; t in RR-POS-STAR from (IN t RR) and (<= 0 t) in context
(define (rtp-rps! t)
  (if (not (dk-asm? (list 'IN t 'RR-POS-STAR)))
      (dk-have! (list 'IN t 'RR-POS-STAR)
        (lambda () (mac 'rr-pos-star-membership) (oi-l) (dk-conj-close! (lambda () (ass)))))))

;;; beta-reduce the focus goal; the reduct is a NEW node that becomes the focus
;;; while the worked leaf stays open, unless beta grounded it: run CLOSER then.
(define (rtp-beta! closer)
  (let ((leaf (proof-state-focus *ps*)))
    (dk-lam-b!)
    (if (not (sequent-node-grounded? leaf)) (closer))))

;;; ======================================================================
;;; (a) elimsup-eventually-le
;;; ======================================================================
(define rtp-h1 '(FORALL cpsk_ (IMPLIES (IN cpsk_ NN) (IN (f cpsk_) RR))))
(define rtp-h2 '(FORALL cpsk_ (IMPLIES (IN cpsk_ NN) (<= 0 (f cpsk_)))))
(sp (make-wff
  (list 'FORALL 'f (list 'IMPLIES rtp-h1 (list 'IMPLIES rtp-h2
    '(FORALL rtpr_ (IMPLIES (IN rtpr_ RR)
       (FORALL rtpn_ (IMPLIES (IN rtpn_ NN)
         (IMPLIES (FORALL k_ (IMPLIES (IN k_ NN) (IMPLIES (<= rtpn_ k_) (<= (f k_) rtpr_))))
           (<= (ELIMSUP f) rtpr_)))))))))))
(dk-peel!)
(define rtp-el-f (cadr (cadr (dk-goal))))
(define rtp-el-r (caddr (dk-goal)))
(define rtp-el-ev (dk-pick (lambda (a) (and (eq? (rtp-head a) 'FORALL) (dk-contains? a rtp-el-r))) "eventual bound"))
(define rtp-el-n (cadr (cadr (caddr (caddr rtp-el-ev)))))
(define rtp-el-tl (list 'ETAIL rtp-el-f rtp-el-n))
;; 0 <= r, from f(n) <= r
(fact 'nn-le-refl rtp-el-n)
(inst+ rtp-el-ev rtp-el-n)
(inst+ (dk-ctx-form rtp-h1) rtp-el-n)
(inst+ (dk-ctx-form rtp-h2) rtp-el-n)
(dk-have! (list '<= 0 rtp-el-r)
  (lambda () (dk-ineq! (list '<= 0 (list rtp-el-f rtp-el-n)) (list '<= (list rtp-el-f rtp-el-n) rtp-el-r))))
(rtp-rps! rtp-el-r)
;; ESUP of the n-th tail is <= r
(fact 'etail-subset-rr-pos-star rtp-el-f rtp-el-n)
(fact 'esup-in rtp-el-tl)
(dk-have! (list 'FORALL 'rtpx_ (list 'IMPLIES (list 'IN 'rtpx_ rtp-el-tl) (list '<= 'rtpx_ rtp-el-r)))
  (lambda ()
    (mac 'ETAIL)
    (let* ((w (dk-di-var!))
           (mem (dk-pick (lambda (a) (and (eq? (rtp-head a) 'IN) (eq? (cadr a) w))) "tail membership"))
           (p (dk-skolem! (car (dk-landed (lambda () (mac-h 'image-membership-iff mem)))))))
      (sep-me (dk-pick (lambda (a) (and (eq? (rtp-head a) 'IN) (eq? (cadr a) p))) "sep membership"))
      (dk-apply! rtp-el-ev p)
      (subst (list '= w (list rtp-el-f p)))
      (ass))))
(rtp-detach-all! (dk-fact! 'esup-least rtp-el-tl rtp-el-r))
;; EINF of the image is below the n-th tail's ESUP
(mac 'ELIMSUP)
(define rtp-el-im (cadr (cadr (dk-goal))))
(dk-have! (list 'SUBSET rtp-el-im 'RR-POS-STAR)
  (lambda ()
    (mac 'subset-def)
    (let* ((w (dk-di-var!))
           (mem (dk-pick (lambda (a) (and (eq? (rtp-head a) 'IN) (eq? (cadr a) w))) "image membership"))
           (m (dk-skolem! (car (dk-landed (lambda () (mac-h 'image-membership-iff mem))))))
           (veq (dk-pick (lambda (a) (and (eq? (rtp-head a) '=) (eq? (caddr a) w))) "value equation")))
      (dk-lam-b-h! veq)
      (fact 'etail-subset-rr-pos-star rtp-el-f m)
      (fact 'esup-in (list 'ETAIL rtp-el-f m))
      (subst (list '= w (cadr (dk-pick (lambda (a) (and (eq? (rtp-head a) '=) (eq? (caddr a) w))) "value equation"))))
      (ass))))
(define rtp-el-e (list 'ESUP rtp-el-tl))
(dk-have! (list 'IN rtp-el-e rtp-el-im)
  (lambda ()
    (dk-image-goal!)
    (ew rtp-el-n)
    (dk-conj-close!
      (lambda ()
        (if (dk-head-is? (dk-goal) '=)
            (rtp-beta! (lambda () (rfl)))
            (ass))))))
(dk-apply! (dk-fact! 'einf-lower rtp-el-im) rtp-el-e)
(fact 'einf-in rtp-el-im)
(rtp-detach-all! (dk-fact! 'rr-pos-star-le-trans (list 'EINF rtp-el-im) rtp-el-e rtp-el-r))
(ass)
(qed 'elimsup-eventually-le)

;;; ======================================================================
;;; (b) ratio-test-converges, the support's statement literally
;;; ======================================================================
(sp (make-wff
  '(FORALL coef
     (IMPLIES (IN coef (FUN NN RR))
       (FORALL L
         (IMPLIES (AND (IN L RR) (AND (<= 0 L) (AND (FORALL n
                         (IMPLIES (IN n NN) (NOT (= (coef n) 0)))) (PS-RATIO-LIMIT coef L))))
           (FORALL x
             (IMPLIES (AND (IN x RR) (< (* (abs x) L) 1))
               (PS-CONVERGES-AT coef x)))))))))
(dk-peel!)
(dk-split-all!)
(define rtp-nz (dk-pick (lambda (a) (and (eq? (rtp-head a) 'FORALL) (dk-contains? a '(NOT (= (coef n) 0))))) "coefficients nonzero"))
(define rtp-psiff (dk-fact! 'ps-converges-as-series 'coef 'x))
(define rtp-a (cadr (caddr rtp-psiff)))
(define rtp-th (list 'VNB-LAMBDA 'rtpk_ 'NN (list 'abs (list '* '(coef rtpk_) '(power x rtpk_)))))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'nn-zero-in)
;;; coef(k), x^k, coef(k) x^k typed; k typed in NN
(define (rtp-term-typ! k)
  (fact 'fun-apply-type-c 'coef 'NN 'RR k)
  (fact 'power-real-closed 'x k)
  (fact 'rr-mul-in-rr (list 'coef k) (list 'power 'x k))
  (fact 'rr-abs-closed (list '* (list 'coef k) (list 'power 'x k))))
(dk-have! (list 'IN rtp-a '(FUN NN RR))
  (lambda () (dk-lam-t!) (let ((k (dk-di-var!))) (rtp-term-typ! k) (ass))))
(dk-have! (list 'IN rtp-th '(FUN NN RR))
  (lambda () (dk-lam-t!) (let ((k (dk-di-var!))) (rtp-term-typ! k) (ass))))
(define rtp-th-nn (list 'FORALL 'cpsk_ (list 'IMPLIES '(IN cpsk_ NN) (list '<= 0 (list rtp-th 'cpsk_)))))
(dk-have! rtp-th-nn
  (lambda ()
    (let ((k (dk-di-var!)))
      (rtp-term-typ! k)
      (rtp-beta! (lambda () (fact 'rr-abs-nonneg (list '* (list 'coef k) (list 'power 'x k))) (ass))))))

;;; (< 0 (abs B)) from (IN B RR) and (NOT (= B 0)) in context
(define (rtp-abs-pos! b)
  (let ((ab (list 'abs b)))
    (fact 'rr-abs-closed b)
    (fact 'rr-abs-nonneg b)
    (if (not (dk-asm? (list '< 0 ab)))
        (let ((iff (dk-fact! 'rr-abs-zero b)))
          (dk-have! (list 'NOT (list '= ab 0))
            (lambda () (if (dk-only! iff (list 'NOT (list '= b 0))) (prop))))
          (dk-have! (list 'NOT (list '= 0 ab))
            (lambda ()
              (di)
              (dk-have! (list '= ab 0) (lambda () (subst (list '= ab 0)) (rfl)))
              (ai (list 'NOT (list '= ab 0)))))
          (dk-have! (list '< 0 ab) (lambda () (mac '<) (dk-conj-close! (lambda () (ass)))))))))

;;; POS-RR c from (IN c RR) and (< 0 c) in context
(define (rtp-pos-rr! c)
  (dk-have! (list 'POS-RR c)
    (lambda ()
      (mac-h '< (dk-ctx-form (list '< 0 c)))
      (dk-split-all!)
      (mac 'pos-rr)
      (dk-conj-close! (lambda () (ass))))))

;;; ---- x /= 0: the parts of theta(k) and of the ratio q(k) -------------------
(define rtp-s '(abs x))
(define (rtp-and! a b)
  (let ((f (list 'AND a b)))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! (lambda () (ass))))))
    f))
;;; theta(k) = |coef(k) x^k| = |coef(k)| |x|^k > 0; returns T = |coef(k) x^k|,
;;; landing (< 0 T) and (NOT (= T 0)).  Needs (< 0 (abs x)) in context.
(define (rtp-tparts! k)
  (let ((tk (list 'abs (list '* (list 'coef k) (list 'power 'x k)))))
    (rtp-term-typ! k)
    (dk-apply! rtp-nz k)
    (rtp-abs-pos! (list 'coef k))
    (fact 'rr-power-pos rtp-s k)
    (fact 'power-real-closed rtp-s k)
    (fact 'rr-mul-pos (list 'abs (list 'coef k)) (list 'power rtp-s k))
    (if (not (dk-asm? (list '< 0 tk)))
        (let ((pe (dk-fact! 'ps-abs-term 'coef 'x k)))
          (dk-have! (list '< 0 tk) (lambda () (subst pe) (ass)))))
    (fact 'rr-pos-ne-zero tk)
    tk))
;;; the ratio at k: T1 . recip(T0) typed, positive; returns (T0 T1)
(define (rtp-qparts! k)
  (fact 'nn-succ-closed k)
  (let* ((t0 (rtp-tparts! k)) (t1 (rtp-tparts! (list 'succ k))))
    (rtp-and! (list 'IN t0 'RR) (list 'NOT (list '= t0 0)))
    (fact 'rr-recip-closed t0)
    (fact 'rr-recip-pos t0)
    (fact 'rr-mul-in-rr t1 (list 'recip t0))
    (fact 'rr-mul-pos t1 (list 'recip t0))
    (list t0 t1)))
(define rtp-th-pos (list 'FORALL 'cpsk_ (list 'IMPLIES '(IN cpsk_ NN) (list '< 0 (list rtp-th 'cpsk_)))))

;;; detach an implication chain: an antecedent in context by detach!, one not
;;; in context (a conjunction of context facts) proved conjunct by conjunct by
;;; `ass' -- the kit's `dk-chain!' with that one prover (2026-09-25).
(define (rtp-chain! ch)
  (dk-chain! ch (lambda (ante) (lambda () (dk-conj-close! (lambda () (ass)))))))

;;; q(k) = al(k) |x|, on the lane where the goal is that equation at k
(define (rtp-ratio-eq! k)
  (let* ((sk (list 'succ k)) (c0 (list 'coef k)) (c1 (list 'coef sk)) (pk (list 'power 'x k))
         (tt (rtp-qparts! k)))
    (fact 'fun-apply-type-c 'coef 'NN 'RR sk)
    (rtp-and! (list 'IN c0 'RR) (list 'NOT (list '= c0 0)))
    (fact 'rr-recip-closed c0)
    (fact 'rr-mul-in-rr c1 (list 'recip c0))
    (fact 'rr-recip-cancel-right c1 c0)
    ;; w = c1 / c0, a SYMBOL (crs declines recip), with w c0 = c1
    (dk-have! (list 'FORSOME 'rtpw_ (list 'AND '(IN rtpw_ RR)
                (list 'AND (list '= 'rtpw_ (list '* c1 (list 'recip c0)))
                           (list '= (list '* 'rtpw_ c0) c1))))
      (lambda ()
        (ew (list '* c1 (list 'recip c0)))
        (dk-conj-close!
          (lambda ()
            (cond ((dk-head-is? (dk-goal) 'IN) (ass))
                  ((equal? (caddr (dk-goal)) c1)
                   (subst (list '= (cadr (dk-goal)) c1)) (rfl))
                  (#t (rfl)))))))
    (let* ((w (dk-skolem! (dk-pick (lambda (a) (and (dk-head-is? a 'FORSOME) (dk-contains? a 'rtpw_))) "w")))
           (e1 (list '= (list '* c1 (list 'power 'x sk)) (list '* (list '* w 'x) (list '* c0 pk)))))
      (rtp-beta!
        (lambda ()
          (fact 'rr-subset-cc 'x)
          (rtp-and! '(IN x CC) (list 'IN k 'NN))
          (fact 'rr-mul-in-rr w 'x)
          (fact 'rr-mul-in-rr c0 pk)
          (dk-have! e1
            (lambda ()
              (subst (list '= c1 (list '* w c0)))
              (subst (dk-fact! 'power-succ 'x k))
              (crs)))
          (subst e1)
          (subst (list '= (list '* c1 (list 'recip c0)) w))
          (rtp-and! (list 'IN (list '* w 'x) 'RR) (list 'IN (list '* c0 pk) 'RR))
          (subst (dk-fact! 'rr-abs-mult (list '* w 'x) (list '* c0 pk)))
          (rtp-and! (list 'IN w 'RR) '(IN x RR))
          (subst (dk-fact! 'rr-abs-mult w 'x))
          (fact 'rr-abs-closed w)
          (fact 'rr-mul-in-rr (list 'abs w) rtp-s)
          (let ((cancel (dk-fact! 'rr-mul-recip-cancel (list '* (list 'abs w) rtp-s) (car tt))))
            (subst (list '= (caddr cancel) (cadr cancel)))
            (rfl)))))))

;;; x /= 0: sum theta converges by the ratio test
(define (rtp-case-nonzero!)
  (rtp-abs-pos! 'x)
  (fact 'rr-pos-ne-zero rtp-s)
  (dk-have! rtp-th-pos
    (lambda () (let ((k (dk-di-var!))) (rtp-tparts! k) (rtp-beta! (lambda () (ass))))))
  (let* ((ch (dk-fact! 'ratio-test-converges-limsup rtp-th))
         (q (cadr (cadr (cadr ch))))
         (riff (dk-fact! 'ps-ratio-limit 'coef 'L))
         (al (caddr (caddr riff)))
         (qh1 (subst-free 'f q rtp-h1))
         (qh2 (subst-free 'f q rtp-h2))
         (ls (list '* 'L rtp-s))
         (c (list '* 1/2 (list '- 1 ls)))
         (r (list '+ ls c)))
    (dk-have! (list 'CONVERGES-TO 'RR-MS al 'L)
      (lambda () (if (dk-only! riff '(PS-RATIO-LIMIT coef L)) (prop))))
    (dk-have! (list 'IN al '(FUN NN RR))
      (lambda ()
        (dk-lam-t!)
        (let* ((k (dk-di-var!)) (c0 (list 'coef k)) (c1 (list 'coef (list 'succ k))))
          (rtp-qparts! k)
          (fact 'fun-apply-type-c 'coef 'NN 'RR (list 'succ k))
          (rtp-and! (list 'IN c0 'RR) (list 'NOT (list '= c0 0)))
          (fact 'rr-recip-closed c0)
          (fact 'rr-mul-in-rr c1 (list 'recip c0))
          (fact 'rr-abs-closed (list '* c1 (list 'recip c0)))
          (ass))))
    (dk-have! (list 'IN q '(FUN NN RR))
      (lambda () (dk-lam-t!) (let ((k (dk-di-var!))) (rtp-qparts! k) (rtp-beta! (lambda () (ass))))))
    (dk-have! qh1
      (lambda () (let ((k (dk-di-var!))) (rtp-qparts! k) (rtp-beta! (lambda () (ass))))))
    (dk-have! qh2
      (lambda ()
        (let* ((k (dk-di-var!)) (tt (rtp-qparts! k)))
          (rtp-beta! (lambda () (dk-ineq! (list '< 0 (list '* (cadr tt) (list 'recip (car tt))))))))))
    ;; q -> L |x|
    (fact 'rr-abs-closed 'x)
    (rtp-chain!
      (detach-with! (dk-fact! 'rr-limit-scale rtp-s al q 'L)
        (lambda () (let ((k (dk-di-var!))) (rtp-ratio-eq! k)))))
    ;; eventually q(k) <= r = L|x| + (1 - L|x|)/2 < 1, so ELIMSUP(q) < 1
    (fact 'rr-mul-in-rr 'L rtp-s)
    (fact 'rr-mul-in-rr rtp-s 'L)
    (dk-have! '(IN 1/2 RR) (lambda () (arith)))
    (fact 'rr-sub-in-rr 1 ls)
    (fact 'rr-mul-in-rr 1/2 (list '- 1 ls))
    (fact 'rr-add-in-rr ls c)
    (dk-have! (list '= ls (list '* rtp-s 'L)) (lambda () (crs)))
    (dk-have! (list '< 0 c)
      (lambda () (dk-ineq! (list '= ls (list '* rtp-s 'L)) (list '< (list '* rtp-s 'L) 1))))
    (rtp-pos-rr! c)
    (let ((nt (dk-skolem! (dk-fact! 'rr-limit-tail-le q ls c))))
      (rtp-chain! (dk-fact! 'elimsup-eventually-le q r nt))
      (fact 'elimsup-in-rr-pos-star q)
      (rtp-chain! (dk-fact! 'rr-pos-star-le-real-in-rr (list 'ELIMSUP q) r))
      (dk-have! (list '< (list 'ELIMSUP q) 1)
        (lambda ()
          (dk-ineq! (list '<= (list 'ELIMSUP q) r) (list '= ls (list '* rtp-s 'L)) (list '< (list '* rtp-s 'L) 1))))
      (rtp-chain! ch)
      (ass))))

;;; x = 0: theta(k) = 0 for k >= 1
(define (rtp-case-zero!)
  (dk-have! '(<= 0 0) (lambda () (dk-ineq!)))
  (dk-have! '(< 0 1) (lambda () (dk-ineq!)))
  (fact 'nn-one-in)
  (rtp-chain!
    (detach-with! (dk-fact! 'series-eventually-geometric-converges rtp-th 0 0 1)
      (lambda ()
        (dk-peel!)
        (let* ((k (cadr (cadr (dk-goal))))
               (cases (dk-fact! 'nn-zero-or-succ k)))
          (fact 'nn-in-rr k)
          (use-cases cases
            (lambda ()
              (dk-have! '(< 0 0) (lambda () (dk-ineq! (list '<= 1 k) (list '= k 0))))
              (fact 'rr-lt-irrefl 0)
              (ai '(NOT (< 0 0))))
            (lambda ()
              (let* ((q (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the predecessor")))
                     (sq (list 'succ q)))
                (subst (list '= k sq))
                (fact 'nn-succ-closed q)
                (rtp-term-typ! sq)
                (rtp-beta!
                  (lambda ()
                    (subst '(= x 0))
                    (subst (dk-fact! 'power-zero-base q))
                    (subst (dk-fact! 'rr-mul-zero (list 'coef sq)))
                    (subst (dk-fact! 'rr-abs-zero-value))
                    (dk-ineq!))))))))))
  (ass))

(dk-have! (list 'SERIES-CONVERGES rtp-th)
  (lambda () (use-em '(= x 0) rtp-case-zero! rtp-case-nonzero!)))
;; sum |a_k| converges => sum a_k converges => PS-CONVERGES-AT
(let ((ch (dk-fact! 'series-abs-converges rtp-a rtp-th)))
  (rtp-chain!
    (detach-with! ch
      (lambda ()
        (let ((k (dk-di-var!)))
          (rtp-term-typ! k)
          (rtp-beta! (lambda () (rfl))))))))
(if (dk-only! rtp-psiff (list 'SERIES-CONVERGES rtp-a)) (prop))
(qed 'ratio-test-converges)
