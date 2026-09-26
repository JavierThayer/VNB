;;; regulated-step-approx.scm -- Dieudonne (7.6.1), NECESSITY: a function
;;; regulated on [a, b] is the uniform limit on [a, b] of step functions.
;;; (Batch 22-A, 2026-09-23.)
;;;
;;;   regulated-on-is-step-limit
;;;     forall([a in rr, b in rr, f], is-regulated-on(f, a, b) implies
;;;       forsome([fam in fun(nn, fun(rr, rr))], forall([k in nn], is-step-fn(fam(k), a, b))
;;;         and is-unif-limit-on(fam, extend-const(f, a, b), a, b)))
;;;
;;;   Dieudonne (7.6.1): "In order that a mapping f of I into F be regulated, it
;;;   is necessary and sufficient that f be the limit of a uniformly convergent
;;;   sequence of step-functions."  Sufficiency is `uniform-limit-of-regulated'.
;;;
;;; WHY EXTEND-CONST.  f lives ON [a, b] (IS-REGULATED-ON types it in
;;; FUN(CCINT(a,b), RR)); IS-STEP-FN and IS-UNIF-LIMIT-ON are stated for functions
;;; on the line (structure-library/regulated.scm).  The limit is therefore stated
;;; for EXTEND-CONST(f, a, b), which agrees with f on [a, b] (extend-const-fixes),
;;; and IS-UNIF-LIMIT-ON only reads its limit on [a, b].  No definition changed.
;;; The working lemma `regulated-on-step-approx-creep' is stated for ANY F in
;;; FUN(RR, RR) agreeing with f on [a, b], so a consumer that extends f some other
;;; way (RESTRICT of a total function it already has, say) cites it directly.
;;;
;;; ROUTE (ii) of the brief, the CREEP; no sorting.  For e > 0 let
;;;   Q(x):  some p_0 = a < p_1 < ... < p_n = x (n = 0 allowed) and some h on the
;;;          line, constant on each ]p_i, p_(i+1)[, with |F(z) - h(z)| <= e on [a, x]
;;; (a formula builder, `rsa-qpred', not a definition).  Q(a) holds (n = 0, h = F).
;;; The JUXTAPOSITION (sections 1-4): Q(x), x < y and a constant k within e of F on
;;; ]x, y[ give Q(y) -- append ONE point y at the right end of the sequence
;;; (strict-seq-append-point), change h to k on ]x, y[ and to F(y) at y
;;; (fun-append-constant-piece), and the pieces stay constant (step-pieces-append).
;;; At each t of [a, b] the one-sided limits within [a, b] give windows
;;; ]t - d, t[ and ]t, t + d[ on which F is within e of a constant (section 5);
;;; `ccint-creep' (the tree's least-upper-bound brick, theorem-library/ccint-creep.scm)
;;; applied to G = { x in [a, b] : Q(w) for some w in [x, b] } puts b in G
;;; (section 6).  Q(b) with a < b has n >= 1 and is IS-STEP-FN plus the estimate
;;; (section 7).  The sequence is CHOSEN at e = 1/(k+1) (section 8, the
;;; witness-family-choice.scm pattern).  Dieudonne's cover argument (finitely
;;; many V(x_i), sorted) is replaced by the creep, so no finite set of reals is
;;; ever sorted.
;;;
;;; STATEMENT CHECKS.  Every dimension/index is typed (n in NN, p in FUN(NN,RR));
;;; strict increase is IS-PARTITION's own clause; the approximant family is typed
;;; FUN(NN, FUN(RR,RR)); no CHOICE escapes (the headline concludes with FORSOME).
;;; Binders of driver-built terms are prefixed `rs' and bound nowhere else.
;;;
;;; Theorems (all `modulo 0'): strict-seq-append-point, fun-append-constant-piece,
;;; step-pieces-append, step-approx-start, step-approx-append,
;;; regulated-on-right-window, regulated-on-left-window,
;;; regulated-on-step-approx-creep, step-approx-q-step-fn, regulated-on-step-approx,
;;; regulated-on-is-step-limit.
;;;
;;; Load window: lo = theorem-library/interval-calculus-laws (extend-const-*);
;;; also needs structure-library/regulated, structure-library/regulated-primitive,
;;; ccint-creep, nn-recip-succ-*, rr-min-pos, witness-family-choice's tools
;;; (choose!, in-sep! -- driver-kit).  No top-level macro: compilable.

;;; ---- file-local helpers (prefix rsa-) ---------------------------------

(define (rsa-head f) (if (pair? f) (car f) f))

;;; the strict-increase clause of IS-PARTITION, for family P on 0..N
(define (rsa-strict p n)
  (list 'FORALL 'rsi_
    (list 'FORALL 'rsj_
      (list 'IMPLIES
        (list 'AND (list 'IN 'rsi_ (list 'INTERVAL 0 n))
                   (list 'AND (list 'IN 'rsj_ (list 'INTERVAL 0 n)) '(< rsi_ rsj_)))
        (list '< (list p 'rsi_) (list p 'rsj_))))))

;;; close the focus goal: `rfl' on a reflexive equation, else `ass'
(define (rsa-close!)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))
        (rfl)
        (ass))))

;;; An IF term is resolved by the kit's `dk-if-branch! TRUE? IFT CLOSE-COND K'
;;; (K = rsa-close! where nothing else follows); rsa-if! retired 2026-09-25.

;;; the three parts of I in INTERVAL(0, M), without consuming the membership
(define (rsa-interval-parts! i m)
  (let ((mem (list 'IN i (list 'INTERVAL 0 m))))
    (for-each
     (lambda (c)
       (dk-have! c (lambda ()
                     (dk-split-all! (dk-landed (lambda () (mac-h 'interval-membership mem))))
                     (ass))))
     (list (list 'IN i 'NN) (list '<= 0 i) (list '<= i m)))))

(define (rsa-interval-in! i m)
  (dk-have! (list 'IN i (list 'INTERVAL 0 m))
    (lambda () (mac 'interval-membership)
      (dk-conj-close!
       (lambda ()
         (if (and (equal? (dk-goal) (list '<= 0 i)) (not (dk-asm? (dk-goal))))
             (begin (fact 'nn-zero-le i) (ass))
             (ass)))))))

;;; close the focus goal from contradictory LINEAR premises (named by formula)
(define (rsa-absurd! . prems)
  (fact 'rr-zero-in)
  (dk-have! '(< 0 0) (lambda () (apply dk-ineq! prems)))
  (fact 'rr-lt-irrefl 0)
  (ai '(NOT (< 0 0))))

;;; the piece clause of IS-STEP-FN for H on the partition P with N pieces
(define (rsa-pieces h p n)
  (list 'FORALL 'rspi_
    (list 'IMPLIES (list 'AND (list 'IN 'rspi_ (list 'INTERVAL 0 n)) (list '< 'rspi_ n))
      (list 'FORSOME 'rspc_
        (list 'AND '(IN rspc_ RR)
          (list 'FORALL 'rspt_
            (list 'IMPLIES
              (list 'AND '(IN rspt_ RR)
                (list 'AND (list '< (list p 'rspi_) 'rspt_) (list '< 'rspt_ (list p '(SUCC rspi_)))))
              (list '= (list h 'rspt_) 'rspc_))))))))

(define (rsa-foralls vs body)
  (if (null? vs) body (list 'FORALL (car vs) (rsa-foralls (cdr vs) body))))
(define (rsa-imps hs concl)
  (if (null? hs) concl (list 'IMPLIES (car hs) (rsa-imps (cdr hs) concl))))

(define (rsa-nn-rr! . ks) (for-each (lambda (k) (dk-have! (list 'IN k 'RR) (lambda () (fact 'nn-in-rr k) (ass)))) ks))

;;; =====================================================================
;;; (1) APPENDING ONE POINT TO A STRICTLY INCREASING FINITE SEQUENCE.
;;; =====================================================================

(define rsa1-q '(VNB-LAMBDA rsv_ NN (IF (<= rsv_ rsan_) (rsap_ rsv_) rsad_)))
(define (rsa1-ift k) (list 'IF (list '<= k 'rsan_) (list 'rsap_ k) 'rsad_))

(sp (make-wff
  (list 'FORALL 'rsap_
   (list 'FORALL 'rsan_
    (list 'FORALL 'rsad_
     (list 'IMPLIES '(IN rsap_ (FUN NN RR))
      (list 'IMPLIES '(IN rsan_ NN)
       (list 'IMPLIES '(IN rsad_ RR)
        (list 'IMPLIES (rsa-strict 'rsap_ 'rsan_)
         (list 'IMPLIES '(< (rsap_ rsan_) rsad_)
          (list 'FORSOME 'rsaq_
           (list 'AND '(IN rsaq_ (FUN NN RR))
            (list 'AND '(= (rsaq_ (SUCC rsan_)) rsad_)
             (list 'AND '(FORALL rsak_ (IMPLIES (IN rsak_ NN)
                                        (IMPLIES (<= rsak_ rsan_) (= (rsaq_ rsak_) (rsap_ rsak_)))))
                        (rsa-strict 'rsaq_ '(SUCC rsan_))))))))))))))))
(define rsa1-ls (dk-peel!))
(define rsa1-str (dk-pick (lambda (f) (alpha-equiv? f (rsa-strict 'rsap_ 'rsan_))) "the strict clause"))
(fact 'nn-succ-closed 'rsan_)
(fact 'nn-in-rr 'rsan_)
(fact 'fun-apply-type-c 'rsap_ 'NN 'RR 'rsan_)

;;; q(k) = p(k) for k <= n, and q(succ n) = d, as context equations
(define (rsa1-low! k)
  (dk-have! (list '= (list rsa1-q k) (list 'rsap_ k))
    (lambda () (dk-lam-b!) (dk-if-branch! #t (rsa1-ift k) (lambda () (ass)) rsa-close!))))
(dk-have! (list '= (list rsa1-q '(SUCC rsan_)) 'rsad_)
  (lambda () (dk-lam-b!)
     (dk-if-branch! #f (rsa1-ift '(SUCC rsan_)) (lambda () (fact 'nn-succ-not-le 'rsan_) (ass))
                    rsa-close!)))

(ew rsa1-q)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((eq? (rsa-head g) 'IN)
       (dk-lam-t!)
       (let ((k (dk-di-var!)))
         (fact 'fun-apply-type-c 'rsap_ 'NN 'RR k)
         (use-em (list '<= k 'rsan_)
           (lambda () (dk-if-branch! #t (rsa1-ift k) (lambda () (ass)) rsa-close!))
           (lambda () (dk-if-branch! #f (rsa1-ift k) (lambda () (ass)) rsa-close!)))))
      ((eq? (rsa-head g) '=) (ass))
      ((and (eq? (rsa-head g) 'FORALL) (eq? (rsa-head (caddr g)) 'IMPLIES)
            (eq? (rsa-head (cadr (caddr g))) 'IN))
       ;; forall k in nn. k <= n => q(k) = p(k)
       (let ((k (dk-di-var!)))
         (di)
         (dk-lam-b!)
         (dk-if-branch! #t (rsa1-ift k) (lambda () (ass)) rsa-close!)))
      (#t
       ;; the strict clause for q on 0..succ(n)
       (let* ((ls (dk-peel!))
              (ls (append ls (dk-split-all! ls)))
              (g2 (dk-goal))
              (i (cadr (cadr g2)))
              (j (cadr (caddr g2))))
         (rsa-interval-parts! i '(SUCC rsan_))
         (rsa-interval-parts! j '(SUCC rsan_))
         (rsa-nn-rr! i j)
         (fact 'fun-apply-type-c 'rsap_ 'NN 'RR i)
         (fact 'nn-le-succ-cases 'rsan_ j)
         (use-cases (list (list '<= j 'rsan_) (list '= j '(SUCC rsan_)))
           (lambda ()
             ;; both inside 0..n
             (dk-have! (list '<= i 'rsan_)
               (lambda () (dk-ineq! (list 'IN i 'RR) (list 'IN j 'RR) '(IN rsan_ RR)
                                    (list '< i j) (list '<= j 'rsan_))))
             (rsa1-low! i)
             (rsa1-low! j)
             (subst (list '= (list rsa1-q i) (list 'rsap_ i)))
             (subst (list '= (list rsa1-q j) (list 'rsap_ j)))
             (rsa-interval-in! i 'rsan_)
             (rsa-interval-in! j 'rsan_)
             (have! (list 'AND (list 'IN i '(INTERVAL 0 rsan_))
                               (list 'AND (list 'IN j '(INTERVAL 0 rsan_)) (list '< i j))))
             (dk-apply! rsa1-str i j)
             (ass))
           (lambda ()
             ;; j is the new last index
             (fact 'nn-lt-succ-le i j)
             (dk-have! (list '<= (list 'SUCC i) '(SUCC rsan_))
               (lambda () (subst (list '= '(SUCC rsan_) j)) (ass)))
             (fact 'nn-succ-le-cancel i 'rsan_)
             (rsa1-low! i)
             (subst (list '= (list rsa1-q i) (list 'rsap_ i)))
             (subst (list '= j '(SUCC rsan_)))
             (subst (list '= (list rsa1-q '(SUCC rsan_)) 'rsad_))
             (use-em (list '= i 'rsan_)
               (lambda ()
                 (subst (list '= i 'rsan_))
                 (ass))
               (lambda ()
                 (have! (list 'AND (list '<= i 'rsan_) (list 'NOT (list '= i 'rsan_))))
                 (fact 'rr-le-ne-lt i 'rsan_)
                 (fact 'nn-le-refl 'rsan_)
                 (fact 'nn-zero-in)
                 (fact 'rr-zero-in)
                 (dk-have! '(<= 0 rsan_) (lambda () (dk-ineq! '(IN rsan_ RR) (list '<= 0 i) (list '<= i 'rsan_) (list 'IN i 'RR))))
                 (rsa-interval-in! i 'rsan_)
                 (rsa-interval-in! 'rsan_ 'rsan_)
                 (have! (list 'AND (list 'IN i '(INTERVAL 0 rsan_))
                                   (list 'AND '(IN rsan_ (INTERVAL 0 rsan_)) (list '< i 'rsan_))))
                 (dk-apply! rsa1-str i 'rsan_)
                 (dk-ineq! (list 'IN (list 'rsap_ i) 'RR) '(IN (rsap_ rsan_) RR) '(IN rsad_ RR)
                           (list '< (list 'rsap_ i) '(rsap_ rsan_)) '(< (rsap_ rsan_) rsad_))))))))))))
(qed 'strict-seq-append-point)

;;; =====================================================================
;;; (2) A FUNCTION ON THE LINE, CHANGED TO A CONSTANT ON ]c, d[ AND TO A
;;;     GIVEN VALUE AT d.
;;; =====================================================================

(define rsa2-g '(VNB-LAMBDA rsw_ RR (IF (<= rsw_ rsbc_) (rsbh_ rsw_) (IF (< rsw_ rsbd_) rsbk_ rsbv_))))
(define (rsa2-in t) (list 'IF (list '< t 'rsbd_) 'rsbk_ 'rsbv_))
(define (rsa2-out t) (list 'IF (list '<= t 'rsbc_) (list 'rsbh_ t) (rsa2-in t)))

(sp (make-wff "forall([rsbh_ in fun(rr, rr), rsbc_ in rr, rsbd_ in rr, rsbk_ in rr, rsbv_ in rr],
   rsbc_ < rsbd_ implies
   forsome([rsbg_ in fun(rr, rr)],
     forall([rsbt_ in rr], rsbt_ <= rsbc_ implies rsbg_(rsbt_) = rsbh_(rsbt_)) and
     forall([rsbt_ in rr], rsbc_ < rsbt_ implies rsbt_ < rsbd_ implies rsbg_(rsbt_) = rsbk_) and
     rsbg_(rsbd_) = rsbv_))"))
(dk-peel!)
(ew rsa2-g)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((eq? (rsa-head g) 'IN)
       (dk-lam-t!)
       (let ((w (dk-di-var!)))
         (fact 'fun-apply-type-c 'rsbh_ 'RR 'RR w)
         (use-em (list '<= w 'rsbc_)
           (lambda () (dk-if-branch! #t (rsa2-out w) (lambda () (ass)) rsa-close!))
           (lambda ()
             (dk-if-branch! #f (rsa2-out w) (lambda () (ass))
               (lambda ()
                 (use-em (list '< w 'rsbd_)
                   (lambda () (dk-if-branch! #t (rsa2-in w) (lambda () (ass)) rsa-close!))
                   (lambda () (dk-if-branch! #f (rsa2-in w) (lambda () (ass)) rsa-close!)))))))))
      ((eq? (rsa-head g) '=)
       ;; g(d) = v
       (dk-lam-b!)
       (dk-if-branch! #f (rsa2-out 'rsbd_)
         (lambda () (di) (rsa-absurd! '(IN rsbc_ RR) '(IN rsbd_ RR) '(< rsbc_ rsbd_) '(<= rsbd_ rsbc_)))
         (lambda ()
           (dk-if-branch! #f (rsa2-in 'rsbd_) (lambda () (fact 'rr-lt-irrefl 'rsbd_) (ass))
                          rsa-close!))))
      (#t
       (let* ((ls (dk-peel!))
              (t (cadr (car ls))))
         (if (= (length ls) 2)
             ;; t <= c
             (begin (dk-lam-b!) (dk-if-branch! #t (rsa2-out t) (lambda () (ass)) rsa-close!))
             ;; c < t < d
             (begin
               (dk-lam-b!)
               (dk-if-branch! #f (rsa2-out t)
                 (lambda () (di) (rsa-absurd! '(IN rsbc_ RR) (list 'IN t 'RR)
                                              (list '< 'rsbc_ t) (list '<= t 'rsbc_)))
                 (lambda () (dk-if-branch! #t (rsa2-in t) (lambda () (ass)) rsa-close!)))))))))))
(qed 'fun-append-constant-piece)

;;; =====================================================================
;;; (3) THE PIECES OF THE JUXTAPOSED STEP FUNCTION.
;;; =====================================================================

(sp (make-wff
  (rsa-foralls '(rsp_ rsn_ rsh_ rsq_ rsg_ rsc_ rsd_ rsk_)
    (rsa-imps
      (list '(IN rsp_ (FUN NN RR)) '(IN rsn_ NN) '(IN rsh_ (FUN RR RR)) '(IN rsq_ (FUN NN RR))
            '(IN rsg_ (FUN RR RR)) '(IN rsc_ RR) '(IN rsd_ RR) '(IN rsk_ RR)
            (rsa-strict 'rsp_ 'rsn_)
            (rsa-pieces 'rsh_ 'rsp_ 'rsn_)
            '(= (rsp_ rsn_) rsc_)
            '(FORALL rsj_ (IMPLIES (IN rsj_ NN) (IMPLIES (<= rsj_ rsn_) (= (rsq_ rsj_) (rsp_ rsj_)))))
            '(= (rsq_ (SUCC rsn_)) rsd_)
            '(FORALL rst_ (IMPLIES (IN rst_ RR) (IMPLIES (<= rst_ rsc_) (= (rsg_ rst_) (rsh_ rst_)))))
            '(FORALL rst_ (IMPLIES (IN rst_ RR) (IMPLIES (< rsc_ rst_) (IMPLIES (< rst_ rsd_) (= (rsg_ rst_) rsk_))))))
      (rsa-pieces 'rsg_ 'rsq_ '(SUCC rsn_))))))
(define rsa3-all (dk-peel!))
(define rsa3-str (dk-pick (lambda (f) (alpha-equiv? f (rsa-strict 'rsp_ 'rsn_))) "the strict clause"))
(define rsa3-pcs (dk-pick (lambda (f) (alpha-equiv? f (rsa-pieces 'rsh_ 'rsp_ 'rsn_))) "the pieces of h"))
(define rsa3-qlow (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f '(rsq_ rsj_)))) "q = p below n"))
(define rsa3-glow (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f '(rsh_ rst_)))) "g = h below c"))
(define rsa3-gmid (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f 'rsk_))) "g = k on ]c,d["))
(fact 'nn-in-rr 'rsn_)
(fact 'nn-le-refl 'rsn_)
(fact 'fun-apply-type-c 'rsp_ 'NN 'RR 'rsn_)
(fact 'nn-succ-closed 'rsn_)
(fact 'fun-apply-type-c 'rsq_ 'NN 'RR 'rsn_)
(fact 'fun-apply-type-c 'rsq_ 'NN 'RR '(SUCC rsn_))
(define rsa3-ls (filter (lambda (f) (and (eq? (rsa-head f) 'AND) (dk-contains? f '(INTERVAL 0 (SUCC rsn_))))) rsa3-all))
(define rsa3-i (cadr (cadr (car rsa3-ls))))
(dk-split-all! rsa3-ls)
(rsa-interval-parts! rsa3-i '(SUCC rsn_))
(fact 'nn-lt-succ-le rsa3-i '(SUCC rsn_))
(fact 'nn-succ-le-cancel rsa3-i 'rsn_)
(rsa-nn-rr! rsa3-i)
(let ((i rsa3-i))
  (use-em (list '= i 'rsn_)
    ;; the last piece ]c, d[
    (lambda ()
      (subst (list '= i 'rsn_))
      (ew 'rsk_)
      (dk-conj-close!
       (lambda ()
         (if (eq? (rsa-head (dk-goal)) 'IN)
             (ass)
             (let* ((ls (dk-peel!))
                    (ls (append ls (dk-split-all! ls)))
                    (t (cadr (cadr (dk-goal)))))
               (dk-apply! rsa3-qlow 'rsn_)
               (dk-have! (list '< 'rsc_ t)
                 (lambda () (dk-ineq! (list 'IN t 'RR) '(IN (rsq_ rsn_) RR) '(IN (rsp_ rsn_) RR) '(IN rsc_ RR)
                                      (list '< '(rsq_ rsn_) t) '(= (rsq_ rsn_) (rsp_ rsn_)) '(= (rsp_ rsn_) rsc_))))
               (dk-have! (list '< t 'rsd_)
                 (lambda () (dk-ineq! (list 'IN t 'RR) '(IN (rsq_ (SUCC rsn_)) RR) '(IN rsd_ RR)
                                      (list '< t '(rsq_ (SUCC rsn_))) '(= (rsq_ (SUCC rsn_)) rsd_))))
               (dk-apply! rsa3-gmid t)
               (ass))))))
    ;; an old piece
    (lambda ()
      (have! (list 'AND (list '<= i 'rsn_) (list 'NOT (list '= i 'rsn_))))
      (fact 'rr-le-ne-lt i 'rsn_)
      (rsa-interval-in! i 'rsn_)
      (have! (list 'AND (list 'IN i '(INTERVAL 0 rsn_)) (list '< i 'rsn_)))
      (let* ((c0 (dk-skolem! (dk-apply! rsa3-pcs i)))
             (hc (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f c0))) "h = c0 on the piece"))
             (si (list 'SUCC i)))
        (fact 'nn-succ-closed i)
        (fact 'nn-lt-succ-le i 'rsn_)
        (rsa-nn-rr! si)
        (fact 'fun-apply-type-c 'rsp_ 'NN 'RR i)
        (fact 'fun-apply-type-c 'rsp_ 'NN 'RR si)
        (fact 'fun-apply-type-c 'rsq_ 'NN 'RR i)
        (fact 'fun-apply-type-c 'rsq_ 'NN 'RR si)
        (dk-apply! rsa3-qlow i)
        (dk-apply! rsa3-qlow si)
        ;; p(succ i) <= c
        (dk-have! (list '<= (list 'rsp_ si) 'rsc_)
          (lambda ()
            (use-em (list '= si 'rsn_)
              (lambda ()
                (dk-have! (list '= (list 'rsp_ si) '(rsp_ rsn_)) (lambda () (subst (list '= si 'rsn_)) (rfl)))
                (dk-ineq! (list 'IN (list 'rsp_ si) 'RR) '(IN (rsp_ rsn_) RR) '(IN rsc_ RR)
                          (list '= (list 'rsp_ si) '(rsp_ rsn_)) '(= (rsp_ rsn_) rsc_)))
              (lambda ()
                (have! (list 'AND (list '<= si 'rsn_) (list 'NOT (list '= si 'rsn_))))
                (fact 'rr-le-ne-lt si 'rsn_)
                (rsa-interval-in! si 'rsn_)
                (rsa-interval-in! 'rsn_ 'rsn_)
                (have! (list 'AND (list 'IN si '(INTERVAL 0 rsn_))
                                  (list 'AND '(IN rsn_ (INTERVAL 0 rsn_)) (list '< si 'rsn_))))
                (dk-apply! rsa3-str si 'rsn_)
                (dk-ineq! (list 'IN (list 'rsp_ si) 'RR) '(IN (rsp_ rsn_) RR) '(IN rsc_ RR)
                          (list '< (list 'rsp_ si) '(rsp_ rsn_)) '(= (rsp_ rsn_) rsc_))))))
        (ew c0)
        (dk-conj-close!
         (lambda ()
           (if (eq? (rsa-head (dk-goal)) 'IN)
               (ass)
               (let* ((ls (dk-peel!))
                      (ls (append ls (dk-split-all! ls)))
                      (t (cadr (cadr (dk-goal)))))
                 (dk-have! (list '< (list 'rsp_ i) t)
                   (lambda () (dk-ineq! (list 'IN t 'RR) (list 'IN (list 'rsq_ i) 'RR) (list 'IN (list 'rsp_ i) 'RR)
                                        (list '< (list 'rsq_ i) t) (list '= (list 'rsq_ i) (list 'rsp_ i)))))
                 (dk-have! (list '< t (list 'rsp_ si))
                   (lambda () (dk-ineq! (list 'IN t 'RR) (list 'IN (list 'rsq_ si) 'RR) (list 'IN (list 'rsp_ si) 'RR)
                                        (list '< t (list 'rsq_ si)) (list '= (list 'rsq_ si) (list 'rsp_ si)))))
                 (dk-have! (list '<= t 'rsc_)
                   (lambda () (dk-ineq! (list 'IN t 'RR) (list 'IN (list 'rsp_ si) 'RR) '(IN rsc_ RR)
                                        (list '< t (list 'rsp_ si)) (list '<= (list 'rsp_ si) 'rsc_))))
                 (dk-apply! rsa3-glow t)
                 (have! (list 'AND (list 'IN t 'RR) (list 'AND (list '< (list 'rsp_ i) t) (list '< t (list 'rsp_ si)))))
                 (dk-apply! hc t)
                 (subst (list '= (list 'rsg_ t) (list 'rsh_ t)))
                 (ass)))))))))
(qed 'step-pieces-append)

;;; =====================================================================
;;; (4) THE CREEPING PREDICATE AND ITS TWO STEPS.
;;;
;;; Q(a, F, e, x): some finite strictly increasing sequence p_0 = a < ... <
;;; p_n = x (n = 0 allowed: then x = a) and some h in FUN(RR,RR) constant on
;;; each open piece ]p_i, p_(i+1)[, with |F(z) - h(z)| <= e on [a, x].  A
;;; FORMULA BUILDER, not a definition.  For x > a it is IS-STEP-FN(h, a, x)
;;; plus the estimate, once n >= 1 is read off p_0 = a /= x = p_n (section 6).
;;; =====================================================================

(define (rsa-approx f h e a x)
  (list 'FORALL 'rsqz_
    (list 'IMPLIES (list 'IN 'rsqz_ (list 'CCINT a x))
      (list '<= (list 'ABS (list '- (list f 'rsqz_) (list h 'rsqz_))) e))))

(define (rsa-qpred a f e x)
  (list 'FORSOME 'rsqn_
   (list 'AND '(IN rsqn_ NN)
    (list 'FORSOME 'rsqp_
     (list 'AND '(IN rsqp_ (FUN NN RR))
      (list 'FORSOME 'rsqh_
       (list 'AND '(IN rsqh_ (FUN RR RR))
        (list 'AND (list '= '(rsqp_ 0) a)
         (list 'AND (list '= '(rsqp_ rsqn_) x)
          (list 'AND (rsa-strict 'rsqp_ 'rsqn_)
           (list 'AND (rsa-pieces 'rsqh_ 'rsqp_ 'rsqn_)
                      (rsa-approx f 'rsqh_ e a x))))))))))))

;;; close |U - U| <= E  (U, E typed, 0 <= E in context)
(define (rsa-ew! w in-closer)
  (ew w)
  (let* ((ls (dk-opened (lambda () (di))))
         (in-leaf (find-first (lambda (l) (let ((g (dk-goal-of l)))
                                            (and (eq? (rsa-head g) 'IN) (equal? (cadr g) w))))
                              ls))
         (rest (find-first (lambda (l) (not (eq? l in-leaf))) ls)))
    (if (not rest) (error "rsa-ew!: no body leaf for" w))
    (if in-leaf (begin (dk-focus! in-leaf) (in-closer)))
    (dk-focus! rest)))

(define (rsa-abs-self! u e)
  (fact 'rr-sub-in-rr u u)
  (mac 'rr-abs-bound)
  (dk-conj-close!
   (lambda () (dk-ineq! (list 'IN u 'RR) (list 'IN e 'RR) (list '<= 0 e)))))

;;; the three parts of Z in CCINT(LO, HI), without consuming the membership
(define (rsa-ccint-parts! z lo hi)
  (let ((mem (list 'IN z (list 'CCINT lo hi))))
    (fact 'ccint-elt-in-rr lo hi z)
    (dk-have! (list '<= lo z)
      (lambda () (dk-split-all! (dk-landed (lambda () (mac-h 'ccint-membership mem)))) (ass)))
    (dk-have! (list '<= z hi)
      (lambda () (dk-split-all! (dk-landed (lambda () (mac-h 'ccint-membership mem)))) (ass)))))

(define (rsa-ccint-in! z lo hi)
  (dk-have! (list 'IN z (list 'CCINT lo hi))
    (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass))))))

;;; skolemize the three witnesses of a Q in context; returns (n p h)
(define (rsa-qpred-open! qf)
  (let* ((n (dk-skolem! qf))
         (p (dk-skolem! (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORSOME) (eq? (cadr f) 'rsqp_)))
                                 "the sequence")))
         (h (dk-skolem! (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORSOME) (eq? (cadr f) 'rsqh_)))
                                 "the step function"))))
    (list n p h)))

;;; ---- (4a) the start: Q(a, F, e, a) --------------------------------------

(define rsa4s-p '(VNB-LAMBDA rs4v_ NN rsca_))
(sp (make-wff
  (rsa-foralls '(rsca_ rscf_ rsce_)
    (rsa-imps (list '(IN rsca_ RR) '(IN rscf_ (FUN RR RR)) '(IN rsce_ RR) '(<= 0 rsce_))
      (rsa-qpred 'rsca_ 'rscf_ 'rsce_ 'rsca_)))))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'rr-zero-in)
(rsa-ew! 0 ass)
(rsa-ew! rsa4s-p (lambda () (dk-lam-t!) (dk-di-var!) (ass)))
(rsa-ew! 'rscf_ ass)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((and (eq? (rsa-head g) 'IN) (dk-contains? g 'VNB-LAMBDA))
       (dk-lam-t!) (dk-di-var!) (ass))
      ((eq? (rsa-head g) 'IN) (ass))
      ((eq? (rsa-head g) '=) (dk-lam-b!) (rsa-close!))
      ((dk-contains? g 'CCINT)
       (let ((z (dk-di-var!)))
         (fact 'ccint-elt-in-rr 'rsca_ 'rsca_ z)
         (fact 'fun-apply-type-c 'rscf_ 'RR 'RR z)
         (rsa-abs-self! (list 'rscf_ z) 'rsce_)))
      ((dk-contains? g 'FORSOME)
       ;; pieces on 0..0: there is no i < 0
       (let* ((ls (dk-peel!))
              (ls (append ls (dk-split-all! ls)))
              (i (cadr (find-first (lambda (f) (and (eq? (rsa-head f) 'IN) (dk-contains? f 'INTERVAL))) ls))))
         (rsa-interval-parts! i 0)
         (rsa-nn-rr! i)
         (rsa-absurd! (list 'IN i 'RR) (list '<= 0 i) (list '< i 0))))
      (#t
       ;; strict on 0..0: no i < j
       (let* ((ls (dk-peel!))
              (ls (append ls (dk-split-all! ls)))
              (g2 (dk-goal))
              (i (cadr (cadr g2)))
              (j (cadr (caddr g2))))
         (rsa-interval-parts! i 0)
         (rsa-interval-parts! j 0)
         (rsa-nn-rr! i j)
         (rsa-absurd! (list 'IN i 'RR) (list 'IN j 'RR) (list '<= 0 i) (list '<= j 0) (list '< i j))))))))
(qed 'step-approx-start)

;;; ---- (4b) the juxtaposition: Q(x) and a constant within e on ]x, y[ give Q(y) --

(sp (make-wff
  (rsa-foralls '(rsca_ rscx_ rscy_ rscf_ rsce_ rsck_)
    (rsa-imps (list '(IN rsca_ RR) '(IN rscx_ RR) '(IN rscy_ RR) '(IN rscf_ (FUN RR RR))
                    '(IN rsce_ RR) '(IN rsck_ RR) '(<= 0 rsce_)
                    (rsa-qpred 'rsca_ 'rscf_ 'rsce_ 'rscx_)
                    '(< rscx_ rscy_)
                    '(FORALL rscs_ (IMPLIES (IN rscs_ RR) (IMPLIES (< rscx_ rscs_) (IMPLIES (< rscs_ rscy_)
                        (<= (ABS (- (rscf_ rscs_) rsck_)) rsce_))))))
      (rsa-qpred 'rsca_ 'rscf_ 'rsce_ 'rscy_)))))
(define rsa4-all (dk-peel!))
(define rsa4-mid (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f 'rsck_))) "F near k on ]x,y["))
(define rsa4-nph (rsa-qpred-open! (dk-pick (dk-head? 'FORSOME) "Q(x)")))
(define rsa4-n (car rsa4-nph))
(define rsa4-p (cadr rsa4-nph))
(define rsa4-h (caddr rsa4-nph))
(define rsa4-apx (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f (list rsa4-h 'rsqz_)))) "the estimate on [a,x]"))
(fact 'fun-apply-type-c rsa4-p 'NN 'RR rsa4-n)
(dk-have! (list '< (list rsa4-p rsa4-n) 'rscy_)
  (lambda () (dk-ineq! (list 'IN (list rsa4-p rsa4-n) 'RR) '(IN rscx_ RR) '(IN rscy_ RR)
                       (list '= (list rsa4-p rsa4-n) 'rscx_) '(< rscx_ rscy_))))
(define rsa4-q (dk-skolem! (dk-fact! 'strict-seq-append-point rsa4-p rsa4-n 'rscy_)))
(fact 'fun-apply-type-c 'rscf_ 'RR 'RR 'rscy_)
(define rsa4-g (dk-skolem! (dk-fact! 'fun-append-constant-piece rsa4-h 'rscx_ 'rscy_ 'rsck_ '(rscf_ rscy_))))
(define rsa4-qlow (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f (list rsa4-q 'rsak_)))) "q = p below n"))
(define rsa4-glow (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f (list rsa4-h 'rsbt_)))) "g = h below x"))
(define rsa4-gmid (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f (list '= (list rsa4-g 'rsbt_) 'rsck_)))) "g = k on ]x,y["))
(define rsa4-pcs
  (dk-apply! (dk-fact! 'step-pieces-append rsa4-p rsa4-n rsa4-h rsa4-q) rsa4-g 'rscx_ 'rscy_ 'rsck_))
(fact 'nn-succ-closed rsa4-n)
(rsa-ew! (list 'SUCC rsa4-n) ass)
(rsa-ew! rsa4-q ass)
(rsa-ew! rsa4-g ass)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((and (eq? (rsa-head g) '=) (equal? (cadr g) (list rsa4-q 0)))
       (fact 'nn-zero-in)
       (fact 'nn-zero-le rsa4-n)
       (dk-apply! rsa4-qlow 0)
       (subst (list '= (list rsa4-q 0) (list rsa4-p 0)))
       (ass))
      ((dk-contains? g 'CCINT)
       (let ((z (dk-di-var!)))
         (rsa-ccint-parts! z 'rsca_ 'rscy_)
         (fact 'fun-apply-type-c 'rscf_ 'RR 'RR z)
         (use-em (list '<= z 'rscx_)
           (lambda ()
             (dk-apply! rsa4-glow z)
             (rsa-ccint-in! z 'rsca_ 'rscx_)
             (dk-apply! rsa4-apx z)
             (subst (list '= (list rsa4-g z) (list rsa4-h z)))
             (ass))
           (lambda ()
             (fact 'rr-not-le-lt z 'rscx_)
             (use-em (list '= z 'rscy_)
               (lambda ()
                 (subst (list '= z 'rscy_))
                 (subst (list '= (list rsa4-g 'rscy_) '(rscf_ rscy_)))
                 (rsa-abs-self! '(rscf_ rscy_) 'rsce_))
               (lambda ()
                 (have! (list 'AND (list '<= z 'rscy_) (list 'NOT (list '= z 'rscy_))))
                 (fact 'rr-le-ne-lt z 'rscy_)
                 (dk-apply! rsa4-gmid z)
                 (dk-apply! rsa4-mid z)
                 (subst (list '= (list rsa4-g z) 'rsck_))
                 (ass)))))))
      (#t (ass))))))
(qed 'step-approx-append)

;;; =====================================================================
;;; (5) THE ONE-SIDED WINDOWS OF A REGULATED FUNCTION AT A POINT.
;;;
;;; At t in [a, b] there are d > 0 and a constant l with |F(s) - l| <= e for
;;; the s of [a, b] in ]t, t + d[ (right) / ]t - d, t[ (left): the one-sided
;;; limit within [a, b] where it exists (t < b, resp. a < t), vacuously
;;; otherwise.  F is any function on the line agreeing with f on [a, b].
;;; =====================================================================

(define (rsa-rw t)
  (list 'FORSOME 'rsrd_
    (list 'AND '(IN rsrd_ RR)
      (list 'AND '(< 0 rsrd_)
        (list 'FORSOME 'rsrl_
          (list 'AND '(IN rsrl_ RR)
            (list 'FORALL 'rsrs_
              (rsa-imps (list '(IN rsrs_ RR) (list '< t 'rsrs_) (list '< 'rsrs_ (list '+ t 'rsrd_))
                              '(<= rsrs_ rswb_))
                '(<= (ABS (- (rswg_ rsrs_) rsrl_)) rswe_)))))))))

(define (rsa-lw t)
  (list 'FORSOME 'rsld_
    (list 'AND '(IN rsld_ RR)
      (list 'AND '(< 0 rsld_)
        (list 'FORSOME 'rsll_
          (list 'AND '(IN rsll_ RR)
            (list 'FORALL 'rsls_
              (rsa-imps (list '(IN rsls_ RR) '(<= rswa_ rsls_) (list '< (list '- t 'rsld_) 'rsls_)
                              (list '< 'rsls_ t))
                '(<= (ABS (- (rswg_ rsls_) rsll_)) rswe_)))))))))

(define (rsa5-stmt side)
  (rsa-foralls '(rswa_ rswb_ rswf_ rswg_ rswe_ rswt_)
    (rsa-imps (list '(IS-REGULATED-ON rswf_ rswa_ rswb_)
                    '(IN rswg_ (FUN RR RR))
                    '(FORALL rswz_ (IMPLIES (IN rswz_ (CCINT rswa_ rswb_)) (= (rswg_ rswz_) (rswf_ rswz_))))
                    '(POS-RR rswe_)
                    '(IN rswt_ (CCINT rswa_ rswb_)))
      (if (eq? side 'right) (rsa-rw 'rswt_) (rsa-lw 'rswt_)))))

;;; the goal is (AND A B): split it, close A by CLOSER, focus B
(define (rsa-first! closer)
  (let* ((g (dk-goal))
         (ls (dk-opened (lambda () (di))))
         (la (find-first (lambda (l) (alpha-equiv? (dk-goal-of l) (cadr g))) ls))
         (lb (find-first (lambda (l) (not (eq? l la))) ls)))
    (if (not (and la lb)) (error "rsa-first!: not a two-leaf conjunction" g))
    (dk-focus! la) (closer) (dk-focus! lb)))

(define (rsa5-drive! side)
  (let* ((right? (eq? side 'right))
         (ls (dk-peel!)))
    (dk-pos-parts! 'rswe_)
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-regulated-on '(IS-REGULATED-ON rswf_ rswa_ rswb_)))))
    (rsa-ccint-parts! 'rswt_ 'rswa_ 'rswb_)
    (let ((lim (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL)
                                         (dk-contains? f (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN))))
                        "the one-sided limit clause"))
          (gf (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f '(rswg_ rswz_))))
                       "F = f on [a,b]"))
          (vac (if right? '(<= rswb_ rswt_) '(<= rswt_ rswa_))))
      (use-em vac
        ;; no such side: any d, any l
        (lambda ()
          (fact 'rr-one-in) (fact 'rr-zero-in)
          (dk-have! '(< 0 1) (lambda () (dk-ineq!)))
          (rsa-ew! 1 ass)
          (rsa-first! ass)
          (rsa-ew! 0 ass)
          (let* ((ls (dk-peel!))
                 (s (cadr (find-first (lambda (f) (and (eq? (rsa-head f) 'IN) (eq? (caddr f) 'RR))) ls))))
            (if right?
                (rsa-absurd! (list 'IN s 'RR) '(IN rswt_ RR) '(IN rswb_ RR) vac
                             (list '< 'rswt_ s) (list '<= s 'rswb_))
                (rsa-absurd! (list 'IN s 'RR) '(IN rswt_ RR) '(IN rswa_ RR) vac
                             (list '< s 'rswt_) (list '<= 'rswa_ s)))))
        ;; the limit l and its delta at e
        (lambda ()
          (if right? (fact 'rr-not-le-lt 'rswb_ 'rswt_) (fact 'rr-not-le-lt 'rswt_ 'rswa_))
          (let* ((l (dk-skolem! (dk-apply! lim 'rswt_)))
                 (limf (list (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN)
                             'rswf_ '(CCINT rswa_ rswb_) 'rswt_ l)))
            (dk-split-all! (dk-landed (lambda () (mac-h (rsa-head limf) limf))))
            (let* ((eu (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f 'POS-RR)
                                                 (dk-contains? f l)))
                                "the eps clause"))
                   (d (dk-skolem! (dk-apply! eu 'rswe_)))
                   (du (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f d)
                                                 (dk-contains? f l)))
                                "the delta clause")))
              (dk-pos-parts! d)
              (rsa-ew! d ass)
              (rsa-first! ass)
              (rsa-ew! l ass)
              (let* ((ls (dk-peel!))
                     (s (cadr (find-first (lambda (f) (and (eq? (rsa-head f) 'IN) (eq? (caddr f) 'RR))) ls)))
                     (fs (list 'rswf_ s)))
                (if right?
                    (begin
                      (dk-have! (list '<= 'rswa_ s)
                        (lambda () (dk-ineq! (list 'IN s 'RR) '(IN rswa_ RR) '(IN rswt_ RR)
                                             '(<= rswa_ rswt_) (list '< 'rswt_ s))))
                      (rsa-ccint-in! s 'rswa_ 'rswb_))
                    (begin
                      (dk-have! (list '<= s 'rswb_)
                        (lambda () (dk-ineq! (list 'IN s 'RR) '(IN rswb_ RR) '(IN rswt_ RR)
                                             '(<= rswt_ rswb_) (list '< s 'rswt_))))
                      (rsa-ccint-in! s 'rswa_ 'rswb_)))
                (dk-apply! du s)
                (dk-apply! gf s)
                (fact 'fun-apply-type-c 'rswf_ '(CCINT rswa_ rswb_) 'RR s)
                (fact 'rr-sub-in-rr fs l)
                (fact 'rr-abs-closed (list '- fs l))
                (fact 'rr-lt-implies-le (list 'ABS (list '- fs l)) 'rswe_)
                (subst (list '= (list 'rswg_ s) fs))
                (ass)))))))))

(sp (make-wff (rsa5-stmt 'right)))
(rsa5-drive! 'right)
(qed 'regulated-on-right-window)

(sp (make-wff (rsa5-stmt 'left)))
(rsa5-drive! 'left)
(qed 'regulated-on-left-window)

;;; =====================================================================
;;; (6) THE CREEP: Q(a, F, e, b).
;;;
;;; G = { x in [a, b] : some w in [x, b] has Q(a, F, e, w) } (downward closed
;;; by construction, so no step function is ever cut down).  a is in G; at t in
;;; [a, b] take d below the two window radii: a point x >= w > t - d of G extends
;;; to every y <= t + d of [a, b], by at most two juxtapositions (through t with
;;; the left window's constant, past t with the right one's).  `ccint-creep'
;;; puts b in G.
;;; =====================================================================

(define rsa6-g
  (list 'SEP 'rsgx_ 'RR
    (list 'AND '(AND (<= rswa_ rsgx_) (<= rsgx_ rswb_))
      (list 'FORSOME 'rsgw_
        (list 'AND '(IN rsgw_ RR)
          (list 'AND '(<= rsgx_ rsgw_)
            (list 'AND '(<= rsgw_ rswb_) (rsa-qpred 'rswa_ 'rswg_ 'rswe_ 'rsgw_))))))))

(define (rsa6-local g)
  (list 'FORALL 't_
    (list 'IMPLIES '(IN t_ (CCINT rswa_ rswb_))
      (list 'FORSOME 'd_
        (list 'AND '(IN d_ RR)
          (list 'AND '(< 0 d_)
            (list 'IMPLIES
              (list 'FORSOME 'w_ (list 'AND (list 'IN 'w_ g) '(< (- t_ d_) w_)))
              (list 'FORALL 'y_
                (list 'IMPLIES (list 'AND '(IN y_ (CCINT rswa_ rswb_)) '(<= y_ (+ t_ d_)))
                      (list 'IN 'y_ g))))))))))

;;; close (IN Y G) from Q(XP), Y <= XP <= b, XP in RR, a <= Y <= b in context
(define (rsa6-in-g! y xp)
  (in-sep! (lambda () (ass))
    (lambda ()
      (dk-conj-close!
       (lambda ()
         (if (eq? (rsa-head (dk-goal)) 'FORSOME)
             (begin (rsa-ew! xp ass) (dk-conj-close! (lambda () (ass))))
             (ass)))))))

;;; land forall s in RR. X < s => s < Y => |F(s) - K| <= e, from the window
;;; universal UNIV; FACTS! lands, for the eigenvariable s, UNIV's guards
(define (rsa6-window! x y k univ facts!)
  (dk-have! (list 'FORALL 'rscs_
              (rsa-imps (list '(IN rscs_ RR) (list '< x 'rscs_) (list '< 'rscs_ y))
                (list '<= (list 'ABS (list '- '(rswg_ rscs_) k)) 'rswe_)))
    (lambda ()
      (let* ((ls (dk-peel!))
             (s (cadr (find-first (lambda (f) (and (eq? (rsa-head f) 'IN) (eq? (caddr f) 'RR))) ls))))
        (facts! s)
        (dk-apply! univ s)
        (ass)))))

(define (rsa6-append! x y k)
  (dk-apply! (dk-fact! 'step-approx-append 'rswa_ x y 'rswg_ 'rswe_ k)))

(sp (make-wff
  (rsa-foralls '(rswa_ rswb_ rswf_ rswg_ rswe_)
    (rsa-imps (list '(IS-REGULATED-ON rswf_ rswa_ rswb_)
                    '(IN rswg_ (FUN RR RR))
                    '(FORALL rswz_ (IMPLIES (IN rswz_ (CCINT rswa_ rswb_)) (= (rswg_ rswz_) (rswf_ rswz_))))
                    '(POS-RR rswe_))
      (rsa-qpred 'rswa_ 'rswg_ 'rswe_ 'rswb_)))))
(dk-peel!)
(dk-pos-parts! 'rswe_)
(dk-have! '(AND (IN rswa_ RR) (AND (IN rswb_ RR) (< rswa_ rswb_)))
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-regulated-on '(IS-REGULATED-ON rswf_ rswa_ rswb_)))))
    (dk-conj-close! (lambda () (ass)))))
(dk-split-all! (list '(AND (IN rswa_ RR) (AND (IN rswb_ RR) (< rswa_ rswb_)))))
(fact 'rr-lt-implies-le 'rswa_ 'rswb_)
(fact 'rr-leq-reflexive 'rswa_)
(fact 'rr-leq-reflexive 'rswb_)
(have! (list 'SUBSET rsa6-g 'RR)
  (lambda () (mac 'subset-def)
             (let ((m (dk-landed-1 (lambda () (di))))) (sep-me m) (ass))))
(dk-fact! 'step-approx-start 'rswa_ 'rswg_ 'rswe_)
(dk-have! (list 'IN 'rswa_ rsa6-g) (lambda () (rsa6-in-g! 'rswa_ 'rswa_)))
(dk-have! (list 'RR-UPPER-BOUND rsa6-g 'rswb_)
  (lambda ()
    (mac 'rr-upper-bound)
    (dk-conj-close!
     (lambda ()
       (if (eq? (rsa-head (dk-goal)) 'IN)
           (ass)
           (let ((m (dk-landed-1 (lambda () (di)))))
             (dk-split-all! (dk-landed (lambda () (sep-me m))))
             (ass)))))))

;;; the right window on ]LO, Y[ for LO >= t (LO-GE-T in context)
(define (rsa6-right-to-y! lo lo-ge-t y t d dr tpd tpr lr ru base)
  (rsa6-window! lo y lr ru
    (lambda (s)
      (dk-have! (list '< t s)
        (lambda () (apply dk-ineq! (append base (list (list 'IN s 'RR) lo-ge-t (list '< lo s))))))
      (dk-have! (list '< s tpr)
        (lambda () (apply dk-ineq! (append base (list (list 'IN s 'RR) (list '< s y)
                                                      (list '<= y tpd) (list '<= d dr))))))
      (dk-have! (list '<= s 'rswb_)
        (lambda () (apply dk-ineq! (append base (list (list 'IN s 'RR) (list '< s y)
                                                      (list '<= y 'rswb_)))))))))

(define (rsa6-local-step!)
  (let* ((mem (dk-landed-1 (lambda () (di))))
         (t (cadr mem)))
    (rsa-ccint-parts! t 'rswa_ 'rswb_)
    (let* ((rw (dk-fact! 'regulated-on-right-window 'rswa_ 'rswb_ 'rswf_ 'rswg_ 'rswe_ t))
           (dr (dk-skolem! rw))
           (lr (dk-skolem! (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORSOME) (eq? (cadr f) 'rsrl_)))
                                    "the right constant")))
           (ru (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f lr))) "the right window"))
           (lw (dk-fact! 'regulated-on-left-window 'rswa_ 'rswb_ 'rswf_ 'rswg_ 'rswe_ t))
           (dl (dk-skolem! lw))
           (ll (dk-skolem! (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORSOME) (eq? (cadr f) 'rsll_)))
                                    "the left constant")))
           (lu (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORALL) (dk-contains? f ll))) "the left window"))
           (d (dk-skolem! (dk-fact! 'rr-min-pos dr dl)))
           (tpd (list '+ t d)) (tmd (list '- t d))
           (tpr (list '+ t dr)) (tml (list '- t dl)))
      (rsa-ew! d ass)
      (rsa-first! ass)
      (let* ((ex (dk-landed-1 (lambda () (di))))
             (w (dk-skolem! ex))
             (wm (list 'IN w rsa6-g)))
        (dk-split-all! (dk-landed (lambda () (sep-me wm))))
        (let* ((x (dk-skolem! (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORSOME) (eq? (cadr f) 'rsgw_)))
                                       "the witness of w in G")))
               (ls (dk-peel!))
               (ls (append ls (dk-split-all! ls)))
               (y (cadr (find-first (lambda (f) (and (eq? (rsa-head f) 'IN) (dk-contains? f 'CCINT))) ls)))
               (base (list '(IN rswa_ RR) '(IN rswb_ RR) (list 'IN t 'RR) (list 'IN d 'RR) (list 'IN dr 'RR)
                           (list 'IN dl 'RR) (list 'IN w 'RR) (list 'IN x 'RR) (list 'IN y 'RR))))
          (rsa-ccint-parts! y 'rswa_ 'rswb_)
          (fact 'rr-leq-reflexive y)
          (fact 'rr-leq-reflexive t)
          (fact 'rr-add-in-rr t d)
          (use-em (list '<= y x)
            (lambda () (rsa6-in-g! y x))
            (lambda ()
              (fact 'rr-not-le-lt y x)
              (use-em (list '<= t x)
                (lambda ()
                  (rsa6-right-to-y! x (list '<= t x) y t d dr tpd tpr lr ru base)
                  (rsa6-append! x y lr)
                  (rsa6-in-g! y y))
                (lambda ()
                  (fact 'rr-not-le-lt t x)
                  (rsa6-window! x t ll lu
                    (lambda (s)
                      (dk-have! (list '<= 'rswa_ s)
                        (lambda () (apply dk-ineq! (append base (list (list 'IN s 'RR) (list '<= 'rswa_ w)
                                                                      (list '<= w x) (list '< x s))))))
                      (dk-have! (list '< tml s)
                        (lambda () (apply dk-ineq! (append base (list (list 'IN s 'RR) (list '< tmd w)
                                                                      (list '<= w x) (list '< x s)
                                                                      (list '<= d dl))))))))
                  (rsa6-append! x t ll)
                  (use-em (list '<= y t)
                    (lambda () (rsa6-in-g! y t))
                    (lambda ()
                      (fact 'rr-not-le-lt y t)
                      (rsa6-right-to-y! t (list '<= t t) y t d dr tpd tpr lr ru base)
                      (rsa6-append! t y lr)
                      (rsa6-in-g! y y))))))))))))

(dk-have! (rsa6-local rsa6-g) (lambda () (rsa6-local-step!)))
(define rsa6-atb (dk-fact! 'ccint-creep 'rswa_ 'rswb_ rsa6-g))
(sep-me (list 'IN 'rswb_ rsa6-g))
(dk-split-all!)
(define rsa6-x (dk-skolem! (dk-pick (lambda (f) (and (eq? (rsa-head f) 'FORSOME) (eq? (cadr f) 'rsgw_)))
                                   "the witness of b in G")))
(have! (list 'AND '(IN rswb_ RR) (list 'IN rsa6-x 'RR)))
(have! (list 'AND (list '<= 'rswb_ rsa6-x) (list '<= rsa6-x 'rswb_)))
(fact 'rr-leq-antisymmetric 'rswb_ rsa6-x)
(subst (list '= 'rswb_ rsa6-x))
(ass)
(qed 'regulated-on-step-approx-creep)

;;; =====================================================================
;;; (7) FROM Q(a, F, e, b) TO A STEP FUNCTION ON [a, b]; ONE e AT A TIME.
;;; =====================================================================

(sp (make-wff
  (rsa-foralls '(rsta_ rstb_ rstf_ rste_)
    (rsa-imps (list '(IN rsta_ RR) '(IN rstb_ RR) '(< rsta_ rstb_) (rsa-qpred 'rsta_ 'rstf_ 'rste_ 'rstb_))
      (list 'FORSOME 'rsth_
        (list 'AND '(IN rsth_ (FUN RR RR))
          (list 'AND '(IS-STEP-FN rsth_ rsta_ rstb_) (rsa-approx 'rstf_ 'rsth_ 'rste_ 'rsta_ 'rstb_))))))))
(dk-peel!)
(define rsa7-nph (rsa-qpred-open! (dk-pick (dk-head? 'FORSOME) "Q(b)")))
(define rsa7-n (car rsa7-nph))
(define rsa7-p (cadr rsa7-nph))
(define rsa7-h (caddr rsa7-nph))
(fact 'nn-zero-in)
(fact 'fun-apply-type-c rsa7-p 'NN 'RR 0)
(rsa-ew! rsa7-h ass)
(rsa-first!
 (lambda ()
   (mac 'is-step-fn)
   (dk-conj-close!
    (lambda ()
      (if (not (eq? (rsa-head (dk-goal)) 'FORSOME))
          (ass)
          (begin
            (ew rsa7-n)
            (ew rsa7-p)
            (dk-conj-close!
             (lambda ()
               (if (not (eq? (rsa-head (dk-goal)) 'IS-PARTITION))
                   (ass)
                   (begin
                     (mac 'is-partition)
                     (dk-conj-close!
                      (lambda ()
                        (if (not (equal? (dk-goal) (list '<= 1 rsa7-n)))
                            (ass)
                            (use-em (list '= rsa7-n 0)
                              (lambda ()
                                (dk-have! (list '= (list rsa7-p 0) 'rstb_)
                                  (lambda () (subst (list '= 0 rsa7-n)) (ass)))
                                (rsa-absurd! (list 'IN (list rsa7-p 0) 'RR) '(IN rsta_ RR) '(IN rstb_ RR)
                                             (list '= (list rsa7-p 0) 'rsta_) (list '= (list rsa7-p 0) 'rstb_)
                                             '(< rsta_ rstb_)))
                              (lambda ()
                                (let ((q (dk-skolem! (dk-fact! 'nn-nonzero-is-succ rsa7-n))))
                                  (fact 'nn-one-le-succ q)
                                  (subst (list '= rsa7-n (list 'SUCC q)))
                                  (ass)))))))))))))))))
(ass)
(qed 'step-approx-q-step-fn)

;;; Dieudonne (7.6.1), necessity, for ONE e: a function regulated on [a, b]
;;; is within e of a step function on [a, b].  The distance is measured with
;;; f extended to the line by EXTEND-CONST (IS-STEP-FN is total).
(define rsa7-e '(EXTEND-CONST rswf_ rswa_ rswb_))
(sp (make-wff
  (rsa-foralls '(rswa_ rswb_ rswf_)
    (rsa-imps (list '(IS-REGULATED-ON rswf_ rswa_ rswb_))
      (list 'FORALL 'rswe_
        (rsa-imps (list '(POS-RR rswe_))
          (list 'FORSOME 'rsth_
            (list 'AND '(IN rsth_ (FUN RR RR))
              (list 'AND '(IS-STEP-FN rsth_ rswa_ rswb_) (rsa-approx rsa7-e 'rsth_ 'rswe_ 'rswa_ 'rswb_))))))))))
(dk-peel!)
(dk-have! '(AND (IN rswa_ RR) (AND (IN rswb_ RR) (AND (< rswa_ rswb_) (IN rswf_ (FUN (CCINT rswa_ rswb_) RR)))))
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-regulated-on '(IS-REGULATED-ON rswf_ rswa_ rswb_)))))
    (dk-conj-close! (lambda () (ass)))))
(dk-split-all! (list '(AND (IN rswa_ RR) (AND (IN rswb_ RR) (AND (< rswa_ rswb_) (IN rswf_ (FUN (CCINT rswa_ rswb_) RR)))))))
(fact 'rr-lt-implies-le 'rswa_ 'rswb_)
(dk-fact! 'extend-const-in-fun 'rswa_ 'rswb_ 'rswf_)
(dk-have! (list 'FORALL 'rswz_ (list 'IMPLIES '(IN rswz_ (CCINT rswa_ rswb_)) (list '= (list rsa7-e 'rswz_) '(rswf_ rswz_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (rsa-ccint-parts! z 'rswa_ 'rswb_)
      (dk-apply! (dk-fact! 'extend-const-fixes 'rswa_ 'rswb_ z) 'rswf_)
      (fact 'fun-apply-type-c 'rswf_ '(CCINT rswa_ rswb_) 'RR z)
      (subst (list '= (list rsa7-e z) (list 'rswf_ z)))
      (rsa-close!))))
(dk-apply! (dk-fact! 'regulated-on-step-approx-creep 'rswa_ 'rswb_ 'rswf_ rsa7-e 'rswe_))
(dk-apply! (dk-fact! 'step-approx-q-step-fn 'rswa_ 'rswb_ rsa7-e 'rswe_))
(ass)
(qed 'regulated-on-step-approx)

;;; =====================================================================
;;; (8) THE HEADLINE: Dieudonne (7.6.1), necessity.
;;;
;;; The k-th approximant is CHOSEN within 1/(k+1) of f (section 7 at
;;; e = recip(k + 1)); the family is k |-> CHOICE of the SEP of such step
;;; functions, the witness-family-choice.scm pattern.  1/(k+1) <= 1/(n+1) < eps
;;; for n <= k (nn-recip-succ-antitone, nn-recip-succ-small).
;;; =====================================================================

(define rsa8-e '(EXTEND-CONST f a b))
(define (rsa8-r k) (list 'RECIP (list '+ k 1)))
(define (rsa8-s k)
  (list 'SEP 'rsch_ '(FUN RR RR)
    (list 'AND '(IS-STEP-FN rsch_ a b) (rsa-approx rsa8-e 'rsch_ (rsa8-r k) 'a 'b))))
(define (rsa8-c k) (list 'CHOICE (rsa8-s k)))
(define rsa8-fam (list 'VNB-LAMBDA 'rscj_ 'NN (rsa8-c 'rscj_)))

(sp (make-wff (parse-string "forall([a in rr, b in rr, f], is-regulated-on(f, a, b) implies
   forsome([fam in fun(nn, fun(rr, rr))], forall([k in nn], is-step-fn(fam(k), a, b)) and
     is-unif-limit-on(fam, extend-const(f, a, b), a, b)))")))
(dk-peel!)
(dk-have! '(AND (< a b) (IN f (FUN (CCINT a b) RR)))
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-regulated-on '(IS-REGULATED-ON f a b)))))
    (dk-conj-close! (lambda () (ass)))))
(dk-split-all! (list '(AND (< a b) (IN f (FUN (CCINT a b) RR)))))
(fact 'rr-lt-implies-le 'a 'b)
(dk-fact! 'extend-const-in-fun 'a 'b 'f)
(define rsa8-each (dk-fact! 'regulated-on-step-approx 'a 'b 'f))

;;; for each k, CHOICE(S(k)) is a step function within 1/(k+1)
(define rsa8-pt-form
  (list 'FORALL 'rsck_
    (list 'IMPLIES '(IN rsck_ NN)
      (list 'AND (list 'IN (rsa8-c 'rsck_) '(FUN RR RR))
        (list 'AND (list 'IS-STEP-FN (rsa8-c 'rsck_) 'a 'b)
                   (rsa-approx rsa8-e (rsa8-c 'rsck_) (rsa8-r 'rsck_) 'a 'b))))))
(dk-have! rsa8-pt-form
  (lambda ()
    (let* ((k (dk-di-var!)))
      (fact 'nn-recip-succ-pos k)
      (let ((h (dk-skolem! (dk-apply! rsa8-each (rsa8-r k)))))
        (dk-split-all!
          (choose! (rsa8-s k) h
                   (lambda () (in-sep! (lambda () (ass))
                                       (lambda () (dk-conj-close! (lambda () (ass))))))))
        (dk-conj-close! (lambda () (ass)))))))
(define rsa8-pt (dk-pick (lambda (f) (alpha-equiv? f rsa8-pt-form)) "the per-index facts"))

(define (rsa8-at! k) (dk-split! (dk-apply! rsa8-pt k)))

(dk-have! (list 'IN rsa8-fam '(FUN NN (FUN RR RR)))
  (lambda ()
    (dk-lam-t!)
    (let ((k (dk-di-var!)))
      (rsa8-at! k)
      (ass))))
(rsa-ew! rsa8-fam ass)
(rsa-first!
 (lambda ()
   (let ((k (dk-di-var!)))
     (dk-lam-b!)
     (rsa8-at! k)
     (ass))))
(mac 'is-unif-limit-on)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (rsa-head (dk-goal)) 'FORALL))
       (ass)
       (let* ((ls (dk-peel!))
              (eps (cadr (find-first (dk-head? 'POS-RR) ls)))
              (n (dk-skolem! (dk-fact! 'nn-recip-succ-small eps))))
         (fact 'rr-pos-rr-in-rr eps)
         (rsa-ew! n ass)
         (let* ((ls (dk-peel!))
                (ls (append ls (dk-split-all! ls)))
                (k (cadr (find-first (lambda (f) (and (eq? (rsa-head f) 'IN) (eq? (caddr f) 'NN))) ls)))
                (x (cadr (find-first (lambda (f) (and (eq? (rsa-head f) 'IN) (dk-contains? f 'CCINT))) ls)))
                (c (rsa8-c k))
                (ex (list rsa8-e x)) (cx (list c x))
                (rk (rsa8-r k)) (rn (rsa8-r n))
                (ab (list 'ABS (list '- ex cx))))
           (dk-lam-b!)
           (rsa8-at! k)
           (dk-apply! (dk-pick (lambda (f) (alpha-equiv? f (rsa-approx rsa8-e c rk 'a 'b))) "approx at k") x)
           (fact 'nn-recip-succ-antitone n k)
           (fact 'nn-recip-succ-pos k)
           (fact 'nn-recip-succ-pos n)
           (fact 'rr-pos-rr-in-rr rk)
           (fact 'rr-pos-rr-in-rr rn)
           (fact 'ccint-elt-in-rr 'a 'b x)
           (fact 'fun-apply-type-c rsa8-e 'RR 'RR x)
           (fact 'fun-apply-type-c c 'RR 'RR x)
           (fact 'rr-sub-in-rr ex cx)
           (fact 'rr-abs-closed (list '- ex cx))
           (dk-ineq! (list 'IN ab 'RR) (list 'IN rk 'RR) (list 'IN rn 'RR) (list 'IN eps 'RR)
                     (list '<= ab rk) (list '<= rk rn) (list '< rn eps)))))))
(qed 'regulated-on-is-step-limit)
