;;; unif-cauchy-limit.scm -- unif-cauchy-has-uniform-limit, PROVEN (2026-09-14).
;;;
;;;   A uniformly Cauchy sequence fam : NN -> (PTS(s) -> RR) has a uniform
;;;   limit: some g in FUN(PTS(s), RR) with CONVERGES-UNIFORMLY(s, fam, g).
;;;
;;; The completeness of the sup metric, proved once already over RR as
;;; `uniform-cauchy-limit' (theorem-library/antiderivable-uniform-limit.scm);
;;; this is the same construction over a metric-space domain, with the strict
;;; `<' the CONVERGES-UNIFORMLY definition asks for:
;;;
;;;   g := VNB-LAMBDA x in PTS(s). SEQ-LIMIT(VNB-LAMBDA k in NN. fam(k)(x))
;;;
;;;   * g in FUN(PTS(s), RR): `dk-lam-t!' -- PTS(s) is a set by the metric-space
;;;     unfold, and the body is real by `seq-limit-in-rr' (unconditional).
;;;   * at each x the section k |-> fam(k)(x) is Cauchy (uniform Cauchy at x,
;;;     `<' weakened to `<='), so it CONVERGES (`rr-cauchy-converges'), and
;;;     `seq-limit-converges-to' names SEQ-LIMIT as its limit.
;;;   * uniform estimate: given eps, halve it (d + d = eps); the uniform Cauchy
;;;     threshold cap for d works: for k >= cap and any x, every later term is
;;;     within d of fam(k)(x), so the LIMIT is within d of it
;;;     (`rr-limit-tail-abs-le'), and d < eps.
;;;
;;; Window: the file must sit BEFORE its citer ascoli-bridge (which assembles
;;; `unif-cauchy-cont-implies-uniform-limit' from this fact), and AFTER
;;; theorem-library/seq-limit-core (SEQ-LIMIT, seq-limit-in-rr, seq-limit-converges-to,
;;; rr-limit-tail-abs-le, rr-cauchy-converges) -- the block SPLIT OUT of seq-limit.scm on
;;; 2026-09-14 precisely so that it, and metric-limit-unique (rr-limit-unique), load
;;; BEFORE ascoli-bridge; this file sits right after ascoli-analytic-cores.  Everything
;;; else cited loads earlier still: ascoli-analytic-cores (IS-UNIF-CAUCHY),
;;; ascoli-arzela-statement (CONVERGES-UNIFORMLY), fun-apply-type-proof, rr-abs-basics,
;;; rr-order-basics, pos-rr-bridges, rr-halving, binary-minus-laws.
;;;
;;; Helper prefix `ucl-'.

;;; ---- file-local helpers ----------------------------------------------------

(define (ucl-seq v) (list 'VNB-LAMBDA 'k_ 'NN (list (list 'fam 'k_) v)))
(define ucl-lim (list 'VNB-LAMBDA 'x_ '(PTS s) (list 'SEQ-LIMIT (ucl-seq 'x_))))

;;; `have!' that declines when the claim is already in context (a `cut' of an
;;; in-context formula self-loops; `have!' errors on it).
(define (ucl-have! form . opt)
  (let ((f (->raw-formula form)))
    (if (any-pred (lambda (a) (alpha-equiv? a f)) (dk-asms))
        f
        (apply have! form opt))))

;;; does the term hold an applied VNB-LAMBDA?
(define (ucl-redex? t)
  (and (pair? t)
       (or (and (pair? (car t)) (eq? (caar t) 'VNB-LAMBDA))
           (any-pred ucl-redex? t))))

;;; beta-reduce the goal while it holds a redex (so the last `lam-b' never
;;; fires on nothing and warns)
(define (ucl-beta!)
  (let loop ((n 0))
    (if (and (< n 10) (ucl-redex? (dk-goal)))
        (begin (lam-b) (loop (+ n 1))))))

;;; the premise indices `ineq' may be handed: those whose atoms the oracle can
;;; certify in RR (copied from antiderivable-uniform-limit.scm's au-usable-indices;
;;; `contra--usable-indices' is unreachable from a library proof).
(define (ucl-usable-indices)
  (let* ((sqn  (proof-state-focus *ps*))
         (asms (sequent-node-assumptions sqn)))
    (let loop ((as asms) (k 1) (acc '()))
      (if (null? as)
          (reverse acc)
          (let* ((f  (wff-formula (car as)))
                 (pr (formula->lin+rel f)))
            (loop (cdr as) (+ k 1)
                  (if (and pr
                           (let allok ((vs (map car (lin-coeffs (car pr)))))
                             (or (null? vs)
                                 (and (ineq-atom-rr-ok? (car vs) asms '())
                                      (allok (cdr vs))))))
                      (cons k acc)
                      acc)))))))
(define (ucl-ineq!) (apply ineq (ucl-usable-indices)))

;;; the eigenvariable among VARS typed in DOM
(define (ucl-typed vars dom)
  (or (any-pred (lambda (v)
                  (any-pred (lambda (f) (equal? f (list 'IN v dom))) (dk-asms)))
                vars)
      (error "ucl-typed: no variable typed in" dom (map symbol->string vars))))

;;; peel the goal's whole prefix, split the landed conjunctions (an AND-guarded
;;; universal lands its guard as ONE conjunction), return the new eigenvariables.
(define (ucl-peel-vars!)
  (let ((fv0 (free-vars (dk-goal))))
    (dk-split-all! (dk-peel!))
    (filter (lambda (v) (not (memq v fv0))) (free-vars (dk-goal)))))

;;; (IN ((fam k) v) RR), by the two fun-apply-type-c steps
(define (ucl-app-real! k v)
  (fact 'fun-apply-type-c 'fam 'NN '(FUN (PTS s) RR) k)
  (fact 'fun-apply-type-c (list 'fam k) '(PTS s) 'RR v))

;;; (IN (abs (- a b)) RR) for a, b already typed in RR
(define (ucl-abs-real! a b)
  (fact 'rr-sub-in-rr a b)
  (fact 'rr-abs-closed (list '- a b)))

;;; the section  k_ |-> fam(k_)(v)  is a real sequence
(define (ucl-seqfun! v)
  (ucl-have! (list 'IN (ucl-seq v) '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let ((j (dk-di-var!)))
        (ucl-app-real! j v)
        (ass)))))

;;; From the uniform-Cauchy clause UC and the two guards, land
;;;    (< (abs (- ((fam m) v) ((fam p) v))) e)
;;; for thresholds  cap <= m, cap <= p  already in context.
(define (ucl-uc-at! inner cap m p v)
  (ucl-have! (list 'AND (list 'IN m 'NN) (list '<= cap m)))
  (ucl-have! (list 'AND (list 'IN p 'NN) (list '<= cap p)))
  (dk-apply! inner m p v))

;;; (IN e RR) off (POS-RR e), by citation -- never by `mac-h pos-rr' (destructive)
(define (ucl-real! e)
  (if (not (any-pred (lambda (a) (equal? a (list 'IN e 'RR))) (dk-asms)))
      (fact 'rr-pos-rr-in-rr e)))

;;; the same, weakened to <=  (typing the abs so rr-lt-implies-le detaches)
(define (ucl-uc-le! inner cap m p v e)
  (ucl-uc-at! inner cap m p v)
  (ucl-real! e)
  (ucl-app-real! m v)
  (ucl-app-real! p v)
  (ucl-abs-real! (list (list 'fam m) v) (list (list 'fam p) v))
  (fact 'rr-lt-implies-le
        (list 'abs (list '- (list (list 'fam m) v) (list (list 'fam p) v))) e))

;;; ---- the theorem -------------------------------------------------------------

(sp (make-wff
  '(FORALL s (FORALL fam
     (IMPLIES (IN fam (FUN NN (FUN (PTS s) RR)))
       (IMPLIES (IS-UNIF-CAUCHY s fam)
         (FORSOME g (AND (IN g (FUN (PTS s) RR))
                         (CONVERGES-UNIFORMLY s fam g)))))))))
(dk-peel!)
(dk-split-all! (dk-landed (lambda () (mac-h 'is-unif-cauchy '(IS-UNIF-CAUCHY s fam)))))
(define ucl-uc
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'abs)))
           "the uniform-Cauchy clause"))

;;; PTS(s) is a set (a metric-space carrier), read off on a side branch
(have! '(IN (PTS s) SET)
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)))))
    (ass)))

;;; the limit map is a function PTS(s) -> RR
(have! (list 'IN ucl-lim '(FUN (PTS s) RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (dk-di-var!)))
      (fact 'seq-limit-in-rr (ucl-seq v))
      (ass))))

;;; at a point v of PTS(s) the section converges, to SEQ-LIMIT of itself
(define (ucl-converges! v)
  (ucl-seqfun! v)
  (let* ((imp (dk-fact! 'rr-cauchy-converges (ucl-seq v)))
         (ant (cadr imp)))
    (ucl-have! ant
      (lambda ()
        (let* ((vars (ucl-peel-vars!))
               (e    (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)
                                                     (memq (cadr f) vars)))
                                    "the peeled epsilon")))
               (ex   (dk-apply! ucl-uc e))
               (cap  (dk-skolem! ex))
               (inner (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                (dk-contains? f cap) (dk-contains? f 'abs)))
                               "the instantiated Cauchy universal")))
          (ew cap)
          (dk-conj-close!
           (lambda ()
             (if (eq? (car (dk-goal)) 'IN)
                 (ass)
                 (let* ((ws (ucl-peel-vars!))
                        (dd (cadr (cadr (dk-goal))))          ; (- (seq m) (seq p))
                        (m  (cadr (cadr dd)))
                        (p  (cadr (caddr dd))))
                   (ucl-beta!)
                   (ucl-uc-le! inner cap m p v e)
                   (ass))))))))
    (detach! imp)
    (fact 'seq-limit-converges-to (ucl-seq v))))

;;; ---- the witness -----------------------------------------------------------

(ew ucl-lim)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((memq (car g) '(IN IS-METRIC-SPACE)) (ass))
       ((eq? (car g) 'CONVERGES-UNIFORMLY)
        (mac 'converges-uniformly)
        (dk-conj-close!
         (lambda ()
           (let ((g2 (dk-goal)))
             (cond
               ((memq (car g2) '(IN IS-METRIC-SPACE)) (ass))
               (#t
                ;; forall eps > 0. exists cap. forall k >= cap. forall x. |fam(k)(x) - g(x)| < eps
                (let* ((vars (ucl-peel-vars!))
                       (e (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)
                                                          (memq (cadr f) vars)))
                                         "the peeled epsilon")))
                       (d (begin (ucl-real! e) (dk-halve! e)))
                       (ex (dk-apply! ucl-uc d))
                       (cap (dk-skolem! ex))
                       (inner (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                        (dk-contains? f cap) (dk-contains? f 'abs)))
                                       "the instantiated Cauchy universal")))
                  (ew cap)
                  (dk-conj-close!
                   (lambda ()
                     (if (eq? (car (dk-goal)) 'IN)
                         (ass)
                         (let* ((ws (ucl-peel-vars!))
                                (k  (ucl-typed ws 'NN))
                                (x  (ucl-typed ws '(PTS s))))
                           (ucl-beta!)                       ; g(x) -> SEQ-LIMIT(seq x)
                           (ucl-converges! x)
                           (let ((lv   (list 'SEQ-LIMIT (ucl-seq x)))
                                 (fkx  (list (list 'fam k) x)))
                             (fact 'seq-limit-in-rr (ucl-seq x))
                             (ucl-app-real! k x)
                             ;; the tail estimate:  for j >= cap, |seq(j) - fam(k)(x)| <= d
                             (ucl-have!
                              (list 'FORALL 'j_
                                (list 'IMPLIES '(IN j_ NN)
                                  (list 'IMPLIES (list '<= cap 'j_)
                                    (list '<= (list 'abs (list '- (list (ucl-seq x) 'j_) fkx)) d))))
                              (lambda ()
                                (let* ((js (ucl-peel-vars!))
                                       (j  (ucl-typed js 'NN)))
                                  (ucl-beta!)
                                  (ucl-uc-le! inner cap j k x d)
                                  (ass))))
                             (fact 'rr-limit-tail-abs-le (ucl-seq x) lv fkx d cap)
                             ;; |lv - fkx| <= d, d + d = e, 0 < d  =>  |fkx - lv| < e
                             (ucl-abs-real! lv fkx)
                             (ucl-abs-real! fkx lv)
                             (fact 'rr-abs-sub-sym lv fkx)
                             (ucl-ineq!)))))))))))))
       (#t (error "ucl: unexpected conjunct" (expression->string g)))))))
(qed 'unif-cauchy-has-uniform-limit)
(topic! 'unif-cauchy-has-uniform-limit 'analysis)
