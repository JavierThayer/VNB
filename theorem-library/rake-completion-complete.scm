;;; rake-completion-complete.scm -- BATCH 12-D (2026-09-20):
;;; `completion-is-complete' (structure-library/metric-completion.scm:110,
;;; asserted `well-known') and the general bricks its diagonal argument needs.
;;;
;;;     forall M.  IS-METRIC-SPACE(M)  =>  IS-COMPLETE(COMPLETION M)
;;;
;;; THE TWO GENERAL BRICKS, proved first and stated about CONVERGES-TO in RR-MS
;;; alone -- they mention neither the completion nor a quotient:
;;;
;;;   rr-limit-tail-le     f -> lv, c > 0  =>  f(k) <= lv + c for all large k
;;;                          (a bound on the LIMIT reads back onto the TAIL --
;;;                          the converse direction of r7q-dist-value, which
;;;                          batch 8-C named as the one missing piece)
;;;   rr-limit-le-of-tail  f -> lv, f(k) <= c for all large k  =>  lv <= c
;;;                          (the tree has only `rr-limit-tail-abs-le', whose
;;;                          hypothesis and conclusion are both about an
;;;                          ABSOLUTE value around a fixed point, and
;;;                          `rr-limit-le', whose hypothesis must hold at EVERY
;;;                          index)
;;;
;;; Helper prefix `r12d-'.  All helpers are file-local.

;;; ---- file-local driver helpers ---------------------------------------

(define (r12d-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "r12d-find: no context formula" what))
          ((pred (car l)) (car l))
          (#t (loop (cdr l))))))

;;; The eps-universal of an unfolded CONVERGES-TO(RR-MS, SQ, LV).  `mac-h'
;;; CONSUMES the CONVERGES-TO, so a caller that needs it again works in a lane.
(define (r12d-conv-tail! sq lv)
  (dk-split!
   (dk-landed-find (lambda () (mac-h 'CONVERGES-TO (list 'CONVERGES-TO 'RR-MS sq lv)))
                   (lambda (a) (and (pair? a) (eq? (car a) 'AND)))))
  (r12d-find "the eps-universal of the limit"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a 'POS-RR) (dk-contains? a sq)))))

;;; The inner (FORALL k ... (<= bigN k) => ...) clause a skolemized threshold
;;; BIGN left in the context.  Discriminated on the threshold, never on a head.
(define (r12d-inner bigN sq)
  (r12d-find "the skolemized tail clause"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a bigN) (dk-contains? a sq)
                              (not (dk-contains? a 'POS-RR))))))

;;; |f(kk) - lv| <= EV from the distance bound, split into its two linear
;;; halves.  Every atom typed FIRST: `rr-ms-dist' and `rr-abs-bound' are both
;;; GUARDED, and an untyped argument spawns a side condition nobody closes.
(define (r12d-abs-split! sq kk lv ev)
  (fact 'fun-apply-type-c sq 'NN 'RR kk)
  (fact 'rr-sub-in-rr (list sq kk) lv)
  (fact 'rr-abs-closed (list '- (list sq kk) lv))
  (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list sq kk) lv) ev))
  (dk-split! (dk-landed-1
              (lambda () (mac-h 'rr-abs-bound
                                (list '<= (list 'abs (list '- (list sq kk) lv)) ev))))))

;;; =====================================================================
;;; B1.  rr-limit-tail-le -- a bound on the limit reads back onto the tail.
;;; =====================================================================

(sp (make-wff (forall-guarded '(f lv c)
   '((IN f (FUN NN RR)) (IN lv RR) (IN c RR))
   (list 'IMPLIES '(CONVERGES-TO RR-MS f lv)
     (list 'IMPLIES '(POS-RR c)
       (forsome-guarded '(nt_) '((IN nt_ NN))
         (forall-guarded '(k_) '((IN k_ NN))
           '(IMPLIES (<= nt_ k_) (<= (f k_) (+ lv c))))))))))
(dk-peel!)
(define r12d-b1-tail (r12d-conv-tail! 'f 'lv))
(let* ((ex   (dk-apply! r12d-b1-tail 'c))
       (bigN (dk-skolem! ex))
       (inner (r12d-inner bigN 'f)))
  (ew bigN)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IN)
         (ass)
         (begin
           (dk-peel!)
           (let ((kk (cadr (cadr (dk-goal)))))
             (dk-apply! inner kk)
             (r12d-abs-split! 'f kk 'lv 'c)
             (dk-ineq! (list '<= (list '- (list 'f kk) 'lv) 'c))))))))
(qed 'rr-limit-tail-le)
(topic! 'rr-limit-tail-le 'analysis)
(alias! 'rr-limit-tail-le
        "a bound on the limit of a real sequence holds on its tail, up to any slack")

;;; =====================================================================
;;; B2.  rr-limit-le-of-tail -- a tail bound passes to the limit.
;;; =====================================================================

(sp (make-wff (forall-guarded '(f lv c nt_)
   '((IN f (FUN NN RR)) (IN lv RR) (IN c RR) (IN nt_ NN))
   (list 'IMPLIES '(CONVERGES-TO RR-MS f lv)
     (list 'IMPLIES
       (forall-guarded '(k_) '((IN k_ NN)) '(IMPLIES (<= nt_ k_) (<= (f k_) c)))
       '(<= lv c))))))
(dk-peel!)
(define r12d-b2-pt
  (r12d-find "the pointwise tail bound"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a 'nt_) (dk-contains? a 'f)
                              (not (dk-contains? a 'POS-RR))))))
(define r12d-b2-tail (r12d-conv-tail! 'f 'lv))
(fact 'rr-sub-in-rr 'lv 'c)
(have! (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps) (list '<= '(- lv c) 'eps)))
  (lambda ()
    (let* ((pl (dk-peel!))
           (ev (cadr (or (find-first (dk-head? 'POS-RR) pl)
                         (error "r12d-b2: di landed no POS-RR")))))
      (fact 'rr-pos-rr-in-rr ev)
      (let* ((ex   (dk-apply! r12d-b2-tail ev))
             (bigN (dk-skolem! ex))
             (inner (r12d-inner bigN 'f))
             (kk   (list 'MAX 'nt_ bigN)))
        (fact 'nn-max-closed 'nt_ bigN)
        (fact 'nn-in-rr 'nt_) (fact 'nn-in-rr bigN) (fact 'nn-in-rr kk)
        (fact 'rr-le-max-left 'nt_ bigN)
        (fact 'rr-le-max-right 'nt_ bigN)
        (dk-apply! inner kk)
        (dk-apply! r12d-b2-pt kk)
        (r12d-abs-split! 'f kk 'lv ev)
        (dk-ineq! (list '<= (list '- ev) (list '- (list 'f kk) 'lv))
                  (list '<= (list 'f kk) 'c))))))
(fact 'rr-le-all-pos-nonpos '(- lv c))
(dk-ineq! '(<= (- lv c) 0))
(qed 'rr-limit-le-of-tail)
(topic! 'rr-limit-le-of-tail 'analysis)
(alias! 'rr-limit-le-of-tail
        "a tail bound on a real sequence passes to its limit")

;;; =====================================================================
;;; S1.  r12d-repfam -- a Cauchy sequence of CLASSES has a family of
;;; REPRESENTATIVES, as a FUNCTION on NN.
;;;
;;; The choice is NN-INDEXED and NON-DEPENDENT: the set chosen from at index p
;;; does not mention any earlier choice, so this is global CHOICE under a
;;; VNB-LAMBDA (witness-family-choice.scm's shape), never `dc-on-nn-pred'.
;;; The CHOICE term does not escape: the statement concludes with a FORSOME.
;;; =====================================================================

;; the representatives of the class bigF(pv), as a SET.  Binders `hv_' / `pv_':
;; names nothing in the library binds, so subst-free never renames them.
(define (r12d-rep-sep pv)
  (list 'SEP 'hv_ '(CSEQ M)
        (list '= (list 'bigF pv) '(CLASS (CAUCHY-SETOID M) hv_))))
(define (r12d-rep-pick pv) (list 'CHOICE (r12d-rep-sep pv)))
(define r12d-rep-lam (list 'VNB-LAMBDA 'pv_ 'NN (r12d-rep-pick 'pv_)))

;; the common tail: exhibit LAM, type it by `lam-t', and close the pointwise
;; claim by `lam-b' against the per-index fact PT.
(define (r12d-exhibit! lam pt)
  (ew lam)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (if (and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
           (begin
             (dk-lam-t!)
             (let ((z (dk-di-var!)))
               (dk-split! (dk-deepest (lambda () (inst+ pt z))))
               (ass)))
           (let ((z (dk-di-var!)))
             (lam-b)
             (dk-split! (dk-deepest (lambda () (inst+ pt z))))
             (dk-conj-close! (lambda () (ass)))))))))

(sp (make-wff (forall-guarded '(M) '((IS-METRIC-SPACE M))
  (forall-guarded '(bigF) '((IN bigF (FUN NN (QUOTIENT (CAUCHY-SETOID M)))))
    (forsome-guarded '(rf) '((IN rf (FUN NN (CSEQ M))))
      (forall-guarded '(p_) '((IN p_ NN))
        '(= (bigF p_) (CLASS (CAUCHY-SETOID M) (rf p_)))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(have! (forall-guarded '(p_) '((IN p_ NN))
         (list 'AND (list 'IN (r12d-rep-pick 'p_) '(CSEQ M))
                    (list '= '(bigF p_)
                          (list 'CLASS '(CAUCHY-SETOID M) (r12d-rep-pick 'p_)))))
  (lambda ()
    (let ((pv (dk-di-var!)))
      (fact 'fun-apply-type-c 'bigF 'NN '(QUOTIENT (CAUCHY-SETOID M)) pv)
      (let* ((ex (dk-fact! 'quotient-rep '(CAUCHY-SETOID M) (list 'bigF pv)))
             (w  (dk-skolem! ex)))
        (have! (list 'IN w '(CSEQ M))
          (lambda ()
            (mac-h 'rkt-cauchy-setoid-pts (list 'IN w '(PTS (CAUCHY-SETOID M))))
            (ass)))
        (dk-split-all!
         (choose! (r12d-rep-sep pv) w
                  (lambda () (in-sep! (lambda () (ass)) (lambda () (ass))))))
        (dk-conj-close! (lambda () (ass)))))))
(r12d-exhibit! r12d-rep-lam (car (dk-asms)))
(qed 'r12d-repfam)
(topic! 'r12d-repfam 'analysis)
(alias! 'r12d-repfam
        "a sequence of classes in the completion has a sequence of representatives")

;;; =====================================================================
;;; S2.  r12d-rapid-indices -- a family of CAUCHY THRESHOLDS, one per index.
;;;
;;; rf(p) is Cauchy, so for the positive radius rad(p) there is a threshold
;;; past which its terms are within rad(p) of each other.  Choosing one such
;;; threshold for every p is again an NN-indexed, NON-DEPENDENT choice.
;;; The conclusion is CURRIED (i <= , j <= as separate antecedents), while
;;; IS-CAUCHY-SEQ's own clause has a CONJUNCTIVE antecedent: `fact' will not
;;; split one, so the conjunction is `dk-have!'d at the point of use.
;;; =====================================================================

(define (r12d-idx-prop nv pv)
  (forall-guarded '(iv_ jv_) '((IN iv_ NN) (IN jv_ NN))
    (list 'IMPLIES (list '<= nv 'iv_)
      (list 'IMPLIES (list '<= nv 'jv_)
        (list '<= (list '(DIST M) (list (list 'rf pv) 'iv_) (list (list 'rf pv) 'jv_))
              (list 'rad pv))))))
(define (r12d-idx-sep pv) (list 'SEP 'nv_ 'NN (r12d-idx-prop 'nv_ pv)))
(define (r12d-idx-pick pv) (list 'CHOICE (r12d-idx-sep pv)))
(define r12d-idx-lam (list 'VNB-LAMBDA 'pv_ 'NN (r12d-idx-pick 'pv_)))

(sp (make-wff (forall-guarded '(M) '((IS-METRIC-SPACE M))
  (forall-guarded '(rf rad) '((IN rf (FUN NN (CSEQ M))) (IN rad (FUN NN RR)))
    (list 'IMPLIES (forall-guarded '(p_) '((IN p_ NN)) '(POS-RR (rad p_)))
      (forsome-guarded '(mm) '((IN mm (FUN NN NN)))
        (forall-guarded '(p_) '((IN p_ NN))
          (forall-guarded '(i_ j_) '((IN i_ NN) (IN j_ NN))
            '(IMPLIES (<= (mm p_) i_)
               (IMPLIES (<= (mm p_) j_)
                 (<= ((DIST M) ((rf p_) i_) ((rf p_) j_)) (rad p_))))))))))))
(dk-peel!)
(define r12d-idx-pos
  (r12d-find "the pointwise positivity of rad"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))
(have! (forall-guarded '(p_) '((IN p_ NN))
         (list 'AND (list 'IN (r12d-idx-pick 'p_) 'NN)
                    (r12d-idx-prop (r12d-idx-pick 'p_) 'p_)))
  (lambda ()
    (let ((pv (dk-di-var!)))
      (fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) pv)
      (fact 'r7q-cseq-cauchy 'M (list 'rf pv))
      (dk-apply! r12d-idx-pos pv)
      (dk-split!
       (dk-landed-find
        (lambda () (mac-h 'IS-CAUCHY-SEQ (list 'IS-CAUCHY-SEQ 'M (list 'rf pv))))
        (lambda (a) (and (pair? a) (eq? (car a) 'AND)))))
      (let* ((tail (r12d-find "the eps-universal of the Cauchy clause"
                              (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                               (dk-contains? a 'POS-RR)
                                               (dk-contains? a (list 'rf pv))))))
             (ex   (dk-apply! tail (list 'rad pv)))
             (w    (dk-skolem! ex))
             (inner (r12d-find "the skolemized Cauchy tail clause"
                               (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                (dk-contains? a w)
                                                (dk-contains? a (list 'rf pv))
                                                (not (dk-contains? a 'POS-RR)))))))
        (dk-split-all!
         (choose! (r12d-idx-sep pv) w
                  (lambda ()
                    (in-sep! (lambda () (ass))
                             (lambda ()
                               (dk-peel!)
                               (let* ((gg (dk-goal))
                                      (dt (cadr gg))
                                      (iv (cadr (cadr dt)))
                                      (jv (cadr (caddr dt))))
                                 (dk-have! (list 'AND (list '<= w iv) (list '<= w jv)))
                                 (dk-apply! inner iv jv)
                                 (ass)))))))
        (dk-conj-close! (lambda () (ass)))))))
(define r12d-idx-pt (car (dk-asms)))
(ew r12d-idx-lam)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (if (and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
         (begin
           (dk-lam-t!)
           (let ((z (dk-di-var!)))
             (dk-split! (dk-deepest (lambda () (inst+ r12d-idx-pt z))))
             (ass)))
         (let ((z (dk-di-var!)))
           (lam-b)
           (dk-peel!)
           (let* ((parts (dk-split! (dk-deepest (lambda () (inst+ r12d-idx-pt z)))))
                  (pr (or (find-first (dk-head? 'FORALL) parts)
                          (error "r12d: no property conjunct")))
                  (gg (dk-goal))
                  (dt (cadr gg))
                  (iv (cadr (cadr dt)))
                  (jv (cadr (caddr dt))))
             (dk-apply! pr iv jv)
             (ass)))))))
(qed 'r12d-rapid-indices)
(topic! 'r12d-rapid-indices 'analysis)
(alias! 'r12d-rapid-indices
        "a sequence of Cauchy sequences has a sequence of Cauchy thresholds")

;;; =====================================================================
;;; S3.  r12d-key -- THE KEY ESTIMATE.
;;;
;;; d-hat([f_p],[f_q]) is the LIMIT of n |-> d(f_p(n), f_q(n)) (r7q-dist-value),
;;; so by B1 that bound reads back onto the tail: past any prescribed index b
;;; there is an n with d(f_p(n), f_q(n)) <= d-hat + c.  Everything else in the
;;; diagonal argument is three triangle inequalities around this one n.
;;; =====================================================================

;;; the limit LV of a CONVERGES-TO in RR-MS, as a REAL.  `mac-h' is destructive,
;;; so the typing is read out inside a `dk-have!' LANE and the CONVERGES-TO
;;; itself survives for the citations below.
(define (r12d-limit-in-rr! conv)
  (dk-have! (list 'IN (cadddr conv) '(PTS RR-MS))
    (lambda ()
      (dk-split-all! (dk-landed* (lambda () (mac-h 'CONVERGES-TO conv))))
      (ass)))
  (dk-have! (list 'IN (cadddr conv) 'RR) (lambda () (mac 'r7q-rr-pts) (ass))))

;;; the limit of DIST-SEQ(M,FA,FB), with (= d-hat([FA],[FB]) L) beside it.
(define (r12d-dhat-limit! fa fb)
  (fact 'r7q-dist-seq-converges 'M fa fb)
  (let* ((cv (list 'CONVERGES 'RR-MS (list 'DIST-SEQ 'M fa fb)))
         (ex (dk-landed-1 (lambda () (mac-h 'CONVERGES cv))))
         (lv (dk-skolem! ex)))
    (r12d-limit-in-rr! (list 'CONVERGES-TO 'RR-MS (list 'DIST-SEQ 'M fa fb) lv))
    (fact 'r7q-dist-value 'M fa fb lv)
    lv))

(sp (make-wff (forall-guarded '(M) '((IS-METRIC-SPACE M))
  (forall-guarded '(bigF rf)
    '((IN bigF (FUN NN (QUOTIENT (CAUCHY-SETOID M)))) (IN rf (FUN NN (CSEQ M))))
    (list 'IMPLIES
      (forall-guarded '(p_) '((IN p_ NN))
                      '(= (bigF p_) (CLASS (CAUCHY-SETOID M) (rf p_))))
      (forall-guarded '(p_ q_ b_ c) '((IN p_ NN) (IN q_ NN) (IN b_ NN) (IN c RR))
        (list 'IMPLIES '(POS-RR c)
          (forsome-guarded '(n_) '((IN n_ NN))
            '(AND (<= b_ n_)
                  (<= ((DIST M) ((rf p_) n_) ((rf q_) n_))
                      (+ ((DIST (COMPLETION M)) (bigF p_) (bigF q_)) c)))))))))))
(dk-peel!)
(define r12d-k-cls
  (r12d-find "the class equation"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'CLASS)))))
(fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) 'p_)
(fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) 'q_)
(fact 'rko2-cseq-in-fun 'M '(rf p_))
(fact 'rko2-cseq-in-fun 'M '(rf q_))
(fact 'rko2-dist-seq-type 'M '(rf p_) '(rf q_))
(define r12d-k-lv (r12d-dhat-limit! '(rf p_) '(rf q_)))
(dk-apply! r12d-k-cls 'p_)
(dk-apply! r12d-k-cls 'q_)
(let* ((ex (dk-fact! 'rr-limit-tail-le '(DIST-SEQ M (rf p_) (rf q_)) r12d-k-lv 'c))
       (nt (dk-skolem! ex))
       (inner (r12d-find "the tail clause of B1"
                         (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                          (dk-contains? a nt)
                                          (dk-contains? a 'DIST-SEQ)))))
       (nv (list 'MAX 'b_ nt)))
  (fact 'nn-max-closed 'b_ nt)
  (fact 'nn-in-rr 'b_) (fact 'nn-in-rr nt) (fact 'nn-in-rr nv)
  (fact 'rr-le-max-left 'b_ nt)
  (fact 'rr-le-max-right 'b_ nt)
  (dk-apply! inner nv)
  (fact 'fun-apply-type-c '(rf p_) 'NN '(PTS M) nv)
  (fact 'fun-apply-type-c '(rf q_) 'NN '(PTS M) nv)
  (mac-h 'rko2-dist-seq-at
         (list '<= (list '(DIST-SEQ M (rf p_) (rf q_)) nv)
               (list '+ r12d-k-lv 'c)))
  (ew nv)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond ((eq? (car g) 'IN) (ass))
             ((equal? (cadr g) 'b_) (ass))
             (#t
              (subst '(= (bigF p_) (CLASS (CAUCHY-SETOID M) (rf p_))))
              (subst '(= (bigF q_) (CLASS (CAUCHY-SETOID M) (rf q_))))
              (subst (list '= '((DIST (COMPLETION M)) (CLASS (CAUCHY-SETOID M) (rf p_))
                                (CLASS (CAUCHY-SETOID M) (rf q_)))
                           r12d-k-lv))
              (ass)))))))
(qed 'r12d-key)
(topic! 'r12d-key 'analysis)
(alias! 'r12d-key
        "past any index, two representatives are within the completion distance plus any slack")

;;; =====================================================================
;;; S4.  THE DIAGONAL, and the curried tail of a null radius sequence.
;;; =====================================================================

(define r12d-diag '(VNB-LAMBDA pv_ NN ((rf pv_) (mm pv_))))

(sp (make-wff (forall-guarded '(rf mm p_) '((IN p_ NN))
                              (list '== (list r12d-diag 'p_) '((rf p_) (mm p_))))))
(dk-peel!)
(lam-b)
(qrfl)
(qed 'r12d-diag-at)
(topic! 'r12d-diag-at 'plumbing)

(sp (make-wff (forall-guarded '(M) '((IS-METRIC-SPACE M))
  (forall-guarded '(rf mm) '((IN rf (FUN NN (CSEQ M))) (IN mm (FUN NN NN)))
    (list 'IN r12d-diag '(FUN NN (PTS M)))))))
(dk-peel!)
(dk-lam-t!)
(let ((z (dk-di-var!)))
  (fact 'fun-apply-type-c 'mm 'NN 'NN z)
  (fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) z)
  (fact 'rko2-cseq-in-fun 'M (list 'rf z))
  (fact 'fun-apply-type-c (list 'rf z) 'NN '(PTS M) (list 'mm z))
  (ass))
(qed 'r12d-diag-in-fun)
(topic! 'r12d-diag-in-fun 'analysis)

;;; NULL-RR-SEQ's tail clause has a CONJUNCTIVE antecedent, which `fact' will
;;; not split; this is the curried form every use below wants.
(sp (make-wff (forall-guarded '(rad) '((NULL-RR-SEQ rad))
  (forall-guarded '(ev) '((POS-RR ev))
    (forsome-guarded '(nr_) '((IN nr_ NN))
      (forall-guarded '(k_) '((IN k_ NN)) '(IMPLIES (<= nr_ k_) (<= (rad k_) ev))))))))
(dk-peel!)
(dk-split! (dk-landed-find (lambda () (mac-h 'NULL-RR-SEQ '(NULL-RR-SEQ rad)))
                           (lambda (a) (and (pair? a) (eq? (car a) 'AND)))))
(let* ((tail (r12d-find "the eps-universal of NULL-RR-SEQ"
                        (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                         (dk-contains? a 'POS-RR)
                                         (dk-contains? a 'FORSOME)))))
       (ex (dk-apply! tail 'ev))
       (w  (dk-skolem! ex))
       (inner (r12d-find "the skolemized radius tail"
                         (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                          (dk-contains? a w)
                                          (not (dk-contains? a 'POS-RR)))))))
  (ew w)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IN)
         (ass)
         (begin
           (dk-peel!)
           (let ((kv (cadr (cadr (dk-goal)))))
             (dk-have! (list 'AND (list 'IN kv 'NN) (list '<= w kv)))
             (dk-apply! inner kv)
             (ass)))))))
(qed 'r12d-rad-tail)
(topic! 'r12d-rad-tail 'analysis)

;;; =====================================================================
;;; S5.  THE TWO TRIANGLE ESTIMATES.
;;;
;;;   r12d-diag-est    d(f_p(m_p), f_q(m_q)) <= rad(p) + rad(q) + d-hat + c
;;;   r12d-cross-est   d(f_q(m_q), f_p(q))   <= rad(q) + rad(p) + d-hat + c,
;;;                    when m_p <= q
;;;
;;; Both are r12d-key at n := MAX(m_p, m_q) with two threshold instances and
;;; two `metric-triangle' hops; the composition is one linear `ineq'.
;;; =====================================================================

(define (r12d-est-hyps concl)
  (forall-guarded '(M) '((IS-METRIC-SPACE M))
    (forall-guarded '(bigF rf rad mm)
      '((IN bigF (FUN NN (QUOTIENT (CAUCHY-SETOID M))))
        (IN rf (FUN NN (CSEQ M)))
        (IN rad (FUN NN RR))
        (IN mm (FUN NN NN)))
      (list 'IMPLIES
        (forall-guarded '(p_) '((IN p_ NN))
                        '(= (bigF p_) (CLASS (CAUCHY-SETOID M) (rf p_))))
        (list 'IMPLIES
          (forall-guarded '(p_) '((IN p_ NN))
            (forall-guarded '(i_ j_) '((IN i_ NN) (IN j_ NN))
              '(IMPLIES (<= (mm p_) i_)
                 (IMPLIES (<= (mm p_) j_)
                   (<= ((DIST M) ((rf p_) i_) ((rf p_) j_)) (rad p_))))))
          concl)))))

;;; the typings both estimates open with, at the two indices P and Q.
(define (r12d-est-types! pp qq)
  (fact 'fun-apply-type-c 'mm 'NN 'NN pp)
  (fact 'fun-apply-type-c 'mm 'NN 'NN qq)
  (fact 'nn-in-rr (list 'mm pp))
  (fact 'nn-in-rr (list 'mm qq))
  (fact 'nn-max-closed (list 'mm pp) (list 'mm qq))
  (fact 'nn-in-rr (list 'MAX (list 'mm pp) (list 'mm qq)))
  (fact 'rr-le-max-left (list 'mm pp) (list 'mm qq))
  (fact 'rr-le-max-right (list 'mm pp) (list 'mm qq))
  (fact 'rr-leq-reflexive (list 'mm pp))
  (fact 'rr-leq-reflexive (list 'mm qq))
  (fact 'fun-apply-type-c 'rad 'NN 'RR pp)
  (fact 'fun-apply-type-c 'rad 'NN 'RR qq)
  (fact 'fun-apply-type-c 'bigF 'NN '(QUOTIENT (CAUCHY-SETOID M)) pp)
  (fact 'fun-apply-type-c 'bigF 'NN '(QUOTIENT (CAUCHY-SETOID M)) qq)
  (fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) pp)
  (fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) qq)
  (fact 'rko2-cseq-in-fun 'M (list 'rf pp))
  (fact 'rko2-cseq-in-fun 'M (list 'rf qq)))

(define (r12d-dm a b) (list '(DIST M) a b))

(sp (make-wff (r12d-est-hyps
  (forall-guarded '(p_ q_ c) '((IN p_ NN) (IN q_ NN) (IN c RR))
    (list 'IMPLIES '(POS-RR c)
      (list '<= (r12d-dm '((rf p_) (mm p_)) '((rf q_) (mm q_)))
            (list '+ '(+ (rad p_) (rad q_))
                  (list '+ '((DIST (COMPLETION M)) (bigF p_) (bigF q_)) 'c))))))))
(dk-peel!)
(define r12d-e-thr
  (r12d-find "the threshold property"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a 'mm) (dk-contains? a 'rad)))))
(r12d-est-types! 'p_ 'q_)
(fact 'r7q-dhat-in-rr 'M '(bigF p_) '(bigF q_))
(fact 'fun-apply-type-c '(rf p_) 'NN '(PTS M) '(mm p_))
(fact 'fun-apply-type-c '(rf q_) 'NN '(PTS M) '(mm q_))
(let* ((bb '(MAX (mm p_) (mm q_)))
       (ex (dk-fact! 'r12d-key 'M 'bigF 'rf 'p_ 'q_ bb 'c))
       (nv (dk-skolem! ex)))
  (fact 'nn-in-rr nv)
  (dk-have! (list '<= '(mm p_) nv)
            (lambda () (dk-ineq! (list '<= '(mm p_) bb) (list '<= bb nv))))
  (dk-have! (list '<= '(mm q_) nv)
            (lambda () (dk-ineq! (list '<= '(mm q_) bb) (list '<= bb nv))))
  (dk-apply! r12d-e-thr 'p_ '(mm p_) nv)
  (dk-apply! r12d-e-thr 'q_ nv '(mm q_))
  (fact 'fun-apply-type-c '(rf p_) 'NN '(PTS M) nv)
  (fact 'fun-apply-type-c '(rf q_) 'NN '(PTS M) nv)
  (let ((fpm '((rf p_) (mm p_))) (fpn (list '(rf p_) nv))
        (fqm '((rf q_) (mm q_))) (fqn (list '(rf q_) nv)))
    (fact 'metric-dist-real 'M fpm fpn)
    (fact 'metric-dist-real 'M fpn fqn)
    (fact 'metric-dist-real 'M fqn fqm)
    (fact 'metric-dist-real 'M fpm fqm)
    (fact 'metric-dist-real 'M fpn fqm)
    (fact 'metric-triangle 'M fpm fpn fqm)
    (fact 'metric-triangle 'M fpn fqn fqm)
    (dk-ineq! (list '<= (r12d-dm fpm fqm)
                    (list '+ (r12d-dm fpm fpn) (r12d-dm fpn fqm)))
              (list '<= (r12d-dm fpn fqm)
                    (list '+ (r12d-dm fpn fqn) (r12d-dm fqn fqm)))
              (list '<= (r12d-dm fpm fpn) '(rad p_))
              (list '<= (r12d-dm fqn fqm) '(rad q_))
              (list '<= (r12d-dm fpn fqn)
                    (list '+ '((DIST (COMPLETION M)) (bigF p_) (bigF q_)) 'c)))))
(qed 'r12d-diag-est)
(topic! 'r12d-diag-est 'analysis)

(sp (make-wff (r12d-est-hyps
  (forall-guarded '(p_ q_ c) '((IN p_ NN) (IN q_ NN) (IN c RR))
    (list 'IMPLIES '(POS-RR c)
      (list 'IMPLIES '(<= (mm p_) q_)
        (list '<= (r12d-dm '((rf q_) (mm q_)) '((rf p_) q_))
              (list '+ '(+ (rad q_) (rad p_))
                    (list '+ '((DIST (COMPLETION M)) (bigF q_) (bigF p_)) 'c)))))))))
(dk-peel!)
(define r12d-x-thr
  (r12d-find "the threshold property"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a 'mm) (dk-contains? a 'rad)))))
(r12d-est-types! 'q_ 'p_)
(fact 'r7q-dhat-in-rr 'M '(bigF q_) '(bigF p_))
(fact 'fun-apply-type-c '(rf q_) 'NN '(PTS M) '(mm q_))
(fact 'fun-apply-type-c '(rf p_) 'NN '(PTS M) 'q_)
(let* ((bb '(MAX (mm q_) (mm p_)))
       (ex (dk-fact! 'r12d-key 'M 'bigF 'rf 'q_ 'p_ bb 'c))
       (nv (dk-skolem! ex)))
  (fact 'nn-in-rr nv)
  (dk-have! (list '<= '(mm q_) nv)
            (lambda () (dk-ineq! (list '<= '(mm q_) bb) (list '<= bb nv))))
  (dk-have! (list '<= '(mm p_) nv)
            (lambda () (dk-ineq! (list '<= '(mm p_) bb) (list '<= bb nv))))
  (dk-apply! r12d-x-thr 'q_ '(mm q_) nv)
  (dk-apply! r12d-x-thr 'p_ nv 'q_)
  (fact 'fun-apply-type-c '(rf q_) 'NN '(PTS M) nv)
  (fact 'fun-apply-type-c '(rf p_) 'NN '(PTS M) nv)
  (let ((fqm '((rf q_) (mm q_))) (fqn (list '(rf q_) nv))
        (fpn (list '(rf p_) nv)) (fpq '((rf p_) q_)))
    (fact 'metric-dist-real 'M fqm fqn)
    (fact 'metric-dist-real 'M fqn fpn)
    (fact 'metric-dist-real 'M fpn fpq)
    (fact 'metric-dist-real 'M fqm fpq)
    (fact 'metric-dist-real 'M fqn fpq)
    (fact 'metric-triangle 'M fqm fqn fpq)
    (fact 'metric-triangle 'M fqn fpn fpq)
    (dk-ineq! (list '<= (r12d-dm fqm fpq)
                    (list '+ (r12d-dm fqm fqn) (r12d-dm fqn fpq)))
              (list '<= (r12d-dm fqn fpq)
                    (list '+ (r12d-dm fqn fpn) (r12d-dm fpn fpq)))
              (list '<= (r12d-dm fqm fqn) '(rad q_))
              (list '<= (r12d-dm fpn fpq) '(rad p_))
              (list '<= (r12d-dm fqn fpn)
                    (list '+ '((DIST (COMPLETION M)) (bigF q_) (bigF p_)) 'c)))))
(qed 'r12d-cross-est)
(topic! 'r12d-cross-est 'analysis)

;;; =====================================================================
;;; S6.  THE DIAGONAL IS CAUCHY IN M.
;;;
;;; eps/4 four times over: rad(p), rad(q), d-hat(x_p, x_q) and the slack c of
;;; r12d-diag-est.  `dk-halve!' twice gives the quarter as e with e+e = d and
;;; d+d = eps, and `ineq' composes the two equations with the four bounds.
;;; =====================================================================

(define (r12d-full-hyps concl)
  (forall-guarded '(M) '((IS-METRIC-SPACE M))
    (forall-guarded '(bigF rf rad mm)
      '((IN bigF (FUN NN (QUOTIENT (CAUCHY-SETOID M))))
        (IN rf (FUN NN (CSEQ M)))
        (NULL-RR-SEQ rad)
        (IN mm (FUN NN NN)))
      (list 'IMPLIES
        (forall-guarded '(p_) '((IN p_ NN))
                        '(= (bigF p_) (CLASS (CAUCHY-SETOID M) (rf p_))))
        (list 'IMPLIES
          (forall-guarded '(p_) '((IN p_ NN))
            (forall-guarded '(i_ j_) '((IN i_ NN) (IN j_ NN))
              '(IMPLIES (<= (mm p_) i_)
                 (IMPLIES (<= (mm p_) j_)
                   (<= ((DIST M) ((rf p_) i_) ((rf p_) j_)) (rad p_))))))
          (list 'IMPLIES '(IS-CAUCHY-SEQ (COMPLETION M) bigF) concl))))))

;;; (IN ((rf IV) (mm IV)) (PTS M)) -- the diagonal's value at IV, typed.
(define (r12d-diag-type! iv)
  (fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) iv)
  (fact 'rko2-cseq-in-fun 'M (list 'rf iv))
  (fact 'fun-apply-type-c 'mm 'NN 'NN iv)
  (fact 'fun-apply-type-c (list 'rf iv) 'NN '(PTS M) (list 'mm iv)))

;;; the standing forward facts of S6 / S7, in one place.  RETURNS the curried
;;; radius tail: NULL-RR-SEQ's OWN eps-universal is in the context too and has
;;; the same head and the same free symbols, so it is never looked up by shape.
(define (r12d-open-hyps!)
  (let ((rt (dk-fact! 'r12d-rad-tail 'rad)))
    (dk-split! (dk-landed-find (lambda () (mac-h 'NULL-RR-SEQ '(NULL-RR-SEQ rad)))
                               (lambda (a) (and (pair? a) (eq? (car a) 'AND)))))
    (dk-split! (dk-landed-find
                (lambda () (mac-h 'IS-CAUCHY-SEQ '(IS-CAUCHY-SEQ (COMPLETION M) bigF)))
                (lambda (a) (and (pair? a) (eq? (car a) 'AND)))))
    rt))

(define (r12d-ft)
  (r12d-find "the eps-universal of bigF's Cauchy clause"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a 'POS-RR) (dk-contains? a 'bigF)))))
(define (r12d-in-rad n1)
  (r12d-find "the skolemized radius tail"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a n1) (dk-contains? a 'rad)
                              (not (dk-contains? a 'POS-RR))))))
(define (r12d-in-dh n2)
  (r12d-find "the skolemized d-hat tail"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (dk-contains? a n2) (dk-contains? a 'bigF)
                              (not (dk-contains? a 'POS-RR))))))

(sp (make-wff (r12d-full-hyps (list 'IS-CAUCHY-SEQ 'M r12d-diag))))
(dk-peel!)
(define r12d-c-rt (r12d-open-hyps!))
(fact 'r12d-diag-in-fun 'M 'rf 'mm)
(mac 'IS-CAUCHY-SEQ)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (if (not (eq? (car g) 'FORALL))
         (ass)
         (begin
           (di) (di)
           (fact 'rr-pos-rr-in-rr 'eps)
           (let* ((dd (dk-halve! 'eps))
                  (ee (dk-halve! dd))
                  (ex1 (dk-apply! r12d-c-rt ee))
                  (n1  (dk-skolem! ex1))
                  (in1 (r12d-in-rad n1))
                  (ex2 (dk-apply! (r12d-ft) ee))
                  (n2  (dk-skolem! ex2))
                  (in2 (r12d-in-dh n2))
                  (bnd (list 'MAX n1 n2)))
             (fact 'nn-max-closed n1 n2)
             (fact 'nn-in-rr n1) (fact 'nn-in-rr n2) (fact 'nn-in-rr bnd)
             (fact 'rr-le-max-left n1 n2)
             (fact 'rr-le-max-right n1 n2)
             (ew bnd)
             (dk-conj-close!
              (lambda ()
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (begin
                      (dk-peel!)
                      (dk-split-all!)
                      (let* ((gg (dk-goal))
                             (dt (cadr gg))
                             (mv (cadr (cadr dt)))
                             (nv (cadr (caddr dt))))
                        (fact 'nn-in-rr mv) (fact 'nn-in-rr nv)
                        (for-each
                         (lambda (iv)
                           (dk-have! (list '<= n1 iv)
                             (lambda () (dk-ineq! (list '<= n1 bnd) (list '<= bnd iv))))
                           (dk-have! (list '<= n2 iv)
                             (lambda () (dk-ineq! (list '<= n2 bnd) (list '<= bnd iv))))
                           (dk-apply! in1 iv)
                           (fact 'fun-apply-type-c 'rad 'NN 'RR iv)
                           (fact 'fun-apply-type-c 'bigF 'NN
                                 '(QUOTIENT (CAUCHY-SETOID M)) iv)
                           (r12d-diag-type! iv))
                         (list mv nv))
                        (dk-have! (list 'AND (list '<= n2 mv) (list '<= n2 nv)))
                        (dk-apply! in2 mv nv)
                        (fact 'r7q-dhat-in-rr 'M (list 'bigF mv) (list 'bigF nv))
                        (fact 'r12d-diag-est 'M 'bigF 'rf 'rad 'mm mv nv ee)
                        (fact 'r12d-diag-at 'rf 'mm mv)
                        (fact 'r12d-diag-at 'rf 'mm nv)
                        (subst (list '== (list r12d-diag mv)
                                     (list (list 'rf mv) (list 'mm mv))))
                        (subst (list '== (list r12d-diag nv)
                                     (list (list 'rf nv) (list 'mm nv))))
                        (fact 'metric-dist-real 'M
                              (list (list 'rf mv) (list 'mm mv))
                              (list (list 'rf nv) (list 'mm nv)))
                        (dk-ineq!
                         (list '<= (r12d-dm (list (list 'rf mv) (list 'mm mv))
                                            (list (list 'rf nv) (list 'mm nv)))
                               (list '+ (list '+ (list 'rad mv) (list 'rad nv))
                                     (list '+ (list '(DIST (COMPLETION M))
                                                    (list 'bigF mv) (list 'bigF nv))
                                           ee)))
                         (list '<= (list 'rad mv) ee)
                         (list '<= (list 'rad nv) ee)
                         (list '<= (list '(DIST (COMPLETION M))
                                         (list 'bigF mv) (list 'bigF nv)) ee)
                         (list '= (list '+ ee ee) dd)
                         (list '= (list '+ dd dd) 'eps)))))))))))))
(qed 'r12d-diag-cauchy)
(topic! 'r12d-diag-cauchy 'analysis)
(alias! 'r12d-diag-cauchy "the diagonal of a Cauchy sequence of classes is Cauchy")

;;; =====================================================================
;;; S7.  THE CLASS OF THE DIAGONAL IS THE LIMIT.
;;;
;;; d-hat([D], x_p) is the LIMIT of q |-> d(D(q), f_p(q)) (r7q-dist-value), and
;;; r12d-cross-est bounds that by rad(q) + rad(p) + d-hat(x_q,x_p) + c on the
;;; tail q >= MAX(bnd, m_p); B2 reads the bound back onto the limit.  The
;;; completion's metric is then flipped by r7q-dhat-sym, because CONVERGES-TO's
;;; clause is about d(f(n), L) and the estimate is about d(L, f(n)).
;;; =====================================================================

(sp (make-wff (r12d-full-hyps (list 'IN r12d-diag '(CSEQ M)))))
(dk-peel!)
(fact 'r12d-diag-in-fun 'M 'rf 'mm)
(fact 'r12d-diag-cauchy 'M 'bigF 'rf 'rad 'mm)
(mac 'CSEQ)
(in-sep! (lambda () (ass)) (lambda () (ass)))
(qed 'r12d-diag-in-cseq)
(topic! 'r12d-diag-in-cseq 'analysis)

(define r12d-cls-diag (list 'CLASS '(CAUCHY-SETOID M) r12d-diag))

(sp (make-wff (r12d-full-hyps
   (list 'CONVERGES-TO '(COMPLETION M) 'bigF r12d-cls-diag))))
(dk-peel!)
(define r12d-l-cls
  (r12d-find "the class equation"
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'CLASS)))))
;; EVERYTHING that consumes NULL-RR-SEQ(rad) or IS-CAUCHY-SEQ(COMPLETION M, bigF)
;; as a whole hypothesis must be cited BEFORE `r12d-open-hyps!' unfolds them:
;; `mac-h' REPLACES the formula it opens, and a later `fact' that needs it then
;; lands the implication silently.
(fact 'completion-is-metric-space 'M)
(fact 'cauchy-setoid-is-setoid 'M)
(fact 'r12d-diag-in-fun 'M 'rf 'mm)
(fact 'r12d-diag-in-cseq 'M 'bigF 'rf 'rad 'mm)
(dk-have! (list 'IN r12d-diag '(PTS (CAUCHY-SETOID M)))
          (lambda () (mac 'rkt-cauchy-setoid-pts) (ass)))
(fact 'class-in-quotient '(CAUCHY-SETOID M) r12d-diag)
(define r12d-l-rt (r12d-open-hyps!))
(mac 'CONVERGES-TO)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'IS-METRIC-SPACE) (ass))
       ((and (eq? (car g) 'IN) (eq? (cadr g) 'bigF)) (ass))
       ((eq? (car g) 'IN) (mac 'rkt-completion-pts) (ass))
       (#t
        (di) (di)
        (fact 'rr-pos-rr-in-rr 'eps)
        (let* ((dd (dk-halve! 'eps))
               (ee (dk-halve! dd))
               (ex1 (dk-apply! r12d-l-rt ee))
               (n1  (dk-skolem! ex1))
               (in1 (r12d-in-rad n1))
               (ex2 (dk-apply! (r12d-ft) ee))
               (n2  (dk-skolem! ex2))
               (in2 (r12d-in-dh n2))
               (bnd (list 'MAX n1 n2)))
          (fact 'nn-max-closed n1 n2)
          (fact 'nn-in-rr n1) (fact 'nn-in-rr n2) (fact 'nn-in-rr bnd)
          (fact 'rr-le-max-left n1 n2)
          (fact 'rr-le-max-right n1 n2)
          (ew bnd)
          (dk-conj-close!
           (lambda ()
             (if (eq? (car (dk-goal)) 'IN)
                 (ass)
                 (begin
                   (dk-peel!)
                   (let* ((pv (cadr (cadr (cadr (dk-goal))))))
                     (fact 'nn-in-rr pv)
                     (dk-have! (list '<= n1 pv)
                       (lambda () (dk-ineq! (list '<= n1 bnd) (list '<= bnd pv))))
                     (dk-have! (list '<= n2 pv)
                       (lambda () (dk-ineq! (list '<= n2 bnd) (list '<= bnd pv))))
                     (dk-apply! in1 pv)
                     (fact 'fun-apply-type-c 'rad 'NN 'RR pv)
                     (fact 'fun-apply-type-c 'rf 'NN '(CSEQ M) pv)
                     (fact 'rko2-cseq-in-fun 'M (list 'rf pv))
                     (fact 'fun-apply-type-c 'mm 'NN 'NN pv)
                     (fact 'nn-in-rr (list 'mm pv))
                     (fact 'fun-apply-type-c 'bigF 'NN
                           '(QUOTIENT (CAUCHY-SETOID M)) pv)
                     (dk-apply! r12d-l-cls pv)
                     (fact 'rko2-dist-seq-type 'M r12d-diag (list 'rf pv))
                     (let* ((lv (r12d-dhat-limit! r12d-diag (list 'rf pv)))
                            (dsq (list 'DIST-SEQ 'M r12d-diag (list 'rf pv)))
                            (nt (list 'MAX bnd (list 'mm pv))))
                       (fact 'nn-max-closed bnd (list 'mm pv))
                       (fact 'nn-in-rr nt)
                       (fact 'rr-le-max-left bnd (list 'mm pv))
                       (fact 'rr-le-max-right bnd (list 'mm pv))
                       (dk-have!
                        (forall-guarded '(k_) '((IN k_ NN))
                          (list 'IMPLIES (list '<= nt 'k_)
                                (list '<= (list dsq 'k_) 'eps)))
                        (lambda ()
                          (dk-peel!)
                          (let ((kv (cadr (cadr (dk-goal)))))
                            (fact 'nn-in-rr kv)
                            (dk-have! (list '<= bnd kv)
                              (lambda () (dk-ineq! (list '<= bnd nt) (list '<= nt kv))))
                            (dk-have! (list '<= (list 'mm pv) kv)
                              (lambda () (dk-ineq! (list '<= (list 'mm pv) nt)
                                                   (list '<= nt kv))))
                            (dk-have! (list '<= n1 kv)
                              (lambda () (dk-ineq! (list '<= n1 bnd) (list '<= bnd kv))))
                            (dk-have! (list '<= n2 kv)
                              (lambda () (dk-ineq! (list '<= n2 bnd) (list '<= bnd kv))))
                            (dk-apply! in1 kv)
                            (dk-have! (list 'AND (list '<= n2 kv) (list '<= n2 pv)))
                            (dk-apply! in2 kv pv)
                            (fact 'fun-apply-type-c 'rad 'NN 'RR kv)
                            (fact 'fun-apply-type-c 'bigF 'NN
                                  '(QUOTIENT (CAUCHY-SETOID M)) kv)
                            (fact 'r7q-dhat-in-rr 'M (list 'bigF kv) (list 'bigF pv))
                            (r12d-diag-type! kv)
                            (fact 'fun-apply-type-c (list 'rf pv) 'NN '(PTS M) kv)
                            (fact 'r12d-cross-est 'M 'bigF 'rf 'rad 'mm pv kv ee)
                            (fact 'rko2-dist-seq-at 'M r12d-diag (list 'rf pv) kv)
                            (subst (list '== (list dsq kv)
                                         (list '(DIST M) (list r12d-diag kv)
                                               (list (list 'rf pv) kv))))
                            (fact 'r12d-diag-at 'rf 'mm kv)
                            (subst (list '== (list r12d-diag kv)
                                         (list (list 'rf kv) (list 'mm kv))))
                            (fact 'metric-dist-real 'M
                                  (list (list 'rf kv) (list 'mm kv))
                                  (list (list 'rf pv) kv))
                            (dk-ineq!
                             (list '<= (r12d-dm (list (list 'rf kv) (list 'mm kv))
                                                (list (list 'rf pv) kv))
                                   (list '+ (list '+ (list 'rad kv) (list 'rad pv))
                                         (list '+ (list '(DIST (COMPLETION M))
                                                        (list 'bigF kv) (list 'bigF pv))
                                               ee)))
                             (list '<= (list 'rad kv) ee)
                             (list '<= (list 'rad pv) ee)
                             (list '<= (list '(DIST (COMPLETION M))
                                             (list 'bigF kv) (list 'bigF pv)) ee)
                             (list '= (list '+ ee ee) dd)
                             (list '= (list '+ dd dd) 'eps)))))
                       (fact 'rr-limit-le-of-tail dsq lv 'eps nt)
                       (fact 'r7q-dhat-sym 'M (list 'bigF pv) r12d-cls-diag)
                       (subst (list '= (list '(DIST (COMPLETION M))
                                             (list 'bigF pv) r12d-cls-diag)
                                    (list '(DIST (COMPLETION M))
                                          r12d-cls-diag (list 'bigF pv))))
                       (subst (list '= (list 'bigF pv)
                                    (list 'CLASS '(CAUCHY-SETOID M) (list 'rf pv))))
                       (subst (list '= (list '(DIST (COMPLETION M)) r12d-cls-diag
                                             (list 'CLASS '(CAUCHY-SETOID M)
                                                   (list 'rf pv)))
                                    lv))
                       (ass)))))))))))))
(qed 'r12d-diag-limit)
(topic! 'r12d-diag-limit 'analysis)
(alias! 'r12d-diag-limit
        "the class of the diagonal is the limit of the sequence of classes")

;;; =====================================================================
;;; S8.  THE LEAF: completion-is-complete.
;;;
;;; The statement is the support's, copied from structure-library/
;;; metric-completion.scm:110 and unchanged.
;;; =====================================================================

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IS-COMPLETE (COMPLETION M))))))
(di) (di)
(fact 'completion-is-metric-space 'M)
(mac 'IS-COMPLETE)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (car (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let* ((cy (dk-pick (dk-head? 'IS-CAUCHY-SEQ) "the Cauchy hypothesis"))
                (fv (caddr cy)))
           (fact 'rkt-completion-pts 'M)
           ;; the carrier of the completion IS the quotient; `mac-h' of the
           ;; Cauchy hypothesis happens on a LANE, so the hypothesis itself
           ;; survives for r12d-diag-limit below.
           (dk-have! (list 'IN fv '(FUN NN (QUOTIENT (CAUCHY-SETOID M))))
             (lambda ()
               (dk-split! (dk-landed-find
                           (lambda () (mac-h 'IS-CAUCHY-SEQ cy))
                           (lambda (a) (and (pair? a) (eq? (car a) 'AND)))))
               (subst '(== (QUOTIENT (CAUCHY-SETOID M)) (PTS (COMPLETION M))))
               (ass)))
           (let* ((ex1  (dk-fact! 'r12d-repfam 'M fv))
                  (rfv  (dk-skolem! ex1))
                  (ex2  (dk-fact! 'null-rr-seq-exists))
                  (radv (dk-skolem! ex2)))
             (dk-have! (list 'IN radv '(FUN NN RR))
               (lambda ()
                 (dk-split-all! (dk-landed* (lambda () (mac-h 'NULL-RR-SEQ
                                                              (list 'NULL-RR-SEQ radv)))))
                 (ass)))
             (dk-have! (forall-guarded '(p_) '((IN p_ NN))
                                       (list 'POS-RR (list radv 'p_)))
               (lambda ()
                 (dk-split-all! (dk-landed* (lambda () (mac-h 'NULL-RR-SEQ
                                                              (list 'NULL-RR-SEQ radv)))))
                 (ass)))
             (let* ((ex3 (dk-fact! 'r12d-rapid-indices 'M rfv radv))
                    (mmv (dk-skolem! ex3))
                    (dg  (list 'VNB-LAMBDA 'pv_ 'NN
                               (list (list rfv 'pv_) (list mmv 'pv_)))))
               (fact 'r12d-diag-limit 'M fv rfv radv mmv)
               (mac 'CONVERGES)
               (ew (list 'CLASS '(CAUCHY-SETOID M) dg))
               (ass))))))))
(qed 'completion-is-complete)
(topic! 'completion-is-complete 'constructions)
