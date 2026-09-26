;;; ms-continuity-algebra.scm -- THE CONTINUITY ALGEBRA OFF THE REAL LINE.
;;;
;;; The algebra of theorem-library/continuity-{basics,sum,product,transfer,
;;; compose}.scm and cont-agree-off-pt.scm is stated for RR-MS only.  Batch
;;; 12-G stopped at exactly that: IS-DIFF-ON is defined over a normed field K,
;;; its factor phi is continuous as a map SUBSPACE-MS(NF-METRIC-SPACE K, U) ->
;;; NF-METRIC-SPACE(K), and not one line of the real algebra can be cited about
;;; it.  This file proves the algebra where it belongs:
;;;
;;;   (A) for ARBITRARY metric spaces, everything that needs no arithmetic on
;;;       the VALUES -- the constant and identity maps, the transfer along
;;;       pointwise equality, composition, and "two maps continuous at a limit
;;;       point and agreeing off it agree at it";
;;;   (B) over a NORMED FIELD K, with the codomain NF-METRIC-SPACE(K) and an
;;;       arbitrary metric space as domain -- the pointwise sum, product and
;;;       negation.
;;;
;;; THE DOMAIN IS AN ARBITRARY METRIC SPACE `mss_', NOT a subspace.  The
;;; consumer (theorem-library/diff-on-laws-2.scm) instantiates it at
;;; SUBSPACE-MS(NF-METRIC-SPACE K, U) and rewrites PTS of that to U by
;;; `subspace-pts'; stating the laws on the subspace directly would have fixed
;;; the shape of the domain for no gain and would not have covered RR-MS.
;;;
;;; WHY THE MAPS ARE VNB-LAMBDAS AND COMPOSITION IS NOT `COMPOSE'.  A member of
;;; FUN(A,B) is defined exactly on A, so the pointwise combinations are built as
;;; lambdas over PTS(mss_), exactly as the RR algebra builds them over RR; and
;;; the composite is written as the lambda x |-> g(f(x)) rather than
;;; COMPOSE(g,f), because that is the shape the Caratheodory chain rule needs
;;; (its factor is x |-> phi_g(f(x)) . phi_f(x), a single lambda) and because it
;;; spares the two COMPOSE laws and the (A in SET) guard `compose-type' carries.
;;; `compose-continuous-at' (theorem-library/continuity-compose.scm) is the
;;; COMPOSE form on RR and is untouched.
;;;
;;; NO TRIVIAL-NORM AND NO EMPTY-SET HAZARD.  Nothing here asks the domain to be
;;; inhabited: every statement is guarded on a point `msa_' of PTS(mss_), so on
;;; an empty space each is vacuous.  Nothing here asks the norm to be
;;; non-trivial either -- that hypothesis belongs to UNIQUENESS of the
;;; derivative, not to continuity, and it appears first in diff-on-laws-2.scm.
;;; Every equation between values is guarded by the typing of both sides.
;;;
;;; Helper prefix: msc-.
;;;
;;; Dependencies: metric-continuity.scm (IS-CONTINUOUS-AT), metric-space.scm,
;;; metric-laws.scm (metric-self-zero, metric-sym, metric-pos, metric-zero-eq,
;;; metric-triangle), op-typing.scm (metric-dist-real), normed-field.scm,
;;; normed-field-metric.scm (nf-metric-carrier, nf-metric-distance),
;;; rake-nf-norm.scm, theorem-library/diff-on-laws.scm (the nf-norm toolkit:
;;; nf-norm-in-rr, nf-norm-nonneg, nf-norm-mult, nf-norm-subadd,
;;; nf-add-in-carr, nf-mul-in-carr, nf-neg-in-carr, nf-norm-le-add,
;;; normed-field-ring-view-*), rr-order-basics (rr-min-pos, rr-prod-le-prod,
;;; rr-le-add, rr-le-all-pos-nonpos, rr-leq-transitive, rr-leq-antisymmetric),
;;; rr-halving (rr-pos-halvable), rr-scale-eps.
;;; Load slot: immediately after theorem-library/diff-on-laws.

;;; ---- file-local driver helpers --------------------------------------

(define (msc-head e) (and (pair? e) (car e)))

;;; The eps just peeled, off the POS-RR guard `di' landed.
(define (msc-eps)
  (cadr (dk-pick (dk-head? 'POS-RR) "POS-RR eps")))

;;; An eps-universal of an UNFOLDED IS-CONTINUOUS-AT hypothesis, discriminated
;;; by a term that occurs in it and in no sibling (never by its head).
;;;
;;; DIST IS PART OF THE TEST, not decoration.  Without it the product proof
;;; below picks `rr-scale-eps' instead: that theorem is also a FORALL over a
;;; POS-RR guard with a FORSOME body, and the instance in context is taken at
;;; c = ||g(a)|| + ||h(a)|| + 1, so it CONTAINS both msg_ and msh_ and passes
;;; every other test.  Three eigenvariables came back that were the scale
;;; lemma's radii and not the maps' deltas, and the failure surfaced two steps
;;; later as "dk-pick: nothing matching a delta universal".
(define (msc-eps-univ . marks)
  (dk-pick (lambda (fm)
             (and (pair? fm) (eq? (car fm) 'FORALL)
                  (dk-contains? fm 'POS-RR) (dk-contains? fm 'FORSOME)
                  (dk-contains? fm 'DIST)
                  (let loop ((m marks))
                    (cond ((null? m) #t)
                          ((dk-contains? fm (car m)) (loop (cdr m)))
                          (#t #f)))))
           "an eps universal"))

;;; The delta-universal that `dk-skolem!' of an eps-universal's witness landed:
;;; the one mentioning that delta and a DIST, and no POS-RR.
(define (msc-delta-univ d . marks)
  (dk-pick (lambda (fm)
             (and (pair? fm) (eq? (car fm) 'FORALL)
                  (dk-contains? fm 'DIST) (dk-contains? fm d)
                  (not (dk-contains? fm 'POS-RR))
                  (let loop ((m marks))
                    (cond ((null? m) #t)
                          ((dk-contains? fm (car m)) (loop (cdr m)))
                          (#t #f)))))
           "a delta universal"))

;;; POS-RR t  ->  (IN t RR) and (< 0 t), by CITATION (mac-h would consume the
;;; POS-RR, which the eps-universals still detach against).
(define (msc-pos! t)
  (fact 'rr-pos-rr-in-rr t)
  (fact 'rr-lt-of-pos-rr t))

;;; The FUN typing of a lambda: the pointwise leaf is closed by BODY (run with
;;; the peeled point in context), the sethood leaf by `ms-pts-is-set'.
(define (msc-lam-fun! space body)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (msc-head (dk-goal)) 'FORALL)
         (let ((z (dk-di-var!))) (body z) (ass))
         (begin (fact 'ms-pts-is-set space) (ass))))
   (dk-opened (lambda () (lam-t)))))

;;; =====================================================================
;;; (0) THE POINTS OF A METRIC SPACE FORM A SET.
;;;
;;; A conjunct of the IS-METRIC-SPACE iff, surfaced as its own theorem: it is
;;; the SETHOOD leaf `lam-t' opens for every lambda built over PTS(s) below,
;;; and the unfold that produces it is destructive.
;;; =====================================================================
(sp (make-wff '(FORALL mss_ (IMPLIES (IS-METRIC-SPACE mss_) (IN (PTS mss_) SET)))))
(dk-peel!)
(mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE mss_))
(dk-split-all!)
(ass)
(qed 'ms-pts-is-set)
(topic! 'ms-pts-is-set 'topology)
(alias! 'ms-pts-is-set "the points of a metric space form a set")

;;; =====================================================================
;;; (1) THE CONSTANT MAP.
;;; =====================================================================

(sp (make-wff '(FORALL mss_ (IMPLIES (IS-METRIC-SPACE mss_)
     (FORALL mst_ (FORALL msc_ (IMPLIES (IN msc_ (PTS mst_))
       (IN (VNB-LAMBDA msz_ (PTS mss_) msc_) (FUN (PTS mss_) (PTS mst_))))))))))
(dk-peel!)
(msc-lam-fun! 'mss_ (lambda (z) #t))
(qed 'ms-const-lam-in-fun)
(topic! 'ms-const-lam-in-fun 'topology)
(alias! 'ms-const-lam-in-fun "a constant map is a function between the point sets")

;;; Any positive delta serves: d(c,c) = 0 <= eps.
(sp (make-wff '(FORALL mss_ (IMPLIES (IS-METRIC-SPACE mss_)
     (FORALL mst_ (IMPLIES (IS-METRIC-SPACE mst_)
       (FORALL msc_ (IMPLIES (IN msc_ (PTS mst_))
         (FORALL msa_ (IMPLIES (IN msa_ (PTS mss_))
           (IS-CONTINUOUS-AT mss_ mst_ (VNB-LAMBDA msz_ (PTS mss_) msc_) msa_)))))))))))
(dk-peel!)
(fact 'ms-const-lam-in-fun 'mss_ 'mst_ 'msc_)
(fact 'metric-self-zero 'mst_ 'msc_)
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (msc-head (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let ((eps (msc-eps)))
           (msc-pos! eps)
           (dk-have! '(POS-RR 1)
             (lambda () (dk-have! '(< 0 1) (lambda () (ineq)))
                        (fact 'rr-pos-rr-of-lt 1) (ass)))
           (ew 1)
           (dk-conj-close!
            (lambda ()
              (if (eq? (msc-head (dk-goal)) 'POS-RR)
                  (ass)
                  (begin
                    (dk-peel!)
                    (dk-lam-b!)
                    (subst (list '= (list '(DIST mst_) 'msc_ 'msc_) 0))
                    (dk-ineq! (list '< 0 eps) (list 'IN eps 'RR)))))))))))
(qed 'ms-const-continuous-at)
(topic! 'ms-const-continuous-at 'analysis)
(alias! 'ms-const-continuous-at "a constant map is continuous at every point")

;;; =====================================================================
;;; (2) THE IDENTITY MAP.  delta = eps, and after the beta the goal IS the
;;; hypothesis.
;;; =====================================================================

(sp (make-wff '(FORALL mss_ (IMPLIES (IS-METRIC-SPACE mss_)
     (IN (VNB-LAMBDA msz_ (PTS mss_) msz_) (FUN (PTS mss_) (PTS mss_)))))))
(dk-peel!)
(msc-lam-fun! 'mss_ (lambda (z) #t))
(qed 'ms-ident-lam-in-fun)
(topic! 'ms-ident-lam-in-fun 'topology)
(alias! 'ms-ident-lam-in-fun "the identity is a function on the point set")

(sp (make-wff '(FORALL mss_ (IMPLIES (IS-METRIC-SPACE mss_)
     (FORALL msa_ (IMPLIES (IN msa_ (PTS mss_))
       (IS-CONTINUOUS-AT mss_ mss_ (VNB-LAMBDA msz_ (PTS mss_) msz_) msa_)))))))
(dk-peel!)
(fact 'ms-ident-lam-in-fun 'mss_)
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (msc-head (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let ((eps (msc-eps)))
           (ew eps)
           (dk-conj-close!
            (lambda ()
              (if (eq? (msc-head (dk-goal)) 'POS-RR)
                  (ass)
                  (begin (dk-peel!) (dk-lam-b!) (ass))))))))))
(qed 'ms-identity-continuous-at)
(topic! 'ms-identity-continuous-at 'analysis)
(alias! 'ms-identity-continuous-at "the identity map is continuous at every point")

;;; =====================================================================
;;; (3) TRANSFER ALONG POINTWISE EQUALITY.  The generic twin of
;;; `cont-transfer-ptwise-eq' (theorem-library/continuity-transfer.scm).  It is
;;; the mechanism by which every law below is USED: the algebra produces a
;;; lambda, and the phi a proof actually holds is some other function equal to
;;; it pointwise.  The SAME delta serves; there is no arithmetic.
;;; =====================================================================
(sp (make-wff '(FORALL mss_ (FORALL mst_ (FORALL msg_ (FORALL msf_ (FORALL msa_
     (IMPLIES (IS-CONTINUOUS-AT mss_ mst_ msg_ msa_)
       (IMPLIES (IN msf_ (FUN (PTS mss_) (PTS mst_)))
         (IMPLIES (FORALL msz_ (IMPLIES (IN msz_ (PTS mss_))
                    (= (msf_ msz_) (msg_ msz_))))
           (IS-CONTINUOUS-AT mss_ mst_ msf_ msa_)))))))))))
(define msc-tr-landed (dk-peel!))
(define msc-tr-agree
  (dk-pick (lambda (fm) (and (member fm msc-tr-landed) (eq? (msc-head fm) 'FORALL)
                             (dk-contains? fm 'msf_)))
           "the pointwise-equality universal"))
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT mss_ mst_ msg_ msa_))
(dk-split-all!)
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (msc-head (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let* ((eps (msc-eps))
                (del (dk-skolem! (dk-apply! (msc-eps-univ 'msg_) eps))))
           (ew del)
           (dk-conj-close!
            (lambda ()
              (if (eq? (msc-head (dk-goal)) 'POS-RR)
                  (ass)
                  (let ((b (dk-di-var!)))
                    (dk-peel!)
                    (dk-apply! msc-tr-agree 'msa_)
                    (dk-apply! msc-tr-agree b)
                    (subst (list '= (list 'msf_ 'msa_) (list 'msg_ 'msa_)))
                    (subst (list '= (list 'msf_ b) (list 'msg_ b)))
                    (dk-apply! (msc-delta-univ del) b)
                    (ass))))))))))
(qed 'ms-cont-transfer-ptwise-eq)
(topic! 'ms-cont-transfer-ptwise-eq 'analysis)
(alias! 'ms-cont-transfer-ptwise-eq
        "continuity transfers along pointwise equality")

;;; =====================================================================
;;; (4) COMPOSITION, as the lambda x |-> g(f(x)).  One nesting of deltas: take
;;; g's delta at f(a) for eps, then f's delta at a for that.
;;; =====================================================================
(sp (make-wff '(FORALL mss_ (FORALL mst_ (FORALL msu_ (FORALL msf_ (FORALL msg_
     (FORALL msa_
       (IMPLIES (IS-CONTINUOUS-AT mss_ mst_ msf_ msa_)
         (IMPLIES (IS-CONTINUOUS-AT mst_ msu_ msg_ (msf_ msa_))
           (IS-CONTINUOUS-AT mss_ msu_
             (VNB-LAMBDA msz_ (PTS mss_) (msg_ (msf_ msz_))) msa_)))))))))))
(dk-peel!)
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT mss_ mst_ msf_ msa_))
(dk-split-all!)
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT mst_ msu_ msg_ (msf_ msa_)))
(dk-split-all!)
(dk-have! '(IN (VNB-LAMBDA msz_ (PTS mss_) (msg_ (msf_ msz_)))
               (FUN (PTS mss_) (PTS msu_)))
  (lambda ()
    (msc-lam-fun! 'mss_
      (lambda (z)
        (fact 'fun-apply-type-c 'msf_ '(PTS mss_) '(PTS mst_) z)
        (fact 'fun-apply-type-c 'msg_ '(PTS mst_) '(PTS msu_) (list 'msf_ z))))))
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (msc-head (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let* ((eps (msc-eps))
                (d1  (dk-skolem! (dk-apply! (msc-eps-univ 'msg_) eps))))
           (msc-pos! d1)
           (let ((d2 (dk-skolem! (dk-apply! (msc-eps-univ 'msf_ 'mss_) d1))))
             (ew d2)
             (dk-conj-close!
              (lambda ()
                (if (eq? (msc-head (dk-goal)) 'POS-RR)
                    (ass)
                    (let ((b (dk-di-var!)))
                      (dk-peel!)
                      (dk-lam-b!)
                      (fact 'fun-apply-type-c 'msf_ '(PTS mss_) '(PTS mst_) b)
                      (dk-apply! (msc-delta-univ d2 'mss_) b)
                      (dk-apply! (msc-delta-univ d1 'msg_) (list 'msf_ b))
                      (ass)))))))))))
(qed 'ms-compose-continuous-at)
(topic! 'ms-compose-continuous-at 'analysis)
(alias! 'ms-compose-continuous-at
        "the composite of two maps continuous at matching points is continuous")

;;; =====================================================================
;;; (5) TWO MAPS CONTINUOUS AT A LIMIT POINT AND AGREEING OFF IT AGREE AT IT.
;;;
;;; The generic twin of `cont-agree-off-pt' (theorem-library/cont-agree-off-pt
;;; .scm), whose RR proof samples at pt + w and so cannot leave the line.  Here
;;; the sample point is supplied by an EXPLICIT LIMIT-POINT HYPOTHESIS:
;;;
;;;   for every r > 0 there is b in PTS(s) with b /= p and d(p, b) <= r.
;;;
;;; That hypothesis is exactly what the statement needs and no more -- on the
;;; real line it is a theorem, on a discrete space it is false and so is the
;;; conclusion, and the tree has no LIMIT-POINT predicate to hide it behind.
;;; `diff-on-laws-2.scm' discharges it for an open subset of a normed field
;;; whose norm has arbitrarily small nonzero elements.
;;;
;;; THE ESTIMATE is ONE triangle inequality, not the three terms of the RR
;;; proof: d(f p, g p) <= d(f p, f b) + d(f b, g p), and the second term IS
;;; d(g b, g p) because f and g agree at b.  Both are at most eps/2.  True of
;;; every positive eps, so `rr-le-all-pos-nonpos' and the metric's own
;;; positivity make the distance 0, and `metric-zero-eq' finishes.
;;; =====================================================================

(define msc-ag-d '((DIST mst_) (msf_ msp_) (msg_ msp_)))

(sp (make-wff '(FORALL mss_ (FORALL mst_ (FORALL msf_ (FORALL msg_ (FORALL msp_
     (IMPLIES (IS-CONTINUOUS-AT mss_ mst_ msf_ msp_)
       (IMPLIES (IS-CONTINUOUS-AT mss_ mst_ msg_ msp_)
         (IMPLIES (FORALL msr_ (IMPLIES (POS-RR msr_)
                    (FORSOME msb_ (AND (IN msb_ (PTS mss_))
                                  (AND (NOT (= msb_ msp_))
                                       (<= ((DIST mss_) msp_ msb_) msr_))))))
           (IMPLIES (FORALL msy_ (IMPLIES (IN msy_ (PTS mss_))
                      (IMPLIES (NOT (= msy_ msp_)) (= (msf_ msy_) (msg_ msy_)))))
             (= (msf_ msp_) (msg_ msp_)))))))))))))
(define msc-ag-landed (dk-peel!))
(define msc-ag-lim
  (dk-pick (lambda (fm) (and (member fm msc-ag-landed) (eq? (msc-head fm) 'FORALL)
                             (dk-contains? fm 'FORSOME)))
           "the limit-point hypothesis"))
(define msc-ag-agree
  (dk-pick (lambda (fm) (and (member fm msc-ag-landed) (eq? (msc-head fm) 'FORALL)
                             (dk-contains? fm 'msf_)))
           "the agreement hypothesis"))
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT mss_ mst_ msf_ msp_))
(dk-split-all!)
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT mss_ mst_ msg_ msp_))
(dk-split-all!)
(fact 'fun-apply-type-c 'msf_ '(PTS mss_) '(PTS mst_) 'msp_)
(fact 'fun-apply-type-c 'msg_ '(PTS mss_) '(PTS mst_) 'msp_)
(fact 'metric-dist-real 'mst_ '(msf_ msp_) '(msg_ msp_))
(fact 'rr-zero-in)

(dk-have! (list 'FORALL 'mse_ (list 'IMPLIES '(POS-RR mse_) (list '<= msc-ag-d 'mse_)))
  (lambda ()
    (let* ((peeled (dk-peel!))
           (eps (cadr (dk-pick (lambda (fm) (and (member fm peeled)
                                                 (eq? (msc-head fm) 'POS-RR)))
                               "POS-RR eps")))
           (hf  (dk-skolem! (dk-fact! 'rr-pos-halvable eps)))
           (d1  (dk-skolem! (dk-apply! (msc-eps-univ 'msf_) hf)))
           (d2  (dk-skolem! (dk-apply! (msc-eps-univ 'msg_) hf))))
      (msc-pos! eps)
      (msc-pos! hf)
      (msc-pos! d1)
      (msc-pos! d2)
      (let ((w (dk-skolem! (dk-fact! 'rr-min-pos d1 d2))))
        (fact 'rr-pos-rr-of-lt w)
        (let ((b (dk-skolem! (dk-apply! msc-ag-lim w))))
          (fact 'metric-dist-real 'mss_ 'msp_ b)
          (for-each
           (lambda (dd)
             (dk-have! (list '<= (list '(DIST mss_) 'msp_ b) dd)
               (lambda ()
                 (dk-ineq! (list '<= (list '(DIST mss_) 'msp_ b) w)
                           (list '<= w dd)
                           (list 'IN (list '(DIST mss_) 'msp_ b) 'RR)
                           (list 'IN w 'RR) (list 'IN dd 'RR)))))
           (list d1 d2))
          (dk-apply! (msc-delta-univ d1 'msf_) b)
          (dk-apply! (msc-delta-univ d2 'msg_) b)
          (dk-apply! msc-ag-agree b)
          (fact 'fun-apply-type-c 'msf_ '(PTS mss_) '(PTS mst_) b)
          (fact 'fun-apply-type-c 'msg_ '(PTS mss_) '(PTS mst_) b)
          (fact 'metric-dist-real 'mst_ '(msf_ msp_) (list 'msf_ b))
          (fact 'metric-dist-real 'mst_ (list 'msf_ b) '(msg_ msp_))
          (fact 'metric-sym 'mst_ (list 'msg_ b) '(msg_ msp_))
          (dk-have! (list '<= (list '(DIST mst_) (list 'msf_ b) '(msg_ msp_)) hf)
            (lambda ()
              (subst (list '= (list 'msf_ b) (list 'msg_ b)))
              (subst (list '= (list '(DIST mst_) (list 'msg_ b) '(msg_ msp_))
                              (list '(DIST mst_) '(msg_ msp_) (list 'msg_ b))))
              (ass)))
          (fact 'metric-triangle 'mst_ '(msf_ msp_) (list 'msf_ b) '(msg_ msp_))
          (dk-ineq! (list '<= msc-ag-d
                          (list '+ (list '(DIST mst_) '(msf_ msp_) (list 'msf_ b))
                                   (list '(DIST mst_) (list 'msf_ b) '(msg_ msp_))))
                    (list '<= (list '(DIST mst_) '(msf_ msp_) (list 'msf_ b)) hf)
                    (list '<= (list '(DIST mst_) (list 'msf_ b) '(msg_ msp_)) hf)
                    (list '= (list '+ hf hf) eps)
                    (list 'IN msc-ag-d 'RR)
                    (list 'IN (list '(DIST mst_) '(msf_ msp_) (list 'msf_ b)) 'RR)
                    (list 'IN (list '(DIST mst_) (list 'msf_ b) '(msg_ msp_)) 'RR)
                    (list 'IN hf 'RR) (list 'IN eps 'RR)))))))

(let ((r (dk-fact! 'rr-le-all-pos-nonpos msc-ag-d)))
  (if (eq? (msc-head r) 'IMPLIES) (detach! r)))
(fact 'metric-pos 'mst_ '(msf_ msp_) '(msg_ msp_))
(have! (list 'AND (list 'IN msc-ag-d 'RR) '(IN 0 RR)))
(have! (list 'AND (list '<= msc-ag-d 0) (list '<= 0 msc-ag-d)))
(fact 'rr-leq-antisymmetric msc-ag-d 0)
(fact 'metric-zero-eq 'mst_ '(msf_ msp_) '(msg_ msp_))
(ass)
(qed 'ms-cont-agree-off-pt)
(topic! 'ms-cont-agree-off-pt 'analysis)
(alias! 'ms-cont-agree-off-pt
        "maps continuous at a limit point and agreeing off it agree at it")

;;; =====================================================================
;;; PART (B).  THE NORMED FIELD.
;;;
;;; The codomain is NF-METRIC-SPACE(K) and the domain is still an arbitrary
;;; metric space.  Two ring identities of K, three norm estimates built on
;;; them, and then the pointwise sum, negation and product.
;;;
;;; THE IDENTITIES GO THROUGH THE VIEW.  `crs' decides commutative-ring
;;; identities and reaches (ADD R) / (MUL R) / (NEG R) once IS-COMMUTATIVE-RING
;;; of that structure is in context; a NORMED-FIELD is a 7-tuple and the ring
;;; predicates pin length 6, so the structure `crs' is handed is
;;; NORMED-FIELD-AS-COMMUTATIVE-RING(K) and the three slot read-offs move the
;;; goal onto it.  This is `nf-sub-add-back' (theorem-library/diff-on-laws.scm)
;;; with more operations.
;;; =====================================================================

(define msc-view '(NORMED-FIELD-AS-COMMUTATIVE-RING K))
(define (msc-add a b) (list '(ADD K) a b))
(define (msc-mul a b) (list '(MUL K) a b))
(define (msc-neg a)   (list '(NEG K) a))
(define (msc-sub a b) (msc-add a (msc-neg b)))
(define (msc-nrm a)   (list '(FNRM K) a))

(define (msc-occurs? sub e)
  (cond ((equal? sub e) #t)
        ((pair? e) (or (msc-occurs? sub (car e)) (msc-occurs? sub (cdr e))))
        (#t #f)))

;;; `subst' only where the goal actually holds the left-hand side: a rewrite
;;; that changes nothing prints "nothing changed" and leaves an inert step.
(define (msc-subst-if! eq)
  (if (msc-occurs? (cadr eq) (dk-goal)) (subst eq)))

;;; A ring identity of K on the typed ARGS, by `crs' through the view.
(define (msc-ring-id! args)
  (fact 'normed-field-as-commutative-ring-is-commutative-ring 'K)
  (fact 'commutative-ring-is-ring msc-view)
  (fact 'normed-field-ring-view-carr 'K)
  (fact 'normed-field-ring-view-add 'K)
  (fact 'normed-field-ring-view-mul 'K)
  (fact 'normed-field-ring-view-neg 'K)
  (for-each (lambda (u)
              (dk-have! (list 'IN u (list 'CARR msc-view))
                (lambda () (subst (list '== (list 'CARR msc-view) '(CARR K))) (ass))))
            args)
  (msc-subst-if! (list '== '(ADD K) (list 'ADD msc-view)))
  (msc-subst-if! (list '== '(MUL K) (list 'MUL msc-view)))
  (msc-subst-if! (list '== '(NEG K) (list 'NEG msc-view)))
  (crs))

(define (msc-nf-thm! name concl body)
  (sp (make-wff (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K) concl))))
  (dk-peel!)
  (body)
  (if (not (proof-done? *ps*))
      (error "msc-nf-thm!: proof did not close" name (dk-goal)))
  (qed name))

;;; the four carrier guards used over and over
(define (msc-carr-guards vs) (map (lambda (v) (list 'IN v '(CARR K))) vs))

;;; ---- (B.1) the two ring identities ----------------------------------

(msc-nf-thm! 'nf-sub-split
  (forall-guarded '(nfu_ nfv_ nfp_ nfq_) (msc-carr-guards '(nfu_ nfv_ nfp_ nfq_))
    (list '= (msc-sub (msc-add 'nfu_ 'nfv_) (msc-add 'nfp_ 'nfq_))
             (msc-add (msc-sub 'nfu_ 'nfp_) (msc-sub 'nfv_ 'nfq_))))
  (lambda () (msc-ring-id! '(nfu_ nfv_ nfp_ nfq_))))
(topic! 'nf-sub-split 'algebra)
(alias! 'nf-sub-split "a difference of sums splits into the sum of the differences")

(msc-nf-thm! 'nf-mul-sub-split
  (forall-guarded '(nfu_ nfv_ nfp_ nfq_) (msc-carr-guards '(nfu_ nfv_ nfp_ nfq_))
    (list '= (msc-sub (msc-mul 'nfu_ 'nfv_) (msc-mul 'nfp_ 'nfq_))
             (msc-add (msc-mul 'nfu_ (msc-sub 'nfv_ 'nfq_))
                      (msc-mul 'nfq_ (msc-sub 'nfu_ 'nfp_)))))
  (lambda () (msc-ring-id! '(nfu_ nfv_ nfp_ nfq_))))
(topic! 'nf-mul-sub-split 'algebra)
(alias! 'nf-mul-sub-split "the standard splitting of a difference of products")

(msc-nf-thm! 'nf-neg-sub-split
  (forall-guarded '(nfu_ nfv_) (msc-carr-guards '(nfu_ nfv_))
    (list '= (msc-sub (msc-neg 'nfu_) (msc-neg 'nfv_))
             (msc-neg (msc-sub 'nfu_ 'nfv_))))
  (lambda () (msc-ring-id! '(nfu_ nfv_))))
(topic! 'nf-neg-sub-split 'algebra)

(msc-nf-thm! 'nf-sub-anti
  (forall-guarded '(nfu_ nfv_) (msc-carr-guards '(nfu_ nfv_))
    (list '= (msc-neg (msc-sub 'nfu_ 'nfv_)) (msc-sub 'nfv_ 'nfu_)))
  (lambda () (msc-ring-id! '(nfu_ nfv_))))
(topic! 'nf-sub-anti 'algebra)

;;; ---- (B.2) the norm estimates ---------------------------------------

;;; u - v is in the carrier: the pair of closures, used at every step below.
(define (msc-sub-in-carr! u v)
  (fact 'nf-neg-in-carr 'K v)
  (fact 'nf-add-in-carr 'K u (msc-neg v)))

(msc-nf-thm! 'nf-norm-sub-sym
  (forall-guarded '(nfu_ nfv_) (msc-carr-guards '(nfu_ nfv_))
    (list '= (msc-nrm (msc-sub 'nfu_ 'nfv_)) (msc-nrm (msc-sub 'nfv_ 'nfu_))))
  (lambda ()
    (msc-sub-in-carr! 'nfu_ 'nfv_)
    (fact 'nf-sub-anti 'K 'nfu_ 'nfv_)
    (fact 'nf-norm-neg 'K (msc-sub 'nfu_ 'nfv_))
    (subst (list '= (msc-sub 'nfv_ 'nfu_) (msc-neg (msc-sub 'nfu_ 'nfv_))))
    (subst (list '= (msc-nrm (msc-neg (msc-sub 'nfu_ 'nfv_)))
                    (msc-nrm (msc-sub 'nfu_ 'nfv_))))
    (rfl)))
(topic! 'nf-norm-sub-sym 'algebra)
(alias! 'nf-norm-sub-sym "the norm of a difference is symmetric")

(msc-nf-thm! 'nf-norm-neg-diff
  (forall-guarded '(nfu_ nfv_) (msc-carr-guards '(nfu_ nfv_))
    (list '= (msc-nrm (msc-sub (msc-neg 'nfu_) (msc-neg 'nfv_)))
             (msc-nrm (msc-sub 'nfu_ 'nfv_))))
  (lambda ()
    (msc-sub-in-carr! 'nfu_ 'nfv_)
    (fact 'nf-neg-sub-split 'K 'nfu_ 'nfv_)
    (fact 'nf-norm-neg 'K (msc-sub 'nfu_ 'nfv_))
    (subst (list '= (msc-sub (msc-neg 'nfu_) (msc-neg 'nfv_))
                    (msc-neg (msc-sub 'nfu_ 'nfv_))))
    (subst (list '= (msc-nrm (msc-neg (msc-sub 'nfu_ 'nfv_)))
                    (msc-nrm (msc-sub 'nfu_ 'nfv_))))
    (rfl)))
(topic! 'nf-norm-neg-diff 'algebra)
(alias! 'nf-norm-neg-diff "negation preserves the norm of a difference")

(msc-nf-thm! 'nf-norm-sum-diff
  (forall-guarded '(nfu_ nfv_ nfp_ nfq_) (msc-carr-guards '(nfu_ nfv_ nfp_ nfq_))
    (list '<= (msc-nrm (msc-sub (msc-add 'nfu_ 'nfv_) (msc-add 'nfp_ 'nfq_)))
              (list '+ (msc-nrm (msc-sub 'nfu_ 'nfp_))
                       (msc-nrm (msc-sub 'nfv_ 'nfq_)))))
  (lambda ()
    (msc-sub-in-carr! 'nfu_ 'nfp_)
    (msc-sub-in-carr! 'nfv_ 'nfq_)
    (fact 'nf-sub-split 'K 'nfu_ 'nfv_ 'nfp_ 'nfq_)
    (fact 'nf-norm-subadd 'K (msc-sub 'nfu_ 'nfp_) (msc-sub 'nfv_ 'nfq_))
    (subst (list '= (msc-sub (msc-add 'nfu_ 'nfv_) (msc-add 'nfp_ 'nfq_))
                    (msc-add (msc-sub 'nfu_ 'nfp_) (msc-sub 'nfv_ 'nfq_))))
    (ass)))
(topic! 'nf-norm-sum-diff 'algebra)
(alias! 'nf-norm-sum-diff
        "the norm of a difference of sums is at most the sum of the norms")

;;; The product estimate, the normed-field twin of `rr-abs-prod-bound'
;;; (theorem-library/rr-abs-basics.scm) and stated in its shape: BOUNDS ON TWO
;;; OF THE FOUR VALUES -- ||u|| and ||q|| -- and one radius t for both
;;; differences.  The chain is by CITATION, not by `ineq': every rung is a
;;; product of two non-constant terms and the oracle drops such a premise
;;; silently (CLAUDE.md, 2026-09-19).
(msc-nf-thm! 'nf-norm-prod-bound
  (forall-guarded '(nfu_ nfv_ nfp_ nfq_ nfm_ nfk_ nft_ nfe_)
    (append (msc-carr-guards '(nfu_ nfv_ nfp_ nfq_))
            '((IN nfm_ RR) (IN nfk_ RR) (IN nft_ RR) (IN nfe_ RR)))
    (list 'IMPLIES (list '<= (msc-nrm 'nfu_) 'nfm_)
     (list 'IMPLIES (list '<= (msc-nrm 'nfq_) 'nfk_)
      (list 'IMPLIES (list '<= (msc-nrm (msc-sub 'nfu_ 'nfp_)) 'nft_)
       (list 'IMPLIES (list '<= (msc-nrm (msc-sub 'nfv_ 'nfq_)) 'nft_)
        (list 'IMPLIES (list '<= (list '* (list '+ 'nfm_ 'nfk_) 'nft_) 'nfe_)
          (list '<= (msc-nrm (msc-sub (msc-mul 'nfu_ 'nfv_) (msc-mul 'nfp_ 'nfq_)))
                    'nfe_)))))))
  (lambda ()
    (let* ((dup (msc-sub 'nfu_ 'nfp_))         ; u - p
           (dvq (msc-sub 'nfv_ 'nfq_))         ; v - q
           (a1  (msc-mul 'nfu_ dvq))           ; u.(v-q)
           (a2  (msc-mul 'nfq_ dup))           ; q.(u-p)
           (n1  (list '* (msc-nrm 'nfu_) (msc-nrm dvq)))
           (n2  (list '* (msc-nrm 'nfq_) (msc-nrm dup)))
           (lhsn  (msc-nrm (msc-sub (msc-mul 'nfu_ 'nfv_) (msc-mul 'nfp_ 'nfq_))))
           (bnd1  (list '+ n1 n2))
           (bnd2  (list '+ (list '* 'nfm_ 'nft_) (list '* 'nfk_ 'nft_)))
           (bnd3  (list '* (list '+ 'nfm_ 'nfk_) 'nft_)))
      (msc-sub-in-carr! 'nfu_ 'nfp_)
      (msc-sub-in-carr! 'nfv_ 'nfq_)
      (fact 'nf-mul-in-carr 'K 'nfu_ dvq)
      (fact 'nf-mul-in-carr 'K 'nfq_ dup)
      (fact 'nf-mul-in-carr 'K 'nfu_ 'nfv_)
      (fact 'nf-mul-in-carr 'K 'nfp_ 'nfq_)
      (msc-sub-in-carr! (msc-mul 'nfu_ 'nfv_) (msc-mul 'nfp_ 'nfq_))
      (fact 'nf-norm-in-rr 'K 'nfu_)
      (fact 'nf-norm-in-rr 'K 'nfq_)
      (fact 'nf-norm-in-rr 'K dup)
      (fact 'nf-norm-in-rr 'K dvq)
      (fact 'nf-norm-nonneg 'K 'nfu_)
      (fact 'nf-norm-nonneg 'K 'nfq_)
      (fact 'nf-norm-nonneg 'K dup)
      (fact 'nf-norm-nonneg 'K dvq)
      (fact 'nf-mul-sub-split 'K 'nfu_ 'nfv_ 'nfp_ 'nfq_)
      (fact 'nf-norm-subadd 'K a1 a2)
      (fact 'nf-norm-mult 'K 'nfu_ dvq)
      (fact 'nf-norm-mult 'K 'nfq_ dup)
      ;; ||u.v - p.q||  <=  ||u||.||v-q|| + ||q||.||u-p||
      (dk-have! (list '<= lhsn bnd1)
        (lambda ()
          (subst (list '= (msc-sub (msc-mul 'nfu_ 'nfv_) (msc-mul 'nfp_ 'nfq_))
                          (msc-add a1 a2)))
          (subst (list '= n1 (msc-nrm a1)))
          (subst (list '= n2 (msc-nrm a2)))
          (ass)))
      ;; each factor pair, by rr-prod-le-prod
      (dk-have! (list '<= n1 (list '* 'nfm_ 'nft_))
        (lambda ()
          (dk-have! (list 'AND (list 'AND (list '<= 0 (msc-nrm 'nfu_))
                                           (list '<= (msc-nrm 'nfu_) 'nfm_))
                               (list 'AND (list '<= 0 (msc-nrm dvq))
                                           (list '<= (msc-nrm dvq) 'nft_))))
          (fact 'rr-prod-le-prod (msc-nrm 'nfu_) 'nfm_ (msc-nrm dvq) 'nft_)
          (ass)))
      (dk-have! (list '<= n2 (list '* 'nfk_ 'nft_))
        (lambda ()
          (dk-have! (list 'AND (list 'AND (list '<= 0 (msc-nrm 'nfq_))
                                           (list '<= (msc-nrm 'nfq_) 'nfk_))
                               (list 'AND (list '<= 0 (msc-nrm dup))
                                           (list '<= (msc-nrm dup) 'nft_))))
          (fact 'rr-prod-le-prod (msc-nrm 'nfq_) 'nfk_ (msc-nrm dup) 'nft_)
          (ass)))
      (dk-le-add! n1 (list '* 'nfm_ 'nft_) n2 (list '* 'nfk_ 'nft_))
      (dk-have! (list '= bnd2 bnd3) (lambda () (crs)))
      (fact 'nf-norm-in-rr 'K (msc-sub (msc-mul 'nfu_ 'nfv_) (msc-mul 'nfp_ 'nfq_)))
      (dk-le-chain! lhsn bnd1 bnd2 bnd3 'nfe_))))
(topic! 'nf-norm-prod-bound 'algebra)
(alias! 'nf-norm-prod-bound "the product estimate for a field norm")

;;; =====================================================================
;;; (B.3) THE POINTWISE SUM, NEGATION AND PRODUCT ARE CONTINUOUS.
;;;
;;; The codomain is M = NF-METRIC-SPACE(K) throughout; `nf-metric-carrier'
;;; (PTS(M) == CARR(K), unconditional) moves a typing between the two
;;; spellings, and `nf-metric-distance' turns every distance into a norm.  The
;;; estimates are then (B.2) and nothing else.
;;; =====================================================================

(define msc-M '(NF-METRIC-SPACE K))
(define (msc-dM x y) (list (list 'DIST msc-M) x y))

;;; fn(Z) in CARR(K), from the FUN typing into PTS(M).
(define (msc-val-in-carr! fn z)
  (fact 'fun-apply-type-c fn '(PTS mss_) (list 'PTS msc-M) z)
  (dk-have! (list 'IN (list fn z) '(CARR K))
    (lambda () (subst (list '== '(CARR K) (list 'PTS msc-M))) (ass))))

;;; d_M(X, Y) <= R  from  ||X - Y|| <= R, and back: both directions are one
;;; `nf-metric-distance' rewrite, landed on a `have!' lane.
(define (msc-norm-le! x y r)
  (fact 'nf-metric-distance 'K x y)
  (dk-have! (list '<= (msc-nrm (msc-sub x y)) r)
    (lambda () (subst (list '= (msc-nrm (msc-sub x y)) (msc-dM x y))) (ass))))

;;; The FUN typing of a lambda built from msg_ (and msh_) by OP.
(define (msc-nf-lam-thm! name lam binary? body)
  (sp (make-wff
       (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
         (list 'FORALL 'mss_ (list 'IMPLIES '(IS-METRIC-SPACE mss_)
           (list 'FORALL 'msg_
             (list 'IMPLIES (list 'IN 'msg_ (list 'FUN '(PTS mss_) (list 'PTS msc-M)))
               (if binary?
                   (list 'FORALL 'msh_
                     (list 'IMPLIES (list 'IN 'msh_ (list 'FUN '(PTS mss_)
                                                         (list 'PTS msc-M)))
                       (list 'IN lam (list 'FUN '(PTS mss_) (list 'PTS msc-M)))))
                   (list 'IN lam (list 'FUN '(PTS mss_) (list 'PTS msc-M)))))))))))) 
  (dk-peel!)
  (fact 'nf-metric-carrier 'K)
  (msc-lam-fun! 'mss_
    (lambda (z)
      (msc-val-in-carr! 'msg_ z)
      (if binary? (msc-val-in-carr! 'msh_ z))
      (body z)
      (subst (list '== (list 'PTS msc-M) '(CARR K)))))
  (if (not (proof-done? *ps*))
      (error "msc-nf-lam-thm!: proof did not close" name (dk-goal)))
  (qed name))

(define msc-sum-lam
  '(VNB-LAMBDA msz_ (PTS mss_) ((ADD K) (msg_ msz_) (msh_ msz_))))
(define msc-prod-lam
  '(VNB-LAMBDA msz_ (PTS mss_) ((MUL K) (msg_ msz_) (msh_ msz_))))
(define msc-neg-lam
  '(VNB-LAMBDA msz_ (PTS mss_) ((NEG K) (msg_ msz_))))

(msc-nf-lam-thm! 'nf-sum-lam-in-fun msc-sum-lam #t
  (lambda (z) (fact 'nf-add-in-carr 'K (list 'msg_ z) (list 'msh_ z))))
(topic! 'nf-sum-lam-in-fun 'analysis)

(msc-nf-lam-thm! 'nf-prod-lam-in-fun msc-prod-lam #t
  (lambda (z) (fact 'nf-mul-in-carr 'K (list 'msg_ z) (list 'msh_ z))))
(topic! 'nf-prod-lam-in-fun 'analysis)

(msc-nf-lam-thm! 'nf-neg-lam-in-fun msc-neg-lam #f
  (lambda (z) (fact 'nf-neg-in-carr 'K (list 'msg_ z))))
(topic! 'nf-neg-lam-in-fun 'analysis)

;;; The statement of a continuity law over K: two maps into M, continuous at
;;; msa_, and the lambda LAM continuous there.  BINARY? #f drops msh_.
(define (msc-nf-cont-stmt lam binary?)
  (list 'FORALL 'K (list 'IMPLIES '(IS-NORMED-FIELD K)
    (list 'FORALL 'mss_ (list 'FORALL 'msg_
      ((lambda (rest) (if binary? (list 'FORALL 'msh_ rest) rest))
       (list 'FORALL 'msa_
         (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ msc-M 'msg_ 'msa_)
           ((lambda (concl)
              (if binary?
                  (list 'IMPLIES (list 'IS-CONTINUOUS-AT 'mss_ msc-M 'msh_ 'msa_)
                        concl)
                  concl))
            (list 'IS-CONTINUOUS-AT 'mss_ msc-M lam 'msa_))))))))))

;;; ---- the sum ---------------------------------------------------------
(sp (make-wff (msc-nf-cont-stmt msc-sum-lam #t)))
(dk-peel!)
(fact 'nf-metric-carrier 'K)
(mac-h 'IS-CONTINUOUS-AT (list 'IS-CONTINUOUS-AT 'mss_ msc-M 'msg_ 'msa_))
(dk-split-all!)
(mac-h 'IS-CONTINUOUS-AT (list 'IS-CONTINUOUS-AT 'mss_ msc-M 'msh_ 'msa_))
(dk-split-all!)
(fact 'nf-sum-lam-in-fun 'K 'mss_ 'msg_ 'msh_)
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (msc-head (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let* ((eps (msc-eps))
                (hf  (dk-skolem! (dk-fact! 'rr-pos-halvable eps)))
                (d1  (dk-skolem! (dk-apply! (msc-eps-univ 'msg_) hf)))
                (d2  (dk-skolem! (dk-apply! (msc-eps-univ 'msh_) hf))))
           (msc-pos! eps) (msc-pos! hf) (msc-pos! d1) (msc-pos! d2)
           (let ((w (dk-skolem! (dk-fact! 'rr-min-pos d1 d2))))
             (fact 'rr-pos-rr-of-lt w)
             (ew w)
             (dk-conj-close!
              (lambda ()
                (if (eq? (msc-head (dk-goal)) 'POS-RR)
                    (ass)
                    (let ((b (dk-di-var!)))
                      (dk-peel!)
                      (dk-lam-b!)
                      (let* ((ga '(msg_ msa_)) (ha '(msh_ msa_))
                             (gb (list 'msg_ b)) (hb (list 'msh_ b))
                             (sa (msc-add ga ha)) (sb (msc-add gb hb))
                             (dab (list '(DIST mss_) 'msa_ b))
                             (n1 (msc-nrm (msc-sub ga gb)))
                             (n2 (msc-nrm (msc-sub ha hb)))
                             (lhsn (msc-nrm (msc-sub sa sb))))
                        (msc-val-in-carr! 'msg_ 'msa_)
                        (msc-val-in-carr! 'msh_ 'msa_)
                        (msc-val-in-carr! 'msg_ b)
                        (msc-val-in-carr! 'msh_ b)
                        (fact 'nf-add-in-carr 'K ga ha)
                        (fact 'nf-add-in-carr 'K gb hb)
                        (msc-sub-in-carr! ga gb)
                        (msc-sub-in-carr! ha hb)
                        (msc-sub-in-carr! sa sb)
                        (fact 'nf-norm-in-rr 'K (msc-sub ga gb))
                        (fact 'nf-norm-in-rr 'K (msc-sub ha hb))
                        (fact 'nf-norm-in-rr 'K (msc-sub sa sb))
                        (fact 'metric-dist-real 'mss_ 'msa_ b)
                        (for-each
                         (lambda (dd)
                           (dk-have! (list '<= dab dd)
                             (lambda ()
                               (dk-ineq! (list '<= dab w) (list '<= w dd)
                                         (list 'IN dab 'RR) (list 'IN w 'RR)
                                         (list 'IN dd 'RR)))))
                         (list d1 d2))
                        (dk-apply! (msc-delta-univ d1 'msg_) b)
                        (dk-apply! (msc-delta-univ d2 'msh_) b)
                        (msc-norm-le! ga gb hf)
                        (msc-norm-le! ha hb hf)
                        (fact 'nf-metric-distance 'K sa sb)
                        (subst (list '= (msc-dM sa sb) lhsn))
                        (fact 'nf-norm-sum-diff 'K ga ha gb hb)
                        (dk-le-add! n1 hf n2 hf)
                        (dk-le-chain! lhsn (list '+ n1 n2) (list '+ hf hf) eps)))))))))))) 
(qed 'nf-sum-continuous-at)
(topic! 'nf-sum-continuous-at 'analysis)
(alias! 'nf-sum-continuous-at
        "the pointwise sum of two maps continuous into a normed field is continuous")

;;; ---- the negation ----------------------------------------------------
(sp (make-wff (msc-nf-cont-stmt msc-neg-lam #f)))
(dk-peel!)
(fact 'nf-metric-carrier 'K)
(mac-h 'IS-CONTINUOUS-AT (list 'IS-CONTINUOUS-AT 'mss_ msc-M 'msg_ 'msa_))
(dk-split-all!)
(fact 'nf-neg-lam-in-fun 'K 'mss_ 'msg_)
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (msc-head (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let* ((eps (msc-eps))
                (d1  (dk-skolem! (dk-apply! (msc-eps-univ 'msg_) eps))))
           (ew d1)
           (dk-conj-close!
            (lambda ()
              (if (eq? (msc-head (dk-goal)) 'POS-RR)
                  (ass)
                  (let ((b (dk-di-var!)))
                    (dk-peel!)
                    (dk-lam-b!)
                    (let* ((ga '(msg_ msa_)) (gb (list 'msg_ b)))
                      (msc-val-in-carr! 'msg_ 'msa_)
                      (msc-val-in-carr! 'msg_ b)
                      (fact 'nf-neg-in-carr 'K ga)
                      (fact 'nf-neg-in-carr 'K gb)
                      (dk-apply! (msc-delta-univ d1 'msg_) b)
                      (fact 'nf-metric-distance 'K (msc-neg ga) (msc-neg gb))
                      (fact 'nf-norm-neg-diff 'K ga gb)
                      (fact 'nf-metric-distance 'K ga gb)
                      (subst (list '= (msc-dM (msc-neg ga) (msc-neg gb))
                                      (msc-nrm (msc-sub (msc-neg ga) (msc-neg gb)))))
                      (subst (list '= (msc-nrm (msc-sub (msc-neg ga) (msc-neg gb)))
                                      (msc-nrm (msc-sub ga gb))))
                      (subst (list '= (msc-nrm (msc-sub ga gb)) (msc-dM ga gb)))
                      (ass)))))))))))
(qed 'nf-neg-continuous-at)
(topic! 'nf-neg-continuous-at 'analysis)
(alias! 'nf-neg-continuous-at
        "the pointwise negation of a map continuous into a normed field is continuous")

;;; ---- the product -----------------------------------------------------
;;;
;;; The extra work over the sum is ONE preliminary delta, exactly as in
;;; theorem-library/continuity-product.scm: the estimate
;;; ||g(a)h(a) - g(b)h(b)|| <= ||g(a)||.||h(a)-h(b)|| + ||h(b)||.||g(a)-g(b)||
;;; bounds two of the four VALUES, and the second of them, ||h(b)||, is at the
;;; MOVING point -- bounded only inside h's own delta at eps' = 1, where
;;; ||h(b)|| <= ||h(a)|| + 1 by `nf-norm-le-add' and `nf-norm-sub-sym'.
;;;
;;; The radius is `rr-scale-eps' at C = ||g(a)|| + ||h(a)|| + 1 rather than a
;;; quotient eps * recip(C): `crs' declines anything containing `recip', and
;;; the scale lemma hands back the radius with the product estimate attached.
(sp (make-wff (msc-nf-cont-stmt msc-prod-lam #t)))
(dk-peel!)
(fact 'nf-metric-carrier 'K)
(mac-h 'IS-CONTINUOUS-AT (list 'IS-CONTINUOUS-AT 'mss_ msc-M 'msg_ 'msa_))
(dk-split-all!)
(mac-h 'IS-CONTINUOUS-AT (list 'IS-CONTINUOUS-AT 'mss_ msc-M 'msh_ 'msa_))
(dk-split-all!)
(fact 'nf-prod-lam-in-fun 'K 'mss_ 'msg_ 'msh_)
(define msc-pr-ga '(msg_ msa_))
(define msc-pr-ha '(msh_ msa_))
(define msc-pr-m (msc-nrm msc-pr-ga))
(define msc-pr-k (list '+ (msc-nrm msc-pr-ha) 1))
(define msc-pr-c (list '+ msc-pr-m msc-pr-k))
(msc-val-in-carr! 'msg_ 'msa_)
(msc-val-in-carr! 'msh_ 'msa_)
(fact 'nf-norm-in-rr 'K msc-pr-ga)
(fact 'nf-norm-in-rr 'K msc-pr-ha)
(fact 'nf-norm-nonneg 'K msc-pr-ga)
(fact 'nf-norm-nonneg 'K msc-pr-ha)
(fact 'rr-one-in)
(fact 'rr-zero-in)
(fact 'rr-add-in-rr (msc-nrm msc-pr-ha) 1)
(fact 'rr-add-in-rr msc-pr-m msc-pr-k)
(dk-have! (list '<= 0 msc-pr-c)
  (lambda () (dk-ineq! (list '<= 0 msc-pr-m) (list '<= 0 (msc-nrm msc-pr-ha))
                       (list 'IN msc-pr-m 'RR) (list 'IN (msc-nrm msc-pr-ha) 'RR))))
(fact 'rr-leq-reflexive msc-pr-m)
(mac 'IS-CONTINUOUS-AT)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (msc-head (dk-goal)) 'FORALL))
       (ass)
       (begin
         (dk-peel!)
         (let ((eps (msc-eps)))
           (msc-pos! eps)
           (dk-have! '(POS-RR 1)
             (lambda () (dk-have! '(< 0 1) (lambda () (ineq)))
                        (fact 'rr-pos-rr-of-lt 1) (ass)))
           (let* ((d0  (dk-skolem! (dk-fact! 'rr-scale-eps msc-pr-c eps)))
                  (dh1 (dk-skolem! (dk-apply! (msc-eps-univ 'msh_) 1))))
             (msc-pos! d0)
             (fact 'rr-lt-implies-le 0 d0)
             (fact 'rr-leq-reflexive d0)
             (dk-apply! (dk-pick (lambda (fm)
                                   (and (pair? fm) (eq? (car fm) 'FORALL)
                                        (dk-contains? fm d0)
                                        (dk-contains? fm msc-pr-c)))
                                 "the rr-scale-eps universal")
                        d0)
             (let* ((dg (dk-skolem! (dk-apply! (msc-eps-univ 'msg_) d0)))
                    (dh (dk-skolem! (dk-apply! (msc-eps-univ 'msh_) d0))))
               (msc-pos! dh1) (msc-pos! dg) (msc-pos! dh)
               (let* ((m1 (dk-skolem! (dk-fact! 'rr-min-pos dh1 dg)))
                      (w  (begin (msc-pos! m1)
                                 (dk-skolem! (dk-fact! 'rr-min-pos m1 dh)))))
                 (fact 'rr-pos-rr-of-lt w)
                 (msc-pos! w)
                 (ew w)
                 (dk-conj-close!
                  (lambda ()
                    (if (eq? (msc-head (dk-goal)) 'POS-RR)
                        (ass)
                        (let ((b (dk-di-var!)))
                          (dk-peel!)
                          (dk-lam-b!)
                          (let* ((ga msc-pr-ga) (ha msc-pr-ha)
                                 (gb (list 'msg_ b)) (hb (list 'msh_ b))
                                 (dab (list '(DIST mss_) 'msa_ b)))
                            (msc-val-in-carr! 'msg_ b)
                            (msc-val-in-carr! 'msh_ b)
                            (msc-sub-in-carr! ga gb)
                            (msc-sub-in-carr! ha hb)
                            (msc-sub-in-carr! hb ha)
                            (fact 'nf-mul-in-carr 'K ga ha)
                            (fact 'nf-mul-in-carr 'K gb hb)
                            (fact 'nf-norm-in-rr 'K hb)
                            (fact 'nf-norm-in-rr 'K (msc-sub ga gb))
                            (fact 'nf-norm-in-rr 'K (msc-sub ha hb))
                            (fact 'nf-norm-in-rr 'K (msc-sub hb ha))
                            (fact 'metric-dist-real 'mss_ 'msa_ b)
                            ;; d(a,b) <= w <= each of the three deltas
                            (for-each
                             (lambda (pr)
                               (dk-have! (list '<= dab (car pr))
                                 (lambda () (apply dk-ineq!
                                                   (append (cdr pr)
                                                           (list (list 'IN dab 'RR)))))))
                             (list (list dh1 (list '<= dab w) (list '<= w m1)
                                         (list '<= m1 dh1) (list 'IN w 'RR)
                                         (list 'IN m1 'RR) (list 'IN dh1 'RR))
                                   (list dg (list '<= dab w) (list '<= w m1)
                                         (list '<= m1 dg) (list 'IN w 'RR)
                                         (list 'IN m1 'RR) (list 'IN dg 'RR))
                                   (list dh (list '<= dab w) (list '<= w dh)
                                         (list 'IN w 'RR) (list 'IN dh 'RR))))
                            (dk-apply! (msc-delta-univ dh1 'msh_) b)
                            (dk-apply! (msc-delta-univ dg 'msg_) b)
                            (dk-apply! (msc-delta-univ dh 'msh_) b)
                            (msc-norm-le! ha hb 1)
                            (msc-norm-le! ga gb d0)
                            (dk-have! (list '<= (msc-nrm (msc-sub ha hb)) d0)
                              (lambda ()
                                (subst (list '= (msc-nrm (msc-sub ha hb))
                                                (msc-dM ha hb)))
                                (ass)))
                            ;; ||h(b)|| <= ||h(a)|| + 1
                            (fact 'nf-norm-le-add 'K hb ha)
                            (fact 'nf-norm-sub-sym 'K ha hb)
                            (dk-have! (list '<= (msc-nrm hb) msc-pr-k)
                              (lambda ()
                                (dk-ineq!
                                 (list '<= (msc-nrm hb)
                                       (list '+ (msc-nrm (msc-sub hb ha))
                                                (msc-nrm ha)))
                                 (list '= (msc-nrm (msc-sub ha hb))
                                          (msc-nrm (msc-sub hb ha)))
                                 (list '<= (msc-nrm (msc-sub ha hb)) 1)
                                 (list 'IN (msc-nrm hb) 'RR)
                                 (list 'IN (msc-nrm (msc-sub hb ha)) 'RR)
                                 (list 'IN (msc-nrm (msc-sub ha hb)) 'RR)
                                 (list 'IN (msc-nrm ha) 'RR))))
                            (fact 'nf-norm-prod-bound 'K ga ha gb hb
                                  msc-pr-m msc-pr-k d0 eps)
                            (fact 'nf-metric-distance 'K (msc-mul ga ha)
                                  (msc-mul gb hb))
                            (subst (list '= (msc-dM (msc-mul ga ha) (msc-mul gb hb))
                                            (msc-nrm (msc-sub (msc-mul ga ha)
                                                              (msc-mul gb hb)))))
                            (ass))))))))))))))
(qed 'nf-product-continuous-at)
(topic! 'nf-product-continuous-at 'analysis)
(alias! 'nf-product-continuous-at
        "the pointwise product of two maps continuous into a normed field is continuous")
