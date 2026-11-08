;;; product2-laws.scm -- the laws of PRODUCT2-MS (structure-library/product2-vocab.scm),
;;; the binary product of two metric spaces with the MAX metric.  Everything PROVEN,
;;; modulo 0; nothing asserted.  Helper prefix p2-.
;;;
;;;   product2-pts / product2-dist-slot   the two read-offs (guarded by IS-METRIC-SPACE s, t)
;;;   product2-dist                       d(p, q) == max(d_s(p1, q1), d_t(p2, q2)) on pairs of points
;;;   product2-dist-pair                  the same at literal pairs [a, b], [c, d]
;;;   product2-is-metric-space            the product of two metric spaces is a metric space
;;;   product2-fst/snd-continuous-at      the projections are continuous (delta = eps)
;;;   product2-pair-continuous-at         PAIRING: f, g continuous at x => z |-> [f z, g z] is
;;;   product2-continuous-at-coords       the converse
;;;   product2-continuous-at-iff          continuous into the product iff both coordinates are
;;;   product2-converges-to-iff           a sequence converges iff both coordinates do
;;;
;;; Every map is an arbitrary h with its value given POINTWISE (h(z) = [f z, g z],
;;; h(z) = NTH k z), the convention of ms-cont-transfer-ptwise-eq: no lambda is
;;; reduced under a binder.
;;;
;;; THE TRIANGLE INEQUALITY is the two coordinate triangle inequalities plus
;;; d_s <= max, d_t <= max and rr-max-le; SEPARATION is antisymmetry from
;;; 0 <= d_s <= max = 0 in each coordinate, then cartesian-pair-eq.
;;;
;;; WINDOW.  lo = theorem-library/monalg-is-ring (cartesian-pair-eq), load.scm
;;; line 1740 on 2026-10-25; next-latest finsum-fiber (cartesian-nth, 1716),
;;; structure-library/metric-laws (1452), op-typing (1071).  ms-pts-is-set
;;; (ms-continuity-algebra, 3034) and rr-max-left-le (one-sided-derivative-laws,
;;; 3072) were avoided on purpose to keep the floor there.  hi: none.  Needs
;;; structure-library/product2-vocab before it.  Tactics: the early kit only
;;; (dk-*, ineq, arith, dk-nn!, dk-halve!).  No top-level macro: compilable.

;;; ---- file-local driver helpers --------------------------------------

(define (p2-head g) (and (pair? g) (car g)))

;;; Land (IN (NTH 1 W) (PTS S)) and (IN (NTH 2 W) (PTS T)) from W in CARTESIAN.
(define (p2-comps! w s t)
  (if (not (dk-asm? (list 'IN (list 'NTH 1 w) (list 'PTS s))))
      (let ((c (dk-cite! 'cartesian-nth w (list 'PTS s) (list 'PTS t))))
        (if (dk-head-is? c 'AND) (dk-split! c)))))

;;; (IN ((DIST S) A B) RR)
(define (p2-dreal! s a b)
  (let ((f (list 'IN (list (list 'DIST s) a b) 'RR)))
    (if (not (dk-asm? f)) (dk-cite! 'metric-dist-real s a b))
    f))

;;; The two points of a max term (max ((DIST s) (NTH 1 u) (NTH 1 v)) ...).
(define (p2-pts-of m) (let ((a (cadr m))) (list (caddr (cadr a)) (caddr (caddr a)))))
(define (p2-x s u v) (list (list 'DIST s) (list 'NTH 1 u) (list 'NTH 1 v)))
(define (p2-y t u v) (list (list 'DIST t) (list 'NTH 2 u) (list 'NTH 2 v)))
(define (p2-m s t u v) (list 'max (p2-x s u v) (p2-y t u v)))

;;; Everything about the max term at u, v: components, the two real typings,
;;; the max typing, and X <= m, Y <= m.
(define (p2-max-facts! s t u v)
  (p2-comps! u s t) (p2-comps! v s t)
  (let ((x (p2-x s u v)) (y (p2-y t u v)))
    (p2-dreal! s (list 'NTH 1 u) (list 'NTH 1 v))
    (p2-dreal! t (list 'NTH 2 u) (list 'NTH 2 v))
    (if (not (dk-asm? (list 'IN (list 'max x y) 'RR))) (dk-cite! 'rr-max-closed x y))
    (if (not (dk-asm? (list '<= x (list 'max x y)))) (dk-cite! 'rr-le-max-left x y))
    (if (not (dk-asm? (list '<= y (list 'max x y)))) (dk-cite! 'rr-le-max-right x y))
    (list 'max x y)))

;;; From (= M 0), (<= 0 X), (<= X M): land (= X 0).
(define (p2-zero-of! x m)
  (dk-le-chain! x m 0)
  (dk-real! 0)
  (dk-have! (list 'AND (list 'IN x 'RR) (list 'IN 0 'RR)))
  (dk-have! (list 'AND (list '<= x 0) (list '<= 0 x)))
  (dk-cite! 'rr-leq-antisymmetric x 0))

;;; Goal (= U V), U, V in CARTESIAN(PTS s, PTS t), component equations in context.
(define (p2-pair-eq! u v s t)
  (let ((eu (dk-cite! 'cartesian-pair-eq u (list 'PTS s) (list 'PTS t)))
        (ev (dk-cite! 'cartesian-pair-eq v (list 'PTS s) (list 'PTS t))))
    (subst eu)
    (subst (list '= (list 'NTH 1 u) (list 'NTH 1 v)))
    (subst (list '= (list 'NTH 2 u) (list 'NTH 2 v)))
    (subst (list '= (caddr ev) v))
    (rfl)))

(define (p2-has-lam? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (p2-has-lam? (car g)) (p2-has-lam? (cdr g))))
        (#t #f)))

(define (p2-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (p2-has-lam? (dk-goal)))
        (let ((before (dk-goal))) (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

(define (p2-drive!)
  (let loop ((fuel 200))
    (let ((k (find-first (lambda (n) (memq (p2-head (dk-goal-of n))
                                           '(FORALL IMPLIES AND)))
                         (dk-open-leaves))))
      (if (and k (> fuel 0))
          (begin (dk-focus! k) (p2-beta!)
                 (if (memq (p2-head (dk-goal)) '(FORALL IMPLIES AND)) (di) #t)
                 (loop (- fuel 1)))
          #t))))

;;; The sethoods every proof below wants, landed once at the top.
(define (p2-sets! s t)
  ;; (IN (PTS x) SET) from the sethood conjunct of IS-METRIC-SPACE(x), on a lane
  ;; (mac-h consumes the folded hypothesis there only).  Not ms-pts-is-set: it
  ;; loads at ms-continuity-algebra, far below the rest of this file's citations.
  (for-each (lambda (x)
              (dk-have! (list 'IN (list 'PTS x) 'SET)
                (lambda ()
                  (mac-h 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE x))
                  (dk-split-all!)
                  (ass))))
            (list s t))
  (let ((p (list 'CARTESIAN (list 'PTS s) (list 'PTS t))))
    (dk-have! (list 'IN p 'SET)
      (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass)))))
    (dk-have! (list 'IN (list 'CARTESIAN p p) 'SET)
      (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass)))))))

(define P2-BODY
  '(VNB-LAMBDA (LIST p2u_ p2v_)
     (CARTESIAN (CARTESIAN (PTS s) (PTS t)) (CARTESIAN (PTS s) (PTS t)))
     (max ((DIST s) (NTH 1 p2u_) (NTH 1 p2v_))
          ((DIST t) (NTH 2 p2u_) (NTH 2 p2v_)))))

;;; =====================================================================
;;; (1) THE READ-OFFS.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (IMPLIES (IS-METRIC-SPACE s) (IMPLIES (IS-METRIC-SPACE t)
     (== (PTS (PRODUCT2-MS s t)) (CARTESIAN (PTS s) (PTS t)))))))))
(dk-peel!)
(p2-sets! 's 't)
(mac 'PRODUCT2-MS)
(slot 'PTS)
(nth-r)
(slot 'PTS)
(qrfl)
(qed 'product2-pts)
(topic! 'product2-pts 'constructions)
(alias! 'product2-pts "the points of a binary product metric space are the pairs")

(sp (make-wff (list 'FORALL 's (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE s)
     (list 'IMPLIES '(IS-METRIC-SPACE t)
       (list '== '(DIST (PRODUCT2-MS s t)) P2-BODY)))))))
(dk-peel!)
(p2-sets! 's 't)
(mac 'PRODUCT2-MS)
(slot 'DIST)
(nth-r)
(slot 'DIST)
(qrfl)
(qed 'product2-dist-slot)
(topic! 'product2-dist-slot 'constructions)
(alias! 'product2-dist-slot "the distance of a binary product metric space is the max metric")

;;; =====================================================================
;;; (2) THE DISTANCE VALUE, at points of the product and at literal pairs.
;;; =====================================================================
(sp (make-wff (list 'FORALL 's (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE s)
     (list 'IMPLIES '(IS-METRIC-SPACE t)
       (forall-guarded '(p2p_ p2q_) '((IN p2p_ (CARTESIAN (PTS s) (PTS t)))
                                      (IN p2q_ (CARTESIAN (PTS s) (PTS t))))
         '(== ((DIST (PRODUCT2-MS s t)) p2p_ p2q_)
              (max ((DIST s) (NTH 1 p2p_) (NTH 1 p2q_))
                   ((DIST t) (NTH 2 p2p_) (NTH 2 p2q_)))))))))))
(dk-peel!)
(p2-sets! 's 't)
(mac 'product2-dist-slot)
(dk-lam-b!)
(qrfl)
(qed 'product2-dist)
(topic! 'product2-dist 'constructions)
(alias! 'product2-dist "the product distance is the max of the coordinate distances")

(sp (make-wff (list 'FORALL 's (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE s)
     (list 'IMPLIES '(IS-METRIC-SPACE t)
       (forall-guarded '(p2a_ p2c_ p2b_ p2d_) '((IN p2a_ (PTS s)) (IN p2c_ (PTS s))
                                                (IN p2b_ (PTS t)) (IN p2d_ (PTS t)))
         '(== ((DIST (PRODUCT2-MS s t)) (LIST p2a_ p2b_) (LIST p2c_ p2d_))
              (max ((DIST s) p2a_ p2c_) ((DIST t) p2b_ p2d_))))))))))
(dk-peel!)
;; the eigenvariables are read off the GOAL: ((DIST ..) (LIST a b) (LIST c d))
(let* ((app (cadr (dk-goal))) (l1 (cadr app)) (l2 (caddr app))
       (a (cadr l1)) (b (caddr l1)) (c (cadr l2)) (d (caddr l2)))
  (dk-cite! 'pair-in-cartesian '(PTS s) '(PTS t) a b)
  (dk-cite! 'pair-in-cartesian '(PTS s) '(PTS t) c d)
  (let ((e (dk-cite! 'product2-dist 's 't (list 'LIST a b) (list 'LIST c d))))
    (subst e)
    (nth-r)
    (qrfl)))
(qed 'product2-dist-pair)
(topic! 'product2-dist-pair 'constructions)
(alias! 'product2-dist-pair "d([a,b],[c,d]) = max(d(a,c), d(b,d)) in the product")

;;; =====================================================================
;;; (3) THE PRODUCT OF TWO METRIC SPACES IS A METRIC SPACE.
;;; =====================================================================
(define (p2-law! s t)
  (let ((g (dk-goal)))
    (cond
      ;; d(u,u) = 0
      ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'max) (equal? (caddr g) 0))
       (let* ((u (car (p2-pts-of (cadr g)))))
         (p2-max-facts! s t u u)
         (dk-cite! 'metric-self-zero s (list 'NTH 1 u))
         (dk-cite! 'metric-self-zero t (list 'NTH 2 u))
         (subst (list '= (p2-x s u u) 0))
         (subst (list '= (p2-y t u u) 0))
         ;; max(0, 0) = 0 by antisymmetry: max(0,0) <= 0 (rr-max-le), 0 <= max(0,0)
         (dk-real! 0)
         (dk-have! '(<= 0 0) (lambda () (ineq)))
         (dk-cite! 'rr-max-le 0 0 0)
         (dk-cite! 'rr-le-max-left 0 0)
         (dk-cite! 'rr-max-closed 0 0)
         (dk-have! '(AND (IN (max 0 0) RR) (IN 0 RR)))
         (dk-have! '(AND (<= (max 0 0) 0) (<= 0 (max 0 0))))
         (dk-cite! 'rr-leq-antisymmetric '(max 0 0) 0)
         (ass)))
      ;; 0 <= d(u,v)
      ((and (dk-head-is? g '<=) (equal? (cadr g) 0))
       (let* ((uv (p2-pts-of (caddr g))) (u (car uv)) (v (cadr uv)))
         (p2-max-facts! s t u v)
         (dk-cite! 'metric-pos s (list 'NTH 1 u) (list 'NTH 1 v))
         (dk-le-chain! 0 (p2-x s u v) (p2-m s t u v))))
      ;; d(u,v) = 0 => u = v
      ((and (dk-head-is? g '=) (symbol? (cadr g)))
       (let* ((u (cadr g)) (v (caddr g)) (m (p2-m s t u v)))
         (p2-max-facts! s t u v)
         (dk-cite! 'metric-pos s (list 'NTH 1 u) (list 'NTH 1 v))
         (dk-cite! 'metric-pos t (list 'NTH 2 u) (list 'NTH 2 v))
         (p2-zero-of! (p2-x s u v) m)
         (p2-zero-of! (p2-y t u v) m)
         (dk-cite! 'metric-zero-eq s (list 'NTH 1 u) (list 'NTH 1 v))
         (dk-cite! 'metric-zero-eq t (list 'NTH 2 u) (list 'NTH 2 v))
         (p2-pair-eq! u v s t)))
      ;; d(u,v) = d(v,u)
      ((dk-head-is? g '=)
       (let* ((uv (p2-pts-of (cadr g))) (u (car uv)) (v (cadr uv)))
         (p2-max-facts! s t u v)
         (p2-max-facts! s t v u)
         (dk-cite! 'metric-sym s (list 'NTH 1 u) (list 'NTH 1 v))
         (dk-cite! 'metric-sym t (list 'NTH 2 u) (list 'NTH 2 v))
         (subst (list '= (p2-x s u v) (p2-x s v u)))
         (subst (list '= (p2-y t u v) (p2-y t v u)))
         (rfl)))
      ;; d(u,w) <= d(u,v) + d(v,w)
      ((dk-head-is? g '<=)
       (let* ((uw (p2-pts-of (cadr g))) (u (car uw)) (w (cadr uw))
              (v  (cadr (p2-pts-of (cadr (caddr g)))))
              (m1 (p2-m s t u v)) (m2 (p2-m s t v w)) (sum (list '+ m1 m2)))
         (p2-max-facts! s t u w) (p2-max-facts! s t u v) (p2-max-facts! s t v w)
         (dk-cite! 'metric-triangle s (list 'NTH 1 u) (list 'NTH 1 v) (list 'NTH 1 w))
         (dk-cite! 'metric-triangle t (list 'NTH 2 u) (list 'NTH 2 v) (list 'NTH 2 w))
         (dk-le-add! (p2-x s u v) m1 (p2-x s v w) m2)
         (dk-le-chain! (p2-x s u w) (list '+ (p2-x s u v) (p2-x s v w)) sum)
         (dk-le-add! (p2-y t u v) m1 (p2-y t v w) m2)
         (dk-le-chain! (p2-y t u w) (list '+ (p2-y t u v) (p2-y t v w)) sum)
         (dk-real! sum)
         (dk-cite! 'rr-max-le (p2-x s u w) (p2-y t u w) sum)
         (ass)))
      (#t (error "p2-law!: unexpected leaf" g)))))

(sp (make-wff '(FORALL s (FORALL t (IMPLIES (IS-METRIC-SPACE s) (IMPLIES (IS-METRIC-SPACE t)
     (IS-METRIC-SPACE (PRODUCT2-MS s t))))))))
(dk-peel!)
(p2-sets! 's 't)
(mac 'IS-METRIC-SPACE)
(dk-isx-set!)                ; W1J-A: the conjunct t in SET, from the typings
(mac 'product2-pts)
(mac 'product2-dist-slot)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'LENGTH))
        (mac 'PRODUCT2-MS) (len-r) (arith))
       ((and (dk-head-is? g 'IN) (equal? (caddr g) 'SET)) (ass))
       ((dk-head-is? g 'IN)
        (for-each (lambda (k)
                    (dk-focus! k) (p2-drive!)
                    (let ((g2 (dk-goal)))
                      (if (equal? (caddr g2) 'SET)
                          (ass)
                          (let ((uv (p2-pts-of (cadr g2))))
                            (p2-max-facts! 's 't (car uv) (cadr uv))
                            (ass)))))
                  (dk-opened (lambda () (lam-t)))))
       (#t (let ((before (dk-open-leaves)))
             (mac 'is-metric) (p2-drive!)
             (for-each (lambda (k) (dk-focus! k) (p2-law! 's 't))
                       (filter (lambda (n) (not (memq n before))) (dk-open-leaves)))))))))
(qed 'product2-is-metric-space)
(topic! 'product2-is-metric-space 'constructions)
(alias! 'product2-is-metric-space "the product of two metric spaces, with the max metric, is a metric space")

;;; =====================================================================
;;; (4) CONTINUITY.  Helpers for the eps-delta drives.
;;; =====================================================================

;;; POS-RR t -> (IN t RR), (< 0 t), by citation (the POS-RR stays).
(define (p2-pos! t)
  (if (not (dk-asm? (list 'IN t 'RR))) (dk-cite! 'rr-pos-rr-in-rr t))
  (if (not (dk-asm? (list '< 0 t))) (dk-cite! 'rr-lt-of-pos-rr t)))

;;; The eps just peeled: the POS-RR among the formulas LANDED.
(define (p2-landed-eps landed)
  (let ((l (filter (dk-head? 'POS-RR) landed)))
    (if (null? l) (error "p2-landed-eps: no POS-RR landed") (cadr (car l)))))

;;; The variable typed in CLS among LANDED.
(define (p2-landed-var landed cls)
  (let ((l (filter (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) cls))) landed)))
    (if (null? l) (error "p2-landed-var: nothing typed in" cls) (cadr (car l)))))

;;; An eps universal of an unfolded continuity / convergence hypothesis,
;;; discriminated by a term only it contains.
(define (p2-eps-univ mark)
  (dk-pick (lambda (fm)
             (and (dk-head-is? fm 'FORALL) (dk-contains? fm 'POS-RR)
                  (dk-contains? fm 'FORSOME) (dk-contains? fm 'DIST)
                  (dk-contains? fm mark)))
           "an eps universal"))

;;; The universal that skolemising an eps universal at D landed.
(define (p2-delta-univ d mark)
  (dk-pick (lambda (fm)
             (and (dk-head-is? fm 'FORALL) (dk-contains? fm 'DIST) (dk-contains? fm d)
                  (not (dk-contains? fm 'POS-RR)) (dk-contains? fm mark)))
           "a delta universal"))

;;; The pointwise agreement h(z) = [f z, g z] among LANDED.
(define (p2-agree landed mark)
  (let ((l (filter (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f mark)
                                    (dk-contains? f 'LIST)))
                   landed)))
    (if (null? l) (error "p2-agree: no agreement universal") (car l))))

;;; (= (h z) (LIST (f z) (g z))) at Z, with both values typed; returns the equation.
(define (p2-agree-at! agree z f g dom s t)
  (dk-cite! 'fun-apply-type-c f dom (list 'PTS s) z)
  (dk-cite! 'fun-apply-type-c g dom (list 'PTS t) z)
  (dk-apply! agree z))

;;; =====================================================================
;;; (4a) THE PROJECTIONS ARE CONTINUOUS (they are 1-Lipschitz).  Any h equal to
;;; the projection pointwise; the same delta = eps.
;;; =====================================================================
(define (p2-proj-thm! k)
  (let ((cod (if (= k 1) 's 't)))
    (sp (make-wff
      (list 'FORALL 's (list 'FORALL 't (list 'IMPLIES '(IS-METRIC-SPACE s)
        (list 'IMPLIES '(IS-METRIC-SPACE t)
          (list 'FORALL 'p2h_
            (list 'IMPLIES (list 'IN 'p2h_ (list 'FUN '(CARTESIAN (PTS s) (PTS t)) (list 'PTS cod)))
              (list 'IMPLIES
                (list 'FORALL 'p2z_ (list 'IMPLIES '(IN p2z_ (CARTESIAN (PTS s) (PTS t)))
                                          (list '= '(p2h_ p2z_) (list 'NTH k 'p2z_))))
                (list 'FORALL 'p2x_ (list 'IMPLIES '(IN p2x_ (CARTESIAN (PTS s) (PTS t)))
                  (list 'IS-CONTINUOUS-AT '(PRODUCT2-MS s t) cod 'p2h_ 'p2x_))))))))))))
    (let* ((ld (dk-peel!))
           (agree (car (filter (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'p2h_))) ld)))
           (x (p2-landed-var ld '(CARTESIAN (PTS s) (PTS t)))))
      (p2-sets! 's 't)
      (dk-cite! 'product2-is-metric-space 's 't)
      (mac 'IS-CONTINUOUS-AT)
      (mac 'product2-pts)
      (dk-conj-close!
       (lambda ()
         (if (not (dk-head-is? (dk-goal) 'FORALL))
             (ass)
             (let* ((ld2 (dk-peel!)) (eps (p2-landed-eps ld2)))
               (p2-pos! eps)
               (ew eps)
               (dk-conj-close!
                (lambda ()
                  (if (dk-head-is? (dk-goal) 'POS-RR)
                      (ass)
                      (let* ((ld3 (dk-peel!))
                             (b (p2-landed-var ld3 '(CARTESIAN (PTS s) (PTS t))))
                             (hyp (car (filter (dk-head? '<=) ld3))))
                        (subst (dk-apply! agree x))
                        (subst (dk-apply! agree b))
                        (let* ((e (dk-cite! 'product2-dist 's 't x b))
                               (h2 (dk-rewrite-h! hyp (cadr e) (caddr e)))
                               (m (p2-max-facts! 's 't x b)))
                          (dk-le-chain! (if (= k 1) (p2-x 's x b) (p2-y 't x b)) m eps)))))))))))))

(p2-proj-thm! 1)
(qed 'product2-fst-continuous-at)
(topic! 'product2-fst-continuous-at 'analysis)
(alias! 'product2-fst-continuous-at "the first projection of a product metric space is continuous")

(p2-proj-thm! 2)
(qed 'product2-snd-continuous-at)
(topic! 'product2-snd-continuous-at 'analysis)
(alias! 'product2-snd-continuous-at "the second projection of a product metric space is continuous")

;;; =====================================================================
;;; (4b) THE PAIRING PROPERTY: f, g continuous at x  =>  z |-> [f z, g z]
;;; continuous at x into the product.  delta = a common lower bound of the two.
;;; =====================================================================
(sp (make-wff '(FORALL p2w_ (FORALL s (FORALL t (FORALL p2f_ (FORALL p2g_ (FORALL p2x_
     (IMPLIES (IS-CONTINUOUS-AT p2w_ s p2f_ p2x_)
       (IMPLIES (IS-CONTINUOUS-AT p2w_ t p2g_ p2x_)
         (FORALL p2h_ (IMPLIES (IN p2h_ (FUN (PTS p2w_) (CARTESIAN (PTS s) (PTS t))))
           (IMPLIES (FORALL p2z_ (IMPLIES (IN p2z_ (PTS p2w_))
                      (= (p2h_ p2z_) (LIST (p2f_ p2z_) (p2g_ p2z_)))))
             (IS-CONTINUOUS-AT p2w_ (PRODUCT2-MS s t) p2h_ p2x_))))))))))))))
(define p2-pc-landed (dk-peel!))
(define p2-pc-agree (p2-agree p2-pc-landed 'p2h_))
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT p2w_ s p2f_ p2x_))
(dk-split-all!)
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT p2w_ t p2g_ p2x_))
(dk-split-all!)
(p2-sets! 's 't)
(dk-cite! 'product2-is-metric-space 's 't)
(mac 'IS-CONTINUOUS-AT)
(mac 'product2-pts)
(dk-conj-close!
 (lambda ()
   (if (not (dk-head-is? (dk-goal) 'FORALL))
       (ass)
       (let* ((ld (dk-peel!)) (eps (p2-landed-eps ld)))
         (p2-pos! eps)
         (let* ((d1 (dk-skolem! (dk-apply! (p2-eps-univ 'p2f_) eps)))
                (d2 (dk-skolem! (dk-apply! (p2-eps-univ 'p2g_) eps))))
           (p2-pos! d1) (p2-pos! d2)
           (let ((dl (dk-skolem! (dk-cite! 'rr-min-pos d1 d2))))
             (dk-cite! 'rr-pos-rr-of-lt dl)
             (ew dl)
             (dk-conj-close!
              (lambda ()
                (if (dk-head-is? (dk-goal) 'POS-RR)
                    (ass)
                    (let* ((ld2 (dk-peel!))
                           (b (p2-landed-var ld2 '(PTS p2w_)))
                           (dxb (list '(DIST p2w_) 'p2x_ b)))
                      (subst (p2-agree-at! p2-pc-agree 'p2x_ 'p2f_ 'p2g_ '(PTS p2w_) 's 't))
                      (subst (p2-agree-at! p2-pc-agree b 'p2f_ 'p2g_ '(PTS p2w_) 's 't))
                      (subst (dk-cite! 'product2-dist-pair 's 't
                                       '(p2f_ p2x_) (list 'p2f_ b) '(p2g_ p2x_) (list 'p2g_ b)))
                      (p2-dreal! 'p2w_ 'p2x_ b)
                      (dk-le-chain! dxb dl d1)
                      (dk-le-chain! dxb dl d2)
                      (dk-apply! (p2-delta-univ d1 'p2f_) b)
                      (dk-apply! (p2-delta-univ d2 'p2g_) b)
                      (let ((x1 (p2-dreal! 's '(p2f_ p2x_) (list 'p2f_ b)))
                            (y1 (p2-dreal! 't '(p2g_ p2x_) (list 'p2g_ b))))
                        (dk-cite! 'rr-max-le (cadr x1) (cadr y1) eps)
                        (ass))))))))))))
(qed 'product2-pair-continuous-at)
(topic! 'product2-pair-continuous-at 'analysis)
(alias! 'product2-pair-continuous-at
        "a map into a product metric space is continuous where both coordinates are")

;;; =====================================================================
;;; (4c) THE CONVERSE: the coordinates of a continuous map into the product are
;;; continuous.  The same delta.
;;; =====================================================================
(define P2-AGREE-W
  '(FORALL p2z_ (IMPLIES (IN p2z_ (PTS p2w_))
     (= (p2h_ p2z_) (LIST (p2f_ p2z_) (p2g_ p2z_))))))

(sp (make-wff (list 'FORALL 'p2w_ (list 'FORALL 's (list 'FORALL 't (list 'FORALL 'p2f_
     (list 'FORALL 'p2g_ (list 'FORALL 'p2h_ (list 'FORALL 'p2x_
       (list 'IMPLIES '(IS-METRIC-SPACE s) (list 'IMPLIES '(IS-METRIC-SPACE t)
         (list 'IMPLIES '(IN p2f_ (FUN (PTS p2w_) (PTS s)))
           (list 'IMPLIES '(IN p2g_ (FUN (PTS p2w_) (PTS t)))
             (list 'IMPLIES P2-AGREE-W
               (list 'IMPLIES '(IS-CONTINUOUS-AT p2w_ (PRODUCT2-MS s t) p2h_ p2x_)
                 '(AND (IS-CONTINUOUS-AT p2w_ s p2f_ p2x_)
                       (IS-CONTINUOUS-AT p2w_ t p2g_ p2x_)))))))))))))))))
(define p2-cc-landed (dk-peel!))
(define p2-cc-agree (p2-agree p2-cc-landed 'p2h_))
(p2-sets! 's 't)
(dk-cite! 'product2-is-metric-space 's 't)
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT p2w_ (PRODUCT2-MS s t) p2h_ p2x_))
(dk-split-all!)
(dk-conj-close!
 (lambda ()
   (let ((first? (dk-contains? (dk-goal) 'p2f_)))
     (mac 'IS-CONTINUOUS-AT)
     (dk-conj-close!
      (lambda ()
        (if (not (dk-head-is? (dk-goal) 'FORALL))
            (ass)
            (let* ((ld (dk-peel!)) (eps (p2-landed-eps ld)))
              (p2-pos! eps)
              (let ((del (dk-skolem! (dk-apply! (p2-eps-univ 'p2h_) eps))))
                (ew del)
                (dk-conj-close!
                 (lambda ()
                   (if (dk-head-is? (dk-goal) 'POS-RR)
                       (ass)
                       (let* ((ld2 (dk-peel!))
                              (b (p2-landed-var ld2 '(PTS p2w_)))
                              (h0 (dk-apply! (p2-delta-univ del 'p2h_) b))
                              (h1 (dk-rewrite-h! h0 '(p2h_ p2x_)
                                    (caddr (p2-agree-at! p2-cc-agree 'p2x_ 'p2f_ 'p2g_ '(PTS p2w_) 's 't))))
                              (h2 (dk-rewrite-h! h1 (list 'p2h_ b)
                                    (caddr (p2-agree-at! p2-cc-agree b 'p2f_ 'p2g_ '(PTS p2w_) 's 't))))
                              (e (dk-cite! 'product2-dist-pair 's 't
                                           '(p2f_ p2x_) (list 'p2f_ b) '(p2g_ p2x_) (list 'p2g_ b)))
                              (h3 (dk-rewrite-h! h2 (cadr e) (caddr e))))
                         (p2-dreal! 's '(p2f_ p2x_) (list 'p2f_ b))
                         (p2-dreal! 't '(p2g_ p2x_) (list 'p2g_ b))
                         (let* ((x1 (list '(DIST s) '(p2f_ p2x_) (list 'p2f_ b)))
                                (y1 (list '(DIST t) '(p2g_ p2x_) (list 'p2g_ b)))
                                (m (list 'max x1 y1)))
                           (dk-cite! 'rr-max-closed x1 y1)
                           (if first?
                               (begin (dk-cite! 'rr-le-max-left x1 y1) (dk-le-chain! x1 m eps))
                               (begin (dk-cite! 'rr-le-max-right x1 y1) (dk-le-chain! y1 m eps))))))))))))))))
(qed 'product2-continuous-at-coords)
(topic! 'product2-continuous-at-coords 'analysis)
(alias! 'product2-continuous-at-coords
        "the coordinates of a map continuous into a product metric space are continuous")

;;; (4d) THE IFF.
(sp (make-wff (list 'FORALL 'p2w_ (list 'FORALL 's (list 'FORALL 't (list 'FORALL 'p2f_
     (list 'FORALL 'p2g_ (list 'FORALL 'p2h_ (list 'FORALL 'p2x_
       (list 'IMPLIES '(IS-METRIC-SPACE s) (list 'IMPLIES '(IS-METRIC-SPACE t)
         (list 'IMPLIES '(IN p2f_ (FUN (PTS p2w_) (PTS s)))
           (list 'IMPLIES '(IN p2g_ (FUN (PTS p2w_) (PTS t)))
             (list 'IMPLIES '(IN p2h_ (FUN (PTS p2w_) (CARTESIAN (PTS s) (PTS t))))
               (list 'IMPLIES P2-AGREE-W
                 '(IFF (IS-CONTINUOUS-AT p2w_ (PRODUCT2-MS s t) p2h_ p2x_)
                       (AND (IS-CONTINUOUS-AT p2w_ s p2f_ p2x_)
                            (IS-CONTINUOUS-AT p2w_ t p2g_ p2x_))))))))))))))))))
(dk-peel!)
(dk-iff! (dk-head? 'AND)
  (lambda ()
    (dk-cite! 'product2-continuous-at-coords 'p2w_ 's 't 'p2f_ 'p2g_ 'p2h_ 'p2x_)
    (ass))
  (lambda ()
    (dk-split-all!)
    (dk-cite! 'product2-pair-continuous-at 'p2w_ 's 't 'p2f_ 'p2g_ 'p2x_ 'p2h_)
    (ass)))
(qed 'product2-continuous-at-iff)
(topic! 'product2-continuous-at-iff 'analysis)
(alias! 'product2-continuous-at-iff
        "a map into a product metric space is continuous at a point iff both coordinates are")

;;; =====================================================================
;;; (5) SEQUENCES: convergence in the product iff coordinatewise.
;;; Forward: the same N.  Backward: N = N1 + N2.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (IMPLIES (IS-METRIC-SPACE s) (IMPLIES (IS-METRIC-SPACE t)
     (FORALL p2u_ (FORALL p2a_ (FORALL p2b_
       (IMPLIES (IN p2u_ (FUN NN (CARTESIAN (PTS s) (PTS t))))
         (IMPLIES (IN p2a_ (FUN NN (PTS s)))
           (IMPLIES (IN p2b_ (FUN NN (PTS t)))
             (IMPLIES (FORALL p2n_ (IMPLIES (IN p2n_ NN)
                        (= (p2u_ p2n_) (LIST (p2a_ p2n_) (p2b_ p2n_)))))
               (FORALL p2l_ (FORALL p2m_
                 (IMPLIES (IN p2l_ (PTS s)) (IMPLIES (IN p2m_ (PTS t))
                   (IFF (CONVERGES-TO (PRODUCT2-MS s t) p2u_ (LIST p2l_ p2m_))
                        (AND (CONVERGES-TO s p2a_ p2l_) (CONVERGES-TO t p2b_ p2m_))))))))))))))))))))
(define p2-sq-landed (dk-peel!))
(define p2-sq-agree (p2-agree p2-sq-landed 'p2u_))
(p2-sets! 's 't)
(dk-cite! 'product2-is-metric-space 's 't)
(dk-cite! 'pair-in-cartesian '(PTS s) '(PTS t) 'p2l_ 'p2m_)

;;; At index K: (= (u k) [a k, b k]) with both values typed, and the distance
;;; equation at the limit; returns the equation d(u k, [l, m]) == max(..).
(define (p2-sq-at! k)
  (dk-cite! 'fun-apply-type-c 'p2a_ 'NN '(PTS s) k)
  (dk-cite! 'fun-apply-type-c 'p2b_ 'NN '(PTS t) k)
  (p2-dreal! 's (list 'p2a_ k) 'p2l_)
  (p2-dreal! 't (list 'p2b_ k) 'p2m_)
  (dk-cite! 'product2-dist-pair 's 't (list 'p2a_ k) 'p2l_ (list 'p2b_ k) 'p2m_))

(dk-iff! (dk-head? 'AND)
  ;; forward
  (lambda ()
    (mac-h 'CONVERGES-TO '(CONVERGES-TO (PRODUCT2-MS s t) p2u_ (LIST p2l_ p2m_)))
    (dk-split-all!)
    (dk-conj-close!
     (lambda ()
       (let ((first? (dk-contains? (dk-goal) 'p2a_)))
         (mac 'CONVERGES-TO)
         (dk-conj-close!
          (lambda ()
            (if (not (dk-head-is? (dk-goal) 'FORALL))
                (ass)
                (let* ((ld (dk-peel!)) (eps (p2-landed-eps ld)))
                  (p2-pos! eps)
                  (let ((n0 (dk-skolem! (dk-apply! (p2-eps-univ 'p2u_) eps))))
                    (ew n0)
                    (dk-conj-close!
                     (lambda ()
                       (if (not (dk-head-is? (dk-goal) 'FORALL))
                           (ass)
                           (let* ((ld2 (dk-peel!))
                                  (k (p2-landed-var ld2 'NN))
                                  (h0 (dk-apply! (p2-delta-univ n0 'p2u_) k))
                                  (h1 (dk-rewrite-h! h0 (list 'p2u_ k)
                                                     (caddr (dk-apply! p2-sq-agree k))))
                                  (e  (p2-sq-at! k))
                                  (h2 (dk-rewrite-h! h1 (cadr e) (caddr e)))
                                  (x1 (list '(DIST s) (list 'p2a_ k) 'p2l_))
                                  (y1 (list '(DIST t) (list 'p2b_ k) 'p2m_))
                                  (m  (list 'max x1 y1)))
                             (dk-cite! 'rr-max-closed x1 y1)
                             (if first?
                                 (begin (dk-cite! 'rr-le-max-left x1 y1) (dk-le-chain! x1 m eps))
                                 (begin (dk-cite! 'rr-le-max-right x1 y1) (dk-le-chain! y1 m eps))))))))))))))))
  ;; backward
  (lambda ()
    (dk-split-all!)
    (mac-h 'CONVERGES-TO '(CONVERGES-TO s p2a_ p2l_))
    (dk-split-all!)
    (mac-h 'CONVERGES-TO '(CONVERGES-TO t p2b_ p2m_))
    (dk-split-all!)
    (mac 'CONVERGES-TO)
    (mac 'product2-pts)
    (dk-conj-close!
     (lambda ()
       (if (not (dk-head-is? (dk-goal) 'FORALL))
           (ass)
           (let* ((ld (dk-peel!)) (eps (p2-landed-eps ld)))
             (p2-pos! eps)
             (let* ((n1 (dk-skolem! (dk-apply! (p2-eps-univ 'p2a_) eps)))
                    (n2 (dk-skolem! (dk-apply! (p2-eps-univ 'p2b_) eps)))
                    (nn (list '+ n1 n2)))
               (dk-have! (list 'AND (list 'IN n1 'NN) (list 'IN n2 'NN)))
               (dk-cite! 'nn-add-closed n1 n2)
               (ew nn)
               (dk-conj-close!
                (lambda ()
                  (if (not (dk-head-is? (dk-goal) 'FORALL))
                      (ass)
                      (let* ((ld2 (dk-peel!))
                             (k (p2-landed-var ld2 'NN))
                             (le (list '<= nn k)))
                        (dk-have! (list '<= n1 k) (lambda () (dk-nn! le)))
                        (dk-have! (list '<= n2 k) (lambda () (dk-nn! le)))
                        (dk-apply! (p2-delta-univ n1 'p2a_) k)
                        (dk-apply! (p2-delta-univ n2 'p2b_) k)
                        (subst (dk-apply! p2-sq-agree k))
                        (subst (p2-sq-at! k))
                        (dk-cite! 'rr-max-le (list '(DIST s) (list 'p2a_ k) 'p2l_)
                                             (list '(DIST t) (list 'p2b_ k) 'p2m_) eps)
                        (ass))))))))))))
(qed 'product2-converges-to-iff)
(topic! 'product2-converges-to-iff 'analysis)
(alias! 'product2-converges-to-iff
        "a sequence converges in a product metric space iff both coordinate sequences do")
