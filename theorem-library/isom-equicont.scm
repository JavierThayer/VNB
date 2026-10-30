;;; isom-equicont.scm -- calculus.pdf Proposition 3.33: on a compact metric space,
;;; pointwise and uniform convergence agree for an equicontinuous sequence of
;;; functions into ANY metric space.  Agent ISOM, 2026-10-26.
;;;
;;;   uniform-conv-implies-ptwise                      (the notes' "other direction")
;;;     CONVERGES-UNIFORMLY-TO(s, t, fam, g)  ==>  CONVERGES-PTWISE-TO(s, t, fam, g)
;;;
;;;   equicont-ptwise-implies-uniform                  (the notes' main direction)
;;;     s compact, fam equicontinuous from s to t, fam -> g pointwise
;;;       ==>  fam -> g uniformly
;;;
;;;   equicont-compact-ptwise-iff-uniform              (Prop 3.33)
;;;     s compact, fam equicontinuous  ==>  (pointwise iff uniform), for every g
;;;
;;; THE NOTES' PROOF assumes the limit f lies in E (equicontinuity at x is then used for
;;; f too, through Remark 3.32).  Here the limit g is ANY function pts(s) -> pts(t) and
;;; the estimate goes through a second index l instead: for y near x and k >= m_x,
;;;
;;;   d(f_k y, g y) <= d(f_k y, f_k x) + d(f_k x, g x) + d(g x, f_l x)
;;;                    + d(f_l x, f_l y) + d(f_l y, g y)  <=  5c
;;;
;;; with l = m_x + N_y large enough at x and at y (N_y the pointwise threshold at y).
;;; So no closedness of balls, no limit inequality and no Remark 3.32 is needed.
;;;
;;; COMPACTNESS.  As in calc3-uniform.scm (Prop 3.22) the cover is COUNTABLE, indexed by
;;; the threshold, so no choice function x |-> m_x and no maximum over a finite set:
;;;
;;;   W_n = { y in pts(s) : some x in pts(s) and r > 0 have d(x, y) < r,
;;;            d(f_k x, f_k z) < c for every k and every z with d(x, z) < r, and
;;;            d(f_k x, g x) <= c for every k >= n }.
;;;
;;; W_n is open (a ball of radius r - d(x, y) around y stays in it with the same x, r);
;;; the W_n cover pts(s) (at x: the equicontinuity radius at (x, c) and the pointwise
;;; threshold at (x, c)); pts(s) is closed in s (carrier-is-closed, isom-uc.scm), and
;;; compact-closed-countable-subcover returns N with every point in some W_n, n < N.
;;; c = eps/8 (three halvings), 5c <= eps.
;;;
;;; WINDOW.  Citations: carrier-is-closed (isom-uc.scm), compact-closed-countable-subcover
;;; (metric-finite-subcover), ball-membership (rake-balls), metric-triangle / metric-sym /
;;; metric-self-zero (metric-laws), metric-dist-real (op-typing), fun-apply-type-c,
;;; nn-add-closed, rr-* order and halving lemmas, the vocabulary (isom-vocab.scm) and
;;; IS-EQUICONTINUOUS (ascoli-arzela-statement).  lo = after isom-uc.scm; hi = none.
;;; Library: analysis.
;;;
;;; Helper prefix: iec-.

(define (iec-head g) (and (pair? g) (car g)))

(define (iec-iff-rhs! iff)
  (let ((rhs (caddr iff)))
    (dk-have! rhs (lambda () (prop)))
    (if (eq? (iec-head rhs) 'AND) (dk-split-all! (list rhs)))
    rhs))

(define (iec-ds a b) (list '(DIST s) a b))
(define (iec-dt a b) (list '(DIST t) a b))
(define (iec-F k x) (list (list 'fam k) x))
(define (iec-g x) (list 'g x))

;;; W_n with tolerance C.  NBGSEP (2026-10-28): the radius carries `iwr_ in RR' (implied by
;;; POS-RR), so the SEP is predicative and the family VNB-LAMBDA(n, NN, W_n) is certified defined.
(define (iec-w n C)
  (list 'SEP 'iwy_ '(PTS s)
    (list 'FORSOME 'iwx_
      (list 'AND (list 'IN 'iwx_ '(PTS s))
        (list 'FORSOME 'iwr_
          (list 'AND (list 'IN 'iwr_ 'RR) (list 'AND (list 'POS-RR 'iwr_)
           (list 'AND (list '< (iec-ds 'iwx_ 'iwy_) 'iwr_)
            (list 'AND
              (list 'FORALL 'iwk_ (list 'IMPLIES (list 'IN 'iwk_ 'NN)
                (list 'FORALL 'iwz_ (list 'IMPLIES (list 'IN 'iwz_ '(PTS s))
                  (list 'IMPLIES (list '< (iec-ds 'iwx_ 'iwz_) 'iwr_)
                    (list '< (iec-dt (iec-F 'iwk_ 'iwx_) (iec-F 'iwk_ 'iwz_)) C))))))
              (list 'FORALL 'iwk_ (list 'IMPLIES (list 'IN 'iwk_ 'NN)
                (list 'IMPLIES (list '<= n 'iwk_)
                  (list '<= (iec-dt (iec-F 'iwk_ 'iwx_) (iec-g 'iwx_)) C)))))))))))))

;;; Membership of P in W_n with centre X and radius R: run sep-mi, give X and R to the
;;; two existentials in order, LT-PROOF closes the strict inequality, `ass' the rest.
(define (iec-into-w! X R lt-proof)
  (let ((wits (list X R)))
    (define (closer)
      (let ((g (dk-goal)))
        (cond ((eq? (iec-head g) 'FORSOME)
               (let ((w (car wits)))
                 (set! wits (cdr wits))
                 (ew w)
                 (dk-conj-close! closer)))
              ((eq? (iec-head g) '<) (lt-proof))
              (#t (ass)))))
    (for-each
     (lambda (leaf)
       (if (not (sequent-node-grounded? leaf))
           (begin (dk-focus! leaf) (closer))))
     (dk-opened (lambda () (sep-mi))))))

;;; Open the membership (IN P (SEP ...)) in context; return what landed.
(define (iec-sep-open! P)
  (let ((m (dk-pick (lambda (h) (and (eq? (iec-head h) 'IN) (equal? (cadr h) P)
                                     (dk-head-is? (caddr h) 'SEP)))
                    "the SEP membership")))
    (dk-split-all! (dk-landed (lambda () (sep-me m))))))

;;; skolemise the centre and the radius of a W-membership just opened; return (x r)
(define (iec-centre!)
  (let* ((x (dk-skolem! (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORSOME) (eq? (cadr h) 'iwx_)))
                                 "the centre existential")))
         (r (dk-skolem! (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORSOME) (eq? (cadr h) 'iwr_)))
                                 "the radius existential"))))
    (list x r)))

;;; the instance at the focus: close the goal by instantiating the in-context
;;; universal F at TERMS (the last detachment may land the goal itself)
(define (iec-inst-close! f . terms)
  (dk-close-if! (lambda () (apply inst*! f terms)) ass))

;;; =====================================================================
;;; (1) uniform convergence implies pointwise convergence
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL fam (FORALL g
     (IMPLIES (CONVERGES-UNIFORMLY-TO s t fam g)
              (CONVERGES-PTWISE-TO s t fam g))))))))
(dk-peel!)
(iec-iff-rhs! (dk-cite! 'converges-uniformly-to 's 't 'fam 'g))
(define iec-u1 (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h 'POS-RR)))
                        "the uniform clause"))
(mac 'converges-ptwise-to)
(dk-conj-close!
 (lambda ()
   (if (eq? (iec-head (dk-goal)) 'FORALL)
       (let* ((pl (dk-peel!))
              (x (cadr (car (filter (lambda (f) (eq? (iec-head f) 'IN)) pl))))
              (e (cadr (car (filter (lambda (f) (eq? (iec-head f) 'POS-RR)) pl))))
              (n (dk-skolem! (dk-apply! iec-u1 e)))
              (cl (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h n)))
                           "the threshold clause")))
         (ew n)
         (dk-conj-close!
          (lambda ()
            (if (eq? (iec-head (dk-goal)) 'FORALL)
                (let* ((pk (dk-peel!))
                       (k (cadr (car (filter (lambda (f) (eq? (iec-head f) 'IN)) pk))))
                       (fx (dk-apply! cl k)))
                  (iec-inst-close! fx x))
                (ass)))))
       (ass))))
(qed 'uniform-conv-implies-ptwise)
(topic! 'uniform-conv-implies-ptwise 'analysis)
(alias! 'uniform-conv-implies-ptwise
        "uniform convergence of a sequence of functions implies pointwise convergence")

;;; =====================================================================
;;; (2) compact + equicontinuous + pointwise  ==>  uniform
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL fam (FORALL g
     (IMPLIES (IS-COMPACT s)
       (IMPLIES (IS-EQUICONTINUOUS s t fam)
         (IMPLIES (CONVERGES-PTWISE-TO s t fam g)
                  (CONVERGES-UNIFORMLY-TO s t fam g))))))))))
(dk-peel!)
(dk-project! '(IS-METRIC-SPACE s) 'is-compact '(IS-COMPACT s))
(iec-iff-rhs! (dk-cite! 'is-equicontinuous 's 't 'fam))
(iec-iff-rhs! (dk-cite! 'converges-ptwise-to 's 't 'fam 'g))
(dk-project! '(IN (PTS s) SET) 'is-metric-space '(IS-METRIC-SPACE s))
(define iec-eq (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h 'del)
                                         (dk-contains? h 'POS-RR)))
                        "the equicontinuity clause"))
(define iec-pw (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h 'POS-RR)
                                         (dk-contains? h '(DIST t)) (not (eq? h iec-eq))
                                         (dk-contains? h 'g)))
                        "the pointwise clause"))
(mac 'converges-uniformly-to)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (iec-head (dk-goal)) 'FORALL))
       (ass)
       (let* ((pe (dk-peel!))
              (eps (cadr (car (filter (lambda (f) (eq? (iec-head f) 'POS-RR)) pe))))
              (h1 (dk-halve! eps))
              (h2 (dk-halve! h1))
              (c (dk-halve! h2))
              (Lw (list 'VNB-LAMBDA 'isn_ 'NN (iec-w 'isn_ c)))
              (inst (dk-cite! 'compact-closed-countable-subcover 's '(PTS s) Lw)))
         (fact 'rr-pos-rr-in-rr eps)
         (fact 'rr-pos-rr-in-rr h1)
         (fact 'rr-pos-rr-in-rr h2)
         ;; (a) pts(s) is closed in s
         (dk-have! (cadr inst) (lambda () (fact 'carrier-is-closed 's) (ass)))
         ;; (b) every W_n is open
         (dk-have! (cadr (caddr inst))
           (lambda ()
             (let ((n (dk-di-var!)))
               (dk-lam-b!)
               (mac 'is-open)
               (dk-conj-close!
                (lambda ()
                  (let ((g (dk-goal)))
                    (cond
                     ((eq? (iec-head g) 'SUBSET)
                      (mac 'subset-def)
                      (let ((z (dk-di-var!)))
                        (iec-sep-open! z)
                        (ass)))
                     ((eq? (iec-head g) 'FORALL)
                      (let* ((y (dk-di-var!))
                             (yin (iec-sep-open! y))
                             (xr (iec-centre!))
                             (x (car xr)) (r (cadr xr))
                             (dxy (iec-ds x y))
                             (rho (list '- r dxy)))
                        (fact 'metric-dist-real 's x y)
                        (fact 'rr-pos-rr-in-rr r)
                        (fact 'rr-sub-in-rr r dxy)
                        (dk-have! (list '< 0 rho)
                          (lambda () (dk-ineq! (list '< dxy r) (list 'IN dxy 'RR) (list 'IN r 'RR)
                                               (list 'IN rho 'RR))))
                        (fact 'rr-pos-rr-of-lt rho)
                        (ew rho)
                        (dk-conj-close!
                         (lambda ()
                           (if (eq? (iec-head (dk-goal)) 'SUBSET)
                               (begin
                                 (mac 'subset-def)
                                 (let* ((z (dk-di-var!))
                                        (dyz (iec-ds y z))
                                        (dxz (iec-ds x z)))
                                   (mac-h 'ball-membership (list 'IN z (list 'BALL 's y rho)))
                                   (dk-split-all!)
                                   (fact 'metric-dist-real 's y z)
                                   (fact 'metric-dist-real 's x z)
                                   (dk-have! (list 'AND (list '<= dyz rho) (list 'NOT (list '= dyz rho)))
                                     (lambda () (dk-conj-close! (lambda () (ass)))))
                                   (fact 'rr-le-ne-lt dyz rho)
                                   (fact 'metric-triangle 's x y z)
                                   (iec-into-w! x r
                                     (lambda ()
                                       (dk-ineq! (list '<= dxz (list '+ dxy dyz))
                                                 (list '< dyz rho)
                                                 (list 'IN dxy 'RR) (list 'IN dyz 'RR) (list 'IN dxz 'RR)
                                                 (list 'IN r 'RR) (list 'IN rho 'RR))))))
                               (ass))))))
                     (#t (ass)))))))))
         ;; (c) the W_n cover pts(s)
         (dk-have! (cadr (caddr (caddr inst)))
           (lambda ()
             (let* ((x (dk-di-var!))
                    (dl (dk-skolem! (dk-apply! iec-eq x c)))
                    (dclause (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h dl)))
                                      "the delta clause"))
                    (n (dk-skolem! (dk-apply! iec-pw x c))))
               (fact 'metric-self-zero 's x)
               (fact 'metric-dist-real 's x x)
               (fact 'rr-pos-rr-in-rr dl)
               (fact 'rr-lt-of-pos-rr dl)
               (ew n)
               (dk-conj-close!
                (lambda ()
                  (if (and (eq? (iec-head (dk-goal)) 'IN) (dk-contains? (dk-goal) 'VNB-LAMBDA))
                      (begin
                        (dk-lam-b!)
                        (iec-into-w! x dl
                          (lambda ()
                            (dk-ineq! (list '= (iec-ds x x) 0) (list '< 0 dl)
                                      (list 'IN (iec-ds x x) 'RR) (list 'IN dl 'RR)))))
                      (ass)))))))
         ;; (d) the threshold N
         (let* ((nf (dk-skolem! (dk-apply! inst)))
                (cover (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h nf)))
                                "the finite subcover clause")))
           (ew nf)
           (dk-conj-close!
            (lambda ()
              (if (not (eq? (iec-head (dk-goal)) 'FORALL))
                  (ass)
                  (let* ((pk (dk-peel!))
                         (k (cadr (car (filter (lambda (f) (and (eq? (iec-head f) 'IN) (eq? (caddr f) 'NN))) pk))))
                         (y (cadr (car (filter (lambda (f) (and (eq? (iec-head f) 'IN)
                                                                (equal? (caddr f) '(PTS s)))) pk))))
                         (n (dk-skolem! (dk-apply! cover y)))
                         (mem (dk-pick (lambda (h) (and (eq? (iec-head h) 'IN) (eq? (cadr h) y)
                                                        (dk-contains? h 'VNB-LAMBDA)))
                                       "y in L(n)")))
                    (dk-lam-b-h! mem)
                    (iec-sep-open! y)
                    (let* ((xr (iec-centre!))
                           (x (car xr)) (r (cadr xr))
                           (ecl (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h r)))
                                         "the equicontinuity clause of the centre"))
                           (tcl (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h x)
                                                          (not (dk-contains? h r)) (dk-contains? h 'g)))
                                         "the threshold clause of the centre"))
                           (ny (dk-skolem! (dk-apply! iec-pw y c)))
                           (ycl (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h ny)))
                                         "the threshold clause at y"))
                           (l (list '+ n ny))
                           (Fky (iec-F k y)) (Fkx (iec-F k x)) (gx (iec-g x)) (gy (iec-g y))
                           (Flx (iec-F l x)) (Fly (iec-F l y)))
                      (dk-have! (list 'AND (list 'IN n 'NN) (list 'IN ny 'NN))
                        (lambda () (dk-conj-close! (lambda () (ass)))))
                      (fact 'nn-add-closed n ny)
                      (dk-have! (list '<= n k) (lambda () (dk-nn! (list '< n nf) (list '<= nf k))))
                      (dk-have! (list '<= n l) (lambda () (dk-nn!)))
                      (dk-have! (list '<= ny l) (lambda () (dk-nn!)))
                      ;; the five hops
                      (dk-apply! ecl k y)
                      (dk-apply! ecl l y)
                      (dk-apply! tcl k)
                      (dk-apply! tcl l)
                      (dk-apply! ycl l)
                      ;; the points of t
                      (for-each (lambda (j)
                                  (fact 'fun-apply-type-c 'fam 'NN '(FUN (PTS s) (PTS t)) j)
                                  (fact 'fun-apply-type-c (list 'fam j) '(PTS s) '(PTS t) x)
                                  (fact 'fun-apply-type-c (list 'fam j) '(PTS s) '(PTS t) y))
                                (list k l))
                      (fact 'fun-apply-type-c 'g '(PTS s) '(PTS t) x)
                      (fact 'fun-apply-type-c 'g '(PTS s) '(PTS t) y)
                      (fact 'metric-triangle 't Fky Fkx gy)
                      (fact 'metric-triangle 't Fkx gx gy)
                      (fact 'metric-triangle 't gx Flx gy)
                      (fact 'metric-triangle 't Flx Fly gy)
                      (fact 'metric-sym 't Fky Fkx)
                      (fact 'metric-sym 't gx Flx)
                      (let ((ds (list (iec-dt Fky gy) (iec-dt Fky Fkx) (iec-dt Fkx gy) (iec-dt Fkx gx)
                                      (iec-dt gx gy) (iec-dt gx Flx) (iec-dt Flx gy) (iec-dt Flx Fly)
                                      (iec-dt Fly gy) (iec-dt Fkx Fky) (iec-dt Flx gx))))
                        (for-each (lambda (d) (fact 'metric-dist-real 't (cadr d) (caddr d))) ds)
                        (fact 'rr-pos-rr-in-rr c)
                        (apply dk-ineq!
                               (append
                                (list (list '<= (iec-dt Fky gy) (list '+ (iec-dt Fky Fkx) (iec-dt Fkx gy)))
                                      (list '<= (iec-dt Fkx gy) (list '+ (iec-dt Fkx gx) (iec-dt gx gy)))
                                      (list '<= (iec-dt gx gy) (list '+ (iec-dt gx Flx) (iec-dt Flx gy)))
                                      (list '<= (iec-dt Flx gy) (list '+ (iec-dt Flx Fly) (iec-dt Fly gy)))
                                      (list '= (iec-dt Fky Fkx) (iec-dt Fkx Fky))
                                      (list '= (iec-dt gx Flx) (iec-dt Flx gx))
                                      (list '< (iec-dt Fkx Fky) c)
                                      (list '< (iec-dt Flx Fly) c)
                                      (list '<= (iec-dt Fkx gx) c)
                                      (list '<= (iec-dt Flx gx) c)
                                      (list '<= (iec-dt Fly gy) c)
                                      (list '= (list '+ c c) h2)
                                      (list '= (list '+ h2 h2) h1)
                                      (list '= (list '+ h1 h1) eps)
                                      (list '< 0 c)
                                      (list 'IN c 'RR) (list 'IN h2 'RR) (list 'IN h1 'RR)
                                      (list 'IN eps 'RR))
                                (map (lambda (d) (list 'IN d 'RR)) ds))))))))))))))
(qed 'equicont-ptwise-implies-uniform)
(topic! 'equicont-ptwise-implies-uniform 'analysis)
(alias! 'equicont-ptwise-implies-uniform
        "on a compact space an equicontinuous sequence converging pointwise converges uniformly")

;;; =====================================================================
;;; (3) Prop 3.33
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL fam (FORALL g
     (IMPLIES (IS-COMPACT s)
       (IMPLIES (IS-EQUICONTINUOUS s t fam)
         (IFF (CONVERGES-PTWISE-TO s t fam g)
              (CONVERGES-UNIFORMLY-TO s t fam g))))))))))
(dk-peel!)
(fact 'equicont-ptwise-implies-uniform 's 't 'fam 'g)
(fact 'uniform-conv-implies-ptwise 's 't 'fam 'g)
(for-each (lambda (n) (if (not (sequent-node-grounded? n)) (begin (dk-focus! n) (prop))))
          (dk-opened (lambda () (di))))
(qed 'equicont-compact-ptwise-iff-uniform)
(topic! 'equicont-compact-ptwise-iff-uniform 'analysis)
(alias! 'equicont-compact-ptwise-iff-uniform
        "on a compact space pointwise and uniform convergence agree for an equicontinuous sequence")

;;; =====================================================================
;;; (4) the notes' wording: a sequence in an equicontinuous SET E
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL es (FORALL fam
     (IMPLIES (IS-EQUICONTINUOUS-SET s t es)
       (IMPLIES (IN fam (FUN NN es))
         (IS-EQUICONTINUOUS s t fam)))))))))
(dk-peel!)
(iec-iff-rhs! (dk-cite! 'is-equicontinuous-set 's 't 'es))
(define iec-sc (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h 'POS-RR))) "the set clause"))
(dk-close-if! (lambda () (fact 'fun-codomain-superset 'fam 'NN 'es '(FUN (PTS s) (PTS t)))) (lambda () #t))
(mac 'is-equicontinuous)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (iec-head (dk-goal)) 'FORALL))
       (ass)
       (let* ((pl (dk-peel!))
              (x (cadr (car (filter (lambda (f) (eq? (iec-head f) 'IN)) pl))))
              (e (cadr (car (filter (lambda (f) (eq? (iec-head f) 'POS-RR)) pl))))
              (d (dk-skolem! (dk-apply! iec-sc x e)))
              (dcl (dk-pick (lambda (h) (and (eq? (iec-head h) 'FORALL) (dk-contains? h d))) "the delta clause")))
         (ew d)
         (dk-conj-close!
          (lambda ()
            (if (not (eq? (iec-head (dk-goal)) 'FORALL))
                (ass)
                (let* ((pk (dk-peel!))
                       (k (cadr (car (filter (lambda (f) (and (eq? (iec-head f) 'IN) (eq? (caddr f) 'NN))) pk))))
                       (y (cadr (car (filter (lambda (f) (and (eq? (iec-head f) 'IN) (equal? (caddr f) '(PTS s)))) pk)))))
                  (fact 'fun-apply-type-c 'fam 'NN 'es k)
                  (dk-close-if! (lambda () (inst*! dcl (list 'fam k) y)) ass)))))))))
(qed 'equicontinuous-set-sequence)
(topic! 'equicontinuous-set-sequence 'analysis)
(alias! 'equicontinuous-set-sequence "a sequence in an equicontinuous set is equicontinuous")

(sp (make-wff '(FORALL s (FORALL t (FORALL es (FORALL fam (FORALL g
     (IMPLIES (IS-COMPACT s)
       (IMPLIES (IS-EQUICONTINUOUS-SET s t es)
         (IMPLIES (IN fam (FUN NN es))
           (IFF (CONVERGES-PTWISE-TO s t fam g)
                (CONVERGES-UNIFORMLY-TO s t fam g))))))))))))
(dk-peel!)
(fact 'equicontinuous-set-sequence 's 't 'es 'fam)
(fact 'equicont-compact-ptwise-iff-uniform 's 't 'fam 'g)
(prop)
(qed 'equicont-set-compact-ptwise-iff-uniform)
(topic! 'equicont-set-compact-ptwise-iff-uniform 'analysis)
(alias! 'equicont-set-compact-ptwise-iff-uniform
        "on a compact space pointwise and uniform convergence agree for sequences in an equicontinuous set")
