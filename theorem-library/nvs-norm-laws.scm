;;; nvs-norm-laws.scm -- THE NORM LAWS OF A REAL NORMED VECTOR SPACE, in ONE
;;; place.  Rake batch 8, assignment 8-K1.
;;;
;;;   nvs-vnrm-triangle   ||x + y|| <= ||x|| + ||y||
;;;   nvs-vnrm-homog-c    ||r.x|| = |r| * ||x||        (r in carr(scal m))
;;;   nvs-vnrm-homog      ||r.x|| = |r| * ||x||        (r in RR)
;;;   nvs-vnrm-vzero      ||vzero(m)|| = 0
;;;
;;; All four are projections of the IS-NORMED-VECTOR-SPACE unfold (the RR form
;;; of homogeneity is the carrier form plus nvs-scal-carr).  They were proved
;;; THREE times on 2026-09-19, under three prefixes, by three agents:
;;;
;;;   nvs-vnrm-triangle  <- directional-derivative.scm (7-F), hbg-vnrm-triangle
;;;                         (rake-hb-gap.scm, 7-D)
;;;   nvs-vnrm-homog-c   <- directional-derivative.scm (7-F), hbg-vnrm-homog-c
;;;                         (7-D), lfe-vnrm-homog-c (rake-line-functional, 7-C)
;;;   nvs-vnrm-homog     <- directional-derivative.scm (7-F), hbg-vnrm-homog
;;;                         (7-D), lfe-vnrm-homog (7-C)
;;;   nvs-vnrm-vzero     <- lfe-vnrm-vzero (7-C)
;;;
;;; The proofs kept here are the directional-derivative ones (7-F), except
;;; nvs-vnrm-vzero, which only 7-C proved.  Every duplicate is CUT from its old
;;; file and its citations re-pointed here, so install-duplicate-audit stays at
;;; zero.
;;;
;;; THE METRIC SECTION (added 2026-09-20, batch 12-A).  The four laws of the
;;; metric NVS-METRIC-SPACE(m) = [VEC(m), (x,y) |-> ||x (-) y||] now live here
;;; too, at the end of the file:
;;;
;;;   nvs-ms-pts             PTS(NVS-METRIC-SPACE m) == VEC(m)
;;;   nvs-metric-distance    d(u,v) = ||u (-) v||          (strict `=')
;;;   nvs-metric-distance-q  the same, as a QUASI-equation (`==')
;;;   nvs-dist-shift         d(u, u (+) w) = ||w||
;;;
;;; They were scattered over two proof files -- nvs-ms-pts and
;;; nvs-metric-distance-q in theorem-library/vector-taylor-proof.scm,
;;; nvs-metric-distance and nvs-dist-shift in
;;; theorem-library/directional-derivative.scm -- for ONE reason: the
;;; def-functoid NVS-METRIC-SPACE was declared inside vector-taylor-proof.scm,
;;; so nothing stated with it could load above that file.  The functoid is now
;;; structure-library/nvs-metric.scm and rake-norm-metrics.scm (nvs-metric-is-ms,
;;; which nvs-dist-shift cites) loads immediately above this file, so the laws
;;; come home.  Every old citation site keeps its name.
;;;
;;; LOAD WINDOW.  lo = theorem-library/rake-norm-metrics (nvs-metric-is-ms, the
;;; latest citation; then nvs-scal-carr of theorem-library/nvs-act-laws;
;;; everything else is the IS-NORMED-VECTOR-SPACE macete of
;;; structure-library/normed-vector-space, the NVS-METRIC-SPACE macete of
;;; structure-library/nvs-metric, metric-sym of structure-library/metric-laws
;;; and the dk- kit).  hi = theorem-library/rake-hb-gap, the earliest citer (it
;;; used to prove hbg-vnrm-triangle / -homog / -homog-c itself).  Slot:
;;; immediately after "theorem-library/rake-norm-metrics".
;;; No late tactic is used (no contra / prep / ineq-supply).
;;;
;;; Helper prefix `r8f-' (the block is directional-derivative's, copied with the
;;; proofs so that no proof text changed); `r8c-' names are aliases for the one
;;; proof taken from rake-line-functional.scm.

;;; ---- file-local driver helpers ---------------------------------------

(define r8f-nvs '(IS-NORMED-VECTOR-SPACE m))

(define (r8f-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space r8f-nvs)
  (dk-split-all!))

(define (r8f-check! name)
  (if (not (proof-done? *ps*))
      (error "nvs-norm-laws: proof did not close" name
             (expression->string (dk-goal))))
  (qed name)
  (topic! name 'analysis))

;; the innermost consequent of a FORALL/IMPLIES tower
(define (r8f-core fm)
  (cond ((and (pair? fm) (eq? (car fm) 'FORALL)) (r8f-core (caddr fm)))
        ((and (pair? fm) (eq? (car fm) 'IMPLIES)) (r8f-core (caddr fm)))
        (#t fm)))

(define (r8f-eigen! vars)
  (let ((fv (free-vars (dk-goal))))
    (for-each (lambda (v)
                (if (not (memq v fv))
                    (error "nvs-norm-laws: eigenvariable not in goal" v
                           (expression->string (dk-goal)))))
              vars)))

;; A law of the IS-NORMED-VECTOR-SPACE unfold, instantiated at the goal's
;; eigenvariables and closed by `ass'.  FIND picks the law by its CONSEQUENT.
(define (r8f-project! name stmt find vars)
  (r8f-open! stmt)
  (r8f-eigen! vars)
  (let ((law (dk-pick (lambda (fm) (find (r8f-core fm))) name)))
    (apply dk-apply! law vars)
    (ass))
  (r8f-check! name))

;; (IN r (CARR (SCAL m))) from (IN r RR), by nvs-act-laws.scm's carrier read-off
(define (r8f-scalar! r)
  (have! (list 'IN r '(CARR (SCAL m)))
         (lambda () (mac 'nvs-scal-carr) (ass))))

(define r8c-open! r8f-open!)
(define (r8c-check! name) (r8f-check! name))
(define (r8c-law find what) (dk-pick (lambda (f) (find (r8f-core f))) what))

;;; ||x + y|| <= ||x|| + ||y||  -- the triangle law
(r8f-project! 'nvs-vnrm-triangle
  `(FORALL m (IMPLIES ,r8f-nvs
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (<= ((VNRM m) ((VADD m) x_ y_))
           (+ ((VNRM m) x_) ((VNRM m) y_)))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '<=)
                   (pair? (cadr c)) (equal? (car (cadr c)) '(VNRM m))
                   (pair? (cadr (cadr c)))
                   (equal? (car (cadr (cadr c))) '(VADD m))))
  '(x_ y_))

;;; ||r.x|| = |r| * ||x||  -- the homogeneity law, scalars in carr(scal m)
(r8f-project! 'nvs-vnrm-homog-c
  `(FORALL m (IMPLIES ,r8f-nvs
     (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((VNRM m) ((ACT m) r_ x_)) (* (abs r_) ((VNRM m) x_)))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '=)
                   (pair? (cadr c)) (equal? (car (cadr c)) '(VNRM m))
                   (pair? (cadr (cadr c)))
                   (equal? (car (cadr (cadr c))) '(ACT m))))
  '(r_ x_))

(sp (make-wff
  `(FORALL m (IMPLIES ,r8f-nvs
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((VNRM m) ((ACT m) r_ x_)) (* (abs r_) ((VNRM m) x_)))))))))))
(dk-peel!)
(r8f-eigen! '(r_ x_))
(r8f-scalar! 'r_)
(fact 'nvs-vnrm-homog-c 'm 'r_ 'x_)
(ass)
(r8f-check! 'nvs-vnrm-homog)

;;; ||vzero(m)|| = 0 -- the definiteness law at the zero vector
;;; (rake-line-functional.scm, 7-C).
(r8c-open! '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
   (= ((VNRM m) (VZERO m)) 0))))
(let ((law (r8c-law (lambda (c) (and (pair? c) (eq? (car c) 'IFF))) "the definiteness law")))
  (dk-apply! law '(VZERO m))
  (have! '(= (VZERO m) (VZERO m)) (lambda () (rfl)))
  (prop))
(r8c-check! 'nvs-vnrm-vzero)

;;; =====================================================================
;;; THE METRIC LAWS of NVS-METRIC-SPACE (structure-library/nvs-metric.scm).
;;; Moved here 2026-09-20 (batch 12-A) from vector-taylor-proof.scm (the two
;;; read-offs) and directional-derivative.scm (the two distance laws); the
;;; proof text is unchanged except that both files' local `check!' helpers are
;;; this file's `r8f-check!'.
;;; =====================================================================

;;; PTS(NVS-METRIC-SPACE m) == VEC(m).  NVS-METRIC-SPACE is a def-functoid
;;; LIST, so `slot-h' has no projection for it; this equation is the macete
;;; that reads the carrier off (bdd-metric-carrier's recipe).
(sp (make-wff '(FORALL m (== (PTS (NVS-METRIC-SPACE m)) (VEC m)))))
(di)
(mac 'NVS-METRIC-SPACE)   ; (== (PTS (LIST (VEC m) (VNB-LAMBDA ...))) (VEC m))
(slot 'PTS)               ; (== (nth 1 (LIST (VEC m) ...)) (VEC m))
(nth-r)                   ; (== (VEC m) (VEC m))
(qrfl)
(qed 'nvs-ms-pts)
(topic! 'nvs-ms-pts 'analysis)
(alias! 'nvs-ms-pts "the points of the norm metric space are the vectors")

;;; d(u,v) = ||u + (-v)|| in the norm metric  (nag-metric-distance's recipe)
(sp (make-wff
  `(FORALL m (IMPLIES ,r8f-nvs
     (FORALL u_ (IMPLIES (IN u_ (VEC m))
     (FORALL v_ (IMPLIES (IN v_ (VEC m))
       (= ((DIST (NVS-METRIC-SPACE m)) u_ v_)
          ((VNRM m) ((VADD m) u_ ((VNEG m) v_))))))))))))
(dk-peel!)
(r8f-eigen! '(u_ v_))
(fact 'nvs-vneg-in-vec 'm 'v_)
(fact 'nvs-vadd-in-vec 'm 'u_ '((VNEG m) v_))
(fact 'vnrm-real 'm '((VADD m) u_ ((VNEG m) v_)))
(mac 'NVS-METRIC-SPACE)
(slot 'DIST)
(nth-r)
(lam-b)
(rfl)
(r8f-check! 'nvs-metric-distance)

;;; The same distance as a QUASI-equation (`nvs-metric-distance-q', renamed
;;; from r8e-nvs-dist in batch 8).  The two are NOT the same statement: the
;;; strict `=' form above asserts definedness, this one does not, and the
;;; citers differ.  Unfold, slot, nth-r -- nvs-ms-pts' recipe one storey down
;;; -- then beta at the pair.
(sp (make-wff
     '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
        (FORALL u_ (IMPLIES (IN u_ (VEC m))
        (FORALL v_ (IMPLIES (IN v_ (VEC m))
          (== ((DIST (NVS-METRIC-SPACE m)) u_ v_)
              ((VNRM m) ((VADD m) u_ ((VNEG m) v_))))))))))))
(dk-peel!)
(fact 'pair-in-cartesian '(VEC m) '(VEC m) 'u_ 'v_)
(mac 'NVS-METRIC-SPACE)
(slot 'DIST)
(nth-r)
(lam-b)
(qrfl)
(r8f-check! 'nvs-metric-distance-q)

;;; d(u, u + w) = ||w||
(sp (make-wff
  `(FORALL m (IMPLIES ,r8f-nvs
     (FORALL u_ (IMPLIES (IN u_ (VEC m))
     (FORALL w_ (IMPLIES (IN w_ (VEC m))
       (= ((DIST (NVS-METRIC-SPACE m)) u_ ((VADD m) u_ w_))
          ((VNRM m) w_))))))))))
(dk-peel!)
(r8f-eigen! '(u_ w_))
(fact 'nvs-metric-is-ms 'm)
(fact 'nvs-vadd-in-vec 'm 'u_ 'w_)
(fact 'nvs-vneg-in-vec 'm 'u_)
(fact 'vnrm-real 'm 'w_)
(let ((pv '((VADD m) u_ w_)))
  (for-each (lambda (z)
              (have! (list 'IN z '(PTS (NVS-METRIC-SPACE m)))
                     (lambda () (mac 'nvs-ms-pts) (ass))))
            (list 'u_ pv))
  (subst (dk-fact! 'metric-sym '(NVS-METRIC-SPACE m) 'u_ pv))
  (subst (dk-fact! 'nvs-metric-distance 'm pv 'u_))
  ;; (u + w) + (-u) = w
  (subst (dk-fact! 'nvs-vadd-comm 'm 'u_ 'w_))
  (subst (dk-fact! 'nvs-vadd-assoc 'm 'w_ 'u_ '((VNEG m) u_)))
  (subst (dk-fact! 'nvs-vneg-right 'm 'u_))
  (subst (dk-fact! 'nvs-vzero-right 'm 'w_))
  (rfl))
(r8f-check! 'nvs-dist-shift)
