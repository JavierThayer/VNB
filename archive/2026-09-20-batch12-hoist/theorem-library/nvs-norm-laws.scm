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
;;; NOT HERE, and why.  The two METRIC laws of a normed vector space --
;;; `nvs-metric-distance' (d(u,v) = ||u + (-v)||) and `nvs-dist-shift'
;;; (d(u, u+w) = ||w||), with the quasi-equation twin `nvs-metric-distance-q'
;;; -- cannot join them.  NVS-METRIC-SPACE is a `def-functoid' declared in
;;; theorem-library/vector-taylor-proof.scm:28, and nvs-dist-shift also needs
;;; `nvs-metric-is-ms' (theorem-library/rake-norm-metrics.scm), both of which
;;; load far below this file.  They stay where they are:
;;; nvs-metric-distance-q in vector-taylor-proof.scm, nvs-metric-distance and
;;; nvs-dist-shift in directional-derivative.scm.  Hoisting the
;;; NVS-METRIC-SPACE def-functoid into structure-library is the prerequisite
;;; for a metric section here, and is a design decision, not a repair.
;;;
;;; LOAD WINDOW.  lo = theorem-library/nvs-act-laws (nvs-scal-carr, the latest
;;; citation; everything else is the IS-NORMED-VECTOR-SPACE macete of
;;; structure-library/normed-vector-space and the dk- kit).  hi =
;;; theorem-library/rake-hb-gap, the earliest citer (it used to prove
;;; hbg-vnrm-triangle / -homog / -homog-c itself).  Recommended slot:
;;; immediately after "theorem-library/nvs-act-laws".
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
