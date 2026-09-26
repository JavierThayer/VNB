;;; rake-cont-preimage.scm -- continuous-implies-open-preimage, PROVEN.
;;;
;;;   continuous-implies-open-preimage:
;;;     forall s, t, f.  IS-CONTINUOUS(s,t,f)  =>
;;;       forall V.  IS-OPEN(t,V)  =>  IS-OPEN(s, PREIMAGE(s,f,V))
;;;
;;; Statement copied LITERALLY from structure-library/metric-open-sets.scm:91, the
;;; last support left in that file.  It was warranted `informal': a machine proof
;;; existed (archive/calculus-pre-rename/prop-3-15-proof.scm) and stopped running at the
;;; PTS/DIST accessor rename, and nobody re-ran it.  This is not that file revived --
;;; the argument is rewritten as the MIRROR of `open-preimage-implies-continuous'
;;; (theorem-library/rake-open-sets.scm), whose helpers this one reuses by shape.
;;;
;;; THE ARGUMENT.  Let a be in PREIMAGE(s,f,V), so f(a) is in the open V, which
;;; therefore holds a ball BALL(t, f(a), eps) about it.  Continuity at a is stated
;;; with a NON-STRICT bound -- d(t)(f a, f b) <= h -- while ball membership is
;;; STRICT, so continuity is invoked at h = eps/2 (`dk-halve!'), not at eps, and
;;; `ball-mem-from-le' bridges h < eps back to strict membership.  The delta it
;;; returns is the radius: every b in BALL(s,a,delta) satisfies d(s)(a,b) <= delta
;;; (strict implies non-strict, the easy way round), so f(b) is in the eps-ball,
;;; hence in V, hence b is in the preimage.
;;; The other two conjuncts of IS-OPEN are bookkeeping: IS-METRIC-SPACE(s) is a
;;; typing conjunct of IS-CONTINUOUS, and PREIMAGE(s,f,V) subset PTS(s) is the
;;; first conjunct of its own membership law.
;;;
;;; THE WARRANT'S PLAN IS FOLLOWED EXCEPT IN ONE PLACE, and the difference is the
;;; point of the batch: it proposed `rr-pos-shrink' to shrink eps, which is the last
;;; of the five archimedean supports still ASSERTED (order-predicates.scm).
;;; `dk-halve!' does the same job through `rr-pos-halvable', PROVEN -- so this bill
;;; is `modulo 0' where the warrant's own route would have billed one leaf.
;;; `continuous-is-continuous-at' (also asserted, also named by the warrant) is
;;; likewise avoided: the pointwise conjunct is read off IS-CONTINUOUS in a `have!'
;;; lane, since `mac-h' is destructive and the hypothesis is wanted twice.
;;;
;;; WHAT IT CLEARS.  `continuous-implies-closed-preimage' (rake-open-sets.scm) bills
;;; exactly this one leaf; with this file it reads `modulo 0', and
;;; structure-library/metric-open-sets.scm holds no support at all.
;;;
;;; CITATIONS, with the 0-based load position of the file that installs each:
;;;   primitive/base:      subset-def, rr order axioms (through `ineq').
;;;   definitional:        preimage-membership (metric-open-sets 46, stamped in
;;;                        structure-library/definitional-reclass), the is-open /
;;;                        is-continuous / is-continuous-at unfolds.
;;;   proven:  fun-apply-type-c 163 (fun-apply-type-proof),
;;;            rr-pos-rr-in-rr / rr-lt-of-pos-rr 178 (pos-rr-bridges),
;;;            rr-pos-halvable 185 (rr-halving, through dk-halve!),
;;;            subset-mem-fwd 193 (subset-lemmas),
;;;            ball-membership + ball-mem-from-le 261 (rake-balls).
;;;   oracle:  ineq.
;;;   NOTHING ASSERTED.
;;;
;;; LOAD WINDOW [262, 279).
;;;   lo = 262: theorem-library/rake-balls (261) is the latest citation.
;;;   hi = 279: theorem-library/rake-open-sets, whose
;;;     `continuous-implies-closed-preimage' cites this theorem; the only other
;;;     citer is metric-top-functorial-proof (474).
;;;   The batch's other five leaves cite nothing above subset-lemmas (193) and are
;;;   in theorem-library/rake-analysis2.scm, window [194, 252) -- two files because
;;;   theorem-library/card-finite (259) cites `bijection-compose', which puts that
;;;   file's ceiling BELOW this file's floor.
;;;
;;; Helper prefix: rkl-.

;;; --- file-local helpers (rkl-) -------------------------------------------

(define (rkl-head? f h) (and (pair? f) (eq? (car f) h)))
(define (rkl-in? f set) (and (rkl-head? f 'IN) (equal? (caddr f) set)))

;; goal (SUBSET A B): unfold and introduce the element; return the landed (IN z A).
(define (rkl-subset-elt!)
  (mac 'subset-def)
  (dk-landed-1 (lambda () (di))))

;; 1-based context index of FORM, for `ineq' (ineq-oracle.scm:206).
(define (rkl-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rkl-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))

;; (IS-OPEN s U) in context -> its conjuncts, split, returned.  DESTRUCTIVE.
(define (rkl-open-h! op) (dk-split! (dk-landed-1 (lambda () (mac-h 'is-open op)))))

;; the interior universal of an unfolded IS-OPEN, picked by the SET its guard
;; ranges over -- never by head alone.
(define (rkl-interior-univ set)
  (dk-pick (lambda (p)
             (and (rkl-head? p 'FORALL) (rkl-head? (caddr p) 'IMPLIES)
                  (let ((ante (cadr (caddr p))))
                    (and (rkl-head? ante 'IN) (equal? (caddr ante) set)))))
           "the interior universal"))

;; the eps-universal of an unfolded IS-CONTINUOUS-AT.
(define (rkl-eps-univ)
  (dk-pick (lambda (p)
             (and (rkl-head? p 'FORALL) (rkl-head? (caddr p) 'IMPLIES)
                  (rkl-head? (cadr (caddr p)) 'POS-RR)))
           "the eps universal of IS-CONTINUOUS-AT"))

;;; =====================================================================
;;; continuous-implies-open-preimage
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-CONTINUOUS s t f)
       (FORALL V (IMPLIES (IS-OPEN t V)
         (IS-OPEN s (PREIMAGE s f V))))))))))
(dk-peel!)

(define rkl-cont (dk-pick (dk-head? 'IS-CONTINUOUS) "the continuity hypothesis"))
(define rkl-open (dk-pick (dk-head? 'IS-OPEN) "the open-set hypothesis"))
(define rkl-v    (caddr rkl-open))
(define rkl-typings
  '(AND (IS-METRIC-SPACE s) (AND (IS-METRIC-SPACE t) (IN f (FUN (PTS s) (PTS t))))))
(define rkl-at-univ
  '(FORALL a_ (IMPLIES (IN a_ (PTS s)) (IS-CONTINUOUS-AT s t f a_))))

;; Read the typings and the pointwise-continuity universal off IS-CONTINUOUS in
;; `have!' LANES: mac-h REPLACES what it unfolds, and the hypothesis is wanted twice.
(have! rkl-typings
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous rkl-cont))))
    (dk-conj-close!)))
(dk-split! rkl-typings)
(have! rkl-at-univ
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous rkl-cont))))
    (ass)))

;; goal (SUBSET (BALL s a delta) (PREIMAGE s f v)), with continuity's delta-universal
;; (bound h), (< h eps) and (SUBSET (BALL t (f a) eps) v) in context.
(define (rkl-ball-subset! a delta h eps)
  (let* ((mem (rkl-subset-elt!))                   ; (IN b (BALL s a delta))
         (b   (cadr mem)))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'ball-membership mem))))
    (dk-apply! (dk-pick (lambda (p)
                          (and (rkl-head? p 'FORALL) (rkl-head? (caddr p) 'IMPLIES)
                               (rkl-in? (cadr (caddr p)) '(PTS s))))
                        "the delta universal")
               b)                                  ; d(t)(f a, f b) <= h
    (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) a)
    (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) b)
    ;; ball-mem-from-le's premise is one AND; `fact' will not split one.
    (have! `(AND (IN (f ,b) (PTS t))
             (AND (IN ,h RR)
             (AND (IN ,eps RR)
             (AND (<= ((DIST t) (f ,a) (f ,b)) ,h)
                  (< ,h ,eps))))))
    (fact 'ball-mem-from-le 't `(f ,a) `(f ,b) h eps)
    (fact 'subset-mem-fwd `(BALL t (f ,a) ,eps) rkl-v `(f ,b))
    (mac 'preimage-membership)
    (dk-conj-close!)))

;; goal (FORSOME r (AND (POS-RR r) (SUBSET (BALL s a r) (PREIMAGE s f v)))).
(define (rkl-interior!)
  (let* ((mem (car (dk-peel!)))                    ; (IN a (PREIMAGE s f v))
         (a   (cadr mem)))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'preimage-membership mem))))
    (rkl-open-h! rkl-open)
    (let* ((ex  (dk-apply! (rkl-interior-univ rkl-v) `(f ,a)))
           (eps (dk-skolem! ex)))
      (fact 'rr-pos-rr-in-rr eps)
      (let ((h (dk-halve! eps)))                   ; h + h = eps, 0 < h
        (have! `(< ,h ,eps)
          (lambda () (ineq (rkl-idx `(= (+ ,h ,h) ,eps)) (rkl-idx `(< 0 ,h)))))
        (dk-apply! rkl-at-univ a)                  ; IS-CONTINUOUS-AT s t f a
        (dk-split! (dk-landed-1
                    (lambda () (mac-h 'is-continuous-at `(IS-CONTINUOUS-AT s t f ,a)))))
        (let* ((dex   (dk-apply! (rkl-eps-univ) h))
               (delta (dk-skolem! dex)))
          (ew delta)
          (dk-conj-close!
           (lambda ()
             (if (rkl-head? (dk-goal) 'POS-RR)
                 (ass)
                 (rkl-ball-subset! a delta h eps)))))))))

(mac 'is-open)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((rkl-head? g 'IS-METRIC-SPACE) (ass))
      ((rkl-head? g 'SUBSET)                       ; the preimage is a SEP over PTS(s)
       (let ((mem (rkl-subset-elt!)))
         (dk-split! (dk-landed-1 (lambda () (mac-h 'preimage-membership mem))))
         (ass)))
      ((rkl-head? g 'FORALL) (rkl-interior!))
      (#t (error "continuous-implies-open-preimage: unexpected conjunct"
                 (expression->string g)))))))
(qed 'continuous-implies-open-preimage)
(gloss! 'continuous-implies-open-preimage
  "A continuous map pulls open sets back to open sets -- Prop 3.15 (1) => (2).
   The eps-ball about f(a) inside the open target set is reached with room to
   spare: continuity is invoked at eps/2, so its non-strict bound still lands
   strictly inside.")
(topic! 'continuous-implies-open-preimage 'topology)
