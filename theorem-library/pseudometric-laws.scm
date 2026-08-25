;;; pseudometric-laws.scm -- the FOUR PSEUDOMETRIC LAWS, proven by projecting
;;; the `is-pseudometric' property, exactly as structure-library/metric-laws.scm
;;; projects `is-metric'.
;;;
;;;   pseudometric-self-zero   d(u,u) = 0
;;;   pseudometric-pos         0 <= d(u,v)
;;;   pseudometric-sym         d(u,v) = d(v,u)
;;;   pseudometric-triangle    d(u,w) <= d(u,v) + d(v,w)
;;;
;;; The metric family (metric-laws.scm) is stated about a metric SPACE -- the
;;; arguments are a structure s and points of PTS(s).  These are stated about a
;;; bare DISTANCE FUNCTION and a carrier, which is what `is-pseudometric' itself
;;; takes, because that is the form the consumers need: the k-th entry of a
;;; C-METRIC-SPACE's DISTS is a function in FUN(CARTESIAN(PTS,PTS), RR) and not a
;;; structure, and pseudometric.scm's IS-COUNTABLE-PSEUDOMETRIC-FAMILY reaches
;;; its distances as (DIST (fam n)), also a bare function.  A PSEUDOMETRIC-SPACE
;;; instance gets them by citing at (DIST s), (PTS s).
;;;
;;; The tree had NO projection of is-pseudometric at all: the predicate was
;;; introduced (2026-07-20) for the metrizability cluster, whose four statements
;;; are asserted supports, so nothing had ever needed to open it.
;;;
;;; All four are `modulo 0'.  Loads after structure-library/metric-laws (nothing
;;; is shared; the placement keeps the two families together) and needs only the
;;; interactive engine and operation-properties.

;;; ---- file-local driver helpers (the `pml-' prefix) -------------------

(define (pml-peel!)
  (let lp ((n 0))
    (if (and (< n 12) (memq (car (dk-goal)) '(FORALL IMPLIES)))
        (begin (di) (lp (+ n 1))))))

(define (pml-find pred)
  (let lp ((l (dk-asms)))
    (cond ((null? l) #f) ((pred (car l)) (car l)) (else (lp (cdr l))))))

;; ai every conjunction in the context, to exhaustion
(define (pml-split-all!)
  (let lp ()
    (let ((a (pml-find (lambda (f) (eq? (car f) 'AND)))))
      (if a (begin (ai a) (lp))))))

;; Instantiate the NEWEST context universal guarded by (IN _ crr) at V.
;; Newest-first is the peel order of the unfolded is-pseudometric body -- the
;; u-universal is landed first, its v-universal next, its w-universal last --
;; so the caller's variable list (u v w) meets them in the right order.  It
;; ERRORS on a miss: a silent no-op here would leave `ass' looking for a
;; hypothesis nobody built.
(define (pml-inst! v)
  (let ((u (pml-find (lambda (f)
                       (and (eq? (car f) 'FORALL)
                            (let ((b (caddr f)))
                              (and (pair? b) (eq? (car b) 'IMPLIES)
                                   (equal? (cadr b) (list 'IN (cadr f) 'crr)))))))))
    (if (not u) (error "pml-inst!: no crr-guarded universal in context" v))
    (inst+ u v)
    (pml-split-all!)))

(define (pml-prove! name stmt vars)
  (sp (make-wff stmt))
  (pml-peel!)
  (mac-h 'is-pseudometric '(IS-PSEUDOMETRIC dst crr))
  (for-each (lambda (v) (pml-inst! v)) vars)
  (ass)
  (qed name)
  (topic! name 'analysis))

;;; =====================================================================

(pml-prove! 'pseudometric-self-zero
  "forall([dst, crr], is-pseudometric(dst, crr) implies
     forall([u in crr], dst(u, u) = 0))"
  '(u))
(alias! 'pseudometric-self-zero "a pseudometric vanishes on the diagonal")

(pml-prove! 'pseudometric-pos
  "forall([dst, crr], is-pseudometric(dst, crr) implies
     forall([u in crr, v in crr], 0 <= dst(u, v)))"
  '(u v))
(alias! 'pseudometric-pos "a pseudometric is nonnegative")

(pml-prove! 'pseudometric-sym
  "forall([dst, crr], is-pseudometric(dst, crr) implies
     forall([u in crr, v in crr], dst(u, v) = dst(v, u)))"
  '(u v))
(alias! 'pseudometric-sym "a pseudometric is symmetric")

(pml-prove! 'pseudometric-triangle
  "forall([dst, crr], is-pseudometric(dst, crr) implies
     forall([u in crr, v in crr, w in crr],
       dst(u, w) <= dst(u, v) + dst(v, w)))"
  '(u v w))
(alias! 'pseudometric-triangle "the triangle inequality for a pseudometric")
