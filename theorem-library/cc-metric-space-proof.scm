;;; cc-metric-space-proof.scm -- IS-METRIC-SPACE(CC-MS), PROVEN.
;;;
;;; It was an AXIOM -- `theory-add-axiom!' in structure-library/complex.scm with
;;; no `warrant!' at all, so it billed `trust: none', the weakest report there
;;; is, and it was one of the three such bills left in the library.
;;;
;;; WHY IT IS AVAILABLE NOW.  The distance on CC-MS is `magnitude(x - y)', and
;;; until 2026-08-17 `magnitude' was characterised by NORM-SHAPED AXIOMS: they
;;; said it was *a* norm and never said which.  With real-part / imag-part
;;; defined, `magnitude' is now DEFINED (complex.scm, magnitude-def) and its
;;; laws are theorems (theorem-library/cc-magnitude.scm) -- in particular
;;; `cc-magnitude-triangle', which is two-dimensional Cauchy-Schwarz done as a
;;; RING IDENTITY, (x^2+y^2)(u^2+v^2) - (xu+yv)^2 = (xv-yu)^2, and nothing more
;;; abstract than that.  So the three metric laws that carry content are now
;;; citations, and this file is the assembly.
;;;
;;; It is the exact analogue of theorem-library/rr-metric-space-proof.scm, which
;;; retired the same axiom one system down, and the driver is that file's with
;;; `abs' replaced by `magnitude' and `ineq' -- which has no complex analogue --
;;; replaced by `crs'.  The RR proof could finish a metric law by linear
;;; arithmetic over the order; CC has no order, so every step here is either a
;;; magnitude theorem or a commutative-ring identity.
;;;
;;; THE FOUR CONJUNCTS of the generated IS-METRIC-SPACE IFF:
;;;
;;;   length(CC-MS) = 2               unfold the tuple, `len-r', `arith'.
;;;   PTS(CC-MS) in SET               cc-is-set (primitive).
;;;   DIST(CC-MS) in FUN(CCxCC, RR)   `lam-t': |x-y| is real pointwise
;;;                                   (cc-sub-in-cc + cc-magnitude-closed), and
;;;                                   CCxCC is a set (cartesian-set-iff).
;;;   is-metric(DIST(CC-MS), CC)      the five laws, after `lam-b' reduces
;;;                                   d(u,v) to magnitude(u-v).
;;;
;;;   d(u,u) = 0        cc-magnitude-zero-iff, then u - u = 0 by `crs'.
;;;   0 <= d(u,v)       cc-magnitude-nonneg.
;;;   separation        cc-sub-zero-eq below -- the one place CC needs a lemma
;;;                     the RR proof got from the oracle.
;;;   symmetry          cc-magnitude-neg at u-v, since -(u-v) = v-u by `crs'.
;;;   triangle          cc-magnitude-triangle at (u-v) + (v-w), since
;;;                     u-w = (u-v) + (v-w) by `crs'.
;;;
;;; WHAT IT COSTS.  The four sqrt supports that `magnitude' now discloses
;;; (sqrt-nonneg / sqrt-sq / sqrt-of-sq / sqrt-mono, real-powers.scm, all
;;; `well-known'), and nothing else.  That is a strict improvement on the axiom
;;; it replaces, which billed `trust: none' -- and it moves the whole complex
;;; metric layer onto the SQRT question, which is the honest place for it: SQRT
;;; is the one symbol here nobody has derived from order completeness, and `ivt'
;;; (proven 2026-08-17) is what will discharge it.
;;;
;;; Loads after cc-magnitude (the modulus laws), complex (CC-MS, magnitude-def),
;;; metric-laws / metric-space (is-metric), and driver-kit.

;;; ---- file-local driver helpers (the `cms-' prefix) -------------------

(define (cms-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-leaves)))
(define (cms-goal-of s) (wff-formula (sequent-node-assertion s)))
(define (cms-head g) (and (pair? g) (car g)))

;;; Focus the first open leaf satisfying PRED, and ERROR on a miss -- a focus
;;; helper that returns #f and leaves focus put hides every later mistake.
(define (cms-focus! pred)
  (let ((s (find-first (lambda (s) (pred (cms-goal-of s))) (cms-open))))
    (if (not s) (error "cms-focus!: no open leaf matches") (begin (dk-focus! s) s))))

(define (cms-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (cms-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 12)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (cms-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (cms-has-lambda-app? (car g)) (cms-has-lambda-app? (cdr g))))
        (else #f)))

;;; Beta-reduce to a fixpoint, guarded on PROGRESS (`lam-b' only warns when
;;; there is nothing to do, so a "while there is an application" loop spins).
(define (cms-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (cms-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; Decompose every open leaf whose goal is a FORALL, an IMPLIES or an AND,
;;; beta-reducing first so that what an IMPLIES lands is already magnitude-shaped
;;; rather than a lambda application nothing downstream can match.
(define (cms-drive!)
  (let loop ((fuel 200))
    (let ((s (find-first (lambda (s) (memq (cms-head (cms-goal-of s))
                                           '(FORALL IMPLIES AND)))
                         (cms-open))))
      (if (and s (> fuel 0))
          (begin (dk-focus! s) (cms-beta!)
                 (if (memq (cms-head (dk-goal)) '(FORALL IMPLIES AND)) (di) #t)
                 (loop (- fuel 1)))
          #t))))

;;; =====================================================================
;;; Two arithmetic lemmas CC lacks and RR did not need.
;;;
;;; The RR proof closed its typing and separation steps with `ineq', the linear
;;; oracle over the real ORDER.  CC has no order, so both come back as ordinary
;;; ring facts.  Neither is deep; both were simply absent.
;;; =====================================================================

;;; a - b is complex.  `binary-minus-def' makes the difference a sum with a
;;; negation, and both closures are axioms of the field.
(sp (make-wff (forall-guarded '(a b) (list '(IN a CC) '(IN b CC))
                '(IN (- a b) CC))))
(cms-peel!)
(fact 'cc-neg-closed 'b)
(have! '(AND (IN a CC) (IN (- b) CC)))
(fact 'cc-add-closed 'a '(- b))
(have! '(= (- a b) (+ a (- b))) (lambda () (crs)))
(subst '(= (- a b) (+ a (- b))))
(ass)
(qed 'cc-sub-in-cc)
(topic! 'cc-sub-in-cc 'algebra)

;;; a - b = 0 gives a = b.  This is the step the RR proof got from `ineq'.
(sp (make-wff (forall-guarded '(a b) (list '(IN a CC) '(IN b CC) '(= (- a b) 0))
                '(= a b))))
(cms-peel!)
(have! '(= a (+ (- a b) b)) (lambda () (crs)))
(subst '(= a (+ (- a b) b)))
(subst '(= (- a b) 0))
(crs)
(qed 'cc-sub-zero-eq)
(topic! 'cc-sub-zero-eq 'algebra)

;;; =====================================================================
;;; IS-METRIC-SPACE(CC-MS)
;;; =====================================================================

(sp (make-wff '(IS-METRIC-SPACE CC-MS)))
(mac 'IS-METRIC-SPACE)                        ; the generated definitional IFF
(quietly (lambda () (surface-goal! 'CC-MS)))  ; PTS -> CC, DIST -> the lambda
(mac 'is-metric)                              ; the five laws, spelled out

;; length(CC-MS) = 2 -- before the AND split, since the tuple unfold is local.
(cms-focus! (lambda (g) (eq? (cms-head g) 'AND)))
(cms-drive!)

(cms-focus! (lambda (g) (and (eq? (cms-head g) '=) (pair? (cadr g))
                             (eq? (car (cadr g)) 'LENGTH))))
(mac 'cc-ms-def)
(len-r)
(arith)

;; PTS(CC-MS) = CC is a set.
(cms-focus! (lambda (g) (equal? g '(IN CC SET))))
(fact 'cc-is-set)
(ass)

;; DIST(CC-MS) : CC x CC -> RR.  `lam-t' opens the pointwise typing AND the
;; sethood of the domain -- a lambda over a proper class is not a function.
(cms-focus! (lambda (g) (and (eq? (cms-head g) 'IN) (pair? (cadr g))
                             (eq? (car (cadr g)) 'VNB-LAMBDA))))
(lam-t)

(cms-focus! (lambda (g) (and (eq? (cms-head g) 'IN) (pair? (cadr g))
                             (eq? (car (cadr g)) 'CARTESIAN))))
(mac 'cartesian-set-iff)
(for-each (lambda (k) (dk-focus! k) (fact 'cc-is-set) (ass))
          (dk-opened (lambda () (di))))

;; ... and the body lands in RR: the difference is complex, its modulus real.
(cms-focus! (lambda (g) (eq? (cms-head g) 'FORALL)))
(cms-drive!)
(let ((s (find-first (lambda (s) (let ((g (cms-goal-of s)))
                                   (and (eq? (cms-head g) 'IN)
                                        (pair? (cadr g))
                                        (eq? (car (cadr g)) 'magnitude))))
                     (cms-open))))
  (dk-focus! s)
  (let* ((g   (cms-goal-of s))
         (dif (cadr (cadr g)))
         (u   (cadr dif)) (v (caddr dif)))
    (fact 'cc-sub-in-cc u v)
    (fact 'cc-magnitude-closed dif)
    (ass)))

;; ---- the five metric laws.  Everything left is atomic; dispatch on shape.
;; GUARDED ON PROGRESS: a leaf that does not close would otherwise be re-focused
;; for ever, and a second `have!' of a formula already in context is an alpha
;; self-loop rather than a no-op.  Error instead.
(let close ((fuel 40) (prev #f))
  (let ((s (find-first (lambda (s) #t) (cms-open))))
    (if (and s (> fuel 0))
        (begin
          (if (eq? s prev)
              (error "cc-metric-space-proof: leaf did not close" (cms-goal-of s)))
          (dk-focus! s)
          (cms-beta!)
          (cms-split!)
          (let* ((g (dk-goal)) (h (cms-head g)))
            (cond
              ;; d(u,u) = 0 : |u-u| = 0, and u-u is 0.
              ((and (eq? h '=) (pair? (cadr g)) (eq? (car (cadr g)) 'magnitude)
                    (equal? (caddr g) 0))
               (let* ((dif (cadr (cadr g))) (u (cadr dif)) (v (caddr dif)))
                 (fact 'cc-sub-in-cc u v)
                 (mac 'cc-magnitude-zero-iff)            ; |t| = 0  <->  t = 0
                 (crs)))
              ;; 0 <= d(u,v)
              ((and (eq? h '<=) (equal? (cadr g) 0))
               (let* ((dif (cadr (caddr g))) (u (cadr dif)) (v (caddr dif)))
                 (fact 'cc-sub-in-cc u v)
                 (fact 'cc-magnitude-nonneg dif)
                 (ass)))
              ;; the triangle inequality
              ((eq? h '<=)
               (let* ((lhs (cadr g)) (rhs (caddr g))
                      (duw (cadr lhs))                   ; (- u w)
                      (duv (cadr (cadr rhs)))            ; (- u v)
                      (dvw (cadr (caddr rhs)))           ; (- v w)
                      (u (cadr duw)) (w (caddr duw)) (v (caddr duv)))
                 (fact 'cc-sub-in-cc u v)
                 (fact 'cc-sub-in-cc v w)
                 (have! (list 'AND (list 'IN duv 'CC) (list 'IN dvw 'CC)))
                 (fact 'cc-magnitude-triangle duv dvw)
                 (have! (list '= duw (list '+ duv dvw)) (lambda () (crs)))
                 (subst (list '= duw (list '+ duv dvw)))
                 (ass)))
              ;; symmetry: |u-v| = |v-u|, because -(u-v) = v-u.
              ((and (eq? h '=) (pair? (cadr g)) (eq? (car (cadr g)) 'magnitude)
                    (pair? (caddr g)) (eq? (car (caddr g)) 'magnitude))
               (let* ((duv (cadr (cadr g))) (dvu (cadr (caddr g)))
                      (u (cadr duv)) (v (caddr duv)))
                 (fact 'cc-sub-in-cc u v)
                 (fact 'cc-magnitude-closed duv)
                 (fact 'cc-magnitude-neg duv)
                 (have! (list '= dvu (list '- duv)) (lambda () (crs)))
                 (subst (list '= dvu (list '- duv)))
                 (subst (list '= (list 'magnitude (list '- duv))
                                 (list 'magnitude duv)))
                 (rfl)))
              ;; separation: |u-v| = 0 is in context, conclude u = v
              ((eq? h '=)
               (let* ((u (cadr g)) (v (caddr g)) (dif (list '- u v)))
                 (fact 'cc-sub-in-cc u v)
                 (mac-h 'cc-magnitude-zero-iff (list '= (list 'magnitude dif) 0))
                 (fact 'cc-sub-zero-eq u v)
                 (ass)))
              (else (error "cc-metric-space-proof: unexpected leaf" g))))
          (close (- fuel 1) s))
        #t)))

(qed 'cc-is-metric-space)
(topic! 'cc-is-metric-space 'constructions)
