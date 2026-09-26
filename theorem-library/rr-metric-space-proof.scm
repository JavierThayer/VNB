;;; rr-metric-space-proof.scm -- IS-METRIC-SPACE(RR-MS), PROVEN.
;;;
;;; It was an AXIOM, `add-axiom!' in structure-library/numeric-instances.scm
;;; with no `warrant!' at all -- so it billed `trust: none', the weakest report
;;; there is, and it was the SOLE unwarranted leaf of `rr-complete'.  Its own
;;; comment there said what was missing: "provable from the abs axioms in
;;; number-systems.scm once FUN-typing of the lambda is in place".
;;;
;;; THAT TYPING ARRIVED ON 2026-08-14.  `pi--lambda-type-subgoal'
;;; (primitive-inferences.scm) grew the MULTI-BINDER case -- a lambda whose bind
;;; spec is a LIST against a CARTESIAN domain -- and the comment above it named
;;; this very theorem as the thing the gap was blocking ("it is the blocker on
;;; IS-METRIC-SPACE(RR-MS), whose DIST is a two-binder lambda").  Nobody came
;;; back for it.  This file is that.
;;;
;;; THE FOUR CONJUNCTS of the generated IS-METRIC-SPACE IFF, and what each costs:
;;;
;;;   length(RR-MS) = 2                 unfold the tuple, `len-r', `arith'.
;;;   PTS(RR-MS) in SET                 rr-is-set (primitive).
;;;   DIST(RR-MS) in FUN(RRxRR, RR)     `lam-t' -- the rule that did not exist.
;;;                                     Two obligations: |x-y| in RR pointwise
;;;                                     (rr-sub-in-rr, then rr-abs-closed), and
;;;                                     RRxRR is a set (cartesian-set-iff).
;;;   is-metric(DIST(RR-MS), RR)        the five metric laws, after `lam-b'
;;;                                     reduces d(u,v) to |u-v|.
;;;
;;; The five laws come out of the abs axioms one apiece -- d(u,u)=0 is
;;; rr-abs-zero at u-u, nonnegativity is rr-abs-nonneg, separation is rr-abs-zero
;;; the other way, the triangle inequality is rr-abs-triangle at (u-v)+(v-w) --
;;; EXCEPT symmetry, |u-v| = |v-u|, which no abs axiom gives.  That is
;;; `rr-abs-sub-sym' (theorem-library/rr-order-basics.scm), proved there from
;;; multiplicativity and the zero-divisor lemma, and it is the one piece of this
;;; proof that is not a citation.

;;; ---- file-local driver helpers (rms- prefix) -------------------------
(define (rms-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-leaves)))
(define (rms-goal-of s) (wff-formula (sequent-node-assertion s)))
(define (rms-head g) (and (pair? g) (car g)))

;;; Focus the first open leaf satisfying PRED.  ERRORS on a miss: a focus helper
;;; that returns #f and leaves focus put hides every later mistake.
(define (rms-focus! pred)
  (let ((s (find-first (lambda (s) (pred (rms-goal-of s))) (rms-open))))
    (if (not s) (error "rms-focus!: no open leaf matches") (begin (dk-focus! s) s))))

;;; The 1-based indices of the order-shaped assumptions -- what `ineq' wants.
;;; Local, because load.scm gives every theorem-library file its own environment:
;;; rr-order-basics.scm's `ro-idx' is not visible here.
(define (rms-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <= =)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (else (loop (cdr l) (+ i 1) acc)))))
(define (rms-ineq!) (apply ineq (rms-idx)))

(define (rms-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (rms-has-lambda-app? (car g)) (rms-has-lambda-app? (cdr g))))
        (else #f)))

;;; Beta-reduce to a fixpoint, guarded on PROGRESS (`lam-b' only warns when there
;;; is nothing to do, so a "while there is an application" loop would spin).
(define (rms-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (rms-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; Decompose every open leaf whose goal is a FORALL, an IMPLIES or an AND.
;;; Beta-reduce first, so the assumption an IMPLIES lands is already |u-v|-shaped
;;; rather than a lambda application nothing downstream can match.
(define (rms-drive!)
  (let loop ((fuel 200))
    (let ((s (find-first (lambda (s) (memq (rms-head (rms-goal-of s))
                                           '(FORALL IMPLIES AND)))
                         (rms-open))))
      (if (and s (> fuel 0))
          (begin (dk-focus! s) (rms-beta!)
                 (if (memq (rms-head (dk-goal)) '(FORALL IMPLIES AND))
                     (di)
                     #t)
                 (loop (- fuel 1)))
          #t))))

;;; ---- the proof -------------------------------------------------------
(sp (make-wff '(IS-METRIC-SPACE RR-MS)))
(mac 'IS-METRIC-SPACE)                       ; the generated definitional IFF
(quietly (lambda () (surface-goal! 'RR-MS))) ; PTS(RR-MS) -> RR, DIST(RR-MS) -> the lambda
(mac 'is-metric)                             ; and the five laws, spelled out

;; length(RR-MS) = 2 -- before the AND split, since the tuple unfold is local.
(rms-focus! (lambda (g) (and (eq? (rms-head g) 'AND))))
(rms-drive!)

(rms-focus! (lambda (g) (and (eq? (rms-head g) '=) (pair? (cadr g))
                             (eq? (car (cadr g)) 'LENGTH))))
(mac 'rr-ms-def)
(len-r)
(arith)

;; PTS(RR-MS) = RR is a set.
(rms-focus! (lambda (g) (equal? g '(IN RR SET))))
(fact 'rr-is-set)
(ass)

;; DIST(RR-MS) : RR x RR -> RR.  `lam-t' splits it into the pointwise typing and
;; the sethood of the domain -- the second is not a formality (a lambda over a
;; proper class is not a function), see pi-lambda-type!'s header.
(rms-focus! (lambda (g) (and (eq? (rms-head g) 'IN) (pair? (cadr g))
                             (eq? (car (cadr g)) 'VNB-LAMBDA))))
(lam-t)

;; ... the domain is a set.
(rms-focus! (lambda (g) (and (eq? (rms-head g) 'IN) (pair? (cadr g))
                             (eq? (car (cadr g)) 'CARTESIAN))))
(mac 'cartesian-set-iff)
(for-each (lambda (k) (dk-focus! k) (fact 'rr-is-set) (ass))
          (dk-opened (lambda () (di))))

;; ... and the body lands in RR.  Peel both binders, then subtraction closure
;; followed by rr-abs-closed.
(rms-focus! (lambda (g) (eq? (rms-head g) 'FORALL)))
(rms-drive!)
(let ((s (find-first (lambda (s) (let ((g (rms-goal-of s)))
                                   (and (eq? (rms-head g) 'IN)
                                        (pair? (cadr g)) (eq? (car (cadr g)) 'abs))))
                     (rms-open))))
  (dk-focus! s)
  (let* ((g   (rms-goal-of s))
         (dif (cadr (cadr g)))                ; the (- x_ y_) inside the abs
         (u   (cadr dif)) (v (caddr dif)))
    (fact 'rr-sub-in-rr u v)
    (fact 'rr-abs-closed dif)
    (ass)))

;; ---- the five metric laws.  Everything left is atomic; dispatch on shape.
;; GUARDED ON PROGRESS: a leaf that does not close would otherwise be re-focused
;; for ever, and the second `have!' of a formula already in context is an alpha
;; self-loop, not a no-op.  Error instead.
(let close ((fuel 40) (prev #f))
  (let ((s (find-first (lambda (s) #t) (rms-open))))
    (if (and s (> fuel 0))
        (begin
          (if (eq? s prev)
              (error "rr-metric-space-proof: leaf did not close" (rms-goal-of s)))
          (dk-focus! s)
          (rms-beta!)
          (let* ((g (dk-goal)) (h (rms-head g)))
            (cond
              ;; d(u,u) = 0 : |u-u| = 0, and u-u is 0.
              ((and (eq? h '=) (pair? (cadr g)) (eq? (car (cadr g)) 'abs)
                    (equal? (caddr g) 0))
               (let* ((dif (cadr (cadr g))) (u (cadr dif)) (v (caddr dif)))
                 (fact 'rr-sub-in-rr u v)
                 (mac 'rr-abs-zero)                    ; |t| = 0  <->  t = 0
                 (rms-ineq!)))
              ;; 0 <= d(u,v)
              ((and (eq? h '<=) (equal? (cadr g) 0))
               (let* ((dif (cadr (caddr g))) (u (cadr dif)) (v (caddr dif)))
                 (fact 'rr-sub-in-rr u v)
                 (fact 'rr-abs-nonneg dif)
                 (ass)))
              ;; the triangle inequality
              ((eq? h '<=)
               (let* ((lhs (cadr g)) (rhs (caddr g))
                      (duw (cadr lhs))                 ; (- u w)
                      (duv (cadr (cadr rhs)))          ; (- u v)
                      (dvw (cadr (caddr rhs)))         ; (- v w)
                      (u (cadr duw)) (w (caddr duw)) (v (caddr duv)))
                 (fact 'rr-sub-in-rr u v)
                 (fact 'rr-sub-in-rr v w)
                 (fact 'rr-abs-triangle-c duv dvw)
                 (have! (list '= duw (list '+ duv dvw)) (lambda () (crs)))
                 (subst (list '= duw (list '+ duv dvw)))
                 (ass)))
              ;; symmetry
              ((and (eq? h '=) (pair? (cadr g)) (eq? (car (cadr g)) 'abs)
                    (pair? (caddr g)) (eq? (car (caddr g)) 'abs))
               (let* ((dif (cadr (cadr g))) (u (cadr dif)) (v (caddr dif)))
                 (fact 'rr-abs-sub-sym u v)
                 (ass)))
              ;; separation: |u-v| = 0 is in context, conclude u = v
              ((eq? h '=)
               (let* ((u (cadr g)) (v (caddr g)) (dif (list '- u v)))
                 (fact 'rr-sub-in-rr u v)
                 (mac-h 'rr-abs-zero (list '= (list 'abs dif) 0))
                 (rms-ineq!)))
              (else (error "rr-metric-space-proof: unexpected leaf" g))))
          (close (- fuel 1) s))
        #t)))

(qed 'rr-is-metric-space)
(topic! 'rr-is-metric-space 'constructions)
