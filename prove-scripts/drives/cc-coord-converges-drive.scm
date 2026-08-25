;;; cc-coord-converges-drive.scm -- a TEST DRIVE, left deliberately open.
;;;
;;;     forall f in FUN(NN,CC), g in FUN(NN,RR), lv in CC.
;;;       CONVERGES-TO(CC-MS, f, lv)  =>  (forall n. g(n) = Re(f(n)))
;;;         =>  CONVERGES-TO(RR-MS, g, Re(lv))
;;;
;;; "A complex sequence converges coordinatewise."  This is the CONVERSE of
;;; `cc-converges-of-coords' (theorem-library/cc-complete-proof.scm, proved
;;; 2026-08-24 on the way to `cc-complete'), and the tree does not have it: that
;;; file needed only the direction that ASSEMBLES a complex limit out of two
;;; real ones, so the direction that TAKES a complex limit APART was never
;;; written.  Any ell^p argument that wants to read a coordinate off a limit
;;; needs this one, not that one.
;;;
;;; RUN IT:      ./prover -b prove-scripts/drives/cc-coord-converges-drive.scm
;;; OR DRIVE IT: ./prover -b -i prove-scripts/drives/cc-coord-converges-drive.scm
;;;              ... which loads the library from the band in a second and drops
;;;              you at the ONE open leaf, with (show) / (what-now) available.
;;;
;;; This file does all the bookkeeping -- unfold CONVERGES-TO on the hypothesis
;;; and on the goal, take the SAME threshold N at the SAME eps, peel the index,
;;; walk both metric accessors down to `abs' and `magnitude' -- and stops on the
;;; single leaf that is the mathematics:
;;;
;;;     |g(n_) - Re(lv)| <= eps
;;;   given   |f(n_) - lv| <= eps,   g(n_) = Re(f(n_))
;;;
;;; FIVE LINES close it, and they are exactly the two facts this arc added:
;;;
;;;     (subst '(= (g n_) (real-part (f n_))))
;;;     (fact 'cc-re-sub-rev '(f n_) 'lv)
;;;     (subst '(= (- (real-part (f n_)) (real-part lv))
;;;                (real-part (- (f n_) lv))))
;;;     (fact 'cc-abs-re-le-magnitude '(- (f n_) lv))
;;;     (cd-ineq '(<= (abs (real-part (- (f n_) lv))) (magnitude (- (f n_) lv)))
;;;              '(<= (magnitude (- (f n_) lv)) eps))
;;;     (qed 'cc-coord-converges)
;;;
;;; -- where `eps' is the eigenvariable the run prints (a literal eps if you are
;;; driving the file).  The bill is `modulo 0'.
;;;
;;; THE POINT, and why the two `subst's are in that order.  `ineq' reads
;;; abs(t) and magnitude(t) as OPAQUE ATOMS: an identity between their ARGUMENTS
;;; is of no use to it, so the rewriting has to happen INSIDE the abs before the
;;; oracle is called.  `cc-re-sub' (Re(z - w) = Re z - Re w) is what moves the
;;; difference inside, and `cc-abs-re-le-magnitude' (|Re w| <= |w|) is what
;;; leaves the CC-MS distance standing where the hypothesis put it.  Neither
;;; fact existed in the tree before 2026-08-24; what stood in their place was
;;; `cc-re-sq-le-mod-sq', Re(z)^2 <= z conj z, one square root short.
;;;
;;; Note the ORIENTATION of the pointwise hypothesis: `g(n_) = real-part(f(n_))'
;;; and not the reverse, because `subst' rewrites LEFT to RIGHT along the goal
;;; and the goal is the one carrying g(n_).  cc-converges-of-coords states its
;;; own pointwise hypotheses the OTHER way round, for the mirror-image reason.
;;; =====================================================================

;;; ---- file-local driver helpers (the `cd-' prefix) --------------------

(define (cd-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1))) #t))))

(define (cd-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cd-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cd-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT: `obtain' sees only what its own
;;; lane landed, and this one arrives by inst+.
(define (cd-skolem! ex)
  (let* ((fv0 (cd-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (cd-fvs (dk-asms)))))
      (if (null? fresh) (error "cd-skolem!: nothing appeared" ex) (car fresh)))))

;;; `di' until an ASSUMPTION lands -- never a `di' COUNT.
(define (cd-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "cd-di-landed!: nothing landed"))
            (else (loop (+ n 1)))))))
(define (cd-di-landed-1!)
  (let ((new (cd-di-landed!)))
    (if (null? (cdr new)) (car new) (error "cd-di-landed-1!: expected 1"))))

;;; `ineq' wants 1-based assumption indices, and premises are named one by one.
(define (cd-at form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cd-at: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (cd-ineq . forms) (apply ineq (map cd-at forms)))

;;; (IN x RR) from (POS-RR x) on a SIDE branch -- `mac-h' is destructive and the
;;; main branch still wants POS-RR.
(define (cd-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

(define (cd-and-goal! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cd-and-goal! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; ---- the drive -------------------------------------------------------

(sp (make-wff "forall([f in fun(nn,cc), g in fun(nn,rr), lv in cc],
     converges-to(cc-ms, f, lv) implies
     forall([n_ in nn], g(n_) = real-part(f(n_))) implies
     converges-to(rr-ms, g, real-part(lv)))"))
(cd-peel!)
(define cd-pt (cd-find 'pointwise
   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'real-part)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO CC-MS f lv)))
                           (lambda (a) (eq? (car a) 'AND))))
(define cd-tail (cd-find 'tail
   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))
(fact 'real-part-in-rr 'lv)
(mac 'converges-to)
(cd-and-goal!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
           ((eq? (car gl) 'IN) (slot 'PTS) (ass))
           (else
            (let* ((eps  (cadr (cd-di-landed-1!)))
                   (ex   (dk-deepest (lambda () (inst+ cd-tail eps))))
                   (bigN (cd-skolem! ex))
                   (inner (cd-find 'inner
                            (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                             (dk-contains? a bigN)
                                             (dk-contains? a 'DIST))))))
              (ew bigN)
              (cd-and-goal!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (let ((nx (cadr (cd-di-landed-1!))))
                       (cd-di-landed!)                     ; the (bigN <= nx) bound
                       (inst+ inner nx)
                       (inst+ cd-pt nx)
                       (fact 'fun-apply-type-c 'f 'NN 'CC nx)
                       (fact 'fun-apply-type-c 'g 'NN 'RR nx)
                       (cd-pos-in-rr! eps)
                       (fact 'cc-sub-in-cc (list 'f nx) 'lv)
                       (fact 'cc-magnitude-closed (list '- (list 'f nx) 'lv))
                       (fact 'real-part-in-rr (list '- (list 'f nx) 'lv))
                       (fact 'rr-abs-closed (list 'real-part (list '- (list 'f nx) 'lv)))
                       (fact 'rr-sub-in-rr (list 'g nx) '(real-part lv))
                       (fact 'rr-abs-closed (list '- (list 'g nx) '(real-part lv)))
                       ;; both metrics down to the surface.  GUARDED macetes, so
                       ;; every argument is typed ABOVE these two lines.
                       (mac-h 'cc-ms-dist
                         (list '<= (list (list 'DIST 'CC-MS) (list 'f nx) 'lv) eps))
                       (mac 'rr-ms-dist)
                       (display ";; cc-coord-converges-drive: ")
                       (display (length (proof-leaves)))
                       (display " leaf/leaves left open (expected 1).")
                       (newline)
                       (display ";;   goal: ") (display (wff->string (sequent-node-assertion
                                                          (proof-state-focus *ps*))))
                       (newline)
                       (display ";;   index variable is ") (write nx)
                       (display ", eps is ") (write eps) (newline)
                       (display ";;   the five lines that close it are in the header.")
                       (newline)))))))))))
