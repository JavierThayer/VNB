;;; drive-converges-implies-cauchy.scm -- a TEST DRIVE, left deliberately open.
;;;
;;;     forall s, f.   CONVERGES(s, f)  =>  IS-CAUCHY-SEQ(s, f)
;;;
;;; A convergent sequence in a metric space is Cauchy.  The tree does not have
;;; this (grep: no converges-implies-cauchy under any spelling), and its absence
;;; is why theorem-library/ascoli-analytic-cores.scm's estimate has FOUR hops
;;; where the user's notes have three -- the middle hop there had to be routed
;;; through the limit by hand.
;;;
;;; RUN IT:      ./prover -b scratchpad/drive-converges-implies-cauchy.scm
;;; OR DRIVE IT: ./prover -b -i scratchpad/drive-converges-implies-cauchy.scm
;;;              ... which loads the library from the band in a second and drops
;;;              you at the ONE open leaf, with (show) / (what-now) available.
;;;
;;; This file does all the bookkeeping and stops on the single leaf that is the
;;; mathematics:
;;;
;;;     d(f(m), f(n_)) <= eps
;;;   given   d(f(m), L) <= hh,   d(f(n_), L) <= hh,   hh + hh = eps
;;;
;;; THREE LINES close it, and the middle one is the interesting part.  This is
;;; the first use of `eps-chain' (driver-kit.scm) anywhere in the tree:
;;;
;;;     (fact 'metric-sym 's L (list 'f 'n_))          ; d(L,f n_) = d(f n_,L)
;;;     (fact 'metric-dist-real 's (list 'f 'n_) L)    ; ... and certify THAT atom
;;;     (eps-chain 's (list (list 'f 'm) L (list 'f 'n_)))
;;;     (qed 'converges-implies-cauchy)
;;;
;;; -- where L is the limit eigenvariable, which the run prints (it is `dcc-L'
;;; if you are driving the file, and a literal l_NNNN if you are typing).
;;;
;;; eps-chain builds the triangle instance, certifies the distance atoms of ITS
;;; OWN chain with metric-dist-real, and hands the composition to `ineq'.  The
;;; second line is needed because the hop bound in context is d(f n_, L) and the
;;; chain's atom is d(L, f n_): eps-chain does not certify the flipped
;;; orientation, so the symmetry equation it needs would otherwise be dropped as
;;; uncertifiable.  If it declines it SAYS so, naming the goal -- it does not
;;; no-op.  The bill is `modulo {metric-dist-real}` [trust: well-known].
;;;
;;; (eps-chain was BROKEN until 2026-08-23, and this leaf is what found it: its
;;; premise selection named every order assumption in the context, including the
;;; NN threshold facts `cap <= m' and `cap <= n_', whose atoms `ineq' cannot
;;; certify in RR -- one such premise makes the whole call refuse.  It now
;;; filters by the oracle's own test, as `contra' does.)
;;; =====================================================================

(define (dcc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (begin (di) (loop (+ n 1))) n))))

(define (dcc-peel-collect!)
  (let loop ((acc '()) (n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (loop (append acc (dk-landed* (lambda () (di)))) (+ n 1))
          acc))))

(define (dcc-di-landed!)
  (let loop ((n 0))
    (let ((ls (dk-landed* (lambda () (di)))))
      (cond ((pair? ls) (car ls))
            ((> n 5) (error "dcc-di-landed!: nothing ever landed"))
            (else (loop (+ n 1)))))))

(define (dcc-skolem! fm)
  (let* ((new (car (dk-landed* (lambda () (ai fm)))))
         (fv0 (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fv0))) (free-vars new)))))

(define (dcc-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (dcc-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (dcc-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

(define (dcc-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

(define (dcc-halve! e)
  (let ((sk (dcc-skolem! (dk-fact! 'rr-pos-halvable e))))
    (dk-split! (car sk))
    (car (cadr sk))))

(sp (make-wff
  (forall-guarded '(s f) (list '(CONVERGES s f)) '(IS-CAUCHY-SEQ s f))))
(dcc-peel!)

;;; CONVERGES(s,f) is FORSOME L. CONVERGES-TO(s,f,L) behind a def-predicate, so
;;; unfold before skolemizing -- `ai' cannot decompose the folded form.
(define dcc-cv (dk-landed-1 (lambda () (mac-h 'converges '(CONVERGES s f)))))
(define dcc-sk (dcc-skolem! dcc-cv))
(define dcc-L  (car (cadr dcc-sk)))
(dk-split! (dk-landed-1 (lambda () (mac-h 'converges-to (car dcc-sk)))))
(define dcc-EPS (car (dk-asms)))          ; forall eps>0. forsome N. forall n_>=N...

(mac 'is-cauchy-seq)
(dcc-and!
 (lambda ()
   (if (memq (car (dk-goal)) '(IS-METRIC-SPACE IN))
       (ass)
       (let* ((me  (dcc-di-landed!)) (eps (cadr me)))
         (dcc-pos-in-rr! eps)
         (let* ((hh  (dcc-halve! eps))
                (junk (dcc-pos-in-rr! hh))     ; `ineq' certifies abs and DIST atoms itself; a BOUND it does not
                (sk2 (dcc-skolem! (dcc-inst! dcc-EPS hh)))
                (cap (car (cadr sk2))))
           (dk-split! (car sk2))
           (let ((thr (car (dk-asms))))     ; forall n_ in NN. cap <= n_ => d(f n_,L) <= hh
             (ew cap)
             (dcc-and!
              (lambda ()
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (let* ((ls (dcc-peel-collect!))
                           (ns (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                        (eq? (caddr a) 'NN))) ls))
                           (m  (cadr (car ns)))
                           (n_ (cadr (cadr ns)))
                           (cj (car (filter (lambda (a) (and (pair? a) (eq? (car a) 'AND))) ls))))
                      (dk-split! cj)
                      (dcc-inst! thr m)                    ; d(f m , L) <= hh
                      (dcc-inst! thr n_)                   ; d(f n_, L) <= hh
                      (fact 'fun-apply-type-c 'f 'NN (list 'PTS 's) m)
                      (fact 'fun-apply-type-c 'f 'NN (list 'PTS 's) n_)
                      (write-line "")
                      (write-line ";; ---- THE LEAF -------------------------------------")
                      (write-line (list 'GOAL (dk-goal)))
                      (write-line (list 'LIMIT-EIGENVARIABLE dcc-L))
                      (write-line ";; premises that matter (top of context):")
                      (for-each
                       (lambda (a)
                         (if (and (pair? a) (memq (car a) '(<= =))) (write-line a)))
                       (dk-asms))
                      (write-line ";; next move -- three lines, then qed:")
                      (write-line (list 'fact (list 'quote 'metric-sym) (list 'quote 's)
                                        dcc-L (list 'f n_)))
                      (write-line (list 'fact (list 'quote 'metric-dist-real) (list 'quote 's)
                                        (list 'f n_) dcc-L))
                      (write-line (list 'eps-chain (list 'quote 's)
                                        (list 'quote (list (list 'f m) dcc-L (list 'f n_)))))
                      (write-line (list 'qed (list 'quote 'converges-implies-cauchy)))
                      (write-line ";; ---------------------------------------------------")
                      #t))))))))))
(write-line (list 'OPEN-LEAVES (length (proof-leaves))))
