;;; product-projection-drive.scm -- A LEAF TO DRIVE.
;;;
;;; `product-projection-continuous' (structure-library/product-metric.scm:92) is
;;; still an ASSERTED support:
;;;
;;;   IS-MS-SEQUENCE(ms), SUMMABLE-WEIGHT(w), n in NN
;;;     =>  IS-CONTINUOUS( PRODUCT-METRIC-W(ms,w),  ms(n),  PRODUCT-PROJ(ms,n) )
;;;
;;; It is rung 3, and after the 2026-08-23 work on rungs 4 and 5 everything it
;;; needs is proven.  This script does the plumbing and STOPS at the one leaf
;;; that carries the mathematics.  Run it with
;;;
;;;     ./prover -b prove-scripts/drives/product-projection-drive.scm      (batch)
;;;     ./prover -b -i prove-scripts/drives/product-projection-drive.scm   (REPL)
;;;
;;; -- the second form leaves you at the open leaf with `pj-*' in scope.
;;; (If `./prover -b' warns the band is stale, `./prover --build-band' first, or
;;; drop the -b and pay the full load.)
;;;
;;; WHAT IS ALREADY DONE when the script stops
;;; ------------------------------------------
;;; IS-CONTINUOUS is unfolded and three of its four conjuncts are closed: both
;;; metric-space facts, and the typing of the projection.  Focus is on
;;;
;;;     IS-CONTINUOUS-AT( P_w, ms(n), PRODUCT-PROJ(ms,n), a )
;;;
;;; for a fixed point `a' of the product, with `a in PRODUCT-CARRIER(ms)' and
;;; `a(n) in PTS(ms(n))' already in the context.
;;;
;;; THE MOVE
;;; --------
;;; `sequential-implies-continuous-at' (theorem-library/sequential-continuity.scm)
;;; takes it, once you have supplied its sequential clause
;;;
;;;   forall sq in SQN(PTS(P_w)).
;;;     CONVERGES-TO(P_w, sq, a)
;;;       implies CONVERGES-TO(ms(n), COMPOSE(PRODUCT-PROJ(ms,n), sq),
;;;                            PRODUCT-PROJ(ms,n)(a))
;;;
;;; and that clause is ONE citation of rung 4 plus one transfer:
;;;
;;;   (fact 'product-convergence-coordinatewise-fwd ms w sq a)
;;;       lands  forall i in NN. CONVERGES-TO(ms(i), (VNB-LAMBDA k NN (sq(k))(i)),
;;;                                           a(i)),
;;;       and `inst+' at n gives the coordinate sequence converging to a(n);
;;;   (fact 'converges-to-transfer (ms n) <that lambda> (COMPOSE proj sq) (a n))
;;;       moves the conclusion onto COMPOSE(proj, sq), whose j-th value is
;;;       proj(sq(j)) = (sq(j))(n) -- `compose-apply' then `lam-b'.
;;;
;;; The pattern to copy is `product-identity-continuous'
;;; (theorem-library/product-weights.scm:151); the only difference is that the
;;; target is the FACTOR ms(n) rather than a second product, so the transfer
;;; happens in ms(n) and there is no second rung-4 citation.
;;;
;;; THREE TRAPS ALREADY PAID FOR BELOW, so you do not meet them
;;; ----------------------------------------------------------
;;; * `product-metric-carrier' rewrites PTS(PRODUCT-METRIC-W(ms,w)) ->
;;;   PRODUCT-CARRIER(ms) and NOT the other way.  `mac' on a goal that mentions
;;;   PTS, `mac-h' on a hypothesis that does; aimed the other way it is a silent
;;;   no-op.  The projection's domain is spelled PRODUCT-CARRIER(ms) while
;;;   IS-CONTINUOUS wants FUN(PTS(P_w), PTS(ms(n))), so the goal has to be
;;;   rewritten BEFORE `lam-t' or the domains do not match.
;;; * `lam-t' owes (IN PRODUCT-CARRIER(ms) SET), and `dk-set-close!' does not
;;;   know that domain -- it falls through to `ass', so the fact must already be
;;;   in the context.  It is a typing conjunct of IS-METRIC-SPACE(P_w).
;;; * `mac-h' REPLACES what it unfolds, so IS-METRIC-SPACE(P_w) is opened on a
;;;   `have!' LANE; unfolded in the main branch it would delete the predicate
;;;   the other conjuncts cite.

;;; ---- file-local driver helpers (the `pj-' prefix) ---------------------
(define (pj-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (pj-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (pj-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "pj-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (pj-di-landed-1!)
  (let ((new (pj-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "pj-di-landed-1!: expected 1" (map expression->string new)))))
(define (pj-peel-to! head)
  (let lp ((k 0))
    (if (and (< k 16) (not (eq? (car (dk-goal)) head)))
        (begin (di) (lp (+ k 1))))))
(define (pj-split-h! name form)
  (dk-split! (dk-landed-find (lambda () (mac-h name form))
                             (lambda (f) (eq? (car f) 'AND)))))
(define (pj-dump tag)
  (display "\n===== ") (display tag) (display " =====\n")
  (display "GOAL: ") (display (expression->string (dk-goal))) (newline)
  (let loop ((l (dk-asms)) (i 1))
    (if (pair? l)
        (begin (display "  [") (display i) (display "] ")
               (display (expression->string (car l))) (newline)
               (loop (cdr l) (+ i 1)))))
  (newline))

;;; ---- the statement, verbatim from structure-library/product-metric.scm ----
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
   (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
     (FORALL n (IMPLIES (IN n NN)
       (IS-CONTINUOUS (PRODUCT-METRIC-W ms w) (ms n)
                      (PRODUCT-PROJ ms n))))))))))
(pj-peel-to! 'IS-CONTINUOUS)

(define pj-g    (dk-goal))
(define pj-p    (cadr pj-g))                       ; PRODUCT-METRIC-W(ms, w)
(define pj-msn  (caddr pj-g))                      ; ms(n)
(define pj-proj (cadddr pj-g))                     ; PRODUCT-PROJ(ms, n)
(define pj-ms   (cadr pj-p))
(define pj-w    (caddr pj-p))
(define pj-n    (cadr pj-msn))
(define pj-pc   (list 'PRODUCT-CARRIER pj-ms))
(define pj-a    #f)   ; the point, set below once `di' has fixed it

;;; both spaces are metric spaces
(fact 'product-is-metric-space pj-ms pj-w)
(define pj-msu
  (list 'FORALL 'nx_ (list 'IMPLIES '(IN nx_ NN) (list 'IS-METRIC-SPACE (list pj-ms 'nx_)))))
(have! pj-msu
  (lambda () (mac-h 'is-ms-sequence (list 'IS-MS-SEQUENCE pj-ms)) (ass)))
(inst+ pj-msu pj-n)

;;; the sethood of the product carrier, off IS-METRIC-SPACE, on a LANE
(have! (list 'IN pj-pc 'SET)
  (lambda ()
    (pj-split-h! 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE pj-p))
    (mac-h 'product-metric-carrier (list 'IN (list 'PTS pj-p) 'SET))
    (ass)))

;;; the projection is a map of the two carriers
(have! (list 'IN pj-proj (list 'FUN (list 'PTS pj-p) (list 'PTS pj-msn)))
  (lambda ()
    (mac 'product-metric-carrier)                  ; PTS(P_w) -> PRODUCT-CARRIER(ms)
    (mac 'PRODUCT-PROJ)                            ; the functoid, unfolded
    (dk-lam-t!)
    (let ((x (cadr (pj-di-landed-1!))))
      (fact 'product-carrier-coord pj-ms x pj-n)
      (ass))))

;;; ---- unfold IS-CONTINUOUS and close everything but the point ----------
(mac 'is-continuous)
(pj-and!
 (lambda ()
   (let ((g (dk-goal)))
     (if (memq (car g) '(IS-METRIC-SPACE IN)) (ass)
         (let ((a (cadr (pj-di-landed-1!))))
           (set! pj-a a)
           (have! (list 'IN a pj-pc)
             (lambda () (mac-h 'product-metric-carrier
                               (list 'IN a (list 'PTS pj-p)))
                     (ass)))
           (fact 'product-carrier-coord pj-ms a pj-n)
           (pj-dump "YOUR LEAF -- IS-CONTINUOUS-AT at the point a"))))))

(display "\nOpen leaves: ") (display (length (proof-leaves))) (newline)
(display "Bindings in scope: pj-ms pj-w pj-n pj-p pj-msn pj-proj pj-pc pj-a\n")
(display "Next move: have! the sequential clause, then\n")
(display "  (fact 'sequential-implies-continuous-at pj-p pj-msn pj-proj pj-a)\n")
(display "  (ass)\n")
