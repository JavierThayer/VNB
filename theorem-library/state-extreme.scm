;;; state-extreme.scm -- PROPOSITION 4.24, second sentence: the extreme points of Sigma(A) are the pure
;;; states.  F. J. Thayer, "Banach Algebras and Applications", Proposition 4.24.
;;; Agent BA-1117-GNS2, 2026-11-17.  Destination: theorem-library/state-extreme.scm.
;;; Library: operator-algebras.  Load window: after ba4-states (pure-state-extreme,
;;; extreme-state-pure) and structure-library/ba-gns2-vocab (IS-EXTREME-STATE).  Prefix g4x-.
;;; The two directions were proven by BA-1111-B in ba4-states with the convex combination written
;;; out; this file states them with the predicate and joins them.

(define (g4x-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (for-each (lambda (l) (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)) (dk-open-leaves))
        (error "state-extreme: unfinished" name))))
(define (g4x-st body) (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a) body))))
(define (g4x-dec-parts d)    ; (FORALL y (IMPLIES _ (= (f y) (+ (* r (g y)) (* (- 1 r) (h y)))))) -> (g h r)
  (let* ((e (caddr (caddr d))) (s (caddr e)) (A (cadr s)) (B (caddr s)))
    (list (car (caddr A)) (car (caddr B)) (cadr A))))
(define (g4x-dec? h)
  (and (dk-head-is? h 'FORALL) (pair? (caddr h)) (dk-head-is? (caddr h) 'IMPLIES)
       (let ((e (caddr (caddr h)))) (and (dk-head-is? e '=) (dk-head-is? (caddr e) '+)))))

(sp (g4x-st '(FORALL f (IMPLIES (IS-PURE-STATE a f) (IS-EXTREME-STATE a f)))))
(dk-peel!)
(dk-cite! 'pure-state-extreme 'a 'f)
(let ((pf (dk-cite! 'is-pure-state 'a 'f)))
  (dk-iff-fwd! pf))
(mac 'IS-EXTREME-STATE)
(dk-conj-close!
  (lambda ()
    (if (dk-asm? (dk-goal)) (dk-ass!)
        (begin
          (dk-peel!)
          (let* ((d (car (filter g4x-dec? (dk-asms))))
                 (ghr (g4x-dec-parts d))
                 (all (apply dk-cite! 'pure-state-extreme 'a 'f ghr))
                 (g (dk-goal))
                 (z (if (dk-head-is? g 'AND) (cadr (cadr (cadr g))) (cadr (cadr g)))))
            (let loop ((r all)) (if (dk-head-is? r 'IMPLIES) (loop (dk-landed-1 (lambda () (detach! r)))) (dk-apply! r z)))
            (dk-conj-close! (lambda () (dk-ass!))))))))
(g4x-qed! 'pure-state-is-extreme)

(define g4x-ext
  '(FORALL g (IMPLIES (IN g (STATES a)) (FORALL h (IMPLIES (IN h (STATES a))
     (FORALL r (IMPLIES (IN r RR) (IMPLIES (< 0 r) (IMPLIES (< r 1)
       (IMPLIES (FORALL g4ty_ (IMPLIES (IN g4ty_ (VEC a)) (= (f g4ty_) (+ (* r (g g4ty_)) (* (- 1 r) (h g4ty_))))))
         (FORALL g4tz_ (IMPLIES (IN g4tz_ (VEC a)) (= (g g4tz_) (f g4tz_))))))))))))))
(sp (g4x-st '(FORALL f (IMPLIES (IS-EXTREME-STATE a f) (IS-PURE-STATE a f)))))
(dk-peel!)
(dk-iff-fwd! (dk-cite! 'is-extreme-state 'a 'f))
(let ((hy (car (filter (lambda (h) (and (dk-head-is? h 'FORALL) (not (g4x-dec? h)))) (dk-asms)))))
  (dk-have! g4x-ext
    (lambda ()
      (dk-peel!)
      (let* ((d (car (filter g4x-dec? (dk-asms))))
             (ghr (g4x-dec-parts d))
             (z (cadr (cadr (dk-goal))))
             (r1 (apply dk-apply! hy ghr))
             (r2 (dk-apply! r1 z)))
        (dk-split! r2)
        (dk-ass!)))))
(dk-cite! 'extreme-state-pure 'a 'f)
(dk-ass!)
(g4x-qed! 'extreme-state-is-pure)

(sp (g4x-st '(FORALL f (IFF (IS-PURE-STATE a f) (IS-EXTREME-STATE a f)))))
(dk-peel!)
(dk-cite! 'pure-state-is-extreme 'a 'f)
(dk-cite! 'extreme-state-is-pure 'a 'f)
(define (g4x-mp!)
  (let* ((g (dk-goal))
         (i (car (filter (lambda (h) (and (dk-head-is? h 'IMPLIES) (equal? (caddr h) g))) (dk-asms)))))
    (detach! i) (if (not (proof-done? *ps*)) (dk-ass!))))
(dk-iff! (lambda (g) (dk-head-is? g 'IS-EXTREME-STATE)) g4x-mp! g4x-mp!)
(g4x-qed! 'pure-state-iff-extreme)
