;;; sketch.scm -- the structured-proof surface (sketch/step/obtain/qed-sketch),
;;; the generalization of `calc' off chains onto the whole argument.  You write
;;; the PREAMBLE -- the intermediate claims -- and the machine discharges each
;;; with an existing lane.  TWO outcomes, by design (the calc contract):
;;;
;;;   (1) every step discharges AND the goal closes -> the proof CLOSES.  The
;;;       kernel trace lives underneath; `qed' bills `modulo 0'.
;;;   (2) a step will not discharge -> it is GRANTED to context (so the rest of
;;;       the sketch proceeds) and REPORTED BY NAME: "prove this -- if true at all".
;;;       These gaps are exactly proof-debt leaves; the report is the ledger read
;;;       out loud.
;;;
;;; Reuses calc's lane machinery (calc--try / calc--in-ctx? / calc--order-close!
;;; / calc--auto-scout?) and driver-kit focus (dk-focus! by NODE, never by shape).
;;; Loads after `calc' (whose helpers it calls) in load.scm.

(define *sk-gaps* '())
(define (sk-reset!) (set! *sk-gaps* '()))

(define (sk--goalof n) (wff-formula (sequent-node-assertion n)))
(define (sk--find lst p) (cond ((null? lst) #f) ((p (car lst)) (car lst)) (else (sk--find (cdr lst) p))))

;;; a typing lane: close (IN (* a b) NN) by nn-mul-closed on the factors (the
;;; "so a*b is a natural" bookkeeping a human never writes).  fact discharges a
;;; ground factor's (IN 2 NN) itself.
(define (sk--type-nn! node)
  (let ((g (sk--goalof node)))
    (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'NN)
         (pair? (cadr g)) (eq? (car (cadr g)) '*)
         ;; fact lands the typing into context but does NOT ground the goal node;
         ;; ass links goal to the landed assumption.  Without it this lane no-ops.
         (calc--try (lambda () (fact 'nn-mul-closed (cadr (cadr g)) (caddr (cadr g))) (ass)) node))))

;;; generic closer: try the cheap lanes in order; #t iff NODE grounded.
(define (sk--auto node)
  (or (calc--try (lambda () (ass))  node)
      (calc--try (lambda () (rfl))  node)
      (calc--try (lambda () (qrfl)) node)
      (calc--try (lambda () (crs))  node)
      (calc--try (lambda () (arith)) node)
      (sk--type-nn! node)
      (calc--try (lambda () (calc--order-close!)) node)
      (calc--auto-scout? node)))

;;; a lane: #f/'auto -> sk--auto ; a thunk ; a symbol (macete name) ; a tactic form.
(define (sk--discharge node lane)
  (cond ((or (not lane) (eq? lane 'auto)) (sk--auto node))
        ((procedure? lane) (calc--try lane node))
        ((symbol? lane)    (calc--try (lambda () (mac lane) (ass)) node))
        ((pair? lane)      (calc--try (lambda () (eval lane user-initial-environment)) node))
        (else #f)))

;;; START: state the goal, strip its leading FORALL/IMPLIES into context.
(define (sketch g)
  (sk-reset!)
  (sp g)
  (let loop ((n 0))
    (let ((gg (sk--goalof (proof-state-focus *ps*))))
      (when (and (< n 40) (pair? gg) (memq (car gg) '(FORALL IMPLIES)))
        (vnb-guard (lambda () (di)))
        (loop (+ n 1))))))

;;; HAVE: cut CLAIM, try to discharge it; grant it to the main branch either way.
;;; If it does not discharge it is recorded as a gap.  A claim already in context
;;; is a GIVEN -- no cut (would alpha-self-loop), no gap.
(define (step claim . opt)
  (let* ((raw  (->raw-formula claim))
         (lane (and (pair? opt) (car opt))))
    (if (calc--in-ctx? raw)
        'given
        (let ((before (proof-leaves)))
          (cut raw)
          (let* ((new  (filter (lambda (n) (not (memq n before))) (proof-leaves)))
                 (side (sk--find new (lambda (n) (alpha-equiv? (sk--goalof n) raw))))
                 (cont (sk--find new (lambda (n) (not (alpha-equiv? (sk--goalof n) raw))))))
            (when side
              (dk-focus! side)
              (sk--discharge side lane)      ; run the lane (may leave AND-split tails)
              (sk--sweep!)                    ; mop them up
              (unless (sequent-node-grounded? side)
                (set! *sk-gaps* (cons raw *sk-gaps*))))
            (when cont (dk-focus! cont))
            (if side 'stepped 'BONGO))))))

;;; context of the current focus, as raw formulas; and its free variables.
(define (sk--ctx) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (sk--fvs forms) (apply append (map free-vars forms)))

;;; ai every landed AND in the focus context, to exhaustion (unpack a conjunction).
(define (sk--split!)
  (let loop ((fuel 6))
    (let ((cj (sk--find (sk--ctx) (lambda (f) (and (pair? f) (eq? (car f) 'AND))))))
      (when (and cj (> fuel 0)) (vnb-guard (lambda () (ai cj))) (loop (- fuel 1))))))

;;; OBTAIN: run LANE (a forward move that lands an existential into context),
;;; skolemize it, and RETURN the fresh eigenvariable -- read off by free-variable
;;; set-difference (the symbol now in context that was not before), NOT guessed by
;;; shape.  This is the s2-any pattern made robust: obtain names its own output.
(define (obtain lane)
  (let ((before (sk--ctx)))
    (vnb-guard (lambda () (sk--discharge (proof-state-focus *ps*) lane)))  ; lands the forsome
    (let ((ex (sk--find (sk--ctx)
                (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME) (not (member f before)))))))
      (if (not ex)
          (begin (display ";; obtain: no existential landed\n") #f)
          (let ((fv0 (sk--fvs (sk--ctx))))
            (vnb-guard (lambda () (ai ex)))       ; skolemize: introduces a fresh eigenvar
            (sk--split!)                          ; unpack the body conjunction
            (let* ((fresh (filter (lambda (v) (not (memq v fv0))) (sk--fvs (sk--ctx))))
                   (eig   (and (pair? fresh) (car fresh))))
              eig))))))

;;; close every open leaf that auto can close, to a fixpoint (mops up the AND-split
;;; tails an existential witness leaves behind).
(define (sk--sweep!)
  (let loop ((fuel 12))
    (let ((open (filter (lambda (n) (not (sequent-node-grounded? n))) (proof-leaves)))
          (progress #f))
      (when (and (pair? open) (> fuel 0))
        (for-each (lambda (n)
                    (when (not (sequent-node-grounded? n))
                      (dk-focus! n)
                      (when (sk--auto n) (set! progress #t))))
                  open)
        (when progress (loop (- fuel 1)))))))

;;; FINISH: close the main goal (auto, or an explicit lane), then report the outcome.
(define (qed-sketch name . opt)
  (let ((lane (and (pair? opt) (car opt))))
    (sk--discharge (proof-state-focus *ps*) lane)
    (sk--sweep!)
    (let ((gaps (reverse *sk-gaps*)) (open (proof-leaves)))
      (newline)
      (cond
        ((and (null? gaps) (null? open))
         (display ";; ================ OUTCOME 1: the sketch CLOSES ================\n")
         (display ";; Viewer discretion advised: the kernel trace is the gory version.\n")
         (display ";;   (write-proof-reader '") (display name)
         (display " \"...\") renders it; qed bills the trust below.\n")
         (qed name))
        (else
         (display ";; ============ OUTCOME 2: prompt insufficient ============\n")
         (if (pair? gaps)
             (begin
               (display ";; These intermediate steps did NOT discharge -- prove them\n")
               (display ";; (give a lane), or they are false:\n")
               (for-each (lambda (g) (display ";;   FUBA> ") (write g) (newline)) gaps))
             (display ";; The goal itself did not follow from the steps as given.\n"))
         (display ";; open leaves remaining: ") (display (length open)) (newline)
         #f)))))
