;;; rr-ineq.scm -- PROTOTYPE of the rr-ineq applier (plan item 2, the "dumb
;;; applier"; see [[project-rr-ineq-toolkit]]).
;;;
;;; The cluster of cheap real-analysis inequality moves already exists, curated
;;; and warranted, across order-lemmas.scm (transitivity / adding / scaling /
;;; abs / sign-of-a-product) and scalar-inequalities.scm (Young, AM-GM, QM-AM,
;;; Cauchy-Schwarz, the t/(1+t) family), all filed under `inequalities' in
;;; pss-categories.scm.  And the LINEAR decision lane -- plan item 3 -- already
;;; exists as the (ineq) oracle (ineq-oracle.scm + linear-arith.scm), which
;;; closes any linear <=/</= goal from named premises with a Farkas certificate.
;;;
;;; What was missing is the GLUE the analyst asked for: a way to FIRE the cluster
;;; at a goal without hand-picking the lemma name.  Two lanes dispatch almost all
;;; routine "proof block" inequality arithmetic:
;;;
;;;   LINEAR lane      -- (ineq ...) over the order-shaped assumptions.  Handles
;;;                       transitivity chains, eps/2 + eps/2, k*eps absorption,
;;;                       adding inequalities, |a|<=c => -c<=a<=c once unpacked --
;;;                       everything linear in the atoms.
;;;   CLUSTER lane     -- bc* a cluster lemma whose CONCLUSION matches the goal,
;;;                       then auto-discharge its guards (ass / arith / ineq / di).
;;;                       Handles the NONLINEAR / abs steps the oracle cannot see:
;;;                       a<=b & 0<=c => a*c<=b*c, 0<=x*x, x<=|x|, Young, AM-GM.
;;;
;;; This file adds three procedures on top of the existing tactic layer -- no new
;;; kernel rule, no new axiom; every move it commits is a real checked proof:
;;;
;;;   (rr-ineq-scan)   READ-ONLY.  Speculatively sweeps both lanes on scratch
;;;                    clones of the current focus and reports which close it.
;;;                    Returns the results as structured records (per the
;;;                    return-data-not-just-print rule); prints an ASCII table.
;;;   (rr-ineq!)       COMMITS the first lane/lemma the scan finds that fully
;;;                    closes the goal, on the live proof state.  A no-op (state
;;;                    untouched) if nothing closes.  Returns the winning record.
;;;   (rr-ineq?)       Predicate: does either lane close the current focus?
;;;
;;; DESIGN RULE honoured: the cluster is MANY SMALL CURRIED lemmas that bc*/fact
;;; glue, never one fat warrant (that shape caused the vtaylor-clear no-op).
;;;
;;; PROTOTYPE STATUS: not yet wired into load.scm.  Load by hand after a full
;;; boot: (load "structure-library/rr-ineq.scm").  Self-test: calculus/
;;; rr-ineq-probe.scm.  Once it earns its keep, fold into load.scm after suggest.
;;;
;;; Depends on: ineq-oracle (cmd-ineq), order-lemmas + scalar-inequalities (the
;;; cluster supports), suggest.scm (vnb--scratch-state), interactive.scm
;;; (apply-recorded-cmd! and the tactic wrappers), kernel (proof-done? etc.).

;;; =======================================================================
;;; The cluster registry -- the "one home" for the applier's sweep.
;;;
;;; Each entry is (name . role):
;;;   'back    conclusion is an inequality; cite by bc* and discharge guards.
;;;   The LINEAR lane is not a lemma -- it is the (ineq) oracle, swept separately.
;;;
;;; Ordered NONLINEAR-FIRST: the distinctive value of the cluster is the moves
;;; the linear oracle CANNOT make (products, squares, abs), so the sweep tries
;;; those before the linear-subsumed transitivity/add lemmas.  (The oracle lane
;;; is tried first of all, so a purely linear goal never reaches these.)

(define *rr-ineq-cluster*
  '(;; --- nonlinear: scaling / products (Farkas cannot see these) ---
    (rr-le-scale-nonneg   . back)   ; 0<=c & x<=y => c*x <= c*y
    (rr-lt-scale-pos      . back)   ; 0<c  & x<y  => c*x <  c*y
    (rr-mul-le-right      . back)   ; a<=b & 0<=c => a*c <= b*c   [vector-taylor]
    (rr-sq-nonneg         . back)   ; 0 <= x*x
    (rr-prod-nonpos-pos   . back)   ; u*v<=0 & 0<v => u<=0
    (rr-prod-nonpos-neg   . back)   ; u*v<=0 & v<0 => 0<=u
    ;; --- abs ---
    (rr-le-abs            . back)   ; x <= |x|
    (rr-le-abs-self       . back)   ; c <= |c|                    [vector-taylor]
    (rr-abs-reverse-triangle . back); ||x|-|y|| <= |x-y|
    ;; --- sum-of-squares polynomial estimates ---
    (rr-young-2           . back)   ; a*b <= (a^2+b^2)/2
    (rr-amgm-2            . back)   ; 4ab <= (a+b)^2
    (rr-qm-am-2           . back)   ; (a+b)^2 <= 2(a^2+b^2)
    ;; --- the t/(1+t) bounded-function family ---
    (bdd-fn-nonneg        . back)
    (bdd-fn-lt-one        . back)
    (bdd-fn-le-arg        . back)
    (bdd-fn-mono          . back)
    (bdd-fn-subadd        . back)
    ;; --- difference<->order glue, negation ---
    (rr-le-from-diff-nonneg . back) ; 0<=y-x => x<=y
    (rr-le-diff-nonpos    . back)   ; u<=v => u-v<=0
    (rr-lt-diff-pos       . back)   ; u<v  => 0<v-u
    (rr-le-neg            . back)   ; u<=v => -v<=-u
    ;; --- linear siblings (usually the oracle beats these; kept for coverage
    ;;     when a premise is not order-shaped, e.g. hidden behind a defn) ---
    (rr-le-trans-c        . back)
    (rr-le-add            . back)
    (rr-add-nonneg        . back)))

;;; The order-relation heads the linear lane and the leaf-closer recognise.
(define *rr-ineq-rel-heads* '(<= < = > >=))

;;; =======================================================================
;;; Reading the focus.

(define (rr-ineq--focus-asms)
  (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))

(define (rr-ineq--focus-goal)
  (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))

;;; 1-based indices of the ORDER-SHAPED assumptions at the focus -- the linear
;;; premises to hand the (ineq) oracle.  (Typing assumptions (IN t RR) are not
;;; linear constraints; the oracle picks those up itself for atom certification.)
(define (rr-ineq--lin-indices)
  (let loop ((as (rr-ineq--focus-asms)) (i 1) (acc '()))
    (cond ((null? as) (reverse acc))
          ((and (pair? (car as)) (memq (caar as) *rr-ineq-rel-heads*))
           (loop (cdr as) (+ i 1) (cons i acc)))
          (else (loop (cdr as) (+ i 1) acc)))))

;;; The open frontier of *ps*: ungrounded leaves (no in-arrows) -- the goals a
;;; tactic still owes.  Mirrors vnb--scout-open-leaves.
(define (rr-ineq--frontier)
  (filter (lambda (n) (null? (sequent-node-in-arrows n)))
          (proof-open-goals *ps*)))

;;; =======================================================================
;;; The generic guard-discharger.  `run' is a 2-arg (cmd args) applier -- either
;;; the raw apply-recorded-cmd! (speculative, non-recording) or the live wrappers
;;; (committing, recording into the proof script).  Both drive *ps*.

(define (rr-ineq--ok? r) (not (or (vnb-error? r) (vnb-warning? r))))

;;; Try to advance the CURRENT focus one step: a closer (ass/rfl/arith/ineq) if
;;; one fits the goal head, else a decomposition (di) to split AND/IMPLIES/FORALL
;;; guards.  Returns #t if it made a move.  Closers before di so a guard that IS
;;; an assumption closes outright rather than being pointlessly peeled.
(define (rr-ineq--advance-leaf! run)
  (let ((g (rr-ineq--focus-goal)))
    (or
     ;; goal is literally an assumption
     (and (asms-find (sequent-node-assumptions (proof-state-focus *ps*)) g)
          (rr-ineq--ok? (run 'ass '())))
     ;; t = t
     (and (pair? g) (eq? (car g) '=) (rr-ineq--ok? (run 'rfl '())))
     ;; ground arithmetic
     (and (pair? g) (memq (car g) *rr-ineq-rel-heads*)
          (rr-ineq--ok? (run 'arith '())))
     ;; linear over named order premises
     (and (pair? g) (memq (car g) *rr-ineq-rel-heads*)
          (let ((idx (rr-ineq--lin-indices)))
            (and (pair? idx) (rr-ineq--ok? (run 'ineq idx)))))
     ;; decompose a compound guard (AND of two bounds, a typing IMPLIES, ...)
     (and (pair? g) (memq (car g) '(FORALL FORSOME IMPLIES AND IFF NOT))
          (rr-ineq--ok? (run 'di '()))))))

;;; Drive every open leaf to closure with the discharger, to a fixpoint.  Returns
;;; #t iff *ps* ends fully proved.  Capped so a stuck leaf cannot spin forever.
(define (rr-ineq--close-open! run)
  (let loop ((budget 60))
    (cond
     ((proof-done? *ps*) #t)
     ((<= budget 0) #f)
     (else
      (let ((frontier (rr-ineq--frontier)) (progressed #f))
        (if (null? frontier)
            (proof-done? *ps*)
            (begin
              (for-each
               (lambda (leaf)
                 ;; still an open frontier leaf? (an earlier di may have grounded it)
                 (when (memq leaf (rr-ineq--frontier))
                   (focus-on *ps* leaf)
                   (when (rr-ineq--advance-leaf! run) (set! progressed #t))))
               frontier)
              (if progressed (loop (- budget 1)) (proof-done? *ps*)))))))))

;;; The two runners.
(define (rr-ineq--run-raw cmd args)             ; speculative: no script recording
  (vnb-guard (lambda () (apply-recorded-cmd! cmd args))))

(define (rr-ineq--run-live cmd args)            ; committing: goes through wrappers
  (case cmd
    ((ass)  (ass))
    ((rfl)  (rfl))
    ((arith)(arith))
    ((di)   (di))
    ((ineq) (apply ineq args))
    ((bc*)  (bc*-apply (car args) '()))   ; not reached by close-open; kept for parity
    (else (error "rr-ineq--run-live: unhandled cmd" cmd))))

;;; =======================================================================
;;; Speculative probes (READ-ONLY): run a lane on a scratch clone of the focus
;;; and report 'closed / 'progress / #f without touching the live state.

;;; Hard output swallow: quietly only sets suppression FLAGS, but bc*'s no-match
;;; warning and the ineq Farkas certificate print straight to the port ignoring
;;; them.  For a sweep that tries dozens of non-matching lemmas that is a wall of
;;; noise, so we also rebind current-output-port to a discarded string port.
;;; Returns THUNK's value (the captured text is thrown away).
(define (rr-ineq--silent thunk)
  (let ((result #f))
    (with-output-to-string (lambda () (set! result (quietly thunk))))
    result))

;;; Run THUNK (which drives *ps*) on a scratch clone.  'closed if it fully proved
;;; the clone, 'progress if it advanced without closing, #f if it errored/no-op.
(define (rr-ineq--probe thunk)
  (let ((clone (vnb--scratch-state)))
    (and clone
         (fluid-let ((*ps* clone))
           (rr-ineq--silent
            (lambda ()
              (let ((r (vnb-guard thunk)))
                (cond ((or (vnb-error? r) (vnb-warning? r)) #f)
                      ((proof-done? clone) 'closed)
                      (else 'progress)))))))))

;;; LINEAR lane probe: (ineq <order-premise-indices>).
(define (rr-ineq--probe-oracle)
  (let ((idx (rr-ineq--lin-indices)))
    (and (pair? idx)
         (rr-ineq--probe
          (lambda () (apply-recorded-cmd! 'ineq idx))))))

;;; CLUSTER lane probe for one lemma: bc* it, then discharge the guards.
(define (rr-ineq--probe-lemma name)
  (rr-ineq--probe
   (lambda ()
     (apply-recorded-cmd! 'bc* (list name))     ; errors out (caught) if no match
     (rr-ineq--close-open! rr-ineq--run-raw))))

;;; =======================================================================
;;; (rr-ineq-scan) -- the read-only sweep.  Structured return + ASCII table.

;;; A result record: (list lane name status) where lane in {oracle cluster},
;;; status in {closed progress no}.
(define (rr-ineq--status->sym s) (cond ((eq? s 'closed) 'closed)
                                       ((eq? s 'progress) 'progress)
                                       (else 'no)))

(define (rr-ineq-scan)
  (if (not *ps*)
      (begin (display ";; rr-ineq-scan: no proof in progress\n") '())
      (let* ((goal (rr-ineq--focus-goal))
             (results '()))
        (define (record! lane name st)
          (set! results (cons (list lane name (rr-ineq--status->sym st)) results)))
        ;; linear lane first
        (record! 'oracle 'ineq (rr-ineq--probe-oracle))
        ;; cluster lane, nonlinear-first
        (for-each
         (lambda (entry)
           (record! 'cluster (car entry) (rr-ineq--probe-lemma (car entry))))
         *rr-ineq-cluster*)
        (set! results (reverse results))
        ;; ---- ASCII report ----
        (display ";; rr-ineq-scan at the focus:\n")
        (display ";;   goal: ") (display (expression->string goal)) (newline)
        (let ((closers (filter (lambda (r) (eq? (caddr r) 'closed)) results)))
          (if (null? closers)
              (display ";;   no lane closes it outright (try (rr-ineq-scan) after more (di)/facts)\n")
              (begin
                (display ";;   CLOSES (") (display (length closers))
                (display "):\n")
                (for-each
                 (lambda (r)
                   (display ";;     [") (display (car r)) (display "] ")
                   (display (cadr r)) (newline))
                 closers)))
          ;; also surface partial (bc* matched but guards not all discharged)
          (let ((partials (filter (lambda (r) (eq? (caddr r) 'progress)) results)))
            (when (pair? partials)
              (display ";;   applies-but-leaves-guards:\n")
              (for-each
               (lambda (r)
                 (display ";;     [") (display (car r)) (display "] ")
                 (display (cadr r)) (newline))
               partials))))
        results)))

;;; =======================================================================
;;; (rr-ineq?) / (rr-ineq!) -- the applier.

;;; #t iff some lane closes the current focus (read-only, no commit).
(define (rr-ineq?)
  (and *ps* (rr-ineq--find-winner) #t))

;;; Find the first lane/lemma that CLOSES the focus, without committing.
;;; Returns (list lane name) or #f.
(define (rr-ineq--find-winner)
  (cond
   ((not *ps*) #f)
   ((eq? (rr-ineq--probe-oracle) 'closed) (list 'oracle 'ineq))
   (else
    (let loop ((cs *rr-ineq-cluster*))
      (cond ((null? cs) #f)
            ((eq? (rr-ineq--probe-lemma (caar cs)) 'closed)
             (list 'cluster (caar cs)))
            (else (loop (cdr cs))))))))

;;; Commit the winner on the LIVE state.  No-op if nothing closes.  Returns the
;;; winning (list lane name), or #f.
(define (rr-ineq!)
  (if (not *ps*)
      (begin (display ";; rr-ineq!: no proof in progress\n") #f)
      (let ((winner (rr-ineq--find-winner)))
        (cond
         ((not winner)
          (display ";; rr-ineq!: no lane closes the focus -- state untouched.\n")
          (display ";;   run (rr-ineq-scan) to see partial matches.\n")
          #f)
         ((eq? (car winner) 'oracle)
          ;; commit for real; swallow the sub-tactic chatter (state dumps, the
          ;; Farkas certificate) so only our one summary line shows.  Recording
          ;; into the proof script is independent of output, so the step is
          ;; still captured.
          (rr-ineq--silent (lambda () (apply ineq (rr-ineq--lin-indices))))
          (display ";; rr-ineq!: closed by the linear (ineq) oracle.\n")
          winner)
         (else
          (let ((name (cadr winner)))
            (rr-ineq--silent
             (lambda ()
               (bc*-apply name '())      ; = (bc* name); function form, no macro dep
               (rr-ineq--close-open! rr-ineq--run-live)))
            (display ";; rr-ineq!: closed by cluster lemma ") (display name)
            (display " (bc* + guard discharge).\n")
            winner))))))
