;;; prep.scm -- (prep 'FUBA): why will FUBA not fire here, and what must be done
;;; to make it fire?
;;;
;;; A tactic reports failure as a boolean.  `pi-ineq!' is one long `and', so every
;;; unmet precondition -- goal not order-shaped, premise not order-shaped, atom not
;;; typed in RR, goal simply false -- comes out as the same #f, printed as the one
;;; warning "goal not a linear-RR consequence of the named assumptions".  That
;;; warning is true and useless: it cannot tell "your goal needs a di" from "this
;;; is not a theorem".  `prep' runs the SAME predicates and reports WHICH failed,
;;; and searches the library for the fact that would repair it.
;;;
;;; Worked case (nn-lt-double, 2026-07-17).  |- FORALL k in NN. ~(k=0) => k < 2k.
;;; ineq refuses.  Three preps -- di, di; (fact 'nn-pos-of-nonzero 'k); (fact
;;; 'nn-in-rr 'k) -- and (ineq 4) closes it: six steps against the thirteen of the
;;; hand-built cut/crs route through k = k+0 < k+k = 2k, and a SMALLER bill
;;; (modulo {nn-pos-of-nonzero, nn-in-rr} against that route's two extra
;;; transitivity lemmas).  Each of those three preps is discoverable by shape,
;;; which is what this file does.
;;;
;;; READ-ONLY.  Every probe runs on a scratch clone (vnb--scratch-state) under a
;;; fluid-let *ps*; the live proof state is never touched.  Nothing here is a
;;; kernel rule and nothing is asserted -- prep only READS, and the plan it prints
;;; is checked by being RUN on a clone before it is shown.
;;;
;;; THE TABLE.  *prep-methods* keys a tactic name to its diagnosis procedure --
;;; the house pattern (*pss-topics*, *tactic-help*, operators.scm): one table,
;;; not a method per tactic scattered about.  A tactic joins by registering one,
;;;     (prep-method! 'FUBA (lambda (sqn) -> diagnosis))
;;; which returns a record per obligation.  `ineq' is the only entry so far; `crs'
;;; and `ass' are the obvious next two.
;;;
;;; Depends on: ineq-oracle (formula->lin+rel, ineq-atom-rr-ok?, lin-coeffs,
;;; ineq-peel-rr-foralls), suggest (vnb--scratch-state), interactive
;;; (apply-recorded-cmd!, quietly, theorem-names), macetes (*theorem-table*),
;;; kernel.  Loads after suggest.
;;;
;;; NB: `make-list' here is NOT MIT's -- expressions.scm rebinds it to build VNB
;;; LIST terms.  Hence prep--repeat below.

;;; =======================================================================
;;; The diagnosis table.

(define *prep-methods* (make-equal-hash-table))

;;; A sweep runs cmd-fact on a clone per candidate lemma; the cap keeps a
;;; pathological library from turning (prep 'ineq) into a coffee break.  It
;;; ANNOUNCES itself when it bites -- a silent truncation reads as "searched
;;; everything" when it did not.
(define *prep-sweep-cap* 400)

;;; (prep-method! TAC PROC) -- PROC takes the focus sequent node and returns the
;;; diagnosis alist.  It MUST NOT touch *ps*.
(define (prep-method! tac proc)
  (hash-table-set! *prep-methods* tac proc))

;;; Tactics that can currently be prepped.
(define (prep-methods)
  (sort (hash-table-keys *prep-methods*)
        (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

;;; An obligation record.  STATUS is met | unmet | blocked -- `unmet' means prep
;;; found a repair; `blocked' means the obligation fails and prep knows no way to
;;; fix it, which for `entailment' means the goal is not a linear consequence: no
;;; amount of prepping will help, and saying so IS the useful answer.
(define (prep--ob kind status detail repair)
  (list (cons 'obligation kind)
        (cons 'status     status)
        (cons 'detail     detail)
        (cons 'repair     repair)))

(define (prep-ob-ref r k) (cdr (assq k r)))

;;; =======================================================================
;;; Speculation.  rr-ineq.scm has cousins of these, but rr-ineq--probe reports a
;;; VERDICT ('closed / 'progress / #f) and throws the clone away.  prep needs the
;;; resulting proof STATE -- the whole point is to read the context that the preps
;;; produced, and to count the di's by watching the goal change shape.

(define (prep--repeat n x)
  (if (<= n 0) '() (cons x (prep--repeat (- n 1) x))))

;;; quietly only sets suppression FLAGS; the ineq Farkas certificate and cmd-fact
;;; chatter print straight to the port regardless.  A sweep of hundreds of lemmas
;;; would be a wall of noise, so swallow the port too.
(define (prep--silent thunk)
  (let ((result #f))
    (with-output-to-string (lambda () (set! result (quietly thunk))))
    result))

;;; Run CMDS -- a list of (NAME . ARGS) -- on a scratch clone of the live focus.
;;; Returns the resulting proof state, or #f if a step failed or there is nothing
;;; to clone.  apply-recorded-cmd! ends in (set! *ps* result) and turns a warning
;;; into an error, so the fluid binding is read back from INSIDE the extent, and a
;;; failed step is a vnb-error the guard catches rather than a silent no-op.
(define (prep--clone-run cmds)
  (let ((clone (vnb--scratch-state)) (final #f) (ok #t))
    (and clone
         (begin
           (fluid-let ((*ps* clone))
             (prep--silent
              (lambda ()
                (for-each
                 (lambda (c)
                   (when ok
                     (let ((r (vnb-guard (lambda () (apply-recorded-cmd! (car c) (cdr c))))))
                       (if (or (vnb-error? r) (vnb-warning? r)) (set! ok #f)))))
                 cmds)))
             (set! final *ps*))
           (and ok final)))))

(define (prep--goal-of ps)
  (and ps (not (proof-done? ps))
       (wff-formula (sequent-node-assertion (proof-state-focus ps)))))

(define (prep--asms-of ps)
  (if (or (not ps) (proof-done? ps))
      '()
      (sequent-node-assumptions (proof-state-focus ps))))

(define (prep--asm-formulas ps) (map wff-formula (prep--asms-of ps)))

;;; 1-based indices of the ORDER-SHAPED assumptions -- the linear premises to hand
;;; the oracle.  A typing assumption (IN k RR) is not one of them: the oracle picks
;;; those up itself, to certify atoms.
(define (prep--lin-indices ps)
  (let loop ((as (prep--asm-formulas ps)) (i 1) (acc '()))
    (cond ((null? as) (reverse acc))
          ((formula->lin+rel (car as)) (loop (cdr as) (+ i 1) (cons i acc)))
          (else (loop (cdr as) (+ i 1) acc)))))

(define (prep--head-str f)
  (if (and (pair? f) (symbol? (car f)))
      (symbol->string (car f))
      (expression->string f)))

;;; =======================================================================
;;; Library search: the repair lemmas, found by SHAPE.

(define (prep--theorem-formula nm)
  (hash-table-ref/default *theorem-table* nm #f))

;;; Strip leading universals and antecedents to reach what a lemma concludes.
(define (prep--peel-concl f)
  (let loop ((f f) (n 0))
    (cond ((> n 8) f)
          ((and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3))
           (loop (caddr f) (+ n 1)))
          ((and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3))
           (loop (caddr f) (+ n 1)))
          (else f))))

;;; The antecedents a lemma would have to discharge, after peeling universals.
(define (prep--antecedents f)
  (let loop ((f f) (n 0) (acc '()))
    (cond ((> n 8) (reverse acc))
          ((and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3))
           (loop (caddr f) (+ n 1) acc))
          ((and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3))
           (loop (caddr f) (+ n 1) (cons (cadr f) acc)))
          (else (reverse acc)))))

(define (prep--typing? f) (and (pair? f) (eq? (car f) 'IN)))
(define (prep--head-of f) (and (pair? f) (car f)))

(define (prep--some pred lst)
  (let loop ((l lst))
    (cond ((null? l) #f) ((pred (car l)) #t) (else (loop (cdr l))))))

(define (prep--uniq lst)
  (let loop ((l lst) (acc '()))
    (cond ((null? l) (reverse acc))
          ((memq (car l) acc) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

;;; The heads of the context facts the oracle CANNOT read and that are not mere
;;; typing -- here `not(k = 0)', head NOT.  These are what a bridge must consume.
(define (prep--unreadable-heads ps)
  (prep--uniq
   (map prep--head-of
        (filter (lambda (f) (and (pair? f)
                                 (not (formula->lin+rel f))
                                 (not (prep--typing? f))))
                (prep--asm-formulas ps)))))

;;; Lemmas that CONCLUDE an order relation: candidate bridges from a context fact
;;; the oracle cannot read (not(k=0)) to one it can (0<k).
;;;
;;; 1457 of the 2803 registered facts conclude an order relation, and trying each
;;; on a clone costs a cmd-fact -- nn-pos-of-nonzero is the 1076th alphabetically,
;;; so a brute sweep is ~11s and a capped one silently misses the answer.  The
;;; filter that matters: a bridge is only useful if it CONSUMES something the
;;; oracle cannot already read, so it must carry a non-typing antecedent whose
;;; head appears among the context's unreadable facts -- or none at all, which is
;;; the unconditional order fact (0 <= x*x).  Typing antecedents do not count:
;;; every lemma in the library is guarded by those.
(define (prep--bridge-candidates ps)
  (let ((heads (prep--unreadable-heads ps)))
    (filter
     (lambda (nm)
       (let ((f (prep--theorem-formula nm)))
         (and f
              (formula->lin+rel (prep--peel-concl f))
              (let ((ants (filter (lambda (a) (not (prep--typing? a)))
                                  (prep--antecedents f))))
                (or (null? ants)
                    (prep--some (lambda (a) (memq (prep--head-of a) heads)) ants))))))
     (theorem-names))))

;;; Lemmas that CONCLUDE (IN x RR): candidate coercions for an uncertified atom.
(define (prep--coercion-candidates)
  (filter (lambda (nm)
            (let* ((f (prep--theorem-formula nm))
                   (c (and f (prep--peel-concl f))))
              (and (pair? c) (= (length c) 3) (eq? (car c) 'IN)
                   (equal? (caddr c) 'RR))))
          (theorem-names)))

;;; Does (fact NM ATOM) land a formula satisfying PRED, given the assumptions OLD
;;; that were there before?  Speculative: run it on a clone and DIFF -- naming a
;;; landing by shape alone is the standing trap (dk-landed), and `fact' lands its
;;; whole instantiation chain, so the test is "did anything NEW satisfy PRED", not
;;; "look at the first thing it landed".
(define (prep--fact-lands? base old nm atom pred)
  (let ((after (prep--clone-run (append base (list (list 'fact nm (list atom)))))))
    (and after
         (let loop ((ns (prep--asm-formulas after)))
           (cond ((null? ns) #f)
                 ((and (not (member (car ns) old)) (pred (car ns))) (car ns))
                 (else (loop (cdr ns))))))))

;;; Returns the lemma name, or #f.
(define (prep--search-coercion base old atom)
  (let loop ((cs (prep--coercion-candidates)) (n 0))
    (cond ((null? cs) #f)
          ((> n *prep-sweep-cap*)
           (display ";; prep: coercion sweep hit the cap at ")
           (display *prep-sweep-cap*) (display " lemmas; search TRUNCATED\n")
           #f)
          ((prep--fact-lands? base old (car cs) atom
                              (lambda (f) (and (pair? f) (= (length f) 3)
                                               (eq? (car f) 'IN)
                                               (equal? (cadr f) atom)
                                               (equal? (caddr f) 'RR))))
           (car cs))
          (else (loop (cdr cs) (+ n 1))))))

;;; Every (NAME . ATOM) that would LAND an order-shaped premise.  Landing one is
;;; necessary, not sufficient: `bt-lt-succ' lands k < succ(k), which is true, order-
;;; shaped, and no use for k < 2k.  Which candidate is the REPAIR is settled by
;;; prep--try-close, i.e. by whether ineq then fires -- that is what "what must be
;;; done to apply ineq" means.  Picking the first lander instead names a lemma
;;; alphabetically, which is how this first reported (fact 'bt-lt-succ 'k).
(define (prep--search-bridges base old atoms ps)
  (let loop ((cs (prep--bridge-candidates ps)) (n 0) (acc '()))
    (cond ((null? cs) (reverse acc))
          ((> n *prep-sweep-cap*)
           (display ";; prep: bridge sweep hit the cap at ")
           (display *prep-sweep-cap*) (display " lemmas; search TRUNCATED\n")
           (reverse acc))
          (else
           (let try ((as atoms))
             (cond ((null? as) (loop (cdr cs) (+ n 1) acc))
                   ((prep--fact-lands? base old (car cs) (car as)
                                       (lambda (f) (formula->lin+rel f)))
                    (loop (cdr cs) (+ n 1) (cons (cons (car cs) (car as)) acc)))
                   (else (try (cdr as)))))))))

;;; BASE, then optionally one bridge, then ineq over whatever premises are then
;;; order-shaped.  Returns EVERY option that actually closes the goal on a clone,
;;; as a list of (BRIDGE . FULL-PLAN); BRIDGE is #f for the no-bridge option.
;;;
;;; All of them, not the first: the options are alphabetical, which is no order of
;;; merit.  If the goal is itself a library theorem, citing IT is a closer -- prep
;;; on nn-lt-double duly offers (fact 'nn-lt-double 'k), which is valid, circular,
;;; and sorts before the nn-pos-of-nonzero you wanted.  Report the choice rather
;;; than make it badly.
(define (prep--all-closers base options)
  (let loop ((os options) (acc '()))
    (if (null? os)
        (reverse acc)
        (let* ((bridge (car os))
               (plan   (if bridge
                           (append base (list (list 'fact (car bridge) (list (cdr bridge)))))
                           base))
               (ps     (prep--clone-run plan))
               (idx    (if ps (prep--lin-indices ps) '()))
               (full   (append plan (list (cons 'ineq idx))))
               (out    (and ps (prep--clone-run full))))
          (loop (cdr os)
                (if (and out (proof-done? out)) (cons (cons bridge full) acc) acc))))))

;;; =======================================================================
;;; The ineq method.

;;; How many di's make the focus goal order-shaped?  MEASURED, not modelled: one
;;; di consumes a typed FORALL and its guard together, and no static count of the
;;; goal's connectives gets that right.
(define (prep--di-depth cap)
  (let loop ((n 0))
    (cond ((> n cap) #f)
          (else
           (let ((ps (prep--clone-run (prep--repeat n '(di)))))
             (if (and ps (not (proof-done? ps)) (formula->lin+rel (prep--goal-of ps)))
                 n
                 (loop (+ n 1))))))))

;;; The atoms of the goal that the oracle would have to certify in RR.
(define (prep--goal-atoms ps)
  (let* ((g   (prep--goal-of ps))
         (gpr (and g (formula->lin+rel g))))
    (if gpr (map car (lin-coeffs (car gpr))) '())))

(define (prep--atom-typed? ps atom)
  (ineq-atom-rr-ok? atom (prep--asms-of ps)
                    (cdr (ineq-peel-rr-foralls (prep--goal-of ps)))))

(define (prep--ineq sqn)
  (let* ((obs  '())
         (plan '())
         (live (wff-formula (sequent-node-assertion sqn))))
    (define (add! ob) (set! obs (append obs (list ob))))

    ;; ---- 1. the goal must BE an order relation (formula->lin+rel of the goal)
    (let ((d (prep--di-depth 6)))
      (if (not d)
          (add! (prep--ob 'goal-shape 'blocked
                          (string-append "goal is " (prep--head-str live)
                                         "-headed and no run of di reaches an order relation")
                          '()))
          (begin
            (if (= d 0)
                (add! (prep--ob 'goal-shape 'met "goal is already an order relation" '()))
                (add! (prep--ob 'goal-shape 'unmet
                                (string-append "goal is " (prep--head-str live)
                                               "-headed, not < / <= / =")
                                (prep--repeat d '(di)))))
            (set! plan (prep--repeat d '(di)))

            ;; ---- 2. every atom must be certified in RR by ineq-atom-rr-ok?,
            ;; which is a LITERAL (IN atom RR) scan: (IN k NN) does not count, the
            ;; oracle does no subtype reasoning at all.
            (let* ((ps    (prep--clone-run plan))
                   (old   (prep--asm-formulas ps))
                   (atoms (prep--goal-atoms ps))
                   (bad   (filter (lambda (a) (not (prep--atom-typed? ps a))) atoms)))
              (if (null? bad)
                  (add! (prep--ob 'atom-typing 'met
                                  (string-append (number->string (length atoms))
                                                 " atom(s) certified in RR")
                                  '()))
                  (for-each
                   (lambda (atom)
                     (let ((hit (prep--search-coercion plan old atom)))
                       (if hit
                           (let ((cmd (list 'fact hit (list atom))))
                             (add! (prep--ob 'atom-typing 'unmet
                                             (string-append "atom " (expression->string atom)
                                                            " is not certified in RR")
                                             (list cmd)))
                             (set! plan (append plan (list cmd))))
                           (add! (prep--ob 'atom-typing 'blocked
                                           (string-append "atom " (expression->string atom)
                                                          " is not in RR and no library lemma coerces it")
                                           '())))))
                   bad)))

            ;; ---- 3 and 4 together.  The oracle needs an order-shaped PREMISE (a
            ;; context fact like not(k=0) is invisible to Farkas), and the goal
            ;; must actually FOLLOW from the premises.  These are one search: which
            ;; bridge repairs the context is decided by whether ineq then fires.
            (let* ((ps      (prep--clone-run plan))
                   (idx0    (prep--lin-indices ps))
                   (bridges (if (pair? idx0)
                                '()
                                (prep--search-bridges plan (prep--asm-formulas ps)
                                                      (prep--goal-atoms ps) ps)))
                   (options (if (pair? idx0) (list #f) bridges))
                   (wins    (prep--all-closers plan options))
                   (win     (and (pair? wins) (car wins)))
                   (bridge  (and win (car win))))

              ;; premise-shape
              (cond
               ((pair? idx0)
                (add! (prep--ob 'premise-shape 'met
                                (string-append "order-shaped assumption(s) at "
                                               (str-join (map number->string idx0) ", "))
                                '())))
               (bridge
                (add! (prep--ob 'premise-shape 'unmet
                                (string-append
                                 "no assumption is an order relation; Farkas cannot read the context"
                                 (if (> (length wins) 1)
                                     (string-append " -- "
                                                    (number->string (length wins))
                                                    " lemmas repair it, any one will do")
                                     ""))
                                (map (lambda (w)
                                       (list 'fact (car (car w)) (list (cdr (car w)))))
                                     wins))))
               ((pair? bridges)
                (add! (prep--ob 'premise-shape 'unmet
                                (string-append "no assumption is an order relation; "
                                               (number->string (length bridges))
                                               " library lemma(s) would supply one, none of which makes the goal follow")
                                '())))
               (else
                (add! (prep--ob 'premise-shape 'blocked
                                "no assumption is an order relation and no library lemma yields one"
                                '()))))

              ;; entailment
              (if win
                  (begin
                    (add! (prep--ob 'entailment 'met
                                    "goal follows from the premises by Fourier-Motzkin"
                                    '()))
                    (set! plan (cdr win)))
                  (begin
                    (add! (prep--ob 'entailment 'blocked
                                    "not a linear consequence of the available premises -- no prepping of ineq closes this goal"
                                    '()))
                    (set! plan '())))))))

    (let ((result (list (cons 'tactic 'ineq)
                        (cons 'obligations obs)
                        (cons 'plan plan)
                        (cons 'verified (pair? plan)))))
      (prep--report result)
      result)))

;;; =======================================================================
;;; Reporting.  The plan is printed as SURFACE syntax, to be pasted at the REPL.

(define (prep--status-mark s)
  (case s ((met) "ok  ") ((unmet) "PREP") ((blocked) "STOP") (else "?   ")))

(define (prep--cmd-str c)
  (case (car c)
    ((fact)
     (string-append "(fact '" (symbol->string (cadr c))
                    (apply string-append
                           (map (lambda (a) (string-append " '" (expression->string a)))
                                (caddr c)))
                    ")"))
    ((ineq)
     (string-append "(ineq" (if (null? (cdr c)) ""
                                (string-append " " (str-join (map number->string (cdr c)) " ")))
                    ")"))
    (else (with-output-to-string (lambda () (write c))))))

(define (prep--report result)
  (let ((obs  (cdr (assq 'obligations result)))
        (plan (cdr (assq 'plan result)))
        (tac  (cdr (assq 'tactic result))))
    (newline)
    (display ";; prep ") (display tac) (display ": obligations at the focus\n")
    (display ";; --------------------------------------------------------------\n")
    (for-each
     (lambda (ob)
       (display ";;  [") (display (prep--status-mark (prep-ob-ref ob 'status)))
       (display "] ") (display (prep-ob-ref ob 'obligation))
       (display " -- ") (display (prep-ob-ref ob 'detail)) (newline)
       (for-each (lambda (r)
                   (display ";;         repair: ") (display (prep--cmd-str r)) (newline))
                 (prep-ob-ref ob 'repair)))
     obs)
    (display ";; --------------------------------------------------------------\n")
    (if (pair? plan)
        (begin
          (display ";; PLAN -- checked: this closes the goal on a scratch clone\n")
          (for-each (lambda (c) (display ";;    ") (display (prep--cmd-str c)) (newline))
                    plan))
        (display ";; NO PLAN -- see the STOP line above.\n"))
    (newline)))

;;; =======================================================================
;;; The surface.

;;; (prep 'ineq) -- diagnose the focus, commit nothing.  Prints the obligation
;;; table and the plan; RETURNS the records.
(define (prep tac)
  (cond
   ((not (symbol? tac))
    (display ";; prep: give a tactic NAME, quoted: (prep 'ineq)\n") #f)
   ((or (not *ps*) (proof-done? *ps*))
    (display ";; prep: no open goal at the focus\n") #f)
   (else
    (let ((m (hash-table-ref/default *prep-methods* tac #f)))
      (if m
          (m (proof-state-focus *ps*))
          (begin
            (display ";; prep: no diagnosis method for ") (display tac)
            (display "; have: ") (display (prep-methods)) (newline)
            #f))))))

(prep-method! 'ineq prep--ineq)
