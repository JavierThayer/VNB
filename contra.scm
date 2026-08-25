;;; contra.scm -- (contra): close a branch whose CONTEXT is arithmetically
;;; inconsistent.
;;;
;;; WHY THIS EXISTS.  A proof by cases or by unfolding a membership routinely
;;; produces a branch that cannot happen, and the reason is a handful of order
;;; facts that cannot all hold.  The worked example is the base case of a list
;;; induction on cardinality (2026-08-15), where unfolding
;;; `make-set-membership' leaves
;;;
;;;     nth(i,l) = x,  i <= length(l),  1 <= i,  i in nn,
;;;     x in set,  length(l) = 0,  l in tuples(a)   |-   x in empty-set
;;;
;;; The goal is unprovable on its own -- nothing is in the empty set -- and the
;;; branch closes only because `1 <= i <= length(l) = 0' is absurd.  The user
;;; hit exactly this and reported "context is clearly contradictory, but I'm
;;; stuck", and the copilot had nothing to say, because:
;;;
;;;   * `prop' treats every atom as opaque, so `1 <= i', `i <= length(l)' and
;;;     `length(l) = 0' are three unrelated propositions to it.  It correctly
;;;     reports a countermodel.
;;;   * `ineq' can do the arithmetic, but it must be handed the RIGHT premise
;;;     indices by hand, and until 2026-08-15 naming one non-arithmetic
;;;     assumption among them made the whole call fail.
;;;
;;; So the arithmetic was reachable and nothing reached it.  `contra' does.
;;;
;;; TRUST.  It adds none.  The inconsistency is certified by `ineq' -- already a
;;; warranted oracle with a Farkas certificate -- and the closure is then
;;; discharged through ordinary rules: `have!' the absurdity, `have!' its
;;; arithmetic refutation, `ai' the negation against the positive.  A `qed' over
;;; a contra-closed proof bills exactly what `ineq' bills and nothing more.
;;;
;;; IT PROBES BEFORE IT COMMITS.  There is no undo in the deduction graph, so a
;;; composite that cuts first and discovers afterwards that the context was
;;; consistent would leave two unprovable leaves behind.  `contra' runs the
;;; whole attempt on a scratch state first (`vnb--scratch-state', suggest.scm --
;;; which is why this file loads after it) and touches the live proof only when
;;; the scratch run closed.

;;; 1-based indices of every assumption of the focus.
(define (contra--all-indices)
  (let ((n (length (sequent-node-assumptions (proof-state-focus *ps*)))))
    (let lp ((k 1)) (if (> k n) '() (cons k (lp (+ k 1)))))))

;;; The indices `ineq' can actually USE: order formulas all of whose atoms are
;;; RR-certified.  Naming anything else poisons the call.
;;;
;;; `ineq' now SKIPS a named premise that is not arithmetic at all -- but an
;;; arithmetic premise whose ATOMS are not RR-certifiable is a different and
;;; fatal thing, because `ineq-atom-rr-ok?' runs over the union of the atoms of
;;; every premise it accepted.  In the motivating leaf the equation
;;;
;;;     nth(i, l) = x
;;;
;;; is arithmetic in shape, so it is accepted, and it contributes the atoms `x'
;;; and `nth(i,l)' -- neither of which is a real number and neither of which can
;;; ever be certified.  One irrelevant equation in the context therefore killed
;;; a call whose real premises (1 <= i, i <= length(l), length(l) = 0) were
;;; perfectly good.  So filter FIRST, by exactly the oracle's own test.
(define (contra--usable-indices)
  (let* ((sqn  (proof-state-focus *ps*))
         (asms (sequent-node-assumptions sqn)))
    (let loop ((as asms) (k 1) (acc '()))
      (if (null? as)
          (reverse acc)
          (let ((f (wff-formula (car as))))
            (loop (cdr as) (+ k 1)
                  (if (and (contra--order-formula? f)
                           (let ((ats (contra--atoms-of (caddr f)
                                        (contra--atoms-of (cadr f) '()))))
                             (let allok ((vs ats))
                               (or (null? vs)
                                   (and (contra--already-rr? (car vs))
                                        (allok (cdr vs)))))))
                      (cons k acc)
                      acc)))))))

;;; The absurdity we drive at.  `1 <= 0' is ground, so `arith' refutes it
;;; without any typing hypothesis -- which matters, because the variables in the
;;; context are typically NN-typed and `arith' is the only closer that needs
;;; nothing of them.
(define *contra-absurdity* '(<= 1 0))

;;; DISCHARGING ineq's PRECONDITION, which is the whole reason this is a
;;; composite and not a one-liner.  `ineq-atom-rr-ok?' (ineq-oracle.scm) demands
;;; that every maximal non-arithmetic subterm of the goal and premises be
;;; certified `IN _ RR' by an assumption.  A combinatorial context types its
;;; terms in NN -- `i in nn' -- so the oracle refuses every such goal, which is
;;; why the arithmetic in the motivating leaf was unreachable although it is
;;; trivial.  Rather than weaken the oracle (it is TRUSTED; widening what it
;;; accepts widens the trusted surface), `contra' supplies what it asks for.
;;;
;;; Two steps, in this order:
;;;   1. land every `IN t NN' the context already FIRES but has not stated --
;;;      `length(l) in nn' from `l in tuples(a)' via `length-in-nn' is the case
;;;      that matters, and the forward-citation scan (suggest.scm) finds it
;;;      generically rather than by a hard-coded lemma name;
;;;   2. lift every `IN t NN' to `IN t RR' by `nn-in-rr' (proven, modulo 0).
;;; Both are ordinary citations; neither adds trust.

(define (contra--nn-typed-terms)
  (let loop ((as (sequent-node-assumptions (proof-state-focus *ps*))) (acc '()))
    (if (null? as)
        (reverse acc)
        (let ((f (wff-formula (car as))))
          (loop (cdr as)
                (if (and (pair? f) (memq (car f) '(IN in)) (= (length f) 3)
                         (eq? (caddr f) 'NN))
                    (cons (cadr f) acc)
                    acc))))))

(define (contra--already-rr? t)
  (let loop ((as (sequent-node-assumptions (proof-state-focus *ps*))))
    (and (pair? as)
         (or (let ((f (wff-formula (car as))))
               (and (pair? f) (memq (car f) '(IN in)) (= (length f) 3)
                    (equal? (cadr f) t) (eq? (caddr f) 'RR)))
             (loop (cdr as))))))

;;; The ATOMS the oracle will need certified: the maximal non-arithmetic
;;; subterms of the context's order facts.  Only these matter -- typing every
;;; term in sight is what made the first version drag in junk citations (and a
;;; degenerate `have!' of `(and (in i nn) (in i nn))', which errors).
(define *contra-arith-heads* '(+ - * recip abs succ binplus binneg bintimes))

(define (contra--order-formula? f)
  (and (pair? f) (memq (car f) '(<= < >= > = ==)) (= (length f) 3)))

(define (contra--atoms-of term acc)
  (cond ((number? term) acc)
        ((symbol? term) (if (member term acc) acc (cons term acc)))
        ((pair? term)
         (if (memq (car term) *contra-arith-heads*)
             (let lp ((l (cdr term)) (a acc))
               (if (null? l) a (lp (cdr l) (contra--atoms-of (car l) a))))
             (if (member term acc) acc (cons term acc))))
        (else acc)))

(define (contra--arith-atoms)
  (let loop ((as (sequent-node-assumptions (proof-state-focus *ps*))) (acc '()))
    (if (null? as)
        acc
        (let ((f (wff-formula (car as))))
          (loop (cdr as)
                (if (contra--order-formula? f)
                    (contra--atoms-of (caddr f) (contra--atoms-of (cadr f) acc))
                    acc))))))

;;; Land the NN typings those atoms need (step 1).  Only citations that land
;;; exactly `IN <atom> NN' and need no `have!' -- speculative enrichment should
;;; never be able to error, and the ineq call is what actually decides.
(define (contra--land-nn-typings!)
  (let* ((sqn   (proof-state-focus *ps*))
         (atoms (contra--arith-atoms))
         (hits  (what-now--forward-citations
                 (wff-formula (sequent-node-assertion sqn))
                 (map wff-formula (sequent-node-assumptions sqn)))))
    (for-each
     (lambda (h)
       (let ((landed (caddr h)) (have (list-ref h 4)))
         (when (and (not have)
                    (pair? landed) (memq (car landed) '(IN in))
                    (= (length landed) 3) (eq? (caddr landed) 'NN)
                    (member (cadr landed) atoms))
           (vnb-guard (lambda () (apply fact (car h) (cadr h)))))))
     hits)))

(define (contra--lift-to-rr!)
  (for-each (lambda (t)
              (unless (contra--already-rr? t)
                (vnb-guard (lambda () (fact 'nn-in-rr t)))))
            (contra--nn-typed-terms)))

;;; The whole move, as run on either the live state or a scratch clone.
;;; Returns #t if it closed the focus goal.
(define (contra--attempt!)
  (contra--land-nn-typings!)
  (contra--lift-to-rr!)
  (let ((idxs (contra--usable-indices)))
    (have! *contra-absurdity* (lambda () (apply ineq idxs)))
    (have! (list 'NOT *contra-absurdity*) (lambda () (arith)))
    (ai (list 'NOT *contra-absurdity*))
    #t))

(define (contra--probe)
  (let ((scratch (vnb--scratch-state)))
    (and scratch
         (eq? 'closed
              (vnb--probing scratch
                (lambda ()
                  (let ((r (vnb-guard (lambda () (contra--attempt!)))))
                    (if (and (not (vnb-error? r)) (proof-done? scratch))
                        'closed
                        'open))))))))

;;; NOT wrapped in `vnb--run!', and deliberately -- same shape as `prop'.
;;; `vnb--run!' takes the thunk's RETURN VALUE to be the new proof state and
;;; assigns it to `*ps*'; a composite whose thunk ends in a `display' therefore
;;; set `*ps*' to #!unspecific and the following `show' died with "The object
;;; #!unspecific ... is not the correct type", AFTER announcing success.  A
;;; composite drives ordinary tactics (`have!', `ai'), each of which already
;;; updates `*ps*' and records itself, so the wrapper has nothing to add.  The
;;; recorded script is therefore the step-by-step proof, not a `(contra)' line.
;;; SAY IT, do not merely construct it.  `vnb--warn' (proof-commands.scm) only
;;; BUILDS a <vnb-warning> record; the thing that prints it is `vnb--run!', and
;;; `contra' is deliberately not wrapped in `vnb--run!' (see above).  So both
;;; declining branches returned a warning nobody ever displayed, and from a
;;; script `contra' was indistinguishable from a tactic that does not exist --
;;; the carefully worded "the context's arithmetic is satisfiable" message was
;;; unreachable.  Found 2026-08-16 by an agent driving the base case, which is
;;; exactly the case where `contra' correctly declines.  `prop' avoids this by
;;; printing through its own `prop--say'; this is the same fix.
(define (contra--warn msg str)
  (vnb--print-warning (if (string-null? str)
                          msg
                          (string-append msg ": " str))))

(define (contra)
  (cond
        ((or (not *ps*) (proof-done? *ps*))
         (contra--warn "contra: no open goal" ""))
        ((not (contra--probe))
         ;; Say WHICH atoms were available, the way `prop' names its
         ;; countermodel: the usual cause is an order fact still bound up in a
         ;; hypothesis that has not been unfolded, or one that needs a citation
         ;; (`length-in-nn') before it is in the context at all.
         (contra--warn
          "contra: the context's arithmetic is satisfiable -- no contradiction to exploit"
          (vnb--goal-str (proof-state-focus *ps*))))
        (else
         (contra--attempt!)
         (display ";; contra: context is arithmetically inconsistent -- branch closed.")
         (newline))))
