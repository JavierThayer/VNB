;;; ineq-supply.scm -- the What Now lane that SUPPLIES the inequalities the
;;; linear oracle cannot see, so that Fourier-Motzkin can finish the goal.
;;;
;;; THE USER'S DESIGN, 2026-08-19: "If there is a d(x,y) <= something then cut
;;; with triangle-inequality.  More generally look for ways to add known
;;; inequalities to make a Farkas-FUBA algorithm usable."  The case that
;;; prompted it wanted `forall([a in rr, b in rr], a <= max(a,b))'.
;;;
;;; WHY THE ORACLE NEEDS HELP, and it is not a defect in the oracle.  `ineq'
;;; linearizes over + - * and treats everything else as an opaque ATOM.  So
;;; `max(a,b)' and `(dist(s))(x,y)' are variables to it, and it has no way to
;;; know that `a <= max(a,b)' or that d obeys the triangle inequality.  Land
;;; those facts as premises and the goal becomes a linear consequence, which the
;;; oracle then decides with a Farkas certificate.  Verified end to end before
;;; this file was written:
;;;
;;;   max(a,b) <= c |- a <= c        rr-max-closed + rr-le-max-left, then ineq
;;;                                  => ((h1 . 1) (goal . 1) (h11 . 1))
;;;   d(x,y)+d(y,z) <= e |- d(x,z) <= e
;;;                                  metric-space-class, metric-dist-real x3,
;;;                                  metric-triangle, then ineq
;;;                                  => ((h1 . 1) (goal . 1) (h24 . 1))
;;;
;;; THREE OBSTACLES THE PROBE FOUND, all of which this lane has to handle:
;;;
;;; 1. `(ineq)' WITH NO ARGUMENTS PROVES NOTHING.  It takes premise INDICES, so
;;;    naming none means no premises -- and it then reports "goal not a
;;;    linear-RR consequence of the named assumptions", which is true and reads
;;;    as though the goal were wrong.  The max goal above closes with the
;;;    indices named and fails without them, everything else being equal.  So
;;;    this lane always emits the explicit index list.
;;; 2. THE ATOM CERTIFICATE.  `ineq-atom-rr-ok?' (structure-library/
;;;    ineq-oracle.scm:112) requires `(IN v RR)' in the context for every atom
;;;    it does not otherwise know.  Supplying the BOUND without the TYPING gets
;;;    nowhere, so each table entry carries both.  This is the same
;;;    precondition `contra' discharges for NN, one level up.
;;; 3. THE CLASS BRIDGE.  `forall([m in metric-space], ...)' puts
;;;    `m in metric-space' in the context, while every metric theorem is guarded
;;;    on `is-metric-space(m)'.  `fact' then lands the IMPLICATION, silently,
;;;    and every later step runs against a hypothesis that never arrived.
;;;    `<NAME>-class' (generated for every declared structure) bridges it and
;;;    `mac-h' applies it.  Handled generically below, by name.
;;;
;;; IT NAMES MOVES, IT DOES NOT COMMIT.  Every move it prints is a real tactic
;;; call the reader can run, and the lane probes the whole sequence on a scratch
;;; clone (`vnb--scratch-state') to say whether it closes.  It adds no trust:
;;; the moves are `fact', `mac-h' and `ineq', which is exactly what a hand proof
;;; would use.  Committing is `rr-ineq!'-shaped work and is deliberately not
;;; done here.
;;;
;;; Loads after `suggest' (vnb--probing, vnb--scratch-state) and after
;;; `cite-index'.  The lemma names are resolved at CALL time, so the theorem
;;; files it cites may load later.

;;; -----------------------------------------------------------------------
;;; The curated table.
;;;
;;; Each entry:  (KEY MATCH CERT BOUNDS)
;;;   MATCH   term -> the argument list to build citations from, or #f
;;;   CERT    the lemma landing `(IN <term> RR)' -- the atom certificate
;;;   BOUNDS  lemma names landing inequalities about the term
;;; Both CERT and BOUNDS are cited at MATCH's argument list.  A THIRD-POINT
;;; entry (the triangle) is handled separately: its extra argument comes from
;;; the sequent, not from the term.
;;;
;;; Curated, not measured, and deliberately so: these are the facts a
;;; mathematician reaches for without thinking, and there is no sample to
;;; measure them from ([[project_cite_index]] shows the frequency index says
;;; nothing in an area the library has not already covered).

(define (ineq-supply--max-args t)
  (and (pair? t) (eq? (car t) 'max) (= (length t) 3) (cdr t)))

(define (ineq-supply--abs-args t)
  (and (pair? t) (eq? (car t) 'abs) (= (length t) 2) (cdr t)))

(define (ineq-supply--min-args t)
  (and (pair? t) (eq? (car t) 'min) (= (length t) 3) (cdr t)))

;;; ((DIST s) x y) -- the head is itself an application, so the structure comes
;;; out of the head and the points out of the arguments.
(define (ineq-supply--dist-parts t)
  (and (pair? t) (pair? (car t)) (eq? (car (car t)) 'DIST)
       (= (length (car t)) 2) (= (length t) 3)
       (list (cadr (car t)) (cadr t) (caddr t))))     ; (s x y)

(define *ineq-supply-table*
  (list
   (list 'max ineq-supply--max-args
         'rr-max-closed
         '(rr-le-max-left rr-le-max-right))
   (list 'abs ineq-supply--abs-args
         'rr-abs-closed
         '(rr-le-abs rr-neg-abs-le rr-abs-nonneg))
   (list 'min ineq-supply--min-args
         'rr-min-closed
         '(rr-min-le-left rr-min-le-right))
   (list 'dist ineq-supply--dist-parts
         'metric-dist-real
         '(metric-pos))))

;;; WANTED but absent from the library, so deliberately NOT in the table --
;;; naming a lemma that does not exist would make the lane emit moves that
;;; cannot run.  `(ineq-supply-audit)' reports both halves.
;;;
;;; `min' was the sole entry here and was CLOSED on 2026-08-21: the head is
;;; registered (wff.scm), the defining equation is `rr-min-def'
;;; (number-systems.scm) and the three lemmas this entry named are proven in
;;; theorem-library/rr-min-basics.scm.  It is in the table above.  The list is
;;; empty and that is the good case; it is kept because a gap recorded is a gap
;;; someone can close, and this one was closed by being written down.
(define *ineq-supply-wanted* '())

;;; -----------------------------------------------------------------------
;;; Finding the atoms.

;;; Every subterm of the sequent that some table entry matches, deduplicated,
;;; as (ENTRY . TERM) pairs.
(define (ineq-supply--atoms goal asms)
  (let ((seen '()) (out '()))
    (for-each
     (lambda (f)
       (for-each
        (lambda (t)
          (unless (member t seen)
            (set! seen (cons t seen))
            (for-each
             (lambda (e) (if ((cadr e) t) (set! out (cons (cons e t) out))))
             *ineq-supply-table*)))
        (what-now--subterms f)))
     (cons goal asms))
    (reverse out)))

;;; The metric points in the sequent -- the candidate intermediate points for
;;; the triangle inequality.  THIS is the only real choice the lane makes: the
;;; triangle needs a third point and the sequent's own points are the candidate
;;; list.  Read off `(IN p (PTS s))' assumptions, so it is the points the
;;; context has actually typed.
(define (ineq-supply--points s asms)
  (let loop ((as asms) (acc '()))
    (cond ((null? as) (reverse acc))
          (else
           (let ((f (car as)))
             (loop (cdr as)
                   (if (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'PTS)
                            (equal? (cadr (caddr f)) s)
                            (not (member (cadr f) acc)))
                       (cons (cadr f) acc)
                       acc)))))))

;;; The class bridges the context needs: an assumption `(IN v CLS)' for which
;;; `<cls>-class' is a theorem becomes `(mac-h '<cls>-class k)'.  Generic --
;;; `declare-structure' generates the iff for every structure, so this is not a
;;; metric-space special case.
(define (ineq-supply--bridges asms)
  (let loop ((as asms) (k 1) (acc '()))
    (if (null? as)
        (reverse acc)
        (let* ((f (car as))
               (cls (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                         (symbol? (caddr f)) (caddr f)))
               (nm  (and cls (string->symbol
                              (string-append (symbol->string cls) "-class")))))
          (loop (cdr as) (+ k 1)
                (if (and nm (hash-table-ref/default *theorem-table* nm #f))
                    (cons (list 'mac-h (list 'quote nm) k) acc)
                    acc))))))

;;; A citation, as `fact' takes it (see what-now--term-arg: compound terms go in
;;; as quoted S-expressions).  Returns #f when the lemma is not in the library,
;;; so a table entry that outruns the tree is skipped rather than emitted.
(define (ineq-supply--cite name args)
  (and (hash-table-ref/default *theorem-table* name #f)
       (cons 'fact (cons (list 'quote name) (map (lambda (a) (list 'quote a)) args)))))

;;; -----------------------------------------------------------------------
;;; Typing a SUMMAND, for the triangle inequality.
;;;
;;; `rr-abs-triangle-c' is guarded on `u in rr' and `v in rr', and `fact' with a
;;; missing guard lands the IMPLICATION -- silently, which is the trap CLAUDE.md
;;; documents and the reason a triangle citation emitted without the typings
;;; would be worse than none.  A typing already in the context costs nothing;
;;; otherwise the FORWARD lane is asked for a citation that lands it.
;;;
;;; That composition is the whole point.  On the leaf this was written for --
;;; the induction step of series-partial-sum-abs-le -- the panel was ALREADY
;;; printing `(fact 'series-partial-sum-in-rr 'k 'f)' and
;;; `(fact 'fun-apply-type-c 'f 'nn 'rr 'k)' in the forward lane, twenty lines
;;; above a supply lane that could not use them. Neither half was missing; only
;;; the join was.  See [[reference_typing_chain_lane]].
(define (ineq-supply--hit->fact h)
  (cons 'fact (cons (list 'quote (car h))
                    (map what-now--typing-arg (cadr h)))))

;;; The first forward citation in FWD that lands WANT, as a `fact' form, or #f.
(define (ineq-supply--fwd-cite fwd want)
  (let lp ((h fwd))
    (cond ((null? h) #f)
          ((and (pair? (car h)) (alpha-equiv? want (caddr (car h))))
           (ineq-supply--hit->fact (car h)))
          (else (lp (cdr h))))))

(define (ineq-supply--rr-typing-cite term asms fwd)
  (let ((want (list 'IN term 'RR)))
    (and (not (any-pred (lambda (a) (alpha-equiv? a want)) asms))
         (ineq-supply--fwd-cite fwd want))))

;;; -----------------------------------------------------------------------
;;; CERTIFYING THE PREMISES' OWN ATOMS -- the other half of the same problem.
;;;
;;; `ineq-atom-rr-ok?' (structure-library/ineq-oracle.scm:112) demands an
;;; `IN t RR' for every atom of every premise it accepts, so a context
;;; inequality whose terms are not certified is DROPPED, and the oracle then
;;; reports -- truthfully -- that the goal is not a linear consequence of what
;;; remains.  Nothing in that message says a typing was missing, and the
;;; premise it silently declined is usually the induction hypothesis.
;;;
;;; DEPTH 2, and that is why this is not one lookup.  On the leaf this was
;;; written for the uncertified atom is `series-partial-sum(L, k)' where L is
;;; the abs-sequence.  `series-partial-sum-in-rr' types it -- but is guarded on
;;; `L in FUN(NN,RR)', which is `abs-seq-in-fun', a SECOND citation.  One
;;; forward pass cannot find it: the guard is not in the context until the first
;;; citation has been made.  So a failed direct lookup extends the context by
;;; the MEMBERSHIP landings whose subject occurs in the atom -- an exact filter,
;;; not a guess -- and asks again.
;;;
;;; The atom enumeration is `contra''s, which is the ORACLE'S OWN test rather
;;; than a second opinion about what it will accept.
(define (ineq-supply--uncertified goal asms)
  (let ((ats (let loop ((fs (cons goal asms)) (acc '()))
               (if (null? fs)
                   acc
                   (loop (cdr fs)
                         (if (contra--order-formula? (car fs))
                             (contra--atoms-of (caddr (car fs))
                                               (contra--atoms-of (cadr (car fs)) acc))
                             acc))))))
    ;; compound atoms only: a bare variable's typing comes from the context or
    ;; from an NN->RR lift, neither of which is a library citation
    (let keep ((l ats) (out '()))
      (cond ((null? l) (reverse out))
            ((and (pair? (car l)) (not (contra--already-rr? (car l))))
             (keep (cdr l) (cons (car l) out)))
            (else (keep (cdr l) out))))))

(define *ineq-supply-certify-cap* 4)

(define (ineq-supply--certify goal asms fwd)
  (let ((out '()))
    (let loop ((ts (ineq-supply--uncertified goal asms)) (n 0))
      (if (and (pair? ts) (< n *ineq-supply-certify-cap*))
          (let* ((t      (car ts))
                 (target (list 'IN t 'RR))
                 (direct (ineq-supply--fwd-cite (fwd) target)))
            (if direct
                (set! out (cons direct out))
                (let ((helpers
                       (filter (lambda (h)
                                 (let ((l (caddr h)))
                                   (and (pair? l) (memq (car l) '(IN in)) (= (length l) 3)
                                        (not (eq? (caddr l) 'RR))
                                        ;; the SUBJECT must be a constructed
                                        ;; term, not a bare variable.  A
                                        ;; variable's memberships are already in
                                        ;; the context and match every atom that
                                        ;; mentions it -- `nn in set', `k in zz',
                                        ;; `f in fun(nn,rr)' all passed the
                                        ;; occurrence test and none of them was
                                        ;; the guard that blocked the citation.
                                        ;; What blocks a citation ABOUT a
                                        ;; constructed term is a membership OF
                                        ;; that constructed term.
                                        (pair? (cadr l))
                                        (what-now--occurs? (cadr l) t))))
                               (fwd))))
                  (if (pair? helpers)
                      (let* ((ext  (append (map caddr helpers) asms))
                             (fwd2 (let ((r (vnb-guard
                                             (lambda ()
                                               (what-now--forward-citations goal ext)))))
                                     (if (or (vnb-error? r) (vnb-warning? r) (not (list? r)))
                                         '() r)))
                             (hit  (ineq-supply--fwd-cite fwd2 target)))
                        (if hit
                            (begin
                              (for-each (lambda (h)
                                          (set! out (cons (ineq-supply--hit->fact h) out)))
                                        helpers)
                              (set! out (cons hit out))))))))
            (loop (cdr ts) (+ n 1)))))
    (reverse out)))

;;; The forward citations, computed at most ONCE per lane call and only when a
;;; triangle decomposition was actually found -- it is a whole lane's work and
;;; what-now is already O(candidates x context) (see [[reference_whatnow_nontermination]]).
(define (ineq-supply--fwd-thunk goal asms)
  (let ((cache 'unset))
    (lambda ()
      (if (eq? cache 'unset)
          (set! cache (let ((r (vnb-guard
                                (lambda () (what-now--forward-citations goal asms)))))
                        (if (or (vnb-error? r) (vnb-warning? r) (not (list? r)))
                            '() r))))
      cache)))

;;; -----------------------------------------------------------------------
;;; The lane.

;;; Is the goal one the oracle could finish -- an order or equality atom?
(define (ineq-supply--goal-shape? g)
  (and (pair? g) (memq (car g) '(<= < = >= >)) (= (length g) 3)))

;;; The move SEQUENCE: bridges, then certificates, then bounds, then `ineq' over
;;; every premise.  Order matters -- the bridge must precede the citations it
;;; unlocks, and the typing must precede the oracle call that needs it.
(define (ineq-supply--moves goal asms)
  (let* ((bridges (ineq-supply--bridges asms))
         (atoms   (ineq-supply--atoms goal asms))
         (fwd     (ineq-supply--fwd-thunk goal asms))
         (cites   '()))
    (for-each
     (lambda (p)
       (let* ((e    (car p))
              (t    (cdr p))
              (args ((cadr e) t))
              (cert (caddr e))
              (bnds (cadddr e)))
         (let ((c (ineq-supply--cite cert args)))
           (if c (set! cites (cons c cites))))
         (for-each (lambda (b)
                     (let ((c (ineq-supply--cite b args)))
                       (if c (set! cites (cons c cites)))))
                   bnds)
         ;; THE ABS TRIANGLE.  Unlike the metric one it needs NO third point and
         ;; makes no choice at all: |u + v| <= |u| + |v| decomposes the term
         ;; itself, so where the metric case searches the context for an
         ;; intermediate point, here the intermediate term IS the sum's own
         ;; summands.  Without this the lane offered `rr-le-abs',
         ;; `rr-neg-abs-le' and `rr-abs-nonneg' at abs(S + f(k)) -- all true,
         ;; none of them relating the abs of a sum to the sum of the abs -- and
         ;; then honestly reported that the oracle does not close.  Subadditivity
         ;; was the one fact it was missing and the only one it could not reach
         ;; from a bound on the whole term.
         (when (and (eq? (car e) 'abs)
                    (pair? (car args))
                    (eq? (car (car args)) '+)
                    (= (length (car args)) 3))
           (let* ((u   (cadr (car args)))
                  (v   (caddr (car args)))
                  (tri (ineq-supply--cite 'rr-abs-triangle-c (list u v))))
             (when tri
               ;; typings BEFORE the citation they guard, or `fact' lands the
               ;; implication and the driver sails on
               (let ((tu (ineq-supply--rr-typing-cite u asms (fwd)))
                     (tv (ineq-supply--rr-typing-cite v asms (fwd))))
                 (if tu (set! cites (cons tu cites)))
                 (if tv (set! cites (cons tv cites))))
               (set! cites (cons tri cites))
               ;; the two NEW abs atoms need certificates of their own, or
               ;; ineq-atom-rr-ok? refuses the premise it was just handed
               (for-each (lambda (w)
                           (let ((c (ineq-supply--cite 'rr-abs-closed (list w))))
                             (if c (set! cites (cons c cites)))))
                         (list u v)))))
         ;; THE METRIC TRIANGLE: one instance per intermediate point the context types.
         (when (eq? (car e) 'dist)
           (let* ((s (car args)) (x (cadr args)) (y (caddr args)))
             (for-each
              (lambda (z)
                (unless (or (equal? z x) (equal? z y))
                  (let ((c (ineq-supply--cite 'metric-triangle (list s x z y))))
                    (if c (set! cites (cons c cites))))
                  ;; and the two legs need typing too, or the oracle refuses
                  (for-each (lambda (pr)
                              (let ((c (ineq-supply--cite 'metric-dist-real
                                                          (list s (car pr) (cdr pr)))))
                                (if c (set! cites (cons c cites)))))
                            (list (cons x z) (cons z y)))))
              (ineq-supply--points s asms))))))
     atoms)
    ;; DEDUPE.  Three intermediate points ask for the same leg typing, and a
    ;; citation landing a formula already in context is a no-op that pads the
    ;; list and pushes the move that matters off the bottom.
    (append bridges
            ;; certificates FIRST: a premise the oracle drops for want of a
            ;; typing is a premise the bounds below cannot compensate for
            (let loop ((cs (ineq-supply--certify goal asms fwd)) (seen '()) (out '()))
              (cond ((null? cs) (reverse out))
                    ((member (car cs) seen) (loop (cdr cs) seen out))
                    (else (loop (cdr cs) (cons (car cs) seen)
                                (cons (car cs) out)))))
            (let loop ((cs (reverse cites)) (seen '()) (out '()))
              (cond ((null? cs) (reverse out))
                    ((member (car cs) seen) (loop (cdr cs) seen out))
                    (else (loop (cdr cs) (cons (car cs) seen)
                                (cons (car cs) out))))))))

;;; A move as `apply-recorded-cmd!' takes it.  The lane RETURNS and PRINTS the
;;; quoted form -- `(fact 'rr-max-closed 'a 'b)', which is what a reader pastes
;;; and what the panel's [do this] sends -- but a RECORDED command carries its
;;; arguments already evaluated (`(fact rr-max-closed a b)', interactive.scm).
;;; Handing the quoted form to the executor passes the LIST `(quote
;;; rr-max-closed)' where a symbol was wanted, so every citation silently fails
;;; and the probe reports "does not close" on a goal that closes by hand.
(define (ineq-supply--unquote a)
  (if (and (pair? a) (eq? (car a) 'quote)) (cadr a) a))

;;; ...and the shapes are NOT uniform.  `apply-recorded-cmd!' dispatches `fact'
;;; as `(cmd-fact *ps* (car args) (cadr args))' -- the theorem name and then the
;;; term list as ONE argument (interactive.scm:4321).  So the recorded form of
;;; `(fact 'rr-max-closed 'a 'b)' is `(fact rr-max-closed (a b))', not
;;; `(fact rr-max-closed a b)'.  Spread flat, `cmd-fact' gets `a' where a LIST
;;; of terms was wanted, instantiates nothing, and lands the raw universal --
;;; which is not an error, so the probe reported "does not close" on a goal that
;;; closes by hand, with three true-but-uninstantiated theorems in the context.
(define (ineq-supply--exec m)
  (let ((head (car m)) (args (map ineq-supply--unquote (cdr m))))
    (case head
      ((fact) (list 'fact (car args) (cdr args)))
      (else   (cons head args)))))

;;; Run the sequence on a scratch clone and report what `ineq' then does.
;;; Returns 'CLOSED, #f, or 'no-oracle when the run itself failed.
(define (ineq-supply--probe moves)
  (let ((scratch (vnb--scratch-state)))
    (and scratch
         (vnb--probing
          scratch
          (lambda ()
            (vnb-guard
             (lambda ()
               (for-each (lambda (m)
                           (let ((e (ineq-supply--exec m)))
                             (apply-recorded-cmd! (car e) (cdr e))))
                         moves)
               (let ((n (length (sequent-node-assumptions (proof-state-focus *ps*)))))
                 (apply-recorded-cmd!
                  'ineq (let lp ((i n) (a '())) (if (= i 0) a (lp (- i 1) (cons i a)))))
                 (and (proof-done? *ps*) 'CLOSED))))))
         )))

;;; `vnb-guard' returns a <vnb-error> OBJECT rather than raising, and it is
;;; TRUTHY -- so `(or (vnb--probing ...) 0)' hands the error on as though it
;;; were the answer, and the first arithmetic on it dies with "the object
;;; #[vnb-error 14] ... is not the correct type" from inside the panel.  Both
;;; readers below therefore test the TYPE of what came back, not its truth.
(define (ineq-supply--ok result pred default)
  (if (pred result) result default))

;;; How many premises `ineq' should be told about, after the sequence has run.
(define (ineq-supply--final-count moves)
  (let ((scratch (vnb--scratch-state)))
    (ineq-supply--ok
     (and scratch
          (vnb--probing
           scratch
           (lambda ()
             (vnb-guard
              (lambda ()
                (for-each (lambda (m)
                            (let ((e (ineq-supply--exec m)))
                              (apply-recorded-cmd! (car e) (cdr e))))
                          moves)
                (length (sequent-node-assumptions (proof-state-focus *ps*))))))))
     (lambda (r) (and (integer? r) (> r 0)))
     0)))

(define (what-now--show-ineq-supply goal)
  (if (or (not *ps*) (proof-done? *ps*) (not (ineq-supply--goal-shape? goal)))
      '()
      (let* ((sqn  (proof-state-focus *ps*))
             (asms (map wff-formula (sequent-node-assumptions sqn)))
             (moves (ineq-supply--moves goal asms)))
        (if (null? moves)
            '()
            (let* ((n     (ineq-supply--final-count moves))
                   (idxs  (let lp ((i n) (a '())) (if (= i 0) a (lp (- i 1) (cons i a)))))
                   (final (if (pair? idxs) (cons 'ineq idxs) '(ineq)))
                   (all   (append moves (list final)))
                   (closed (ineq-supply--ok (ineq-supply--probe moves)
                                            (lambda (r) (eq? r 'CLOSED)) #f)))
              (display ";; SUPPLY THE ORACLE -- `ineq' reads max(...), abs(...) and")
              (newline)
              (display ";;   (dist(s))(x,y) as opaque atoms.  These land the facts it")
              (newline)
              (display ";;   cannot know, and then decide the goal linearly")
              (if (eq? closed 'CLOSED)
                  (display "   => CLOSES the goal:")
                  (display " (probed: does NOT close):"))
              (newline)
              (for-each (lambda (m)
                          (display ";;   ") (vnb--write-form m) (newline))
                        all)
              (when (not (eq? closed 'CLOSED))
                (display ";;   -- run them anyway to see what the oracle is still missing;")
                (newline)
                (display ";;      an atom with no `in rr' certificate is the usual cause.")
                (newline))
              all)))))

;;; -----------------------------------------------------------------------
;;; The audit.  A table naming a lemma the library does not have would emit
;;; moves that cannot run, and a gate that passes everything reads exactly like
;;; a clean table -- so this reports both the entries that resolve and the ones
;;; that are wanted and absent.  Returns the data as well as printing it.
(define (ineq-supply-audit)
  (let ((ok '()) (missing '()))
    (for-each
     (lambda (e)
       (for-each
        (lambda (nm)
          (if (hash-table-ref/default *theorem-table* nm #f)
              (set! ok (cons nm ok))
              (set! missing (cons (cons (car e) nm) missing))))
        (cons (caddr e) (cadddr e))))
     *ineq-supply-table*)
    ;; metric-triangle is cited by the third-point branch, not by the table
    (if (hash-table-ref/default *theorem-table* 'metric-triangle #f)
        (set! ok (cons 'metric-triangle ok))
        (set! missing (cons (cons 'dist 'metric-triangle) missing)))
    (display ";; ineq-supply: ") (display (length ok))
    (display " table lemma(s) resolve; ") (display (length missing))
    (display " missing") (newline)
    (for-each (lambda (m) (display ";;   MISSING  ") (display (cdr m))
                          (display "   (") (display (car m)) (display ")") (newline))
              missing)
    (for-each (lambda (w)
                (display ";;   WANTED   ") (display (car w)) (display " -- ")
                (display (cadr w)) (newline))
              *ineq-supply-wanted*)
    (list (cons 'resolved (reverse ok)) (cons 'missing missing)
          (cons 'wanted *ineq-supply-wanted*))))

;;; -----------------------------------------------------------------------
;;; (supply) -- the lane, COMMITTED
;;;
;;; The lane above NAMES a sequence and probes it; this runs it.  It is the
;;; distillation of the user's own recipe for an inequality leaf, 2026-08-21:
;;;
;;;   "for inequalities apply whenever the Farkas-FUBA decision doesn't work
;;;    introduce intermediate terms using subadditivity of +"
;;;
;;; and of the induction step of `series-partial-sum-abs-le' (theorem-library/
;;; comparison-test-proof.scm), which is where the recipe was worked out by
;;; hand.  Everything from `(lam-b)' down in that proof is what this does.
;;;
;;; THREE THINGS IN ORDER, and the order is the content:
;;;
;;;   1. BETA.  While the goal applies a VNB-LAMBDA to an argument, reduce it.
;;;      Until that happens `(|f|)(k)' and `|f(k)|' are unrelated ATOMS to the
;;;      oracle and NO set of true inequalities about them can close the goal.
;;;      The moves in 2 are computed AFTER this, because they are computed from
;;;      the goal.
;;;   2. SUPPLY.  Certificates for the premises' atoms (to depth 2), the bounds
;;;      the table knows, and -- where an `abs' is applied to a sum -- the
;;;      TRIANGLE at that sum's own summands.  That is the intermediate term:
;;;      the decomposition is in the term, so nothing is searched for.
;;;   3. `ineq' over every premise.
;;;
;;; IT PROBES BEFORE IT COMMITS, and there is no undo: a run that got as far as
;;; the betas and then failed would have spent them, and a `lam-b' on an untyped
;;; argument owes a leaf that can be unprovable at a node whose context predates
;;; the variable.  So the whole sequence is rehearsed on `vnb--scratch-state'
;;; and committed only if it CLOSED there.  On a miss nothing has happened and
;;; the goal is untouched.
;;;
;;; IT ADDS NO TRUST.  Every move is `lam-b', `fact' and `ineq' -- what the hand
;;; proof used -- and each records itself, so the emitted script is the ordinary
;;; step-by-step proof and the `qed' bill is whatever those citations cost.

(define *supply-max-betas* 8)

;;; Reduce applied lambdas in the GOAL until there are none (or the cap).
;;; Returns how many fired.
(define (supply--betas!)
  (let loop ((n 0))
    (if (or (>= n *supply-max-betas*)
            (null? (what-now--redexes (vnb--focus-goal))))
        n
        (let ((r (vnb-guard (lambda () (apply-recorded-cmd! 'lam-b '())))))
          (if (vnb-error? r) n (loop (+ n 1)))))))

(define (vnb--focus-goal)
  (and *ps* (not (proof-done? *ps*))
       (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))

;;; The whole sequence, on whatever state is current.  Returns #t if the goal
;;; closed.  Used for the rehearsal and for the commit, so the two cannot drift.
(define (supply--attempt!)
  (supply--betas!)
  (let* ((goal (vnb--focus-goal))
         (asms (map wff-formula
                    (sequent-node-assumptions (proof-state-focus *ps*)))))
    (and goal
         (ineq-supply--goal-shape? goal)
         (begin
           (for-each (lambda (m)
                       (let ((e (ineq-supply--exec m)))
                         (apply-recorded-cmd! (car e) (cdr e))))
                     (ineq-supply--moves goal asms))
           (let ((n (length (sequent-node-assumptions (proof-state-focus *ps*)))))
             (apply-recorded-cmd!
              'ineq (let lp ((i n) (a '())) (if (= i 0) a (lp (- i 1) (cons i a))))))
           #t))))

(define (supply--probe)
  (let ((scratch (vnb--scratch-state)))
    (and scratch
         (eq? 'closed
              (vnb--probing scratch
                (lambda ()
                  (let ((r (vnb-guard (lambda () (supply--attempt!)))))
                    (if (and (not (vnb-error? r)) (proof-done? scratch))
                        'closed
                        'open))))))))

;;; NOT wrapped in `vnb--run!' -- same reason as `prop' and `contra': that
;;; wrapper takes the thunk's return value to BE the new proof state, and a
;;; composite ending in a `display' would set *ps* to #!unspecific.  The
;;; ordinary tactics this drives each record themselves.
(define (supply)
  (cond
   ((or (not *ps*) (proof-done? *ps*))
    (begin (display ";; supply: no open goal.") (newline)))
   ((not (supply--probe))
    ;; Say what it would have run.  The usual causes, in order of frequency:
    ;; an atom with no `in rr' certificate that no library citation lands, a
    ;; hypothesis the oracle needs that is still bound up inside a quantifier,
    ;; and a goal that is simply not a linear consequence of anything available.
    (let* ((goal (vnb--focus-goal))
           (asms (and goal (map wff-formula
                                (sequent-node-assumptions (proof-state-focus *ps*)))))
           (mv   (and goal (ineq-supply--goal-shape? goal)
                      (vnb-guard (lambda () (ineq-supply--moves goal asms))))))
      (display ";; supply: rehearsed on a throwaway copy -- does NOT close, nothing done.")
      (newline)
      (if (and (list? mv) (pair? mv))
          (begin
            (display ";;   the sequence it tried:") (newline)
            (for-each (lambda (m) (display ";;     ") (vnb--write-form m) (newline)) mv)
            (display ";;   Run them by hand and read `ineq''s complaint: an atom with no")
            (newline)
            (display ";;   `in rr' certificate is the usual cause.") (newline))
          (begin
            (display ";;   (no supply moves apply to this goal -- it is not an order or")
            (newline)
            (display ";;   equality atom, or its heads are none the table knows).") (newline)))))
   (else
    (supply--attempt!)
    (display ";; supply: beta, certificates, subadditivity, oracle -- goal closed.")
    (newline))))

