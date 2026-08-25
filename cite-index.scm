;;; cite-index.scm -- MEASURED citation affinity: P(theorem cited | head in goal).
;;;
;;; WHY THIS EXISTS.  Every ranking lane in `suggest.scm' orders candidates by a
;;; syntactic proxy for relevance -- fingerprint specificity, connective count,
;;; term size, "does the landed formula introduce a head the sequent does not
;;; mention".  Each proxy was written from ONE goal that provoked it, and each
;;; has a counterexample: specificity buries `class-extensionality', the
;;; vocabulary filter demotes a bridging lemma, and the ubiquitous-head list is
;;; a hand-maintained blacklist of thirteen symbols.  The harvester
;;; (`harvest.scm') put a number on the result: the move the author actually
;;; took is offered 23% of the time, and for `fact' -- the commonest citation
;;; tactic in the library, 3666 recorded steps -- 16%.
;;;
;;; The user's design for the fix: "there should be some kind of user-editable
;;; filter that excludes and includes stuff" (that is `*what-now-suppress*' /
;;; `*what-now-pin*'), and behind it, measured frequencies rather than more hand
;;; proxies.  This file is the measurement.
;;;
;;; THE DATA IS ALREADY IN MEMORY, and no replay is needed to read it.  Every
;;; `qed' files its command list in `*proof-script-table*' (interactive.scm:88),
;;; so a loaded library carries 464 scripts and 22,816 steps.  Pair each script
;;; with the STATEMENT of the theorem it proves, and one pass gives, exactly:
;;;
;;;     how many proofs whose statement mentions `dist' cite `metric-triangle'
;;;
;;; -- which is what the hand-written vocabulary filter is a crude guess at.
;;;
;;; THE UNIT IS THE SCRIPT, NOT THE STEP, and that is a deliberate approximation
;;; rather than a limitation we failed to notice.  The exact per-step quantity
;;; would be P(cited here | heads of THIS sequent), and computing it needs the
;;; sequent at each step, i.e. replay -- which 87% of the library's scripts do
;;; not survive (see [[project_copilot_harvester]]).  Measuring the 13% that do
;;; would sample the short simple proofs and call it the library.  The
;;; script-level quantity needs no replay at all, so it covers ALL 464, and the
;;; vocabulary of a proof is largely set by its statement.  What it CANNOT see:
;;; that a citation is characteristic of the SECOND half of a proof, after the
;;; unfolds have brought in vocabulary the statement never had.
;;;
;;; WHAT IT IS NOT.  Not a model, not learned, no parameters.  It is a hash
;;; table and a ratio, recomputed from the live tables, so it cannot drift from
;;; the library the way a written-out data file would.  It is built lazily on
;;; first use -- the library proofs load long after this file, so there is
;;; nothing to count at load time.
;;;
;;; SELECTION BIAS, stated once and inherited from the harvester: the library
;;; was written by someone who already knew which lemma to cite.  This measures
;;; what an expert cited, not what is objectively relevant, and a lemma nobody
;;; has yet had occasion to use scores as no-evidence rather than as bad.

;;; The tactics whose first argument NAMES a library fact.  `inst+' and `subst'
;;; are excluded on purpose: their first argument is an assumption index or a
;;; formula, not a name.
(define *cite--naming-tactics* '(fact bc bc* ta mac mac-h wbc))

;;; A recorded step is `(fact metric-self-zero m a)' -- the arguments are
;;; VALUES, already evaluated.  A hand-written or emitted one may carry the
;;; quote.  Accept both; anything else contributes no name.
(define (cite--step-name step)
  (and (pair? step)
       (memq (car step) *cite--naming-tactics*)
       (pair? (cdr step))
       (let ((a (cadr step)))
         (cond ((symbol? a) a)
               ((and (pair? a) (eq? (car a) 'quote) (pair? (cdr a))) (cadr a))
               (else #f)))))

;;; ---- the tables ------------------------------------------------------
;;; All four are filled in one pass by `cite--build!' and are #f until then.

(define *cite--nscripts*    #f)   ; scripts with a readable statement
(define *cite--head-count*  #f)   ; head -> # such scripts mentioning it
(define *cite--thm-count*   #f)   ; thm  -> # such scripts citing it
(define *cite--pair-count*  #f)   ; (head . thm) -> # scripts doing both
(define *cite--thm-heads*   #f)   ; thm  -> the heads of the goals citing it
(define *cite--co-count*    #f)   ; (u . t) -> # scripts citing BOTH, u /= t

(define (cite--bump! tbl key)
  (hash-table-set! tbl key (+ 1 (hash-table-ref/default tbl key 0))))

;;; TOPIC HOLD-OUT.  Leave-one-out removes one SCRIPT, which is enough to stop
;;; the index reading its own notes back, and NOT enough to answer the sharper
;;; objection: `border-is-diagonal' still has its sibling `border-*' scripts in
;;; the table, so the index may be memorising a neighbourhood rather than
;;; generalising.  The test that settles it is holding out a whole FAMILY --
;;; rebuild the index with every `cc-*' script removed, then measure on those
;;; scripts.  A gain that survives that is a gain on unseen subject matter,
;;; which is the only kind that would help on a proof in a new area.
;;;
;;; A predicate, not a list, so the caller says what a family is.  #f counts
;;; everything, which is the normal case.  Changing it requires
;;; `cite-index-reset!' -- the tables are built once.
(define *cite-script-filter* #f)

(define (cite--build!)
  (let ((nheads (make-strong-eqv-hash-table))
        (nthms  (make-strong-eqv-hash-table))
        (npair  (make-equal-hash-table))
        (theads (make-strong-eqv-hash-table))
        (nco    (make-equal-hash-table))
        (n 0))
    (for-each
     (lambda (name)
       (let ((stmt   (vnb-guard (lambda () (lookup-theorem name))))
             (script (hash-table-ref/default *proof-script-table* name '())))
         (when (and (pair? stmt) (pair? script)
                    (or (not *cite-script-filter*) (*cite-script-filter* name)))
           (set! n (+ n 1))
           (let ((heads (what-now--heads-of stmt))
                 ;; DISTINCT names: a proof citing `nn-in-rr' nine times is one
                 ;; piece of evidence that the lemma belongs to this vocabulary,
                 ;; not nine.  Without this the counts measure how often a
                 ;; driver repeats itself, which is a fact about the driver.
                 (cited (let loop ((s script) (acc '()))
                          (cond ((null? s) acc)
                                ((let ((c (cite--step-name (car s))))
                                   (and c (not (memq c acc)) c))
                                 => (lambda (c) (loop (cdr s) (cons c acc))))
                                (else (loop (cdr s) acc))))))
             (for-each (lambda (h) (cite--bump! nheads h)) heads)
             ;; CO-CITATION.  Every ordered pair of distinct names cited by the
             ;; same script.  This is the signal the statement-head table cannot
             ;; carry: what a proof reaches for AFTER the unfolds have brought in
             ;; vocabulary the statement never had.  Both directions are stored,
             ;; because the ratio below is not symmetric -- "proofs citing
             ;; `ball-membership' also cite `metric-triangle'" and its converse
             ;; are different claims with different denominators.
             (for-each
              (lambda (u)
                (for-each (lambda (t)
                            (if (not (eq? u t)) (cite--bump! nco (cons u t))))
                          cited))
              cited)
             (for-each
              (lambda (c)
                (cite--bump! nthms c)
                (hash-table-set! theads c
                  (let loop ((hs heads) (acc (hash-table-ref/default theads c '())))
                    (cond ((null? hs) acc)
                          ((memq (car hs) acc) (loop (cdr hs) acc))
                          (else (loop (cdr hs) (cons (car hs) acc))))))
                (for-each (lambda (h) (cite--bump! npair (cons h c))) heads))
              cited)))))
     (hash-table-keys *proof-script-table*))
    (set! *cite--nscripts* n)
    (set! *cite--head-count* nheads)
    (set! *cite--thm-count* nthms)
    (set! *cite--pair-count* npair)
    (set! *cite--thm-heads* theads)
    (set! *cite--co-count* nco)
    n))

(define (cite--ready!)
  (or *cite--nscripts* (cite--build!)))

;;; ---- leave-one-out ---------------------------------------------------
;;;
;;; THE CONTAMINATION, and the reason this section exists.  The index is built
;;; from the library's own 464 scripts, and the harvester measures the panel
;;; against those same scripts.  Scoring a citation in `matmul-assoc' with an
;;; index that counted `matmul-assoc' citing it is not a measurement -- it is
;;; the index reading its own notes back, and it would report an improvement
;;; whatever the ranking did.
;;;
;;; So a caller may name ONE script to leave out, and every count below is
;;; adjusted as if that script had never been read.  The adjustment is exact,
;;; not approximate, because every count is an INDICATOR over scripts: leaving
;;; out script S subtracts 1 from `n', from each head in S's statement, from
;;; each name S cites, and from each pair and co-pair S contributed.
;;;
;;; It costs nothing in normal use: `*cite-exclude-script*' is #f in a live
;;; proof, and every adjustment is then skipped.
(define *cite-exclude-script* #f)
(define *cite--parts-cache* #f)

;;; (HEADS . CITED) for script NAME, cached.  Same extraction as the build.
(define (cite--script-parts name)
  (if (not *cite--parts-cache*) (set! *cite--parts-cache* (make-strong-eqv-hash-table)))
  (let ((hit (hash-table-ref/default *cite--parts-cache* name 'miss)))
    (if (not (eq? hit 'miss))
        hit
        (let* ((stmt   (vnb-guard (lambda () (lookup-theorem name))))
               (script (hash-table-ref/default *proof-script-table* name '()))
               (v (and (pair? stmt) (pair? script)
                       (cons (what-now--heads-of stmt)
                             (let loop ((s script) (acc '()))
                               (cond ((null? s) acc)
                                     ((let ((c (cite--step-name (car s))))
                                        (and c (not (memq c acc)) c))
                                      => (lambda (c) (loop (cdr s) (cons c acc))))
                                     (else (loop (cdr s) acc))))))))
          (hash-table-set! *cite--parts-cache* name v)
          v))))

;;; The excluded script's parts, or #f -- computed once per call site.
(define (cite--excluded)
  (and *cite-exclude-script* (cite--script-parts *cite-exclude-script*)))

(define (cite--n)
  (- *cite--nscripts* (if (cite--excluded) 1 0)))

(define (cite--nhead h)
  (let ((x (cite--excluded)))
    (- (hash-table-ref/default *cite--head-count* h 0)
       (if (and x (memq h (car x))) 1 0))))

(define (cite--nthm t)
  (let ((x (cite--excluded)))
    (- (hash-table-ref/default *cite--thm-count* t 0)
       (if (and x (memq t (cdr x))) 1 0))))

(define (cite--npair h t)
  (let ((x (cite--excluded)))
    (- (hash-table-ref/default *cite--pair-count* (cons h t) 0)
       (if (and x (memq h (car x)) (memq t (cdr x))) 1 0))))

(define (cite--nco u t)
  (let ((x (cite--excluded)))
    (- (hash-table-ref/default *cite--co-count* (cons u t) 0)
       (if (and x (memq u (cdr x)) (memq t (cdr x))) 1 0))))

;;; Recompute from scratch.  Only needed after new proofs land in the same
;;; session -- which happens on every library load, and the lazy build already
;;; runs after that.
(define (cite-index-reset!)
  (set! *cite--nscripts* #f)
  (set! *cite--head-count* #f)
  (set! *cite--thm-count* #f)
  (set! *cite--pair-count* #f)
  (set! *cite--thm-heads* #f)
  (set! *cite--co-count* #f)
  (set! *cite--parts-cache* #f))

;;; ---- the ratio -------------------------------------------------------
;;;
;;; LIFT, not probability.  P(T | h) alone ranks the theorems everybody cites --
;;; `nn-in-rr' is cited in proofs about everything, so it wins every head.  The
;;; quantity that says "T BELONGS to the vocabulary of h" is
;;;
;;;     lift(h,T) = P(T cited | h in statement) / P(T cited)
;;;
;;; -- how much more often than usual.  1 is neutral, and a lemma nobody has
;;; cited yet has no evidence either way, which is 1 as well.  This is the
;;; standard pointwise ratio; nothing is estimated or fitted.

;;; Below this many co-occurrences the ratio is one proof's accident.  Two is
;;; the smallest number that can be a pattern; it is a floor, not a tuned knob.
(define *cite-support-floor* 2)

(define (cite-lift head thm)
  (cite--ready!)
  (let ((nh (cite--nhead head))
        (nt (cite--nthm thm))
        (np (cite--npair head thm)))
    (if (or (< np *cite-support-floor*) (= nh 0) (= nt 0))
        1
        (exact->inexact (/ (* np (cite--n)) (* nh nt))))))

;;; The evidence for THM against a set of sequent HEADS, best head first:
;;; ((head lift co-occurrences head-scripts) ...).  Data, not print -- the panel
;;; renders it and `cite-why' is only its display form.
(define (cite-evidence thm heads)
  (cite--ready!)
  (sort
   (filter (lambda (e) (> (cadr e) 1))
           (map (lambda (h)
                  (list h (cite-lift h thm)
                        (cite--npair h thm)
                        (cite--nhead h)))
                heads))
   (lambda (a b) (> (cadr a) (cadr b)))))

;;; The single score the ranking lanes use: the BEST lift over the sequent's
;;; heads, 1 when no head has evidence.  Max rather than sum or mean, because a
;;; lemma characteristic of ONE head in the sequent is exactly the lemma the
;;; sequent's subject matter calls for; averaging it against the sequent's other
;;; heads dilutes precisely the signal we came for.
(define (cite-score thm heads)
  (cite--ready!)
  (let loop ((hs heads) (best 1))
    (if (null? hs)
        best
        (let ((l (cite-lift (car hs) thm)))
          (loop (cdr hs) (if (> l best) l best))))))

;;; How often THM is cited at all, in scripts.  A lane wanting "has anyone ever
;;; used this" asks here rather than guessing from the name.
(define (cite-uses thm)
  (cite--ready!)
  (cite--nthm thm))

;;; ---- co-citation -----------------------------------------------------
;;;
;;; THE SECOND SIGNAL, and the one the panel can use DURING a proof.  The
;;; statement-head table above answers "what do proofs about `dist' cite", and
;;; it is thin wherever the head is rare -- `dist' occurs in 6 of 470 statements
;;; and `metric-triangle' is cited in none of them, because the metric facts are
;;; mostly asserted supports rather than proven scripts.  Co-citation answers a
;;; different question with a much denser table:
;;;
;;;     of the proofs that cited `ball-membership', how many went on to cite
;;;     `metric-triangle' -- against how often anything cites it at all?
;;;
;;; and the panel knows the left-hand side at any moment, because the steps
;;; taken so far are in `*proof-script*' (interactive.scm).  It needs no replay,
;;; no sequent, and no head extraction: it is a fact about which lemmas travel
;;; together, which is exactly what a reader wants named after their first
;;; citation lands.
;;;
;;; NOT SYMMETRIC.  P(T | U) and P(U | T) have different denominators: a lemma
;;; cited in three proofs and a lemma cited in forty co-occur in three, which is
;;; everything the first one does and nothing much about the second.

(define (cite-co-lift u thm)
  (cite--ready!)
  (let ((nu (cite--nthm u))
        (nt (cite--nthm thm))
        (nc (cite--nco u thm)))
    (if (or (< nc *cite-support-floor*) (= nu 0) (= nt 0))
        1
        (exact->inexact (/ (* nc (cite--n)) (* nu nt))))))

;;; Best co-lift of THM over the names CITED so far, 1 when there is no
;;; evidence.  Max for the same reason `cite-score' takes a max: one lemma that
;;; strongly predicts THM is the whole signal, and averaging it against the
;;; other citations in the proof dilutes it away.
(define (cite-co-score thm cited)
  (cite--ready!)
  (let loop ((us cited) (best 1))
    (if (null? us)
        best
        (let ((l (cite-co-lift (car us) thm)))
          (loop (cdr us) (if (> l best) l best))))))

;;; The names cited so far in the LIVE proof, most recent first, deduplicated.
;;; `*proof-script*' is the running command list `qed' eventually files.
(define (cite-cited-so-far)
  (let loop ((s (if (list? *proof-script*) *proof-script* '())) (acc '()))
    (cond ((null? s) (reverse acc))
          ((let ((c (cite--step-name (car s)))) (and c (not (memq c acc)) c))
           => (lambda (c) (loop (cdr s) (cons c acc))))
          (else (loop (cdr s) acc)))))

;;; What proofs citing U go on to cite, best lift first.  Returns the ranked
;;; alist (also printed).
(define (cite-next u #!optional n)
  (cite--ready!)
  (let* ((k (if (default-object? n) 12 n))
         (cands (filter (lambda (t)
                          (>= (hash-table-ref/default *cite--co-count* (cons u t) 0)
                              *cite-support-floor*))
                        (hash-table-keys *cite--thm-count*)))
         (ranked (sort (map (lambda (t) (cons t (cite-co-lift u t))) cands)
                       (lambda (a b) (> (cdr a) (cdr b))))))
    (display ";; after ") (display u)
    (display " -- cited in ") (display (cite-uses u))
    (display " of ") (display *cite--nscripts*) (display " scripts")
    (newline)
    (for-each (lambda (p)
                (display ";;   lift ") (display (/ (round (* 10 (cdr p))) 10.))
                (display "  ") (display (car p))
                (display "  (") (display (hash-table-ref/default
                                          *cite--co-count* (cons u (car p)) 0))
                (display " scripts together, ") (display (cite-uses (car p)))
                (display " overall)")
                (newline))
              (list-head ranked (min k (length ranked))))
    ranked))

;;; ---- reports ---------------------------------------------------------

(define (cite--pct n d) (if (= d 0) 0 (round (/ (* 100 n) d))))

;;; What vocabulary is THM at home in?  Returns the evidence list (also printed).
(define (cite-why thm)
  (cite--ready!)
  (let* ((heads (hash-table-ref/default *cite--thm-heads* thm '()))
         (ev    (cite-evidence thm heads)))
    (display ";; ") (display thm)
    (display " -- cited in ") (display (cite-uses thm))
    (display " of ") (display *cite--nscripts*) (display " scripts")
    (newline)
    (if (null? ev)
        (begin (display ";;   no head reaches the support floor of ")
               (display *cite-support-floor*)
               (display " -- no measured vocabulary") (newline))
        (for-each
         (lambda (e)
           (display ";;   ") (display (car e))
           (display "  lift ") (display (/ (round (* 10 (cadr e))) 10.))
           (display "  (") (display (caddr e))
           (display " of ") (display (cadddr e))
           (display " scripts mentioning it, vs ")
           (display (cite--pct (cite-uses thm) *cite--nscripts*))
           (display "% overall)")
           (newline))
         (list-head ev (min 6 (length ev)))))
    ev))

;;; The theorems most characteristic of HEAD, best lift first.  This is the
;;; answer to "what do proofs about `dist' actually cite", which nothing in the
;;; tree could say before.
(define (cite-for head #!optional n)
  (cite--ready!)
  (let* ((k     (if (default-object? n) 12 n))
         (cands (filter (lambda (t)
                          (>= (hash-table-ref/default *cite--pair-count* (cons head t) 0)
                              *cite-support-floor*))
                        (hash-table-keys *cite--thm-count*)))
         (ranked (sort (map (lambda (t) (cons t (cite-lift head t))) cands)
                       (lambda (a b) (> (cdr a) (cdr b))))))
    (display ";; ") (display head)
    (display " -- in ") (display (hash-table-ref/default *cite--head-count* head 0))
    (display " of ") (display *cite--nscripts*) (display " proof statements")
    (newline)
    (for-each (lambda (p)
                (display ";;   lift ") (display (/ (round (* 10 (cdr p))) 10.))
                (display "  ") (display (car p))
                (display "  (") (display (hash-table-ref/default
                                          *cite--pair-count* (cons head (car p)) 0))
                (display " scripts)")
                (newline))
              (list-head ranked (min k (length ranked))))
    ranked))

;;; The shape of the table itself -- run this before believing anything above.
(define (cite-index-report)
  (cite--ready!)
  (display ";; ==== CITATION INDEX ====") (newline)
  (display ";; scripts with a statement : ") (display *cite--nscripts*) (newline)
  (display ";; distinct heads           : ")
  (display (length (hash-table-keys *cite--head-count*))) (newline)
  (display ";; distinct cited theorems  : ")
  (display (length (hash-table-keys *cite--thm-count*))) (newline)
  (display ";; co-citation pairs        : ")
  (display (length (hash-table-keys *cite--co-count*))) (newline)
  (display ";; (head, theorem) pairs    : ")
  (display (length (hash-table-keys *cite--pair-count*))) (newline)
  (display ";; pairs at/above the floor : ")
  (display (length (filter (lambda (v) (>= v *cite-support-floor*))
                           (hash-table-values *cite--pair-count*))))
  (newline)
  (display ";; most-cited theorems      : ")
  (display (list-head (sort (hash-table->alist *cite--thm-count*)
                            (lambda (a b) (> (cdr a) (cdr b))))
                      (min 8 (length (hash-table-keys *cite--thm-count*)))))
  (newline)
  (list (cons 'scripts *cite--nscripts*)
        (cons 'heads (length (hash-table-keys *cite--head-count*)))
        (cons 'theorems (length (hash-table-keys *cite--thm-count*)))
        (cons 'pairs (length (hash-table-keys *cite--pair-count*)))))
