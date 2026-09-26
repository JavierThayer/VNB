;;; proof-reader.scm -- the HUMAN-READABLE proof sketch ("reader mode"), the
;;; companion of proof-tex.scm (which dumps every tactic as a numbered sequent).
;;;
;;; It collapses the mechanical bookkeeping -- runs of `di' / `ai' (the
;;; decompose-goal / unpack-hypothesis kernel rules) -- into a single
;;; "Assume ...; Show ..." opening, and renders only the CONTENT-bearing steps
;;; (ew witnesses, mac unfolds, fact / lemma citations, oracle / assumption
;;; closes) as bullets.  Each bullet carries the ORIGINAL step-number range in
;;; its margin, so the sketch stays auditable against the full machine proof.
;;;
;;; FAITHFUL, not fluent.  It cites lemma NAMES and shows the actual witness
;;; term / unfolded goal / instantiated hypothesis the machine produced; it does
;;; NOT paraphrase what a lemma "means" (that would need per-lemma NL templates,
;;; a later layer).  What you read is exactly what the checker did, minus the
;;; di/ai noise.
;;;
;;; Entry points mirror proof-tex:
;;;   (proof-reader name)            -> the LaTeX document as a string
;;;   (write-proof-reader name path) -> writes path, returns path
;;;   (view-proof-reader-pdf name)   -> write + pdflatex + open (best-effort)
;;;
;;; Loaded after proof-tex.scm (reuses its preamble, expr->tex sequent/align
;;; helpers, replay machinery, *proof-live-trace*, *session-log*).

;;; --- capture: per-step records that KEEP the raw entry -----------------
;;; proof-tex--steps stores a truncated LABEL string ("(ew ...)"); the reader
;;; needs the raw (tactic . args) so it can show the actual witness term.  A
;;; record is (entry goal asms new-ids); the first record's entry is (sp).
(define (proof-reader--records name)
  (or (proof-reader--records-from-live name)
      (proof-reader--records-by-replay name)))

(define (proof-reader--records-from-live name)
  (let ((trace (hash-table-ref/default *proof-live-trace* name #f)))
    (and (pair? trace)
         (let ((prev '()) (out '()))
           (for-each
            (lambda (rec)
              (let* ((entry (car rec)) (g (cadr rec)) (a (caddr rec)) (open (list-ref rec 4))
                     (added (sort (filter (lambda (k)(not (memv k prev))) open) <)))
                (set! prev open)
                (set! out (cons (list entry g a added) out))))
            trace)
           (reverse out)))))

(define (proof-reader--records-by-replay name)
  (let ((rec (proof-tex--record name)))
    (if (not rec)
        (error "proof-reader: no proof named this in *session-log* (proofs run this session)" name)
        (let ((goal (cadr rec)) (script (caddr rec)) (acc '()) (prev '()))
          (define (new-ids)
            (let ((now (proof-tex--open-ids)))
              (let ((added (filter (lambda (k)(not (memv k prev))) now)))
                (set! prev now) (sort added <))))
          (quietly
           (lambda ()
             (fluid-let ((*fresh-counter*
                          (hash-table-ref/default *proof-start-counter* name *fresh-counter*)))
               (sp (make-wff goal))
               (set! acc (list (list (list 'sp) (proof-tex--focus-goal)
                                     (proof-tex--focus-asms) (new-ids))))
               (fluid-let ((*replaying?* #t))
                 (for-each
                  (lambda (entry)
                    (apply-recorded-cmd! (car entry) (cdr entry))
                    (set! acc (cons (list entry (proof-tex--focus-goal)
                                          (proof-tex--focus-asms) (new-ids)) acc)))
                  script)))))
          (reverse acc)))))

;;; --- classification ----------------------------------------------------
;; `wk' / `keep' only shrink the context: bookkeeping, folded like di / ai
;; into the step they prepare (a run of them never gets a bullet of its own).
(define *proof-reader-structural* '(di ai wk keep))         ; folded into prose
(define *proof-reader-closer*     '(ass rfl qrfl crs rs simp ineq sos arith))
;; fact-family tactics that merely DISCHARGE side-conditions (introduce a
;; hypothesis).  When everything such a step introduces is a typing/membership
;; predicate, it is BOOKKEEPING -- the in-carrier plumbing an oracle needs, not
;; something a human reader wants a bullet for.  A run of them collapses to one line.
(define *proof-reader-fact-tacs* '(fact ta inst inst+ pi-detach! detach))
(define (proof-reader--tac r) (car (car r)))
(define (proof-reader--structural? r) (memq (proof-reader--tac r) *proof-reader-structural*))
(define (proof-reader--closer? r)     (memq (proof-reader--tac r) *proof-reader-closer*))
(define (proof-reader--content? r)
  (and (not (eq? (proof-reader--tac r) 'sp)) (not (proof-reader--structural? r))))
;; a wff is TYPING if it is (or curries/quantifies down to) a membership `IN'.
(define (proof-reader--typing-wff? w)
  (and (pair? w)
       (case (car w)
         ((IN) #t)
         ((FORALL FORSOME) (proof-reader--typing-wff? (caddr w)))
         ((IMPLIES) (proof-reader--typing-wff? (caddr w)))
         (else #f))))

;;; --- grouping ----------------------------------------------------------
;; Attach a 0-based step index to each record: (idx entry goal asms new-ids).
(define (proof-reader--index records)
  (let loop ((rs records) (i 0) (out '()))
    (if (null? rs) (reverse out)
        (loop (cdr rs) (+ i 1) (cons (cons i (car rs)) out)))))
(define (ir-idx r)(car r))
(define (ir-rec r)(cdr r))

;;; --- footprint collapse: recognise a composite tactic's PRIMITIVE trace and
;;; fold it back to its intent.  The excluded-middle helper (cc-em / bm-em /
;;; cc-cases) always emits the SAME deterministic 13-step block; it introduces
;;; NO new inference rule (every step is a kernel cut/pbc/oi/ai/ass), it is pure
;;; case analysis on a formula P.  We match that block and replace it with a
;;; single synthetic record (CASE-SPLIT P hi) so the sketch reads "split on P"
;;; instead of a cut/pbc/oi soup.  The margin still spans the original step range.
(define (proof-reader--orneg f)          ; (or P (not P)) -> P, else #f
  (and (pair? f) (= (length f) 3) (memq (car f) '(or OR))
       (let ((a (cadr f)) (b (caddr f)))
         (and (pair? b) (memq (car b) '(not NOT)) (equal? (cadr b) a) a))))
(define (proof-reader--em-match irecs)   ; irecs from a candidate anchor -> P or #f
  (and (>= (length irecs) 13)
       (let ((es (map (lambda (ir) (car (ir-rec ir))) (list-head irecs 13))))
         (let* ((e0 (car es))
                (orn (and (pair? e0) (eq? (car e0) 'cut) (cadr e0)))
                (P   (and orn (proof-reader--orneg orn))))
           (and P
                (let ((notP (caddr orn)))            ; (not P), with the recorded `not'
                  (and (equal? (list-ref es 1)  '(pbc))
                       (equal? (list-ref es 2)  (list 'cut notP))
                       (equal? (list-ref es 3)  '(di))
                       (equal? (list-ref es 4)  (list 'cut orn))
                       (equal? (list-ref es 5)  '(oi-l))
                       (equal? (list-ref es 6)  '(ass))
                       (equal? (list-ref es 7)  (list 'ai (list (car notP) orn)))
                       (equal? (list-ref es 8)  (list 'cut orn))
                       (equal? (list-ref es 9)  '(oi-r))
                       (equal? (list-ref es 10) '(ass))
                       (equal? (list-ref es 11) (list 'ai (list (car notP) orn)))
                       (equal? (list-ref es 12) (list 'ai orn))
                       P)))))))
(define (proof-reader--collapse-em irecs)
  (let loop ((rs irecs) (out '()))
    (if (null? rs) (reverse out)
        (let ((P (proof-reader--em-match rs)))
          (if P
              (let* ((blk (list-head rs 13))
                     (fst (car blk)) (lst (list-ref blk 12)) (rec (ir-rec lst))
                     (nids (apply append (map (lambda (ir) (list-ref (ir-rec ir) 3)) blk)))
                     (syn (list (list 'CASE-SPLIT P (ir-idx lst)) (cadr rec) (caddr rec) nids)))
                (loop (list-tail rs 13) (cons (cons (ir-idx fst) syn) out)))
              (loop (cdr rs) (cons (car rs) out)))))))

(define (proof-reader--all? p lst)
  (or (null? lst) (and (p (car lst)) (proof-reader--all? p (cdr lst)))))

;; new-asms of each record = its asms minus the immediately-preceding record's
;; asms (assumptions accumulate, so this is what the step introduced).  Returns a
;; hash idx -> (wff ...).  Used to tell a typing/bookkeeping step from a real one.
(define (proof-reader--annotate irecs)
  (let ((ht (make-equal-hash-table)) (prev '()))
    (for-each
     (lambda (ir)
       (let ((asms (caddr (ir-rec ir))))
         (hash-table-set! ht (ir-idx ir)
                          (filter (lambda (a) (not (member a prev))) asms))
         (set! prev asms)))
     irecs)
    ht))

;; kind of a group's MAIN record, given the new-asms hash.
(define (proof-reader--kind main-ir ht)
  (let* ((r (ir-rec main-ir)) (tac (proof-reader--tac r)))
    (cond ((proof-reader--closer? r) 'closer)
          ((and (memq tac *proof-reader-fact-tacs*)
                (let ((na (hash-table-ref/default ht (ir-idx main-ir) '())))
                  (and (pair? na) (proof-reader--all? proof-reader--typing-wff? na))))
           'typing)
          (else 'content))))

;; Split into (setup-irecs . body-groups).  setup = the opening run [sp di* ai*]
;; up to (not incl.) the first content step.  Each body group = a maximal
;; [structural* content] run (structural leads into the content step it sets up).
;; Then a group whose content is a pure CLOSER is merged into the preceding
;; group (so "by lemma L" and "which holds" become one bullet).
(define (proof-reader--group irecs)
  (let* ((ht (proof-reader--annotate irecs))
         (first-content
          (let loop ((rs irecs))
            (cond ((null? rs) #f)
                  ((proof-reader--content? (ir-rec (car rs))) (car rs))
                  (else (loop (cdr rs))))))
         (c0 (if first-content (ir-idx first-content) (length irecs)))
         (setup (filter (lambda (ir) (< (ir-idx ir) c0)) irecs))
         (body  (filter (lambda (ir) (>= (ir-idx ir) c0)) irecs)))
    ;; raw groups: accumulate structural, flush on each content record
    (let ((groups '()) (buf '()))
      (for-each
       (lambda (ir)
         (set! buf (cons ir buf))
         (when (proof-reader--content? (ir-rec ir))
           (set! groups (cons (reverse buf) groups))
           (set! buf '())))
       body)
      (when (pair? buf) (set! groups (cons (reverse buf) groups)))  ; trailing structural
      (define (grp-kind g)
        (let ((p (proof-reader--group-primary g)))
          (and p (proof-reader--kind p ht))))
      (let ((glist (reverse groups)))
        ;; merge a pure-closer group into its predecessor
        (let ((merged '()))
          (for-each
           (lambda (g)
             (let ((main (proof-reader--group-main g)))
               (if (and main (proof-reader--closer? main) (pair? merged))
                   (set-car! merged (append (car merged) g))   ; fold into previous
                   (set! merged (cons g merged)))))
           glist)
          ;; merge a RUN of typing/bookkeeping groups into one collapsed line
          (let ((tmerged '()))
            (for-each
             (lambda (g)
               (if (and (eq? (grp-kind g) 'typing) (pair? tmerged)
                        (eq? (grp-kind (car tmerged)) 'typing))
                   (set-car! tmerged (append (car tmerged) g))
                   (set! tmerged (cons g tmerged))))
             (reverse merged))
            ;; then merge a RUN of inst/inst+ content groups (the IH specialization:
            ;; peel r, x, y, ... off one hypothesis) into one collapsed line.
            (define (inst-grp? g)
              (let ((m (proof-reader--group-main g)))
                (and m (memq (proof-reader--tac m) '(inst inst+))
                     (not (eq? (grp-kind g) 'typing)))))
            (let ((imerged '()))
              (for-each
               (lambda (g)
                 (if (and (inst-grp? g) (pair? imerged) (inst-grp? (car imerged)))
                     (set-car! imerged (append (car imerged) g))
                     (set! imerged (cons g imerged))))
               (reverse tmerged))
              (cons setup (reverse imerged)))))))))

;; the CONTENT record of a group = its last content record (there is exactly one
;; per raw group; after a closer-merge there may be two -- main + the closer).
(define (proof-reader--group-main g)
  (let loop ((rs (reverse g)))
    (cond ((null? rs) #f)
          ((proof-reader--content? (ir-rec (car rs))) (ir-rec (car rs)))
          (else (loop (cdr rs))))))

;; the PRIMARY content of a possibly-merged group (first content record) and the
;; trailing closer (if the group was merged with one).
(define (proof-reader--group-primary g)
  (let loop ((rs g))
    (cond ((null? rs) #f)
          ((proof-reader--content? (ir-rec (car rs))) (car rs))
          (else (loop (cdr rs))))))
(define (proof-reader--group-closer g primary)
  ;; a content record AFTER the primary that is a closer
  (let loop ((rs g) (seen-primary #f))
    (cond ((null? rs) #f)
          ((eq? (car rs) primary) (loop (cdr rs) #t))
          ((and seen-primary (proof-reader--content? (ir-rec (car rs)))
                (proof-reader--closer? (ir-rec (car rs)))) (ir-rec (car rs)))
          (else (loop (cdr rs) seen-primary)))))

(define (proof-reader--range g)
  ;; a CASE-SPLIT synthetic carries its collapsed block's hi index in (caddr entry)
  (let* ((idxs (map ir-idx g))
         (his (let lp ((rs g) (acc '()))
                (if (null? rs) acc
                    (let ((e (car (ir-rec (car rs)))))
                      (lp (cdr rs) (if (and (eq? (car e) 'CASE-SPLIT) (pair? (cddr e)))
                                       (cons (caddr e) acc) acc))))))
         (lo (apply min idxs)) (hi (apply max (append idxs his))))
    (if (= lo hi) (number->string lo)
        (string-append (number->string lo) "--" (number->string hi)))))

;;; --- prose glosses -----------------------------------------------------
(define (proof-reader--arg-tex a)
  (cond ((string? a) (string-append "\\texttt{" (proof-tex--escape-tt a) "}"))
        ((or (pair? a) (symbol? a) (number? a)) (expr->tex a))
        (else (proof-tex--escape-tt (call-with-output-string (lambda (p)(write a p)))))))
;; a lemma CITATION: a symbol -> its name as an \operatorname; a raw wff
;; (instantiating an unnamed hypothesis) -> the phrase "the hypothesis".
(define (proof-reader--cite a)
  (if (symbol? a)
      (string-append "$" (tex--operatorname (symbol->string a)) "$")
      "the hypothesis"))

;; a formula shown as its own displayed equation (breaks/wraps via
;; expr->tex-display so wide prefix terms fit the page instead of overflowing).
(define (proof-reader--display e)
  (string-append "\n\\begin{equation*}\n" (expr->tex-display e) "\n\\end{equation*}\n"))
;; assumptions in R2 not (alpha-)in R1  -- the hypotheses a step introduced.
(define (proof-reader--new-asms before after)
  (filter (lambda (a) (not (member a before))) after))

;; prose for bare tactics that take no cited lemma / witness (the `else' fallback).
;; ni/subst/lam-b are handled explicitly above (they read the goal / induction var).
(define *proof-reader-tac-prose*
  '((cut       . "By a cut on the auxiliary claim.")
    (contra    . "By contradiction.")
    (weaken    . "Weakening the context.")
    (grind     . "By exhaustive simplification.")
    (unfold    . "Unfold the definition.")
    (gi        . "Generalize.")))

;; The goal as it stood immediately before the group's PRIMARY record.
;;
;; NOT the group's entry goal.  A group routinely opens with structural di/ai
;; steps that rewrite the goal -- `di di di ew' peels FORALLs down to the FORSOME
;; the `ew' then witnesses -- and the ew / ni glosses read their quantified
;; variable off that goal.  Passing the group's entry goal made `ew' see a FORALL
;; where it wanted a FORSOME, fail to find the bound variable, and fall back to
;; printing the literal string "w": a witness named after a variable that occurs
;; nowhere in the proof.  (The line 301 comment always claimed this contract; the
;; call site did not honour it.)
(define (proof-reader--goal-before g primary pre-goal)
  (let loop ((rs g) (prev #f))
    (cond ((null? rs) pre-goal)
          ((eq? (car rs) primary) (if prev (cadr (ir-rec prev)) pre-goal))
          (else (loop (cdr rs) (car rs))))))

;; gloss for the PRIMARY content record; pre-goal = goal of the record before it
;; (see proof-reader--goal-before), pre-asms = assumptions before the group.
;; Returns a LaTeX fragment -- prose, with any formula shown as a displayed
;; equation (proof-reader--display) below the text.
(define (proof-reader--gloss main pre-goal pre-asms)
  (let* ((entry (car main)) (tac (car entry)) (args (cdr entry))
         (goal (cadr main)) (asms (caddr main))
         (news (proof-reader--new-asms pre-asms asms)))
    (case tac
      ((ew)
       (let ((v (and (pair? pre-goal) (eq? (car pre-goal) 'FORSOME) (cadr pre-goal)))
             (w (and (pair? args) (car args))))
         ;; No invented variable name: if the existential's bound variable cannot
         ;; be recovered, say so, rather than naming the witness after a `w' the
         ;; reader will hunt for in vain.
         (if v
             (string-append "Take $" (expr->tex v) " :=$"
                            (if (and w (pair? w)) (proof-reader--display w)
                                (string-append " $" (if w (proof-reader--arg-tex w) "\\cdot") "$.")))
             (string-append "Supply the witness"
                            (if (and w (pair? w)) (proof-reader--display w)
                                (string-append " $" (if w (proof-reader--arg-tex w) "\\cdot") "$."))))))
      ((mac macm)
       (string-append "By " (proof-reader--cite (and (pair? args)(car args)))
                      (if goal (string-append ", reduce to" (proof-reader--display goal)) ".")))
      ((fact ta)
       (string-append "By " (proof-reader--cite (and (pair? args)(car args)))
                      (cond ((pair? news)      ; show only the CONCLUSION it detaches
                             (string-append ":" (proof-reader--display (car news))))
                            (goal (string-append ", reduce to" (proof-reader--display goal)))
                            (else "."))))
      ((inst inst+)
       (string-append "Instantiate " (proof-reader--cite (and (pair? args)(car args)))
                      (if (pair? news) (string-append ":" (proof-reader--display (car news))) ".")))
      ((bc bc*)
       (string-append "Backchain through " (proof-reader--cite (and (pair? args)(car args)))
                      (if goal (string-append "; it remains to show" (proof-reader--display goal)) ".")))
      ((ni)
       (let ((v (and (pair? pre-goal) (eq? (car pre-goal) 'FORALL) (cadr pre-goal))))
         (string-append "By induction"
                        (if v (string-append " on $" (expr->tex v) "$") "") ".")))
      ((CASE-SPLIT)
       (string-append "\\emph{Split into cases} on whether"
                      (proof-reader--display (car args))))
      ((cut)
       (if (pair? args)
           (string-append "Introduce the auxiliary claim" (proof-reader--display (car args)))
           "By a cut on the auxiliary claim."))
      ((subst) "Substitute the established equation.")
      ((lam-b) "$\\beta$-reduce the applied $\\lambda$.")
      ((ass) "\\emph{Holds by assumption.}")
      ((rfl qrfl) "\\emph{Holds by reflexivity.}")
      ((crs rs simp) "\\emph{Closes by commutative-ring simplification.}")
      ((ineq) "\\emph{Closes by linear arithmetic} (the Farkas certificate is on the full page).")
      ((sos) "\\emph{Closes by sum-of-squares} (the squares and weights are on the full page).")
      ((arith) "\\emph{Closes by ground arithmetic.}")
      (else
       (let ((p (assq tac *proof-reader-tac-prose*)))
         (if p (cdr p)
             (string-append "By " (proof-reader--cite tac) ".")))))))

;;; --- assembly ----------------------------------------------------------
;; a collapsed line for a RUN of typing/bookkeeping steps: just the atoms they
;; established (each fact's detached conclusion), no per-step bullets.
(define (proof-reader--typing-row g ht)
  (let ((atoms '()))
    (for-each
     (lambda (ir)
       (when (memq (proof-reader--tac (ir-rec ir)) *proof-reader-fact-tacs*)
         (let ((na (hash-table-ref/default ht (ir-idx ir) '())))
           (when (pair? na) (set! atoms (cons (car na) atoms))))))
     g)
    (string-append
     "\\emph{Establish in-carrier / typing side-conditions:}"
     (let ((atoms (reverse atoms)))
       (if (pair? atoms)
           ;; displayed, one atom per row -- never overflows and can't break
           ;; mid-atom the way an inline list does.
           (string-append
            "\n\\begin{equation*}\n\\begin{array}{@{}l@{}}\n"
            (proof-tex--join (map expr->tex-display atoms) " \\\\\n")
            "\n\\end{array}\n\\end{equation*}\n")
           "")))))

;; a collapsed line for a RUN of inst/inst+ steps that peel nested quantifiers off
;; one hypothesis (the classic induction-hypothesis specialization: instantiate at
;; r, x, y, ...).  The intermediate half-peeled forms are noise; only the FINAL
;; fully-instantiated instance matters, so show just that -- the new-asm the LAST
;; inst/inst+ record introduced.  Mirrors proof-reader--typing-row's run-collapse.
(define (proof-reader--inst-row g ht)
  (let ((last-na #f))
    (for-each
     (lambda (ir)
       (when (memq (proof-reader--tac (ir-rec ir)) '(inst inst+))
         (let ((na (hash-table-ref/default ht (ir-idx ir) '())))
           (when (pair? na) (set! last-na (car na))))))
     g)
    (string-append
     "Instantiate the hypothesis"
     (if last-na (string-append ":" (proof-reader--display last-na)) "."))))

;; a bulletless sub-header row marking the base / inductive-step branch of an
;; `ni' proof (empty \item label -> no step number in the margin).
(define (proof-reader--branch-hdr indvar which)
  (let ((v (if indvar (expr->tex indvar) "n")))
    (if (eq? which 'base)
        (string-append "  \\item[]\\textbf{Base case} ($" v " = 0$):\n")
        (string-append "  \\item[]\\textbf{Inductive step} ($" v " \\to " v " + 1$):\n"))))

;;; --- statement verbalizer (the Proposition) ----------------------------
;;; Render a proposition wff as structured mathematician's English: a leading run
;;; of guarded universals -> "Suppose/Let v in S" (a PREDICATE guard folds to
;;; "v s.t. P(v)" and forms its own clause, preserving the formal =>); a bare
;;; implication -> "If A then B"; an existential -> "There is v in S such that ...".
;;; Keyword alternates Suppose/Let across clauses.  Arithmetic renders PREFIX here
;;; (*tex-arith-prefix?*) so it never competes with the ring operations.

;; internal op -> its "usual" name; drives the "we use the internal representation"
;; note appended when a statement mentions such an op.
(define *proof-reader-internal-notes* '((comb-kk . "the binomial coefficient term")))

;; one peel of a leading guarded universal: (kind item-tex body) or #f.
;;   'mem  v in S   (groups into a run)   'pred v s.t. P (own clause)   'bare v
(define (proof-reader--univ-step e)
  (cond
    ((tex--typed-forall-parts e)
     => (lambda (vsb)
          (list 'mem (string-append (expr->tex (car vsb)) " \\in " (expr->tex (cadr vsb)))
                (caddr vsb))))
    ((and (pair? e) (eq? (car e) 'forall) (= (length e) 3)
          (pair? (caddr e)) (eq? (car (caddr e)) 'implies) (= (length (caddr e)) 3))
     (let ((v (cadr e)) (imp (caddr e)))
       ;; the two halves are kept APART -- a `pred' item is (variable . condition)
       ;; and not one glued string -- because "Let h be s.t. P" needs a word
       ;; between them and "for every h s.t. P" does not.  Glued at build time,
       ;; the only place left to insert it was before the keyword, which is how
       ;; "Let be h s.t." got out (2026-09-05).
       (list 'pred (cons (expr->tex v) (expr->tex (cadr imp)))
             (caddr imp))))
    ((and (pair? e) (eq? (car e) 'forall) (= (length e) 3))
     (list 'bare (expr->tex (cadr e)) (caddr e)))
    (else #f)))

;; --- display-time prenex normalization -------------------------------------
;; A goal may bind several variables before stating their guards, e.g.
;;   forall n. forall p. (n in NN) => (p in mat(k,n)) => body
;; which renders as "Let n, and suppose p s.t. (n in NN)" -- n's typing dangling
;; on p.  Reorder for DISPLAY so each guard sits right after the binder it types:
;;   forall n. (n in NN) => forall p. (p in mat(k,n)) => body
;; A guard is assigned to the LATEST bound variable free in it (so p in mat(k,n)
;; goes to p, not n).  Pure display transform -- the proof is untouched.
(define (proof-reader--pr-any p lst)
  (and (pair? lst) (or (p (car lst)) (proof-reader--pr-any p (cdr lst)))))
(define (proof-reader--interleave vs guards body)
  (if (null? vs)
      (fold-right (lambda (g acc) (list 'implies g acc)) body guards)   ; unbound guards
      (let* ((v (car vs)) (rest (cdr vs))
             (mine (filter (lambda (g)
                             (and (memq v (free-vars g))
                                  (not (proof-reader--pr-any
                                        (lambda (w) (memq w (free-vars g))) rest))))
                           guards))
             (others (filter (lambda (g) (not (memq g mine))) guards)))
        (list 'forall v
              (fold-right (lambda (g acc) (list 'implies g acc))
                          (proof-reader--interleave rest others body) mine)))))
(define (proof-reader--norm e)
  (cond
    ((and (pair? e) (eq? (car e) 'forall) (= (length e) 3))
     (let vloop ((x e) (vs '()))
       (if (and (pair? x) (eq? (car x) 'forall) (= (length x) 3))
           (vloop (caddr x) (cons (cadr x) vs))
           (let gloop ((y x) (gs '()))
             (if (and (pair? y) (eq? (car y) 'implies) (= (length y) 3))
                 (gloop (caddr y) (cons (cadr y) gs))
                 (proof-reader--interleave (reverse vs) (reverse gs)
                                           (proof-reader--norm y)))))))
    ((and (pair? e) (eq? (car e) 'implies) (= (length e) 3))
     (list 'implies (cadr e) (proof-reader--norm (caddr e))))
    (else e)))

;; peel a maximal universal run into (clauses . body); a 'mem run accumulates,
;; a 'pred is flushed on its own (an implication boundary in the formal wff).
(define (proof-reader--peel-univs e)
  (let loop ((e e) (clauses '()) (cur '()))
    (let ((step (proof-reader--univ-step e)))
      (cond
        ((not step)
         (cons (append clauses (if (pair? cur) (list (cons 'mem cur)) '())) e))
        ((eq? (car step) 'pred)
         (loop (caddr step)
               (append clauses (if (pair? cur) (list (cons 'mem cur)) '())
                       (list (cons 'pred (list (cadr step)))))
               '()))
        (else (loop (caddr step) clauses (append cur (list (cadr step)))))))))

(define (proof-reader--exists-step e)
  (cond
    ((tex--typed-exists-parts e)
     => (lambda (vsb)
          (list (string-append (expr->tex (car vsb)) " \\in " (expr->tex (cadr vsb)))
                (caddr vsb))))
    ((and (pair? e) (eq? (car e) 'forsome) (= (length e) 3))
     (list (expr->tex (cadr e)) (caddr e)))
    (else #f)))

;; Join rendered items as English rather than as a list: "a, b and c", with
;; each item its own math group.  The items used to sit inside ONE $...$ joined
;; by ", ", which reads as a list of symbols where the sentence wants a
;; conjunction -- "Suppose n in N, x in R" for two independent suppositions.
;; a clause item is either a rendered string or, for a `pred' clause, the pair
;; (variable . condition).  GLUE says what goes between the halves.
(define (proof-reader--item->string it glue)
  (if (pair? it)
      (string-append (car it) glue (cdr it))
      it))

(define (proof-reader--join-and items0)
  (let* ((items (map (lambda (i) (proof-reader--item->string i " \\text{ s.t. } "))
                     items0))
         (n (length items)))
    (cond ((= n 0) "")
          ((= n 1) (string-append "$" (car items) "$"))
          ((= n 2) (string-append "$" (car items) "$ and $" (cadr items) "$"))
          (else
           (string-append
            (proof-tex--join (map (lambda (i) (string-append "$" i "$"))
                                  (except-last-pair items))
                             ", ")
            " and $" (car (last-pair items)) "$")))))

;; render clauses, alternating Suppose/Let starting at index `depth'.
;;
;; "be" belongs to the LET branch alone, and only before a `pred' clause: the
;; clause text is shared between the two keywords, so putting it in the s.t.
;; renderer would produce "Suppose h be s.t.".  "Let h be s.t. P" is English;
;; "Let n, x" is too, and takes no "be" -- which is why the test is on the
;; clause KIND and not on the keyword alone.
(define (proof-reader--render-clauses clauses depth)
  (let loop ((cs clauses) (i depth) (out '()))
    (if (null? cs) (proof-tex--join (reverse out) ". ")
        (let* ((kw    (if (even? i) "Suppose" "Let"))
               (pred? (eq? (car (car cs)) 'pred))
               (items (if (and pred? (string=? kw "Let"))
                          (map (lambda (it)
                                 (if (pair? it)
                                     (string-append (car it)
                                                    " \\text{ be s.t. } " (cdr it))
                                     it))
                               (cdr (car cs)))
                          (cdr (car cs)))))
          (loop (cdr cs) (+ i 1)
                (cons (string-append kw " " (proof-reader--join-and items)) out))))))

;; render clauses in a NESTED position.  "Suppose"/"Let" are imperative: they
;; instruct the reader to fix something before the claim is made, and only the
;; LEADING run of a proposition is in that position.  A universal reached after
;; "such that" or "if ... then" is part of the claim itself and has to read as a
;; quantifier -- "There is m in T such that Let k in T, m <= k" (nn-least-element,
;; found 2026-08-09) is not English.  No alternation here, hence no `depth'.
(define (proof-reader--render-clauses-nested clauses)
  (proof-tex--join
   (map (lambda (c)
          (string-append (if (= (length (cdr c)) 1) "for every $" "for all $")
                         (proof-tex--join
                          (map (lambda (i)
                                 (proof-reader--item->string i " \\text{ s.t. } "))
                               (cdr c))
                          ", ")
                         "$"))
        clauses)
   ", "))

;; a NESTED statement (after "if ... then" / "such that"): no leading "Then".
(define (proof-reader--stmt-tail e)
  (let* ((cb (proof-reader--peel-univs e)) (clauses (car cb)) (body (cdr cb))
         (head (if (pair? clauses)
                   (string-append (proof-reader--render-clauses-nested clauses) ", ") "")))
    (string-append head
      (cond
        ((and (pair? body) (eq? (car body) 'implies) (= (length body) 3))
         (string-append "if $" (expr->tex (cadr body)) "$ then "
                        (proof-reader--stmt-tail (caddr body))))
        (else (proof-reader--display body))))))

;; PRECEDED? says whether a Suppose/Let clause was rendered before this body.
;; "Then" is the consequent half of a sentence whose antecedent those clauses
;; are; with no clauses there is nothing for it to follow, and a hypothesis-free
;; theorem printed as a bare "Then is-metric-space(cc-ms)" -- correct, and not
;; English (reported 2026-09-05).  The other two branches are whole sentences
;; already and read the same either way.
(define (proof-reader--stmt-body body preceded?)
  (cond
    ((proof-reader--exists-step body)
     => (lambda (step)
          (string-append "There is $" (car step) "$ such that "
                         (proof-reader--stmt-tail (cadr step)))))
    ((and (pair? body) (eq? (car body) 'implies) (= (length body) 3))
     (string-append "If $" (expr->tex (cadr body)) "$, then "
                    (proof-reader--stmt-tail (caddr body))))
    (else (string-append (if preceded? "Then" "")
                         (proof-reader--display body)))))

(define (proof-reader--stmt e depth)
  (let* ((cb (proof-reader--peel-univs e)) (clauses (car cb)) (body (cdr cb)))
    (if (pair? clauses)
        (string-append (proof-reader--render-clauses clauses depth) ". "
                       (proof-reader--stmt-body body #t))
        (proof-reader--stmt-body body #f))))

;; first subterm whose head is OP (for the internal-representation note).
(define (proof-reader--first-app e op)
  (cond ((not (pair? e)) #f)
        ((eq? (car e) op) e)
        (else (let loop ((xs e))
                (if (pair? xs)
                    (or (proof-reader--first-app (car xs) op) (loop (cdr xs)))
                    #f)))))

(define (proof-reader--internal-note claim)
  (apply string-append
    (map (lambda (kv)
           (let ((app (proof-reader--first-app claim (car kv))))
             (if app
                 (string-append "\n\n\\noindent\\emph{(Here $" (expr->tex app)
                                "$ is the internal representation of " (cdr kv)
                                "; it is used throughout the proof.)}\n")
                 "")))
         *proof-reader-internal-notes*)))

;; SETTABLE.  The statement's arithmetic renders PREFIX by default -- +(n,1),
;; \\cdot(a,b) -- so it cannot be read as, or confused with, the ring operations,
;; which are prefix already (add(r)(x,y)).  That is a judgement about a
;; STATEMENT, not about arithmetic, and until 2026-09-05 it was hard-wired: the
;; fluid-let below bound #t unconditionally, so setting `*tex-arith-prefix?*'
;; at the REPL changed nothing and gave no hint why.  Set this to #f for infix
;; statements; proof STEPS have always rendered infix and are unaffected.
(define *proof-reader-statement-prefix?* #t)

;; the proposition body: structured-English statement + any internal-rep note,
;; with arithmetic rendered per the switch above.
(define (proof-reader--statement claim)
  (fluid-let ((*tex-arith-prefix?* *proof-reader-statement-prefix?*))
    (string-append (proof-reader--stmt (proof-reader--norm claim) 0)
                   (proof-reader--internal-note claim))))

;; case-branch headers: after a (CASE-SPLIT P) bullet, the following groups
;; carry P (one branch) or (not P) (the other) among their hypotheses.  Track a
;; stack of active splits (P pos-labelled? neg-labelled?), label each case the
;; first time its hypothesis shows up, and pop a split once both cases are done
;; and we have left its scope.  Nested splits stack; only the innermost is
;; checked per group.  Returns (header-string . new-stack).
(define (proof-reader--case-label P neg?)
  (string-append "  \\item[]\\emph{Case} $"
                 (if neg? (string-append "\\lnot " (expr->tex P)) (expr->tex P))
                 "$:\n"))
(define (proof-reader--case-hdr csplits main asms)
  (cond
    ((and main (eq? (car (car main)) 'CASE-SPLIT))
     (cons "" (cons (list (cadr (car main)) #f #f) csplits)))   ; push, no header
    ((or (null? csplits) (not asms)) (cons "" csplits))
    (else
     (let* ((top (car csplits)) (P (car top)) (pos (cadr top)) (neg (caddr top))
            (inP (and (member P asms) #t))
            (inN (and (member (list 'not P) asms) #t))
            (sign (cond ((and inP (not inN)) 'pos) ((and inN (not inP)) 'neg) (else 'ambig))))
       (cond
         ((and (eq? sign 'pos) (not pos))
          (cons (proof-reader--case-label P #f) (cons (list P #t neg) (cdr csplits))))
         ((and (eq? sign 'neg) (not neg))
          (cons (proof-reader--case-label P #t) (cons (list P pos #t) (cdr csplits))))
         ((and (eq? sign 'ambig) pos neg) (cons "" (cdr csplits)))   ; both done -> pop
         (else (cons "" csplits)))))))

;; --- skolem de-renaming: eigenvariables the kernel mints (di / ew / ai) carry a
;; disambiguating counter, `q_521', `c2_522', ...  Strip it for display: map each
;; `base_<digits>' symbol to `base' (base2, base3, ... if several share a base),
;; consistently across the whole proof, before anything is rendered.
(define (proof-reader--skolem-base sym)
  (and (symbol? sym)
       (let* ((s (symbol->string sym)) (n (string-length s)))
         (let lp ((i (- n 1)))
           (cond ((< i 0) #f)
                 ((char=? (string-ref s i) #\_) (and (< i (- n 1)) (substring s 0 i)))
                 ((char-numeric? (string-ref s i)) (lp (- i 1)))
                 (else #f))))))
(define (proof-reader--collect-skolems records)
  (let ((seen (make-equal-hash-table)) (order '()))
    (define (walk x)
      (cond ((symbol? x)
             (when (and (proof-reader--skolem-base x) (not (hash-table-ref/default seen x #f)))
               (hash-table-set! seen x #t) (set! order (cons x order))))
            ((pair? x) (walk (car x)) (walk (cdr x)))))
    (for-each (lambda (r) (walk (car r)) (walk (cadr r)) (walk (caddr r))) records)
    (reverse order)))
(define (proof-reader--rename-map skolems)
  (let ((by-base (make-equal-hash-table)) (m (make-equal-hash-table)))
    (for-each (lambda (s)
                (let ((b (proof-reader--skolem-base s)))
                  (hash-table-set! by-base b (cons s (hash-table-ref/default by-base b '())))))
              skolems)
    (hash-table-walk by-base
      (lambda (b syms)
        (let lp ((ss (reverse syms)) (i 1))
          (when (pair? ss)
            (hash-table-set! m (car ss)
              (string->symbol (if (= i 1) b (string-append b (number->string i)))))
            (lp (cdr ss) (+ i 1))))))
    m))
(define (proof-reader--subst-syms x m)
  (cond ((symbol? x) (or (hash-table-ref/default m x #f) x))
        ((pair? x) (cons (proof-reader--subst-syms (car x) m)
                         (proof-reader--subst-syms (cdr x) m)))
        (else x)))
(define (proof-reader--derename records)
  (let ((sk (proof-reader--collect-skolems records)))
    (if (null? sk) records
        (let ((m (proof-reader--rename-map sk)))
          (map (lambda (r)
                 (list (proof-reader--subst-syms (car r) m)
                       (proof-reader--subst-syms (cadr r) m)
                       (map (lambda (a) (proof-reader--subst-syms a m)) (caddr r))
                       (list-ref r 3)))
               records)))))

(define (proof-reader--body name)
  (let* ((records (proof-reader--derename (proof-reader--records name)))
         (claim   (cadr (car records)))            ; sp record's goal
         (indexed (proof-reader--collapse-em (proof-reader--index records)))
         (ht      (proof-reader--annotate indexed))
         (grp     (proof-reader--group indexed))
         (setup   (car grp))
         (groups  (cdr grp))
         ;; setup sequent = state just before the first content step = the last
         ;; record in `setup' (or the sp record if setup is only sp).
         (setup-last (if (pair? setup) (ir-rec (car (last-pair setup))) (car records)))
         (setup-asms (caddr setup-last))
         (setup-goal (cadr setup-last))
         (setup-range (if (pair? setup) (proof-reader--range setup) "0")))
    (apply string-append
     "\\begin{proposition}[" (proof-tex--escape-tt (symbol->string name)) "]\n"
     (proof-reader--statement claim)
     "\n\\end{proposition}\n\n"
     "\\begin{proof}\n"
     "\\begin{itemize}[leftmargin=2.8em, itemsep=4pt, parsep=1pt]\n"
     (append
      ;; walk groups, threading the pre-goal / pre-asms (the setup sequent seeds
      ;; it) and, for an `ni' proof, the induction variable + branch phase so we
      ;; can insert "Base case" / "Inductive step" sub-headers.  Branch signal:
      ;; the base leaf proves P(0) (indvar not free); the step leaf proves
      ;; P(n)=>P(n+1) (indvar free again).  See proof-reader--gloss for the ni row.
      (let loop ((gs groups) (pre-goal setup-goal) (pre-asms setup-asms)
                 (indvar #f) (phase 'none) (csplits '()) (rows '()))
        (if (null? gs) (reverse rows)
            (let* ((g (car gs))
                   (primary (proof-reader--group-primary g))
                   (main    (and primary (ir-rec primary)))
                   (kind    (and primary (proof-reader--kind primary ht)))
                   (closer  (and primary (proof-reader--group-closer g primary)))
                   ;; an inst/inst+ content group (possibly a merged run) -> show
                   ;; only the final peeled instance, not each half-peeled form.
                   (inst-run? (and main (memq (car (car main)) '(inst inst+))
                                   (not (eq? kind 'typing))))
                   ;; the goal just before the primary, NOT the group's entry goal
                   (main-pre-goal (if primary
                                      (proof-reader--goal-before g primary pre-goal)
                                      pre-goal))
                   (gloss   (cond ((eq? kind 'typing) (proof-reader--typing-row g ht))
                                  (inst-run? (proof-reader--inst-row g ht))
                                  (main (proof-reader--gloss main main-pre-goal pre-asms))
                                  (else "")))
                   ;; What a merged closer closed depends on what it followed: a
                   ;; `cut' opens a SIDE goal and the steps after it prove that,
                   ;; and a typing row is a side condition; anything else and the
                   ;; closer closed the branch's own goal.  Saying "(closes)" for
                   ;; both read as though the auxiliary claim closed the theorem.
                   (side?   (and primary
                                 (or (eq? kind 'typing)
                                     (eq? (proof-reader--tac (ir-rec primary)) 'cut))))
                   (by-ass? (and closer (eq? (proof-reader--tac closer) 'ass)))
                   (close-txt (cond ((not closer) "")
                                    (side? (if by-ass?
                                               "  \\emph{(side goal holds by assumption)}"
                                               "  \\emph{(side goal discharged)}"))
                                    (by-ass? "  \\emph{(holds by assumption)}")
                                    (else "  \\emph{(closes)}")))
                   (is-ni   (and main (eq? (car (car main)) 'ni)))
                   (new-indvar (if is-ni
                                   (and (pair? pre-goal) (eq? (car pre-goal) 'FORALL) (cadr pre-goal))
                                   indvar))
                   (ggoal   (or (and main (cadr main)) pre-goal))
                   (this-step? (and indvar (memq indvar (free-vars ggoal))))
                   ;; header + phase transition (only for an ni proof, after the ni row)
                   (hdr+phase
                    (cond (is-ni (cons "" 'await-base))
                          ((eq? phase 'await-base)
                           (if this-step?
                               (cons (proof-reader--branch-hdr indvar 'step) 'step)
                               (cons (proof-reader--branch-hdr indvar 'base) 'base)))
                          ((and (eq? phase 'base) this-step?)
                           (cons (proof-reader--branch-hdr indvar 'step) 'step))
                          (else (cons "" phase))))
                   (ch+cs   (proof-reader--case-hdr csplits main (and main (caddr main))))
                   (row (string-append
                         (car hdr+phase)
                         (car ch+cs)
                         "  \\item[\\textbf{" (proof-reader--range g) "}] "
                         gloss close-txt "\n"))
                   ;; thread the state AFTER the whole group (its last record),
                   ;; not the first content record -- so a merged run (inst/typing)
                   ;; hands the next step its true post-run goal/asms.
                   (last-state (ir-rec (car (last-pair g))))
                   (new-goal (cadr last-state))
                   (new-asms (caddr last-state)))
              (loop (cdr gs) new-goal new-asms new-indvar (cdr hdr+phase)
                    (cdr ch+cs) (cons row rows)))))
      (list "\\end{itemize}\n\\end{proof}\n")))))

;; render one proof, or a LIST of proofs into a single document (each its own
;; numbered proposition + proof), sharing one preamble.  A single symbol renders
;; exactly as before.
(define (proof-reader name-or-names)
  (string-append
   proof-tex--preamble
   (if (pair? name-or-names)
       (apply string-append
              (map (lambda (n) (string-append (proof-reader--body n) "\n\\bigskip\n\n"))
                   name-or-names))
       (proof-reader--body name-or-names))
   "\\end{document}\n"))

(define (write-proof-reader name path)
  (call-with-output-file path
    (lambda (port) (display (proof-reader name) port)))
  path)

(define (view-proof-reader-pdf name)
  ;; .tex lives in the source tree (*printouts-dir*) so it ships in the tarball;
  ;; the PDF + pdflatex aux junk render into the regenerable ~/.cache scratch.
  ;; load-option MUST precede any run-shell-command: run-shell-command is
  ;; unassigned until synchronous-subprocess is loaded.
  (load-option 'synchronous-subprocess)
  (let* ((cache (string-append (get-environment-variable "HOME") "/.cache/vnb/tex/"))
         (base  (string-append "reader-"
                               (if (pair? name)
                                   (proof-tex--join (map symbol->string name) "-")
                                   (symbol->string name))))
         ;; the .tex renders into the per-user CACHE, not the source tree: the
         ;; tree is writable by one account (see tex--archive-copy!,
         ;; proof-tex.scm).  The archive copy below is best-effort.
         (tex   (string-append cache base ".tex")))
    (tex--ensure-directory! cache)
    (write-proof-reader name tex)
    (tex--archive-copy! tex (string-append *printouts-dir* base ".tex"))
    (run-shell-command
     (string-append "pdflatex -interaction=nonstopmode -output-directory=" cache
                    " " tex " > /dev/null 2>&1"))
    (let ((pdf (string-append cache base ".pdf")))
      (if (file-exists? pdf) pdf
          (error "view-proof-reader-pdf: pdflatex produced no PDF -- see" (string-append cache base ".log"))))))
