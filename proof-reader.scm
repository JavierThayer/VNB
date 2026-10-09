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
;; a wff is TRIVIAL (the user, 2026-10-04: "Clearly 0 in NN, is-ring(r), one(r) in
;; carr(r)"; "trivial structure specializations can be omitted") when it is a
;; typing, or a STRUCTURE PREDICATE applied to terms -- is-ring(r) from
;; commutative-ring-is-ring -- with no connective in it.  A run of steps that
;; establish only trivial facts collapses to one "Clearly ..." line.
(define (proof-reader--structure-atom? w)
  (and (pair? w) (symbol? (car w))
       (let ((n (symbol->string (car w))))
         (and (> (string-length n) 3) (string-ci=? (substring n 0 3) "is-")))
       (not (find-first (lambda (x) (and (pair? x) (memq (car x) '(AND OR NOT IMPLIES IFF FORALL FORSOME))))
                      (cdr w)))))
(define (proof-reader--trivial-wff? w)
  (and (pair? w)
       (case (car w)
         ((IN) #t)
         ((FORALL FORSOME) (proof-reader--trivial-wff? (caddr w)))
         ((IMPLIES) (proof-reader--trivial-wff? (caddr w)))
         ((< <=) #t)                      ; an ordering fact between terms: (0 - 1) < 0, n < n + 1
         (else (proof-reader--structure-atom? w)))))

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
                  (and (pair? na) (proof-reader--all? proof-reader--trivial-wff? na))))
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

;; Did a group's CLOSER close a SIDE goal?  A record's goal is the focus goal
;; AFTER its step, so the goal the closer closed is the one the step before it
;; recorded.  That goal is a side goal when a `cut' opened it (the cut's own
;; record carries it: focus moves to the side goal) or when it is a typing or
;; definedness obligation posted by a tactic (`t in C', `t = t'); the
;; proposition's own goal (the setup goal) is never one.  Until 2026-10-05 the
;; test was "the primary is a cut, or the group is a typing run"; once the
;; collapse of trivial runs counted ordering facts as trivial, the LAST group of
;; nn-lt-double (two order-transitivity citations, then `ass') became a typing
;; run and the theorem's closer read "(the claim holds by assumption)".
(define (proof-reader--side-closer? g closer irecs setup-goal)
  (let ((closed (let loop ((rs g) (prev #f))
                  (cond ((null? rs) prev)
                        ((eq? (ir-rec (car rs)) closer) prev)
                        (else (loop (cdr rs) (cadr (ir-rec (car rs)))))))))
    (and closed
         (not (equal? closed setup-goal))
         (or (find-first (lambda (ir)
                           (let ((r (ir-rec ir)))
                             (and (eq? (proof-reader--tac r) 'cut)
                                  (equal? (cadr r) closed))))
                         irecs)
             (and (pair? closed)
                  (or (eq? (car closed) 'IN)
                      (and (eq? (car closed) '=)
                           (equal? (cadr closed) (caddr closed))))))
         #t)))

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
;; "By the proposition \emph{is-path-endpoints}" (notes-59, 2026-10-05), the noun
;; by provenance: proven or certified -> proposition, definitional -> definition,
;; asserted or primitive -> axiom.
(define (proof-reader--cite a)
  (if (symbol? a)
      (let ((noun (case (provenance-of a)
                    ((definitional) "definition")
                    ((asserted primitive) "axiom")
                    (else "proposition"))))
        (string-append "the " noun " \\emph{" (proof-tex--escape-tt (symbol->string a)) "}"))
      "the hypothesis"))

;; a formula shown as its own displayed equation (breaks/wraps via
;; expr->tex-display so wide prefix terms fit the page instead of overflowing).
;; A formula that fits in the running text stays there (notes-59, 2026-10-05: "a
;; line break to display an equation which could be better displayed in-line");
;; only a wide one gets its own display.  The ruler is the plain printed width.
(define *proof-reader-inline-width* 60)
(define (proof-reader--display e)
  (if (<= (tex--width e) *proof-reader-inline-width*)
      (string-append " $" (expr->tex-top e) "$")
      (string-append "\n\\begin{equation*}\n" (expr->tex-display e) "\n\\end{equation*}\n")))
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
;; The assumptions the group's STRUCTURAL prefix (di / ai) landed before the primary:
;; the eigenvariables and hypotheses a `di' introduced, which the sketch used to
;; drop silently (the user's notes-58: a direct inference on forall([a in X, b in Y],
;; FUBA(a, b)) reads "Suppose a in X, b in Y").  Rendered as a leading "Suppose ...".
(define (proof-reader--asms-before g primary pre-asms)
  (let loop ((rs g) (prev #f))
    (cond ((null? rs) pre-asms)
          ((eq? (car rs) primary) (if prev (caddr (ir-rec prev)) pre-asms))
          (else (loop (cdr rs) (car rs))))))
;; an atom's TeX without the outer parentheses expr->tex puts around a relation
(define (proof-reader--atom-tex a)
  (let* ((t (if (equal? a '(IS-THE-INDUCTION-HYPOTHESIS)) "\\text{the induction hypothesis}" (expr->tex a)))
         (n (string-length t)))
    (if (and (> n 2) (char=? (string-ref t 0) #\() (char=? (string-ref t (- n 1)) #\))
             ;; balanced as a whole: the first paren closes at the end
             (let loop ((i 1) (d 1))
               (cond ((= i (- n 1)) (= d 1))
                     ((char=? (string-ref t i) #\() (loop (+ i 1) (+ d 1)))
                     ((char=? (string-ref t i) #\)) (if (= d 1) #f (loop (+ i 1) (- d 1))))
                     (else (loop (+ i 1) d)))))
        (substring t 1 (- n 1))
        t)))
;; the guards of the claim's own prefix (what the proposition's "Suppose" fixed):
;; a branch of an induction re-peels them, and they are not to be supposed again
(define (proof-reader--claim-guards claim)
  (let loop ((e claim) (acc '()))
    (cond ((and (pair? e) (eq? (car e) 'FORALL) (= (length e) 3)) (loop (caddr e) acc))
          ((and (pair? e) (eq? (car e) 'IMPLIES) (= (length e) 3)) (loop (caddr e) (cons (cadr e) acc)))
          (else acc))))
(define *proof-reader-claim-guards* '())
;; a list of items as prose when they are short, as a displayed block when not
(define (proof-reader--items-text items)
  (let ((width (apply + (map (lambda (a) (string-length (expression->string a))) items))))
    (if (and (<= width 150) (not (find-first (lambda (a) (> (string-length (expression->string a)) 90)) items)))
        (string-append (proof-reader--join-and (map proof-reader--atom-tex items)) ". ")
        (string-append "\n\\begin{equation*}\n\\begin{array}{@{}l@{}}\n"
                       (proof-tex--join (map expr->tex-display items) " \\\\\n")
                       "\n\\end{array}\n\\end{equation*}\n"))))
;; "Suppose ..." for what the group's `di' steps introduced (eigenvariables, hypotheses),
;; "Hence ..." for what its `ai' steps unpacked -- a consequence, not a supposition
(define (proof-reader--suppose-prefix g primary pre-asms setup-asms indvar)
  (if (not primary) ""
      (let loop ((rs g) (prev pre-asms) (sup '()) (hence '()))
        (cond
          ((or (null? rs) (eq? (car rs) primary))
           (let* ((drop (lambda (l) (filter (lambda (a) (and (not (member a setup-asms))
                                                             (not (member a *proof-reader-claim-guards*))))
                                            l)))
                  ;; an unpacked conjunction whose conjuncts are listed too is noise
                  (no-and (lambda (l) (filter (lambda (a) (not (and (pair? a) (eq? (car a) 'AND)
                                                                     (member (cadr a) l) (member (caddr a) l))))
                                              l)))
                  (sup (no-and (drop (reverse sup)))) (hence (no-and (drop (reverse hence))))
                  (ih (lambda (a) (if (and indvar (> (string-length (expression->string a)) 120))
                                      '(IS-THE-INDUCTION-HYPOTHESIS) a))))
             (string-append
              (if (pair? sup)
                  (string-append "Suppose "
                                 (proof-reader--items-text (map ih sup)))
                  "")
              (if (pair? hence)
                  (string-append "Hence " (proof-reader--items-text hence))
                  ""))))
          (else
           (let* ((r (ir-rec (car rs))) (tac (proof-reader--tac r)) (asms (caddr r))
                  (news (proof-reader--new-asms prev asms)))
             (loop (cdr rs) asms
                   (if (eq? tac 'di) (append (reverse news) sup) sup)
                   (if (memq tac '(ai mac-h lam-b-h slot-h)) (append (reverse news) hence) hence))))))))
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
           (string-append "Claim:" (proof-reader--display (car args)))
           "By a cut on an auxiliary claim."))
      ((slot)
       (string-append "Read off the component " (proof-reader--cite (and (pair? args) (car args)))
                      (if goal (string-append " of the structure, reduce to" (proof-reader--display goal)) ".")))
      ((mac-h)
       (string-append "Unfolding " (proof-reader--cite (and (pair? args) (car args))) " in the hypothesis"
                      (if (pair? news) (string-append ":" (proof-reader--display (car news))) ".")))
      ((lam-b-h)
       (string-append "$\\beta$-reducing the hypothesis"
                      (if (pair? news) (string-append ":" (proof-reader--display (car news))) ".")))
      ((subst)
       ;; the recorded argument IS the equation, in the direction it was used
       ;; (the user, 2026-10-04: "substitute what where?")
       (let ((eqn (and (pair? args) (car args))))
         (string-append
          (if (and (pair? eqn) (= (length eqn) 3))
              (string-append "Substituting $" (expr->tex (cadr eqn)) " = " (expr->tex (caddr eqn)) "$")
              "Substituting the established equation")
          (if goal (string-append ", reduce to" (proof-reader--display goal)) "."))))
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

;; " by linear arithmetic", " by reflexivity", ...: the closer named for the
;; parenthetical after a claim or a branch (notes-62).  `ass' is worded by its callers.
(define (proof-reader--closer-how closer)
  (case (proof-reader--tac closer)
    ((ineq)         " by linear arithmetic")
    ((arith)        " by ground arithmetic")
    ((crs rs simp)  " by commutative-ring simplification")
    ((sos)          " by sum of squares")
    ((prop)         " propositionally")
    ((rfl qrfl)     " by reflexivity")
    ((contra)       " by contradiction")
    ((ass)          " by assumption")
    (else (let ((p (assq (proof-reader--tac closer) *proof-reader-tac-prose*)))
            (if p "" (string-append " by \\texttt{" (proof-tex--escape-tt (symbol->string (proof-reader--tac closer))) "}"))))))

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
    ;; "Clearly a, b and c." on one line when the atoms fit (the user, 2026-10-04);
    ;; the displayed one-atom-per-row block only when they do not.
    (let* ((atoms (reverse atoms))
           (width (apply + (map (lambda (a) (string-length (expression->string a))) atoms))))
      (cond
        ((null? atoms) "\\emph{Clearly.}")
        ((<= width 150)
         (string-append "Clearly "
                        (proof-reader--join-and (map proof-reader--atom-tex atoms))
                        "."))
        (else
         (string-append
          "Clearly"
          "\n\\begin{equation*}\n\\begin{array}{@{}l@{}}\n"
          (proof-tex--join (map expr->tex-display atoms) " \\\\\n")
          "\n\\end{array}\n\\end{equation*}\n"))))))

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
;; the placeholder the Suppose prefix uses for a long hypothesis inside an induction
(define (proof-reader--ih-text? a) (equal? a '(IS-THE-INDUCTION-HYPOTHESIS)))

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
;; a pending run is either a list of `mem' items or ('bare v ...): one clause either way
(define (proof-reader--flush-run cur)
  (cond ((null? cur) '())
        ((eq? (car cur) 'bare) (list cur))
        (else (list (cons 'mem cur)))))
(define (proof-reader--peel-univs e)
  (let loop ((e e) (clauses '()) (cur '()))
    (let ((step (proof-reader--univ-step e)))
      (cond
        ((not step)
         (cons (append clauses (proof-reader--flush-run cur)) e))
        ((eq? (car step) 'pred)
         (loop (caddr step)
               (append clauses (proof-reader--flush-run cur)
                       (list (cons 'pred (list (cadr step)))))
               '()))
        ;; a BARE universal (no guard) is its own clause kind, so the renderer can
        ;; say "For every s" / "Let s be arbitrary" instead of "Suppose s" (the
        ;; user, 2026-10-05); a run of bare variables stays one clause
        ((eq? (car step) 'bare)
         (if (and (pair? cur) (eq? (car cur) 'bare))
             (loop (caddr step) clauses (append cur (list (cadr step))))
             (loop (caddr step)
                   (append clauses (if (pair? cur) (list (cons 'mem cur)) '()))
                   (list 'bare (cadr step)))))
        (else (if (and (pair? cur) (eq? (car cur) 'bare))
                  (loop (caddr step) (append clauses (list cur)) (list (cadr step)))
                  (loop (caddr step) clauses (append cur (list (cadr step))))))))))

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
        (let* ((bare? (eq? (car (car cs)) 'bare))
               (kw    (cond (bare? "Let") ((even? i) "Suppose") (else "Let")))
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
                (cons (string-append kw " " (proof-reader--join-and items)
                                     (if bare? " be arbitrary" ""))
                      out))))))

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
         (string-append "if $" (expr->tex-top (cadr body)) "$ then "
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
     (string-append "If $" (expr->tex-top (cadr body)) "$, then "
                    (proof-reader--stmt-tail (caddr body))))
    (else (string-append (if preceded? "Then" "")
                         (proof-reader--display body)))))

(define (proof-reader--stmt e depth)
  (let* ((cb (proof-reader--peel-univs e)) (clauses (car cb)) (body (cdr cb)))
    (cond
      ;; the whole prefix is unguarded variables: "For every s, ..." (the user,
      ;; 2026-10-05: "Suppose s." read oddly for a variable nothing is supposed about)
      ((and (pair? clauses) (null? (cdr clauses)) (eq? (car (car clauses)) 'bare))
       (string-append (if (null? (cddr (car clauses))) "For every " "For all ")
                      (proof-reader--join-and (cdr (car clauses))) ", "
                      (proof-reader--stmt-body body #f)))
      ((pair? clauses)
       (string-append (proof-reader--render-clauses clauses depth) ". "
                      (proof-reader--stmt-body body #t)))
      (else (proof-reader--stmt-body body #f)))))

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

;;; --- display names for the variables (notes-59, 2026-10-05) ----------------
;;; "As the last step prior to LaTeX all variables in the statement and the proof
;;; should be renamed: single letters if at all possible; variables which can be
;;; easily ascertained to denote sets capitalized; function names f, g, h or
;;; phi, psi."  Computed once per proof from the statement and every recorded
;;; sequent, applied through `*tex-variable-names*' (tex-output.scm) around the
;;; proposition and its proof.  A VARIABLE is a symbol that occurs somewhere
;;; other than in head position and is not a registered constant, a class name
;;; or a printer atom; its KIND is read off its typings; its NAME is, in order of
;;; preference, its own letter, the Greek letter its name contains (pgam ->
;;; gamma), the last letter of an agent-tagged binder (gouz_ -> z) or the first
;;; letter of a word (rad -> r), then the kind's pool -- the first not yet taken.
(define *proof-reader-rename?* #t)

(define (proof-reader--symbol-occurrences x)
  ;; (non-head-symbols . head-symbols), each once, in order of first occurrence
  (let ((plain '()) (heads '()))
    (let walk ((x x) (head? #f))
      (cond ((symbol? x)
             (if head?
                 (if (not (memq x heads)) (set! heads (cons x heads)))
                 (if (not (memq x plain)) (set! plain (cons x plain)))))
            ((pair? x)
             (walk (car x) #t)
             (for-each (lambda (y) (walk y #f)) (cdr x)))))
    (cons (reverse plain) (reverse heads))))

(define (proof-reader--variable? s)
  (and (symbol? s)
       (not (memq s '(TRUTH FALSITY)))
       (not (number? s))
       (not (hash-table-ref/default *constant-registry* s #f))
       (not (memq s *class-name-constants*))
       (not (assq s *tex-atom-table*))
       (not (assq s *tex-binop-table*))
       (not (assq s *tex-special-table*))))

(define (proof-reader--kind-rank k)
  (case k ((function) 6) ((set) 5) ((structure) 4) ((nat) 3) ((number) 2) (else 1)))

(define (proof-reader--kinds vars formulas)
  ;; hash variable -> kind, from the typings in FORMULAS
  (let ((kinds (make-equal-hash-table)))
    (define (bump! v k)
      (when (memq v vars)
        (let ((old (hash-table-ref/default kinds v 'point)))
          (if (> (proof-reader--kind-rank k) (proof-reader--kind-rank old))
              (hash-table-set! kinds v k)))))
    (define (class-kind c)
      (cond ((pair? c) (case (car c) ((fun) 'function) ((power) 'set) (else #f)))
            ((eq? c 'nn) 'nat)
            ((memq c '(rr zz qq cc ord rr-star rr-pos-star)) 'number)
            ((eq? c 'set) 'set)
            (else #f)))
    ;; a typing counts only where the variable occurs FREE: a cited subset lemma
    ;; landed in the context binds its own a, b, x, and `(subset a b)' under that
    ;; binder said nothing about the proof's endpoint a (it printed as A)
    (let walk ((e formulas) (bound '()))
      (when (pair? e)
        (let ((h (car e)))
          (define (free? v) (and (symbol? v) (not (memq v bound))))
          (cond ((and (eq? h 'in) (= (length e) 3))
                 (let ((k (class-kind (caddr e))))
                   (if (and k (free? (cadr e))) (bump! (cadr e) k))
                   (if (free? (caddr e)) (bump! (caddr e) 'set))))
                ((and (eq? h 'subset) (= (length e) 3))
                 (if (free? (cadr e)) (bump! (cadr e) 'set))
                 (if (free? (caddr e)) (bump! (caddr e) 'set)))
                ((and (symbol? h) (memq h vars) (free? h)) (bump! h 'function))
                ((and (proof-reader--structure-atom? e) (pair? (cdr e)) (free? (cadr e)))
                 (bump! (cadr e) 'structure)))
          (let ((inner (if (and (memq h '(forall forsome iota comp sep vnb-lambda)) (pair? (cdr e)))
                           (let ((v (cadr e)))
                             (append (if (pair? v) (filter symbol? (cdr v)) (list v)) bound))
                           bound)))
            (for-each (lambda (y) (walk y inner)) e)))))
    kinds))

(define proof-reader--greek-roots
  '(("alp" . "\\alpha") ("bet" . "\\beta") ("gam" . "\\gamma") ("del" . "\\delta")
    ("eps" . "\\varepsilon") ("zet" . "\\zeta") ("thet" . "\\theta") ("lam" . "\\lambda")
    ("rho" . "\\rho") ("sig" . "\\sigma") ("tau" . "\\tau") ("phi" . "\\varphi")
    ("psi" . "\\psi") ("omeg" . "\\omega") ("eta" . "\\eta")))
(define (proof-reader--greek-root name)
  (let loop ((rs proof-reader--greek-roots))
    (cond ((null? rs) #f)
          ((string-search-forward (caar rs) name 0) (cdar rs))
          (else (loop (cdr rs))))))
(define (proof-reader--name-pool kind)
  (case kind
    ((function) '("f" "g" "h" "\\varphi" "\\psi" "\\chi" "F" "G" "H"))
    ((set) '("U" "V" "W" "A" "B" "S" "X" "Y" "Z" "C" "D" "E"))
    ((nat) '("n" "m" "k" "i" "j" "l" "p" "q"))
    ((structure) '("s" "t" "m" "r" "q"))
    (else '("x" "y" "z" "a" "b" "c" "t" "s" "r" "u" "v" "w"))))

(define (proof-reader--variable-names claim records)
  ;; -> alist symbol -> TeX string, for the variables of CLAIM and RECORDS
  (if (not *proof-reader-rename?*) '()
      (let* ((formulas (cons claim
                             (apply append (map (lambda (r) (cons (cadr r) (caddr r))) records))))
             (occ (proof-reader--symbol-occurrences formulas))
             (vars (filter proof-reader--variable? (car occ)))
             (kinds (proof-reader--kinds vars formulas))
             ;; what the non-variables print as: no variable may take one of these
             (reserved (map tex--symbol->string
                            (filter (lambda (s) (and (symbol? s) (not (memq s vars))))
                                    (append (car occ) (cdr occ)))))
             (used reserved)
             (out '()))
        (define (free? str) (not (member str used)))
        (define (letter? c) (char-alphabetic? c))
        (for-each
         (lambda (v)
           (let* ((kind (hash-table-ref/default kinds v 'point))
                  (name (symbol->string v))
                  (tagged? (and (> (string-length name) 1)
                                (char=? (string-ref name (- (string-length name) 1)) #\_)))
                  (base (if tagged? (substring name 0 (- (string-length name) 1)) name))
                  (cased (lambda (c) (string (if (eq? kind 'set) (char-upcase c) (char-downcase c)))))
                  (own (and (= (string-length base) 1) (letter? (string-ref base 0))
                            (cased (string-ref base 0))))
                  (greek (and (not own) (> (string-length base) 2) (proof-reader--greek-root base)))
                  (derived (and (not own) (> (string-length base) 0)
                                (let ((c (string-ref base (if tagged? (- (string-length base) 1) 0))))
                                  (and (letter? c) (cased c)))))
                  (candidates (append (if own (list own) '())
                                      (if greek (list greek (string-append greek "'") (string-append greek "''")) '())
                                      (if derived (list derived) '())
                                      (proof-reader--name-pool kind)))
                  (pick (find-first free? candidates)))
             (when pick
               (set! used (cons pick used))
               (set! out (cons (cons v pick) out)))))
         vars)
        (reverse out))))

(define (proof-reader--body name)
  (let* ((records (proof-reader--derename (proof-reader--records name)))
         (claim   (cadr (car records)))            ; sp record's goal
         (guards  (begin (set! *proof-reader-claim-guards* (proof-reader--claim-guards claim)) #t))
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
   (fluid-let ((*tex-variable-names* (proof-reader--variable-names claim records)))
    (apply string-append
     "\\begin{proposition*}[" (proof-tex--escape-tt (symbol->string name)) "]\n"
     (proof-reader--statement claim)
     "\n\\end{proposition*}\n\n"
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
                   (side?   (and closer (proof-reader--side-closer? g closer indexed setup-goal)))
                   (by-ass? (and closer (eq? (proof-reader--tac closer) 'ass)))
                   ;; WHAT closed it: the oracle or rule, by name (notes-62, 2026-10-07:
                   ;; "(the claim is established)" said nothing about how; the user asked
                   ;; for the oracle, not the hypotheses it used).
                   (how     (and closer (proof-reader--closer-how closer)))
                   (close-txt (cond ((not closer) "")
                                    (side? (if by-ass?
                                               "  \\emph{(the claim holds by assumption)}"
                                               (string-append "  \\emph{(the claim is established" how ")}")))
                                    (by-ass? "  \\emph{(holds by assumption)}")
                                    (else (string-append "  \\emph{(closes" how ")}"))))
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
                         (proof-reader--suppose-prefix g primary pre-asms setup-asms indvar)
                         gloss close-txt "\n"))
                   ;; thread the state AFTER the whole group (its last record),
                   ;; not the first content record -- so a merged run (inst/typing)
                   ;; hands the next step its true post-run goal/asms.
                   (last-state (ir-rec (car (last-pair g))))
                   (new-goal (cadr last-state))
                   (new-asms (caddr last-state)))
              (loop (cdr gs) new-goal new-asms new-indvar (cdr hdr+phase)
                    (cdr ch+cs) (cons row rows)))))
      (list "\\end{itemize}\n\\end{proof}\n"))))))

;;; --- with-defs: the definitions behind the statement ----------------------
;;; (the user, 2026-10-05: "an option `with-defs' that prefixes the statement with
;;; the relevant definitions, e.g. what is Inf(NN)").  A head of the statement is
;;; DEFINED when `def-predicate' / `def-constant' registered it (its defining
;;; axioms are in `library-definitions') or `def-functoid' did (`*functoid-registry*',
;;; a parameter list and a body; view functors excluded as DEFINITIONS.md excludes
;;; them).  Primitive heads (IN, SUBSET, FUN, succ, ...) and structure predicates
;;; and accessors have no entry here and are passed over.  Depth 1 = the heads of
;;; the statement, in order of first occurrence; depth 2 adds the defined heads of
;;; those definitions, and so on.  The block is independent of the proof: it is
;;; printed for a certified theorem too.
(define *proof-reader-with-defs* #f)        ; #f, or the depth (1 = the statement's heads)

(define (proof-reader--heads e)
  ;; the applied heads of E, each once, in order of first occurrence
  (let ((acc '()))
    (let walk ((e e))
      (when (pair? e)
        (when (and (symbol? (car e)) (not (memq (car e) acc)))
          (set! acc (cons (car e) acc)))
        (for-each walk (cdr e))))
    (reverse acc)))

(define (proof-reader--structure-of-head h ctx)
  ;; -> (NAME . shape|definitional) when H is IS-NAME, or an accessor of the
  ;; declared structure NAME; else #f.  An accessor (pts, dist) is a slot of
  ;; SEVERAL structures: it names NAME only when IS-NAME is among the heads in
  ;; CTX (the statement's and its definitions'), or when it has one owner.
  (let* ((str (symbol->string h))
         (base (and (> (string-length str) 3) (string-ci=? (substring str 0 3) "is-")
                    (string->symbol (substring str 3 (string-length str))))))
    (cond ((and base (lookup-structure base)) (cons base 'shape))
          ((and base (lookup-definitional-structure base)) (cons base 'definitional))
          (else (let* ((owners (filter
                                (lambda (n)
                                  (let ((sd (hash-table-ref/default *structure-table* n #f)))
                                    (and sd (assq h (structure-def-slots sd)))))
                                (hash-table-keys *structure-table*)))
                       (named (filter (lambda (n) (memq (symbol-append 'IS- n) ctx)) owners)))
                  (cond ((= (length named) 1) (cons (car named) 'shape))
                        ((and (null? named) (= (length owners) 1)) (cons (car owners) 'shape))
                        (else #f)))))))

(define (proof-reader--structure-law name kind)
  ;; the characteristic law, as describe-structure finds it; #f when none is stored
  (hash-table-ref/default *theorem-table*
                          (if (eq? kind 'shape)
                              (symbol-append 'IS- name)
                              (string->symbol (string-append "is-" (string-downcase (symbol->string name)) "-def")))
                          #f))

(define (proof-reader--definition-of h #!optional ctx)
  ;; -> (axioms (NAME . FORMULA) ...) | (functoid PARAMS BODY) | (structure NAME KIND) | #f
  (let ((e (assq h (library-definitions *library*)))
        (ctx (if (default-object? ctx) '() ctx)))
    (cond (e (cons 'axioms (cdr e)))
          ((and (not (lookup-view-as h)) (hash-table-ref/default *functoid-registry* h #f))
           => (lambda (reg) (list 'functoid (car reg) (cadr reg))))
          ((proof-reader--structure-of-head h ctx)
           => (lambda (st) (list 'structure (car st) (cdr st))))
          (else #f))))

;; the applied heads inside a definition (what depth + 1 looks at)
(define (proof-reader--def-heads def)
  (case (car def)
    ((functoid) (proof-reader--heads (caddr def)))
    ((structure)
     (let ((law (proof-reader--structure-law (cadr def) (caddr def))))
       (if law (proof-reader--heads law) '())))
    (else (apply append (map (lambda (ax) (proof-reader--heads (cdr ax))) (cdr def))))))

(define (proof-reader--defined-heads claim depth)
  ;; the defined heads of CLAIM to the given depth, with their definitions
  (let loop ((frontier (proof-reader--heads claim)) (depth depth) (seen '()) (out '()))
    (if (or (null? frontier) (< depth 1))
        (reverse out)
        (let* ((new (let loop ((hs frontier) (acc '()))      ; unseen, each once
                      (cond ((null? hs) (reverse acc))
                            ((or (memq (car hs) seen) (memq (car hs) acc)) (loop (cdr hs) acc))
                            (else (loop (cdr hs) (cons (car hs) acc))))))
               ;; the heads an accessor's owner is looked for among: this round's
               ;; heads plus those of this round's (non-structure) definitions
               (ctx (append new
                            (apply append
                                   (map (lambda (h)
                                          (let ((d (proof-reader--definition-of h)))
                                            (if (and d (not (eq? (car d) 'structure)))
                                                (proof-reader--def-heads d) '())))
                                        new))))
               (defs (let loop ((hs new) (structs (map cadr (filter (lambda (d) (eq? (car (cdr d)) 'structure)) out))) (acc '()))
                       (if (null? hs) (reverse acc)
                           (let ((def (proof-reader--definition-of (car hs) ctx)))
                             (cond ((not def) (loop (cdr hs) structs acc))
                                   ((eq? (car def) 'structure)
                                    (if (memq (cadr def) structs)
                                        (loop (cdr hs) structs acc)
                                        (loop (cdr hs) (cons (cadr def) structs) (cons (cons (cadr def) def) acc))))
                                   (else (loop (cdr hs) structs (cons (cons (car hs) def) acc))))))))
               (next (apply append (map (lambda (d) (proof-reader--def-heads (cdr d))) defs))))
          (loop next (- depth 1) (append new seen) (append (reverse defs) out))))))

(define (proof-reader--slot-tex slot)
  ;; one component of a declared structure, as describe-structure--slot-line says it
  (let* ((nm (car slot)) (kind (cadr slot)) (extra (cddr slot))
         (app (lambda () (string-append "$" (expr->tex (list nm 's)) "$"))))
    (case kind
      ((carrier)  (string-append (app) ", the underlying set"))
      ((op)       (string-append (app) "$ : " (expr->tex (car extra)) " \\to " (expr->tex (cadr extra)) "$"))
      ((constant) (string-append (app) "$ \\in " (expr->tex (car extra)) "$, a distinguished element"))
      ((substructure) (string-append (app) ", a " (string-downcase (symbol->string (car extra)))))
      ((family)   (string-append (app) ", a family of subsets of $" (expr->tex (list (car extra) 's)) "$"))
      ((family-fun) (string-append (app) ", a function on the family $" (expr->tex (list (car extra) 's))
                                   "$ into $" (expr->tex (cadr extra)) "$"))
      ((relation) (string-append (app) ", a relation on $" (expr->tex (list (car extra) 's)) "$"))
      (else (app)))))

;; The ITEMIZED entry of a declared structure (the user, 2026-10-08: the book's
;; one-sentence entry gave no way to see which clause of the `declare-structure'
;; form each printed component came from, nor which conjuncts of the
;; characteristic law were the typings of the components and which the laws).
;; Read off the stored IS-X law itself, so nothing is said that the law does not
;; say: its conjuncts are sorted into the length condition, the conjuncts that
;; type or fix ONE component (an IN / = / == / SUBSET with the accessor term on
;; the left, or a one-argument predicate of it, e.g. a substructure's IS-Y), and
;; the rest, the laws.  Every conjunct is printed exactly once.  #f when the law
;; is not of the shape (FORALL s (IFF (IS-X s) <conjunction>)), and the caller
;; then writes the old sentence.
(define *proof-reader-slot-kind-words*
  '((carrier      "carrier"           "carriers")
    (op           "operation"         "op")
    (constant     "constant"          "constant")
    (derived      "derived carrier, fixed by the other components" "derived")
    (substructure "substructure"      "substructure")
    (family       "family of subsets" "family")
    (family-fun   "function on a family" "family-fun")
    (relation     "relation"          "relation")))

(define (proof-reader--structure-items sd law noun article)
  (let* ((body (and (pair? law) (eq? (car law) 'forall) (pair? (cddr law)) (caddr law)))
         (v (and body (let ((b (cadr law))) (cond ((symbol? b) b)
                                                  ((and (pair? b) (null? (cdr b)) (symbol? (car b))) (car b))
                                                  (#t #f)))))
         (iff (and v (pair? body) (eq? (car body) 'iff) body))
         (rhs (and iff (equal? (cadr iff) (list (symbol-append 'is- (structure-def-name sd)) v))
                   (caddr iff))))
    (and rhs
         (let* ((conjs (let flat ((e rhs))
                         (if (and (pair? e) (eq? (car e) 'and)) (append-map flat (cdr e)) (list e))))
                (length-c (find (lambda (c) (and (pair? c) (memq (car c) '(= ==)) (= (length c) 3)
                                                 (equal? (cadr c) (list 'length v))))
                                conjs))
                (slots (structure-def-slots sd))
                ;; what build-is-axiom (structures.scm) writes for a slot: its FIRST
                ;; membership (or, for a substructure, the one-argument IS-Y of it),
                ;; and for a derived carrier also the equation fixing it.  A later
                ;; membership of the same accessor is a LAW (TOP-SPACE: pts(s) is open).
                (owned (map (lambda (slot)
                              (let* ((acc (list (car slot) v))
                                     (typing (find (lambda (c)
                                                     (and (pair? c)
                                                          (or (and (eq? (car c) 'in) (= (length c) 3)
                                                                   (equal? (cadr c) acc))
                                                              (and (eq? (cadr slot) 'substructure)
                                                                   (= (length c) 2) (equal? (cadr c) acc)))))
                                                   conjs))
                                     (fix (and (eq? (cadr slot) 'derived)
                                               (find (lambda (c) (and (pair? c) (memq (car c) '(= ==))
                                                                      (= (length c) 3) (equal? (cadr c) acc)))
                                                     conjs))))
                                (filter (lambda (c) c) (list typing fix))))
                            slots))
                (laws (filter (lambda (c) (and (not (eq? c length-c))
                                               (not (proof-reader--any (lambda (l) (memq c l)) owned))))
                              conjs))
                (tm (lambda (e) (string-append "$" (expr->tex-top e) "$")))
                (is-x (list (symbol-append 'is- (structure-def-name sd)) v)))
           (string-append
            article noun " " (tm v) " is a list"
            (if length-c (string-append " of length " (tm (caddr length-c))) "")
            " whose components are listed below.  Each component is a projection, "
            "defined for any " (tm v) " as a tuple; the clause of the declaration that "
            "introduces it is named in typewriter.\\par\n\\begin{enumerate}[nosep]\n"
            (apply string-append
                   (map (lambda (slot cs)
                          (let ((ix (hash-table-ref/default *accessor-index* (car slot) #f))
                                (kw (assq (cadr slot) *proof-reader-slot-kind-words*)))
                            (string-append
                             "\\item "
                             (if ix
                                 (tm (list '= (list (car slot) v) (list 'nth (car ix) v)))
                                 (tm (list (car slot) v)))
                             (let ((w (if kw (cadr kw) (symbol->string (cadr slot)))))
                               (string-append (if (memv (string-ref w 0) '(#\a #\e #\i #\o #\u)) ", an " ", a ") w))
                             (if kw (string-append " (\\texttt{" (caddr kw) "})") "")
                             (if (pair? cs)
                                 (string-append ":" (proof-tex--join (map proof-reader--display cs) " and"))
                                 "")
                             ".\n")))
                        slots owned))
            "\\end{enumerate}\n"
            (if (pair? laws)
                (string-append
                 "The laws (the \\texttt{property} and \\texttt{law} clauses):\n\\begin{itemize}[nosep]\n"
                 (apply string-append
                        (map (lambda (c) (string-append "\\item" (proof-reader--law-item c) "\n")) laws))
                 "\\end{itemize}\n")
                "")
            "The characteristic law (the axiom \\texttt{"
            (proof-tex--escape-tt (string-downcase (symbol->string (car is-x))))
            "}): " (tm is-x) " holds if and only if "
            (if length-c (string-append (tm length-c) ", ") "")
            "every component has the typing listed with it"
            (if (pair? laws) ", and every law holds" "")
            ".\n")))))

;; one law as an itemize entry: inline up to a wider ruler than the running text's
;; (an item has the line to itself), else displayed -- a display right after \item
;; leaves an empty bullet line, so the ruler is generous.
(define *proof-reader-item-width* 90)
(define (proof-reader--law-item c)
  (if (<= (tex--width c) *proof-reader-item-width*)
      (string-append " $" (expr->tex-top c) "$")
      (proof-reader--display c)))

;; A REFINEMENT (`same-shape-as'): its law is (FORALL s (IFF (IS-X s) (AND (IS-PARENT s)
;; extra ...))).  Itemized the same way: the parent named, the extra laws listed.
;; #f when the law is not of that shape (the caller writes the old paragraph).
(define (proof-reader--refinement-items name parent law noun article noun-of)
  (let* ((body (and (pair? law) (eq? (car law) 'forall) (pair? (cddr law)) (caddr law)))
         (v (and body (let ((b (cadr law))) (cond ((symbol? b) b)
                                                  ((and (pair? b) (null? (cdr b)) (symbol? (car b))) (car b))
                                                  (#t #f)))))
         (rhs (and v (pair? body) (eq? (car body) 'iff)
                   (equal? (cadr body) (list (symbol-append 'is- name) v))
                   (caddr body)))
         (conjs (and rhs (let flat ((e rhs))
                           (if (and (pair? e) (eq? (car e) 'and)) (append-map flat (cdr e)) (list e)))))
         (pc (list (symbol-append 'is- parent) v)))
    (and conjs (member pc conjs)
         (let ((extra (filter (lambda (c) (not (equal? c pc))) conjs))
               (tm (lambda (e) (string-append "$" (expr->tex-top e) "$")))
               (pnoun (noun-of parent)))
           (string-append
            article noun " " (tm v) " is a " pnoun " (a refinement: the same components, see the "
            "definition of \\texttt{" (proof-tex--escape-tt (string-downcase (symbol->string parent))) "})"
            (if (pair? extra)
                (string-append
                 " that satisfies in addition the laws:\n\\begin{itemize}[nosep]\n"
                 (apply string-append
                        (map (lambda (c) (string-append "\\item" (proof-reader--law-item c) "\n")) extra))
                 "\\end{itemize}\n")
                ".\\par\n")
            "The characteristic law: " (tm (list (symbol-append 'is- name) v))
            " holds if and only if " (tm pc)
            (if (pair? extra) " and every law above holds" "") ".\n")))))

;; `any' of sequents.scm returns #t, not the value; this one is only a test.
(define (proof-reader--any pred l) (and (pair? l) (or (pred (car l)) (proof-reader--any pred (cdr l)))))

(define (proof-reader--structure-tex name kind)
  (let* ((sd (if (eq? kind 'shape) (lookup-structure name)
                 (let ((dsd (lookup-definitional-structure name)))
                   (and dsd (find-shape-structure (definitional-structure-parent dsd))))))
         (law (proof-reader--structure-law name kind))
         (noun-of (lambda (sym)                 ; METRIC-SPACE -> "metric space"
                    (list->string (map (lambda (c) (if (char=? c #\-) #\space c))
                                       (string->list (string-downcase (symbol->string sym)))))))
         (noun (noun-of name))
         (article (if (memv (string-ref noun 0) '(#\a #\e #\i #\o #\u)) "An " "A ")))
    (or
     (and (eq? kind 'shape) sd law (proof-reader--structure-items sd law noun article))
     (and (not (eq? kind 'shape)) law
          (proof-reader--refinement-items
           name (definitional-structure-parent (lookup-definitional-structure name))
           law noun article noun-of))
     (string-append
     (if (eq? kind 'shape)
         (string-append article noun " $s$ is a structure with components ")
         (string-append article noun " is a "
                        (noun-of (definitional-structure-parent (lookup-definitional-structure name)))
                        " (a refinement; the components are those of the parent): "))
     (if sd (proof-tex--join (map proof-reader--slot-tex (structure-def-slots sd)) "; ") "")
     ;; the accessors ARE projections (the user's question, 2026-10-08): each slot name is a
     ;; global constant with the definitional rewrite name(s) -> nth(k, s) for ANY s, k the
     ;; slot's 1-based index (structures.scm, install-accessor-macete!); say so with the k.
     (if sd
         (let ((eqs (filter (lambda (x) x)
                            (map (lambda (slot)
                                   (let ((ix (hash-table-ref/default *accessor-index* (car slot) #f)))
                                     (and ix
                                          (string-append "$" (expr->tex (list (car slot) 's)) " = "
                                                         (expr->tex (list 'NTH (car ix) 's)) "$"))))
                                 (structure-def-slots sd)))))
           (if (pair? eqs)
               (string-append ".\\par The components are the projections of $s$, defined for any $s$ as a tuple: "
                              (proof-tex--join eqs ", "))
               ""))
         "")
     (if law
         (string-append ".\\par The characteristic law: " (proof-reader--statement law))
         ".\n")))))

(define (proof-reader--definition-tex d)
  (let ((h (car d)) (def (cdr d)))
    (if (eq? (car def) 'structure)
        (string-append
         "\\noindent\\textbf{Definition} (\\texttt{" (proof-tex--escape-tt (symbol->string (cadr def))) "}).\\;"
         (proof-reader--structure-tex (cadr def) (caddr def)) "\n")
        (proof-reader--definition-tex-1 h def))))
(define (proof-reader--definition-tex-1 h def)
  (let ((h h) (def def))                         ; (the let the original body closed with)
    (string-append
     "\\noindent\\textbf{Definition} (\\texttt{" (proof-tex--escape-tt (symbol->string h)) "}).\\;"
     (if (eq? (car def) 'functoid)
         ;; name(params) := body, as DEFINITIONS.md writes a functoid
         ;; the body on its own display, row-broken like any statement (a
         ;; one-line \fit of CARD's IOTA body still ran off the page)
         (string-append "$" (expr->tex (cons h (cadr def))) " :=$"
                        (proof-reader--display (caddr def)))
         ;; the defining axiom(s), read as a statement is
         (apply string-append
                (map (lambda (ax) (string-append (proof-reader--statement (cdr ax)) "\n"))
                     (cdr def))))
     "\n")))

(define (proof-reader--definitions-block name)
  (let ((defs (and *proof-reader-with-defs*
                   (proof-reader--defined-heads (lookup-theorem name) *proof-reader-with-defs*))))
    (if (and defs (pair? defs))
        (string-append "\\subsection*{Definitions}\n"
                       (apply string-append (map proof-reader--definition-tex defs))
                       "\\bigskip\n\n")
        "")))

;; render one proof, or a LIST of proofs into a single document (each its own
;; numbered proposition + proof), sharing one preamble.  A single symbol renders
;; exactly as before.
(define (proof-reader name-or-names)
  (string-append
   proof-tex--preamble
   (if (pair? name-or-names)
       (apply string-append
              (map (lambda (n) (string-append (proof-reader--body* n) "\n\\bigskip\n\n"))
                   name-or-names))
       (proof-reader--body* name-or-names))
   "\\end{document}\n"))

;; A theorem installed from its certificate (certificates.scm) has no proof in this
;; image -- no trace, no script: say so, as `proof-tex' does, instead of dying with
;; "no proof named this in *session-log*" (2026-09-30: the suite from a certified band
;; died there).
(define (proof-reader--body* name)
  (string-append (proof-reader--definitions-block name) (proof-reader--body** name)))
(define (proof-reader--body** name)
  (if (and (certified-theorem? name)
           (not (hash-table-ref/default *proof-live-trace* name #f)))
      (string-append
       "\\section*{Proof of \\texttt{" (proof-tex--escape-tt (symbol->string name)) "}}\n"
       "Certified, no proof in this image: the theorem was installed from its "
       "certificate, written by an exam that ran and checked its proof "
       "(the last exam: mailbox/metrics/last-exam.json).  Read it from the exam's image "
       "(\\texttt{VNB\\_CERTIFIED=off ./prover --build-band}).\n\n")
      (proof-reader--body name)))

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

;;; =======================================================================
;;; (display-proof NAME PDF-PATH) -- the user's request, 2026-10-05: locate the
;;; proof script of theorem NAME, run it when this image holds no trace of it (a
;;; certified theorem was installed from its certificate and its proof never ran
;;; here), and typeset the READER-MODE printout to PDF-PATH.  Returns the PDF path.
;;;
;;; The script is the theorem's SOURCE FILE: `*theorem-source*' records the path a
;;; file was loaded from (the band carries that machine's path; it is re-rooted at
;;; *prover-dir* when it does not exist here), and when the table has nothing the
;;; theorem-library is searched for the `(qed 'NAME)' form.  Running the file runs
;;; EVERY proof in it (its helpers and the earlier theorems are what the one proof
;;; needs), re-installing the same statements, quietly, into a fresh environment
;;; as the load does; the cost is the file's proving time.  Without pdflatex the
;;; .tex is left beside the requested path and the message says so.
;;; =======================================================================
(define (display-proof--source name)
  (let* ((rec (hash-table-ref/default *theorem-source* name #f))
         (rec (and rec (if (string? rec) rec (->namestring rec))))
         (rerooted (and rec (let ((i (string-search-forward "prover/" rec 0)))
                              (and i (string-append *prover-dir* (substring rec (+ i 7) (string-length rec)))))))
         (found (cond ((and rec (file-exists? rec)) rec)
                      ((and rerooted (file-exists? rerooted)) rerooted)
                      (else #f))))
    (or found
        ;; the fallback: scan the proof files for the qed form
        (let ((needle (string-append "(qed '" (symbol->string name) ")")))
          (let loop ((files (directory-read (string-append *prover-dir* "theorem-library/") #f)))
            (cond ((null? files) #f)
                  ((let ((f (->namestring (car files))))
                     (and (string-suffix? ".scm" f)
                          (call-with-input-file f
                            (lambda (port)
                              (let scan ()
                                (let ((line (read-line port)))
                                  (cond ((eof-object? line) #f)
                                        ((string-search-forward needle line 0) #t)
                                        (else (scan)))))))
                          f)))
                  (else (loop (cdr files)))))))))

(define (display-proof--basename path)
  ;; the file name without directory or extension: `*theorem-source*' holds the
  ;; LOAD pathname (no extension; the loader picks .com or .scm), the source
  ;; found by display-proof--source ends in .scm.
  (let* ((i (let loop ((k (- (string-length path) 1)))
              (cond ((< k 0) 0) ((char=? (string-ref path k) #\/) (+ k 1)) (else (loop (- k 1))))))
         (b (substring path i (string-length path)))
         (n (string-length b)))
    (if (and (> n 4) (member (substring b (- n 4) n) '(".scm" ".com" ".bin")))
        (substring b 0 (- n 4))
        b)))

;; the load-list key certificates.scm files a proof file under: its path below
;; *prover-dir*, without the extension (theorem-library/goursat)
(define (display-proof--file-key src)
  (let* ((pd *prover-dir*) (n (string-length pd))
         (rel (if (and (> (string-length src) n) (string=? (substring src 0 n) pd))
                  (substring src n (string-length src))
                  (string-append "theorem-library/" (display-proof--basename src)))))
    (if (string-suffix? ".scm" rel) (substring rel 0 (- (string-length rel) 4)) rel)))

(define (display-proof--run-source! name)
  (let* ((src (display-proof--source name))
         (f (and src (display-proof--file-key src)))
         (store (and f (cert-read-file f)))
         ;; the file's certificate records MINUS the requested theorem's: the
         ;; certified loader then installs every other proof from its record and
         ;; runs only this one (goursat.scm has 60 proofs; the user waited on all
         ;; of them for one printout, 2026-10-05)
         (records (and store (filter (lambda (r) (not (eq? (cert-rec-name r) name))) (cdr store)))))
    (if (not src) (error "display-proof: no proof script found for" name))
    (display ";; display-proof: no trace of ") (display name)
    (display " in this image; running its proof from ") (display src)
    (if store
        (begin (display " (the file's other ") (display (length records))
               (display " proofs installed from their certificates)")))
    (newline)
    ;; The file re-installs theorems this image already holds (certified): the
    ;; re-installs are INTENTIONAL here, so install-theorem!'s "already installed;
    ;; re-installing the same statement" warning is off for the names this file
    ;; sourced, and the duplicate list the load-end audit reads is restored
    ;; (the user, 2026-10-05: the warning read as if the stored proofs changed;
    ;; nothing on disk does -- certificates are written only by the tree loader).
    (let ((own (let ((base (display-proof--basename src)))
                 (hash-table-fold *theorem-source*
                                  (lambda (n path acc)
                                    (let ((p (if (string? path) path (->namestring path))))
                                      (if (string=? (display-proof--basename p) base) (cons n acc) acc)))
                                  '()))))
      ;; The file's `sp' / `qed' write the SAME proof-state globals the user's own
      ;; proof lives in: hold them for the run and give them back, also when the
      ;; run is escaped (the workspace budget stopped a 90 s run of
      ;; cauchy-convex-closed's file, 2026-10-05, and left ITS proof -- 3 open
      ;; goals -- where the user's had been).  fluid-let restores on a non-local exit.
      (fluid-let ((*vnb-loading* #t)
                  (*install-intentional-redefinitions* (append own *install-intentional-redefinitions*))
                  (*install-duplicates* *install-duplicates*)
                  (*ps* *ps*) (*proof-script* *proof-script*)
                  (*proof-hidden-citations* *proof-hidden-citations*)
                  (*proof-mints* *proof-mints*)
                  (*fresh-mark-at-last-record* *fresh-mark-at-last-record*)
                  (*witness-aliases* *witness-aliases*)
                  (*current-goal* *current-goal*)
                  (*sp-counter-snapshot* *sp-counter-snapshot*)
                  (*live-trace* *live-trace*)
                  (*vnb-undo-stack* *vnb-undo-stack*)
                  (*dg-journal* *dg-journal*)
                  (*vnb-write-certs* #f))            ; a printout rewrites no store
        (if store
            (cert--load-certified! f src (lambda () (extend-top-level-environment *driver-kit-env*))
                                   'on records)
            (load src (extend-top-level-environment *driver-kit-env*)))))
    (if (not (hash-table-ref/default *proof-live-trace* name #f))
        (error "display-proof: the file ran but left no trace for" name src))
    src))

;;; (display-proof 'NAME "path.pdf")            the proof
;;; (display-proof 'NAME "path.pdf" 'with-defs)  prefixed by the definitions of the
;;;                                              statement's defined heads
;;; (display-proof 'NAME "path.pdf" 'with-defs 2) ... and of those definitions' heads
(define (display-proof name pdf-path . opts)
  (let ((depth (cond ((null? opts) #f)
                     ((eq? (car opts) 'with-defs)
                      (if (and (pair? (cdr opts)) (number? (cadr opts))) (cadr opts) 1))
                     (else (error "display-proof: unknown option" (car opts))))))
    (fluid-let ((*proof-reader-with-defs* depth))
      (display-proof--to-pdf name pdf-path))))
(define (display-proof--to-pdf name pdf-path)
  (load-option 'synchronous-subprocess)
  (if (not (hash-table-ref/default *proof-live-trace* name #f))
      (display-proof--run-source! name))
  (let* ((pdf  (->namestring (merge-pathnames pdf-path)))
         (base (let ((n (string-length pdf)))
                 (if (and (> n 4) (string-ci=? (substring pdf (- n 4) n) ".pdf")) (substring pdf 0 (- n 4)) pdf)))
         (tex  (string-append base ".tex"))
         (dir  (directory-namestring pdf)))
    (write-proof-reader name tex)
    (run-shell-command
     (string-append "pdflatex -interaction=nonstopmode -output-directory=" dir " " tex " > /dev/null 2>&1"))
    (cond ((file-exists? (string-append base ".pdf")) (string-append base ".pdf"))
          (else (display ";; display-proof: pdflatex produced no PDF (is it installed?); the TeX is ")
                (display tex) (newline)
                tex))))
