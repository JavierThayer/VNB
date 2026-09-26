;;; clobber-guard.scm -- the gate CLAUDE.md says does not exist.
;;;
;;; Both the VNB reader and MIT Scheme fold symbols to lowercase, so a proof
;;; file's innocent-looking
;;;
;;;     (define BC '(succ p))
;;;
;;; rebinds the `bc' TACTIC to a term.  Every later (bc 'thm) -- in that file
;;; and in every file loaded after it -- dies with "The object (...) is not
;;; applicable", or worse, quietly does the wrong thing.  Real cases: BC in
;;; bordered-eq-border-proof.scm (broke four suite tests in a different file),
;;; TT in hahn-banach-full-proof.scm and nn-least-element.scm, SP in a Smith
;;; driver, ID in mat-equiv-proof.scm.
;;;
;;; `case-fold-audit' and `constant-binder-audit' both inspect WFF binders and
;;; never Scheme defines, so neither sees it.
;;;
;;; The invariant enforced here is stronger than "do not shadow a tactic", and
;;; needs no registry of tactic names:
;;;
;;;   NO FILE MAY REBIND, TO A NON-PROCEDURE, A NAME THAT WAS A PROCEDURE
;;;   BEFORE IT LOADED.
;;;
;;; That is exactly the bug: `bc' was a procedure, `(define BC '(...))' makes it
;;; a list.  Redefining a procedure with another procedure stays legal, which
;;; matters -- several drivers re-define the shared `proof-leaves' / `any-pred'
;;; helpers, and that is (for now) load-bearing.  It is also the one gap:
;;; `(define (append a b) ...)' -- procedure over procedure -- is NOT caught.
;;;
;;; Loads FIRST, before any other VNB file (load.scm); `prover-load' calls
;;; clobber-guard-check! after each subsequent file.  It used to load at
;;; load.scm:518, and its own header admitted the consequence -- "files loaded
;;; before the snapshot are unguarded".  Measured 2026-08-16: **126 library
;;; files loaded before it, 118 after**, so more than half the library --
;;; including all of `structure-library/' -- was outside the alarm.

;;; The environment proof files are loaded into.  MIT's `load' with no
;;; environment argument uses the CALLER's environment, and load.scm's caller is
;;; this same top level -- so `bc' and friends live in this very frame, and
;;; environment-bound-names sees them (it reports the own frame only).
(define *clobber-guard-env* (the-environment))

(define *clobber-guard-procs* #f)        ; name -> #t, or #f before the snapshot

;; environment-lookup REFUSES a syntactic keyword ("Variable reference to a
;; syntactic keyword: bc*") and errors on an unassigned binding, so it cannot be
;; called bare over environment-bound-names.  Macros are simply never watched:
;; they answer 'unavailable both at snapshot and at check time, consistently.
(define (clobber-guard--value n)
  (call-with-current-continuation
    (lambda (k)
      (with-exception-handler (lambda (e) (k 'clobber-guard--unavailable))
        (lambda () (environment-lookup *clobber-guard-env* n))))))

(define (clobber-guard--procedure? n)
  (and (environment-bound? *clobber-guard-env* n)
       (procedure? (clobber-guard--value n))))

;;; SEED FROM THE GLOBAL ENVIRONMENT TOO (2026-08-16), and this is the point.
;;; `environment-bound-names' reports the OWN FRAME ONLY -- the comment above
;;; says so -- and at the head of the load that frame holds nine names.  MIT's
;;; own procedures live in the PARENT, so `append', `list', `cons', `length'
;;; were never in the watch set at all, at any snapshot point, early or late.
;;;
;;; They are exactly the names that matter.  Each is simultaneously a live
;;; Scheme procedure and a VNB head symbol, so a proof file's
;;; `(define APPEND '(...))' shadows a procedure the prover itself calls with a
;;; list.  `environment-bound?' DOES search the parent chain, so a shadow in the
;;; top frame is caught by the ordinary check once the name is in the set.
(define (clobber-guard-snapshot!)
  (let ((h (make-strong-eqv-hash-table)))
    (for-each (lambda (n) (if (clobber-guard--procedure? n) (hash-table-set! h n #t)))
              (append (environment-bound-names *clobber-guard-env*)
                      (environment-bound-names system-global-environment)))
    (set! *clobber-guard-procs* h)
    (display ";; clobber-guard: watching ")
    (display (length (hash-table-keys h)))
    (display " procedure bindings")
    (newline)))

;;; ONE PASS OVER THE OWN FRAME does both jobs -- detect casualties, and absorb
;;; what the file newly defined -- and it is what makes watching MIT's ~3900
;;; globals affordable.
;;;
;;; The obvious implementation walks the WATCH SET after every file, re-looking
;;; up each member.  That is 3975 names x ~250 files, each a `bound?' plus a
;;; lookup inside a continuation and an exception handler, and it cost 23 s on
;;; top of a 48 s cold load -- measured, not guessed.
;;;
;;; The direction was simply wrong.  A file can only turn a procedure into a
;;; non-procedure by DEFINING that name, and a definition lands in the top
;;; frame.  So the names that can possibly have changed are exactly the own
;;; frame's -- whether the victim was a VNB tactic or a shadowed MIT global.
;;; Walking the own frame is therefore COMPLETE for the invariant and costs in
;;; proportion to what the file did rather than to how much is being watched.
;;;
;;; The same pass grows the set: a name in the own frame that is a procedure and
;;; not yet watched becomes watched, so VNB's own tactics join as they appear
;;; and the early snapshot loses nothing.
;;;
;;; Report EVERY casualty, not just the first: one bad `define' usually comes
;;; with siblings, and a second 11-minute load to find the next one is a waste.
(define (clobber-guard-check! file)
  (if *clobber-guard-procs*
      (let ((bad '()))
        (for-each
         (lambda (n)
           (let ((watched (hash-table-ref/default *clobber-guard-procs* n #f))
                 (proc?   (clobber-guard--procedure? n)))
             (cond ((and watched (not proc?)) (set! bad (cons n bad)))
                   ((and (not watched) proc?)
                    (hash-table-set! *clobber-guard-procs* n #t)))))
         (environment-bound-names *clobber-guard-env*))
        (if (not (null? bad))
            (begin
              ;; drop them from the watch set: the damage is already reported,
              ;; and leaving them in would re-blame every later file.
              (for-each (lambda (n) (hash-table-delete! *clobber-guard-procs* n)) bad)
              (error
               (string-append
                "clobber-guard: " file
                " rebound a procedure to a non-procedure -- almost certainly a"
                " top-level (define X ...) whose name case-folds onto a tactic"
                " or onto one of MIT Scheme's own procedures."
                "  Use the file's helper prefix instead.  Casualties:")
               (sort bad (lambda (a b) (string<? (symbol->string a)
                                                 (symbol->string b))))))))))

(clobber-guard-snapshot!)

;;; =======================================================================
;;; THE READ-TIME CASE-FOLD LINT (2026-09-20) -- the sister defect, and the
;;; guard above cannot see it.
;;;
;;;     (define r11f-S (list 'SPAN ...))      ... 200 lines later ...
;;;     (define r11f-s (dk-fact! ...))
;;;
;;; MIT Scheme folds symbols to lowercase AT READ TIME, so those are ONE
;;; binding: the later definition silently replaces the earlier, and every
;;; reference in between now sees the wrong value.  The clobber-guard above
;;; cannot catch it (both are procedures, or neither is), and no audit inside
;;; the image can: by the time any Scheme-level check runs, the two spellings
;;; HAVE ALREADY BECOME THE SAME SYMBOL.  The only place they still differ is
;;; the SOURCE TEXT, which is why this lint reads the file.  Three agents lost
;;; probe runs to the pattern in one week (r11f-S / r11f-s, r8f-W / r8f-w).
;;;
;;; TWO STAGES, because the proof corpus is ~8 MB and a load must not pay for
;;; a character walk over it (measured 2026-09-20, on this box):
;;;
;;;   1. TRIGGER.  Slurp the file as a BYTEVECTOR (0.14 s for the whole tree;
;;;      through a character port the same read costs 8 s), decode it, and let
;;;      the COMPILED `string-search-all' find every "(define" at column 0;
;;;      read the spelling after each with a bounded scan.  Stage 1 sees text
;;;      inside comments and strings too, which is harmless: it never reports,
;;;      and a collision needs at least one spelling with an upper case letter
;;;      in it.  2.9 s for 632 files.
;;;   2. VERDICT.  Only when stage 1 saw a spelling with an upper case letter
;;;      (141 of the 632 files) does MIT's own reader run over the text with
;;;      `param:reader-fold-case?' bound to #f.  The reader handles `;',
;;;      `#|...|#', `#;' and strings itself -- that is the point of using it
;;;      rather than a hand-written scanner -- and it finds a top-level define
;;;      however it is indented.  2 s for those 141 files.
;;;
;;; Whole-tree cost 4.9 s, against a cold load of several minutes.
;;;
;;; WARN-ONLY, and it stays warn-only until the backlog is zero: five files
;;; collide today and all five load.  `report-case-fold-defines' prints what
;;; accumulated; the suite pins the procedure's behaviour on a scratch file.
;;;
;;; NOT the same check as `duplicate-define-audit' (audit.scm): that one reads
;;; 16 named ENGINE files with the FOLDING reader and counts a name defined
;;; twice, so it sees a collision in those files as a duplicate and cannot say
;;; which two spellings caused it; this one runs over every file the loader
;;; touches -- the proof corpus above all -- and names the spellings.
(define *case-fold-define-collisions* '())     ; (file (folded spelling ...) ...)

(define (cfd--slurp path)
  (call-with-binary-input-file path
    (lambda (port)
      (let ((bv (read-bytevector 100000000 port)))
        (if (bytevector? bv) (utf8->string bv) "")))))

(define (cfd--delimiter? c)
  (or (char=? c #\space) (char=? c #\tab) (char=? c #\newline)
      (char=? c #\return) (char=? c #\() (char=? c #\))))

;; The spelling that follows the "(define" starting at POS: `(define NAME',
;; `(define (NAME arg ...)' and the curried `(define ((NAME a) b)' alike.
(define (cfd--name-at text pos)
  (let ((n (string-length text)))
    (let skip ((i (+ pos 7)))
      (and (< i n)
           (let ((c (string-ref text i)))
             (cond ((or (char=? c #\space) (char=? c #\tab)
                        (char=? c #\newline) (char=? c #\return) (char=? c #\())
                    (skip (+ i 1)))
                   ((char=? c #\)) #f)
                   (#t (let scan ((j i))
                         (if (or (>= j n) (cfd--delimiter? (string-ref text j)))
                             (and (> j i) (substring text i j))
                             (scan (+ j 1)))))))))))

(define (cfd--has-upper? s)
  (let ((n (string-length s)))
    (let loop ((i 0))
      (and (< i n)
           (or (char-upper-case? (string-ref s i)) (loop (+ i 1)))))))

;; stage 1 -- cheap, over-approximate, never reports
(define (cfd--maybe-mixed? text)
  (let loop ((ps (if (string-prefix? "(define" text)
                     (cons -1 (string-search-all "\n(define" text))
                     (string-search-all "\n(define" text))))
    (and (pair? ps)
         (let ((nm (cfd--name-at text (+ (car ps) 1))))
           (or (and nm (cfd--has-upper? nm)) (loop (cdr ps)))))))

;; stage 2 -- MIT's reader with case folding OFF: the verdict
(define (cfd--define-target form)
  (and (pair? form)
       (symbol? (car form))
       (string-ci=? (symbol->string (car form)) "define")
       (pair? (cdr form))
       (let loop ((t (cadr form)))
         (cond ((symbol? t) (symbol->string t))
               ((pair? t) (loop (car t)))
               (#t #f)))))

(define (cfd--read-names text)
  (let ((port (string->input-port text)))
    (parameterize ((param:reader-fold-case? #f))
      (let loop ((acc '()))
        (let ((f (read port)))
          (if (eof-object? f)
              (reverse acc)
              (loop (let ((nm (cfd--define-target f)))
                      (if nm (cons nm acc) acc)))))))))

;; names -> ((folded spelling spelling ...) ...), one entry per folded name
;; that two different spellings share.
(define (cfd--collisions names)
  (let ((seen (make-equal-hash-table)) (out '()))
    (for-each (lambda (s)
                (let* ((k (string-downcase s))
                       (prev (hash-table-ref/default seen k '())))
                  (if (not (member s prev)) (hash-table-set! seen k (cons s prev)))))
              names)
    (hash-table-walk seen
      (lambda (k v) (if (> (length v) 1) (set! out (cons (cons k (sort v string<?)) out)))))
    (sort out (lambda (a b) (string<? (car a) (car b))))))

;;; The entry point, called from load.scm's per-file loader.  FILE is the
;;; load-relative name (for the message), PATH the source file to read.  A
;;; missing or unreadable file is NOT an error and NOT a finding: a compiled
;;; file still has its .scm beside it, and if it has not, there is nothing to
;;; lint.  Returns the collisions found in this file.
;;; ---------------------------------------------------------------------
;;; THE LOCAL-BINDING CASE-FOLD LINT (2026-09-24, batch 27-B, item 14).  The
;;; same trap one level down: two LOCAL binders in one top-level form whose
;;; spellings differ only by case -- `(let* ((seqg ...) (seqG ...)) ...)' --
;;; are ONE variable, the second shadowing the first.  Batch 22-B met it twice
;;; in one file (seqg / seqG, gk / Gk); the symptoms were a typing leaf that
;;; could not close and a lemma instantiated at the wrong term.  The define
;;; lint above sees top-level names only.
;;;
;;; Per top-level form, read with folding OFF: every name bound by let, let*,
;;; letrec, letrec*, named let, fluid-let, do, lambda, named-lambda and an
;;; internal define (and the parameters of the top-level define itself; not its
;;; name, which is the other lint's), with quote and quasiquote skipped --
;;; formulas are data.  Two DIFFERENT spellings with one folded name in one
;;; form is a finding.  Warn-only; run by `case-fold-define-lint!' on
;;; theorem-library/ and calculus/ files, so load.scm needs no new line; the
;;; roll-up prints with `report-case-fold-defines'.  No cheap trigger: a text
;;; test ("an upper-case letter near a binding keyword") fired on 466 of 505
;;; proof files, since formulas are upper case; every proof file is read.
(define *case-fold-local-collisions* '())   ; (file (form-name (folded sp ...) ...) ...)

;;; Keywords are compared by `memq' on the symbols as the NON-folding reader
;;; returns them: the tree spells them in lower case, and a string comparison
;;; per pair (the first draft) cost 55 s over the tree, mostly in allocation.
(define cfl--let-heads '(let let* letrec letrec* fluid-let))

(define (cfl--params p acc)                 ; symbols of a (possibly improper) list
  (cond ((symbol? p) (cons p acc))
        ((pair? p) (cfl--params (cdr p) (cfl--params (car p) acc)))
        (#t acc)))

(define (cfl--binders x top? acc)
  (if (not (pair? x))
      acc
      (let ((h (car x)))
        (cond
         ((memq h '(quote quasiquote)) acc)
         ((and (memq h cfl--let-heads) (pair? (cdr x)))
          (let* ((named (symbol? (cadr x)))
                 (bs    (if named (if (pair? (cddr x)) (caddr x) '()) (cadr x)))
                 (body  (if named (if (pair? (cddr x)) (cdddr x) '()) (cddr x)))
                 (acc   (if named (cons (cadr x) acc) acc))
                 (acc   (let loop ((bs bs) (acc acc))
                          (cond ((not (pair? bs)) acc)
                                ((pair? (car bs))
                                 (loop (cdr bs)
                                       (cfl--binders-list (cdar bs)
                                                          (cfl--params (caar bs) acc))))
                                (#t (loop (cdr bs) (cfl--params (car bs) acc)))))))
            (cfl--binders-list body acc)))
         ((and (eq? h 'do) (pair? (cdr x)) (list? (cadr x)))
          (cfl--binders-list (cddr x)
            (fold-left (lambda (a b) (if (pair? b) (cfl--params (car b) a) a)) acc (cadr x))))
         ((and (memq h '(lambda named-lambda)) (pair? (cdr x)))
          (cfl--binders-list (cddr x) (cfl--params (cadr x) acc)))
         ((and (eq? h 'define) (pair? (cdr x)))
          (let ((target (cadr x)))
            (cfl--binders-list
             (cddr x)
             (cond ((pair? target)             ; (define (f . args) ...), curried too
                    (let loop ((t target) (acc acc))
                      (if (pair? (car t))
                          (cfl--params (cdr t) (loop (car t) acc))
                          (cfl--params (cdr t) (if top? acc (cfl--params (car t) acc))))))
                   ((symbol? target) (if top? acc (cons target acc)))
                   (#t acc)))))
         (#t (cfl--binders-list x acc))))))

(define (cfl--binders-list l acc)
  (if (pair? l)
      (cfl--binders-list (cdr l) (cfl--binders (car l) #f acc))
      acc))

(define (cfl--form-name form)
  (let ((t (cfd--define-target form)))
    (or t "<top-level form>")))

(define (cfl--form-collisions form)
  (let ((seen (make-strong-eqv-hash-table)) (mixed? #f) (names '()))
    (for-each (lambda (b)
                (if (and (symbol? b) (not (hash-table-ref/default seen b #f)))
                    (let ((s (symbol->string b)))
                      (hash-table-set! seen b #t)
                      (if (not (string=? s (string-downcase s))) (set! mixed? #t))
                      (set! names (cons s names)))))
              (cfl--binders form #t '()))
    (if mixed? (cfd--collisions names) '())))

(define (case-fold-local-lint-text text)
  (let ((port (string->input-port text)))
        (parameterize ((param:reader-fold-case? #f))
          (let loop ((acc '()))
            (let ((f (read port)))
              (if (eof-object? f)
                  (reverse acc)
                  (loop (let ((cols (if (pair? f) (cfl--form-collisions f) '())))
                          (if (pair? cols) (cons (cons (cfl--form-name f) cols) acc) acc)))))))))

(define (case-fold-local-lint! file path)
  (let ((hits
         (and (file-exists? path)
              (call-with-current-continuation
                (lambda (k)
                  (with-exception-handler (lambda (e) (k '()))
                    (lambda () (case-fold-local-lint-text (cfd--slurp path)))))))))
    (when (pair? hits)
      (set! *case-fold-local-collisions*
            (cons (cons file hits) *case-fold-local-collisions*))
      (display ";VNB warning: case-fold lint: ") (display file)
      (display " binds two LOCAL names MIT Scheme reads as ONE:\n")
      (for-each (lambda (h)
                  (for-each (lambda (c)
                              (display ";              in ") (display (car h)) (display ": ")
                              (for-each (lambda (s) (display s) (display "  ")) (cdr c))
                              (display "->  ") (display (car c)) (newline))
                            (cdr h)))
                hits)
      (display ";              The inner binding silently SHADOWS (or replaces) the other.\n"))
    (if (pair? hits) hits '())))

(define (cfl--proof-file? file)
  (and (string? file)
       (or (string-prefix? "theorem-library/" file) (string-prefix? "calculus/" file))))

(define (case-fold-define-lint! file path)
  (if (cfl--proof-file? file) (case-fold-local-lint! file path))
  (let ((cols
         (and (file-exists? path)
              (call-with-current-continuation
                (lambda (k)
                  (with-exception-handler (lambda (e) (k '()))
                    (lambda ()
                      (let ((text (cfd--slurp path)))
                        (if (cfd--maybe-mixed? text)
                            (cfd--collisions (cfd--read-names text))
                            '())))))))))
    (when (pair? cols)
      (set! *case-fold-define-collisions*
            (cons (cons file cols) *case-fold-define-collisions*))
      (display ";VNB warning: case-fold lint: ") (display file)
      (display " has two top-level defines MIT Scheme reads as ONE name:\n")
      (for-each (lambda (c)
                  (display ";              ")
                  (for-each (lambda (s) (display s) (display "  ")) (cdr c))
                  (display "->  ") (display (car c)) (newline))
                cols)
      (display ";              The later definition silently REPLACES the earlier one.\n"))
    (if (pair? cols) cols '())))

(define (report-case-fold-defines)
  (if (null? *case-fold-define-collisions*)
      (display ";; case-fold lint: no file defines two names that fold together.\n")
      (begin
        (display ";VNB warning: case-fold lint: ")
        (display (length *case-fold-define-collisions*))
        (display " file(s) define two names that fold together:\n")
        (for-each (lambda (e)
                    (display ";              ") (display (car e)) (display ": ")
                    (for-each (lambda (c) (write (cdr c)) (display " ")) (cdr e))
                    (newline))
                  (reverse *case-fold-define-collisions*))))
  (if (null? *case-fold-local-collisions*)
      (display ";; case-fold lint: no proof file binds two local names that fold together.\n")
      (begin
        (display ";VNB warning: case-fold lint: ")
        (display (length *case-fold-local-collisions*))
        (display " proof file(s) bind two LOCAL names that fold together:\n")
        (for-each (lambda (e)
                    (display ";              ") (display (car e)) (display ": ")
                    (for-each (lambda (h) (display (car h)) (display " ") (write (map cdr (cdr h)))
                                (display " "))
                              (cdr e))
                    (newline))
                  (reverse *case-fold-local-collisions*))))
  *case-fold-define-collisions*)
