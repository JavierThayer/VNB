;;; proof-debt.scm -- the warrant / proof-debt ledger.
;;;
;;; When a proof is installed with (qed NAME), the kernel certifies it relative
;;; to whatever it cited.  But many citations are themselves `asserted' facts
;;; (PSS supports with a warrant, or bare axioms) rather than machine-checked
;;; theorems.  This module computes, for each proven theorem, the SET of
;;; asserted facts it ULTIMATELY rests on -- its "bill" -- so a finished proof
;;; can report `proven modulo {a, b, c}' instead of pretending it is
;;; unconditional.
;;;
;;; Core object -- debt(NAME), a SET (not a multiset, not a path):
;;;   provenance primitive / definitional -> {}           (trusted base)
;;;   provenance asserted                 -> { NAME }      (a debt leaf: rests
;;;                                                          on itself)
;;;   provenance proven                   -> debt(c) unioned over its citations
;;;                                          (inherited transitively; stored)
;;; Computed once at qed from the just-finished *proof-script* and memoized in
;;; *proof-debt*, so each qed is a single union over its directly-cited bills --
;;; no DAG re-walk.  A proven theorem cited by a later proof contributes its
;;; STORED bill, so debt resolves THROUGH proven lemmas down to asserted leaves.
;;;
;;; Citation source: *proof-script* (interactive.scm), the flat (cmd . args)
;;; log qed already saves.  We credit the verbs that carry a THEOREM NAME --
;;; `mac', `ta', `bc*'.  `bc', `subst' and `cut' carry a raw formula, not a
;;; name, so they are not credited (accepted gap; see the spec).  The
;;; deduction graph's `rule' slot holds only the primitive step (backchain /
;;; cut / eq-subst), never the cited lemma -- so we use the script, not the
;;; graph.

;;; --- small set helpers (avoid SRFI-1 dependency) ---------------------

(define (pd-uniq lst)
  ;; dedup, preserving first-seen order
  (let loop ((l lst) (seen '()))
    (cond ((null? l) (reverse seen))
          ((memq (car l) seen) (loop (cdr l) seen))
          (else (loop (cdr l) (cons (car l) seen))))))

(define (pd-union a b)
  (pd-uniq (append a b)))

;;; --- citation scan ---------------------------------------------------

;;; Proof-script verbs whose first argument is a cited theorem/axiom/macete
;;; name.  (bc / subst / cut take raw formulas; ass / di / rfl cite nothing.)
;;; mac-h cites the equivalence it applies to a hypothesis -- its FIRST arg is
;;; the macete/theorem name (the second is the assumption), so it is credited
;;; exactly like mac.  Omitting it would let a hypothesis-side use of a
;;; warranted support (e.g. preimage-complement) escape the debt ledger.
(define *pd-citing-verbs* '(mac mac-h ta bc*))

;;; The set of names a proof script directly cites.  A compound-macete arg
;;; (e.g. (mac '(series m1 m2))) is NOT a bare name; we log it as an
;;; uncredited citation rather than silently dropping or mis-crediting it.
(define (proof-citations script)
  (let loop ((s script) (acc '()))
    (if (null? s)
        (pd-uniq (reverse acc))
        (let* ((entry (car s)) (verb (car entry)) (args (cdr entry)))
          (cond
            ((not (memq verb *pd-citing-verbs*)) (loop (cdr s) acc))
            ((and (pair? args) (symbol? (car args)))
             (loop (cdr s) (cons (car args) acc)))
            ((pair? args)
             (display ";; proof-debt: uncredited compound ")
             (display verb) (display " citation ")
             (write (car args)) (newline)
             (loop (cdr s) acc))
            (else (loop (cdr s) acc)))))))

;;; --- the bill --------------------------------------------------------

(define *proof-debt* (make-equal-hash-table))   ; proven name -> bill (name list)

;;; debt(NAME): the set of asserted facts NAME ultimately rests on.
(define (debt-of name)
  (case (provenance-of name)
    ((primitive definitional) '())
    ((proven) (hash-table-ref/default *proof-debt* name '()))
    (else (list name))))            ; asserted (the bare default) -> leaf

;;; Compute and store the bill for the proof just closed under NAME, from the
;;; current *proof-script*.  Returns the bill.  Called by qed AFTER install
;;; (so NAME's own provenance is already 'proven and won't self-cite).
(define (record-proof-debt! name)
  (let loop ((cs (proof-citations *proof-script*)) (bill '()))
    (if (null? cs)
        (begin (hash-table-set! *proof-debt* name bill) bill)
        (loop (cdr cs) (pd-union bill (debt-of (car cs)))))))

;;; --- trust level -----------------------------------------------------

;;; Warrant kinds ranked worst -> best for the ledger.  `none' = an asserted
;;; leaf with NO warrant recorded at all (scarier than a hand-wave: nothing
;;; was even claimed to justify it).  NB: this ranking is the ledger's own
;;; quality order; *warrant-kinds* (macetes.scm) is just an unordered
;;; enumeration and is NOT a ranking.
(define *pd-trust-order* '(none hand-wave informal reference well-known proof))

(define (pd-rank kind)
  (let loop ((o *pd-trust-order*) (i 0))
    (cond ((null? o) 0)
          ((eq? (car o) kind) i)
          (else (loop (cdr o) (+ i 1))))))

(define (pd-leaf-trust name)
  (let ((w (warrant-of name)))
    (if w (car w) 'none)))

;;; Trust level of a bill = the WORST warrant kind over its leaves.
;;; An empty bill (modulo 0) is fully trusted -> 'proof.
(define (debt-trust-level bill)
  (if (null? bill)
      'proof
      (let loop ((b bill) (worst 'proof))
        (if (null? b)
            worst
            (let ((k (pd-leaf-trust (car b))))
              (loop (cdr b) (if (< (pd-rank k) (pd-rank worst)) k worst)))))))

;;; --- surfaces --------------------------------------------------------

(define (pd-display-set names)
  (display "{")
  (let loop ((n names) (first #t))
    (unless (null? n)
      (unless first (display ", "))
      (display (car n))
      (loop (cdr n) #f)))
  (display "}"))

;;; (1) inline at qed: always print the modulo line.
(define (announce-proof-debt name bill)
  (display ";; qed ") (display name) (display ": proven modulo ")
  (if (null? bill) (display "0") (pd-display-set bill))
  (unless (null? bill)
    (display "  [trust: ") (display (debt-trust-level bill)) (display "]"))
  (newline))

;;; (2) REPL query.
(define (debt-of-proof name)
  (let ((bill (debt-of name)))
    (display name) (display ": ")
    (case (provenance-of name)
      ((primitive definitional)
       (display "trusted (") (display (provenance-of name)) (display ") -- modulo 0"))
      ((proven)
       (display "proven modulo ")
       (if (null? bill) (display "0") (pd-display-set bill))
       (unless (null? bill)
         (display "  [trust: ") (display (debt-trust-level bill)) (display "]")))
      (else
       (display "asserted leaf -- rests on itself")
       (let ((w (warrant-of name)))
         (display "  [warrant: ") (display (if w (car w) 'NONE)) (display "]"))))
    (newline)
    bill))

;;; (2a) CERTIFICATION STAMP.  The VNB test (vnb-test: a periodic full run of
;;; every proof script in sequence) records, per proven theorem, the date its
;;; proof last re-ran to QED.  An at-load proof is certified by the load that
;;; runs it; a standalone proof script (e.g. calculus/*) is certified only when
;;; the VNB test runs it.  Stamps live in reference/certification.scm (a list of
;;; (certify! 'name "date") forms) which load.scm loads if present -- so (status)
;;; can show "certified <date>": the proof claim with a date behind it, not just
;;; the word "proven".  PSS members are NEVER certified here (excused by design).
(define *certifications* (make-equal-hash-table))   ; name -> date string
(define (certify! name date) (hash-table-set! *certifications* name date))
(define (certification-of name) (hash-table-ref/default *certifications* name #f))

;;; (2b) STATUS: one command, every axis.  Answers "what IS this result, and
;;;      is its proof complete?" without the user having to remember which of
;;;      provenance-of / warrant-of / debt-of-proof / *support-theorem-names*
;;;      to call.  "complete" is not a separate flag: a result is as complete
;;;      as its provenance + modulo line say it is.  The legend:
;;;        primitive    -- a kernel axiom; trusted by fiat, no proof expected.
;;;        definitional -- introduced by a definition; true by construction.
;;;        asserted     -- ASSUMED, not proved.  Its own justification is only
;;;                        the warrant (if any).  This is the "not complete" case.
;;;        proven       -- closed by qed.  "modulo 0" = unconditional relative
;;;                        to the trusted base (primitive + definitional); i.e.
;;;                        as complete as anything gets here.  "modulo {..}" =
;;;                        proven, but still leaning on those asserted leaves.
(define (status name)
  (let ((prov (provenance-of name))
        (pss? (memq name *support-theorem-names*))
        (w    (warrant-of name)))
    (display name) (display ":") (newline)
    (display "  provenance : ") (display prov)
    (case prov
      ((primitive)    (display "   (kernel axiom -- trusted by fiat)"))
      ((definitional) (display "   (true by construction)"))
      ((proven)       (display "   (closed by qed)"))
      (else           (display "   (ASSUMED, not proved)")))
    (newline)
    (display "  PSS        : ") (display (if pss? "yes (curated support theorem)" "no"))
    (newline)
    (display "  warrant    : ")
    (if w (begin (display (car w)) (display " -- ") (display (cdr w)))
          (display "NONE"))
    (newline)
    (let ((cert (certification-of name)))
      (display "  completion : ")
      (cond
        ((memq prov '(primitive definitional))
         (display "n/a -- trusted base, modulo 0"))
        ((eq? prov 'proven)
         (let ((bill (debt-of name)))
           (if (null? bill)
               (display "COMPLETE -- proven modulo 0 (unconditional)")
               (begin (display "proven modulo ") (pd-display-set bill)
                      (display "  [trust: ") (display (debt-trust-level bill))
                      (display "]")))))
        ;; asserted in the catalog (cached so the everyday load need not re-run
        ;; it) but its proof SCRIPT ran to QED in the last VNB test -- genuinely
        ;; proven, just not re-proved at load.  Certification makes this honest.
        (cert (display "PROVEN by a certified script (cached as asserted for load speed)"))
        (w    (display "asserted on a warrant -- no machine proof"))
        (else (display "INCOMPLETE -- asserted; rests on itself")))
      (newline)
      ;; A "certified" line wherever there is a proof claim to vouch for:
      ;; proven provenance, OR a certification stamp on an asserted entry.
      (when (or (eq? prov 'proven) cert)
        (display "  certified  : ")
        (if cert (begin (display "VNB test ") (display cert))
                 (display "NOT since last VNB test run -- proof unverified"))
        (newline)))))

;;; (3) PROOF-DEBT.md: forward map (each proven theorem -> outstanding base)
;;;     AND reverse keystone index (each asserted leaf -> proven dependents,
;;;     "discharge X -> unlocks N").
(define (proof-debt-ledger)
  (let* ((path  (string-append *reference-dir* "PROOF-DEBT.md"))
         (proven (sort (hash-table-keys *proof-debt*)
                       (lambda (a b) (string<? (symbol->string a)
                                               (symbol->string b)))))
         ;; reverse index: leaf -> list of proven dependents
         (rev   (make-equal-hash-table)))
    (for-each
      (lambda (p)
        (for-each
          (lambda (leaf)
            (hash-table-set! rev leaf
              (cons p (hash-table-ref/default rev leaf '()))))
          (hash-table-ref/default *proof-debt* p '())))
      proven)
    (with-output-to-file path
      (lambda ()
        (display "# Proof Debt Ledger\n\n")
        (display "Auto-generated by `(proof-debt-ledger)`.  ")
        (display (length proven))
        (display " proven theorem(s); each is certified by the kernel relative\n")
        (display "to the `asserted` facts listed as its outstanding base.  ")
        (display "`modulo 0` = unconditional relative to the trusted base ")
        (display "(primitive + definitional).\n\n")
        ;; --- forward ---
        (display "## Forward: proven theorem -> outstanding base\n\n")
        (if (null? proven)
            (display "_No proofs installed via `qed` yet._\n\n")
            (for-each
              (lambda (p)
                (let ((bill (hash-table-ref/default *proof-debt* p '())))
                  (display "### ") (display p)
                  (display "  *(trust: ") (display (debt-trust-level bill))
                  (display ")*\n\n")
                  (if (null? bill)
                      (display "proven **modulo 0** -- unconditional.\n\n")
                      (begin
                        (display "proven modulo:\n\n")
                        (for-each
                          (lambda (leaf)
                            (let ((w (warrant-of leaf)))
                              (display "- `") (display leaf) (display "` -- ")
                              (if w
                                  (begin (display "*warrant ") (display (car w))
                                         (display ":* ") (display (cdr w)))
                                  (display "**NO WARRANT**"))
                              (newline)))
                          bill)
                        (newline)))))
              proven))
        ;; --- reverse keystone index ---
        (display "## Reverse: asserted leaf -> proven dependents (keystones first)\n\n")
        (display "Discharging a high-count leaf to a real proof unlocks the most.\n\n")
        (let ((leaves (sort (hash-table-keys rev)
                            (lambda (a b)
                              (let ((na (length (hash-table-ref/default rev a '())))
                                    (nb (length (hash-table-ref/default rev b '()))))
                                (if (= na nb)
                                    (string<? (symbol->string a) (symbol->string b))
                                    (> na nb)))))))
          (if (null? leaves)
              (display "_No outstanding asserted leaves._\n\n")
              (for-each
                (lambda (leaf)
                  (let* ((deps (sort (hash-table-ref/default rev leaf '())
                                     (lambda (a b) (string<? (symbol->string a)
                                                             (symbol->string b)))))
                         (w    (warrant-of leaf)))
                    (display "- `") (display leaf) (display "` (")
                    (display (length deps)) (display ") ")
                    (display "[warrant: ") (display (if w (car w) 'NONE))
                    (display "] -> ")
                    (let loop ((d deps) (first #t))
                      (unless (null? d)
                        (unless first (display ", "))
                        (display (car d))
                        (loop (cdr d) #f)))
                    (newline)))
                leaves)))))
    path))

;;; --- (4) status audit ------------------------------------------------
;;; Survey the WHOLE catalog on the status axes and surface the hygiene
;;; questions behind "what is, and what SHOULD be, the status of each":
;;;   - provenance census (primitive/definitional/asserted/proven);
;;;   - the asserted pile broken down by warrant quality -- `none' is the
;;;     scary tier (assumed AND unjustified);
;;;     NB asserted is NOT itself a defect in library-build phase; an
;;;     asserted leaf with NO warrant is the thing to chase;
;;;   - PSS supports that are asserted-with-no-warrant (rewrite rules the
;;;     prover trusts yet nothing justifies);
;;;   - proven theorems still modulo a non-empty base (the keystones).
;;; Drift (a result we BELIEVE is proven but stored asserted) is not
;;; machine-detectable here -- it shows up as an asserted-trust-none entry
;;; whose name reads like a theorem; eyeball the list for those.
(define (sa--by name)            ; classify into a coarse bucket symbol
  (let ((p (provenance-of name)))
    (case p
      ((primitive definitional proven) p)
      (else 'asserted))))

(define (status-audit)
  (let* ((all   (hash-table-keys *theorem-table*))
         (prim  (filter (lambda (n) (eq? (sa--by n) 'primitive)) all))
         (defn  (filter (lambda (n) (eq? (sa--by n) 'definitional)) all))
         (prov  (filter (lambda (n) (eq? (sa--by n) 'proven)) all))
         (asrt  (filter (lambda (n) (eq? (sa--by n) 'asserted)) all))
         ;; asserted, bucketed by warrant tier (pd-leaf-trust -> kind or 'none)
         (tiers (map (lambda (k)
                       (cons k (filter (lambda (n) (eq? (pd-leaf-trust n) k)) asrt)))
                     *pd-trust-order*))
         (none  (cdr (assq 'none tiers)))
         ;; PSS supports that are unjustified asserted leaves
         (pss-bad (filter (lambda (n) (and (memq n *support-theorem-names*)
                                           (memq n none)))
                          all))
         ;; asserted facts carrying a 'proof warrant: the warrant claims a
         ;; machine proof, so provenance OUGHT to be `proven'.  (The load-time
         ;; invariant misses these when they are PSS; we don't.)
         (claims-proof (filter (lambda (n)
                                 (let ((w (warrant-of n)))
                                   (and w (eq? (car w) 'proof))))
                               asrt))
         ;; proven theorems still resting on a non-empty base
         (keystone (filter (lambda (n) (not (null? (debt-of n)))) prov))
         (sym<  (lambda (a b) (string<? (symbol->string a) (symbol->string b))))
         (path  (string-append *reference-dir* "STATUS-AUDIT.md")))
    ;; --- REPL summary ---
    (display ";; status-audit: ") (display (length all)) (display " results -- ")
    (display (length prim)) (display " primitive, ")
    (display (length defn)) (display " definitional, ")
    (display (length prov)) (display " proven, ")
    (display (length asrt)) (display " asserted\n")
    (display ";;   asserted by warrant: ")
    (for-each (lambda (t) (unless (null? (cdr t))
                            (display (length (cdr t))) (display " ")
                            (display (car t)) (display "  ")))
              tiers)
    (newline)
    (display ";;   FLAGS: ") (display (length none))
    (display " asserted-no-warrant, ")
    (display (length pss-bad)) (display " PSS-unjustified, ")
    (display (length claims-proof)) (display " asserted-claims-proof, ")
    (display (length keystone)) (display " proven-modulo-nonzero\n")
    (display ";;   full report -> ") (display path) (newline)
    ;; --- the report ---
    (with-output-to-file path
      (lambda ()
        (display "# Status Audit\n\n")
        (display "Auto-generated by `(status-audit)`.  Census of every named ")
        (display "result on the status axes, and the hygiene flags behind ")
        (display "\"what *should* the status be\".\n\n")
        (display "Per-result detail: `(status 'name)` at the REPL.\n\n")
        (display "## Census\n\n")
        (display "| provenance | count | meaning |\n|---|---|---|\n")
        (display "| primitive | ") (display (length prim))
        (display " | kernel axiom, trusted by fiat |\n")
        (display "| definitional | ") (display (length defn))
        (display " | true by construction |\n")
        (display "| proven | ") (display (length prov))
        (display " | closed by `qed` |\n")
        (display "| asserted | ") (display (length asrt))
        (display " | assumed, not proved |\n\n")
        (display "## Asserted, by warrant tier\n\n")
        (display "Worst -> best.  `none` = assumed *and* unjustified.\n\n")
        (display "| tier | count |\n|---|---|\n")
        (for-each (lambda (t)
                    (display "| ") (display (car t)) (display " | ")
                    (display (length (cdr t))) (display " |\n"))
                  tiers)
        (newline)
        (display "## FLAG: asserted with no warrant (")
        (display (length none)) (display ")\n\n")
        (display "Each should get a `(warrant! ...)`, be proved, or be ")
        (display "retired if a definition now subsumes it.  Scan for names ")
        (display "that read like *theorems* -- those are status drift.\n\n")
        (for-each (lambda (n) (display "- `") (display n) (display "`\n"))
                  (sort none sym<))
        (newline)
        (display "## FLAG: PSS supports that are unjustified (")
        (display (length pss-bad)) (display ")\n\n")
        (display "Curated rewrite rules the prover trusts, yet nothing ")
        (display "justifies them.  Highest-priority warrants.\n\n")
        (if (null? pss-bad)
            (display "_None._\n\n")
            (for-each (lambda (n) (display "- `") (display n) (display "`\n"))
                      (sort pss-bad sym<)))
        (newline)
        (display "## FLAG: asserted, but warrant claims a proof (")
        (display (length claims-proof)) (display ")\n\n")
        (display "The `proof` warrant says machine-proven, so provenance ")
        (display "ought to be `proven` (or the warrant downgraded).  Drift.\n\n")
        (if (null? claims-proof)
            (display "_None._\n\n")
            (for-each (lambda (n) (display "- `") (display n) (display "`\n"))
                      (sort claims-proof sym<)))
        (newline)
        (display "## FLAG: proven, modulo a non-empty base (")
        (display (length keystone)) (display ")\n\n")
        (display "Proven by `qed` but still leaning on asserted leaves.  ")
        (display "See `PROOF-DEBT.md` for each bill.\n\n")
        (for-each (lambda (n)
                    (display "- `") (display n) (display "` modulo ")
                    (let ((bill (debt-of n)))
                      (let loop ((b bill) (first #t))
                        (unless (null? b)
                          (unless first (display ", "))
                          (display (car b)) (loop (cdr b) #f))))
                    (display "  *(trust: ") (display (debt-trust-level (debt-of n)))
                    (display ")*\n"))
                  (sort keystone sym<))))
    path))
