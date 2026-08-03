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
;;; fact cites a PSS theorem forward -- its FIRST arg is the theorem name (the
;;; rest are instantiation terms), so a forward-assembled proof (e.g.
;;; cauchy-subseq-proof) bills its cited supports honestly; crediting proven /
;;; definitional citations resolves to nothing, so only asserted leaves count.
(define *pd-citing-verbs* '(mac mac-h ta bc* fact))

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
(define *proof-citation-graph* (make-equal-hash-table))  ; proven name -> immediate citations

;;; debt(NAME): the set of asserted facts NAME ultimately rests on.
;;;
;;; A view-specialized companion (X-module-vector-ag, produced by def-functor)
;;; is stamped `definitional' because the TRANSPORT is definitional -- but its
;;; content is exactly X's, so its debt is X's debt.  Without this case, citing
;;; an asserted structure law through its companion reported an empty bill:
;;; `module-act-neg-one' would read trust:none while resting on the asserted
;;; abelian-group-inverse-unique.  (71 companions had an asserted source.)
(define (debt-of name)
  (let ((src (view-specialized-source name)))
    (if src
        (debt-of src)
        (case (provenance-of name)
          ((primitive definitional) '())
          ((proven) (hash-table-ref/default *proof-debt* name '()))
          (else (list name))))))    ; asserted (the bare default) -> leaf

;;; Compute and store the bill for the proof just closed under NAME, from the
;;; current *proof-script*.  Returns the bill.  Called by qed AFTER install
;;; (so NAME's own provenance is already 'proven and won't self-cite).
(define (record-proof-debt! name)
  (let ((cits (proof-citations *proof-script*)))
    ;; The BILL (below) is computed over the FULL citation list and is unchanged
    ;; by the filter here.  The cycle GRAPH, however, must exclude two kinds of
    ;; edge that are never a real proof dependency, or a well-founded induction
    ;; reads as a cycle:
    ;;   (a) the proof's OWN name -- a `mac'/`mac-h' of the theorem's own name is
    ;;       its induction hypothesis / its own predicate's definitional unfold,
    ;;       not a dependence of the theorem on itself;
    ;;   (b) a citation that is DEFINITIONAL at record time -- unfolding a
    ;;       definition (e.g. `mac 'SMITH-STAIRCASE' unfolds the PREDICATE, which
    ;;       shares the case-folded name of the later-proven THEOREM) adds no
    ;;       dependency; debt-of already scores it 0.
    ;; Dropping both is debt-neutral: debt-of(self) is the not-yet-stored '() and
    ;; debt-of(definitional) is '().  It can only remove false cycles, never hide
    ;; a real one (a genuine circular DEPENDENCY runs through proven citations,
    ;; which are kept).
    (hash-table-set! *proof-citation-graph* name
      (filter (lambda (c)
                (and (not (eq? c name))
                     (not (eq? (provenance-of c) 'definitional))))
              cits))
    (let loop ((cs cits) (bill '()))
      (if (null? cs)
          (begin (hash-table-set! *proof-debt* name bill) bill)
          (loop (cdr cs) (pd-union bill (debt-of (car cs))))))))

;;; --- circular-dependency detection -----------------------------------
;;; Bills (above) are FROZEN snapshots taken at qed time, so they go stale when
;;; an asserted leaf is later retired to proven -- they cannot be trusted to
;;; reveal a cycle.  This walks the LIVE citation graph instead.  Only proven
;;; theorems have outgoing edges; asserted / primitive / definitional are leaves.
(define (proof-citations-of name)
  (if (eq? (provenance-of name) 'proven)
      (hash-table-ref/default *proof-citation-graph* name '())
      ;; A non-proven node is a leaf UNLESS it declared (rests-on ...): those
      ;; edges make the asserted reference base a checkable DAG.  A proven node
      ;; ignores any rests-on -- its real proof citations are the truth.
      (rests-on-of name)))

;;; A path START -> ... -> START through proven-node citations, or #f.  `seen'
;;; is the current path's ancestors, so the walk always terminates.
(define (proof-cycle-from start)
  (let dfs ((node start) (path (list start)) (seen '()))
    (let loop ((cs (proof-citations-of node)))
      (cond
        ((null? cs) #f)
        ((eq? (car cs) start) (reverse (cons start path)))   ; back-edge to start
        ((memq (car cs) seen) (loop (cdr cs)))               ; ancestor already on path
        (else (or (dfs (car cs) (cons (car cs) path) (cons (car cs) seen))
                  (loop (cdr cs))))))))

;;; Every distinct dependency cycle among proven theorems, each as a name path
;;; n -> ... -> n.  Empty list = acyclic = every proof is genuinely grounded.
(define (proof-cycle-check)
  ;; Seed the DFS from every proven theorem AND every node that declared a
  ;; rests-on -- so a cycle living entirely in the ASSERTED base (A rests-on B,
  ;; B rests-on A, neither proven) is caught, not just cycles through proofs.
  (let loop ((names (append *proven-theorem-names* (rests-on-declared-names)))
             (covered '()) (cycles '()))
    (cond
      ((null? names) (reverse cycles))
      ((memq (car names) covered) (loop (cdr names) covered cycles))
      (else
       (let ((c (proof-cycle-from (car names))))
         (if c
             (loop (cdr names) (append c covered) (cons c cycles))
             (loop (cdr names) covered cycles)))))))

;;; --- trust level -----------------------------------------------------

;;; Warrant kinds ranked worst -> best for the ledger.  `none' = an asserted
;;; leaf with NO warrant recorded at all (scarier than a hand-wave: nothing was
;;; even claimed to justify it), prepended below the weakest real kind.
;;;
;;; The real kinds follow *warrant-kinds* (macetes.scm) IN ORDER -- which is the
;;; order the manual documents (ch-classification.tex, "weakest to strongest").
;;; This file used to invent its own order with `well-known' and `informal'
;;; swapped, and a comment calling *warrant-kinds* "not a ranking".  It is a
;;; ranking, and the swap was a bug: `informal' means a rigorous paper-proof
;;; exists (just not mechanised), which is STRONGER than `well-known' (a textbook
;;; fact asserted with no argument at all).  The disagreement flipped the
;;; reported tier of 13 theorems.  Fixed 2026-07-10; derived from *warrant-kinds*
;;; now so the two can never drift again.
(define *pd-trust-order* (cons 'none *warrant-kinds*))

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

;;; The glossary that heads PROOF-DEBT.md and is linked from THEOREMS.md.  One
;;; copy of the vocabulary, so a reader of any theorem-listing surface can
;;; decode `proven modulo {...} [trust: ...]' without reading the source.
(define (pd--legend)
  (display "## Reading an entry\n\n")
  (display "A proof's **bill** is the set of `asserted` facts it ultimately\n")
  (display "leans on -- resolved transitively: a cited *proven* lemma\n")
  (display "contributes its own bill, a *primitive* axiom or *definitional*\n")
  (display "fact contributes nothing, and an *asserted* fact contributes\n")
  (display "itself.  Each such fact is a **leaf** of the bill.\n\n")
  (display "- **`proven modulo 0`** (an *empty bill*) -- the proof rests only\n")
  (display "  on the trusted base (the fixed primitive axioms, the kernel\n")
  (display "  inference rules, and definitions).  Nothing asserted stands\n")
  (display "  between it and the kernel; this is the strongest thing a proof\n")
  (display "  can report, and it carries **no** trust tier.\n")
  (display "- **`proven modulo {a, b, ...}`** -- the proof is unconditional\n")
  (display "  *given* a, b, ...  Discharging every leaf (proving it, or making\n")
  (display "  it a definition) would collapse the bill to 0.\n\n")
  (display "The **trust tier** `[trust: K]` of a non-empty bill is the warrant\n")
  (display "of its **weakest** leaf -- one shaky leaf caps the whole proof.\n")
  (display "Tiers, weakest to strongest (from `*warrant-kinds*`; see the\n")
  (display "manual, ch. Classification):\n\n")
  (display "| tier | the weakest leaf is... |\n")
  (display "|------|------------------------|\n")
  (display "| **`none`** | asserted with **no warrant at all** -- a backlog item, not a category |\n")
  (display "| `hand-wave` | a heuristic / plausibility argument, not rigorous |\n")
  (display "| `well-known` | a standard textbook fact, asserted without argument |\n")
  (display "| `reference` | cites a specific named source |\n")
  (display "| `informal` | a rigorous paper-proof exists, just not mechanised in VNB |\n")
  (display "| `proof` | a machine-checked VNB proof exists |\n\n")
  (display "So `[trust: none]` is the **weakest** report (some leaf justifies\n")
  (display "nothing), and `modulo 0` -- no tier -- is the strongest.\n\n"))

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

;;; --- keystones: the ranking, as a VALUE ---------------------------------
;;;
;;; The reverse index below has always computed this and always buried it -- at
;;; line ~6000 of a 559 KB PROOF-DEBT.md that nobody opens.  The ranking IS the
;;; worklist: an asserted leaf cited by 63 bills is worth sixty-three times what
;;; a leaf cited by one is, and discharging `ord-well-ordered' (2026-08-03) moved
;;; 16 bills for an afternoon's work on exactly that basis.  So compute it
;;; separately and let the load print the head of it.
;;;
;;; Returns ((leaf count warrant-kind) ...), most-cited first.
(define (debt-keystones)
  (let ((rev (make-equal-hash-table)))
    (hash-table-walk *proof-debt*
      (lambda (p bill)
        (for-each (lambda (leaf)
                    (hash-table-set! rev leaf
                      (cons p (hash-table-ref/default rev leaf '()))))
                  bill)))
    (sort (map (lambda (leaf)
                 (let ((w (warrant-of leaf)))
                   (list leaf
                         (length (hash-table-ref/default rev leaf '()))
                         (if w (car w) 'NONE))))
               (hash-table-keys rev))
          (lambda (a b)
            (if (= (cadr a) (cadr b))
                (string<? (symbol->string (car a)) (symbol->string (car b)))
                (> (cadr a) (cadr b)))))))

;;; Print the head of the ranking.  Wired into load.scm beside the other
;;; end-of-load reports; (debt-keystones) at the REPL gives the whole list.
(define (report-keystones #!optional n)
  (let ((n (if (default-object? n) 15 n))
        (ks (debt-keystones)))
    (display ";; debt keystones -- the asserted facts the most proofs lean on\n")
    (display ";;   (discharge one and every bill below it improves; full list in\n")
    (display ";;    reference/PROOF-DEBT.md, or (debt-keystones) for the data)\n")
    (let loop ((ks ks) (i 0))
      (when (and (pair? ks) (< i n))
        (let ((e (car ks)))
          (display ";;   ") (display (cadr e))
          (display (if (< (cadr e) 10) "   " "  "))
          (display (car e))
          (display "  [warrant: ") (display (caddr e)) (display "]")
          (newline))
        (loop (cdr ks) (+ i 1))))))

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
        (display "to the `asserted` facts listed as its outstanding base.\n\n")
        (pd--legend)
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
