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

;;; -----------------------------------------------------------------------
;;; THE ORACLE INVENTORY  (2026-08-04)
;;;
;;; A bill answers "which ASSERTED FACTS does this proof rest on".  It says
;;; nothing about the other half of the trust surface: the DECISION PROCEDURES.
;;; `ineq' (Fourier-Motzkin/Farkas), `arith', `crs'/`rs'/`simp' (ring
;;; normalisation) and `sos' are trusted CODE -- sound on their domain, but
;;; believed rather than checked, and they leave no leaf.  So
;;;
;;;     ;; qed rr-zero-lt-one: proven modulo 0
;;;
;;; read "unconditional", when what it means is "unconditional given that the
;;; Farkas engine is right" -- that proof IS one `ineq' call and nothing else.
;;; The bill now carries the oracles too, transitively, exactly as the debt is
;;; carried: a proof that cites a theorem closed by `ineq' inherits `ineq'.
;;;
;;; The verbs are listed HERE rather than read from *tactic-kind* (tactics-help)
;;; because that file loads near the END of *vnb-files*, long after the first
;;; theorem-library proof calls record-proof-debt!.  load.scm compares the two
;;; lists at the end of the load and complains if they have drifted -- the same
;;; arrangement as kernel-rules-audit.
(define *pd-oracle-verbs* '(arith rs crs simp ineq sos))

;;; --- names that are not facts of their own ---------------------------
;;;
;;; Two kinds of name in the theorem table stand for a fact stated ELSEWHERE:
;;;   * a view-specialized companion (X-module-vector-ag, def-functor), whose
;;;     transport is definitional but whose content is X's;
;;;   * an auto-minted -rev companion (X-rev, install-theorem!), which is X
;;;     with a symmetric core flipped -- the same fact, backwards.
;;; Neither carries its own proof, so neither carries its own debt, its own
;;; oracles or its own citations: all three resolve to the source.  Both tables
;;; are written where the companion's NAME is chosen, so nothing here keys on a
;;; name SHAPE.
(define (pd-source-of name)
  (or (view-specialized-source name)
      (rev-companion-source name)))

(define *proof-oracles* (make-equal-hash-table))   ; proven name -> (verb ...)

;;; The oracles a script invokes DIRECTLY.
(define (script-oracles script)
  (pd-uniq (filter (lambda (v) (memq v *pd-oracle-verbs*)) (map car script))))

;;; The oracles NAME rests on, transitively.  Mirrors debt-of: an asserted or
;;; primitive leaf invokes nothing, a proven citation contributes its own set.
(define (oracles-of name)
  (let ((src (pd-source-of name)))
    (if src
        (oracles-of src)
        (if (eq? (provenance-of name) 'proven)
            (hash-table-ref/default *proof-oracles* name '())
            '()))))

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
  (let ((src (pd-source-of name)))
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
    ;; the ORACLE inventory, transitively -- own calls plus every citation's
    (hash-table-set! *proof-oracles* name
      (let loop ((cs cits) (ors (script-oracles *proof-script*)))
        (if (null? cs)
            ors
            (loop (cdr cs) (pd-union ors (oracles-of (car cs)))))))
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
  (let ((src (pd-source-of name)))
   (if src
      ;; A companion has no proof of its own; its dependencies are its source's.
      ;; Note this adds no edge INTO the source, so a proof that cites both a
      ;; theorem and its own -rev companion gains no self-loop -- the companion
      ;; simply inherits the same out-edges the forward already has.
      (proof-citations-of src)
   (if (eq? (provenance-of name) 'proven)
      (hash-table-ref/default *proof-citation-graph* name '())
      ;; A non-proven node is a leaf UNLESS it declared (rests-on ...): those
      ;; edges make the asserted reference base a checkable DAG.  A proven node
      ;; ignores any rests-on -- its real proof citations are the truth.
      (rests-on-of name)))))

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

;;; --- strongly-connected components over the citation graph -----------
;;;
;;; `start' lies on a cycle IFF `start' is in a NONTRIVIAL strongly-connected
;;; component, or cites itself.  So Tarjan decides exactly the predicate
;;; `proof-cycle-from' decides -- the same nodes flagged, no more and no fewer
;;; -- in O(V+E) instead of O(number of distinct paths).
;;;
;;; WHY, AND WHY IT IS NOT A WEAKENING OF THE GATE.  The version this replaces
;;; called `proof-cycle-from' once per name over ~930 proven names, and that
;;; DFS carries the current PATH's ancestors as `seen' rather than a visited
;;; set, so every node is re-explored once per distinct path reaching it.  The
;;; ACYCLIC case -- the normal one -- was the worst case: `covered' grew only
;;; when a cycle was FOUND, so a clean library got a full from-scratch DFS per
;;; name.  Measured 2026-08-27: 510 s of a 638 s library load, 80% of it, and
;;; the reason the full suite went from 3m12s to ~34 min on a 10% larger tree
;;; (the log/exp arc added DEPTH, and path count grows combinatorially in it).
;;;
;;; A visited-memo bolted onto that walk WOULD have been unsound: it asks "does
;;; START lie on a cycle" per start and deliberately ignores back-edges to
;;; non-START ancestors (proof-cycle-from, line 3 of the loop), so a node
;;; cleared under one start could suppress a cycle found under another.  Tarjan
;;; sidesteps that trap by not asking a per-start question at all -- it
;;; computes the components once and reads cycle-membership off them.
;;;
;;; `proof-cycle-from' is UNCHANGED and remains the single-start query (the
;;; suite uses it directly).  It is simply no longer what the gate calls.

(define (pd-sccs roots)
  (let ((index    (make-equal-hash-table))
        (lowlink  (make-equal-hash-table))
        (on-stack (make-equal-hash-table))
        (counter  0)
        (stack    '())
        (comps    '()))
    (define (idx n) (hash-table-ref/default index   n #f))
    (define (low n) (hash-table-ref/default lowlink n 0))
    (define (visit v)
      (hash-table-set! index   v counter)
      (hash-table-set! lowlink v counter)
      (set! counter (+ counter 1))
      (set! stack (cons v stack))
      (hash-table-set! on-stack v #t)
      (for-each
       (lambda (w)
         (cond ((not (idx w))
                (visit w)
                (hash-table-set! lowlink v (min (low v) (low w))))
               ((hash-table-ref/default on-stack w #f)
                (hash-table-set! lowlink v (min (low v) (idx w))))))
       (proof-citations-of v))
      (if (= (low v) (idx v))
          (let pop ((comp '()))
            (let ((w (car stack)))
              (set! stack (cdr stack))
              (hash-table-set! on-stack w #f)
              (if (eq? w v)
                  (set! comps (cons (cons w comp) comps))
                  (pop (cons w comp)))))))
    (for-each (lambda (r) (if (not (idx r)) (visit r))) roots)
    comps))

;;; A cycle v -> ... -> v with every intermediate node inside COMP.  COMP is
;;; strongly connected, so such a path exists, and the search is bounded by the
;;; component -- tiny even when the whole graph is not.
(define (pd-cycle-in comp v)
  (let dfs ((node v) (path (list v)) (seen '()))
    (let loop ((cs (proof-citations-of node)))
      (cond
        ((null? cs) #f)
        ((eq? (car cs) v) (reverse (cons v path)))
        ((or (not (memq (car cs) comp)) (memq (car cs) seen)) (loop (cdr cs)))
        (else (or (dfs (car cs) (cons (car cs) path) (cons (car cs) seen))
                  (loop (cdr cs))))))))

;;; Every distinct dependency cycle among proven theorems, each as a name path
;;; n -> ... -> n.  Empty list = acyclic = every proof is genuinely grounded.
;;;
;;; Seeded from every proven theorem AND every node that declared a rests-on --
;;; so a cycle living entirely in the ASSERTED base (A rests-on B, B rests-on A,
;;; neither proven) is caught, not just cycles through proofs.  Every node with
;;; an out-edge is one or the other, so every cycle carries a seed on it and no
;;; cycle can hide from the sweep.
(define (proof-cycle-check)
  (let loop ((comps (pd-sccs (append *proven-theorem-names*
                                     (rests-on-declared-names))))
             (cycles '()))
    (if (null? comps)
        (reverse cycles)
        (let* ((comp (car comps))
               (cyc  (cond ((pair? (cdr comp)) (pd-cycle-in comp (car comp)))
                           ((memq (car comp) (proof-citations-of (car comp)))
                            (list (car comp) (car comp)))
                           (else #f))))
          (loop (cdr comps) (if cyc (cons cyc cycles) cycles))))))

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
  ;; ... and the trusted CODE it leans on, which leaves no leaf in the bill.
  (let ((ors (hash-table-ref/default *proof-oracles* name '())))
    (unless (null? ors)
      (display "  [oracles: ")
      (let loop ((o ors) (first #t))
        (unless (null? o)
          (unless first (display " "))
          (display (car o))
          (loop (cdr o) #f)))
      (display "]")))
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
    (let ((ors (oracles-of name)))
      (unless (null? ors)
        (display "\n  trusted code: ") (write ors)
        (display "  -- decision procedures the proof leans on; they leave no")
        (display "\n                leaf in the bill, so `modulo 0' means")
        (display " `modulo 0 AND these'")))
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
                  (let ((ors (hash-table-ref/default *proof-oracles* p '())))
                    (unless (null? ors)
                      (display "*trusted code: ")
                      (let lp ((o ors) (first #t))
                        (unless (null? o)
                          (unless first (display ", "))
                          (display "`") (display (car o)) (display "`")
                          (lp (cdr o) #f)))
                      (display "* -- decision procedures, sound on their domain")
                      (display " but believed rather than checked; they leave no leaf below.\n\n")))
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


;;; --- (3b) DEBT-BUNDLE.md: the pile, raked into heaps -------------------
;;;
;;; PROOF-DEBT.md is a FLAT list -- every proven theorem with the set of
;;; asserted leaves under it, plus a reverse index ranked by citation count.
;;; Two things it cannot tell you, and this file is those two things.
;;;
;;; WHAT TO PROVE NEXT.  Citation count is the WRONG ranking and the tree has
;;; the scar to prove it: `nary-neg-1' headed `debt-keystones' with 14
;;; dependents and was worth NOTHING on its own, because every bill naming it
;;; also named `nary-minus-2'.  The tier of a bill is its WORST leaf, so
;;; discharging a leaf buys nothing until it is the LAST one in the bills that
;;; name it.  The ranking below is therefore a GREEDY WHAT-IF: repeatedly take
;;; the leaf that would empty the most bills outright, remove it from every
;;; bill, and go again.  It answers "prove these N, in this order, and N bills
;;; reach modulo 0", which is the question, and it re-measures itself on every
;;; load so it cannot go stale.
;;;
;;; WHERE A BILL COMES FROM.  A 115-leaf bill is not 115 problems; it is two or
;;; three arcs cited by name.  Each leaf is attributed to the DIRECT citation it
;;; entered through, so `free-length-le-generators' reads as "89 via
;;; smith-diagonalization, 42 via free-transport" rather than as a wall of
;;; symbols.  Attribution is by containment in `debt-of' of each direct
;;; citation, so a leaf reachable through two citations is counted under both --
;;; the columns are entry routes, not a partition, and they do not sum to the
;;; bill.
(define (db--bill-list)                  ; ((name . leaves) ...), non-empty only
  (let ((out '()))
    (hash-table-walk *proof-debt*
      (lambda (p bill) (when (pair? bill) (set! out (cons (cons p bill) out)))))
    out))

;;; One greedy round: the leaf that empties the most bills, and how many.
(define (db--best-leaf bills)
  (let ((h (make-equal-hash-table)) (best #f) (bn 0))
    (for-each (lambda (b)
                (when (= 1 (length (cdr b)))
                  (hash-table-set! h (cadr b)
                    (+ 1 (hash-table-ref/default h (cadr b) 0)))))
              bills)
    (hash-table-walk h
      (lambda (k v)
        (when (or (> v bn)
                  (and (= v bn) best (string<? (symbol->string k)
                                               (symbol->string best))))
          (set! best k) (set! bn v))))
    (cons best bn)))

;;; The ranking, as DATA: ((leaf cleared-count warrant-kind) ...), in order.
;;; Ties broken by name so the file is reproducible across loads.
(define (debt-greedy-order #!optional limit)
  (let ((limit (if (default-object? limit) 40 limit)))
    (let loop ((bills (db--bill-list)) (i 0) (acc '()))
      (let ((r (db--best-leaf bills)))
        (if (or (not (car r)) (>= i limit))
            (reverse acc)
            (let* ((leaf (car r))
                   (short (map (lambda (b) (cons (car b) (delete leaf (cdr b)))) bills))
                   (w     (warrant-of leaf)))
              (loop (filter (lambda (b) (pair? (cdr b))) short)
                    (+ i 1)
                    (cons (list leaf (cdr r) (if w (car w) 'NONE)) acc))))))))

;;; ((citation . how-many-of-NAME's-bill-it-accounts-for) ...), biggest first.
(define (debt-entry-routes name)
  (let* ((bill (debt-of name))
         (cits (delete-duplicates
                (hash-table-ref/default *proof-citation-graph* name '())))
         (rows (map (lambda (c)
                      (cons c (length (filter (lambda (l) (member l bill))
                                              (debt-of c)))))
                    cits)))
    (sort (filter (lambda (r) (> (cdr r) 0)) rows)
          (lambda (a b)
            (if (= (cdr a) (cdr b))
                (string<? (symbol->string (car a)) (symbol->string (car b)))
                (> (cdr a) (cdr b)))))))

(define (debt-bundle-md)
  (let* ((path  (string-append *reference-dir* "DEBT-BUNDLE.md"))
         (bills (db--bill-list))
         (all   (length (hash-table-keys *proof-debt*)))
         (order (debt-greedy-order 40))
         (big   (sort (filter (lambda (b) (>= (length (cdr b)) 10)) bills)
                      (lambda (a b)
                        (if (= (length (cdr a)) (length (cdr b)))
                            (string<? (symbol->string (car a)) (symbol->string (car b)))
                            (> (length (cdr a)) (length (cdr b))))))))
    (with-output-to-file path
      (lambda ()
        (display "# The Debt Bundle\n\n")
        (display "Auto-generated by `(debt-bundle-md)` at load.  ")
        (display all) (display " proven result(s); ")
        (display (- all (length bills)))
        (display " bill `modulo 0`, ")
        (display (length bills)) (display " carry a bill.\n\n")
        (display "`PROOF-DEBT.md` lists every bill flat.  This file answers the two\n")
        (display "questions that list cannot: **what is worth proving next**, and\n")
        (display "**where a long bill comes from**.\n\n")
        ;; --- 1. the greedy ranking
        (display "## 1. What to prove next (greedy what-if)\n\n")
        (display "Ranked by bills CLEARED, not by citations: a leaf buys nothing\n")
        (display "until it is the last unproven one in the bills that name it.  Each\n")
        (display "row assumes every row above it is already discharged.\n\n")
        (display "| # | leaf | warrant | bills cleared | running total |\n")
        (display "|---|------|---------|---------------|---------------|\n")
        (let loop ((o order) (i 1) (run 0))
          (unless (null? o)
            (let ((run (+ run (cadr (car o)))))
              (display "| ") (display i)
              (display " | `") (display (car (car o)))
              (display "` | ") (display (caddr (car o)))
              (display " | ") (display (cadr (car o)))
              (display " | ") (display run) (display " |\n")
              (loop (cdr o) (+ i 1) run))))
        (newline)
        ;; --- 2. entry-route attribution for the long bills
        (display "## 2. Where the long bills come from\n\n")
        (display "Every bill of ten leaves or more, with each leaf attributed to the\n")
        (display "direct citation it entered through.  Routes OVERLAP -- a leaf\n")
        (display "reachable two ways is counted twice -- so the columns do not sum to\n")
        (display "the bill.  A route carrying most of a bill is the arc to attack.\n\n")
        (if (null? big)
            (display "_No bill has ten or more leaves._\n\n")
            (for-each
             (lambda (b)
               (display "### ") (display (car b))
               (display "  *(") (display (length (cdr b)))
               (display " leaves, trust: ") (display (debt-trust-level (cdr b)))
               (display ")*\n\n")
               (let ((routes (debt-entry-routes (car b))))
                 (if (null? routes)
                     (display "_Leaves are cited directly; no intermediate route._\n\n")
                     (begin
                       (for-each (lambda (r)
                                   (display "- ") (display (cdr r))
                                   (display " via `") (display (car r)) (display "`\n"))
                                 (if (> (length routes) 8) (list-head routes 8) routes))
                       (newline)))))
             big))
        (display "---\n\n_Regenerated on every library load; do not hand-edit._\n")))
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
