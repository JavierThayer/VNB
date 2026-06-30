;;; reference-topics.scm -- curated TOPIC pages for the browser reference section.
;;;
;;; "No new math" -- pure organization.  Each topic page groups already-installed
;;; results under reading-order headings, so the browser has an "Elementary
;;; calculus" page and a "Metric spaces" page (same shape) as entry points for
;;; future work.  No result is unique to a topic page; it is a curated view.
;;;
;;; Generated into reference/<TOPIC>.md and surfaced as hub cards by
;;; reference/build-reference-html.py (its DOCS list).  Loaded last, after every
;;; result is installed.  Re-emit by hand with (write-topic-pages).
;;; ====================================================================

;;; render one entry: reuse the catalog renderer when the name is an installed
;;; result; otherwise list it as a vocabulary pointer (def-functoid/-predicate
;;; names are not theorems, but belong on the page as the topic's vocabulary).
(define (topic--known? name) (hash-table-ref *theorem-table* name (lambda () #f)))

;;; inline " · [`file`](file)" link to the .scm that states/proves `name'
;;; (relative to *prover-dir*, forced to .scm -- same pathing as the structure
;;; source links).  Empty when no source was stamped (e.g. REPL installs).
(define (topic--file-link name)
  (let ((p (hash-table-ref *theorem-source* name (lambda () #f))))
    (if (not p) ""
        (let* ((s   (->namestring (pathname-new-type (->pathname p) "scm")))
               (pd  *prover-dir*)
               (rel (if (and (>= (string-length s) (string-length pd))
                             (string=? (substring s 0 (string-length pd)) pd))
                        (substring s (string-length pd) (string-length s))
                        s)))
          ;; href is "../<rel>": the HTML pages live in reference/, the sources
          ;; one level up at the prover root, so a browser viewing
          ;; reference/BY-TOPIC.html resolves ../theorem-library/X.scm correctly.
          (string-append "  see [~/prover/" rel "](../" rel ")")))))

;;; textbook entry: name -- statement -- [warrant] -- link to its proof file.
;;; (Vocabulary names that are not installed results list as plain pointers.)
(define (topic--line name)
  (cond
    ((topic--known? name)
     (display "- `") (display name) (display "` — ")
     (display (expression->string (lookup-theorem name)))
     (let ((w (warrant-of name)))
       (when w (display "  _[warrant: ") (display (car w)) (display "]_")))
     (display (topic--file-link name))
     (newline))
    (else
     (display "- `") (display name) (display "` — _(definition / vocabulary)_") (newline))))

;;; ---- Elementary calculus (the differential arc on RR) ----
(define *elementary-calculus-sections*
  '(("Vocabulary"
     IS-DIFF-AT DERIV NTH-DERIV LITTLE-O-AT TAYLOR-POLY TAYLOR-DIFFERENTIABLE)
    ("Differentiation rules"
     derivative-unique diff-implies-continuous deriv-const deriv-identity
     deriv-sum deriv-product deriv-chain deriv-neg nth-deriv-one)
    ("Little-o calculus"
     diff-iff-little-o little-o-sum little-o-scalar)
    ("Extreme & interior values (Fermat)"
     extreme-value-max extreme-value-min
     interior-max-deriv-zero interior-min-deriv-zero)
    ("Mean value theorems"
     rolle mvt generalized-mvt)
    ("Consequences of the mean value theorem"
     deriv-zero-implies-constant mvt-upper-bound mvt-lower-bound
     deriv-pos-strictly-increasing)
    ("Taylor's theorem"
     taylor-poly-at-center taylor-lagrange)))

;;; ---- Metric spaces ----
(define *metric-spaces-sections*
  '(("Vocabulary"
     IS-MS-SEQUENCE CONVERGES-TO CONVERGES IS-CAUCHY-SEQ IS-COMPLETE
     BALL IS-OPEN IS-CLOSED IS-CONTINUOUS-AT IS-CONTINUOUS IS-UNIFORMLY-CONTINUOUS
     TOTALLY-BOUNDED IS-R-NET PRODUCT-METRIC COMPLETION)
    ("Sequences, limits, completeness"
     complete-cauchy-converges)
    ("Open / closed sets, balls"
     ball-is-open ball-membership ball-center-in empty-is-open
     carrier-is-open inter-of-opens-open)
    ("Continuity"
     continuous-is-continuous-at
     continuous-implies-open-preimage open-preimage-implies-continuous
     continuous-implies-closed-preimage closed-preimage-implies-continuous)
    ("Completion"
     completion-is-metric-space completion-is-complete embed-isometry)
    ("Compactness / total boundedness"
     totally-bounded-has-cauchy-subsequence cauchy-rapid-subsequence)
    ("Product metric spaces"
     product-is-metric-space product-projection-continuous
     product-convergence-coordinatewise compact-countable-product)
    ("Normed-field metric"
     nf-metric-space-is-metric-space)))

;;; ---- the topic table: ONE page, a big section heading per subject ----
(define *library-topics*
  (list (list "Calculus basics" *elementary-calculus-sections*)
        (list "Metric spaces"   *metric-spaces-sections*)))

;;; Emit a single reference page divided into big subject sections (## per
;;; subject), each with a few sub-sections (###), each result line carrying its
;;; statement and a "see ~/prover/<file>" link to the proof.
(define (write-by-topic-md)
  (let ((path (string-append *reference-dir* "BY-TOPIC.md")))
    (with-output-to-file path
      (lambda ()
        (display "# Theorems by topic\n\n")
        (display "The library grouped by subject, like a textbook table of ")
        (display "contents.  Each entry gives its statement and a link to the ")
        (display ".scm file with its proof.  (The flat catalog is `THEOREMS.md`.)\n\n")
        (for-each
          (lambda (topic)
            (display "## ") (display (car topic)) (newline) (newline)
            (for-each
              (lambda (sec)
                (display "### ") (display (car sec)) (newline) (newline)
                (for-each topic--line (cdr sec))
                (newline))
              (cadr topic)))
          *library-topics*)))
    path))

;;; emit at load (every result above is installed by now)
(write-by-topic-md)
(display ";; reference-topics: wrote BY-TOPIC.md\n")
