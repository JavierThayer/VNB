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

;;; ---- Vector calculus (real vector spaces, linear functionals, Hahn-Banach) ----
;;; The linear-functional / Hahn-Banach scaffolding for vector-valued analysis
;;; (the route to a vector Taylor remainder bound).
(define *vector-calculus-sections*
  '(("Vocabulary"
     IS-VECTOR-SPACE IS-SUBMODULE IS-SUBSPACE IS-NOETHERIAN IS-FINITE-DIMENSIONAL
     SPAN-ADD-ONE IS-NORMED-VECTOR-SPACE
     IS-LINEAR-FUNCTIONAL IS-LINEAR-FUNCTIONAL-ON
     IS-BOUNDED-LINEAR-FUNCTIONAL IS-BOUNDED-LINEAR-FUNCTIONAL-ON
     DUAL-NORM DUAL-NORM-ON EXTENDS-ON NPE GOOD-SUB LINE
     NVS-METRIC-SPACE IS-DIFF-AT-V DERIV-V NTH-DERIV-V TAYLOR-POLY-V TAYLOR-DIFFERENTIABLE-V)
    ("Finite-dimensional spaces (noetherian / ascending chain condition)"
     noetherian-set-has-maximal hb-good-has-maximal)
    ("Hahn-Banach extension"
     hahn-banach-extend-one good-step hahn-banach)
    ("The norm as a supremum of functionals"
     norm-bounded-by-functionals norm-attained-by-functional norm-as-sup)
    ("Vector-valued Taylor (remainder-norm bound, reduced to scalar)"
     vector-taylor-remainder-bound)))

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

;;; ---- Combinatorial (pigeonhole, dependent choice on NN, the block family) ----
;;; The metric-free counting/recursion core behind the compactness arguments:
;;; infinite pigeonhole and dependent choice build the nested block family and
;;; the diagonal sequence that make totally-bounded sequences have Cauchy
;;; subsequences (Metric spaces > Compactness).
(define *combinatorial-sections*
  '(("Vocabulary"
     INF-SUBSETS IS-FINITE-COVER)
    ("Dependent choice / recursion on NN"
     dc-on-nn dc-on-nn-pred)
    ("Infinite pigeonhole and the block family"
     pigeonhole-infinite cover-block-step block-family-combinatorial)
    ("Diagonalization"
     diagonalization nn-step-strictly-mono nn-nested-subset-chain
     inf-subset-nn-unbounded)
    ("Well-ordering of NN"
     well-ordering-principle nn-least-element)))

;;; ---- Linear algebra (matrices over a ring; elementary operations; determinants) ----
;;; The algebraic-numbers.pdf ch.3 arc: the matrix ring, the matrix unit and its
;;; column-shift lemma (the engine), and the elementary column matrices F/G/H with
;;; their Prop 3.5 actions and Cor 3.6 inverses -- all machine-checked (trust:none).
;;;
;;; The page used to list six of the ~137 installed matrix results, which made the
;;; whole matrix layer invisible to a reader browsing by subject -- and with it the
;;; determinants, whose only trace anywhere in the docs was one generated row in the
;;; manual's source appendix.  The layer is laid out in reading order below: what a
;;; matrix IS, the arithmetic, the ring, the constructions that cut and extend one,
;;; then the elementary operations built on them, and finally DET.
(define *linear-algebra-sections*
  '(("Vocabulary"
     MAT ENTRY MATOF MATMUL MATADD MATNEG MATSCALE IDENTMAT ZEROMAT MAT-RING
     SUBMAT BLOCK SNOC-COL SNOC-ROW MATUNIT ELEM-F ELEM-G ELEM-H MAT-EQUIV
     MATACT MINOR DET INTERVAL)
    ("Matrices as a set, and their entries"
     mat-is-set matrix-sethood matrix-membership matrix-entry-extensionality
     entry-in-carrier matof-exists matof-in-mat entry-of-matof
     mat-0-1-nonempty mat-1-0-nonempty)
    ("Addition, negation, scaling"
     matadd-type matadd-entry matadd-assoc matadd-comm
     matadd-zero-left matadd-zero-right matadd-neg-left matadd-neg-right
     matneg-type matscale-type matscale-entry)
    ("Multiplication"
     matmul-type matmul-entry matmul-assoc matmul-left-dist matmul-right-dist
     matprod-summand-type matmul-assoc-summand-type)
    ("The identity and zero matrices"
     identmat-type identmat-entry-diag identmat-entry-off
     entry-of-identmat entry-of-zeromat
     identmat-left-identity identmat-right-identity identmat-invertible)
    ("The matrix ring"
     mat-ring-is-ring mat-ring-carr mat-ring-add mat-ring-mul
     mat-ring-zero mat-ring-one mat-ring-neg mat-ring-add-fun mat-ring-mul-fun)
    ("Cutting and extending: submatrices, blocks, bordered matrices"
     submat-type entry-of-submat entry-of-block
     snoc-col-type snoc-col-last entry-of-snoc-col
     snoc-row-type snoc-row-last entry-of-snoc-row)
    ("The matrix unit and its column shift (Lemma 3.3)"
     matunit-type matunit-entry-k-row matunit-entry-off-row
     entry-of-matunit matunit-summand-type matunit-col-shift)
    ("Elementary column operations (Prop 3.5)"
     elem-f-type elem-g-type elem-h-type
     elem-f-action elem-g-action elem-h-action
     entry-of-elem-f entry-of-elem-g entry-of-elem-h)
    ("Elementary row operations"
     elem-f-row-action elem-g-row-action elem-h-row-action)
    ("Elementary inverses (Cor 3.6)"
     elem-f-inverse elem-g-inverse elem-h-inverse
     elem-f-invertible elem-g-invertible)
    ("Matrix equivalence"
     mat-equiv mat-equiv-refl mat-equiv-trans
     mat-equiv-left-mult mat-equiv-right-mult
     mat-equiv-target-is-mat mat-equiv-cod-is-mat)
    ("Matrices acting on sequences of module elements"
     matact-type matact-entry matact-identmat matact-assoc
     matact-row-add matact-row-scale matact-row-peel matact-snoc
     matact-unitrow matact-zerorow matact-empty-vzero
     matact-triple-left matact-triple-right)
    ;; Determinants.  DEFINED, not proved: det-zero and det-cofactor are the two
    ;; definitional recursion axioms (no warrant, no debt), and every property
    ;; below it is an ASSERTED seed carrying a Hoffman-Kunze citation.  The page
    ;; prints each one's warrant, so the reader can see that for himself.
    ("Determinants: minors and cofactor expansion"
     MINOR DET minor-type det-zero det-cofactor
     det-in-carrier det-1x1 det-2x2
     det-identity det-alternating-rows det-multiplicative)
    ("The binomial theorem"
     sum-expansion binomial-theorem)))

;;; ---- the topic table: ONE page, a big section heading per subject ----
(define *library-topics*
  (list (list "Calculus basics"  *elementary-calculus-sections*)
        (list "Vector calculus"  *vector-calculus-sections*)
        (list "Linear algebra"   *linear-algebra-sections*)
        (list "Combinatorial"    *combinatorial-sections*)
        (list "Metric spaces"    *metric-spaces-sections*)))

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

;;; =====================================================================
;;; LaTeX rendition of the same topic table, with a NATURAL-LANGUAGE proof
;;; highlight for each machine-checked result.  Three ingredients per entry:
;;;   * the statement as display math          -- expr->tex   (tex-output.scm)
;;;   * an English paraphrase of the statement -- wff->english (wff-english.scm)
;;;   * proof provenance + an NL "proof idea"  -- provenance-of / debt-of +
;;;     the curated *proof-notes* below (or the warrant text for asserted facts).
;;; Emits reference/BY-TOPIC.tex; build to PDF with pdflatex, or to HTML with
;;; LaTeXML (reference/build-by-topic.sh).  Standard amsmath/amssymb/hyperref
;;; only, so LaTeXML renders it without custom bindings.
;;; =====================================================================

;;; ---- curated NL proof highlights for the marquee machine-checked results ----
;;; (One or two sentences: the KEY IDEA, not the step trace.  Asserted facts use
;;; their warrant text instead; results with neither just show statement+status.)
(define *proof-notes* (make-equal-hash-table))
(define (proof-note! name text) (hash-table-set! *proof-notes* name text))
(define (proof-note-of name) (hash-table-ref/default *proof-notes* name #f))

(proof-note! 'derivative-unique
  "Skolemize the two Caratheodory factors phi, psi from the two differentiability hypotheses; off the point they agree by cancelling (x-a) =/= 0, and continuity at a forces phi(a)=psi(a), i.e. L=M.")
(proof-note! 'diff-implies-continuous
  "f coincides pointwise with the map x |-> f(a) + phi(x)*(x-a), which the continuity algebra makes continuous at a (a constant plus phi times x-a); continuity then transfers to f.")
(proof-note! 'deriv-const
  "Witness phi := 0: the difference f(x)-f(a) = 0 = 0*(x-a), and the zero map is continuous with value 0.")
(proof-note! 'deriv-identity
  "Witness phi := 1: x-a = 1*(x-a), and the constant map 1 is continuous.")
(proof-note! 'rolle
  "The extreme value theorem gives an interior maximum or minimum; Fermat's lemma kills the derivative there.  A three-way case split handles the degenerate case where both extrema sit at the (equal) endpoints.")
(proof-note! 'mvt
  "Apply Rolle to the tilted auxiliary g(x) = f(x) - L(x), where L is the secant line through the two endpoints.")
(proof-note! 'generalized-mvt
  "Rolle applied to a two-function auxiliary -- the Cauchy mean value theorem.")
(proof-note! 'taylor-lagrange
  "The Cauchy mean value theorem (generalized-mvt) applied to the Taylor remainder against (x-a)^(n+1).")
(proof-note! 'deriv-zero-implies-constant
  "For any two points the mean value theorem on the subinterval gives f(y)-f(x) = f'(c)*(y-x) = 0.")
(proof-note! 'deriv-pos-strictly-increasing
  "The mean value theorem gives f(y)-f(x) = f'(c)*(y-x) > 0 whenever x < y.")
(proof-note! 'hahn-banach
  "A maximal norm-preserving extension exists by the ascending chain condition on the finite-dimensional space (via dependent choice on NN); were it proper, the one-step extension lemma would extend it further -- a contradiction.")
(proof-note! 'norm-as-sup
  "The Hahn-Banach payoff: on the line RR*x a norming functional attains ||x||, while every bounded functional is dominated by the norm, so ||x|| is exactly the supremum of the functional values.")
(proof-note! 'vector-taylor-remainder-bound
  "Reduce the vector remainder to a scalar: a norming functional g (Hahn-Banach) turns ||remainder|| into g(remainder); scalar Taylor on g o f, then bound g(f^(n+1)) by ||f^(n+1)||.")
(proof-note! 'diagonalization
  "Dependent choice on NN (dc-on-nn-pred) builds a strictly increasing sequence, each term hopping into the next nested set; the nested chain then puts the whole tail inside every member.")
(proof-note! 'block-family-combinatorial
  "Dependent choice on NN whose step is one infinite-pigeonhole refinement (cover-block-step): each block is an infinite monochromatic sub-block of the previous one for the next cover.  The index shift blk(k)=aux(succ k) aligns capture with level.")
(proof-note! 'totally-bounded-has-cauchy-subsequence
  "Total boundedness supplies a finite eps-net cover at each level; block-family-combinatorial builds nested infinite blocks pinned into shrinking balls; diagonalization extracts one subsequence, and the 2r triangle estimate makes it Cauchy.")
(proof-note! 'noetherian-set-has-maximal
  "The ascending chain condition: a strictly increasing infinite chain of subspaces would, via dependent choice, exceed every finite dimension.")
(proof-note! 'compact-countable-product
  "Sequential compactness of a countable metric product, obtained by a coordinatewise diagonal subsequence.")
(proof-note! 'mat-ring-is-ring
  "Each of the 14 ring axioms is reduced by matrix-entry-extensionality to an entry identity, then discharged against the entrywise ring axioms and the FINSUM distribution / Fubini lemmas.")
(proof-note! 'matmul-assoc
  "Both (PQ)R and P(QR) expand, via matmul-entry twice, to the same canonical double sum; finsum-fubini interchanges the two summation orders.")
(proof-note! 'matunit-col-shift
  "matmul-entry expands (P.E[k,l])_{ic} to FINSUM_j P_{ij}.E[k,l]_{jc}; off the index k the summand vanishes, so finsum-single-support collapses the sum, and an excluded-middle split on c=l finishes.")
(proof-note! 'elem-f-action
  "Right-multiplication by F[k,l] permutes columns k and l: a three-way column split, each branch a single-support finsum collapse of the transposition matrix.")
(proof-note! 'elem-g-action
  "The l-column of G = I + r.E[k,l] has TWO supports (the diagonal l and the r-slot k), so a two-point finsum split gives P_{il} + P_{ik}.r; every other column is a single-support identity column.")
(proof-note! 'elem-h-action
  "H[r,k] scales column k by r: a single-support finsum collapse at the diagonal, then a case split on c=k.")
(proof-note! 'elem-f-inverse
  "F[k,l] is its own inverse: composing its column-swap action (Prop 3.5) with F[l,k] swaps the columns back, matching the identity entrywise.")
(proof-note! 'elem-g-inverse
  "G[r,k,l]^{-1} = G[-r,k,l]: on column l the added term P_{ik}.(-r) cancels the r via r + (-r) = 0; every other column is unchanged.")
(proof-note! 'elem-h-inverse
  "H[r,k]^{-1} = H[r^{-1},k]: the (k,k) diagonal entry becomes r.s = 1 by the unit hypothesis; the rest of the diagonal stays 1 and off-diagonal 0.")
(proof-note! 'binomial-theorem
  "Induction on n via a multiply-and-shift sum expansion and Pascal's recurrence on the binomial coefficients, in integer-range SUM form (no bijections).")

;;; ---- LaTeX escaping for PROSE (statements go through expr->tex, which emits
;;; math directly and must NOT be escaped) ----
;; Map a non-ASCII code point to a pdflatex-safe rendering (the warrant/gloss
;; prose is meant to be ASCII, but a stray math glyph must not break the build).
(define (topic--unicode->tex code)
  (case code
    ((8712) "$\\in$") ((8713) "$\\notin$")
    ((8838) "$\\subseteq$") ((8839) "$\\supseteq$")
    ((8834) "$\\subset$") ((8835) "$\\supset$")
    ((8746) "$\\cup$") ((8745) "$\\cap$")
    ((8804) "$\\le$") ((8805) "$\\ge$") ((8800) "$\\ne$")
    ((8721) "$\\sum$") ((8719) "$\\prod$") ((8734) "$\\infty$")
    ((8594) "$\\to$") ((8658) "$\\Rightarrow$") ((8660) "$\\Leftrightarrow$")
    ((8704) "$\\forall$") ((8707) "$\\exists$") ((172) "$\\neg$")
    ((215) "$\\times$") ((8901) "$\\cdot$") ((8226) "$\\cdot$")
    ((949) "$\\varepsilon$") ((948) "$\\delta$") ((966 981) "$\\varphi$")
    ((968) "$\\psi$") ((955) "$\\lambda$") ((960) "$\\pi$") ((8747) "$\\int$")
    (else "?")))

(define (topic--tex-esc s)
  (list->string
   (apply append
     (map (lambda (c)
            (cond
              ((eqv? c #\\) (string->list "\\textbackslash{}"))
              ((eqv? c #\{) (string->list "\\{"))
              ((eqv? c #\}) (string->list "\\}"))
              ((eqv? c #\$) (string->list "\\$"))
              ((eqv? c #\&) (string->list "\\&"))
              ((eqv? c #\#) (string->list "\\#"))
              ((eqv? c #\_) (string->list "\\_"))
              ((eqv? c #\%) (string->list "\\%"))
              ((eqv? c #\^) (string->list "\\textasciicircum{}"))
              ((eqv? c #\~) (string->list "\\textasciitilde{}"))
              ((> (char->integer c) 127)
               (string->list (topic--unicode->tex (char->integer c))))
              (else (list c))))
          (string->list s)))))

(define (topic--bill->tex bill)
  (topic--tex-esc
   (call-with-output-string
    (lambda (p)
      (let loop ((b bill) (first #t))
        (unless (null? b)
          (unless first (display ", " p))
          (display (car b) p)
          (loop (cdr b) #f)))))))

;;; Render one topic entry as a LaTeX block.  (Safe hash lookup: `lookup-theorem'
;;; ERRORS on a non-theorem name -- the Vocabulary entries are functoids /
;;; predicates, not theorems -- so read the table directly, #f when absent.)
(define (topic--tex-entry name)
  (let ((f (hash-table-ref/default *theorem-table* name #f)))
    (display "\\subsubsection*{\\texttt{")
    (display (topic--tex-esc (symbol->string name)))
    (display "}}\n")
    (cond
      ((not f)
       (display "\\emph{Definition / vocabulary.}\n\n"))
      (else
       ;; English paraphrase + display-math statement
       (display "\\emph{") (display (topic--tex-esc (english-of name))) (display "}\n")
       (display "{\\small\\[\n") (display (expr->tex f)) (display "\n\\]}\n")
       ;; provenance + proof idea
       (let ((prov (provenance-of name))
             (note (proof-note-of name))
             (w    (warrant-of name)))
         (case prov
           ((proven)
            (let* ((bill (debt-of name)) (trust (debt-trust-level bill)))
              (display "\\noindent\\textbf{Machine-checked} (trust: ")
              (display trust) (display ").")
              (when note (display " ") (display (topic--tex-esc note)))
              (newline)
              (when (pair? bill)
                (display "\\par\\smallskip\\noindent\\emph{Rests on ")
                (display (length bill)) (display " fact")
                (when (> (length bill) 1) (display "s"))
                (display ":} \\texttt{") (display (topic--bill->tex bill))
                (display "}.\n"))))
           ((primitive)
            (display "\\noindent\\textbf{Primitive} (kernel axiom).")
            (when note (display " ") (display (topic--tex-esc note))) (newline))
           ((definitional)
            (display "\\noindent\\textbf{Definition.}\n"))
           (else
            (display "\\noindent\\textbf{Asserted}")
            (when w (display " [warrant: ") (display (car w)) (display "].")
                    (display " ") (display (topic--tex-esc (cdr w))))
            (when (and (not w) note) (display ". ") (display (topic--tex-esc note)))
            (newline)))
         (newline))))))

;; Render one entry to a string, or #f if it errors (so a single bad formula
;; degrades to a placeholder rather than blanking the document).
(define (topic--render-string nm)
  (call-with-current-continuation
   (lambda (k)
     (with-exception-handler
      (lambda (exn) exn (k #f))              ; escape on any error -> #f
      (lambda ()
        (with-output-to-string (lambda () (topic--tex-entry nm))))))))

(define (write-by-topic-tex)
  (let ((path (string-append *reference-dir* "BY-TOPIC.tex")))
    (with-output-to-file path
      (lambda ()
        (display "\\documentclass[11pt]{article}\n")
        (display "\\usepackage{amsmath,amssymb}\n")
        (display "\\usepackage[margin=1in]{geometry}\n")
        (display "\\usepackage{hyperref}\n")
        (display "\\allowdisplaybreaks\n")
        (display "\\title{The VNB Library --- Results by Topic}\n")
        (display "\\author{Generated by the VNB proof checker}\n")
        (display "\\date{\\today}\n")
        (display "\\begin{document}\n\\maketitle\n")
        (display "\\noindent Each result is shown three ways: an English paraphrase, ")
        (display "the formal statement, and --- for machine-checked theorems --- a ")
        (display "one-line idea of the proof together with the facts it is checked ")
        (display "modulo.  Grouped by subject, like a textbook table of contents.\n\n")
        (display "\\tableofcontents\n\\bigskip\n\n")
        (for-each
          (lambda (topic)
            (display "\\section{") (display (topic--tex-esc (car topic))) (display "}\n\n")
            (for-each
              (lambda (sec)
                (display "\\subsection{") (display (topic--tex-esc (car sec))) (display "}\n\n")
                (for-each
                  (lambda (nm)
                    ;; render each entry into a string under an error guard, so a
                    ;; single bad formula degrades to a placeholder instead of
                    ;; blanking the document.
                    (let ((s (topic--render-string nm)))
                      (if (string? s)
                          (display s)
                          (begin
                            (display "\\subsubsection*{\\texttt{")
                            (display (topic--tex-esc (symbol->string nm)))
                            (display "}}\n\\emph{(entry rendering skipped)}\n\n")))))
                  (cdr sec)))
              (cadr topic)))
          *library-topics*)
        (display "\\end{document}\n")))
    path))

;;; emit at load (every result above is installed by now)
(write-by-topic-md)
(write-by-topic-tex)
(display ";; reference-topics: wrote BY-TOPIC.md + BY-TOPIC.tex\n")
