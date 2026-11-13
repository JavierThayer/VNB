;;; library-book.scm -- THE BOOK OF THEOREMS AND DEFINITIONS, NO PROOFS (the user,
;;; notes-61, 2026-10-06): every definition, axiom, assumption and theorem the tree
;;; installs, as a statement, in an order in which every theorem follows the theorems
;;; and definitions it depends on, split into PARTS ("books") that are the libraries of
;;; libraries.sexp.  Written at every load to reference/library-book.tex;
;;; docs/library-book.tex is the standalone wrapper (`make library-book' in docs/).
;;;
;;; THE ORDER.  Parts in the table's order, which is a topological order of the
;;; imports; inside a part the files in LOAD order; inside a file the definitions
;;; first (structures, functoids, defined heads, then the other defining axioms, each
;;; group in the order of first mention in the source text), then the axioms and
;;; assumptions, then the propositions in INSTALL order (*proven-theorem-names*).  With
;;; the library gate clean, a theorem's citations are in its own part earlier in load
;;; order or in an earlier part, so the dependency claim holds; the writer checks it
;;; against the live citation graph anyway and prints the exceptions.
;;;
;;; WHAT IS LISTED.  Every name in *theorem-table* with a source file in a library,
;;; minus the machine-minted companions (the -rev of a macete, the view
;;; specialisations): provenance definitional (as a Definition), primitive (Axiom),
;;; asserted (Assumption, with its warrant tier), proven or certified (Proposition).
;;; A def-predicate / def-constant head is ONE entry carrying all its defining axioms;
;;; a declared structure is ONE entry (components, then the characteristic law) and
;;; its IS-X law is not repeated; a functoid reads `name(params) := body'.  The proof
;;; of a proposition is a `(display-proof 'NAME "file.pdf")' away.
;;;
;;; The renderers are the reader's and major-theorems': `mt--statement-tex',
;;; `proof-reader--definition-tex-1', `proof-reader--structure-tex', `at--abstract'.
;;; Loads after libraries.
;;;
;;; TWO LAYOUTS (2026-11-12, BOOK-GEN).  `(write-library-book-tex! PATH)' writes the book in
;;; the OUTLINE OF THE NOTES (the second half of this file: documents, chapters, sections,
;;; major results with their own lemmas, then the libraries); `(write-library-book-tex! PATH
;;; 'by-library)' writes the book described above, byte for byte as before
;;; (`lb--write-by-library!').

(define (lb--file-position rel)
  (let loop ((fs *vnb-files*) (i 0))
    (cond ((null? fs) 100000)
          ((and (string? (car fs)) (string=? (car fs) rel)) i)
          (#t (loop (cdr fs) (+ i 1))))))

(define (lb--listed? name)
  (and (not (rev-companion-source name))
       (not (view-specialized-source name))
       (memq (provenance-of name) '(definitional primitive asserted proven certified))))

;;; position of the first mention of NAME as a token in the file REL, or a large number
(define (lb--text-positions rel names)
  (let ((path (string-append *prover-dir* rel ".scm")))
    (if (not (file-exists? path))
        (map (lambda (n) (cons n 100000)) names)
        (let* ((text (string-downcase
                      (call-with-input-file path
                        (lambda (p)
                          (let loop ((acc '()))
                            (let ((line (read-line p)))
                              (if (eof-object? line)
                                  (apply string-append (reverse acc))
                                  (loop (cons "\n" (cons line acc))))))))))
               (len (string-length text))
               (tok? (lambda (c) (or (char-alphabetic? c) (char-numeric? c)
                                     (memv c '(#\- #\_ #\* #\! #\? #\< #\> #\= #\+ #\/ #\.))))))
          (map (lambda (n)
                 ;; `string-search-all', not `string-search-forward' with a start: the latter
                 ;; signals a range error for any nonzero start on this (non-ASCII) text in
                 ;; MIT Scheme 12.1, found 2026-10-06.
                 (let* ((s (string-downcase (symbol->string n))) (sl (string-length s)))
                   (let loop ((is (if (<= sl len) (string-search-all s text) '())))
                     (cond ((null? is) (cons n 100000))
                           ((let ((i (car is)))
                              (and (or (= i 0) (not (tok? (string-ref text (- i 1)))))
                                   (or (>= (+ i sl) len) (not (tok? (string-ref text (+ i sl)))))))
                            (cons n (car is)))
                           (#t (loop (cdr is)))))))
               names)))))

(define (lb--sort-by-text rel entries key)
  ;; ENTRIES are lists whose KEY element is the name to look up
  (let ((pos (lb--text-positions rel (map key entries))))
    (sort entries (lambda (a b) (< (cdr (assq (key a) pos)) (cdr (assq (key b) pos)))))))

;;; the entries of one file: ((kind name tex) ...) in book order.  HOME? is false for
;;; the share of a CROSS-CUTTING file that lands in another part: then the file's
;;; structures and functoids are not repeated there.
(define (lb--file-entries rel names home?)
  (let* ((defl (library-definitions *library*))
         (consumed '())
         (consume! (lambda (n) (set! consumed (cons n consumed))))
         (structs
          ;; declared structures whose source is this file: one entry each; their IS-X law consumed
          (if (not home?) '()
          (filter (lambda (e) e)
                  (map (lambda (sname)
                         (let ((sd (hash-table-ref/default *structure-table* sname #f)))
                           (and sd (equal? (library-rel-of-path (structure-def-source-file sd)) rel)
                                (begin
                                  (consume! (symbol-append 'IS- sname))
                                  (for-each consume! (structure-def-axiom-names sd))
                                  (list 'structure sname
                                        (string-append "\\vnbstructdef{" (mt--escape-tt (symbol->string sname)) "}{"
                                                       (proof-reader--structure-tex sname 'shape)
                                                       (proof-reader--comments-tex (list sname)) "}\n"))))))
                       (hash-table-keys *structure-table*)))))
         (dstructs
          ;; definitional structures (refinements) through their is-X-def law stated here
          (filter (lambda (e) e)
                  (map (lambda (n)
                         (let* ((s (symbol->string n)) (sl (string-length s)))
                           (and (> sl 7) (string-ci=? (substring s 0 3) "is-")
                                (string-ci=? (substring s (- sl 4) sl) "-def")
                                (eq? (provenance-of n) 'definitional)
                                (let* ((base (string->symbol (string-upcase (substring s 3 (- sl 4))))))
                                  (and (lookup-definitional-structure base)
                                       (begin (consume! n)
                                              (list 'structure base
                                                    (string-append "\\vnbstructdef{" (mt--escape-tt (symbol->string base)) "}{"
                                                                   (proof-reader--structure-tex base 'definitional)
                                                                   (proof-reader--comments-tex (list base n)) "}\n"))))))))
                       names)))
         (heads
          ;; def-predicate / def-constant heads whose first axiom is stated here
          (filter (lambda (e) e)
                  (map (lambda (d)
                         (and (pair? (cdr d))
                              (memq (car (cadr d)) names)
                              (begin (for-each (lambda (ax) (consume! (car ax))) (cdr d))
                                     (list 'definition (car d)
                                           (proof-reader--definition-tex-1 (car d) (cons 'axioms (cdr d)))))))
                       defl)))
         (functoids
          (if (not home?) '()
          (filter (lambda (e) e)
                  (map (lambda (h)
                         (let ((reg (hash-table-ref/default *functoid-registry* h #f)))
                           (and reg (not (lookup-view-as h)) (pair? (cddr reg))
                                (equal? (library-rel-of-path (caddr reg)) rel)
                                (list 'definition h
                                      (proof-reader--definition-tex-1 h (list 'functoid (car reg) (cadr reg)))))))
                       (hash-table-keys *functoid-registry*)))))
         (other-defs
          (filter (lambda (e) e)
                  (map (lambda (n)
                         (and (eq? (provenance-of n) 'definitional) (not (memq n consumed))
                              (list 'definition n
                                    (string-append "\\vnbdef{" (mt--escape-tt (symbol->string n)) "}{"
                                                   (mt--statement-tex (mt--formula n))
                                                   (proof-reader--comments-tex (list n)) "}\n"))))
                       names)))
         (axioms
          (filter (lambda (e) e)
                  (map (lambda (n)
                         (and (eq? (provenance-of n) 'primitive)
                              (list 'axiom n
                                    (string-append "\\vnbaxiom{" (mt--escape-tt (symbol->string n)) "}{"
                                                   (mt--statement-tex (mt--formula n)) "}\n"))))
                       names)))
         (assumptions
          (filter (lambda (e) e)
                  (map (lambda (n)
                         (and (eq? (provenance-of n) 'asserted)
                              (let* ((w (warrant-of n))
                                     (tier (cond ((pair? w) (car w)) (w w) (#t 'none))))
                                (list 'assumption n
                                      (string-append "\\vnbassume{" (mt--escape-tt (symbol->string n)) "}{"
                                                     (mt--escape-tex (if (symbol? tier) (symbol->string tier) "none")) "}{"
                                                     (mt--statement-tex (mt--formula n)) "}\n")))))
                       names)))
         (props
          (filter (lambda (e) e)
                  (map (lambda (n)
                         (and (memq n names) (memq (provenance-of n) '(proven certified))
                              (list 'proposition n
                                    (string-append "\\vnbprop{" (mt--escape-tt (symbol->string n)) "}{"
                                                   (mt--statement-tex (mt--formula n)) "}\n"))))
                       ;; install order, restricted to this file
                       (filter (lambda (n) (memq n names)) (reverse *proven-theorem-names*))))))
    (append (lb--sort-by-text rel (append structs dstructs) cadr)
            (lb--sort-by-text rel (append heads functoids) cadr)
            (lb--sort-by-text rel other-defs cadr)
            axioms assumptions props)))

(define lb--macro-block
  (string-append
   "\\providecommand{\\vnbstructdef}[2]{\\par\\medskip\\noindent\\textbf{Structure definition} (\\texttt{#1}).\\par\\nopagebreak#2\\par}\n"
   "\\providecommand{\\vnbdef}[2]{\\par\\medskip\\noindent\\textbf{Definition} (\\texttt{#1}).\\par\\nopagebreak#2\\par}\n"
   "\\providecommand{\\vnbaxiom}[2]{\\par\\medskip\\noindent\\textbf{Axiom} (\\texttt{#1}).\\par\\nopagebreak#2\\par}\n"
   "\\providecommand{\\vnbassume}[3]{\\par\\medskip\\noindent\\textbf{Assumption} (\\texttt{#1}; warrant: #2).\\par\\nopagebreak#3\\par}\n"
   "\\providecommand{\\vnbprop}[2]{\\par\\medskip\\noindent\\textbf{Proposition} (\\texttt{#1}).\\par\\nopagebreak#2\\par}\n"
   "\\providecommand{\\vnbbookfile}[2]{\\section*{\\href{file:../#2.scm}{\\texttt{#1}}}\\addcontentsline{toc}{section}{\\texttt{#1}}}\n"))

(define (lb--write-by-library! out-path)
  (read-libraries-table!)
  (let* ((all (filter lb--listed? (hash-table-keys *theorem-table*)))
         (by-group (make-equal-hash-table))   ; (lib . rel) -> names
         (out (mt--abs-path out-path))
         (index (make-equal-hash-table))     ; name -> running position in the book
         (counter 0)
         (nentries 0) (nfiles 0)
         (out-of-order '()))
    (for-each (lambda (n)
                (let ((rel (library-rel-of-path (hash-table-ref/default *theorem-source* n #f)))
                      (lib (library-of-name n)))
                  (when (and rel lib (not (eq? lib 'exempt)))
                    (hash-table-update!/default by-group (cons lib rel) (lambda (l) (cons n l)) '()))))
              all)
    ;; a file whose definitions are all def-functoids (or structures) installs no theorem
    ;; and had no section (notes-64 follow-up, 2026-10-12: 32 files, ~59 definitions):
    ;; give its home library a group for it, empty of theorem names
    (let ((home! (lambda (path)
                   (let* ((rel (library-rel-of-path path))
                          (lib (and rel (library-of-file rel))))
                     (when (and lib (not (eq? lib 'exempt)) (not (eq? lib 'cross-cutting)))
                       (hash-table-update!/default by-group (cons lib rel) (lambda (l) l) '()))))))
      (hash-table-walk *functoid-registry*
        (lambda (h reg)
          (if (and (not (lookup-view-as h)) (pair? (cddr reg))) (home! (caddr reg)))))
      (hash-table-walk *structure-table*
        (lambda (sname sd) (home! (structure-def-source-file sd)))))
    (with-output-to-file out
      (lambda ()
        (display "% library-book.tex -- GENERATED by (write-library-book-tex! ...) at load.  Do not hand-edit.\n")
        (display "% The theorems and definitions of the tree, no proofs, one part per library.\n")
        (display mt--macro-block)
        (display lb--macro-block)
        (display "\\tableofcontents\n\n")
        (for-each
          (lambda (lib)
            (let* ((files (sort (map cdr (filter (lambda (k) (eq? (car k) lib))
                                                 (hash-table-keys by-group)))
                                (lambda (a b) (< (lb--file-position a) (lb--file-position b)))))
                   (title (library-title lib)))
              (display "\\part{") (display (mt--escape-tex title)) (display "}\n")
              (display "\\noindent ") (display (mt--escape-tex (library-about lib))) (display "\n")
              (let ((imps (library-imports lib)))
                (if (pair? imps)
                    (begin (display "\\par\\noindent\\textit{Builds on:} ")
                           (display (mt--escape-tex (mt--join (map library-title imps) ", ")))
                           (display ".\n"))))
              (display "\\par\\noindent{\\small ") (display (length files)) (display " files.}\n\n")
              (for-each
                (lambda (rel)
                  (let* ((names (hash-table-ref/default by-group (cons lib rel) '()))
                         (home? (eq? lib (library-of-file rel)))
                         (entries (lb--file-entries rel names home?)))
                    (set! nfiles (+ nfiles 1))
                    (display "\\vnbbookfile{") (display (mt--escape-tt rel)) (display "}{") (display rel) (display "}\n")
                    (if (not home?)
                        (display "\\noindent{\\small A file shared across books; the entries that belong to this one.}\\par\n"))
                    (let ((ab (at--abstract (string-append rel ".scm"))))
                      (if (> (string-length ab) 0)
                          (begin (display "\\noindent{\\small ") (display (mt--escape-tex ab)) (display "}\\par\n"))))
                    (for-each
                      (lambda (e)
                        (set! counter (+ counter 1))
                        (set! nentries (+ nentries 1))
                        (hash-table-set! index (cadr e) counter)
                        (display (caddr e)))
                      entries)
                    (display "\n")))
                files)))
          (library-names))))
    ;; the dependency check: every citation of a listed proposition must precede it
    (hash-table-walk index
      (lambda (n i)
        (when (memq (provenance-of n) '(proven certified))
          (for-each (lambda (c)
                      (let ((j (hash-table-ref/default index c #f)))
                        (when (and j (> j i))
                          (set! out-of-order (cons (list n c) out-of-order)))))
                    (proof-citations-of n)))))
    (display ";; library-book: ") (display nentries) (display " entries in ") (display nfiles)
    (display " files, ") (display (length (library-names))) (display " parts -> ") (display out-path)
    (display "; ") (display (length out-of-order)) (display " citation(s) out of order")
    (newline)
    (let loop ((xs out-of-order) (k 0))
      (when (and (pair? xs) (< k 12))
        (display ";;   ") (display (car (car xs))) (display " cites later ") (display (cadr (car xs))) (newline)
        (loop (cdr xs) (+ k 1))))
    out-path))

;;; ===================================================================================
;;; THE BOOK IN THE OUTLINE OF THE NOTES (the user's approval, 2026-11-12; BOOK-GEN;
;;; measured by BOOK-SECT, scratchpad/triage/BOOK-SECT-REPORT.md).
;;;
;;; PARTS.  One part per document of the notes, in the order of
;;; docs/major-theorems-table.sexp; inside it the notes' chapters and sections (titles
;;; from the table's `outline' forms, the section of an entry from its `section' field),
;;; and inside a section the MAJOR RESULTS (the table's entries) in the notes' order.
;;; Then one part per library (libraries.sexp order): its definitions, axioms and
;;; assumptions by file in load order, then the theorems the notes' outline does not
;;; place, grouped by the statement's PRINCIPAL DEFINED HEAD, in file order.
;;;
;;; OWNERSHIP, from the citation graph (`proof-citations-of': the certificate's cites in a
;;; certified image, the proof's in the exam).  The HOME names of an entry are its `names'
;;; that are theorems of the book minus its `home-elsewhere' names.  From the home names of
;;; each entry the citations are followed DOWNWARD, stopping at any home name of another
;;; entry (that entry is recorded as USED: the "Uses:" line).  A lemma reached from exactly
;;; one entry is OWNED by it and printed after it, nested under its immediate dominator in
;;; the graph ROOT -> every home name -> citations (stopping at home names); a lemma
;;; reached from several is a TOOL of the lowest level they share -- the section, the
;;; chapter, the document -- printed after it, nested the same way; reached from several
;;; documents, or from none, it goes to its library's part.  THE LIBRARY FLOOR: a lemma
;;; whose library is strictly below the library of one of the results that reach it is
;;; never printed under the outline, but in its own library's part.
;;;
;;; THE PRINCIPAL HEAD of a statement: peel the universals and implications; the first
;;; applied head of the conclusion, then of the hypotheses from the last, that is a DEFINED
;;; head (`cert--defined-head?') and not one of `lbn--generic-heads'; else the first head of
;;; the conclusion that is not a connective or an arithmetic sign; else `<logic/arith>'.  A
;;; theorem of a structure-library/ file (the generated laws: functorials, is-X-is-set,
;;; projections) is grouped with its file; the kernel encoded (library `meta') by file.
;;; A head group of fewer than three theorems joins the part's "Other results".
;;; ===================================================================================

(define lbn--generic-heads
  '(< <= pos-rr subset abs card nn-minus binary-minus binary-divide is-metric is-metric-space rr-ms num))
(define lbn--logic-heads
  '(in = == and or not iff forall forsome implies < <= + * -))
(define lbn--small-group 3)       ; a head group smaller than this joins "Other results"
(define lbn--max-depth 6)         ; deepest indentation printed

;;; --- the table: entries and outlines ------------------------------------------------

(define (lbn--read-outlines path)
  (let ((full (mt--abs-path path)))
    (if (not (file-exists? full))
        '()
        (call-with-input-file full
          (lambda (port)
            (let loop ((form (read port)) (acc '()))
              (cond ((eof-object? form) (reverse acc))
                    ((and (pair? form) (eq? (car form) 'outline) (pair? (cdr form)))
                     (loop (read port) (cons form acc)))
                    (#t (loop (read port) acc)))))))))

;;; ((doc . chapter) . title) and ((doc . "C.S") . title), from the outline forms
(define (lbn--outline-titles outlines)
  (let ((t (make-equal-hash-table)))
    (for-each
     (lambda (o)
       (let ((doc (mt--as-string (cadr o))))
         (for-each
          (lambda (ch)
            ;; (title "..." [prefilled]): the document's title in the book
            (if (and (pair? ch) (eq? (car ch) 'title) (pair? (cdr ch)) (string? (cadr ch)))
                (hash-table-set! t (cons doc 'title) (cadr ch)))
            (when (and (pair? ch) (eq? (car ch) 'chapter) (pair? (cdr ch)))
              (let ((c (mt--as-string (cadr ch))))
                (if (and (pair? (cddr ch)) (string? (caddr ch)) (> (string-length (caddr ch)) 0))
                    (hash-table-set! t (cons doc c) (caddr ch)))
                (for-each
                 (lambda (sec)
                   (if (and (pair? sec) (eq? (car sec) 'section) (pair? (cdr sec))
                            (pair? (cddr sec)) (string? (caddr sec)))
                       (hash-table-set! t (cons doc (mt--as-string (cadr sec))) (caddr sec))))
                 (cddr ch)))))
          (cddr o))))
     outlines)
    t))

;;; the chapter of a ref: the leading run of digits and capitals before a `.', else the
;;; first word ("2.3.3.1-hol" -> "2", "A.3" -> "A", "Riesz-Markov (notes-63)" -> "Riesz-Markov")
(define (lbn--chapter-of-ref ref)
  (let ((n (string-length ref)))
    (let loop ((i 0))
      (cond ((and (< i n) (let ((c (string-ref ref i)))
                            (or (char-numeric? c) (and (char-alphabetic? c) (char-upper-case? c)))))
             (loop (+ i 1)))
            ((and (> i 0) (< i n) (char=? (string-ref ref i) #\.)) (substring ref 0 i))
            (#t (let word ((j 0))
                  (if (or (= j n) (char=? (string-ref ref j) #\space))
                      (if (= j 0) "?" (substring ref 0 j))
                      (word (+ j 1)))))))))

;;; one entry as a vector:
;;;  0 index  1 doc  2 ref  3 kind  4 title  5 home names  6 elsewhere  7 definitions+companions
;;;  8 status  9 chapter  10 section key  11 has-section?  12 notes statement  13 all names
(define (lbn--entry-vector i e book?)
  (let* ((names (mt--list e 'names))
         (else-names (mt--list e 'home-elsewhere))
         (home (filter (lambda (n) (and (book? n) (not (memq n else-names)))) names))
         (ref (mt--string e 'ref ""))
         (chap (lbn--chapter-of-ref ref))
         (sec (mt--string e 'section #f)))
    (vector i (mt--string e 'doc "unknown") ref (mt--one e 'kind 'theorem) (mt--string e 'title "")
            home else-names (append (mt--list e 'definitions) (mt--list e 'companions))
            (mt--one e 'status (mt--status-of-names names)) chap (or sec chap) (and sec #t)
            (mt--string e 'notes-statement "") names)))

(define (lbn--e-index v) (vector-ref v 0))
(define (lbn--e-doc v) (vector-ref v 1))
(define (lbn--e-ref v) (vector-ref v 2))
(define (lbn--e-kind v) (vector-ref v 3))
(define (lbn--e-title v) (vector-ref v 4))
(define (lbn--e-home v) (vector-ref v 5))
(define (lbn--e-elsewhere v) (vector-ref v 6))
(define (lbn--e-defs v) (vector-ref v 7))
(define (lbn--e-status v) (vector-ref v 8))
(define (lbn--e-chap v) (vector-ref v 9))
(define (lbn--e-sec v) (vector-ref v 10))
(define (lbn--e-notes v) (vector-ref v 12))
(define (lbn--e-names v) (vector-ref v 13))

(define (lbn--uniq xs)
  (let loop ((xs xs) (acc '()))
    (cond ((null? xs) (reverse acc))
          ((member (car xs) acc) (loop (cdr xs) acc))
          (#t (loop (cdr xs) (cons (car xs) acc))))))

;;; --- the book's theorems and their order ---------------------------------------------

;;; (values NAMES ORDER BY-GROUP): the propositions of the by-library book, a hash
;;; name -> position (parts, files in load order, install order), and the by-library
;;; grouping (lib . rel) -> names that the definitions chapters reuse.
(define (lbn--book-theorems)
  (let ((by-group (make-equal-hash-table))
        (install (make-strong-eqv-hash-table))
        (order (make-strong-eqv-hash-table)))
    (let loop ((ns (reverse *proven-theorem-names*)) (i 0))
      (when (pair? ns)
        (if (not (hash-table-ref/default install (car ns) #f)) (hash-table-set! install (car ns) i))
        (loop (cdr ns) (+ i 1))))
    (for-each (lambda (n)
                (let ((rel (library-rel-of-path (hash-table-ref/default *theorem-source* n #f)))
                      (lib (library-of-name n)))
                  (when (and rel lib (not (eq? lib 'exempt)))
                    (hash-table-update!/default by-group (cons lib rel) (lambda (l) (cons n l)) '()))))
              (filter lb--listed? (hash-table-keys *theorem-table*)))
    ;; files that install only functoids or structures still have definitions to print
    (let ((home! (lambda (path)
                   (let* ((rel (library-rel-of-path path))
                          (lib (and rel (library-of-file rel))))
                     (when (and lib (not (eq? lib 'exempt)) (not (eq? lib 'cross-cutting)))
                       (hash-table-update!/default by-group (cons lib rel) (lambda (l) l) '()))))))
      (hash-table-walk *functoid-registry*
        (lambda (h reg) (if (and (not (lookup-view-as h)) (pair? (cddr reg))) (home! (caddr reg)))))
      (hash-table-walk *structure-table*
        (lambda (sname sd) (home! (structure-def-source-file sd)))))
    (let ((keys (sort (hash-table-keys by-group)
                      (lambda (a b)
                        (let ((la (library-order-index (car a))) (lb (library-order-index (car b))))
                          (or (< la lb)
                              (and (= la lb) (< (lb--file-position (cdr a)) (lb--file-position (cdr b))))))))))
      (let ((k 0) (names '()))
        (for-each
         (lambda (key)
           (for-each (lambda (n)
                       (set! k (+ k 1))
                       (hash-table-set! order n k)
                       (set! names (cons n names)))
                     (sort (filter (lambda (n) (memq (provenance-of n) '(proven certified)))
                                   (hash-table-ref/default by-group key '()))
                           (lambda (a b) (< (hash-table-ref/default install a 0)
                                            (hash-table-ref/default install b 0))))))
         keys)
        (values (reverse names) order by-group)))))

(define (lbn--rel-of n) (library-rel-of-path (hash-table-ref/default *theorem-source* n #f)))
(define (lbn--generated? n)
  (let ((rel (lbn--rel-of n))) (and rel (string-prefix? "structure-library/" rel))))

;;; --- the placement ---------------------------------------------------------------------
;;; Returns an association list (the PLAN) with keys:
;;;   entries   list of entry vectors        name->eid  hash home name -> entry index
;;;   place     hash name -> (major EID) | (owned EID) | (tools LEVEL KEY) | (foundations)
;;;             | (unattached); before the library floor
;;;   floored   hash name -> #t when the floor sends it to its library
;;;   uses      hash eid -> entry indices reached first, in walk order
;;;   idom      hash name -> immediate dominator (symbol `<root>' at the top)
;;; LEAVES? true makes the generated laws leaves (the BOOK-SECT prototype's reading,
;;; for the regression only).
(define (lbn--plan names order table-entries leaves?)
  (let* ((book (make-strong-eqv-hash-table))
         (cites (make-strong-eqv-hash-table))
         (name->eid (make-strong-eqv-hash-table))
         (place (make-strong-eqv-hash-table))
         (owners (make-strong-eqv-hash-table))
         (uses (make-strong-eqv-hash-table))
         (floored (make-strong-eqv-hash-table))
         (warnings '()))
    (for-each (lambda (n) (hash-table-set! book n #t)) names)
    (for-each (lambda (n)
                (hash-table-set! cites n
                  (if (and leaves? (lbn--generated? n))
                      '()
                      (lbn--uniq (filter (lambda (m) (and (not (eq? m n)) (hash-table-ref/default book m #f)))
                                         (proof-citations-of n))))))
              names)
    (let* ((entries (let loop ((es table-entries) (i 0) (acc '()))
                      (if (null? es) (reverse acc)
                          (loop (cdr es) (+ i 1)
                                (cons (lbn--entry-vector i (car es) (lambda (n) (hash-table-ref/default book n #f)))
                                      acc)))))
           (ev (list->vector entries))
           (has-sections (lbn--uniq (map lbn--e-doc (filter (lambda (v) (vector-ref v 11)) entries))))
           (key-of (lambda (i) (let ((v (vector-ref ev i)))
                                 (list (lbn--e-doc v) (lbn--e-chap v) (lbn--e-sec v)))))
           (major-lib (make-strong-eqv-hash-table)))
      ;; homes: a name stays with the first entry that does not send it elsewhere
      (for-each (lambda (v)
                  (for-each (lambda (n)
                              (if (hash-table-ref/default name->eid n #f)
                                  (begin
                                    (set! warnings (cons (list 'two-homes n (lbn--e-doc v) (lbn--e-ref v)) warnings))
                                    (vector-set! v 5 (delete n (lbn--e-home v))))
                                  (hash-table-set! name->eid n (lbn--e-index v))))
                            (lbn--e-home v)))
                entries)
      ;; a home-elsewhere name with no home anywhere is a table error worth saying
      (for-each (lambda (v)
                  (for-each (lambda (n)
                              (if (and (hash-table-ref/default book n #f) (not (hash-table-ref/default name->eid n #f)))
                                  (set! warnings (cons (list 'no-home n (lbn--e-doc v) (lbn--e-ref v)) warnings))))
                            (lbn--e-elsewhere v)))
                entries)
      ;; the library of a result: the latest of its home names' libraries
      (for-each (lambda (v)
                  (let ((ls (filter symbol? (map library-of-name (lbn--e-home v)))))
                    (if (pair? ls)
                        (hash-table-set! major-lib (lbn--e-index v)
                          (car (sort ls (lambda (a b) (> (library-order-index a) (library-order-index b)))))))))
                entries)
      ;; the walk
      (for-each
       (lambda (v)
         (let ((i (lbn--e-index v)) (seen (make-strong-eqv-hash-table)) (used '()))
           (for-each (lambda (n) (hash-table-set! seen n #t)) (lbn--e-home v))
           (let walk ((stack (lbn--e-home v)))
             (when (pair? stack)
               (let ((x (car stack)) (rest (cdr stack)))
                 (let inner ((ys (hash-table-ref/default cites x '())) (rest rest))
                   (cond ((null? ys) (walk rest))
                         ((hash-table-ref/default seen (car ys) #f) (inner (cdr ys) rest))
                         (#t
                          (let* ((y (car ys)) (j (hash-table-ref/default name->eid y #f)))
                            (hash-table-set! seen y #t)
                            (cond ((and j (not (= j i)))
                                   (if (not (memv j used)) (set! used (cons j used)))
                                   (inner (cdr ys) rest))
                                  (j (inner (cdr ys) (cons y rest)))
                                  (#t
                                   (hash-table-update!/default owners y (lambda (l) (cons i l)) '())
                                   (inner (cdr ys) (cons y rest)))))))))))
           (hash-table-set! uses i (reverse used))))
       entries)
      ;; buckets
      (hash-table-walk name->eid (lambda (n i) (hash-table-set! place n (list 'major i))))
      (hash-table-walk owners
        (lambda (n os)
          (if (null? (cdr os))
              (hash-table-set! place n (list 'owned (car os)))
              (let* ((ks (lbn--uniq (map key-of os)))
                     (k1 (car ks)))
                (hash-table-set! place n
                  (cond ((and (null? (cdr ks)) (member (car k1) has-sections)) (list 'tools 'section k1))
                        ((null? (cdr (lbn--uniq (map (lambda (k) (list (car k) (cadr k))) ks))))
                         (list 'tools 'chapter (list (car k1) (cadr k1))))
                        ((null? (cdr (lbn--uniq (map car ks)))) (list 'tools 'doc (list (car k1))))
                        (#t (list 'foundations))))))
          ;; the library floor
          (let ((l (library-of-name n)))
            (if (and (symbol? l)
                     (let any-owner ((os os))
                       (and (pair? os)
                            (or (let ((m (hash-table-ref/default major-lib (car os) #f)))
                                  (and m (not (eq? l m)) (memq l (library-imports* m)) #t))
                                (any-owner (cdr os))))))
                (hash-table-set! floored n #t)))))
      (for-each (lambda (n) (if (not (hash-table-ref/default place n #f)) (hash-table-set! place n (list 'unattached))))
                names)
      (list (cons 'entries entries) (cons 'name->eid name->eid) (cons 'place place) (cons 'floored floored)
            (cons 'uses uses) (cons 'cites cites) (cons 'order order)
            (cons 'idom (lbn--dominators entries cites name->eid order))
            (cons 'has-sections has-sections) (cons 'warnings (reverse warnings))))))

(define (lbn--plan-ref plan key) (cdr (assq key plan)))

;;; Immediate dominators (Cooper, Harvey, Kennedy) of the graph <root> -> every home name
;;; -> citations, never entering a home name from a citation.
(define (lbn--dominators entries cites name->eid order)
  (let* ((root '<root>)
         (roots (append-map lbn--e-home entries))
         (succ (lambda (n)
                 (if (eq? n root)
                     roots
                     (filter (lambda (m) (not (hash-table-ref/default name->eid m #f)))
                             (hash-table-ref/default cites n '())))))
         (po (make-strong-eqv-hash-table))
         (post '())
         (visited (make-strong-eqv-hash-table)))
    ;; iterative depth-first post-order
    (hash-table-set! visited root #t)
    (let loop ((stack (list (cons root (succ root)))))
      (when (pair? stack)
        (let ((top (car stack)))
          (let find ((ws (cdr top)))
            (cond ((null? ws)
                   (set! post (cons (car top) post))
                   (loop (cdr stack)))
                  ((hash-table-ref/default visited (car ws) #f) (find (cdr ws)))
                  (#t
                   (let ((w (car ws)))
                     (set-cdr! top (cdr ws))
                     (hash-table-set! visited w #t)
                     (loop (cons (cons w (succ w)) stack)))))))))
    ;; post is now reverse post-order (root first)
    (let ((k (length post)))
      (let number ((xs post) (i (- k 1)))
        (when (pair? xs) (hash-table-set! po (car xs) i) (number (cdr xs) (- i 1)))))
    (let ((preds (make-strong-eqv-hash-table)) (idom (make-strong-eqv-hash-table)))
      (for-each (lambda (v) (for-each (lambda (w) (hash-table-update!/default preds w (lambda (l) (cons v l)) '()))
                                      (succ v)))
                post)
      (hash-table-set! idom root root)
      (let ((intersect
             (lambda (a b)
               (let loop ((a a) (b b))
                 (if (eq? a b) a
                     (let* ((a (let up ((a a)) (if (< (hash-table-ref po a (lambda () 0)) (hash-table-ref po b (lambda () 0)))
                                                   (up (hash-table-ref idom a (lambda () root))) a)))
                            (b (let up ((b b)) (if (< (hash-table-ref po b (lambda () 0)) (hash-table-ref po a (lambda () 0)))
                                                   (up (hash-table-ref idom b (lambda () root))) b))))
                       (loop a b)))))))
        (let iterate ()
          (let ((changed #f))
            (for-each
             (lambda (v)
               (if (not (eq? v root))
                   (let ((ps (filter (lambda (p) (hash-table-ref/default idom p #f))
                                     (hash-table-ref/default preds v '()))))
                     (if (pair? ps)
                         (let ((new (fold-left (lambda (acc p) (intersect p acc)) (car ps) (cdr ps))))
                           (if (not (eq? (hash-table-ref/default idom v #f) new))
                               (begin (hash-table-set! idom v new) (set! changed #t))))))))
             post)
            (if changed (iterate)))))
      idom)))

;;; --- the principal head ---------------------------------------------------------------

(define (lbn--heads f acc)
  (cond ((not (pair? f)) acc)
        ((symbol? (car f))
         (let loop ((xs (cdr f)) (acc (cons (car f) acc)))
           (if (pair? xs) (loop (cdr xs) (lbn--heads (car xs) acc)) acc)))
        (#t (let loop ((xs f) (acc acc))
              (if (pair? xs) (loop (cdr xs) (lbn--heads (car xs) acc)) acc)))))
(define (lbn--heads-of f) (reverse (lbn--heads f '())))

(define (lbn--principal-head n)
  (if (lbn--generated? n)
      '<generated>
      (let ((f (mt--formula n)))
        (let strip ((f f) (hyps '()))
          (cond ((and (pair? f) (eq? (car f) 'forall) (pair? (cdr f)) (pair? (cddr f))) (strip (caddr f) hyps))
                ((and (pair? f) (eq? (car f) 'implies) (pair? (cdr f)) (pair? (cddr f)))
                 (strip (caddr f) (cons (cadr f) hyps)))
                (#t
                 (or (let parts ((ps (cons f hyps)))       ; hyps is already last-first
                       (and (pair? ps)
                            (or (let hs ((h (lbn--heads-of (car ps))))
                                  (and (pair? h)
                                       (if (and (cert--defined-head? (car h)) (not (eq? (car h) n))
                                                (not (memq (car h) lbn--generic-heads)))
                                           (car h)
                                           (hs (cdr h)))))
                                (parts (cdr ps)))))
                     (let hs ((h (lbn--heads-of f)))
                       (and (pair? h) (if (memq (car h) lbn--logic-heads) (hs (cdr h)) (car h))))
                     '<logic/arith>)))))))

;;; --- rendering ----------------------------------------------------------------------------

(define lbn--macro-block
  (string-append
   "\\providecommand{\\vnbpropat}[3]{\\begin{list}{}{\\setlength{\\leftmargin}{#1pt}\\setlength{\\topsep}{2pt}\\setlength{\\itemsep}{0pt}}\\item[]"
   "\\textbf{\\ifdim#1pt>0pt Lemma\\else Proposition\\fi} (\\texttt{#2}).\\par\\nopagebreak#3\\end{list}}\n"
   "\\providecommand{\\vnbmajor}[2]{\\par\\bigskip\\noindent\\phantomsection\\label{#2}#1.\\par\\nopagebreak}\n"
   "\\providecommand{\\vnbnotesays}[1]{{\\small\\noindent\\textit{The notes:} #1\\par}}\n"
   "\\providecommand{\\vnbuses}[1]{{\\small\\noindent\\textit{Uses:} #1\\par}}\n"
   "\\providecommand{\\vnbstub}[1]{{\\noindent\\textit{#1}\\par}}\n"
   "\\providecommand{\\vnbblock}[1]{\\par\\smallskip{\\small\\noindent\\textit{#1}\\par}\\nopagebreak}\n"
   "\\providecommand{\\vnbgroup}[1]{\\section*{#1}}\n"))

(define (lbn--kind-word k)
  (mt--capitalize (mt--as-string k)))

(define (lbn--label v) (string-append "nb:" (number->string (lbn--e-index v))))

(define (lbn--prop-tex n depth)
  (string-append "\\vnbpropat{" (number->string (* 18 (min depth lbn--max-depth))) "}{"
                 (mt--escape-tt (symbol->string n)) "}{"
                 (mt--statement-tex (mt--formula n)) "}\n"))

;;; print MEMBERS (a list, any order) as a forest: a member's parent is its immediate
;;; dominator when that is a member too; siblings in book order
(define (lbn--forest members idom order depth)
  (let ((in (make-strong-eqv-hash-table)) (kids (make-strong-eqv-hash-table)) (tops '()))
    (for-each (lambda (n) (hash-table-set! in n #t)) members)
    (for-each (lambda (n)
                (let ((d (hash-table-ref/default idom n #f)))
                  (if (and d (not (eq? d n)) (hash-table-ref/default in d #f))
                      (hash-table-update!/default kids d (lambda (l) (cons n l)) '())
                      (set! tops (cons n tops)))))
              members)
    (let ((by-order (lambda (l) (sort l (lambda (a b) (< (hash-table-ref/default order a 0)
                                                          (hash-table-ref/default order b 0)))))))
      (let emit ((ns (by-order tops)) (depth depth))
        (for-each (lambda (n)
                    (display (lbn--prop-tex n depth))
                    (emit (by-order (hash-table-ref/default kids n '())) (+ depth 1)))
                  ns)))))

(define (lbn--ref-text v this-doc)
  (string-append "\\hyperref[" (lbn--label v) "]{" (lbn--kind-word (lbn--e-kind v)) " "
                 (mt--escape-tex (lbn--e-ref v)) "}"
                 (if (string=? (lbn--e-doc v) this-doc) ""
                     (string-append " (" (mt--escape-tex (mt--doc-title (lbn--e-doc v))) ")"))))

(define (lbn--write-entry v plan by-place)
  (let* ((ev (list->vector (lbn--plan-ref plan 'entries)))
         (name->eid (lbn--plan-ref plan 'name->eid))
         (idom (lbn--plan-ref plan 'idom))
         (order (lbn--plan-ref plan 'order))
         (doc (lbn--e-doc v))
         (home (lbn--e-home v))
         (uses (hash-table-ref/default (lbn--plan-ref plan 'uses) (lbn--e-index v) '())))
    (display "\\vnbmajor{\\textbf{") (display (lbn--kind-word (lbn--e-kind v))) (display " ")
    (display (mt--escape-tex (lbn--e-ref v))) (display "}")
    (if (not (string=? (lbn--e-title v) ""))
        (begin (display " (\\emph{") (display (mt--escape-tex (lbn--e-title v))) (display "})")))
    (display "}{") (display (lbn--label v)) (display "}\n")
    (if (not (string=? (lbn--e-notes v) ""))
        (begin (display "\\vnbnotesays{") (display (mt--escape-tex (lbn--e-notes v))) (display "}\n")))
    (cond
     ((pair? home)
      (if (pair? uses)
          (begin (display "\\vnbuses{")
                 (display (mt--join (map (lambda (j) (lbn--ref-text (vector-ref ev j) doc))
                                         (sort uses <))
                                    ", "))
                 (display ".}\n")))
      (for-each (lambda (n) (display (lbn--prop-tex n 0))) home)
      (if (pair? (lbn--e-defs v))
          (begin (display "\\vnbstub{It also quotes, not as theorems: ")
                 (display (mt--join (map mt--tt (lbn--e-defs v)) ", "))
                 (display ".}\n")))
      (let ((owned (hash-table-ref/default by-place (list 'owned (lbn--e-index v)) '())))
        (when (pair? owned)
          (display "\\vnbblock{Lemmas used only by this result (") (display (length owned)) (display "):}\n")
          (lbn--forest owned idom order 1))))
     (#t
      (let* ((homes (lbn--uniq (filter (lambda (x) x)
                                       (map (lambda (n) (hash-table-ref/default name->eid n #f))
                                            (lbn--e-elsewhere v))))))
        (display "\\vnbstub{")
        (cond ((pair? homes)
               (display "Its theorems are printed with ")
               (display (mt--join (map (lambda (j) (lbn--ref-text (vector-ref ev j) doc)) homes) ", "))
               (display "."))
              ((pair? (lbn--e-defs v))
               (display "No theorem of its own; it quotes ")
               (display (mt--join (map mt--tt (lbn--e-defs v)) ", "))
               (display "."))
              ((pair? (lbn--e-names v))
               (display "Not in the book: ")
               (display (mt--join (map mt--tt (lbn--e-names v)) ", "))
               (display " (status ") (display (mt--as-string (lbn--e-status v))) (display ")."))
              (#t (display "Not in the library (status ")
                  (display (mt--as-string (lbn--e-status v))) (display ").")))
        (display "}\n"))))))

;;; hash: placement key -> names, where the key is (owned EID) | (tools LEVEL KEY) |
;;; (library LIB) for everything the library parts print
(define (lbn--by-place plan)
  (let ((place (lbn--plan-ref plan 'place)) (floored (lbn--plan-ref plan 'floored))
        (t (make-equal-hash-table)))
    (hash-table-walk place
      (lambda (n p)
        (let ((key (cond ((eq? (car p) 'major) #f)
                         ((hash-table-ref/default floored n #f) (list 'library (library-of-name n)))
                         ((memq (car p) '(owned tools)) p)
                         (#t (list 'library (library-of-name n))))))
          (if key (hash-table-update!/default t key (lambda (l) (cons n l)) '())))))
    t))

(define (lbn--real-sections? ces)
  (let loop ((vs ces))
    (and (pair? vs)
         (let ((s (lbn--e-sec (car vs))))
           (or (not (or (string=? s (lbn--e-chap (car vs))) (string-suffix? ".0" s)))
               (loop (cdr vs)))))))

(define (lbn--write-document doc plan by-place titles)
  (let* ((idom (lbn--plan-ref plan 'idom)) (order (lbn--plan-ref plan 'order))
         (es (filter (lambda (v) (string=? (lbn--e-doc v) doc)) (lbn--plan-ref plan 'entries)))
         (chapters (lbn--uniq (map lbn--e-chap es)))
         (tools (lambda (key) (hash-table-ref/default by-place key '()))))
    (display "\\part{")
    (display (mt--escape-tex (hash-table-ref/default titles (cons doc 'title) (mt--doc-title doc))))
    (display "}\n")
    (for-each
     (lambda (c)
       (let* ((ces (filter (lambda (v) (string=? (lbn--e-chap v) c)) es))
              (ctitle (hash-table-ref/default titles (cons doc c) #f))
              (head (string-append (if (string->number c) (string-append "Chapter " c)
                                       (if (and (= (string-length c) 1) (char-alphabetic? (string-ref c 0)))
                                           (string-append "Appendix " c) c))
                                   (if ctitle (string-append ". " ctitle) ""))))
         (display "\\chapter*{") (display (mt--escape-tex head)) (display "}\n")
         (display "\\addcontentsline{toc}{chapter}{") (display (mt--escape-tex head)) (display "}\n")
         (for-each
          (lambda (s)
            (let ((ses (filter (lambda (v) (string=? (lbn--e-sec v) s)) ces))
                  (stitle (hash-table-ref/default titles (cons doc s) #f)))
              (if (and (not (string=? s c)) (not (string-suffix? ".0" s)))
                  (begin (display "\\section*{") (display (mt--escape-tex s))
                         (if stitle (begin (display " ") (display (mt--escape-tex stitle))))
                         (display "}\n")))
              (for-each (lambda (v) (lbn--write-entry v plan by-place)) ses)
              (let ((ts (tools (list 'tools 'section (list doc c s)))))
                (when (pair? ts)
                  (display "\\vnbblock{Tools shared by results of ")
                  (display (cond ((not (or (string=? s c) (string-suffix? ".0" s)))
                                  (string-append "section " (mt--escape-tex s)))
                                 ((lbn--real-sections? ces) "this chapter before its first section")
                                 (#t "this chapter")))
                  (display " (") (display (length ts)) (display "):}\n")
                  (lbn--forest ts idom order 1)))))
          (lbn--uniq (map lbn--e-sec ces)))
         (let ((ts (tools (list 'tools 'chapter (list doc c)))))
           (when (pair? ts)
             (display "\\section*{Tools of the chapter}\n")
             (display "\\vnbblock{Shared by results of several sections of this chapter (") (display (length ts))
             (display "):}\n")
             (lbn--forest ts idom order 1)))))
     chapters)
    (let ((ts (tools (list 'tools 'doc (list doc)))))
      (when (pair? ts)
        (display "\\chapter*{Tools of the document}\n")
        (display "\\addcontentsline{toc}{chapter}{Tools of the document}\n")
        (display "\\vnbblock{Shared by results of several chapters (") (display (length ts)) (display "):}\n")
        (lbn--forest ts idom order 1)))))

(define (lbn--write-library lib plan by-place by-group)
  (let* ((order (lbn--plan-ref plan 'order))
         (place (lbn--plan-ref plan 'place))
         (ns (hash-table-ref/default by-place (list 'library lib) '()))
         (files (sort (map cdr (filter (lambda (k) (eq? (car k) lib)) (hash-table-keys by-group)))
                      (lambda (a b) (< (lb--file-position a) (lb--file-position b)))))
         (ord (lambda (l) (sort l (lambda (a b) (< (hash-table-ref/default order a 0)
                                                    (hash-table-ref/default order b 0)))))))
    (display "\\part{") (display (mt--escape-tex (library-title lib))) (display "}\n")
    (display "\\noindent ") (display (mt--escape-tex (library-about lib))) (display "\n")
    ;; definitions, axioms, assumptions, by file
    (display "\\chapter*{Definitions, axioms and assumptions}\n")
    (display "\\addcontentsline{toc}{chapter}{Definitions, axioms and assumptions}\n")
    (for-each
     (lambda (rel)
       (let* ((names (hash-table-ref/default by-group (cons lib rel) '()))
              (entries (filter (lambda (e) (not (eq? (car e) 'proposition)))
                               (lb--file-entries rel names (eq? lib (library-of-file rel))))))
         (when (pair? entries)
           (display "\\vnbbookfile{") (display (mt--escape-tt rel)) (display "}{") (display rel) (display "}\n")
           (for-each (lambda (e) (display (caddr e))) entries)
           (display "\n"))))
     files)
    ;; the theorems the outline does not place
    (let* ((shared (filter (lambda (n) (not (eq? (car (hash-table-ref place n (lambda () '(x))))
                                                 'unattached)))
                           ns))
           (unatt (filter (lambda (n) (eq? (car (hash-table-ref place n (lambda () '(x)))) 'unattached)) ns)))
      (for-each
       (lambda (part)
         (let ((title (car part)) (blurb (cadr part)) (members (caddr part)))
           (when (pair? members)
             (display "\\chapter*{") (display title) (display "}\n")
             (display "\\addcontentsline{toc}{chapter}{") (display title) (display "}\n")
             (display "\\vnbblock{") (display blurb) (display " (") (display (length members)) (display ").}\n")
             (lbn--write-groups lib members order))))
       (list (list "Results shared across documents"
                   "Reached from results of several documents, or from a result of a later library"
                   shared)
             (list "Results not reached from the notes"
                   "Reached from no major result of the notes"
                   unatt))))))

;;; group by principal head (by file for the kernel encoded and the generated laws);
;;; groups in the order of their first member; small groups pooled
(define (lbn--write-groups lib members order)
  (let ((groups (make-equal-hash-table)) (keys '()))
    (for-each (lambda (n)
                (let* ((h (lbn--principal-head n))
                       (key (cond ((eq? lib 'meta) (cons 'file (lbn--rel-of n)))
                                  ((eq? h '<generated>) (cons 'generated (lbn--rel-of n)))
                                  (#t (cons 'head h)))))
                  (if (not (hash-table-ref/default groups key #f)) (set! keys (cons key keys)))
                  (hash-table-update!/default groups key (lambda (l) (cons n l)) '())))
              members)
    (let* ((sorted-members (lambda (key) (sort (hash-table-ref groups key (lambda () '()))
                                               (lambda (a b) (< (hash-table-ref/default order a 0)
                                                                (hash-table-ref/default order b 0))))))
           (first-of (lambda (key) (hash-table-ref/default order (car (sorted-members key)) 0)))
           (keys (sort keys (lambda (a b) (< (first-of a) (first-of b)))))
           (big (filter (lambda (k) (or (not (eq? (car k) 'head))
                                        (>= (length (hash-table-ref groups k (lambda () '()))) lbn--small-group)))
                        keys))
           (small (filter (lambda (k) (not (memq k big))) keys)))
      (for-each
       (lambda (k)
         (display "\\vnbgroup{")
         (display (case (car k)
                    ((file) (string-append "\\texttt{" (mt--escape-tt (or (cdr k) "?")) "}"))
                    ((generated) (string-append "Laws generated with \\texttt{" (mt--escape-tt (or (cdr k) "?")) "}"))
                    (else (if (eq? (cdr k) '<logic/arith>) "Logic and arithmetic"
                              (string-append "\\texttt{" (mt--escape-tt (symbol->string (cdr k))) "}")))))
         (display "}\n")
         (for-each (lambda (n) (display (lbn--prop-tex n 0))) (sorted-members k)))
       big)
      (when (pair? small)
        (display "\\vnbgroup{Other results}\n")
        (for-each (lambda (n) (display (lbn--prop-tex n 0)))
                  (sort (append-map (lambda (k) (hash-table-ref groups k (lambda () '()))) small)
                        (lambda (a b) (< (hash-table-ref/default order a 0) (hash-table-ref/default order b 0)))))))))

;;; the placement as data, one line per theorem: (NAME BUCKET KEY FLOORED? HEAD); for the
;;; regression against the BOOK-SECT prototype and for anyone who wants to query it
(define (lbn--write-placement! plan path)
  (let ((place (lbn--plan-ref plan 'place)) (floored (lbn--plan-ref plan 'floored))
        (idom (lbn--plan-ref plan 'idom)))
    (with-output-to-file (mt--abs-path path)
      (lambda ()
        (display ";; library-book placement (BOOK-GEN): (name bucket key floored idom head)\n")
        (hash-table-walk place
          (lambda (n p)
            (write (list n (car p) (if (pair? (cdr p)) (cdr p) '())
                         (and (hash-table-ref/default floored n #f) #t)
                         (hash-table-ref/default idom n #f)
                         (lbn--principal-head n)))
            (newline)))))))

(define *library-book-table* "docs/major-theorems-table.sexp")

(define (lbn--write-by-notes! out-path)
  (read-libraries-table!)
  (let ((table (mt--read-table *library-book-table*)))
    (if (not table)
        (begin (display ";; library-book: no table of major theorems; writing the book by library\n")
               (lb--write-by-library! out-path))
        (call-with-values lbn--book-theorems
          (lambda (names order by-group)
            (let* ((plan (lbn--plan names order table #f))
                   (titles (lbn--outline-titles (lbn--read-outlines *library-book-table*)))
                   (by-place (lbn--by-place plan))
                   (docs (lbn--uniq (map lbn--e-doc (lbn--plan-ref plan 'entries))))
                   (place (lbn--plan-ref plan 'place))
                   (count (lambda (pred) (let ((k 0)) (hash-table-walk place (lambda (n p) (if (pred n p) (set! k (+ k 1))))) k))))
              (with-output-to-file (mt--abs-path out-path)
                (lambda ()
                  (display "% library-book.tex -- GENERATED by (write-library-book-tex! ...) at load.  Do not hand-edit.\n")
                  (display "% The theorems and definitions of the tree, no proofs, in the outline of the notes\n")
                  (display "% (docs/major-theorems-table.sexp), then one part per library.\n")
                  (display mt--macro-block)
                  (display lb--macro-block)
                  (display lbn--macro-block)
                  (display "\\tableofcontents\n\n")
                  (for-each (lambda (d) (lbn--write-document d plan by-place titles)) docs)
                  (for-each (lambda (lib) (lbn--write-library lib plan by-place by-group)) (library-names))))
              (display ";; library-book: ") (display (length names)) (display " theorems, ")
              (display (length docs)) (display " documents, ") (display (length (library-names)))
              (display " libraries -> ") (display out-path) (newline)
              (display ";;   major ") (display (count (lambda (n p) (eq? (car p) 'major))))
              (display ", owned ") (display (count (lambda (n p) (and (eq? (car p) 'owned)
                                                                       (not (hash-table-ref/default (lbn--plan-ref plan 'floored) n #f))))))
              (display ", tools ") (display (count (lambda (n p) (and (eq? (car p) 'tools)
                                                                       (not (hash-table-ref/default (lbn--plan-ref plan 'floored) n #f))))))
              (display ", to the library parts ") (display (count (lambda (n p) (or (memq (car p) '(foundations unattached))
                                                                                  (hash-table-ref/default (lbn--plan-ref plan 'floored) n #f)))))
              (display " (floored ") (display (length (hash-table-keys (lbn--plan-ref plan 'floored)))) (display ")") (newline)
              (for-each (lambda (w) (display ";;   table: ") (write w) (newline)) (lbn--plan-ref plan 'warnings))
              out-path))))))

;;; THE ENTRY POINT.  LAYOUT 'notes (the default since 2026-11-12) or 'by-library (the
;;; book as it was: one part per library, files in load order).
(define (write-library-book-tex! out-path #!optional layout)
  (if (and (not (default-object? layout)) (eq? layout 'by-library))
      (lb--write-by-library! out-path)
      (lbn--write-by-notes! out-path)))
