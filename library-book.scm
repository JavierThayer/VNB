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

(define (lb--file-position rel)
  (let loop ((fs *vnb-files*) (i 0))
    (cond ((null? fs) 100000)
          ((and (string? (car fs)) (string=? (car fs) rel)) i)
          (else (loop (cdr fs) (+ i 1))))))

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
                           (else (loop (cdr is)))))))
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
                                     (tier (cond ((pair? w) (car w)) (w w) (else 'none))))
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

(define (write-library-book-tex! out-path)
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
