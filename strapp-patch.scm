;;; strapp-patch.scm -- MIT/GNU Scheme 12.1's string-append without its two 1024-slot
;;; builder buffers per call.  Change F14 of Ignacio's GC study (mailbox
;;; 2026-10-16-f14-f15-next-steps.md), approved by the user 2026-10-16.  It changes no
;;; answer of string-append and nothing that is checked.
;;;
;;; MIT 12.1's string-append (runtime string.scm:1459-1461) runs %string-concatenate
;;; twice, discarding the first result, and each run makes a string-builder whose reset!
;;; allocates (make-vector 1024): about 2180 heap words per call however short the
;;; operands; the formula printer makes about 25 calls per formula.  The replacement
;;; (strapp-fast.scm, COMPILED and loaded into the (runtime string) environment) makes
;;; one pass for the length and the widest code point, then calls the same allocator
;;; (immutable-ustring-allocate) and the same copier (%general-copy!) MIT uses.
;;; Measured by Ignacio on a full laptop exam with F1 and F2: wall 7988 -> 4837 s, GC
;;; 1127 -> 188 s, the same outputs; a differential exam (both procedures on every call,
;;; VNB_P_DIFF=1) found no difference in content, length, code-point width, NFC/NFD
;;; flags or immutability.
;;;
;;; The self-test at the end ERRORS -- stopping the load -- when the binding was not
;;; replaced, when the replacement differs from the original on any of its 29 cases or
;;; in its error report on a non-string operand.  VNB_P_REQUIRE_COMPILED=1 also makes an
;;; interpreted replacement (strapp-fast.com missing or stale) an error.  It prints one
;;; ";;P" line.  Restore with (uninstall-fast-string-append!).
;;;
;;; THIRD in *vnb-files* (load.scm), after equal-patch; a band carries it.  Compile
;;; strapp-fast.scm with compile-file after any edit; sf/cf warn about its free
;;; variables (unpack-slice, %general-copy!, ...), which bind in (runtime string) at load.
;;; Ignacio's files were strapp.scm (installer) and p-preload.scm (self-test); they are
;;; joined here verbatim except that the replacement is found beside this file.

(define strapp--fast-path
  (merge-pathnames "strapp-fast" (directory-pathname (current-load-pathname))))

;;; P: allocation-light string-append for MIT/GNU Scheme 12.1 (GC study 2026-10-14).
;;; NOT RUN when written; every runtime name below is cited against
;;; mit-scheme-12.1/src/runtime/string.scm (S) unless stated otherwise.
;;;
;;; Original (S:1459-1461): (string-append . strings) calls %string-concatenate
;;; (S:1466-1472) TWICE (once discarded); each call makes a (string-builder)
;;; (S:590-597 -> %make-string-builder S:648-656 reset! = (make-vector 1024)).
;;; Result = (build-string:immutable chars count max-cp) (S:620-621)
;;;        = (fill-result! chars count (immutable-ustring-allocate count max-cp)).
;;; The replacement itself lives in strapp-fast.scm and is COMPILED (cf) and
;;; loaded into the (runtime string) package env, so it runs as compiled code.
;;; Compile first: cd scripts && mit-scheme --quiet --eval '(begin (cf "strapp-fast") (exit))'
;;; Replacement: one pass for total length + max-cp, then the SAME allocator
;;; (immutable-ustring-allocate, S:227-243) and %general-copy! (S:452).
;;;
;;; Names defined with plain `define` in S (so they exist as variables in the
;;; (runtime string) environment; define-integrable ones such as ustring-length
;;; S:117, %ustring-flags, ustring?, slice-string do NOT, and are not used):
;;;   immutable-ustring-allocate S:227   unpack-slice S:315 (integrate-operator
;;;   declared but still `define`d)      %general-max-cp S:560
;;;   %general-copy! S:452   string-length S:344   string? S:330
;;;   ustring-cp-size S:275 (note: no leading %; handles legacy strings)
;;;   ustring-in-nfc? S:151  ustring-in-nfc-set? S:152  ustring-in-nfd? S:153
;;;   %string-immutable? S:75 (string fail-thunk)
;;;   guarantee: boot.scm:222 ; error:not-a boot.scm:228

;;; Shared state lives in system-global-environment so that the package env and
;;; the user env see the same objects.  Not guarded by `define` at load time, so
;;; reloading this file does not overwrite the saved original with the replacement.
(define (strapp--global-define! name value)
  (environment-define system-global-environment name value))

(if (not (environment-bound? system-global-environment 'strapp--orig-string-append))
    (strapp--global-define!
     'strapp--orig-string-append
     (environment-lookup (->environment '(runtime string)) 'string-append)))
(if (not (environment-bound? system-global-environment 'strapp--calls-cell))
    (strapp--global-define! 'strapp--calls-cell (make-cell 0)))
(if (not (environment-bound? system-global-environment 'strapp--diffs-cell))
    (strapp--global-define! 'strapp--diffs-cell (make-cell 0)))

(define (strapp-calls) (cell-contents strapp--calls-cell))
(define (strapp-diffs) (cell-contents strapp--diffs-cell))
(define (strapp-reset-counters!)
  (set-cell-contents! strapp--calls-cell 0)
  (set-cell-contents! strapp--diffs-cell 0))

;;; Set by install-fast-string-append!: #t iff the installed procedure is compiled.
(define strapp--compiled? #f)

(define (install-fast-string-append! #!optional differential?)
  (let* ((env (->environment '(runtime string)))
         (diff? (and (not (default-object? differential?)) differential? #t)))
    ;; Explicit environment: defines strapp--make-string-append in (runtime string).
    ;; Picks strapp-fast.com if it is newer than strapp-fast.scm, else the source
    ;; (then the result is interpreted; p-preload reports compiled=#f).
    (load strapp--fast-path env)
    (let* ((maker (environment-lookup env 'strapp--make-string-append))
           (proc (maker strapp--orig-string-append diff?
                        strapp--calls-cell strapp--diffs-cell)))
      (set! strapp--compiled? (compiled-procedure? proc))
      (environment-assign! env 'string-append proc)
      proc)))

(define (uninstall-fast-string-append!)
  (environment-assign! (->environment '(runtime string)) 'string-append
                       strapp--orig-string-append))

;;; ---- self-test (Ignacio's p-preload.scm) ----
(let* ((env (->environment '(runtime string)))
       (orig (environment-lookup env 'string-append))
       (diff? (equal? (get-environment-variable "VNB_P_DIFF") "1"))
       (heap-used (lambda () (let ((v (gc-space-status))) ; as f1-preload.scm
                               (quotient (- (vector-ref v 5) (vector-ref v 4)) 8))))
       ;; words used by one call of thunk, minus the cost of calling an empty thunk
       ;; (the interpreter's own frames) measured the same way.
       (raw-words (lambda (thunk)
                    (gc-flip)
                    (let ((h0 (heap-used)))
                      (thunk)
                      (- (heap-used) h0))))
       (words (lambda (thunk)
                (raw-words thunk)               ; warm-up
                (- (raw-words thunk) (raw-words (lambda () #f)))))
       (words-orig (words (lambda () (orig "abc" "de" "f")))))
  (if (not (eq? orig strapp--orig-string-append))
      (error "P: saved original is not the current cell value (already installed?)"))
  (install-fast-string-append! diff?)
  (let* ((now (environment-lookup env 'string-append))
         (words-new (words (lambda () (string-append "abc" "de" "f"))))
         (cp-size (environment-lookup env 'ustring-cp-size))   ; S:275
         (nfc? (environment-lookup env 'ustring-in-nfc?))      ; S:151
         (nfc-set? (environment-lookup env 'ustring-in-nfc-set?))
         (nfd? (environment-lookup env 'ustring-in-nfd?))      ; S:153
         (imm? (environment-lookup env '%string-immutable?))   ; S:75
         (compiled? (compiled-procedure? now))
         (alpha (string (integer->char #x3b1)))
         (emoji (string (integer->char #x1F600)))
         (ascii "hello")
         (legacy (make-legacy-string 3 #\q))   ; legacy-string.scm:40
         (mutable (make-string 3 #\m))         ; cp-size 0 (S:222, mutable-ustring-allocate)
         (sliced (string-slice "abcdef" 1 3))  ; S:377
         (cases (list '()
                      (list ascii)
                      (list "abc" "de" "f")
                      (list alpha)
                      (list ascii alpha ascii)
                      (list emoji)
                      (list ascii emoji alpha)
                      (list legacy)
                      (list legacy ascii legacy)
                      (list legacy alpha)
                      (list "" "")
                      (list "" ascii "")
                      (list sliced)
                      (list sliced ascii sliced)
                      (list (string-slice (string #\a alpha #\b) 1 2) sliced)   ; real slice (a whole-string slice would return the string itself)
                      (list mutable ascii)
                      (list mutable alpha emoji)
                      (list (string-slice legacy 1 3) ascii)
                      ;; max-cp thresholds #xC0 #x100 #x300 #x10000 (S:227-243)
                      (list (string (integer->char #xBF)))
                      (list (string (integer->char #xC0)))
                      (list (string (integer->char #xFF)))
                      (list (string (integer->char #x100)))
                      (list (string (integer->char #x2FF)))
                      (list (string (integer->char #x300)))
                      (list (string (integer->char #xFFFF)))
                      (list (string (integer->char #x10000)))
                      (list ascii (string (integer->char #xFF)) (string (integer->char #x300)))
                      (list (make-string 0))
                      (list (string-slice emoji 0 0) ascii))) ; empty slice
         (same? (lambda (a b)
                  (and (string=? a b)
                       (= (string-length a) (string-length b))
                       (= (cp-size a) (cp-size b))
                       (eq? (nfc? a) (nfc? b))
                       (eq? (nfc-set? a) (nfc-set? b))
                       (eq? (nfd? a) (nfd? b))
                       (eq? (imm? a (lambda () 'x)) (imm? b (lambda () 'x))))))
         ;; non-string operand: same condition report from both (caller, irritant)
         (report (lambda (thunk)
                   (call-with-current-continuation
                    (lambda (k)
                      (with-exception-handler
                       (lambda (e) (k (if (condition? e) (condition/report-string e) 'non-condition)))
                       thunk)))))
         (errors-same? (equal? (report (lambda () (apply orig (list "a" 5 "b"))))
                               (report (lambda () (string-append "a" 5 "b")))))
         (all-same? (let loop ((cs cases))
                      (or (null? cs)
                          (and (same? (apply orig (car cs))
                                      (apply string-append (car cs)))
                               (loop (cdr cs)))))))
    (display ";;P string-append replaced=") (display (not (eq? now orig)))
    (display " mode=") (display (if diff? "diff" "plain"))
    (display " compiled=") (display compiled?)
    (display " from=")
    (write (if compiled?
               (receive (f i . r) (compiled-entry/filename-and-index now) f)
               #f))
    (display " words-per-call=") (display words-new)
    (display " words-per-call-orig=") (display words-orig)
    (display " result-eq-orig=") (display all-same?)
    (display " error-eq-orig=") (display errors-same?)
    (newline)
    (if (eq? now orig) (error "P NOT INSTALLED"))
    (if (and (equal? (get-environment-variable "VNB_P_REQUIRE_COMPILED") "1")
             (not compiled?))
        (error "P NOT COMPILED (run cf on strapp-fast.scm first)"))
    (if (not all-same?) (error "P result differs from original"))
    (if (not errors-same?) (error "P error report differs from original"))))
