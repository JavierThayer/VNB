;;; equal-patch.scm -- MIT/GNU Scheme 12.1's equal? without its per-call hash table.
;;; Change F1 of Ignacio's GC study (mailbox 2026-10-14-f1-f2-speedup.md), approved by
;;; the user 2026-10-15.  It changes no answer of equal? and nothing that is checked.
;;;
;;; MIT 12.1's equal? builds a fresh cycle-detection hash table on EVERY call (about 116
;;; words) before it compares anything.  This file replaces `make-detect-circ' in the
;;; (runtime equality) package by a version that recurses plainly for the first 10000
;;; non-eq node pairs of one call and only then falls back to a memo table of the same
;;; kind as MIT's, so a cyclic argument still terminates and the treatment of numbers,
;;; strings and records (done by equal? itself, not here) is untouched.  Measured on a
;;; full exam of the 2026-10-11 tree, with F2 (wff.scm, wff-equiv?): the same 4708 qed,
;;; the same refusals (none), the same warnings; wall -42%, GC -62%.
;;;
;;; It rewires a runtime INTERNAL by name, so the self-test below ERRORS -- stopping the
;;; load -- when the binding was not replaced, when a cdr-cycle no longer compares equal,
;;; when two different lists compare equal, or when one equal? call still allocates more
;;; than 80 words (unpatched: 116 or more).  A future MIT upgrade that moves the internal
;;; therefore fails loudly instead of silently losing the patch.
;;;
;;; FIRST in *vnb-files* (load.scm), so every later file runs with it; a band carries it.
;;; Everything is local: the file defines no top-level name.
(let* ((env (->environment '(runtime equality)))
       (orig (environment-lookup env 'make-detect-circ))
       (make-ht (hash-table-constructor
                 (make-pair-comparator eq-comparator eq-comparator))))
  (environment-assign!
   env 'make-detect-circ
   (lambda (continue)
     (let ((n 0) (ht #f))
       (lambda (x y)
         (if (fix:< n 10000)
             (begin (set! n (fix:+ n 1)) (continue x y))
             (begin
               (if (not ht) (set! ht (make-ht)))
               (let ((key (cons x y)))
                 (hash-table-ref ht key
                                 (lambda ()
                                   (hash-table-set! ht key #t)
                                   (let ((v (continue x y)))
                                     (hash-table-set! ht key v)
                                     v))
                                 (lambda (v) v)))))))))
  (let* ((now (environment-lookup env 'make-detect-circ))
         (cyc (lambda () (let ((l (list 1 2 3))) (set-cdr! (cddr l) l) l)))
         (heap-used (lambda () (let ((v (gc-space-status)))
                                 (quotient (- (vector-ref v 5) (vector-ref v 4)) 8))))
         (words (begin (gc-flip)
                       (let ((h0 (heap-used)))
                         (equal? 'f1-probe 'f1-probe)
                         (- (heap-used) h0))))
         (cyc-ok (equal? (cyc) (cyc)))
         (diff-ok (not (equal? '(a (b 1)) '(a (b 2))))))
    (display ";; equal-patch: make-detect-circ replaced=") (display (not (eq? now orig)))
    (display " words-per-equal?=") (display words)
    (display " cdr-cycle-equal?=") (display cyc-ok)
    (display " acyclic-diff=") (display diff-ok)
    (newline)
    (if (or (eq? now orig) (> words 80) (not cyc-ok) (not diff-ok))
        (error "equal-patch: the equal? patch is NOT in effect (see the line above)"))))
