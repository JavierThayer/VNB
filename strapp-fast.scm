;;; Maker for patch P's replacement string-append (GC study 2026-10-14).
;;; NOT RUN when written.  Compile with (from this directory):
;;;   cd scripts && mit-scheme --quiet --eval '(begin (cf "strapp-fast") (exit))'
;;; This produces strapp-fast.com (+ .bci/.bin); strapp.scm loads it with
;;; (load ".../strapp-fast" <(runtime string) environment>), and `load` prefers
;;; the .com when it is newer than the .scm.  Compiled code resolves its free
;;; variables in the environment it is LOADED into, so unpack-slice,
;;; %general-copy!, %general-max-cp, immutable-ustring-allocate, ustring-cp-size,
;;; ustring-in-nfc?, ustring-in-nfc-set?, ustring-in-nfd?, %string-immutable?
;;; and guarantee all bind to (runtime string) at load time.  sf/cf will WARN
;;; about these free variables (unbound at compile time): that is expected.
;;;
;;; Deliberately NO (declare (usual-integrations)): we do not want string? and
;;; string-length open-coded as the legacy-string primitives; they must be the
;;; (runtime string) procedures, which also handle ustrings and slices.
;;; fix:+ / fix:- / fix:= / fix:max are fine either way.
;;;
;;; Counters are passed in as cells (make-cell / cell-contents /
;;; set-cell-contents!, boot.scm:252) rather than set! on globals, so nothing
;;; depends on the environment chain.  Nothing here calls string-append.
;;; orig = saved original; diff? = #t for differential mode.
(define (strapp--make-string-append orig diff? calls-cell diffs-cell)
  ;; fast: strings is the rest list.  Pass 1 = same checks and same error
  ;; as S:1466-1472 (guarantee string? s 'string-append, per argument, in order).
  (define (fast strings)
    (let loop ((l strings) (n 0) (mx 0))
      (if (pair? l)
          (let ((s (car l)))
            (guarantee string? s 'string-append)
            (loop (cdr l)
                  (fix:+ n (string-length s))
                  (fix:max mx (unpack-slice s %general-max-cp))))
          ;; Same allocator + flags as build-string:immutable (S:620-621).
          (let ((result (immutable-ustring-allocate n mx)))
            (let copy ((l strings) (at 0))
              (if (pair? l)
                  (copy (cdr l)
                        ;; modelled on string->immutable (S:576-587)
                        (unpack-slice (car l)
                          (lambda (s* start end)
                            (%general-copy! result at s* start end)
                            (fix:+ at (fix:- end start)))))
                  result))))))
  (define (same? a b)
    (and (string=? a b)
         (fix:= (string-length a) (string-length b))
         (fix:= (ustring-cp-size a) (ustring-cp-size b))
         (eq? (ustring-in-nfc? a) (ustring-in-nfc? b))
         (eq? (ustring-in-nfc-set? a) (ustring-in-nfc-set? b))
         (eq? (ustring-in-nfd? a) (ustring-in-nfd? b))
         (eq? (%string-immutable? a (lambda () 'bad))
              (%string-immutable? b (lambda () 'bad)))))
  (if diff?
      (lambda strings
        (set-cell-contents! calls-cell (fix:+ (cell-contents calls-cell) 1))
        (let* ((old (apply orig strings))   ; original: errors first, as plain would
               (new (fast strings)))
          (if (not (same? old new))
              (begin
                (set-cell-contents! diffs-cell (fix:+ (cell-contents diffs-cell) 1))
                (error "P-DIFF mismatch" 'operands strings 'orig old 'new new)))
          new))
      (lambda strings (fast strings))))
