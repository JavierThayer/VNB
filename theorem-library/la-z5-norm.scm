;;; la-z5-norm.scm -- linear algebra 3.41 (second sentence) and the norm N_E(F) as an
;;; object (LA-Z5, 2026-10-25).  Prefix lz5n-.
;;;
;;; THE THEOREMS.
;;;  (1) free-generating-length-unique (3.41, second sentence): over a euclidean scalar
;;;      ring, two free generating sequences of one module have the same length -- two
;;;      applications of free-length-le-generators (the first sentence).
;;;  (2) norm-data-det-unique: two IS-NORM-DATA presentations of F in E give the same
;;;      |det| -- the lengths agree by (1), then 3.45 (norm-independent).
;;;  (3) submodule-norm-value: N_E(F) = |det am| for any IS-NORM-DATA(md, sm, n, xs, ys, am).
;;;  (4) submodule-norm-zero: N_E(F) = 0 when no such data exist.
;;;
;;; Destination theorem-library/.  Library: linear-algebra.  LOAD WINDOW: after
;;; structure-library/la-z5-vocab and theorem-library/la-z2-norm (norm-independent,
;;; load.scm 2190); free-length-le-generators is earlier (rake-asm-b4).  Nothing in the
;;; tree cites the file.

(define (lz5n-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-z5-norm: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display ";;      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))))
  (qed name)
  (topic! name 'algebra))
(define (lz5n-open! name . args)
  (let* ((hyp (cons name args))
         (ignore (apply fact name args))
         (iff (iff-for hyp))
         (rhs (caddr iff)))
    (dk-have! rhs (dk-lane (lambda () (dk-only! iff hyp) (dk-lane-if! prop))))
    (let loop ((todo (list (dk-ctx-form rhs))) (acc '()))
      (cond ((null? todo) (reverse acc))
            ((dk-head-is? (car todo) 'AND) (loop (append (dk-split! (car todo)) (cdr todo)) acc))
            (#t (loop (cdr todo) (cons (car todo) acc)))))))
(define (lz5n-detach-all! inst)
  (let loop ((f inst))
    (if (and (pair? f) (eq? (car f) 'IMPLIES))
        (let ((a (cadr f)))
          (if (not (dk-asm? a)) (dk-have! a (dk-lane (lambda () (dk-lane-if! prop)))))
          (loop (if (dk-asm? (caddr f)) (dk-ctx-form (caddr f))
                    (dk-landed-1 (lambda () (detach! f))))))
        f)))
(define (lz5n-cite! thm . args) (lz5n-detach-all! (apply dk-cite! thm args)))
(define (lz5n-skolem-all! ex)
  (let loop ((ex ex) (acc '()))
    (let* ((v #f)
           (landed (dk-landed (lambda () (set! v (dk-skolem! ex)))))
           (nxt (find-first (dk-head? 'FORSOME) landed)))
      (if nxt (loop nxt (append acc (list v))) (append acc (list v))))))
(define (lz5n-split-all-on! w)
  (let loop ()
    (let ((cj (find-first (lambda (f) (and (dk-head-is? f 'AND) (dk-contains? f w))) (dk-asms))))
      (if cj (begin (dk-split! cj) (loop))))))

;;; ---- (1) 3.41, second sentence ----------------------------------------------------
(sp (make-wff (forall-guarded '(md) '((IS-MODULE md) (IS-EUCLIDEAN-RING (SCAL md)))
  (forall-guarded '(n m u v)
    '((IN n NN) (IN m NN) (IN u (MAT n 1 (VEC md))) (IN v (MAT m 1 (VEC md)))
      (GENERATES md n u) (REL-FREE md n u) (GENERATES md m v) (REL-FREE md m v))
    '(= m n)))))
(dk-peel!)
(lz5n-cite! 'free-length-le-generators 'md 'n 'm 'u 'v)
(lz5n-cite! 'free-length-le-generators 'md 'm 'n 'v 'u)
(lz5n-cite! (quote nn-le-antisym) (quote m) (quote n))
(if (not (proof-done? *ps*)) (ass))
(lz5n-done! 'free-generating-length-unique)
(gloss! 'free-generating-length-unique "Linear algebra 3.41, second sentence: over a euclidean scalar ring all free generating sequences of a module have the same length.")

;;; ---- (2) the |det| of two presentations agree ---------------------------------------
(define LZ5N-ZH '((IS-MODULE md) (= (SCAL md) ZZ-RING)))
(sp (make-wff (forall-guarded '(md) LZ5N-ZH
  (forall-guarded '(sm n xs ys am n2 xs2 ys2 am2)
    '((IS-NORM-DATA md sm n xs ys am) (IS-NORM-DATA md sm n2 xs2 ys2 am2))
    '(= (abs (DET ZZ-RING n2 am2)) (abs (DET ZZ-RING n am)))))))
(dk-peel!)
(lz5n-open! 'IS-NORM-DATA 'md 'sm 'n 'xs 'ys 'am)
(lz5n-open! 'IS-NORM-DATA 'md 'sm 'n2 'xs2 'ys2 'am2)
(fact 'zz-is-euclidean-ring)
(dk-have! '(IS-EUCLIDEAN-RING (SCAL md)) (lambda () (subst '(= (SCAL md) ZZ-RING)) (ass)))
(lz5n-cite! 'free-generating-length-unique 'md 'n 'n2 'xs 'xs2)
(for-each (lambda (f) (dk-rewrite-h! f 'n2 'n))
          (list '(IN xs2 (MAT n2 1 (VEC md))) '(GENERATES md n2 xs2) '(REL-FREE md n2 xs2)
                '(IN ys2 (MAT n2 1 (VEC md))) '(SPANS md n2 ys2 sm) '(REL-FREE md n2 ys2)
                '(IN am2 (MAT n2 n2 ZZ))))
(subst '(= n2 n))
(lz5n-cite! 'norm-independent 'md 'n 'xs 'xs2 'ys 'ys2 'sm 'am 'am2)
(ass)
(lz5n-done! 'norm-data-det-unique)
(gloss! 'norm-data-det-unique "Linear algebra 3.45 with 3.41: any two presentations of a submodule F of rank n in a free Z-module E of rank n give the same absolute determinant.")

;;; ---- (3), (4): the value of N_E(F) ---------------------------------------------------
(define LZ5N-EX '(FORSOME nmn_ (FORSOME nmx_ (FORSOME nmy_ (FORSOME nma_ (IS-NORM-DATA md sm nmn_ nmx_ nmy_ nma_))))))
(define (lz5n-ift) (find-first (lambda (f) #t) (list (cadr (dk-goal)))))
(sp (make-wff (forall-guarded '(md sm) (list (list 'NOT LZ5N-EX))
  '(= (SUBMODULE-NORM md sm) 0))))
(dk-peel!)
(mac 'SUBMODULE-NORM)
(dk-if-branch! #f (cadr (dk-goal)) #f (lambda () (if (not (proof-done? *ps*)) (rfl))))
(lz5n-done! 'submodule-norm-zero)
(gloss! 'submodule-norm-zero "The norm N_E(F) is 0 when F has no relation-free spanning sequence as long as a free generating sequence of E.")

(sp (make-wff (forall-guarded '(md) LZ5N-ZH
  (forall-guarded '(sm n xs ys am) '((IS-NORM-DATA md sm n xs ys am))
    '(= (SUBMODULE-NORM md sm) (abs (DET ZZ-RING n am)))))))
(dk-peel!)
(define LZ5N-ABS '(abs (DET ZZ-RING n am)))
(define (lz5n-eq-close! e)
  (if (dk-asm? (dk-goal)) (ass) (begin (subst e) (if (not (proof-done? *ps*)) (if (dk-asm? (dk-goal)) (ass) (rfl))))))
(let* ((parts (lz5n-open! 'IS-NORM-DATA 'md 'sm 'n 'xs 'ys 'am)))
  (fact 'zz-is-commutative-ring)
  (fact 'zz-is-ring)
  (dk-have! '(== (CARR ZZ-RING) ZZ) (lambda () (slot 'CARR) (qrfl)))
  (dk-rewrite-h! '(IN am (MAT n n ZZ)) 'ZZ '(CARR ZZ-RING))
  (lz5n-cite! 'det-in-carrier 'ZZ-RING 'n 'am)
  (dk-rewrite-h! '(IN (DET ZZ-RING n am) (CARR ZZ-RING)) '(CARR ZZ-RING) 'ZZ)
  (lz5n-cite! 'zz-abs-in-nn '(DET ZZ-RING n am)))
(mac 'SUBMODULE-NORM)
(define LZ5N-IF (cadr (dk-goal)))
(define LZ5N-IOTA (caddr LZ5N-IF))
(dk-if-branch! #t LZ5N-IF
  (lambda () (ew 'n) (ew 'xs) (ew 'ys) (ew 'am) (ass))
  (lambda ()
    (let ((opened (dk-opened (lambda () (iota-d LZ5N-IOTA)))))
      (for-each
        (lambda (l)
          (dk-focus! l)
          (if (dk-head-is? (dk-goal) 'FORSOME)
              ;; existence and uniqueness
              (begin
                (ew LZ5N-ABS)
                (dk-conj-close!
                  (lambda ()
                    (let ((g (dk-goal)))
                      (cond ((dk-head-is? g 'FORSOME)
                             (ew 'n) (ew 'xs) (ew 'ys) (ew 'am)
                             (dk-conj-close! (lambda () (if (dk-asm? (dk-goal)) (ass) (rfl)))))
                            (#t
                             (let* ((ld (dk-peel!))
                                    (ex (find-first (dk-head? 'FORSOME) ld))
                                    (ws (lz5n-skolem-all! ex)))
                               (for-each lz5n-split-all-on! ws)
                               (let ((eq (find-first (lambda (f) (and (dk-head-is? f '=) (dk-contains? f (car ws))
                                                                      (dk-contains? f 'abs))) (dk-asms))))
                                 (subst (list '= (cadr eq) (caddr eq)))
                                 (lz5n-eq-close! (apply lz5n-cite! 'norm-data-det-unique 'md 'sm 'n 'xs 'ys 'am ws))))))))))
              ;; the main leaf: the defining property of the IOTA term
              (let* ((p (find-first (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f LZ5N-IOTA))) (dk-asms)))
                     (ws (lz5n-skolem-all! p)))
                (for-each lz5n-split-all-on! ws)
                (let ((eq (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) LZ5N-IOTA))) (dk-asms))))
                  (subst (list '= (cadr eq) (caddr eq)))
                  (lz5n-eq-close! (apply lz5n-cite! 'norm-data-det-unique 'md 'sm 'n 'xs 'ys 'am ws))))))
        opened))))
(lz5n-done! 'submodule-norm-value)
(gloss! 'submodule-norm-value "The norm N_E(F) is |det A| for any free generating sequence u of E and relation-free sequence v spanning F of the same length with v = A . u.")
