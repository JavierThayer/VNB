;;; zz-pow-via-ring-pow.scm -- wave of 2026-11-09/10 (agent CCR-1109-E2), wired 2026-11-10 from scratchpad/ccr1109e2/zz-pow-via-ring-pow.scm.
;;; Library: linear-algebra.

;;; zz-pow-via-ring-pow.scm -- Z^n as the instance R = ZZ-RING of R^n: the eighteen laws of section (C) of
;;; theorem-library/la-z4-free.scm re-derived from theorem-library/ring-pow.scm (CCR-1109-E2, 2026-11-09;
;;; CCR-1109-E finding F3).  Prefix zvr-.
;;;
;;; DECLARED ALTERNATIVES (the many-versions rule): each theorem NAME-via-ring-pow states, literally, the
;;; statement of the la-z4-free theorem NAME and proves it by one citation of the generic ring-pow law at
;;; ZZ-RING, after the three bridges
;;;   zz-pow-is-ring-pow     ZZ-POW(n) == RING-POW(ZZ-RING, n)
;;;   zz-units-is-ring-units ZZ-UNITS(n) == RING-UNITS(ZZ-RING, n)
;;;   zz-row-is-ring-row     ZZ-ROW(n, x) == RING-ROW(ZZ-RING, n, x)
;;; (each two unfolds and an alpha-aware qrfl).  The originals are NOT replaced; the proven-duplicate-audit
;;; will pair each NAME with NAME-via-ring-pow, and the pairs belong on its declared-exception list with the
;;; route note "instance of the RING-POW law at ZZ-RING".
;;;
;;; Destination theorem-library/zz-pow-via-ring-pow.scm.  Library: linear-algebra.  LOAD WINDOW: after
;;; theorem-library/ring-pow (CCR-1109-E) and theorem-library/la-z4-free; nothing cites this file.
;;; No support, warrant or stamp.

(define (zvr-done! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l)
                  (display ";; zvr OPEN: ") (display (expression->string (dk-goal-of l))) (newline)
                  (for-each (lambda (a) (display ";;      | ") (display (expression->string a)) (newline))
                            (let ((as (dk-asms-of l))) (list-head as (min 25 (length as))))))
                (dk-open-leaves)))
  (qed name)
  (topic! name 'algebra))

(sp (make-wff '(FORALL n (== (ZZ-POW n) (RING-POW ZZ-RING n)))))
(di) (mac 'ZZ-POW) (mac 'RING-POW) (qrfl)
(zvr-done! 'zz-pow-is-ring-pow)
(sp (make-wff '(FORALL n (== (ZZ-UNITS n) (RING-UNITS ZZ-RING n)))))
(di) (mac 'ZZ-UNITS) (mac 'RING-UNITS) (qrfl)
(zvr-done! 'zz-units-is-ring-units)
(sp (make-wff '(FORALL n (FORALL x (== (ZZ-ROW n x) (RING-ROW ZZ-RING n x))))))
(di) (mac 'ZZ-ROW) (mac 'RING-ROW) (qrfl)
(zvr-done! 'zz-row-is-ring-row)

;; the rewrites ZZ-POW, ZZ-UNITS, ZZ-ROW -> the RING-POW forms, ZZ -> CARR ZZ-RING
(define (zvr-pairs f)
  (let loop ((t f) (acc '()))
    (cond ((not (pair? t)) acc)
          ((and (eq? (car t) 'ZZ-POW) (= (length t) 2))
           (cons (cons t (list 'RING-POW 'ZZ-RING (cadr t))) acc))
          ((and (eq? (car t) 'ZZ-UNITS) (= (length t) 2))
           (cons (cons t (list 'RING-UNITS 'ZZ-RING (cadr t))) acc))
          ((and (eq? (car t) 'ZZ-ROW) (= (length t) 3))
           (cons (cons t (list 'RING-ROW 'ZZ-RING (cadr t) (caddr t))) (loop (caddr t) acc)))
          (#t (loop (cdr t) (loop (car t) acc))))))
(define (zvr-bridges! f)                 ; land the bridge instances for the terms of F
  (for-each (lambda (p)
              (let ((t (car p)))
                (cond ((eq? (car t) 'ZZ-POW) (dk-cite! 'zz-pow-is-ring-pow (cadr t)))
                      ((eq? (car t) 'ZZ-UNITS) (dk-cite! 'zz-units-is-ring-units (cadr t)))
                      (#t (dk-cite! 'zz-row-is-ring-row (cadr t) (caddr t))))))
            (zvr-pairs f)))
(define (zvr-all-pairs f) (append (zvr-pairs f) (if (dk--occurs? 'ZZ f) (list (cons 'ZZ '(CARR ZZ-RING))) '())))
(define (zvr-norm-h! f)
  (let loop ((f f) (ps (zvr-all-pairs f)))
    (cond ((null? ps) f)
          ((dk--occurs? (car (car ps)) f) (loop (dk-rewrite-h! f (car (car ps)) (cdr (car ps))) (cdr ps)))
          (#t (loop f (cdr ps))))))
(define (zvr-norm-goal!)
  (for-each (lambda (p) (if (dk--occurs? (car p) (dk-goal)) (subst (list '= (car p) (cdr p)))))
            (zvr-all-pairs (dk-goal))))

;; one alternative: NAME's statement STMT, proved by LAW at ZZ-RING and the arguments ARGS
(define (zvr-alt! name stmt law args)
  (sp (make-wff stmt))
  (let ((ld (dk-peel!)))
    (fact 'zz-is-ring)
    (if (not (dk-asm? '(== (CARR ZZ-RING) ZZ)))
        (dk-have! '(== (CARR ZZ-RING) ZZ) (lambda () (slot 'CARR) (qrfl))))
    (for-each zvr-bridges! ld)
    (zvr-bridges! (dk-goal))
    (for-each (lambda (f) (if (pair? (zvr-all-pairs f)) (zvr-norm-h! f))) ld)
    (zvr-norm-goal!)
    (apply dk-cite! law 'ZZ-RING args)
    (ass))
  (zvr-done! (symbol-append name '-via-ring-pow)))

;; la-z4-free's statement vocabulary, literally
(define ZVR-ZFAM '(VNB-LAMBDA zpi_ (INTERVAL 1 n) (RING-AS-MODULE ZZ-RING)))
(define ZVR-DSZ (list 'DIRECT-SUM 'ZZ-RING 'n ZVR-ZFAM))
(define (zvr-unit k) (list 'VNB-LAMBDA 'zut_ '(INTERVAL 1 n) (list 'ENTRY (list 'UNITROW 'ZZ-RING 'n k) 1 'zut_)))
(define ZVR-ZHM (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ (INTERVAL 1 n)) (list 'IS-MODULE (list ZVR-ZFAM 'i_)))))
(define ZVR-ZHS (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ (INTERVAL 1 n)) (list '= (list 'SCAL (list ZVR-ZFAM 'i_)) 'ZZ-RING))))
(define ZVR-ZRL '(LINCOMB (ZZ-POW n) n (ZZ-ROW n x) (ZZ-UNITS n)))

(zvr-alt! 'zz-pow-unfold (list 'FORALL 'n (list '== '(ZZ-POW n) ZVR-DSZ)) 'ring-pow-unfold '(n))
(zvr-alt! 'zz-pow-family (forall-guarded '(n) '((IN n NN)) (list 'AND ZVR-ZHM ZVR-ZHS)) 'ring-pow-family '(n))
(zvr-alt! 'zz-pow-is-module (forall-guarded '(n) '((IN n NN)) '(IS-MODULE (ZZ-POW n))) 'ring-pow-is-module '(n))
(zvr-alt! 'zz-pow-scal (forall-guarded '(n) '((IN n NN)) '(= (SCAL (ZZ-POW n)) ZZ-RING)) 'ring-pow-scal '(n))
(zvr-alt! 'zz-pow-vec-in (forall-guarded '(n x) '((IN n NN) (IN x (FUN (INTERVAL 1 n) ZZ))) '(IN x (VEC (ZZ-POW n))))
          'ring-pow-vec-in '(n x))
(zvr-alt! 'zz-pow-vec-out (forall-guarded '(n x i) '((IN n NN) (IN x (VEC (ZZ-POW n))) (IN i (INTERVAL 1 n))) '(IN (x i) ZZ))
          'ring-pow-vec-out '(n x i))
(zvr-alt! 'zz-pow-ext (forall-guarded '(n x y) '((IN n NN) (IN x (VEC (ZZ-POW n))) (IN y (VEC (ZZ-POW n)))
                                                 (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 n)) (= (x i_) (y i_)))))
                                      '(= x y))
          'ring-pow-ext '(n x y))
(zvr-alt! 'zz-pow-vzero-at (forall-guarded '(n i) '((IN n NN) (IN i (INTERVAL 1 n))) '(= ((VZERO (ZZ-POW n)) i) (ZERO ZZ-RING)))
          'ring-pow-vzero-at '(n i))
(zvr-alt! 'zz-unit-vec (forall-guarded '(n k) '((IN n NN)) (list 'IN (zvr-unit 'k) '(VEC (ZZ-POW n)))) 'ring-unit-vec '(n k))
(zvr-alt! 'zz-units-type (forall-guarded '(n) '((IN n NN)) '(IN (ZZ-UNITS n) (MAT n 1 (VEC (ZZ-POW n))))) 'ring-units-type '(n))
(zvr-alt! 'zz-units-entry (forall-guarded '(n k) '((IN n NN) (IN k (INTERVAL 1 n))) (list '= '(ENTRY (ZZ-UNITS n) k 1) (zvr-unit 'k)))
          'ring-units-entry '(n k))
(zvr-alt! 'zz-unit-at (forall-guarded '(n k i) '((IN n NN) (IN i (INTERVAL 1 n)))
                        (list '= (list (zvr-unit 'k) 'i) '(ENTRY (UNITROW ZZ-RING n k) 1 i)))
          'ring-unit-at '(n k i))
(zvr-alt! 'zz-pow-lincomb-at (forall-guarded '(n c i) '((IN n NN) (IN c (MAT 1 n (CARR ZZ-RING))) (IN i (INTERVAL 1 n)))
                               '(= ((LINCOMB (ZZ-POW n) n c (ZZ-UNITS n)) i) (ENTRY c 1 i)))
          'ring-pow-lincomb-at '(n c i))
(zvr-alt! 'zz-row-type (forall-guarded '(n x) '((IN n NN) (IN x (VEC (ZZ-POW n)))) '(IN (ZZ-ROW n x) (MAT 1 n (CARR ZZ-RING))))
          'ring-row-type '(n x))
(zvr-alt! 'zz-row-entry (forall-guarded '(n x i) '((IN n NN) (IN x (VEC (ZZ-POW n))) (IN i (INTERVAL 1 n))) '(= (ENTRY (ZZ-ROW n x) 1 i) (x i)))
          'ring-row-entry '(n x i))
(zvr-alt! 'zz-pow-row-lincomb (forall-guarded '(n x) '((IN n NN) (IN x (VEC (ZZ-POW n)))) (list '= ZVR-ZRL 'x))
          'ring-pow-row-lincomb '(n x))
(zvr-alt! 'zz-units-generate (forall-guarded '(n) '((IN n NN)) '(GENERATES (ZZ-POW n) n (ZZ-UNITS n))) 'ring-units-generate '(n))
(zvr-alt! 'zz-units-rel-free (forall-guarded '(n) '((IN n NN)) '(REL-FREE (ZZ-POW n) n (ZZ-UNITS n))) 'ring-units-rel-free '(n))
