;;; ipf-laws.scm -- A MODULE OVER CC WITH AN INNER PRODUCT FORM IS A COMPLEX INNER PRODUCT SPACE.
;;; Agent BA-1111-A2, 2026-11-11.  Destination: theorem-library/ipf-laws.scm.  Library: analysis.
;;; Helper prefix ipl-.
;;;
;;;   module-with-form-{scal,vec,vadd,vzero,vneg,act,ip}   the read-offs of MODULE-WITH-FORM(md, fq)
;;;   hermitian-form-zero-left        f(0, y) = 0 for a hermitian form on a module
;;;   cips-of-inner-product-form      IS-MODULE(md), SCAL(md) = the CC ring view and
;;;                                   IS-INNER-PRODUCT-FORM(md, fq) give
;;;                                   IS-COMPLEX-INNER-PRODUCT-SPACE(MODULE-WITH-FORM(md, fq))
;;;
;;; THE TECHNIQUE.  Slots 1-6 of the tuple are md's accessors, so after the read-offs every
;;; conjunct of IS-COMPLEX-INNER-PRODUCT-SPACE for slots 1-6 is LITERALLY a conjunct of IS-MODULE(md),
;;; and every form conjunct is literally a conjunct of IS-INNER-PRODUCT-FORM(md, fq) (the vocabulary
;;; states them in that shape), except the definiteness IFF, whose converse is f(0, 0) = 0.  An
;;; instance (a subspace with a new form, a quotient, a completion) is then: prove its six slots form a
;;; module (usually already a theorem) and prove the form laws.
;;;
;;; LOAD WINDOW: after structure-library/ipf-vocab, structure-library/complex-inner-product,
;;; theorem-library/la-z3-quotient (nothing cited from it here), and the files of rmod-vzero-left
;;; (tvs-seminorm-extension's window: rake-module laws), module-vzero-in (module.scm),
;;; normed-field-as-commutative-ring-is-commutative-ring, rr-leq-antisymmetric.

(define (ipl-open?) (pair? (dk-open-leaves)))
(define (ipl-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l) (display ";; IPL OPEN ") (display (expression->string (dk-goal-of l))) (newline)
                  (for-each (lambda (a) (display ";;    asm ") (display (expression->string a)) (newline)) (dk-asms-of l)))
                (dk-open-leaves)))
  (qed name) (topic! name 'analysis))
(define ipl-R '(NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD))
(define ipl-S '(MODULE-WITH-FORM md fq))
(define (ipl-has-head? h e)
  (and (pair? e) (or (eq? (car e) h) (ipl-has-head? h (car e)) (let loop ((l (cdr e))) (and (pair? l) (or (ipl-has-head? h (car l)) (loop (cdr l))))))))

;;; ---- the read-offs ----------------------------------------------------------------------
(define (ipl-guarded body)
  (list 'FORALL 'md (list 'IMPLIES '(IS-MODULE md)
    (list 'FORALL 'fq (list 'IMPLIES '(IN fq (FUN (CARTESIAN (VEC md) (VEC md)) CC)) body)))))
(define (ipl-owed-rfl!)
  (let loop ((fuel 10))
    (let ((k (find-first (lambda (n) (let ((g (dk-goal-of n))) (and (dk-head-is? g '=) (equal? (cadr g) (caddr g)))))
                         (dk-open-leaves))))
      (if (and k (> fuel 0)) (begin (dk-focus! k) (rfl) (loop (- fuel 1)))))))
(define (ipl-read-off! name acc val)
  (sp (make-wff (ipl-guarded (list '== (list acc ipl-S) val))))
  (dk-peel!)
  (mac-h 'is-module '(IS-MODULE md)) (dk-split-all!)
  (slot acc)
  (mac 'MODULE-WITH-FORM)
  (nth-r)
  (let loop ((fuel 3))
    (if (and (> fuel 0) (ipl-open?) (ipl-has-head? acc (dk-goal))) (begin (slot acc) (loop (- fuel 1)))))
  (if (ipl-open?) (qrfl))
  (ipl-owed-rfl!)
  (ipl-qed! name))
(ipl-read-off! 'module-with-form-scal 'SCAL '(SCAL md))
(ipl-read-off! 'module-with-form-vec 'VEC '(VEC md))
(ipl-read-off! 'module-with-form-vadd 'VADD '(VADD md))
(ipl-read-off! 'module-with-form-vzero 'VZERO '(VZERO md))
(ipl-read-off! 'module-with-form-vneg 'VNEG '(VNEG md))
(ipl-read-off! 'module-with-form-act 'ACT '(ACT md))
(ipl-read-off! 'module-with-form-ip 'IP 'fq)

;;; ---- the form conditions as they land from the predicates (binders of ipf-vocab) -------------
(define ipl-add-law
  '(FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC md)) (FORALL ipfy_ (IMPLIES (IN ipfy_ (VEC md))
     (FORALL ipfz_ (IMPLIES (IN ipfz_ (VEC md))
       (= (fq ((VADD md) ipfx_ ipfy_) ipfz_) (+ (fq ipfx_ ipfz_) (fq ipfy_ ipfz_))))))))))
(define ipl-real-law '(FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC md)) (IN (fq ipfx_ ipfx_) RR))))
(define ipl-def-law
  '(FORALL ipfx_ (IMPLIES (IN ipfx_ (VEC md)) (IMPLIES (= (fq ipfx_ ipfx_) 0) (= ipfx_ (VZERO md))))))
(define (ipl-need! f)
  (if (not (dk-asm? f)) (error "ipl: expected in context" (expression->string f))) f)

(define (ipl-open-preds! defs)
  (for-each (lambda (pr) (mac-h (car pr) (cadr pr)) (dk-split-all!)) defs))

;;; a = a + a with a real gives a = 0
(define (ipl-zero-of-double! a h)
  (dk-have! (list '<= a 0) (lambda () (dk-ineq! (list 'IN a 'RR) h)))
  (dk-have! (list '<= 0 a) (lambda () (dk-ineq! (list 'IN a 'RR) h)))
  (dk-have! '(IN 0 RR) (lambda () (arith)))
  (dk-have! (list 'AND (list 'IN a 'RR) '(IN 0 RR)) (lambda () (dk-conj-close! dk-ass!)))
  (dk-have! (list 'AND (list '<= a 0) (list '<= 0 a)) (lambda () (dk-conj-close! dk-ass!)))
  (dk-cite! 'rr-leq-antisymmetric a 0))

;;; ---- f(0, 0) = 0 for a positive semi-definite form ----------------------------------------
(sp (make-wff '(FORALL md (IMPLIES (IS-MODULE md) (FORALL fq (IMPLIES (IS-PSD-FORM md fq)
                 (= (fq (VZERO md) (VZERO md)) 0)))))))
(dk-peel!)
(ipl-open-preds! '((is-psd-form (IS-PSD-FORM md fq)) (is-hermitian-form (IS-HERMITIAN-FORM md fq))))
(dk-cite! 'module-vzero-in 'md)
(let* ((z '(VZERO md))
       (h1 (dk-apply! (ipl-need! ipl-add-law) z z z))
       (e  (dk-cite! 'rmod-vzero-left 'md z))
       (h2 (dk-rewrite-h! h1 (list '(VADD md) z z) z))
       (a  (list 'fq z z)))
  (dk-apply! (ipl-need! ipl-real-law) z)
  (ipl-zero-of-double! a h2)
  (dk-close-if-asm!))
(ipl-qed! 'psd-form-zero)

;;; ---- THE THEOREM ---------------------------------------------------------------------------
(sp (make-wff (list 'FORALL 'md (list 'IMPLIES '(IS-MODULE md)
  (list 'FORALL 'fq (list 'IMPLIES (list '= '(SCAL md) ipl-R)
    (list 'IMPLIES '(IS-INNER-PRODUCT-FORM md fq) (list 'IS-COMPLEX-INNER-PRODUCT-SPACE ipl-S))))))))
(dk-peel!)
(dk-cite! 'module-vzero-in 'md)
(dk-have! '(IS-PSD-FORM md fq) (lambda () (mac-h 'is-inner-product-form '(IS-INNER-PRODUCT-FORM md fq)) (dk-split-all!) (ass)))
(dk-cite! 'psd-form-zero 'md 'fq)
(ipl-open-preds! '((is-inner-product-form (IS-INNER-PRODUCT-FORM md fq))
                   (is-psd-form (IS-PSD-FORM md fq)) (is-hermitian-form (IS-HERMITIAN-FORM md fq))))
(for-each (lambda (c) (dk-project! c 'is-module '(IS-MODULE md)))
          '((IN (VADD md) (FUN (CARTESIAN (VEC md) (VEC md)) (VEC md)))
            (IN (VNEG md) (FUN (VEC md) (VEC md)))
            (IN (ACT md) (FUN (CARTESIAN (CARR (SCAL md)) (VEC md)) (VEC md)))))
;;; the carrier of the scalars
(dk-have! '(= (CARR (SCAL md)) CC)
  (lambda () (subst (list '= '(SCAL md) ipl-R)) (subst (dk-cite! 'sip-cc-ring-carr)) (dk-close-if! (lambda () #t) (lambda () (rfl)))))
;;; the operations of S typed BEFORE the unfold (a typing in context certifies the accessor term)
(for-each (lambda (pr)
            (let ((acc (car pr)) (ro (cadr pr)) (cls (caddr pr)))
              (dk-have! (list 'IN (list acc ipl-S) cls) (lambda () (subst (dk-cite! ro 'md 'fq)) (ass)))))
          '((VADD module-with-form-vadd (FUN (CARTESIAN (VEC md) (VEC md)) (VEC md)))
            (VNEG module-with-form-vneg (FUN (VEC md) (VEC md)))
            (ACT module-with-form-act (FUN (CARTESIAN (CARR (SCAL md)) (VEC md)) (VEC md)))
            (IP module-with-form-ip (FUN (CARTESIAN (VEC md) (VEC md)) CC))
            (VZERO module-with-form-vzero (VEC md))))
(dk-have! (list '= (list 'LENGTH ipl-S) 7)
  (lambda () (mac 'MODULE-WITH-FORM) (len-r) (if (and (ipl-open?) (equal? (dk-goal) '(= 7 7))) (arith))))
(mac 'IS-COMPLEX-INNER-PRODUCT-SPACE)
(dk-isx-set!)
(for-each (lambda (ro) (subst (dk-cite! ro 'md 'fq)))
          '(module-with-form-scal module-with-form-vec module-with-form-vadd module-with-form-vzero
            module-with-form-vneg module-with-form-act module-with-form-ip))
(ipl-open-preds! '((is-module (IS-MODULE md))))
(define (ipl-conjunct!)
  (let ((g (dk-goal)))
    (cond ((dk-asm? g) (ass))
          ((dk-head-is? g 'FORALL)          ; the definiteness IFF
           (di)
           (let* ((iff (dk-goal)) (x (cadr (caddr iff))))
             (dk-iff! (lambda (gl) (equal? (if (dk-head-is? gl 'IMPLIES) (caddr gl) gl) (caddr iff)))
               (lambda () (if (dk-head-is? (dk-goal) 'IMPLIES) (di)) (dk-apply! (ipl-need! ipl-def-law) x) (dk-close-if-asm!))
               (lambda () (if (dk-head-is? (dk-goal) 'IMPLIES) (di)) (subst (list '= x '(VZERO md))) (dk-close-if-asm!)))))
          (#t (error "ipl-conjunct!: unexpected conjunct" (expression->string g))))))
(dk-conj-close! (lambda () (if (ipl-open?) (ipl-conjunct!))))
;;; owed reflexivities of the substitutions, if any: the accessor terms are typed in context
(let loop ((fuel 10))
  (let ((k (find-first (lambda (n) (let ((g (dk-goal-of n))) (and (dk-head-is? g '=) (equal? (cadr g) (caddr g)))))
                       (dk-open-leaves))))
    (if (and k (> fuel 0)) (begin (dk-focus! k) (rfl) (loop (- fuel 1))))))
(ipl-qed! 'cips-of-inner-product-form)
