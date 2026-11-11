;;; ccr-ch3c-ext.scm -- wave of 2026-11-09/10 (agent CCR-1109-B3), wired 2026-11-10 from scratchpad/ccr1109b3/ccr-ch3c-ext.scm.
;;; Library: analysis.

;;; ccr-ch3c-ext.scm -- CCR.pdf Proposition 4.2 with the hypothesis "Proposition 3.6 holds on the algebra
;;; {M(xi)}" discharged by the proven ultrametric half of 3.6 (ccr-3-6-ultra), at the price of an
;;; ALGEBRAIC hypothesis: some theta in F has an irreducible multiplication matrix M(theta).
;;; Agent CCR-1109-B3, 2026-11-09.  Destination: theorem-library/ccr-ch3c-ext.scm.  Library: analysis.
;;; Load window: after theorem-library/ccr4x-ext.scm (ccr-4-2, ext-mult-mat-spec, -mul, -one, ext-abs-zero)
;;; and theorem-library/ccr-ch3c-pb.scm (ccr-3-6-ultra).  Helper prefix cd9- (cd9-open! is a copy of
;;; ccr4x-ext.scm's x4-ext-open!).
;;;
;;;   ccr-4-2-full   K a local NV field, F a finite extension with basis u (IS-FIN-EXT), theta in F with
;;;                  M(theta) irreducible  =>  |.|_F = |det M(.)| is an NV valuation of F extending |.|^n.
;;;
;;; THE ROUTE.  ccr-4-2 (CCR-1109-C2) proves the conclusion from h36: |det(M(s) + M(t))| <=
;;; max(|det M(s)|, |det M(t)|) for s, t in F.  ccr-3-6-ultra gives h36 for S = M(s), R = M(t) once
;;;   (i)   M(s), M(t) commute with T = M(theta): M(x y) = M(y) M(x) (ext-mult-mat-mul) and F is commutative;
;;;   (ii)  M(s) is invertible when det M(s) /= 0: then s /= 0 (|0|_F = 0, ext-abs-zero), s has an inverse b
;;;         in the field F, and M(b) M(s) = M(s b) = M(1) = I (ext-mult-mat-one), M(s) M(b) = M(b s) = I.
;;; No adjugate is needed: the inverse of M(s) is M(s^-1).
;;; WHAT IS NOT DISCHARGED: the irreducibility of some M(theta) (Example 4.1).  It needs a primitive
;;; element (F = K[theta]) and, in IS-IRREDUCIBLE-MAT's column convention, that the matrix whose rows are
;;; the images (OP-MAT) has no invariant column subspace -- the dual of the regular representation.  See
;;; the report, finding F3.
;;; No axiom, support or stamp.

(define cd9-v '(NORMED-FIELD-AS-COMMUTATIVE-RING K))
(define (cd9-mm xi) `(MULT-MAT md n u F ,xi))
(define (cd9-ea xi) `(EXT-ABS K F md n u ,xi))
(define (cd9-fm a b) `((MUL F) ,a ,b))
(define (cd9-x a b) `(MATMUL ,cd9-v ,a ,b))
(define cd9-id `(IDENTMAT ,cd9-v n))
(define (cd9-chain! c)
  (let loop ((c c))
    (if (not (dk-head-is? c 'IMPLIES)) c
        (begin
          (if (not (dk-asm? (cadr c))) (error "cd9-chain!: antecedent not in context" (expression->string (cadr c))))
          (let ((new (dk-landed* (lambda () (detach! c)))))
            (loop (if (pair? new) (car new) (caddr c))))))))
;; run the steps on the focus leaf while it is open (a subst whose result hash-conses onto a proven node
;; grounds the leaf, and a later step would fire on a sibling)
(define (cd9-steps! . thunks)
  (let ((lf (proof-state-focus *ps*)))
    (for-each (lambda (t) (if (not (sequent-node-grounded? lf)) (t))) thunks)
    (if (not (sequent-node-grounded? lf)) (error "cd9-steps!: the leaf is still open"))))
(define (cd9-c! . args) (cd9-chain! (apply dk-cite! args)))
(define (cd9-open!)
  (if (not (dk-asm? '(IS-MODULE md)))
      (begin
        (dk-split-all! (list (dk-meta-iff-r! (dk-meta-iff! 'is-fin-ext 'K 'F 'md 'n 'u))))
        (dk-split-all! (list (dk-meta-iff-r! (dk-meta-iff! 'is-field-ring-def 'F))))
        (cd9-c! 'commutative-ring-is-ring 'F)
        (cd9-c! 'normed-field-as-commutative-ring-is-commutative-ring 'K)
        (cd9-c! 'commutative-ring-is-ring cd9-v)
        (for-each (lambda (r) (dk-cite! r 'K))
                  '(normed-field-ring-view-carr normed-field-ring-view-add normed-field-ring-view-mul
                    normed-field-ring-view-neg normed-field-ring-view-zero normed-field-ring-view-one))
        (cd9-c! 'ring-one-in 'F) (cd9-c! 'ring-zero-in 'F))))
(define (cd9-mm! xi)                     ; M(xi) typed over K and over the view
  (if (not (dk-asm? `(IN ,(cd9-mm xi) (MAT n n (CARR K)))))
      (begin
        (dk-split-all! (list (cd9-c! 'ext-mult-mat-spec 'K 'F 'md 'n 'u xi)))
        (dk-rewrite-h! `(IN ,(cd9-mm xi) (MAT n n (CARR K))) '(CARR K) `(CARR ,cd9-v)))))
;; M(a) M(th) = M(th) M(a)
(define (cd9-commute! a th)
  (let ((g `(= ,(cd9-x (cd9-mm a) (cd9-mm th)) ,(cd9-x (cd9-mm th) (cd9-mm a)))))
    (if (not (dk-asm? g))
        (dk-have! g
          (lambda ()
            (cd9-c! 'ring-carrier-closed-mul 'F a th) (cd9-c! 'ring-carrier-closed-mul 'F th a)
            (cd9-c! 'ext-mult-mat-mul 'K 'F 'md 'n 'u th a)
            (cd9-c! 'ext-mult-mat-mul 'K 'F 'md 'n 'u a th)
            (cd9-c! 'commutative-ring-mul-comm 'F a th)
            (subst `(= ,(cd9-x (cd9-mm a) (cd9-mm th)) ,(cd9-mm (cd9-fm th a))))
            (subst `(= ,(cd9-fm th a) ,(cd9-fm a th)))
            (dk-ass!))))
    g))
;; the inverse hypothesis of ccr-3-6-ultra for M(a)
(define (cd9-inv! a inv)
  (let* ((ma (cd9-mm a)) (dt `(DET ,cd9-v n ,ma))
         (g `(IMPLIES (NOT (= ,dt (ZERO K)))
               (FORSOME cd8p_ (AND (IN cd8p_ (MAT n n (CARR K)))
                 (AND (= ,(cd9-x 'cd8p_ ma) ,cd9-id) (= ,(cd9-x ma 'cd8p_) ,cd9-id)))))))
    (dk-have! g
      (lambda ()
        (di)
        (let ((notf `(NOT (= ,dt (ZERO K)))))
          (use-em `(= ,a (ZERO F))
            (lambda ()
              (cd9-c! 'ext-abs-zero 'K 'F 'md 'n 'u)
              (cd9-mm! '(ZERO F))
              (cd9-c! 'det-in-carrier cd9-v 'n (cd9-mm '(ZERO F)))
              (dk-rewrite-h! `(IN (DET ,cd9-v n ,(cd9-mm '(ZERO F))) (CARR ,cd9-v)) `(CARR ,cd9-v) '(CARR K))
              (let ((d0 `(DET ,cd9-v n ,(cd9-mm '(ZERO F)))))
                (dk-have! `(= ((FNRM K) ,d0) 0)
                  (lambda ()
                    (dk-have! `(= ,(cd9-ea '(ZERO F)) ((FNRM K) ,d0)) (lambda () (mac 'EXT-ABS) (mac 'EXT-NORM) (rfl)))
                    (subst `(= ((FNRM K) ,d0) ,(cd9-ea '(ZERO F))))
                    (dk-ass!)))
                (cd9-c! 'nf-norm-zero-implies 'K d0)
                (dk-have! `(= ,dt (ZERO K)) (lambda () (subst `(= ,a (ZERO F))) (dk-ass!)))
                (dk-only! notf `(= ,dt (ZERO K)))
                (prop)))
            (lambda ()
              (let* ((b (dk-skolem! (cd9-chain! (dk-apply! inv a))))
                     (ig (dk-split-all!)))
                (cd9-mm! b) (cd9-mm! '(ONE F))
                (cd9-c! 'ring-carrier-closed-mul 'F a b) (cd9-c! 'ring-carrier-closed-mul 'F b a)
                (cd9-c! 'ext-mult-mat-mul 'K 'F 'md 'n 'u a b)
                (cd9-c! 'ext-mult-mat-mul 'K 'F 'md 'n 'u b a)
                (cd9-c! 'commutative-ring-mul-comm 'F a b)
                (cd9-c! 'ext-mult-mat-one 'K 'F 'md 'n 'u)
                (ew (cd9-mm b))
                (dk-conj-close!
                  (lambda ()
                    (let ((gl (dk-goal)))
                      (cond ((dk-asm? gl) (dk-ass!))
                            ((equal? (cadr gl) (cd9-x (cd9-mm b) ma))
                             (cd9-steps!
                               (lambda () (subst `(= ,(cd9-x (cd9-mm b) ma) ,(cd9-mm (cd9-fm a b)))))
                               (lambda () (subst `(= ,(cd9-fm a b) (ONE F))))
                               (lambda () (dk-ass!))))
                            (#t
                             (cd9-steps!
                               (lambda () (subst `(= ,(cd9-x ma (cd9-mm b)) ,(cd9-mm (cd9-fm b a)))))
                               (lambda () (subst `(= ,(cd9-fm b a) ,(cd9-fm a b))))
                               (lambda () (subst `(= ,(cd9-fm a b) (ONE F))))
                               (lambda () (dk-ass!))))))))))))))
    g))

(define cd9-h36
  `(FORALL x4s (IMPLIES (IN x4s (CARR F)) (FORALL x4t (IMPLIES (IN x4t (CARR F))
     (<= ((FNRM K) (DET ,cd9-v n (MATADD ,cd9-v ,(cd9-mm 'x4s) ,(cd9-mm 'x4t))))
         (MAX ((FNRM K) (DET ,cd9-v n ,(cd9-mm 'x4s))) ((FNRM K) (DET ,cd9-v n ,(cd9-mm 'x4t))))))))))

(sp (make-wff `(FORALL K (FORALL F (FORALL md (FORALL n (FORALL u (IMPLIES (IS-FIN-EXT K F md n u)
  (IMPLIES (IS-LOCAL-NV-FIELD K)
  (FORALL th (IMPLIES (IN th (CARR F)) (IMPLIES (IS-IRREDUCIBLE-MAT K n ,(cd9-mm 'th))
    (AND (IS-NV-VALUATION F (VNB-LAMBDA x4v (CARR F) ,(cd9-ea 'x4v)))
         (FORALL x4l (IMPLIES (IN x4l (CARR K)) (= ,(cd9-ea '((ACT md) x4l (ONE F))) (power ((FNRM K) x4l) n)))))))))))))))))
(dk-peel!)
(cd9-open!)
(let ((inv (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'FORSOME) (dk-contains? h '(ONE F)))) "the inverse law")))
  (dk-have! cd9-h36
    (lambda ()
      (let* ((landed (dk-peel!))
             (xs (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(CARR F)))) landed)))
             (sv (car xs)) (tv (cadr xs)))
        (cd9-mm! sv) (cd9-mm! tv) (cd9-mm! 'th)
        (cd9-commute! sv 'th) (cd9-commute! tv 'th)
        (cd9-inv! sv inv) (cd9-inv! tv inv)
        (dk-cite! 'ccr-3-6-ultra 'K 'n (cd9-mm 'th) (cd9-mm sv) (cd9-mm tv))
        (dk-ass!)))))
(cd9-c! 'ccr-4-2 'K 'F 'md 'n 'u)
(dk-ass!)
(qed 'ccr-4-2-full)
