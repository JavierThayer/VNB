;;; ccr4d-ext.scm -- wave of 2026-11-09/10 (agent CCR-1109-C5), wired 2026-11-10 from scratchpad/ccr1109c5/ccr4d-ext.scm.
;;; Library: analysis.

;;; ccr4d-ext.scm -- A NORMED FIELD K IS A MODULE OVER ANY SUBFIELD S, and a basis of K over S makes K a finite
;;; extension of SUB-NF(K, S) in the sense of CCR-1109-C2's IS-FIN-EXT: the frame of CCR 4.24 and 4.27.
;;; Agent CCR-1109-C5, 2026-11-10.  Destination: theorem-library/ccr4d-ext.scm.  Library: analysis.  Prefix fx5-.
;;;
;;;   nf-view-field-ring             the ring view of a normed field is a field ring (the same statement as
;;;                                  CCR-1109-B2's cq4-view-field-ring, unwired: keep one of the two names)
;;;   nf-subfield-module-scal, -vec, -vadd, -vzero, -vneg, -act    the slots of NF-SUBFIELD-MODULE(K, S)
;;;   nf-subfield-module-is-module   IS-NORMED-FIELD K, IS-NF-SUBFIELD(K, S) => IS-MODULE(NF-SUBFIELD-MODULE K S)
;;;   nf-subfield-fin-ext            ... and u in MAT(n, 1, CARR K), n >= 1, GENERATES and REL-FREE for u
;;;                                  => IS-FIN-EXT(SUB-NF(K, S), ring view of K, NF-SUBFIELD-MODULE(K, S), n, u)
;;;
;;; Load window: after structure-library/ccr4d-ext-vocab, ccr4x-ext-vocab (IS-FIN-EXT, CCR-1109-C2), ccr4b-vocab
;;; (IS-NF-SUBFIELD, CCR-1109-C3), theorem-library/ccr4c-subnf (sub-nf-*, CCR-1109-C4), views, ring laws.

(define fx5-fv '(NORMED-FIELD-AS-COMMUTATIVE-RING K))
(define fx5-sv '(NORMED-FIELD-AS-COMMUTATIVE-RING (SUB-NF K S)))
(define fx5-md '(NF-SUBFIELD-MODULE K S))
(define fx5-act `(VNB-LAMBDA (LIST fmr_ fmx_) (CARTESIAN S (CARR ,fx5-fv)) ((MUL ,fx5-fv) fmr_ fmx_)))
(define fx5-ladd '(VNB-LAMBDA (LIST snu_ snv_) (CARTESIAN S S) ((ADD K) snu_ snv_)))
(define fx5-lmul '(VNB-LAMBDA (LIST snu_ snv_) (CARTESIAN S S) ((MUL K) snu_ snv_)))
(define (fx5-thm body) `(FORALL K (IMPLIES (IS-NORMED-FIELD K) (FORALL S (IMPLIES (IS-NF-SUBFIELD K S) ,body)))))
(define (fx5-curry fs body) (fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) body fs))
(define (fx5-or-asm f thunk) (if (not (dk-asm? f)) (thunk)) f)
(define (fx5-and-list f) (if (and (pair? f) (eq? (car f) 'AND)) (cons (cadr f) (fx5-and-list (caddr f))) (list f)))
(define fx5-sconjs '())

;; qed, after listing the open leaves when the proof is not done (debugging aid)
(define (fx5-qed! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; fx5: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (f) (display ";;      | ") (display (expression->string f)) (newline))
                              (let ((a (dk-asms-of l))) (list-head a (min 6 (length a))))))
                  (dk-open-leaves))))
  (qed name))

;;; ---------------------------------------------------------------------------
;;; the ring view of K is a field ring (CCR-1109-B2's cq4-view-field-ring, the same driver)

(sp (make-wff `(FORALL K (IMPLIES (IS-NORMED-FIELD K) (IS-FIELD-RING ,fx5-fv)))))
(dk-peel!)
(dk-cite! 'normed-field-as-commutative-ring-is-commutative-ring 'K)
(for-each (lambda (r) (dk-cite! r 'K))
          '(normed-field-ring-view-carr normed-field-ring-view-add normed-field-ring-view-mul
            normed-field-ring-view-neg normed-field-ring-view-zero normed-field-ring-view-one))
(mac 'is-field-ring-def)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond
       ((dk-asm? g) (dk-ass!))
       ((dk-head-is? g 'NOT)
        (let ((neg (dk-cite! 'nf-zero-ne-one 'K)))
          (subst `(= (ONE ,fx5-fv) (ONE K)))
          (subst `(= (ZERO ,fx5-fv) (ZERO K)))
          (di)
          (dk-have! '(= (ZERO K) (ONE K)) (lambda () (subst '(= (ZERO K) (ONE K))) (rfl)))
          (dk-only! neg '(= (ZERO K) (ONE K)))
          (prop)))
       (#t
        (subst `(= (CARR ,fx5-fv) (CARR K)))
        (subst `(= (ZERO ,fx5-fv) (ZERO K)))
        (subst `(= (MUL ,fx5-fv) (MUL K)))
        (subst `(= (ONE ,fx5-fv) (ONE K)))
        (let* ((landed (dk-peel!))
               (am (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(CARR K)))) landed))
               (a (cadr am))
               (ex (dk-cite! 'nf-inverse 'K a))
               (y (dk-skolem! ex)))
          (ew y)
          (dk-conj-close! (lambda () (dk-ass!)))))))))
(qed 'nf-view-field-ring)

;;; ---------------------------------------------------------------------------
;;; setup: IS-NORMED-FIELD K, IS-NF-SUBFIELD K S in context

(define (fx5-setup!)
  (let* ((iff (dk-cite! 'is-nf-subfield 'K 'S)) (rhs (caddr iff)))
    (set! fx5-sconjs (fx5-and-list rhs))
    (if (not (dk-asm? (car fx5-sconjs)))
        (begin (ai iff) (detach! (list 'IMPLIES (cadr iff) rhs)) (dk-split-all! (list rhs)))))
  (dk-cite! 'sub-nf-is-normed-field 'K 'S)
  (for-each (lambda (nf)
              (dk-cite! 'normed-field-as-commutative-ring-is-commutative-ring nf)
              (dk-cite! 'commutative-ring-is-ring `(NORMED-FIELD-AS-COMMUTATIVE-RING ,nf))
              (dk-cite! 'is-commutative-ring-is-set `(NORMED-FIELD-AS-COMMUTATIVE-RING ,nf))
              (for-each (lambda (r) (dk-cite! r nf))
                        '(normed-field-ring-view-carr normed-field-ring-view-add normed-field-ring-view-mul
                          normed-field-ring-view-neg normed-field-ring-view-zero normed-field-ring-view-one)))
            (list 'K '(SUB-NF K S)))
  (for-each (lambda (n) (dk-cite! n 'K 'S)) '(sub-nf-carr sub-nf-add sub-nf-mul sub-nf-one sub-nf-zero sub-nf-add-fun sub-nf-mul-fun))
  (fx5-or-asm '(IN (CARR K) SET) (lambda () (dk-project! '(IN (CARR K) SET) 'is-normed-field '(IS-NORMED-FIELD K))))
  (fx5-or-asm '(SUBSET S (CARR K)) (lambda () (dk-have! '(SUBSET S (CARR K)) (lambda () (mac 'subset-def) (dk-close-if-asm!)))))
  (fx5-or-asm '(IN S SET) (lambda () (dk-chain-ass! (dk-cite! 'subclass-of-set-is-set 'S '(CARR K))))))
;; R in S: land R in CARR K and in CARR of the view
(define (fx5-in! r)
  (fx5-or-asm `(IN ,r (CARR K)) (lambda () (dk-chain-ass! (dk-apply! (list-ref fx5-sconjs 0) r))))
  (fx5-or-asm `(IN ,r (CARR ,fx5-fv)) (lambda () (dk-have! `(IN ,r (CARR ,fx5-fv)) (lambda () (subst `(== (CARR ,fx5-fv) (CARR K))) (dk-ass!)))))
  r)
;; the ring view F of K: open IS-RING F (its conjuncts land), and the sethood of its components
(define (fx5-fv-open!)
  (if (not (dk-asm? `(IN (ADD ,fx5-fv) (FUN (CARTESIAN (CARR ,fx5-fv) (CARR ,fx5-fv)) (CARR ,fx5-fv)))))
      (let* ((iff (dk-meta-iff! 'is-ring fx5-fv))
             (rhs (dk-meta-iff-r! iff)))
        (dk-split-all! (list (dk-ctx-form rhs)))))
  (dk-cite! 'membership-implies-sethood `(ADD ,fx5-fv) `(FUN (CARTESIAN (CARR ,fx5-fv) (CARR ,fx5-fv)) (CARR ,fx5-fv)))
  (dk-cite! 'membership-implies-sethood `(NEG ,fx5-fv) `(FUN (CARR ,fx5-fv) (CARR ,fx5-fv)))
  (dk-cite! 'membership-implies-sethood `(ZERO ,fx5-fv) `(CARR ,fx5-fv))
  (for-each (lambda (n) (dk-cite! n fx5-fv)) '(ring-left-dist ring-right-dist ring-mul-assoc ring-mul-left-id)))

;;; ---------------------------------------------------------------------------
;;; the action is a function S x K -> K

(sp (make-wff (fx5-thm `(IN ,fx5-act (FUN (CARTESIAN S (CARR ,fx5-fv)) (CARR ,fx5-fv))))))
(dk-peel!)
(fx5-setup!)
(fx5-fv-open!)
(dk-each-leaf! (lambda () (lam-t))
  (lambda ()
    (if (dk-head-is? (dk-goal) 'FORALL)
        (let* ((landed (dk-landed (lambda () (dk-peel!))))
               (vs (map cadr (filter (lambda (f) (dk-head-is? f 'IN)) landed))))
          (fx5-in! (car vs))
          (subst `(== (MUL ,fx5-fv) (MUL K)))
          (subst `(== (CARR ,fx5-fv) (CARR K)))
          (dk-rewrite-h! `(IN ,(cadr vs) (CARR ,fx5-fv)) `(CARR ,fx5-fv) '(CARR K))
          (dk-cite! 'nf-mul-in-carr 'K (car vs) (cadr vs))
          (dk-close-if-asm!))
        (let ((cs `(IN (CARR ,fx5-fv) SET)))
          (fx5-or-asm cs (lambda () (dk-have! cs (lambda () (subst `(== (CARR ,fx5-fv) (CARR K))) (dk-ass!)))))
          (dk-have-and! '(IN S SET) cs)
          (mac 'cartesian-set-iff)
          (dk-close-if-asm!)))))
(qed 'nf-subfield-module-act-fun)

;;; ---------------------------------------------------------------------------
;;; the slots of NF-SUBFIELD-MODULE(K, S)

(define (fx5-components!)
  (fx5-setup!)
  (fx5-fv-open!)
  (dk-cite! 'nf-subfield-module-act-fun 'K 'S)
  (dk-cite! 'membership-implies-sethood fx5-act `(FUN (CARTESIAN S (CARR ,fx5-fv)) (CARR ,fx5-fv)))
  (let ((cs `(IN (CARR ,fx5-fv) SET)))
    (fx5-or-asm cs (lambda () (dk-have! cs (lambda () (subst `(== (CARR ,fx5-fv) (CARR K))) (dk-ass!)))))))
(define fx5-slots
  (list (list 'SCAL fx5-sv 'nf-subfield-module-scal)
        (list 'VEC `(CARR ,fx5-fv) 'nf-subfield-module-vec)
        (list 'VADD `(ADD ,fx5-fv) 'nf-subfield-module-vadd)
        (list 'VZERO `(ZERO ,fx5-fv) 'nf-subfield-module-vzero)
        (list 'VNEG `(NEG ,fx5-fv) 'nf-subfield-module-vneg)
        (list 'ACT fx5-act 'nf-subfield-module-act)))
(for-each
  (lambda (sl)
    (dk-sp-qed! (make-wff (fx5-thm `(== (,(car sl) ,fx5-md) ,(cadr sl))))
      (lambda ()
        (dk-peel!)
        (fx5-components!)
        (slot (car sl))
        (mac 'NF-SUBFIELD-MODULE)
        (nth-r)
        (qrfl))
      (caddr sl)))
  fx5-slots)

;;; ---------------------------------------------------------------------------
;;; THE MODULE

(define (fx5-crs! vs)
  (for-each fx5-in-view! vs)
  (for-each (lambda (op) (if (dk-contains? (dk-goal) `(,op K)) (subst `(= (,op K) (,op ,fx5-fv))))) '(ADD MUL NEG))
  (for-each (lambda (op) (if (dk-contains? (dk-goal) `(,op K)) (subst `(= (,op K) (,op ,fx5-fv))))) '(ZERO ONE))
  (crs))
(define (fx5-in-view! x)
  (if (not (dk-asm? `(IN ,x (CARR ,fx5-fv))))
      (dk-have! `(IN ,x (CARR ,fx5-fv)) (lambda () (subst `(= (CARR ,fx5-fv) (CARR K))) (dk-ass!)))))
;; the four action laws, after the unfold: peel, type, evaluate the restricted operations and the action, crs
(define (fx5-law-leaf!)
  (let* ((landed (dk-landed (lambda () (dk-peel!))))
         (ins (filter (lambda (f) (dk-head-is? f 'IN)) landed))
         (rs (map cadr (filter (lambda (f) (eq? (caddr f) 'S)) ins)))
         (xs (map cadr (filter (lambda (f) (not (eq? (caddr f) 'S))) ins))))
    (for-each fx5-in! rs)
    (for-each (lambda (x) (if (not (dk-asm? `(IN ,x (CARR K))))
                              (dk-have! `(IN ,x (CARR K)) (lambda () (subst `(== (CARR K) (CARR ,fx5-fv))) (dk-ass!)))))
              xs)
    ;; the ring view of K -> K
    (for-each (lambda (op) (if (dk-contains? (dk-goal) `(,op ,fx5-fv)) (subst `(== (,op ,fx5-fv) (,op K))))) '(ADD MUL CARR))
    ;; the restricted operations of S at points of S
    (for-each (lambda (r) (for-each (lambda (s)
                (dk-chain-ass! (dk-apply! (list-ref fx5-sconjs 3) r s)) (dk-chain-ass! (dk-apply! (list-ref fx5-sconjs 4) r s))
                (fx5-in! `((ADD K) ,r ,s)) (fx5-in! `((MUL K) ,r ,s))
                (dk-cite! 'sub-nf-add-val 'K 'S r s) (dk-cite! 'sub-nf-mul-val 'K 'S r s))
              rs)) rs)
    (for-each (lambda (pr) (if (dk-contains? (dk-goal) (car pr)) (subst `(= ,(car pr) ,(cadr pr)))))
              (append-map (lambda (r) (append-map (lambda (s) (list (list `(,fx5-ladd ,r ,s) `((ADD K) ,r ,s))
                                                                    (list `(,fx5-lmul ,r ,s) `((MUL K) ,r ,s)))) rs)) rs))
    (if (dk-contains? (dk-goal) '(ONE K)) (fx5-in! '(ONE K)))
    ;; products and sums the action will be applied to
    (for-each (lambda (x) (for-each (lambda (y) (dk-cite! 'nf-add-in-carr 'K x y)) xs)) xs)
    (for-each (lambda (r) (for-each (lambda (x) (dk-cite! 'nf-mul-in-carr 'K r x)) xs)) (append rs xs (list '(ONE K))))
    (dk-lam-b!)
    (fx5-crs! (append rs xs))))

(sp (make-wff (fx5-thm `(IS-MODULE ,fx5-md))))
(dk-peel!)
(fx5-components!)
(for-each (lambda (sl) (dk-cite! (caddr sl) 'K 'S)) fx5-slots)
(mac 'IS-MODULE)
(dk-isx-set! 'NF-SUBFIELD-MODULE)
(for-each (lambda (sl) (subst `(== (,(car sl) ,fx5-md) ,(cadr sl)))) (cdr fx5-slots))
(subst `(== (SCAL ,fx5-md) ,fx5-sv))
(for-each (lambda (pr) (if (dk-contains? (dk-goal) (car pr)) (subst `(== ,(car pr) ,(cadr pr)))))
          (list (list `(CARR ,fx5-sv) '(CARR (SUB-NF K S))) (list '(CARR (SUB-NF K S)) 'S)
                (list `(ADD ,fx5-sv) '(ADD (SUB-NF K S))) (list '(ADD (SUB-NF K S)) fx5-ladd)
                (list `(MUL ,fx5-sv) '(MUL (SUB-NF K S))) (list '(MUL (SUB-NF K S)) fx5-lmul)
                (list `(ONE ,fx5-sv) '(ONE (SUB-NF K S))) (list '(ONE (SUB-NF K S)) '(ONE K))))
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond ((dk-asm? g) (dk-ass!))
            ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'LENGTH))
             (mac 'NF-SUBFIELD-MODULE) (len-r) (if (and (dk-head-is? (dk-goal) '=) (number? (cadr (dk-goal)))) (arith)))
            ((dk-head-is? g 'FORALL) (fx5-law-leaf!))
            (#t (error "fx5 module: unexpected conjunct" (expression->string g)))))))
(fx5-qed! 'nf-subfield-module-is-module)

;;; ---------------------------------------------------------------------------
;;; THE FINITE EXTENSION: a generating free family u of n >= 1 elements of K makes K a finite extension of
;;; SUB-NF(K, S) of degree n with basis u, in the sense of IS-FIN-EXT

(sp (make-wff (fx5-thm `(FORALL n (IMPLIES (IN n NN) (IMPLIES (<= 1 n) (FORALL u (IMPLIES (IN u (MAT n 1 (CARR K)))
  (IMPLIES (GENERATES ,fx5-md n u) (IMPLIES (REL-FREE ,fx5-md n u)
    (IS-FIN-EXT (SUB-NF K S) ,fx5-fv ,fx5-md n u)))))))))))
(dk-peel!)
(fx5-components!)
(for-each (lambda (sl) (dk-cite! (caddr sl) 'K 'S)) fx5-slots)
(dk-cite! 'nf-view-field-ring 'K)
(dk-cite! 'nf-subfield-module-is-module 'K 'S)
(dk-have! `(IN u (MAT n 1 (CARR ,fx5-fv))) (lambda () (subst `(== (CARR ,fx5-fv) (CARR K))) (dk-ass!)))
(mac 'IS-FIN-EXT)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond ((dk-asm? g) (dk-ass!))
            ((and (dk-head-is? g '=) (pair? (cadr g)) (memq (car (cadr g)) '(SCAL VEC VADD VZERO VNEG)))
             (let ((sl (assq (car (cadr g)) fx5-slots)))
               (subst `(== (,(car sl) ,fx5-md) ,(cadr sl)))
               (rfl)))
            ((dk-head-is? g 'FORALL)
             (subst `(== (ACT ,fx5-md) ,fx5-act))
             (subst `(== (CARR (SUB-NF K S)) S))
             (fx5-law-leaf!))
            (#t (error "fx5 fin-ext: unexpected conjunct" (expression->string g)))))))
(fx5-qed! 'nf-subfield-fin-ext)
