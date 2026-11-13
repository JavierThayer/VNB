;;; ccr4f-digits.scm -- THE DIGIT MAP AND THE COORDINATE MAP ARE FUNCTIONS (CCR-1111 finding F1), and lifts of a
;;; matrix of residue classes.  Agent CCR-1111B, 2026-11-11.  Destination: theorem-library/ccr4f-digits.scm.
;;; Helper prefix nd6-.  Library: analysis (the 4.17 hypotheses; the setoid and matrix lemmas are core / linear
;;; algebra).
;;;
;;;   nv-digits-spec      under the hypotheses of 4.17, for x in K: NV-DIGITS(K, w, R, x) is in FUN(ZZ, R) and is
;;;                       the digit function of an expansion of x (some start n in ZZ)
;;;   nv-digits-unique    the digits of ANY expansion of x are NV-DIGITS(K, w, R, x)
;;;   nv-digits-fun       x |-> NV-DIGITS(K, w, R, x) is a function CARR K -> FUN(ZZ, R)
;;;   lin-coords-spec     if r = LINCOMB(md, d, c0, u) for a row c0 over P, and rows over P are determined by their
;;;                       combinations, then LIN-COORDS(md, d, u, P, r) is that row
;;;   setoid-lift-matrix  a matrix of classes of a setoid lifts to a matrix of representatives (by CHOICE, entrywise)
;;;
;;; Load window: after ccr4x-unique (ccr-4-17-full / ccr-4-17-unique / ccr-4-17-exists), structure-library/
;;; ccr4f-vocab, mat-map (mat-map-type, mat-map-entry), quotient-member-choice, class-of-member.

(define (nd6-hyp body)
  `(FORALL K (FORALL A (FORALL w (FORALL RP
     (IMPLIES (IS-COMPACT-NV-DOMAIN K A) (IMPLIES (IN w A) (IMPLIES (= (NV-MAXIMAL K A) (NV-PRINCIPAL K A w))
     (IMPLIES (NOT (= w (ZERO K))) (IMPLIES (= A (NV-INTEGERS K)) (IMPLIES (IS-NV-REP-SET K A RP) ,body)))))))))))
(define (nd6-dg x) `(NV-DIGITS K w RP ,x))
(define (nd6-exp a n x) `(IS-NV-EXPANSION K w RP ,a ,n ,x))
(define (nd6-has? t x) (or (equal? t x) (and (pair? t) (or (nd6-has? (car t) x) (nd6-has? (cdr t) x)))))

;; IS-NV-EXPANSION(K, w, RP, a, n, x) in context: land (IN a (FUN ZZ RP))
(define (nd6-exp-fun! e)
  (let ((a (list-ref e 4)))
    (if (not (dk-asm? `(IN ,a (FUN ZZ RP))))
        (dk-project! `(IN ,a (FUN ZZ RP)) 'is-nv-expansion e))
    `(IN ,a (FUN ZZ RP))))
;; two expansions of x in context, digits a (start n) and b (start m), both in FUN(ZZ, RP): land (= a b)
(define (nd6-ext! x a n b m)
  (dk-fun-ext! a b 'ZZ 'RP #f #f
    (lambda (v)
      (dk-cite! 'ccr-4-17-unique 'K 'A 'w 'RP x a n b m v)
      (dk-close-if-asm!))))

;;; ---------------------------------------------------------------------------
(sp (make-wff (nd6-hyp `(FORALL ndx (IMPLIES (IN ndx (CARR K))
   (AND (IN ,(nd6-dg 'ndx) (FUN ZZ RP))
        (FORSOME ndn_ (AND (IN ndn_ ZZ) ,(nd6-exp (nd6-dg 'ndx) 'ndn_ 'ndx)))))))))
(dk-peel!)
(define nd6-ex (dk-cite! 'ccr-4-17-exists 'K 'A 'w 'RP 'ndx))
(define nd6-n0 (dk-skolem! (dk-ctx-form nd6-ex) #t))
(define nd6-ex2 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (nd6-has? f nd6-n0))) "the digit existential"))
(define nd6-a0 (dk-skolem! nd6-ex2 #t))
(define nd6-e0 (nd6-exp nd6-a0 nd6-n0 'ndx))
(nd6-exp-fun! nd6-e0)
(mac 'NV-DIGITS)
(define nd6-io (cadr (cadr (dk-goal))))
(for-each
 (lambda (lf)
  (if (not (sequent-node-grounded? lf)) (begin
   (dk-focus! lf)
   (if (dk-head-is? (dk-goal) 'FORSOME)
       (begin
         (ew nd6-a0)
         (dk-conj-close!
           (lambda ()
             (let ((g (dk-goal)))
               (cond
                 ((dk-asm? g) (ass))
                 ((dk-head-is? g 'FORSOME) (witness! nd6-n0 (lambda () (dk-conj-close! (lambda () (dk-ass!))))))
                 ((dk-head-is? g 'FORALL)
                  (let* ((landed (dk-landed (lambda () (dk-peel!))))
                         (g2 (dk-goal))
                         (b (if (equal? (cadr g2) nd6-a0) (caddr g2) (cadr g2))))
                    (dk-split-all!)
                    (let* ((exb (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (nd6-has? f b))) "b's existential"))
                           (m (dk-skolem! exb #t)))
                      (dk-split-all!)
                      (if (equal? (cadr g2) b) (nd6-ext! 'ndx b m nd6-a0 nd6-n0) (nd6-ext! 'ndx nd6-a0 nd6-n0 b m)))))
                 (#t (error "nd6: unexpected leaf" (expression->string g))))))))
       (begin (dk-split-all!) (dk-conj-close! (lambda () (ass))))))))
 (dk-opened (lambda () (iota-d nd6-io))))
(qed 'nv-digits-spec)

;;; ---------------------------------------------------------------------------
(sp (make-wff (nd6-hyp `(FORALL ndx (IMPLIES (IN ndx (CARR K)) (FORALL nda (FORALL ndn (IMPLIES (IN ndn ZZ)
   (IMPLIES ,(nd6-exp 'nda 'ndn 'ndx) (= nda ,(nd6-dg 'ndx)))))))))))
(dk-peel!)
(nd6-exp-fun! (nd6-exp 'nda 'ndn 'ndx))
(dk-split-all! (list (dk-cite! 'nv-digits-spec 'K 'A 'w 'RP 'ndx)))
(define nd6-ex3 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (nd6-has? f (nd6-dg 'ndx)))) "the digits' start"))
(define nd6-m3 (dk-skolem! nd6-ex3 #t))
(nd6-ext! 'ndx 'nda 'ndn (nd6-dg 'ndx) nd6-m3)
(qed 'nv-digits-unique)

;;; ---------------------------------------------------------------------------
(sp (make-wff (nd6-hyp `(IN (VNB-LAMBDA ndx_ (CARR K) ,(nd6-dg 'ndx_)) (FUN (CARR K) (FUN ZZ RP))))))
(dk-peel!)
(dk-cite! 'nv-compact-domain 'K 'A)
(dk-cite! 'nv-domain-field 'K 'A)
(dk-cite! 'nv-field-normed 'K)
(dk-lam-type!
  (lambda ()
    (let* ((v (dk-di-var!)))
      (dk-split-all! (list (dk-cite! 'nv-digits-spec 'K 'A 'w 'RP v)))
      (dk-close-if-asm!)))
  (lambda () (dk-project! '(IN (CARR K) SET) 'is-normed-field '(IS-NORMED-FIELD K)) (dk-close-if-asm!)))
(qed 'nv-digits-fun)

;;; ---------------------------------------------------------------------------
;;; the coordinate row of r over P, when rows over P are determined by their combinations
(define (nd6-lc c) `(LINCOMB ndm ndd ,c ndu))
(define nd6-uq `(FORALL ndc1 (IMPLIES (IN ndc1 (MAT 1 ndd ndp)) (FORALL ndc2 (IMPLIES (IN ndc2 (MAT 1 ndd ndp))
                  (IMPLIES (= ,(nd6-lc 'ndc1) ,(nd6-lc 'ndc2)) (= ndc1 ndc2)))))))
(sp (make-wff `(FORALL ndm (FORALL ndd (FORALL ndu (FORALL ndp (IMPLIES ,nd6-uq
   (FORALL ndc (IMPLIES (IN ndc (MAT 1 ndd ndp)) (FORALL ndr (IMPLIES (= ndr ,(nd6-lc 'ndc))
     (= (LIN-COORDS ndm ndd ndu ndp ndr) ndc))))))))))))
(dk-peel!)
(define nd6-uqh (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (nd6-has? f 'LINCOMB))) "the uniqueness hypothesis"))
;; y in MAT(1, d, P) and ndr = LINCOMB(y) in context: land (= y ndc)
(define (nd6-same2! a b)                ; land (= a b)
  (dk-have! `(= ,(nd6-lc a) ,(nd6-lc b))
    (lambda () (subst `(= ,(nd6-lc a) ndr)) (dk-close-if-asm!)))
  (dk-apply! nd6-uqh a b)
  (dk-close-if-asm!))
(define (nd6-same! y) (nd6-same2! y 'ndc))
(mac 'LIN-COORDS)
(define nd6-io2 (cadr (dk-goal)))
(for-each
 (lambda (lf)
  (if (not (sequent-node-grounded? lf)) (begin
   (dk-focus! lf)
   (if (dk-head-is? (dk-goal) 'FORSOME)
       (begin
         (ew 'ndc)
         (dk-conj-close!
           (lambda ()
             (let ((g (dk-goal)))
               (cond
                 ((dk-asm? g) (ass))
                 ((dk-head-is? g 'FORALL)
                  (dk-peel!) (dk-split-all!)
                  (let* ((g2 (dk-goal)) (y (if (equal? (cadr g2) 'ndc) (caddr g2) (cadr g2))))
                    (if (equal? (cadr g2) 'ndc) (nd6-same2! 'ndc y) (nd6-same! y))))
                 (#t (error "nd6: unexpected leaf" (expression->string g))))))))
       (begin (dk-split-all!) (nd6-same! nd6-io2))))))
 (dk-opened (lambda () (iota-d nd6-io2))))
(qed 'lin-coords-spec)

;;; ---------------------------------------------------------------------------
;;; a matrix of classes lifts to a matrix of representatives
(define nd6-h '(VNB-LAMBDA ndz_ (QUOTIENT nds) (CHOICE ndz_)))
(sp (make-wff `(FORALL nds (IMPLIES (IS-SETOID nds) (FORALL ndm (IMPLIES (IN ndm NN) (FORALL ndq (IMPLIES (IN ndq NN)
   (FORALL nde (IMPLIES (IN nde (MAT ndm ndq (QUOTIENT nds)))
     (FORSOME ndb (AND (IN ndb (MAT ndm ndq (PTS nds)))
       (FORALL ndi (IMPLIES (IN ndi (INTERVAL 1 ndm)) (FORALL ndj (IMPLIES (IN ndj (INTERVAL 1 ndq))
         (= (CLASS nds (ENTRY ndb ndi ndj)) (ENTRY nde ndi ndj))))))))))))))))))
(dk-peel!)
(dk-cite! 'quotient-is-set 'nds)
(define (nd6-choice! z)                ; z in QUOTIENT nds: land CHOICE z in PTS nds and CLASS(CHOICE z) = z
  (dk-cite! 'quotient-member-choice 'nds z)
  (dk-split-all! (list (dk-cite! 'class-of-member 'nds z `(CHOICE ,z)))))
(dk-have! `(IN ,nd6-h (FUN (QUOTIENT nds) (PTS nds)))
  (lambda ()
    (dk-lam-type! (lambda () (let ((z (dk-di-var!))) (nd6-choice! z) (dk-close-if-asm!)))
                  (lambda () (dk-close-if-asm!)))))
(define nd6-b `(MAT-MAP ,nd6-h ndm ndq nde))
(dk-cite! 'mat-map-type 'ndm 'ndq '(QUOTIENT nds) '(PTS nds) nd6-h 'nde)
(witness! nd6-b
  (lambda ()
    (dk-conj-close!
      (lambda ()
        (if (dk-asm? (dk-goal)) (ass)
            (let* ((landed (dk-landed (lambda () (dk-peel!))))
                   (g (dk-goal))
                   (ent (caddr g)) (i (caddr ent)) (j (cadddr ent)))
              (subst (dk-cite! 'mat-map-entry 'ndm 'ndq '(QUOTIENT nds) '(PTS nds) nd6-h 'nde i j))
              (dk-cite! 'entry-in-carrier 'ndm 'ndq '(QUOTIENT nds) 'nde i j)
              (dk-lam-b!)
              (nd6-choice! ent)
              (dk-close-if-asm!)))))))
(qed 'setoid-lift-matrix)
