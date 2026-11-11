;;; ccr-adj-integral.scm -- wave of 2026-11-09/10 (agent CCR-1109-E), wired 2026-11-10 from scratchpad/ccr1109e/ccr-adj-integral.scm.
;;; Library: complex-analysis.

;;; ccr-adj-integral.scm -- CCR.pdf Definition 6.26 / Remark 6.27: the adjugate of a matrix over Z(K) is over
;;; Z(K), and an integral matrix (entries in Z(K), det a unit of Z(K)) has an inverse with entries in Z(K)
;;; (Cramer's rule).  Agent CCR-1109-E, 2026-11-09.  Prefix cai-.
;;;
;;;   cai-minor-bound        entries of A in Z(K) give ||MINOR(A, p, q, n)||_max <= 1
;;;   adj-entries-integral   K an NV field, A an (n+1)-square matrix with entries in Z(K): the entries of ADJ(V, n, A)
;;;                          are in Z(K).  Route: adj-entry writes the (i, j) entry as (-1)^(i+j) det(minor);
;;;                          the sign has norm 1 (cb3-sign-norm), and |det(minor)| <= 1^n = 1 by the ultrametric
;;;                          determinant bound ccr-3-1-eq21 (CCR-1109-B); Z(K) is closed under products.
;;;   ccr-6-27               Remark 6.27: A n-square with entries in Z(K) and det A in U(Z(K)) = NV-UNITS(K, Z(K))
;;;                          has an inverse B (A B = B A = I over the ring view V) with entries in Z(K).
;;;                          n = 0: det-unit-iff-invertible (CCR-1109-B4) gives the inverse; the entry clause is
;;;                          vacuous.  n = m + 1: B = b ADJ(A) for b the inverse of det A in Z(K), by
;;;                          cramer-inverse and adj-entries-integral.
;;;
;;; V = NORMED-FIELD-AS-COMMUTATIVE-RING(K).  Destination theorem-library/ccr-adj-integral.scm.  Library: analysis
;;; (NV-INTEGERS, FNRM, IS-NV-FIELD; the same as the ccr-ch3* files it cites).  LOAD WINDOW: after
;;; theorem-library/ccr-ch3-ops (ccr-3-1-eq21, cb3-sign-norm; CCR-1109-B), ccr-ch3b-alg (cq4-nvint-parts,
;;; cq4-nvint-intro; CCR-1109-B2) and ccr-adj-unit (det-unit-iff-invertible; CCR-1109-B4); everything else
;;; (adj-entry, adj-type, cramer-inverse, minor-entry, minor-type, matscale-*, nv-integers-domain, nv-domain-mul)
;;; loads earlier.  All three are unwired on 2026-11-09.

(define cai-v '(NORMED-FIELD-AS-COMMUTATIVE-RING K))
(define cai-z '(NV-INTEGERS K))
(define (cai-n x) `((FNRM K) ,x))
(define (cai-za m k)
  `(FORALL i (IMPLIES (IN i (INTERVAL 1 ,k)) (FORALL j (IMPLIES (IN j (INTERVAL 1 ,k)) (IN (ENTRY ,m i j) ,cai-z))))))

(define (cai-qed! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; cai: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (f) (display ";;      | ") (display (expression->string f)) (newline))
                              (let ((a (dk-asms-of l))) (list-head a (min 24 (length a))))))
                  (dk-open-leaves))))
  (qed name))
(define (cai-view!)
  (if (not (dk-asm? `(IS-RING ,cai-v)))
      (begin
        (dk-cite! 'nv-field-normed 'K)
        (dk-cite! 'normed-field-as-commutative-ring-is-commutative-ring 'K)
        (dk-cite! 'commutative-ring-is-ring cai-v)
        (for-each (lambda (r) (dk-cite! r 'K))
                  '(normed-field-ring-view-carr normed-field-ring-view-mul normed-field-ring-view-one
                    normed-field-ring-view-neg)))))
;; (IN m (MAT a b (CARR K))) <-> (IN m (MAT a b (CARR V))), landing the missing one
(define (cai-to-v! m a b)
  (let ((k `(IN ,m (MAT ,a ,b (CARR K)))) (v `(IN ,m (MAT ,a ,b (CARR ,cai-v)))))
    (if (not (dk-asm? v)) (dk-rewrite-h! k '(CARR K) `(CARR ,cai-v)))))
(define (cai-to-k! m a b)
  (let ((k `(IN ,m (MAT ,a ,b (CARR K)))) (v `(IN ,m (MAT ,a ,b (CARR ,cai-v)))))
    (if (not (dk-asm? k)) (dk-rewrite-h! v `(CARR ,cai-v) '(CARR K)))))
;; land (IN val (INTERVAL 1 (succ n))) for val = u or (succ u), u in [1, n]
(define (cai-idx! val u)
  (let ((sn '(succ n)))
    (if (not (dk-asm? `(IN ,val (INTERVAL 1 ,sn))))
        (begin
          (dk-cite! 'interval-elt-in-nn 1 'n u)
          (dk-cite! 'interval-lo 1 'n u)
          (dk-cite! 'interval-hi 1 'n u)
          (dk-cite! 'nn-succ-closed 'n)
          (dk-cite! 'nn-le-succ 'n)
          (if (equal? val u)
              (dk-cite! 'interval-widen 'n sn 1 u)
              (begin
                (dk-cite! 'nn-succ-closed u)
                (dk-cite! 'nn-succ-mono u 'n)
                (dk-have! `(<= 1 ,val) (lambda () (dk-nn!)))
                (dk-cite! 'interval-mem-intro 1 sn val)))))))
(define (cai-absurd! prems)
  (dk-have! '(<= 1 0) (lambda () (apply dk-nn! prems)))
  (dk-focus-having! '(<= 1 0))
  (have! '(NOT (<= 1 0)) (lambda () (arith)))
  (dk-focus-having! '(NOT (<= 1 0)))
  (pbc)
  (ai '(NOT (<= 1 0))))

;;; -----------------------------------------------------------------------
;;; 1. the minors of a matrix over Z(K) have max norm at most 1

(sp (make-wff `(FORALL K (IMPLIES (IS-NV-FIELD K) (FORALL n (IMPLIES (IN n NN)
  (FORALL A (IMPLIES (IN A (MAT (succ n) (succ n) (CARR K))) (IMPLIES ,(cai-za 'A '(succ n))
    (FORALL p (IMPLIES (IN p (INTERVAL 1 (succ n))) (FORALL q (IMPLIES (IN q (INTERVAL 1 (succ n)))
      (IS-MAT-BOUND K n n (MINOR A p q n) 1))))))))))))))
(dk-peel!)
(cai-view!)
(let* ((za (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f cai-z))) "entries in Z"))
       (mn '(MINOR A p q n)))
  (cai-to-v! 'A '(succ n) '(succ n))
  (dk-cite! 'interval-elt-in-nn 1 '(succ n) 'p)
  (dk-cite! 'interval-elt-in-nn 1 '(succ n) 'q)
  (dk-cite! 'minor-type cai-v 'A 'p 'q 'n)
  (cai-to-k! mn 'n 'n)
  (mac 'is-mat-bound)
  (dk-conj-close!
    (lambda ()
      (if (dk-head-is? (dk-goal) 'IN)
          (dk-ass!)
          (begin
            (dk-peel!)
            (let* ((g (dk-goal)) (en (cadr (cadr g))) (uv (caddr en)) (vv (cadddr en)))
              (subst (dk-cite! 'minor-entry cai-v 'A 'p 'q 'n uv vv))
              (let* ((en2 (cadr (cadr (dk-goal)))) (ifr (caddr en2)) (ifc (cadddr en2)))
                (dk-case-if! ifr
                  (lambda (t1 rv)
                    (dk-case-if! ifc
                      (lambda (t2 cv)
                        (cai-idx! rv uv)
                        (cai-idx! cv vv)
                        (dk-apply! za rv cv)
                        (dk-split! (dk-cite! 'cq4-nvint-parts 'K `(ENTRY A ,rv ,cv)))
                        (dk-ass!))))))))))))
(cai-qed! 'cai-minor-bound)

;;; -----------------------------------------------------------------------
;;; 2. the adjugate of a matrix over Z(K) is over Z(K)

(sp (make-wff `(FORALL K (IMPLIES (IS-NV-FIELD K) (FORALL n (IMPLIES (IN n NN)
  (FORALL A (IMPLIES (IN A (MAT (succ n) (succ n) (CARR K))) (IMPLIES ,(cai-za 'A '(succ n))
    ,(cai-za `(ADJ ,cai-v n A) '(succ n)))))))))))
(dk-peel!)
(cai-view!)
(let* ((g (dk-goal)) (en (cadr g)) (iv (caddr en)) (jv (cadddr en))
       (vm `(RING-MULTIPLICATIVE-MONOID ,cai-v)) (s `((NEG ,cai-v) (ONE ,cai-v)))
       (k `(+ ,iv ,jv)) (sg `(MPOW ,vm ,s ,k))
       (mn `(MINOR A ,jv ,iv n)) (d `(DET ,cai-v n ,mn)))
  (cai-to-v! 'A '(succ n) '(succ n))
  (dk-cite! 'nn-succ-closed 'n)
  (subst (dk-cite! 'adj-entry cai-v 'n 'A iv jv))
  ;; the sign: in CARR K, of norm 1, so in Z(K)
  (dk-cite! 'interval-elt-in-nn 1 '(succ n) iv)
  (dk-cite! 'interval-elt-in-nn 1 '(succ n) jv)
  (dk-have! `(AND (IN ,iv NN) (IN ,jv NN)) (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
  (dk-cite! 'nn-add-closed iv jv)
  (dk-cite! 'ring-multiplicative-monoid-is-monoid cai-v)
  (dk-cite! 'rmm-carr cai-v)
  (dk-cite! 'ring-one-in cai-v)
  (dk-cite! 'ring-neg-in-carr cai-v `(ONE ,cai-v))
  (dk-have! `(IN ,s (CARR ,vm)) (lambda () (subst `(= (CARR ,vm) (CARR ,cai-v))) (dk-ass!)))
  (dk-cite! 'mpow-type vm s k)
  (dk-have! `(IN ,sg (CARR K)) (lambda () (subst `(= (CARR K) (CARR ,cai-v))) (subst `(= (CARR ,cai-v) (CARR ,vm))) (dk-ass!)))
  (dk-cite! 'cb3-sign-norm 'K k)
  (dk-have! `(<= ,(cai-n sg) 1) (lambda () (subst `(= ,(cai-n sg) 1)) (dk-ineq!)))
  (dk-cite! 'cq4-nvint-intro 'K sg)
  ;; the minor's determinant: |det| <= 1^n = 1
  (dk-cite! 'cai-minor-bound 'K 'n 'A jv iv)
  (dk-cite! 'minor-type cai-v 'A jv iv 'n)
  (dk-cite! 'det-in-carrier cai-v 'n mn)
  (dk-have! `(IN ,d (CARR K)) (lambda () (subst `(= (CARR K) (CARR ,cai-v))) (dk-ass!)))
  (dk-cite! 'rr-one-in)
  (dk-have! '(<= 0 1) (lambda () (dk-ineq!)))
  (let* ((b (dk-cite! 'ccr-3-1-eq21 'K 'n mn 1))
         (e (dk-cite! 'rr-power-one 'n)))
    (dk-rewrite-h! b '(power 1 n) 1))
  (dk-cite! 'cq4-nvint-intro 'K d)
  ;; the product
  (dk-cite! 'nv-integers-domain 'K)
  (dk-cite! 'nv-domain-mul 'K cai-z sg d)
  (subst `(= (MUL ,cai-v) (MUL K)))
  (dk-ass!))
(cai-qed! 'adj-entries-integral)

;;; -----------------------------------------------------------------------
;;; 3. Remark 6.27: an integral matrix has an inverse over Z(K)

(define cai-627-concl
  `(FORSOME cib_ (AND (IN cib_ (MAT n n (CARR K))) (AND ,(cai-za 'cib_ 'n)
     (AND (= (MATMUL ,cai-v A cib_) (IDENTMAT ,cai-v n)) (= (MATMUL ,cai-v cib_ A) (IDENTMAT ,cai-v n)))))))
(sp (make-wff `(FORALL K (IMPLIES (IS-NV-FIELD K) (FORALL n (IMPLIES (IN n NN)
  (FORALL A (IMPLIES (IN A (MAT n n (CARR K))) (IMPLIES ,(cai-za 'A 'n)
    (IMPLIES (IN (DET ,cai-v n A) (NV-UNITS K ,cai-z)) ,cai-627-concl))))))))))
(dk-peel!)
(cai-view!)
(dk-cite! 'nv-integers-domain 'K)
(let* ((dt `(DET ,cai-v n A))
       (u1 (dk-cite! 'nv-units-unfold 'K cai-z))
       (u2 (dk-rewrite-h! `(IN ,dt (NV-UNITS K ,cai-z)) `(NV-UNITS K ,cai-z) (caddr u1)))
       (ld (dk-landed (lambda () (sep-me u2))))
       (ex (dk-pick (dk-head? 'FORSOME) "the inverse of det A"))
       (b (dk-skolem! ex #t))
       (ig (dk-split-all!))
       (bk (dk-split! (dk-cite! 'cq4-nvint-parts 'K b)))
       (beq `(= ((MUL K) ,dt ,b) (ONE K))))
  (cai-to-v! 'A 'n 'n)
  (dk-have! `(IN ,b (CARR ,cai-v)) (lambda () (subst `(= (CARR ,cai-v) (CARR K))) (dk-ass!)))
  (use-em '(= n 0)
    ;; n = 0: the inverse given by det-unit-iff-invertible; no entries
    (lambda ()
      (let* ((iff (dk-cite! 'det-unit-iff-invertible cai-v 'n 'A)))
        (dk-have! (caddr iff)
          (lambda ()
            (ew b)
            (dk-conj-close!
              (lambda ()
                (if (dk-asm? (dk-goal)) (dk-ass!)
                    (begin
                      (subst `(= (MUL ,cai-v) (MUL K)))
                      (subst `(= (ONE ,cai-v) (ONE K)))
                      (dk-ass!)))))))
        (ai iff)
        (detach! `(IMPLIES ,(caddr iff) ,(cadr iff)))
        (let* ((inv (dk-landed-1 (lambda () (mac-h 'IS-INVERTIBLE-MAT (cadr iff)))))
               (pr (dk-split! inv))
               (ex2 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f 'IDENTMAT))) "the inverse"))
               (w (dk-skolem! ex2 #t))
               (ig2 (dk-split-all!)))
          (cai-to-k! w 'n 'n)
          (ew w)
          (dk-conj-close!
            (lambda ()
              (if (dk-asm? (dk-goal)) (dk-ass!)
                  (begin
                    (dk-peel!)
                    (let* ((g (dk-goal)) (iv (caddr (cadr g))))
                      (dk-rewrite-h! `(IN ,iv (INTERVAL 1 n)) 'n 0)
                      (dk-cite! 'interval-elt-in-nn 1 0 iv)
                      (dk-cite! 'interval-lo 1 0 iv)
                      (dk-cite! 'interval-hi 1 0 iv)
                      (cai-absurd! (list `(<= 1 ,iv) `(<= ,iv 0)))))))))))
    ;; n = m + 1: B = b ADJ(A) (Cramer)
    (lambda ()
      (let* ((m (dk-skolem! (dk-fact! 'nn-nonzero-is-succ 'n)))
             (sm `(succ ,m))
             (adj `(ADJ ,cai-v ,m A))
             (bm `(MATSCALE ,cai-v ,b ,adj))
             (za (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f cai-z) (dk-contains? f 'A))) "entries of A in Z")))
        (dk-cite! 'nn-succ-closed m)
        (dk-rewrite-h! `(IN A (MAT n n (CARR ,cai-v))) 'n sm)
        (dk-rewrite-h! '(IN A (MAT n n (CARR K))) 'n sm)
        (dk-rewrite-h! za 'n sm)
        (let* ((e1 (dk-rewrite-h! beq 'n sm))
               (e2 (dk-rewrite-h! e1 '(MUL K) `(MUL ,cai-v)))
               (e3 (dk-rewrite-h! e2 '(ONE K) `(ONE ,cai-v))))
          (dk-split! (dk-cite! 'cramer-inverse cai-v m 'A b)))
        (dk-cite! 'adj-type cai-v m 'A)
        (dk-cite! 'matscale-type cai-v sm sm b adj)
        (cai-to-k! bm sm sm)
        (subst `(= n ,sm))
        (ew bm)
        (dk-conj-close!
          (lambda ()
            (if (dk-asm? (dk-goal)) (dk-ass!)
                (begin
                  (dk-peel!)
                  (let* ((g (dk-goal)) (en (cadr g)) (iv (caddr en)) (jv (cadddr en)))
                    (subst (dk-cite! 'matscale-entry cai-v sm sm b adj iv jv))
                    (dk-cite! 'adj-entries-integral 'K m 'A iv jv)
                    (dk-cite! 'nv-domain-mul 'K cai-z b `(ENTRY ,adj ,iv ,jv))
                    (subst `(= (MUL ,cai-v) (MUL K)))
                    (dk-ass!))))))))))
(cai-qed! 'ccr-6-27)
(gloss! 'ccr-6-27 "Remark 6.27: a matrix with entries in Z(K) whose determinant is a unit of Z(K) has an inverse with entries in Z(K).")
