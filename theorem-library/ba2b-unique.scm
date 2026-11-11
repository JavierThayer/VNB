;;; ba2b-unique.scm -- wave of 2026-11-09/10 (agent BA-2B), wired 2026-11-10 from scratchpad/ba2b-1109/ba2b-unique.scm.
;;; Library: operator-algebras.

;;; ba2b-unique.scm -- Corollary 1.25 (an involutive algebra with unit carries at most one C*-norm) and the
;;; uniqueness half of Proposition 1.19 (at most one norm on the unitization making it a C*-algebra) of
;;; F. J. Thayer, "Banach Algebras and Applications", ch. 1 s. 2.
;;; Agent BA-2B, wave 2026-11-10.  Destination: theorem-library/ba2b-unique.scm.  Library: operator-algebras.
;;; All proofs modulo 0.  Helper prefix b2u-.
;;; LOAD WINDOW: after ba2b-hom (cstar-hom-contractive) and BA-1's ba-vocab (UNIT-VEC ... UNIT-ISTAR).
;;;
;;; THE ROUTE (the notes').  Two unital C*-algebras a, c with the same vectors and the same algebraic and
;;; involutive operations: the identity of VEC(a) is a unital *-homomorphism a -> c and c -> a, so by
;;; Corollary 1.24 both ways ||x||_c <= ||x||_a <= ||x||_c.  "The same operations" is stated slot by slot
;;; with `==' (SCAL and the norm may differ).

(define (b2u-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** ba2b-unique: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "ba2b-unique: unfinished" name))))
(define (b2u-cite2! . args)
  (let loop ((ch (apply dk-cite! args)))
    (if (dk-head-is? ch 'IMPLIES)
        (loop (detach-with! ch (lambda () (dk-conj-close! (lambda () (dk-ass!))))))
        ch)))

(define b2u-accs '(VEC VADD ACT VMUL VONE VSTAR))
;;; the antecedents "ACC(c) == ACC(a)", curried, around BODY
(define (b2u-same c a body)
  (let loop ((l b2u-accs))
    (if (null? l) body
        (list 'IMPLIES (list '== (list (car l) c) (list (car l) a)) (loop (cdr l))))))
(define (b2u-id a) (list 'VNB-LAMBDA 'b2u_ (list 'VEC a) 'b2u_))

;;; ---- the identity is a unital *-homomorphism ----------------------------------------------------------
(define (b2u-eq-close! a)
  ;; goal, after the peel: (= (L t) rhs) for the identity lambda L; type t, beta, rfl
  (let* ((g (dk-goal)) (t (cadr (cadr g)))
         (h (if (pair? t) (if (pair? (car t)) (car (car t)) (car t)) t)))
    (cond ((eq? h 'VADD) (dk-cite! 'ring-add-closed-uba-as-ring-uiba-as-uba a (cadr t) (caddr t)))
          ((eq? h 'VMUL) (dk-cite! 'ring-carrier-closed-mul-uba-as-ring-uiba-as-uba a (cadr t) (caddr t)))
          ((eq? h 'ACT)  (dk-cite! 'bcp-u-bae-act-type a (cadr t) (caddr t)))
          ((eq? h 'VONE) (dk-cite! 'ring-one-in-uba-as-ring-uiba-as-uba a))
          ((eq? h 'VSTAR)
           (dk-cite! 'bcp-star-fun a)
           (dk-cite! 'fun-apply-type-c (list 'VSTAR a) (list 'VEC a) (list 'VEC a) (cadr t)))
          (#t (error "b2u-eq-close!: unexpected argument" t)))
    (dk-lam-b!)
    (if (not (proof-done? *ps*))
        (if (memq (proof-state-focus *ps*) (dk-open-leaves)) (rfl)))))

(sp (make-wff (list 'FORALL 'a (list 'FORALL 'c
  (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a)
    (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA c)
      (b2u-same 'c 'a (list 'IS-STAR-HOM 'a 'c (b2u-id 'a)))))))))
(dk-peel!)
(mac 'is-star-hom)
(mac 'is-alg-hom)
(for-each (lambda (acc)
            (if (dk-contains? (dk-goal) (list acc 'c))
                (subst (list '= (list acc 'c) (list acc 'a)))))
          b2u-accs)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (if (dk-head-is? g 'IN)
          (dk-lam-type! (lambda () (if (dk-head-is? (dk-goal) 'FORALL) (dk-peel!)) (dk-ass!))
                        (lambda () (dk-cite! 'frm-module-vec-set-uba-as-module-uiba-as-uba 'a) (dk-ass!)))
          (begin
            (if (dk-head-is? g 'FORALL) (dk-peel!))
            (b2u-eq-close! 'a))))))
(b2u-qed! 'b2u-id-star-hom)

;;; ---- COROLLARY 1.25 -----------------------------------------------------------------------------------
(sp (make-wff (list 'FORALL 'a (list 'FORALL 'c
  (list 'IMPLIES '(IS-UNITAL-C-STAR-ALGEBRA a)
    (list 'IMPLIES '(IS-UNITAL-C-STAR-ALGEBRA c)
      (b2u-same 'c 'a '(FORALL x (IMPLIES (IN x (VEC a)) (= ((VNRM c) x) ((VNRM a) x)))))))))))
(dk-peel!)
(dk-cite! 'bcp-ucsa-uiba 'a)
(dk-cite! 'bcp-ucsa-uiba 'c)
(for-each (lambda (acc)
            (dk-have! (list '== (list acc 'a) (list acc 'c))
              (lambda () (subst (list '= (list acc 'c) (list acc 'a))) (qrfl))))
          b2u-accs)
(b2u-cite2! 'b2u-id-star-hom 'a 'c)
(b2u-cite2! 'b2u-id-star-hom 'c 'a)
(let* ((la (b2u-id 'a)) (lc (b2u-id 'c)))
  (dk-rewrite-h! '(IN x (VEC a)) '(VEC a) '(VEC c))
  (let ((c1 (b2u-cite2! 'cstar-hom-contractive 'a 'c la 'x))
        (c2 (b2u-cite2! 'cstar-hom-contractive 'c 'a lc 'x)))
    (dk-lam-b-h! c1)
    (dk-lam-b-h! c2)
    (dk-cite! 'bcp-u-bae-vnrm-type 'a 'x)
    (dk-cite! 'bcp-u-bae-vnrm-type 'c 'x)
    (dk-ineq! '(<= ((VNRM c) x) ((VNRM a) x)) '(<= ((VNRM a) x) ((VNRM c) x))
              '(IN ((VNRM c) x) RR) '(IN ((VNRM a) x) RR))))
(b2u-qed! 'cstar-norm-unique)

;;; ---- PROPOSITION 1.19, uniqueness: two C*-norms on the unitization agree --------------------------------
(define (b2u-tup n)
  (list 'LIST '(NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) '(UNIT-VEC a) '(UNIT-VADD a)
        '(LIST 0 (VZERO a)) '(UNIT-VNEG a) '(UNIT-ACT a) n '(UNIT-VMUL a) '(LIST 1 (VZERO a)) '(UNIT-ISTAR a)))
(define (b2u-readoff! acc)
  ;; goal (== (ACC T1) (ACC T2)) or (== (ACC T) v): unfold the accessor, reduce the NTHs, close
  (slot acc)
  (nth-r)
  (qrfl))
(sp (make-wff (list 'FORALL 'a (list 'FORALL 'nra (list 'FORALL 'nrb
  (list 'IMPLIES (list 'IS-UNITAL-C-STAR-ALGEBRA (b2u-tup 'nra))
    (list 'IMPLIES (list 'IS-UNITAL-C-STAR-ALGEBRA (b2u-tup 'nrb))
      '(FORALL u (IMPLIES (IN u (UNIT-VEC a)) (= (nrb u) (nra u)))))))))))
(dk-peel!)
(let ((ta (b2u-tup 'nra)) (tb (b2u-tup 'nrb)))
  (for-each (lambda (acc)
              (dk-have! (list '== (list acc tb) (list acc ta)) (lambda () (b2u-readoff! acc))))
            b2u-accs)
  (dk-have! (list '== (list 'VEC ta) '(UNIT-VEC a)) (lambda () (b2u-readoff! 'VEC)))
  (dk-have! (list '== (list 'VNRM ta) 'nra) (lambda () (b2u-readoff! 'VNRM)))
  (dk-have! (list '== (list 'VNRM tb) 'nrb) (lambda () (b2u-readoff! 'VNRM)))
  ;; not dk-rewrite-h! from UNIT-VEC(a): the tuple ta itself contains UNIT-VEC(a)
  (dk-have! (list 'IN 'u (list 'VEC ta))
    (lambda () (subst (list '= (list 'VEC ta) '(UNIT-VEC a))) (dk-ass!)))
  (let* ((e0 (b2u-cite2! 'cstar-norm-unique ta tb 'u))
         (e1 (dk-rewrite-h! e0 (list 'VNRM tb) 'nrb))
         (e2 (dk-rewrite-h! e1 (list 'VNRM ta) 'nra)))
    (dk-ass!)))
(b2u-qed! 'unitization-cstar-norm-unique)
