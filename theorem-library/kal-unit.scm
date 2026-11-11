;;; kal-unit.scm -- wave of 2026-11-09/10 (agent KIT-ALG), wired 2026-11-10 from scratchpad/kitalg-1109/kal-unit.scm.
;;; Library: operator-algebras.

;;; kal-unit.scm -- BANACH ALGEBRAS, Proposition 1.1: the unitization C x A of a complex normed
;;; algebra A is an associative complex algebra -- the abelian-group, module and product laws.
;;; F. J. Thayer, "Banach Algebras and Applications", ch. 1.
;;; Agent KIT-ALG, 2026-11-10.  Destination: theorem-library/kal-unit.scm.
;;; Library: operator-algebras.  All proofs modulo 0.  Helper prefix kun-.
;;;
;;; THE TECHNIQUE.  BA-1C's read-offs (bun-vadd-apply, bun-vneg-apply, bun-act-apply,
;;; bun-vmul-apply) reduce an operation of UNITIZATION-NA at literal pairs.  One generic driver
;;; proves every law: (a) at literal pairs (l, x), (r, y), ...: kun-reduce! rewrites every redex,
;;; innermost first, until each side is ONE literal pair; kun-pair-close! proves the VEC
;;; component equation by dk-alg-norm! over the kal-cna law set and the CC component by
;;; dk-cc-norm!; (b) for elements u, v, w of UNIT-VEC(a): the eta law (BA-1C's bun-eta, restated
;;; here as kun-eta!) and one citation of the pair form.  No law is proved by hand.
;;;
;;; LOAD WINDOW: after BA-1C's ba-unitization (the read-offs, unit-vec-unfold) and kal-laws (the
;;; kal-cna law set); kit-alg.scm in the driver-kit environment.

(define (kun-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l)
                  (if (and (not (sequent-node-grounded? l))
                           (let ((g (dk-goal-of l))) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))))
                      (begin (dk-focus! l) (rfl))))
                (dk-open-leaves)))
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** kal-unit: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "kal-unit: unfinished" name))))
(define (kun-fa v cls body) (list 'FORALL v (list 'IMPLIES (list 'IN v cls) body)))
(define (kun-st body) (list 'FORALL 'a (list 'IMPLIES '(IS-COMPLEX-NORMED-ALGEBRA a) body)))
(define (kun-vt t) (dk-alg-type! 'kal-cna 'a t))
(define (kun-pair? t) (and (pair? t) (eq? (car t) 'LIST) (= (length t) 3)))
(define (kun-op? t op n) (and (pair? t) (equal? (car t) (list op 'a)) (= (length t) (+ n 1))))
(define kun-zero '(LIST 0 (VZERO a)))

;;; the redex at T: #f or (THEOREM ARGS CC-ARGS VEC-ARGS)
(define (kun-redex t)
  (cond ((and (kun-op? t 'UNIT-VADD 2) (kun-pair? (cadr t)) (kun-pair? (caddr t)))
         (let ((p (cadr t)) (q (caddr t)))
           (list 'bun-vadd-apply (list (cadr p) (caddr p) (cadr q) (caddr q))
                 (list (cadr p) (cadr q)) (list (caddr p) (caddr q)))))
        ((and (kun-op? t 'UNIT-VMUL 2) (kun-pair? (cadr t)) (kun-pair? (caddr t)))
         (let ((p (cadr t)) (q (caddr t)))
           (list 'bun-vmul-apply (list (cadr p) (caddr p) (cadr q) (caddr q))
                 (list (cadr p) (cadr q)) (list (caddr p) (caddr q)))))
        ((and (kun-op? t 'UNIT-VNEG 1) (kun-pair? (cadr t)))
         (let ((p (cadr t)))
           (list 'bun-vneg-apply (list (cadr p) (caddr p)) (list (cadr p)) (list (caddr p)))))
        ((and (kun-op? t 'UNIT-ACT 2) (kun-pair? (caddr t)))
         (let ((c (cadr t)) (p (caddr t)))
           (list 'bun-act-apply (list c (cadr p) (caddr p)) (list c (cadr p)) (list (caddr p)))))
        (#t #f)))
(define (kun-find t)                        ; innermost first
  (or (and (pair? t) (let loop ((ts t)) (and (pair? ts) (or (kun-find (car ts)) (loop (cdr ts))))))
      (and (kun-redex t) t)))
(define (kun-reduce!)
  (let loop ((n 0))
    (if (> n 200) (error "kun-reduce!: did not terminate"))
    (let ((t (kun-find (dk-goal))))
      (if t
          (let ((r (kun-redex t)))
            (for-each dk-cc-type! (caddr r))
            (for-each kun-vt (cadddr r))
            (let ((inst (apply dk-cite! (car r) 'a (cadr r))))
              (if (not (and (pair? inst) (eq? (car inst) '=) (equal? (cadr inst) t)))
                  (error "kun-reduce!: the read-off did not land as expected" (expression->string inst)))
              (subst inst))
            (loop (+ n 1)))))))
(define (kun-orient-subst! e1 e2)
  (if (not (equal? e1 e2))
      (subst (if (dk--occurs? e1 e2) (list '= e2 e1) (list '= e1 e2)))))
(define (kun-pair-close!)
  (let* ((g (dk-goal)) (l (cadr g)) (r (caddr g)))
    (if (not (and (eq? (car g) '=) (kun-pair? l) (kun-pair? r)))
        (error "kun-pair-close!: not an equation of literal pairs" (expression->string g)))
    (let ((c1 (cadr l)) (v1 (caddr l)) (c2 (cadr r)) (v2 (caddr r)))
      (if (not (equal? v1 v2))
          (begin (dk-alg-have! 'kal-cna 'a (list '= v1 v2)) (kun-orient-subst! v1 v2)))
      (if (not (equal? c1 c2))
          (begin (dk-cc-type! c1) (dk-cc-type! c2)
                 (dk-have! (list '= c1 c2) (lambda () (dk-cc-norm!)))
                 (kun-orient-subst! c1 c2)))
      (let* ((g2 (dk-goal)) (p (cadr g2)))
        (dk-cc-type! (cadr p)) (kun-vt (caddr p))
        (dk-cite! 'pair-in-cartesian 'CC '(VEC a) (cadr p) (caddr p))
        (rfl)))))
;;; eta: u in UNIT-VEC(a) is the pair of its typed components (BA-1C's bun-eta!)
(define (kun-eta! u)
  (dk-project! (list 'IN u '(CARTESIAN CC (VEC a))) 'unit-vec-unfold (list 'IN u '(UNIT-VEC a)))
  (dk-cite! 'cartesian-pair-eq u 'CC '(VEC a))
  (dk-split! (dk-cite! 'cartesian-nth u 'CC '(VEC a)))
  (list 'LIST (list 'NTH 1 u) (list 'NTH 2 u)))

;;; (kun-law! PAIR-NAME NAME NSCAL NVEC BUILD): BUILD maps (scalars elements) to (LHS . RHS).
;;; The pair form binds the scalars c1.. first, then l1 x1 l2 x2 ...; the general form binds the
;;; scalars, then u1 u2 ... in UNIT-VEC(a).
(define kun-cs '(kuc_ kud_))
(define kun-ls '(kul_ kum_ kun_))
(define kun-xs '(kux_ kuy_ kuz_))
(define kun-us '(kuu_ kuv_ kuw_))
(define (kun-take l n) (if (= n 0) '() (cons (car l) (kun-take (cdr l) (- n 1)))))
(define (kun-law! pair-name name nscal nvec build)
  (let* ((cs (kun-take kun-cs nscal)) (ls (kun-take kun-ls nvec)) (xs (kun-take kun-xs nvec))
         (us (kun-take kun-us nvec))
         (prs (map (lambda (l x) (list 'LIST l x)) ls xs))
         (e1 (build cs prs)) (e2 (build cs us)))
    ;; (a) at literal pairs
    (sp (make-wff (kun-st
      (fold-right (lambda (c b) (kun-fa c 'CC b))
        (fold-right (lambda (l x b) (kun-fa l 'CC (kun-fa x '(VEC a) b))) (list '= (car e1) (cdr e1)) ls xs)
        cs))))
    (dk-peel!)
    (kun-reduce!)
    (kun-pair-close!)
    (kun-qed! pair-name)
    ;; (b) for elements of the unitization
    (sp (make-wff (kun-st
      (fold-right (lambda (c b) (kun-fa c 'CC b))
        (fold-right (lambda (u b) (kun-fa u '(UNIT-VEC a) b)) (list '= (car e2) (cdr e2)) us)
        cs))))
    (dk-peel!)
    (let* ((etas (map kun-eta! us))
           (f0 (apply dk-cite! pair-name 'a (append cs (append-map cdr etas))))
           ;; (an explicit loop: the tree's fold-left, sequents.scm, takes ONE list)
           (f (let loop ((f f0) (prs etas) (vs us))
                (if (null? prs) f (loop (dk-rewrite-h! f (car prs) (car vs)) (cdr prs) (cdr vs))))))
      (dk-ass!))
    (kun-qed! name)))

(define (kun-ad p q) (list '(UNIT-VADD a) p q))
(define (kun-mu p q) (list '(UNIT-VMUL a) p q))
(define (kun-ng p) (list '(UNIT-VNEG a) p))
(define (kun-ac c p) (list '(UNIT-ACT a) c p))

;;; ---- the abelian group ------------------------------------------------------------------
(kun-law! 'kun-vadd-assoc-pair 'unitization-vadd-assoc 0 3
  (lambda (cs ps) (let ((p (car ps)) (q (cadr ps)) (r (caddr ps)))
                    (cons (kun-ad (kun-ad p q) r) (kun-ad p (kun-ad q r))))))
(kun-law! 'kun-vadd-comm-pair 'unitization-vadd-comm 0 2
  (lambda (cs ps) (cons (kun-ad (car ps) (cadr ps)) (kun-ad (cadr ps) (car ps)))))
(kun-law! 'kun-vadd-zero-left-pair 'unitization-vadd-zero-left 0 1
  (lambda (cs ps) (cons (kun-ad kun-zero (car ps)) (car ps))))
(kun-law! 'kun-vadd-zero-right-pair 'unitization-vadd-zero-right 0 1
  (lambda (cs ps) (cons (kun-ad (car ps) kun-zero) (car ps))))
(kun-law! 'kun-vadd-neg-right-pair 'unitization-vadd-neg-right 0 1
  (lambda (cs ps) (cons (kun-ad (car ps) (kun-ng (car ps))) kun-zero)))
(kun-law! 'kun-vadd-neg-left-pair 'unitization-vadd-neg-left 0 1
  (lambda (cs ps) (cons (kun-ad (kun-ng (car ps)) (car ps)) kun-zero)))
;;; ---- the module ------------------------------------------------------------------------
(kun-law! 'kun-act-vadd-pair 'unitization-act-vadd 1 2
  (lambda (cs ps) (let ((c (car cs)) (p (car ps)) (q (cadr ps)))
                    (cons (kun-ac c (kun-ad p q)) (kun-ad (kun-ac c p) (kun-ac c q))))))
(kun-law! 'kun-act-add-pair 'unitization-act-add 2 1
  (lambda (cs ps) (let ((c (car cs)) (d (cadr cs)) (p (car ps)))
                    (cons (kun-ac (list '+ c d) p) (kun-ad (kun-ac c p) (kun-ac d p))))))
(kun-law! 'kun-act-mul-pair 'unitization-act-mul 2 1
  (lambda (cs ps) (let ((c (car cs)) (d (cadr cs)) (p (car ps)))
                    (cons (kun-ac (list '* c d) p) (kun-ac c (kun-ac d p))))))
(kun-law! 'kun-act-one-pair 'unitization-act-one 0 1
  (lambda (cs ps) (cons (kun-ac 1 (car ps)) (car ps))))
;;; ---- the product: associative and bilinear ------------------------------------------------
(kun-law! 'kun-vmul-assoc-pair 'unitization-vmul-assoc 0 3
  (lambda (cs ps) (let ((p (car ps)) (q (cadr ps)) (r (caddr ps)))
                    (cons (kun-mu (kun-mu p q) r) (kun-mu p (kun-mu q r))))))
(kun-law! 'kun-vmul-dist-left-pair 'unitization-vmul-dist-left 0 3
  (lambda (cs ps) (let ((p (car ps)) (q (cadr ps)) (r (caddr ps)))
                    (cons (kun-mu p (kun-ad q r)) (kun-ad (kun-mu p q) (kun-mu p r))))))
(kun-law! 'kun-vmul-dist-right-pair 'unitization-vmul-dist-right 0 3
  (lambda (cs ps) (let ((p (car ps)) (q (cadr ps)) (r (caddr ps)))
                    (cons (kun-mu (kun-ad p q) r) (kun-ad (kun-mu p r) (kun-mu q r))))))
(kun-law! 'kun-vmul-act-left-pair 'unitization-vmul-act-left 1 2
  (lambda (cs ps) (let ((c (car cs)) (p (car ps)) (q (cadr ps)))
                    (cons (kun-mu (kun-ac c p) q) (kun-ac c (kun-mu p q))))))
(kun-law! 'kun-vmul-act-right-pair 'unitization-vmul-act-right 1 2
  (lambda (cs ps) (let ((c (car cs)) (p (car ps)) (q (cadr ps)))
                    (cons (kun-mu p (kun-ac c q)) (kun-ac c (kun-mu p q))))))
(display "\n;; KUN qed failures: ")  
