;;; gns-unique.scm -- THE UNIQUENESS HALF OF THE GNS THEOREM, first step: F. J. Thayer, "Banach Algebras
;;; and Applications" (docs/BanachAlgebras.pdf), Theorem 4.13 (the unitary W, [b] |-> rho(b) eta).
;;; Agent BA-1117-GNS2, wave 2026-11-17 (round 2).
;;; Destination: theorem-library/gns-unique.scm.  Library: operator-algebras.  Helper prefix g4u- (the
;;; helpers are BA-1111-B's g4r- helpers of ba4-rep.scm, copied: kit candidates).
;;; All proofs modulo 0.
;;; LOAD WINDOW: after theorem-library/ba4-rep (rep-functional-value, the bh-ro- read-offs) and
;;; hilbert-adjoint (op-adjoint-ip, -involutive, -fun, -bounded).

(define (g4u-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l)
                  (if (and (not (sequent-node-grounded? l))
                           (let ((g (dk-goal-of l))) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))))
                      (begin (dk-focus! l) (rfl))))
                (dk-open-leaves)))
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** gns-unique: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "gns-unique: unfinished" name))))
(define (g4u-close-eq!) (if (not (proof-done? *ps*)) (let ((g (dk-goal))) (if (and (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl)))))

;;; ---- the read-offs
(define g4u-B '(BH-ALGEBRA v))
(define g4u-ro '((VEC . (BOUNDED-OPS v v)) (VADD . (BH-VADD v)) (ACT . (BH-ACT v)) (VMUL . (BH-VMUL v))
                 (VSTAR . (BH-VSTAR v)) (VONE . (BOP-ID v)) (VNRM . (BH-VNRM v))))
(define (g4u-ro-name acc) (string->symbol (string-append "bh-ro-" (string-downcase (symbol->string acc)))))


;;; a formula about BH-ALGEBRA(v)'s slots, rewritten onto the tuple's components
(define (g4u-occurs? x t) (or (equal? x t) (and (pair? t) (or (g4u-occurs? x (car t)) (g4u-occurs? x (cdr t))))))
(define (g4u-readback! f)
  (let loop ((ps g4u-ro) (g f))
    (if (null? ps) g
        (let ((t (list (car (car ps)) g4u-B)))
          (if (g4u-occurs? t g)
              (begin (dk-cite! (g4u-ro-name (car (car ps))) 'v)
                     (loop (cdr ps) (dk-rewrite-h! g t (cdr (car ps)))))
              (loop (cdr ps) g))))))

(define (g4u-st body)
  (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a)
    (list 'FORALL 'v (list 'FORALL 'p (list 'IMPLIES '(IS-REPRESENTATION a v p)
      (list 'FORALL 'e (list 'IMPLIES '(IN e (VEC v)) body)))))))))
(define g4u-F '(REP-FUNCTIONAL a v p e))
(define (g4u-ip x y) (list '(IP v) x y))
(define (g4u-pe x) (list (list 'p x) 'e))
(define (g4u-vt! t) (dk-alg-type! 'kal-uiba 'a t) t)

;;; open IS-REPRESENTATION(a, v, p); returns the alist of the read-back laws
(define g4u-laws #f)
(define (g4u-open!)
  (let* ((rep '(IS-REPRESENTATION a v p))
         (rb (caddr (dk-cite! 'IS-REPRESENTATION 'a 'v 'p)))
         (hs (dk-project! (cadr rb) 'IS-REPRESENTATION rep))
         (sh (dk-project! (caddr rb) 'IS-REPRESENTATION rep))
         (sb (caddr (dk-cite! 'IS-STAR-HOM 'a g4u-B 'p)))
         (ah (dk-project! (cadr sb) 'IS-STAR-HOM sh))
         (pst (dk-project! (caddr sb) 'IS-STAR-HOM sh))
         (hb (caddr (dk-cite! 'IS-ALG-HOM 'a g4u-B 'p)))
         (c1 (cadr hb)) (r1 (caddr hb)) (c2 (cadr r1)) (r2 (caddr r1)) (c3 (cadr r2)) (r3 (caddr r2))
         (c4 (cadr r3)) (c5 (caddr r3))
         (pf (dk-project! c1 'IS-ALG-HOM ah)) (pa (dk-project! c2 'IS-ALG-HOM ah))
         (pc (dk-project! c3 'IS-ALG-HOM ah)) (pm (dk-project! c4 'IS-ALG-HOM ah))
         (po (dk-project! c5 'IS-ALG-HOM ah)))
    (dk-cite! 'hilbert-space-is-cips 'v)
    (set! g4u-laws
      (list (cons 'fun (g4u-readback! pf)) (cons 'add (g4u-readback! pa)) (cons 'act (g4u-readback! pc))
            (cons 'mul (g4u-readback! pm)) (cons 'one (g4u-readback! po)) (cons 'star (g4u-readback! pst))))
    g4u-laws))
(define (g4u-law k) (cdr (assq k g4u-laws)))
;;; x in VEC a: land p(x) in BOUNDED-OPS, in FUN(VEC v, VEC v), and p(x)(e) in VEC v
(define (g4u-px! x)
  (g4u-vt! x)
  (let ((px (list 'p x)))
    (dk-cite! 'fun-apply-type-c 'p '(VEC a) '(BOUNDED-OPS v v) x)
    (dk-cite! 'bop-fun 'v 'v px)
    (dk-cite! 'fun-apply-type-c px '(VEC v) '(VEC v) 'e)
    px))




(define (g4u-val! x) (dk-cite! 'rep-functional-value 'a 'v 'p 'e x))
(define (g4u-rw! from to) (subst (list '= from to)))

;;; ---- rep-functional-polar: f_(rho, eta)(c* b) = <rho(b) eta | rho(c) eta> ---------------------------------
;;; THE ROUTE: rho(c* b) = rho(c)* o rho(b), then the adjoint relation at rho(c)* and rho(c)** = rho(c), as
;;; in rep-functional-square (the case b = c).
(sp (g4u-st (list 'FORALL 'b (list 'IMPLIES '(IN b (VEC a)) (list 'FORALL 'c (list 'IMPLIES '(IN c (VEC a))
  (list '= (list g4u-F '((VMUL a) ((VSTAR a) c) b)) (g4u-ip (g4u-pe 'b) (g4u-pe 'c)))))))))
(dk-peel!)
(g4u-open!)
(let* ((cs (list '(VSTAR a) 'c)) (cb (list '(VMUL a) cs 'b))
       (pb (g4u-px! 'b)) (pc (g4u-px! 'c)) (pcs (g4u-px! cs)) (pcb (g4u-px! cb))
       (A (list 'OP-ADJOINT 'v 'v pc)) (w (g4u-pe 'b)))
  (g4u-rw! (list g4u-F cb) (caddr (g4u-val! cb)))
  (subst (dk-apply! (g4u-law 'mul) cs 'b))
  (subst (dk-cite! 'bh-vmul-value 'v pcs pb))
  (subst (dk-apply! (g4u-law 'star) 'c))
  (subst (dk-cite! 'bh-vstar-value 'v pc))
  (dk-cite! 'op-adjoint-fun 'v 'v pc)
  (dk-cite! 'op-adjoint-bounded 'v 'v pc)
  (subst (dk-cite! 'bop-comp-apply 'v A pb 'e))
  (subst (dk-cite! 'op-adjoint-ip 'v 'v A w 'e))
  (subst (dk-cite! 'op-adjoint-involutive 'v 'v pc))
  (dk-cite! 'cips-ip-type 'v w (g4u-pe 'c))
  (g4u-close-eq!))
(g4u-qed! 'rep-functional-polar)
