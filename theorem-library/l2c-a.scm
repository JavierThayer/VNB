;;; l2c-a.scm -- wave of 2026-11-09/10 (agent TH3-L2), wired 2026-11-10 from scratchpad/th3-1109/l2/l2c-a.scm.
;;; Library: measure.

;;; l2c-a.scm -- COMPLEX L^2 IS A HILBERT SPACE (TH3-L2 target 1, 2026-11-09).
;;; Vocabulary: l2c-vocab.scm (CL2-HILBERT).  Helper prefix: l2a-.
;;;
;;; Section 1 is general: for a semi-inner-product space v, the complexification of its
;;; quotient by the null vectors, w = CSIP-CIPS(COMPLEXIFY(SIP-QUOTIENT v)), read on PAIRS OF
;;; CLASSES [CLASS a1, CLASS a2]: its vector set, zero, sum, complex scalar action and complex
;;; form, and the representation of every vector as such a pair.  Section 2 specialises to
;;; real L^2: CL2-HILBERT is a Hilbert space, its form is
;;;     <[f1], [f2]> , <[g1], [g2]> = (int f1 g1 + int f2 g2) + i (int f2 g1 - int f1 g2),
;;; and two square-integrable functions have the same class iff they agree almost everywhere.
;;;
;;; LOAD WINDOW: after theorem-library/l2-hilbert (l2-quotient-is-real-hilbert) and
;;; theorem-library/sip-d1 (complexify-hilbert, cxw-*), and after l2c-vocab.
;;; Library: measure.

(define (l2a-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** l2c-a: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "l2c-a: unfinished" name))))

(define l2a-q '(SIP-QUOTIENT v))
(define l2a-w '(CSIP-CIPS (COMPLEXIFY (SIP-QUOTIENT v))))
(define l2a-st '(SIP-SETOID v))
(define l2a-qv '(QUOTIENT (SIP-SETOID v)))
(define (l2a-cl x) (list 'CLASS l2a-st x))
(define (l2a-pr a b) (list 'LIST (l2a-cl a) (l2a-cl b)))
(define (l2a-ip a b) (list '(RIP v) a b))
(define (l2a-wa acc) (list acc l2a-w))
(define (l2a-open?) (not (proof-done? *ps*)))
(define (l2a-sp-sip body) (sp (make-wff (list 'FORALL 'v (list 'IMPLIES '(IS-SEMI-INNER-PRODUCT-SPACE v) body)))))
(define (l2a-rw! e) (subst (list '= (cadr e) (caddr e))))

;;; the owed list-definedness leaves (= L L) a read-off may leave: closed by rfl; then focus the
;;; one remaining leaf
(define (l2a-clear-owed!)
  (for-each (lambda (l)
              (let ((g (dk-goal-of l)))
                (if (and (pair? g) (memq (car g) '(= ==)) (equal? (cadr g) (caddr g)))
                    (begin (dk-focus! l) (rfl)))))
            (dk-open-leaves))
  (let ((ls (dk-open-leaves)))
    (if (= (length ls) 1) (dk-focus! (car ls)))))
(define (l2a-nth!) (nth-r) (l2a-clear-owed!))

(define (l2a-op? e op) (and (pair? e) (equal? (car e) (list op 'v))))
(define (l2a-pin!) (if (not (dk-asm? '(= (SCAL v) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))))
                       (fact 'sip-scal-pin 'v)))
;;; type a vector expression of v by citation
(define (l2a-vt x)
  (cond ((l2a-op? x 'VADD) (l2a-vt (cadr x)) (l2a-vt (caddr x)))
        ((l2a-op? x 'VNEG) (l2a-vt (cadr x)))
        ((l2a-op? x 'ACT) (l2a-pin!) (l2a-vt (caddr x)) (dk-real! (cadr x))))
  (cond ((dk-asm? (list 'IN x '(VEC v))) x)
        ((equal? x '(VZERO v)) (dk-cite! 'module-vzero-in-sip-as-module 'v) x)
        ((l2a-op? x 'VADD) (dk-cite! 'module-vadd-type-sip-as-module 'v (cadr x) (caddr x)) x)
        ((l2a-op? x 'VNEG) (dk-cite! 'module-vneg-type-sip-as-module 'v (cadr x)) x)
        ((l2a-op? x 'ACT) (dk-cite! 'hbs-act-in-sip-as-module 'v (cadr x) (caddr x)) x)
        (#t (error "l2a-vt: cannot type" (expression->string x)))))

;;; IS-SIP v in context: the setoid facts and the quotient's equations
(define (l2a-base0!)
  (if (not (dk-asm? (list 'IS-SETOID l2a-st))) (dk-cite! 'sip-setoid-is-setoid 'v))
  (dk-cite! 'sip-setoid-pts 'v)
  (dk-cite! 'sipq-vec 'v))
(define (l2a-base!)
  (l2a-base0!)
  (if (not (dk-asm? (list 'IS-SEMI-INNER-PRODUCT-SPACE l2a-q))) (dk-cite! 'cxq-sip 'v)))
;;; a in VEC v (typable): CLASS a in QV, in VEC q, in SET
(define (l2a-cl-in! a)
  (l2a-vt a)
  (let ((pin (list 'IN a '(PTS (SIP-SETOID v)))))
    (if (not (dk-asm? pin)) (dk-rewrite-h! (list 'IN a '(VEC v)) '(VEC v) '(PTS (SIP-SETOID v)))))
  (dk-cite! 'class-in-quotient l2a-st a)
  (dk-cite! 'class-is-set l2a-st a)
  (let ((want (list 'IN (l2a-cl a) (list 'VEC l2a-q))))
    (if (not (dk-asm? want)) (dk-rewrite-h! (list 'IN (l2a-cl a) l2a-qv) l2a-qv (list 'VEC l2a-q)))
    want))
;;; the pair [CLASS a, CLASS b] in CARTESIAN(VEC q, VEC q)
(define (l2a-pair-in! a b)
  (l2a-cl-in! a) (l2a-cl-in! b)
  (dk-cite! 'pair-in-cartesian (list 'VEC l2a-q) (list 'VEC l2a-q) (l2a-cl a) (l2a-cl b)))
(define (l2a-rip-ty! a b) (l2a-vt a) (l2a-vt b) (dk-cite! 'sip-rip-type 'v a b))

;;; ==========================================================================================
;;; (1) THE COMPLEXIFIED QUOTIENT ON PAIRS OF CLASSES
;;; ==========================================================================================

(l2a-sp-sip (list 'IS-SEMI-INNER-PRODUCT-SPACE l2a-q))
(dk-peel!)
(dk-cite! 'sip-quotient-is-pre-hilbert 'v)
(dk-cite! 'phs-is-sip l2a-q)
(if (l2a-open?) (ass))
(l2a-qed! 'cxq-sip)

(l2a-sp-sip (list '== (l2a-wa 'VEC) (list 'CARTESIAN l2a-qv l2a-qv)))
(dk-peel!)
(l2a-base!)
(l2a-rw! (dk-cite! 'cxw-vec l2a-q))
(l2a-rw! (dk-cite! 'sipq-vec 'v))
(if (l2a-open?) (qrfl))
(l2a-qed! 'cxq-vec)

(l2a-sp-sip (forall-guarded '(a1_ a2_) '((IN a1_ (VEC v)) (IN a2_ (VEC v)))
              (list 'IN (l2a-pr 'a1_ 'a2_) (l2a-wa 'VEC))))
(dk-peel!)
(l2a-base!)
(l2a-cl-in! 'a1_) (l2a-cl-in! 'a2_)
(dk-cite! 'pair-in-cartesian l2a-qv l2a-qv (l2a-cl 'a1_) (l2a-cl 'a2_))
(l2a-rw! (dk-cite! 'cxq-vec 'v))
(if (l2a-open?) (ass))
(l2a-qed! 'cxq-pair-in)

(l2a-sp-sip (list '== (l2a-wa 'VZERO) (l2a-pr '(VZERO v) '(VZERO v))))
(dk-peel!)
(l2a-base!)
(l2a-rw! (dk-cite! 'cxw-vzero l2a-q))
(l2a-rw! (dk-cite! 'sipq-vzero 'v))
(if (l2a-open?) (qrfl))
(l2a-qed! 'cxq-vzero)

;;; every vector of w is a pair of classes
(l2a-sp-sip (forall-guarded '(x_) (list (list 'IN 'x_ (l2a-wa 'VEC)))
  (list 'FORSOME 'a1_ (list 'AND '(IN a1_ (VEC v))
    (list 'FORSOME 'a2_ (list 'AND '(IN a2_ (VEC v)) (list '= 'x_ (l2a-pr 'a1_ 'a2_))))))))
(dk-peel!)
(l2a-base!)
(dk-cite! 'cxq-vec 'v)
(dk-rewrite-h! (list 'IN 'x_ (l2a-wa 'VEC)) (l2a-wa 'VEC) (list 'CARTESIAN l2a-qv l2a-qv))
(dk-split-all! (list (dk-cite! 'cartesian-nth 'x_ l2a-qv l2a-qv)))
(dk-cite! 'cartesian-pair-eq 'x_ l2a-qv l2a-qv)
(let* ((r1 (dk-cite! 'quotient-rep l2a-st '(NTH 1 x_)))
       (k1 (dk-skolem! r1))
       (r2 (dk-cite! 'quotient-rep l2a-st '(NTH 2 x_)))
       (k2 (dk-skolem! r2))
       (b1 k1) (b2 k2))
  (for-each (lambda (b) (dk-rewrite-h! (list 'IN b '(PTS (SIP-SETOID v))) '(PTS (SIP-SETOID v)) '(VEC v))) (list b1 b2))
  (ew b1)
  (dk-conj-close!
    (lambda ()
      (if (not (dk-ass!))
          (begin
            (ew b2)
            (dk-conj-close!
              (lambda ()
                (if (not (dk-ass!))
                    (begin
                      (subst (list '= 'x_ '(LIST (NTH 1 x_) (NTH 2 x_))))
                      (subst (list '= '(NTH 1 x_) (l2a-cl b1)))
                      (subst (list '= '(NTH 2 x_) (l2a-cl b2)))
                      (if (l2a-open?) (rfl)))))))))))
(l2a-clear-owed!)
(l2a-qed! 'cxq-rep)

;;; the sum on pairs of classes
(l2a-sp-sip (forall-guarded '(a1_ a2_ b1_ b2_) '((IN a1_ (VEC v)) (IN a2_ (VEC v)) (IN b1_ (VEC v)) (IN b2_ (VEC v)))
  (list '= (list (l2a-wa 'VADD) (l2a-pr 'a1_ 'a2_) (l2a-pr 'b1_ 'b2_))
           (l2a-pr '((VADD v) a1_ b1_) '((VADD v) a2_ b2_)))))
(dk-peel!)
(l2a-base!)
(l2a-pair-in! 'a1_ 'a2_) (l2a-pair-in! 'b1_ 'b2_)
(l2a-cl-in! '((VADD v) a1_ b1_)) (l2a-cl-in! '((VADD v) a2_ b2_))
(subst (dk-cite! 'cxw-vadd-value l2a-q (l2a-pr 'a1_ 'a2_) (l2a-pr 'b1_ 'b2_)))
(l2a-nth!)
(subst (dk-cite! 'sipq-vadd-computes 'v 'a1_ 'b1_))
(subst (dk-cite! 'sipq-vadd-computes 'v 'a2_ 'b2_))
(if (l2a-open?) (rfl))
(l2a-clear-owed!)
(l2a-qed! 'cxq-vadd-classes)

;;; the complex scalar action on pairs of classes: (a + ib)[u, v] = [a u - b v, a v + b u]
(define l2a-act-rhs
  (l2a-pr '((VADD v) ((ACT v) (real-part z_) a1_) ((ACT v) (imag-part z_) ((VNEG v) a2_)))
          '((VADD v) ((ACT v) (real-part z_) a2_) ((ACT v) (imag-part z_) a1_))))
(l2a-sp-sip (forall-guarded '(z_ a1_ a2_) '((IN z_ CC) (IN a1_ (VEC v)) (IN a2_ (VEC v)))
  (list '= (list (l2a-wa 'ACT) 'z_ (l2a-pr 'a1_ 'a2_)) l2a-act-rhs)))
(dk-peel!)
(l2a-base!)
(dk-cite! 'real-part-in-rr 'z_) (dk-cite! 'imag-part-in-rr 'z_)
(l2a-pair-in! 'a1_ 'a2_)
(l2a-cl-in! (caddr (cadr l2a-act-rhs))) (l2a-cl-in! (caddr (caddr l2a-act-rhs)))
(l2a-cl-in! '((VNEG v) a2_))
(l2a-cl-in! '((ACT v) (real-part z_) a1_)) (l2a-cl-in! '((ACT v) (imag-part z_) ((VNEG v) a2_)))
(l2a-cl-in! '((ACT v) (real-part z_) a2_)) (l2a-cl-in! '((ACT v) (imag-part z_) a1_))
(subst (dk-cite! 'cxw-act-value l2a-q 'z_ (l2a-pr 'a1_ 'a2_)))
(l2a-nth!)
(subst (dk-cite! 'sipq-vneg-computes 'v 'a2_))
(subst (dk-cite! 'sipq-act-computes 'v '(real-part z_) 'a1_))
(subst (dk-cite! 'sipq-act-computes 'v '(imag-part z_) '((VNEG v) a2_)))
(subst (dk-cite! 'sipq-act-computes 'v '(real-part z_) 'a2_))
(subst (dk-cite! 'sipq-act-computes 'v '(imag-part z_) 'a1_))
(subst (dk-cite! 'sipq-vadd-computes 'v '((ACT v) (real-part z_) a1_) '((ACT v) (imag-part z_) ((VNEG v) a2_))))
(subst (dk-cite! 'sipq-vadd-computes 'v '((ACT v) (real-part z_) a2_) '((ACT v) (imag-part z_) a1_)))
(if (l2a-open?) (rfl))
(l2a-clear-owed!)
(l2a-qed! 'cxq-act-classes)

;;; the complex form on pairs of classes:
;;;   <[a1, a2], [b1, b2]> = (<a1,b1> + <a2,b2>) + i (<a2,b1> - <a1,b2>)
(define l2a-ip-rhs
  (list '+ (list '+ (l2a-ip 'a1_ 'b1_) (l2a-ip 'a2_ 'b2_))
           (list '* '+i (list '- (l2a-ip 'a2_ 'b1_) (l2a-ip 'a1_ 'b2_)))))
(l2a-sp-sip (forall-guarded '(a1_ a2_ b1_ b2_) '((IN a1_ (VEC v)) (IN a2_ (VEC v)) (IN b1_ (VEC v)) (IN b2_ (VEC v)))
  (list '= (list (l2a-wa 'IP) (l2a-pr 'a1_ 'a2_) (l2a-pr 'b1_ 'b2_)) l2a-ip-rhs)))
(dk-peel!)
(l2a-base!)
(l2a-pair-in! 'a1_ 'a2_) (l2a-pair-in! 'b1_ 'b2_)
(l2a-cl-in! '((VNEG v) a2_))
(subst (dk-cite! 'cxw-ip-value l2a-q (l2a-pr 'a1_ 'a2_) (l2a-pr 'b1_ 'b2_)))
(l2a-nth!)
(subst (dk-cite! 'sipq-vneg-computes 'v 'a2_))
(subst (dk-cite! 'sipq-rip-computes 'v 'a1_ 'b1_))
(subst (dk-cite! 'sipq-rip-computes 'v 'a2_ 'b2_))
(subst (dk-cite! 'sipq-rip-computes 'v '((VNEG v) a2_) 'b1_))
(subst (dk-cite! 'sipq-rip-computes 'v 'a1_ 'b2_))
(subst (dk-cite! 'sip-rip-neg-left 'v 'a2_ 'b1_))
(l2a-rip-ty! 'a1_ 'b1_) (l2a-rip-ty! 'a2_ 'b2_) (l2a-rip-ty! 'a2_ 'b1_) (l2a-rip-ty! 'a1_ 'b2_)
(fact 'cc-i-in)
(if (l2a-open?) (crs))
(l2a-clear-owed!)
(l2a-qed! 'cxq-ip-classes)

;;; ==========================================================================================
;;; (2) COMPLEX L^2
;;; ==========================================================================================
(define l2a-L '(L2-SPACE omega cA mu))
(define l2a-H '(CL2-HILBERT omega cA mu))
(define l2a-Hw '(CSIP-CIPS (COMPLEXIFY (SIP-QUOTIENT (L2-SPACE omega cA mu)))))
(define l2a-set '(L2-SET omega cA mu))
(define (l2a-lcl f) (list 'CLASS '(SIP-SETOID (L2-SPACE omega cA mu)) f))
(define (l2a-lpr f g) (list 'LIST (l2a-lcl f) (l2a-lcl g)))
(define (l2a-int f g) (list 'RINTEGRAL 'omega 'cA 'mu (list 'VNB-LAMBDA 'lx_ 'omega (list '* (list f 'lx_) (list g 'lx_)))))
(define (l2a-sp-meas body)
  (sp (make-wff (list 'FORALL 'omega (list 'FORALL 'cA (list 'FORALL 'mu
        (list 'IMPLIES '(IS-MEASURE omega cA mu) body)))))))
;;; f in L2-SET in context: (IN f (VEC (L2-SPACE ..)))
(define (l2a-lv! f)
  (let ((want (list 'IN f (list 'VEC l2a-L))))
    (if (not (dk-asm? want)) (dk-rewrite-h! (list 'IN f l2a-set) l2a-set (list 'VEC l2a-L)))
    want))
(define (l2a-lbase!)
  (if (not (dk-asm? (list 'IS-SEMI-INNER-PRODUCT-SPACE l2a-L))) (dk-cite! 'l2-space-is-sip 'omega 'cA 'mu))
  (dk-cite! 'l2-space-vec 'omega 'cA 'mu))

(sp (make-wff (list 'FORALL 'omega (list 'FORALL 'cA (list 'FORALL 'mu (list '== l2a-H l2a-Hw))))))
(di)
(mac 'CL2-HILBERT)
(if (l2a-open?) (qrfl))
(l2a-qed! 'cl2-hilbert-unfold)

;;; TARGET 1: complex L^2 is a Hilbert space
(l2a-sp-meas (list 'IS-HILBERT-SPACE l2a-H))
(dk-peel!)
(dk-cite! 'l2-quotient-is-real-hilbert 'omega 'cA 'mu)
(dk-cite! 'complexify-hilbert (list 'SIP-QUOTIENT l2a-L))
(l2a-rw! (dk-cite! 'cl2-hilbert-unfold 'omega 'cA 'mu))
(if (l2a-open?) (ass))
(l2a-qed! 'cl2-hilbert-is-hilbert-space)
(alias! 'cl2-hilbert-is-hilbert-space "complex L^2 modulo null functions is a complex Hilbert space")

;;; the vectors: pairs of a.e.-classes
(l2a-sp-meas (list '== (list 'VEC l2a-H)
                   (list 'CARTESIAN (list 'QUOTIENT (list 'SIP-SETOID l2a-L)) (list 'QUOTIENT (list 'SIP-SETOID l2a-L)))))
(dk-peel!)
(l2a-lbase!)
(l2a-rw! (dk-cite! 'cl2-hilbert-unfold 'omega 'cA 'mu))
(l2a-rw! (dk-cite! 'cxq-vec l2a-L))
(if (l2a-open?) (qrfl))
(l2a-qed! 'cl2-hilbert-vec)

(l2a-sp-meas (forall-guarded '(f1 f2) (list (list 'IN 'f1 l2a-set) (list 'IN 'f2 l2a-set))
  (list 'IN (l2a-lpr 'f1 'f2) (list 'VEC l2a-H))))
(dk-peel!)
(l2a-lbase!)
(l2a-lv! 'f1) (l2a-lv! 'f2)
(l2a-rw! (dk-cite! 'cl2-hilbert-unfold 'omega 'cA 'mu))
(dk-cite! 'cxq-pair-in l2a-L 'f1 'f2)
(if (l2a-open?) (ass))
(l2a-qed! 'cl2-hilbert-pair-in)

(l2a-sp-meas (forall-guarded '(x_) (list (list 'IN 'x_ (list 'VEC l2a-H)))
  (list 'FORSOME 'f1 (list 'AND (list 'IN 'f1 l2a-set)
    (list 'FORSOME 'f2 (list 'AND (list 'IN 'f2 l2a-set) (list '= 'x_ (l2a-lpr 'f1 'f2))))))))
(dk-peel!)
(l2a-lbase!)
(dk-cite! 'cl2-hilbert-unfold 'omega 'cA 'mu)
(dk-rewrite-h! (list 'IN 'x_ (list 'VEC l2a-H)) l2a-H l2a-Hw)
(subst (list '= '(L2-SET omega cA mu) (list 'VEC l2a-L)))
(dk-cite! 'cxq-rep l2a-L 'x_)
(if (l2a-open?) (ass))
(l2a-qed! 'cl2-hilbert-rep)

;;; the complex form on pairs of classes of square-integrable functions
(define l2a-lip-rhs
  (list '+ (list '+ (l2a-int 'f1 'g1) (l2a-int 'f2 'g2))
           (list '* '+i (list '- (l2a-int 'f2 'g1) (l2a-int 'f1 'g2)))))
(l2a-sp-meas (forall-guarded '(f1 f2 g1 g2)
                (list (list 'IN 'f1 l2a-set) (list 'IN 'f2 l2a-set) (list 'IN 'g1 l2a-set) (list 'IN 'g2 l2a-set))
  (list '= (list (list 'IP l2a-H) (l2a-lpr 'f1 'f2) (l2a-lpr 'g1 'g2)) l2a-lip-rhs)))
(dk-peel!)
(l2a-lbase!)
(for-each l2a-lv! '(f1 f2 g1 g2))
(l2a-rw! (dk-cite! 'cl2-hilbert-unfold 'omega 'cA 'mu))
(subst (dk-cite! 'cxq-ip-classes l2a-L 'f1 'f2 'g1 'g2))
(l2a-rw! (dk-cite! 'l2-space-rip 'omega 'cA 'mu))
(for-each (lambda (pr)
            (let* ((ty (dk-cite! 'sip-rip-type l2a-L (car pr) (cdr pr)))
                   (ty2 (dk-rewrite-h! ty (list 'RIP l2a-L) '(L2-RIP omega cA mu)))
                   (ve (dk-cite! 'l2-rip-value 'omega 'cA 'mu (car pr) (cdr pr))))
              (dk-rewrite-h! ty2 (cadr ve) (caddr ve))
              (subst ve)))
          '((f1 . g1) (f2 . g2) (f2 . g1) (f1 . g2)))
(fact 'cc-i-in)
(if (l2a-open?) (rfl))
(l2a-qed! 'cl2-hilbert-ip-classes)

;;; two square-integrable functions have the same class iff they agree almost everywhere
(l2a-sp-meas (forall-guarded '(f g) (list (list 'IN 'f l2a-set) (list 'IN 'g l2a-set))
  (list 'IFF (list '= (l2a-lcl 'f) (l2a-lcl 'g))
        '(FORSOME aen_ (AND (IS-NULL-SET omega cA mu aen_)
           (FORALL aex_ (IMPLIES (IN aex_ omega) (IMPLIES (NOT (IN aex_ aen_)) (= (f aex_) (g aex_))))))))))
(dk-peel!)
(l2a-lbase!)
(l2a-lv! 'f) (l2a-lv! 'g)
(dk-cite! 'sip-class-eq-iff l2a-L 'f 'g)
(dk-cite! 'l2-null-iff-ae 'omega 'cA 'mu 'f 'g)
(if (l2a-open?) (prop))
(l2a-qed! 'cl2-class-eq-iff-ae)
