;;; theorem-library/module-laws.scm -- the generic laws of a MODULE: the vector group
;;; (associativity, commutativity, zero, inverse, the differences x - y = x + (-y)) and the
;;; scalar action on negatives and differences.  Prefix mlaw-.  Library: linear-algebra.
;;; (MODLAWS, 2026-10-24, the user's order: one early home for the module laws.)
;;;
;;; WHY THIS FILE.  These laws hold in ANY module and were proven in two ANALYSIS files,
;;; theorem-library/hahn-banach-sublinear.scm (the hbs- group laws, section A) and
;;; theorem-library/frechet-metric.scm (the frm-v- / frm-act- laws, sections 1, 12, 14),
;;; where no linear-algebra file could cite them (the library gate).  They are moved here
;;; UNDER THEIR OLD NAMES AND WITH THEIR OLD STATEMENTS (equal?), so no citer changes, and
;;; the proofs are the old ones with the helpers copied under the prefix mlaw-.
;;;
;;; THE THEOREMS (old file in brackets):
;;;   [hbs] hbs-vadd-assoc, hbs-vadd-comm, hbs-vzero-lr, hbs-vzero-r, hbs-vzero-l,
;;;         hbs-interchange, hbs-sub-vec
;;;   [frm] frm-mvag-inv, frm-v-right-inv, frm-v-neg-add, frm-v-neg-neg, frm-v-sub-anti,
;;;         frm-v-sub-chain, frm-v-sub-zero-eq, frm-v-sub-shift, frm-v-sub-add,
;;;         frm-module-vec-set, frm-act-neg-vec, frm-act-neg-scal, frm-act-sub-vec,
;;;         frm-act-sub-scal, frm-act-diff, frm-v-sub-zero
;;; NOT MOVED: the hbs- laws at REAL scalars (hbs-carr .. hbs-cancel-l, hbs-sub-act), whose
;;; statements carry the pin SCAL(m) = NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD)
;;; (normed-field vocabulary: analysis); frm-linear-sub / -zero / -homog, stated with
;;; IS-LINEAR-MAP (structure-library/frechet-open-mapping: analysis).
;;;
;;; LOAD WINDOW: see the report (scratchpad/triage/MODLAWS-REPORT.md); the latest
;;; citations are the MODULE-VECTOR-AG companions minted by the restricted re-runs in
;;; theorem-library/rake-algebra2.scm and theorem-library/cancellation.scm, and
;;; module-zero-act / module-act-zero-vec.  The file must load BEFORE
;;; structure-library/sip-vocab (SIP-AS-MODULE), so that the def-functor there still
;;; mints the -sip-as-module companions sip-a.scm cites.
;;; No late tactic, no top-level macro (compilable).  Every theorem proven modulo 0.

;;; ---- the mlaw- kit (copied from frm- and hbs-) -------------------------------

(define (mlaw-sub m a b) (list (list 'VADD m) a (list (list 'VNEG m) b)))
(define (mlaw-add m a b) (list (list 'VADD m) a b))
(define (mlaw-neg m a) (list (list 'VNEG m) a))
(define (mlaw-act m r v) (list (list 'ACT m) r v))
(define (mlaw-asm? f) (if (dk-asm? f) #t #f))
(define (mlaw-once! f thunk) (if (not (mlaw-asm? f)) (thunk)))

;;; (IN v (VEC m)) for a vector term built from typed atoms by VADD / VNEG / VZERO.
(define (mlaw-vec! m v)
  (let ((ty (list 'IN v (list 'VEC m))))
    (if (not (mlaw-asm? ty))
        (cond ((and (pair? v) (equal? (car v) (list 'VADD m)))
               (mlaw-vec! m (cadr v)) (mlaw-vec! m (caddr v))
               (dk-cite! 'module-vadd-type m (cadr v) (caddr v)))
              ((and (pair? v) (equal? (car v) (list 'VNEG m)))
               (mlaw-vec! m (cadr v))
               (dk-cite! 'module-vneg-type m (cadr v)))
              ((equal? v (list 'VZERO m)) (dk-cite! 'module-vzero-in m))
              (#t (error "mlaw-vec!: cannot type" (expression->string v)))))
    (if (not (mlaw-asm? ty)) (error "mlaw-vec!: typing did not land" (expression->string v)))
    ty))

(define (mlaw-fa v dom body) (list 'FORALL v (list 'IMPLIES (list 'IN v dom) body)))
(define (mlaw-mod1 body) (list 'FORALL 'm (list 'IMPLIES '(IS-MODULE m) body)))

(define (mlaw-vstmt vars body)
  (list 'FORALL 'm
    (list 'IMPLIES '(IS-MODULE m)
      (let loop ((vs vars))
        (if (null? vs) body
            (list 'FORALL (car vs)
                  (list 'IMPLIES (list 'IN (car vs) '(VEC m)) (loop (cdr vs)))))))))

(define (mlaw-mstmt vars guards body)
  (list 'FORALL 'm (list 'IMPLIES '(IS-MODULE m) (forall-guarded vars guards body))))

;;; the hbs- laws were filed under the PSS topic `analysis'; they are module laws.
(define (mlaw-qed! name)
  (if (not (proof-done? *ps*))
      (error "module-laws: proof did not close" name (expression->string (dk-goal))))
  (qed name)
  (topic! name 'algebra))

(define (mlaw-subst-all! . eqs) (for-each (lambda (e) (subst e)) eqs))

;;; =====================================================================
;;; (1) THE VECTOR GROUP, read off the IS-MODULE unfold  [hahn-banach-sublinear (A)]
;;; =====================================================================

(define (mlaw-module-law! prop)
  (dk-project! prop 'is-module '(IS-MODULE m)))

(sp (make-wff (mlaw-mod1 (mlaw-fa 'x_ '(VEC m) (mlaw-fa 'y_ '(VEC m) (mlaw-fa 'z_ '(VEC m)
  '(= ((VADD m) ((VADD m) x_ y_) z_) ((VADD m) x_ ((VADD m) y_ z_)))))))))
(dk-peel!)
(let* ((h (mlaw-module-law! '(IS-ASSOCIATIVE (VADD m) (VEC m))))
       (u (dk-landed-1 (lambda () (mac-h 'is-associative h)))))
  (dk-apply! u 'x_ 'y_ 'z_))
(ass)
(mlaw-qed! 'hbs-vadd-assoc)

(sp (make-wff (mlaw-mod1 (mlaw-fa 'x_ '(VEC m) (mlaw-fa 'y_ '(VEC m)
  '(= ((VADD m) x_ y_) ((VADD m) y_ x_)))))))
(dk-peel!)
(let* ((h (mlaw-module-law! '(IS-COMMUTATIVE (VADD m) (VEC m))))
       (u (dk-landed-1 (lambda () (mac-h 'is-commutative h)))))
  (dk-apply! u 'x_ 'y_))
(ass)
(mlaw-qed! 'hbs-vadd-comm)

(sp (make-wff (mlaw-mod1 (mlaw-fa 'x_ '(VEC m)
  '(AND (= ((VADD m) (VZERO m) x_) x_) (= ((VADD m) x_ (VZERO m)) x_))))))
(dk-peel!)
(let* ((h (mlaw-module-law! '(IS-IDENTITY (VADD m) (VZERO m) (VEC m))))
       (u (dk-landed-1 (lambda () (mac-h 'is-identity h)))))
  (dk-apply! u 'x_))
(ass)
(mlaw-qed! 'hbs-vzero-lr)

(sp (make-wff (mlaw-mod1 (mlaw-fa 'x_ '(VEC m) '(= ((VADD m) x_ (VZERO m)) x_)))))
(dk-peel!)
(dk-split-all! (list (dk-cite! 'hbs-vzero-lr 'm 'x_)))
(ass)
(mlaw-qed! 'hbs-vzero-r)

(sp (make-wff (mlaw-mod1 (mlaw-fa 'x_ '(VEC m) '(= ((VADD m) (VZERO m) x_) x_)))))
(dk-peel!)
(dk-split-all! (list (dk-cite! 'hbs-vzero-lr 'm 'x_)))
(ass)
(mlaw-qed! 'hbs-vzero-l)

;;; (a + b) + (c + d) = (a + c) + (b + d)
(sp (make-wff (mlaw-mod1 (mlaw-fa 'a_ '(VEC m) (mlaw-fa 'b_ '(VEC m) (mlaw-fa 'c_ '(VEC m) (mlaw-fa 'd_ '(VEC m)
  '(= ((VADD m) ((VADD m) a_ b_) ((VADD m) c_ d_)) ((VADD m) ((VADD m) a_ c_) ((VADD m) b_ d_))))))))))
(dk-peel!)
(dk-cite! 'module-vadd-type 'm 'c_ 'd_)
(dk-cite! 'module-vadd-type 'm 'b_ 'd_)
(dk-cite! 'module-vadd-type 'm 'b_ 'c_)
(dk-cite! 'module-vadd-type 'm 'c_ 'b_)
(dk-cite! 'hbs-vadd-assoc 'm 'a_ 'b_ '((VADD m) c_ d_))
(subst '(= ((VADD m) ((VADD m) a_ b_) ((VADD m) c_ d_)) ((VADD m) a_ ((VADD m) b_ ((VADD m) c_ d_)))))
(dk-cite! 'hbs-vadd-assoc 'm 'b_ 'c_ 'd_)
(subst '(= ((VADD m) b_ ((VADD m) c_ d_)) ((VADD m) ((VADD m) b_ c_) d_)))
(dk-cite! 'hbs-vadd-comm 'm 'b_ 'c_)
(subst '(= ((VADD m) b_ c_) ((VADD m) c_ b_)))
(dk-cite! 'hbs-vadd-assoc 'm 'c_ 'b_ 'd_)
(subst '(= ((VADD m) ((VADD m) c_ b_) d_) ((VADD m) c_ ((VADD m) b_ d_))))
(dk-cite! 'hbs-vadd-assoc 'm 'a_ 'c_ '((VADD m) b_ d_))
(subst '(= ((VADD m) a_ ((VADD m) c_ ((VADD m) b_ d_))) ((VADD m) ((VADD m) a_ c_) ((VADD m) b_ d_))))
(rfl)
(mlaw-qed! 'hbs-interchange)

;;; a member of a submodule is a vector  [hahn-banach-sublinear (F)]
(sp (make-wff (mlaw-mod1 '(FORALL s (IMPLIES (IS-SUBMODULE m s) (FORALL x_ (IMPLIES (IN x_ s) (IN x_ (VEC m)))))))))
(dk-peel!)
(dk-cite! 'submodule-subset 'm 's)
(dk-cite! 'subset-mem-fwd 's '(VEC m) 'x_)
(ass)
(mlaw-qed! 'hbs-sub-vec)

;;; =====================================================================
;;; (2) THE VECTOR GROUP AS MODULE-VECTOR-AG: the fourth read-off, and the group
;;;     laws on VEC m that the differences x - y need.  [frechet-metric (1)]
;;; =====================================================================

;;; ---- the read-off procedure of ag-view-read-offs.scm (avr-read-off!), local copy --
(define (mlaw-read-off! name var is-pred is-mac view acc val witness)
  (sp (make-wff (list 'FORALL var
                  (list 'IMPLIES is-pred
                    (list '= (list acc (list view var)) val)))))
  (di)
  (di)
  (mac-h is-mac is-pred)
  (dk-split-all!)
  (if (not (member witness (dk-asms)))
      (error "mlaw-read-off!: the typing conjunct is not in the context"
             name (expression->string witness)))
  (slot acc)
  (mac view)
  (nth-r)
  (rfl)
  (if (not (proof-done? *ps*))
      (error "mlaw-read-off!: proof did not close" name (dk-goal)))
  (qed name))

(mlaw-read-off! 'frm-mvag-inv 'md '(IS-MODULE md) 'is-module 'MODULE-VECTOR-AG
               'INV '(VNEG md) '(IN (VNEG md) (FUN (VEC md) (VEC md))))

;;; cite an ABELIAN-GROUP law at MODULE-VECTOR-AG(m) and land it in the module's own
;;; vocabulary (VADD / VZERO / VNEG / VEC).  The VECS must be typed in VEC m.
(define (mlaw-ag! thm m . vecs)
  (let* ((g (list 'MODULE-VECTOR-AG m))
         (rw (lambda (f from to) (if (dk-contains? f from) (dk-rewrite-h! f from to) f))))
    (dk-cite! 'module-vector-ag-is-abelian-group m)
    (dk-cite! 'mvag-carr m) (dk-cite! 'mvag-op m) (dk-cite! 'mvag-id m)
    (dk-cite! 'frm-mvag-inv m)
    (for-each (lambda (v)
                (let ((ty (mlaw-vec! m v)))
                  (mlaw-once! (list 'IN v (list 'CARR g))
                             (lambda () (dk-rewrite-h! ty (list 'VEC m) (list 'CARR g))))))
              vecs)
    (let* ((f0 (apply dk-cite! thm g vecs))
           (f1 (rw f0 (list 'OPR g) (list 'VADD m)))
           (f2 (rw f1 (list 'INV g) (list 'VNEG m)))
           (f3 (rw f2 (list 'IDEN g) (list 'VZERO m))))
      f3)))

(define (mlaw-ag-lemma! name thm vars body)
  (sp (make-wff (mlaw-vstmt vars body)))
  (dk-peel!)
  (apply mlaw-ag! thm 'm vars)
  (ass)
  (qed name))

(mlaw-ag-lemma! 'frm-v-right-inv 'abelian-group-right-inv '(x)
  (list '= (mlaw-sub 'm 'x 'x) '(VZERO m)))
(mlaw-ag-lemma! 'frm-v-neg-add 'abelian-group-inv-opr '(x y)
  (list '= (mlaw-neg 'm (mlaw-add 'm 'x 'y)) (mlaw-add 'm (mlaw-neg 'm 'x) (mlaw-neg 'm 'y))))
(mlaw-ag-lemma! 'frm-v-neg-neg 'abelian-group-inv-inv '(x)
  (list '= (mlaw-neg 'm (mlaw-neg 'm 'x)) 'x))

;;; ---- differences x - y = x + (-y) ------------------------------------

;;; -(x - y) = y - x
(sp (make-wff (mlaw-vstmt '(x y) (list '= (mlaw-neg 'm (mlaw-sub 'm 'x 'y)) (mlaw-sub 'm 'y 'x)))))
(dk-peel!)
(mlaw-vec! 'm (mlaw-neg 'm 'y)) (mlaw-vec! 'm (mlaw-neg 'm 'x))
(let* ((e1 (dk-cite! 'frm-v-neg-add 'm 'x (mlaw-neg 'm 'y)))
       (e2 (dk-cite! 'frm-v-neg-neg 'm 'y))
       (e3 (dk-cite! 'hbs-vadd-comm 'm (mlaw-neg 'm 'x) 'y)))
  (mlaw-subst-all! e1 e2)
  (ass))
(qed 'frm-v-sub-anti)

;;; (x - y) + (y - z) = x - z
(sp (make-wff (mlaw-vstmt '(x y z)
  (list '= (mlaw-add 'm (mlaw-sub 'm 'x 'y) (mlaw-sub 'm 'y 'z)) (mlaw-sub 'm 'x 'z)))))
(dk-peel!)
(for-each (lambda (v) (mlaw-vec! 'm v))
          (list (mlaw-neg 'm 'x) (mlaw-neg 'm 'y) (mlaw-neg 'm 'z) (mlaw-sub 'm 'x 'z)))
(let* ((e1 (dk-cite! 'hbs-vadd-comm 'm 'y (mlaw-neg 'm 'z)))
       (e2 (dk-cite! 'hbs-interchange 'm 'x (mlaw-neg 'm 'y) (mlaw-neg 'm 'z) 'y))
       (e3 (dk-cite! 'hbs-vadd-comm 'm (mlaw-neg 'm 'y) 'y))
       (e4 (dk-cite! 'frm-v-right-inv 'm 'y))
       (e5 (dk-cite! 'abelian-group-right-id-module-vector-ag 'm (mlaw-sub 'm 'x 'z))))
  (mlaw-subst-all! e1 e2 e3 e4 e5)
  (rfl))
(qed 'frm-v-sub-chain)

;;; x - y = 0  =>  x = y
(sp (make-wff (mlaw-vstmt '(x y)
  (list 'IMPLIES (list '= (mlaw-sub 'm 'x 'y) '(VZERO m)) '(= x y)))))
(dk-peel!)
(mlaw-vec! 'm (mlaw-neg 'm 'y)) (mlaw-vec! 'm (mlaw-neg 'm 'x))
(let* ((e1 (dk-cite! 'abelian-group-inverse-unique-module-vector-ag 'm 'x (mlaw-neg 'm 'y)))
       (e2 (dk-cite! 'frm-v-neg-neg 'm 'x))
       (e3 (dk-cite! 'frm-v-neg-neg 'm 'y)))
  (subst (list '= 'x (mlaw-neg 'm (mlaw-neg 'm 'x))))
  (subst (list '= (mlaw-neg 'm 'x) (mlaw-neg 'm 'y)))
  (ass))
(qed 'frm-v-sub-zero-eq)

;;; (x + r) - (y + r) = x - y      (translation invariance of the difference)
(sp (make-wff (mlaw-vstmt '(x y r)
  (list '= (mlaw-sub 'm (mlaw-add 'm 'x 'r) (mlaw-add 'm 'y 'r)) (mlaw-sub 'm 'x 'y)))))
(dk-peel!)
(for-each (lambda (v) (mlaw-vec! 'm v))
          (list (mlaw-neg 'm 'y) (mlaw-neg 'm 'r) (mlaw-sub 'm 'x 'y)))
(let* ((e1 (dk-cite! 'frm-v-neg-add 'm 'y 'r))
       (e2 (dk-cite! 'hbs-interchange 'm 'x 'r (mlaw-neg 'm 'y) (mlaw-neg 'm 'r)))
       (e3 (dk-cite! 'frm-v-right-inv 'm 'r))
       (e4 (dk-cite! 'abelian-group-right-id-module-vector-ag 'm (mlaw-sub 'm 'x 'y))))
  (mlaw-subst-all! e1 e2 e3 e4)
  (rfl))
(qed 'frm-v-sub-shift)

;;; (x + y) - (u + v) = (x - u) + (y - v)
(sp (make-wff (mlaw-vstmt '(x y u v)
  (list '= (mlaw-sub 'm (mlaw-add 'm 'x 'y) (mlaw-add 'm 'u 'v))
           (mlaw-add 'm (mlaw-sub 'm 'x 'u) (mlaw-sub 'm 'y 'v))))))
(dk-peel!)
(for-each (lambda (v) (mlaw-vec! 'm v))
          (list (mlaw-neg 'm 'u) (mlaw-neg 'm 'v) (mlaw-add 'm (mlaw-sub 'm 'x 'u) (mlaw-sub 'm 'y 'v))))
(let* ((e1 (dk-cite! 'frm-v-neg-add 'm 'u 'v))
       (e2 (dk-cite! 'hbs-interchange 'm 'x 'y (mlaw-neg 'm 'u) (mlaw-neg 'm 'v))))
  (mlaw-subst-all! e1 e2)
  (rfl))
(qed 'frm-v-sub-add)

;;; x - 0 = x    [frechet-metric (14)]
(sp (make-wff (mlaw-vstmt '(x) (list '= (mlaw-sub 'm 'x '(VZERO m)) 'x))))
(dk-peel!)
(let ((z '(VZERO m)))
  (dk-cite! 'module-vzero-in 'm)
  (dk-cite! 'abelian-group-right-id-module-vector-ag 'm z)
  (dk-cite! 'abelian-group-inverse-unique-module-vector-ag 'm z z)
  (subst (list '= (mlaw-neg 'm z) z))
  (dk-cite! 'abelian-group-right-id-module-vector-ag 'm 'x)
  (ass))
(qed 'frm-v-sub-zero)

;;; ---- the vector carrier is a set  [frechet-metric (3)] -----------------------

(define (mlaw-project! name pred mac-name stmt)
  (sp (make-wff stmt))
  (let loop ((n 0))
    (if (not (dk-asm? pred))
        (begin (if (> n 4) (error "mlaw-project!: guard did not land" name)) (di) (loop (+ n 1)))))
  (mac-h mac-name pred)
  (dk-split-all!)
  (ass)
  (qed name))

(mlaw-project! 'frm-module-vec-set '(IS-MODULE m) 'is-module
  '(FORALL m (IMPLIES (IS-MODULE m) (IN (VEC m) SET))))

;;; =====================================================================
;;; (3) THE SCALAR ACTION on negatives and differences  [frechet-metric (12)]
;;; =====================================================================

;;; r.(-x) = -(r.x)
(sp (make-wff (mlaw-mstmt '(r x) '((IN r (CARR (SCAL m))) (IN x (VEC m)))
  (list '= (mlaw-act 'm 'r (mlaw-neg 'm 'x)) (mlaw-neg 'm (mlaw-act 'm 'r 'x))))))
(dk-peel!)
(let* ((nx (mlaw-neg 'm 'x)) (ax (mlaw-act 'm 'r 'x)) (anx (mlaw-act 'm 'r nx)))
  (mlaw-vec! 'm nx)
  (dk-cite! 'module-act-type 'm 'r 'x)
  (dk-cite! 'module-act-type 'm 'r nx)
  (let* ((e1 (dk-cite! 'module-act-distrib-vec 'm 'r 'x nx))
         (e2 (dk-cite! 'frm-v-right-inv 'm 'x))
         (e3 (dk-cite! 'module-act-zero-vec 'm 'r)))
    (dk-have! (list '= (mlaw-add 'm ax anx) '(VZERO m))
      (lambda ()
        (subst (list '= (mlaw-add 'm ax anx) (mlaw-act 'm 'r (mlaw-add 'm 'x nx))))
        (subst e2)
        (ass)))
    (dk-cite! 'abelian-group-inverse-unique-module-vector-ag 'm ax anx)
    (ass)))
(qed 'frm-act-neg-vec)

;;; (-r).x = -(r.x)
(sp (make-wff (mlaw-mstmt '(r x) '((IN r (CARR (SCAL m))) (IN x (VEC m)))
  (list '= (mlaw-act 'm '((NEG (SCAL m)) r) 'x) (mlaw-neg 'm (mlaw-act 'm 'r 'x))))))
(dk-peel!)
(let* ((nr '((NEG (SCAL m)) r)) (ax (mlaw-act 'm 'r 'x)) (anx (mlaw-act 'm nr 'x)))
  (dk-cite! 'module-scalar-ring 'm)
  (dk-cite! 'ring-neg-in-carr '(SCAL m) 'r)
  (dk-cite! 'module-act-type 'm 'r 'x)
  (dk-cite! 'module-act-type 'm nr 'x)
  (let* ((e1 (dk-cite! 'module-act-distrib-scalar 'm 'r nr 'x))
         (e2 (dk-cite! 'ring-add-right-inv '(SCAL m) 'r))
         (e3 (dk-cite! 'module-zero-act 'm 'x)))
    (dk-have! (list '= (mlaw-add 'm ax anx) '(VZERO m))
      (lambda ()
        (subst (list '= (mlaw-add 'm ax anx) (mlaw-act 'm (list '(ADD (SCAL m)) 'r nr) 'x)))
        (subst e2)
        (ass)))
    (dk-cite! 'abelian-group-inverse-unique-module-vector-ag 'm ax anx)
    (ass)))
(qed 'frm-act-neg-scal)

;;; r.(x - y) = r.x - r.y
(sp (make-wff (mlaw-mstmt '(r x y) '((IN r (CARR (SCAL m))) (IN x (VEC m)) (IN y (VEC m)))
  (list '= (mlaw-act 'm 'r (mlaw-sub 'm 'x 'y)) (mlaw-sub 'm (mlaw-act 'm 'r 'x) (mlaw-act 'm 'r 'y))))))
(dk-peel!)
(let ((ny (mlaw-neg 'm 'y)))
  (mlaw-vec! 'm ny)
  (dk-cite! 'module-act-type 'm 'r 'x)
  (dk-cite! 'module-act-type 'm 'r 'y)
  (subst (dk-cite! 'module-act-distrib-vec 'm 'r 'x ny))
  (subst (dk-cite! 'frm-act-neg-vec 'm 'r 'y))
  (mlaw-vec! 'm (mlaw-sub 'm (mlaw-act 'm 'r 'x) (mlaw-act 'm 'r 'y)))
  (rfl))
(qed 'frm-act-sub-vec)

;;; (r - s).x = r.x - s.x
(sp (make-wff (mlaw-mstmt '(r s x) '((IN r (CARR (SCAL m))) (IN s (CARR (SCAL m))) (IN x (VEC m)))
  (list '= (mlaw-act 'm '((ADD (SCAL m)) r ((NEG (SCAL m)) s)) 'x)
           (mlaw-sub 'm (mlaw-act 'm 'r 'x) (mlaw-act 'm 's 'x))))))
(dk-peel!)
(let ((ns '((NEG (SCAL m)) s)))
  (dk-cite! 'module-scalar-ring 'm)
  (dk-cite! 'ring-neg-in-carr '(SCAL m) 's)
  (dk-cite! 'module-act-type 'm 'r 'x)
  (dk-cite! 'module-act-type 'm 's 'x)
  (subst (dk-cite! 'module-act-distrib-scalar 'm 'r ns 'x))
  (subst (dk-cite! 'frm-act-neg-scal 'm 's 'x))
  (mlaw-vec! 'm (mlaw-sub 'm (mlaw-act 'm 'r 'x) (mlaw-act 'm 's 'x)))
  (rfl))
(qed 'frm-act-sub-scal)

;;; r.x - s.y = r.(x - y) + (r - s).y
(sp (make-wff (mlaw-mstmt '(r s x y)
  '((IN r (CARR (SCAL m))) (IN s (CARR (SCAL m))) (IN x (VEC m)) (IN y (VEC m)))
  (list '= (mlaw-sub 'm (mlaw-act 'm 'r 'x) (mlaw-act 'm 's 'y))
           (mlaw-add 'm (mlaw-act 'm 'r (mlaw-sub 'm 'x 'y))
                       (mlaw-act 'm '((ADD (SCAL m)) r ((NEG (SCAL m)) s)) 'y))))))
(dk-peel!)
(let ((rx (mlaw-act 'm 'r 'x)) (ry (mlaw-act 'm 'r 'y)) (sy (mlaw-act 'm 's 'y)))
  (dk-cite! 'module-act-type 'm 'r 'x)
  (dk-cite! 'module-act-type 'm 'r 'y)
  (dk-cite! 'module-act-type 'm 's 'y)
  (subst (dk-cite! 'frm-act-sub-vec 'm 'r 'x 'y))
  (subst (dk-cite! 'frm-act-sub-scal 'm 'r 's 'y))
  (subst (dk-cite! 'frm-v-sub-chain 'm rx ry sy))
  (mlaw-vec! 'm (mlaw-sub 'm rx sy))
  (rfl))
(qed 'frm-act-diff)
