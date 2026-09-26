;;; theorem-library/rake-finsum-core.scm -- the FINSUM CORE, proven.
;;; Rake batch M (2026-09-17).  Nine of the batch's ten leaves; the tenth
;;; (finsum-embed) is BLOCKED and its obstacle is stated at the end of this
;;; header.
;;;
;;; Every statement marked "copied literally" is the support's own S-expression
;;; from its definition site (finsum-additive.scm's `tf' / `tfin' builders are
;;; reproduced here as rkq-tf / rkq-tfin, so the installed formula is
;;; byte-identical; each qed printed "re-installing the same statement").
;;;
;;; THE SUPPORTS PROVEN, and where each is asserted today:
;;;   ord-segment-insert          theorem-library/finsum-additive.scm:102   modulo 0
;;;   finsum-singleton            theorem-library/finsum-singleton.scm:8    modulo 0
;;;   finsum-ord-peel             theorem-library/finsum-additive.scm:296
;;;                                             modulo {finsum-well-defined}
;;;   finsum-ring-distrib-left    theorem-library/finsum-additive.scm:153   modulo 0
;;;   finsum-ring-distrib-right   theorem-library/finsum-additive.scm:174   modulo 0
;;;   finsum-add                  theorem-library/finsum-additive.scm:136   modulo 0
;;;   finsum-act-collect-gen      structure-library/mod-seq.scm:149         modulo 0
;;;   finsum-fubini               theorem-library/finsum-fubini.scm:19      modulo 0
;;;   finsum-ring-scalar-zz       theorem-library/finsum-additive.scm:221
;;;                        modulo {zz-act-zero, zz-act-one, zz-act-add,
;;;                                zz-act-neg-sign, zz-act-type}  [informal]
;;; and one UNWARRANTED axiom retired on the way:
;;;   comm-monoid-opr-comm        structure-library/monoid.scm:61           modulo 0
;;;
;;; NEW THEOREMS this file installs (none of them a PSS name):
;;;   cra-is-rag                  COMMUTATIVE-RING-ADDITIVE-AG(rng) == RING-ADDITIVE-AG(rng)
;;;   comm-monoid-assoc, comm-monoid-left-id, comm-monoid-opr-interchange
;;;   sum-ag-comm-monoid-type-ptwise, sum-ag-comm-monoid-add-ind
;;;   sum-ag-act-collect-ind, sum-ag-fubini-ind
;;;   ras-inv, commutative-ring-mul-comm, ring-scalar-zz-nn
;;;
;;; THE ROUTE.  As in rake-finsum-laws*.scm: a FINSUM is a SUM-AG along the
;;; chosen enumeration, so every law about ONE index set is a law about a FOLD
;;; and `ni' on the fold LENGTH does the work.  Three things are new here.
;;;
;;; (1) `cra-is-rag' is the functoid-unfold recipe applied to two VIEWS:
;;; COMMUTATIVE-RING-ADDITIVE-AG and RING-ADDITIVE-AG have the same def-functor
;;; body, so `(di) (mac ...) (mac ...) (qrfl)' proves them quasi-equal in four
;;; lines, and the two COMMUTATIVE-RING distributions are then one `subst' plus
;;; one `fact' of their -gen forms (rake-finsum-laws2.scm).  Any pair of views
;;; with the same slot list is the same three lines.
;;;
;;; (2) The COMM-MONOID layer needed its own projections.  `monoid-assoc',
;;; `monoid-left-id' and `comm-monoid-opr-comm' are UNWARRANTED
;;; `theory-add-axiom!'s (monoid.scm:17, :27, :61), so a proof citing them bills
;;; `trust: none'.  They are conjuncts of the IS-COMM-MONOID definition;
;;; subtype-laws.scm's `stl--project!' shape proves all three.
;;; `comm-monoid-opr-comm' is proved under ITS OWN name -- nothing in the tree
;;; cites it and it has no view companion, so retiring the axiom costs nothing;
;;; the two MONOID ones are proved at COMM-MONOID under new names, leaving the
;;; MONOID axioms and whatever view companions they carry alone.
;;;
;;; (3) FUBINI is a DOUBLE FOLD, and the statement that makes it induct is one
;;; in which every family is a VARIABLE: `ff_' the rectangle, curried, so that
;;; `(ff_ i)' is itself a family; `gg_' its transpose, related pointwise; `rs_'
;;; the row sums and `cs_' the column sums, each given by a `==' hypothesis.
;;; `ni' on the ROW count then works: the base is sum-ag-all-id-ind (every
;;; column sum is an empty fold), and the step peels the top row with
;;; sum-ag-succ, peels the top ENTRY off every column sum, and splits the right
;;; side with sum-ag-add-ind.  The ONE lambda in the whole proof is the
;;; truncated column-sum family the IH is instantiated at, and it is applied
;;; only under a `forall j in ORD-SEGMENT(n)' guard, so `lam-b' never owes an
;;; unprovable typing leaf.
;;;
;;; NOT PROVEN: `finsum-embed' (finsum-additive.scm:319, 12 bills), and the
;;; obstacle is exactly the one rake-finsum-laws.scm records.  It relates two
;;; index sets with NO bijection between them, so the fold route does not reach
;;; it: writing S2's enumeration phi2 and S's enumeration phi, the content is
;;; that a fold over ORD-SEGMENT(|S2|) supported on the image of the INJECTION
;;; phi2^-1 . phi equals the fold over ORD-SEGMENT(|S|) along it.  That is the
;;; same combinatorial floor as `sum-ag-permutation-invariance', and it is
;;; reachable two ways, neither of which the tree can take today:
;;;   * set surgery -- induct on |S2 \\ S| via finsum-insert-ag, which wants
;;;     `difference-membership' and a CONVERSE of `card-insert' (CARD X in NN
;;;     from CARD(X u {x}) in NN); neither exists.
;;;   * the enumeration -- build a bijection of ORD-SEGMENT(|S2|) listing S
;;;     first (finsum-insert.scm's `enum-append-is-bijection' is the brick) and
;;;     quote `finsum-well-defined'; this still needs CARD(S2 \\ S) and an
;;;     enumeration of it, i.e. the same surgery.
;;; The single lemma that would close it in about forty lines is
;;;   sum-ag-support-inj:  psi injective from ORD-SEGMENT(M) into ORD-SEGMENT(N),
;;;     g_ typed on ORD-SEGMENT(N) and equal to IDEN(ag) off the image of psi,
;;;     h_(i) == g_(psi i)  =>  SUM-AG(ag,g_,N) = SUM-AG(ag,h_,M)
;;; and it belongs with batch N's permutation-invariance work, not here.
;;;
;;; LOAD WINDOW, by FILE NAME: AFTER theorem-library/rake-finsum-laws2
;;; (position 244 -- `enum-fam-value', `sum-ag-type-ptwise', `sum-ag-add-ind',
;;; `finsum-ring-distrib-left-gen', `finsum-ring-distrib-right-gen').  The
;;; next-latest citations are interval-card-in-nn 242 (nothing cited, but
;;; laws2 is below it), card-image-finite 241, rake-finsum-typing 229
;;; (comm-monoid-carrier-closed-opr, comm-monoid-identity-in-carr,
;;; enum-fam-comm-monoid-in-fun), rake-algebra2 228 (ring-neg-mul-left),
;;; nn-parity-proof 213 (nn-succ-plus-one), ring-zero-one-power 211
;;; (ring-mul-zero-right), cancellation 210
;;; (abelian-group-idempotent-is-id-module-vector-ag), finsum-single-support
;;; 202, finsum-type-proof 201 (sum-ag-all-id-ind), op-typing 200
;;; (ring-add-closed, ring-carrier-closed-mul, ring-neg-in-carr),
;;; subtype-laws 199, ag-view-read-offs 161 (ras-/mvag- read-offs),
;;; finsum-insert 155 (fin-enum-is-bijection), card-singleton-proof 156,
;;; ord-segment-nn-subset-proof 154, ord-segment-nn-succ-proof 153.
;;; BEFORE theorem-library/matact-assoc-proof (370), the earliest PROVEN citer
;;; of finsum-act-collect-gen.  I.e. [245, 370).
;;;
;;; ONE INTEGRATOR ACTION BEYOND THE USUAL, and it is forced: the only proven
;;; citer of `finsum-fubini' is `finsum-fubini-c', proved in
;;; theorem-library/rake-finsum-laws.scm (243) -- ABOVE this file.  Retiring the
;;; support at theorem-library/finsum-fubini.scm:19 without moving that block
;;; leaves rake-finsum-laws.scm citing a theorem that no longer exists at its
;;; position.  Move the `finsum-fubini-c' block (rake-finsum-laws.scm, the
;;; section headed "------ fubini-c", 25 lines) to AFTER this file, where it
;;; becomes `modulo 0' instead of `modulo {finsum-fubini}'.
;;;
;;; Helper prefix: rkq-.
(define (rkq-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkq: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkq: proof not complete" name))))
(define (rkq-pick-head head what) (dk-pick (dk-head? head) what))
(define (rkq-guarded-forall? f dom)
  (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3)
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((a (cadr b)))
                (and (pair? a) (eq? (car a) 'IN) (= (length a) 3)
                     (if (procedure? dom) (dom (caddr a)) (equal? (caddr a) dom))))))))
(define (rkq-guarded-forall-inner? f dom pred)
  (and (rkq-guarded-forall? f dom) (pred (caddr (caddr f)))))
(define (rkq-seg-dom? d) (and (pair? d) (eq? (car d) 'ORD-SEGMENT)))
(define (rkq-seg-var landed)
  (let ((f (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'ORD-SEGMENT)))
                     landed)))
    (if f (cadr f) (error "rkq-seg-var: none" (map expression->string landed)))))
(define (rkq-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rkq-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rkq-leaf: ambiguous leaf for" what))
          (#t (car hits)))))
(define (rkq-nn-var)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                  (eq? (caddr f) 'NN))) "n in NN")))
(define (rkq-imps . args)
  (let loop ((a args)) (if (null? (cdr a)) (car a) (list 'IMPLIES (car a) (loop (cdr a))))))
(define (rkq-foralls vars body)
  (fold-right (lambda (v b) (list 'FORALL v b)) body vars))
(define (rkq-o ag x y) (list (list 'OPR ag) x y))
(define (rkq-seg t) (list 'ORD-SEGMENT t))
(define (rkq-in x s) (list 'IN x s))
(define (rkq-gf v dom body) (list 'FORALL v (list 'IMPLIES (rkq-in v dom) body)))


(define (rkq-tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
(define (rkq-tfin S body)
  (list 'FORALL S (list 'IMPLIES (list 'IN S 'SET)
    (list 'IMPLIES (list 'IN (list 'CARD S) 'NN) body))))

;; H is a guarded universal over ORD-SEGMENT(succ n); land its restriction to
;; ORD-SEGMENT(n).  BODY-AT builds the inner formula from a variable.
(define (rkq-restrict! h nv body-at)
  (let ((segN (list 'ORD-SEGMENT nv))
        (segS (list 'ORD-SEGMENT (list 'succ nv))))
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ segN) (body-at 'i_)))
           (lambda ()
             (let* ((landed (dk-peel!)) (iv (rkq-seg-var landed)))
               (have! (list 'IN iv segS)
                      (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! h iv)
               (ass))))))

;; from (IN FAM (FUN NN (CARR m))) in context, land the pointwise typing on
;; ORD-SEGMENT(NC) that the fold-length lemmas want.
(define (rkq-ptwise-from-fun! fam nc mv)
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nc))
                                 (list 'IN (list fam 'i_) (list 'CARR mv))))
         (lambda ()
           (let* ((landed (dk-peel!)) (iv (rkq-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c fam 'NN (list 'CARR mv) iv)
             (ass)))))

;; (IN t (CARR from)) in context, want (IN t to) -- or the other way.
(define (rkq-carr-bridge! t from to)
  (have! (list 'IN t to)
         (lambda () (subst (list '= to from)) (ass))))

;;; commutative-ring-additive-ag-is-ring-additive-ag
(sp (make-wff '(FORALL rng (== (COMMUTATIVE-RING-ADDITIVE-AG rng) (RING-ADDITIVE-AG rng)))))
(di)
(mac 'COMMUTATIVE-RING-ADDITIVE-AG)
(mac 'RING-ADDITIVE-AG)
(show)
(qrfl)
(rkq-check! 'cra-is-rag)
(qed 'cra-is-rag)

(define rkq-cra '(COMMUTATIVE-RING-ADDITIVE-AG rng))
(define rkq-rag '(RING-ADDITIVE-AG rng))

;;; finsum-ring-distrib-left -- finsum-additive.scm:153, copied literally.
(sp (make-wff
  (rkq-tf 'rng '(IS-COMMUTATIVE-RING rng)
   (rkq-tf 'r '(IN r (CARR rng))
    (rkq-tfin 'S
     (rkq-tf 'f '(IN f (FUN S (CARR rng)))
      (list '=
        (list '(MUL rng) 'r (list 'FINSUM rkq-cra 'f 'S))
        (list 'FINSUM rkq-cra (list 'VNB-LAMBDA 'z 'S (list '(MUL rng) 'r '(f z))) 'S))))))))
(dk-peel!)
(let* ((gl  (dk-goal))
       (mul (cadr gl))
       (rngv (cadr (car mul)))
       (rv  (cadr mul))
       (rhs (caddr gl))
       (sv  (cadddr rhs))
       (fv  (caddr (caddr mul))))
  (display ";; rkq distrib-left vars: ") (display (list rngv rv sv fv)) (newline)
  (dk-fact! 'commutative-ring-is-ring rngv)
  (dk-fact! 'cra-is-rag rngv)
  (subst (list '== (list 'COMMUTATIVE-RING-ADDITIVE-AG rngv) (list 'RING-ADDITIVE-AG rngv)))
  (dk-fact! 'finsum-ring-distrib-left-gen rngv rv sv fv)
  (ass))
(rkq-check! 'finsum-ring-distrib-left)
(qed 'finsum-ring-distrib-left)
(topic! 'finsum-ring-distrib-left 'algebra)

;;; finsum-ring-distrib-right -- finsum-additive.scm:174, copied literally.
(sp (make-wff
  (rkq-tf 'rng '(IS-COMMUTATIVE-RING rng)
   (rkq-tf 'r '(IN r (CARR rng))
    (rkq-tfin 'S
     (rkq-tf 'f '(IN f (FUN S (CARR rng)))
      (list '=
        (list '(MUL rng) (list 'FINSUM rkq-cra 'f 'S) 'r)
        (list 'FINSUM rkq-cra (list 'VNB-LAMBDA 'z 'S (list '(MUL rng) '(f z) 'r)) 'S))))))))
(dk-peel!)
(let* ((gl  (dk-goal))
       (mul (cadr gl))
       (rngv (cadr (car mul)))
       (rv  (caddr mul))
       (rhs (caddr gl))
       (sv  (cadddr rhs))
       (fv  (caddr (cadr mul))))
  (display ";; rkq distrib-right vars: ") (display (list rngv rv sv fv)) (newline)
  (dk-fact! 'commutative-ring-is-ring rngv)
  (dk-fact! 'cra-is-rag rngv)
  (subst (list '== (list 'COMMUTATIVE-RING-ADDITIVE-AG rngv) (list 'RING-ADDITIVE-AG rngv)))
  (dk-fact! 'finsum-ring-distrib-right-gen rngv rv sv fv)
  (ass))
(rkq-check! 'finsum-ring-distrib-right)
(qed 'finsum-ring-distrib-right)
(topic! 'finsum-ring-distrib-right 'algebra)

;;; ================================================== ord-segment-insert
;;; finsum-additive.scm:102, copied literally.
(sp (make-wff
     (rkq-tf 'n '(IN n NN)
       '(= (ORD-SEGMENT (succ n))
           (UNION (ORD-SEGMENT n) (PAIR n n))))))
(dk-peel!)
(let* ((nv  (rkq-nn-var))
       (sn  (list 'succ nv))
       (osn (list 'ORD-SEGMENT nv))
       (oss (list 'ORD-SEGMENT sn))
       (pr  (list 'PAIR nv nv))
       (un  (list 'UNION osn pr)))
  (dk-fact! 'nn-succ-closed nv)
  (dk-fact! 'nn-subset-ord nv)
  (dk-fact! 'nn-subset-ord sn)
  (dk-fact! 'ord-segment-is-set nv)
  (dk-fact! 'ord-segment-is-set sn)
  (dk-fact! 'membership-implies-sethood nv 'NN)
  (have! (list 'AND (list 'IN nv 'SET) (list 'IN nv 'SET)))
  (dk-fact! 'pairing nv nv)
  (have! (list 'AND (list 'IN osn 'SET) (list 'IN pr 'SET)))
  (dk-fact! 'union-set-closure osn pr)
  (have! (list 'AND (list 'IN oss 'SET) (list 'IN un 'SET)))
  (let ((ext (dk-fact! 'extensionality oss un)))
    (have! (list 'FORALL 'x_ (list 'IFF (list 'IN 'x_ oss) (list 'IN 'x_ un)))
           (lambda ()
             (let* ((xv (dk-di-var! (lambda (g) (cadr (cadr g)))))
                    (a  (dk-fact! 'ord-segment-nn-succ nv xv))
                    (b  (dk-fact! 'union-membership osn pr xv))
                    (c  (dk-fact! 'pairing-membership nv nv xv)))
               (dk-only! a b c)
               (prop))))
    (dk-only! ext (list 'FORALL 'x_ (list 'IFF (list 'IN 'x_ oss) (list 'IN 'x_ un))))
    (prop)))
(rkq-check! 'ord-segment-insert)
(qed 'ord-segment-insert)
(topic! 'ord-segment-insert 'plumbing)

;;; ==================================================== finsum-singleton
(sp (make-wff
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL x (IMPLIES (IN x SET)
     (FORALL f (IMPLIES (IN f (FUN (PAIR x x) (CARR ag)))
       (= (FINSUM ag f (PAIR x x)) (f x))))))))))
(dk-peel!)
(let* ((gl  (dk-goal))
       (fs  (cadr gl))
       (agv (cadr fs)) (fv (caddr fs)) (pr (cadddr fs))
       (xv  (cadr pr))
       (nc  (list 'CARD pr))
       (phi (list 'FIN-ENUM pr))
       (s0  '(succ 0))
       (fam2 (list 'ENUM-FAM agv fv phi s0))
       (ca  (list 'CARR agv)))
  (display ";; rkq singleton vars: ") (display (list agv xv fv)) (newline)
  (dk-fact! 'nn-zero-in)
  (dk-fact! 'nn-succ-closed 0)
  (dk-fact! 'abelian-group-is-group agv)
  (dk-fact! 'group-identity-in agv)
  (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
  (dk-fact! 'pairing xv xv)
  (have! (list 'IN xv pr)
         (lambda ()
           (let ((pm (dk-fact! 'pairing-membership xv xv xv)))
             (have! (list '= xv xv) (lambda () (rfl)))
             (dk-only! pm (list '= xv xv))
             (prop))))
  (dk-fact! 'card-singleton xv)                   ; (= nc (succ 0))
  (have! (list 'IN nc 'NN) (lambda () (subst (list '= nc s0)) (ass)))
  (let ((bij (dk-fact! 'fin-enum-is-bijection pr)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! (list 'IN 0 (list 'ORD-SEGMENT s0))
         (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
  (have! (list 'IN 0 (list 'ORD-SEGMENT nc))
         (lambda () (subst (list '= nc s0)) (ass)))
  (dk-fact! 'fun-apply-type-c phi (list 'ORD-SEGMENT nc) pr 0)   ; (IN (phi 0) pr)
  (have! (list '= (list phi 0) xv)
         (lambda ()
           (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
           (let ((pm (dk-fact! 'pairing-membership xv xv (list phi 0))))
             (dk-only! pm (list 'IN (list phi 0) pr))
             (prop))))
  (dk-fact! 'fun-apply-type-c fv pr ca xv)                       ; (IN (f x) (CARR ag))
  (dk-fact! 'enum-fam-value s0 agv fv phi 0)                     ; (== (fam2 0) (f (phi 0)))
  (dk-fact! 'group-left-id agv (list fv xv))
  (mac 'FINSUM)
  (subst (list '= nc s0))
  (mac 'sum-ag-succ)
  (mac 'sum-ag-zero)
  (subst (list '== (list fam2 0) (list fv (list phi 0))))
  (subst (list '= (list phi 0) xv))
  (ass))
(rkq-check! 'finsum-singleton)
(qed 'finsum-singleton)
(topic! 'finsum-singleton 'algebra)

;;; ==================================================== finsum-ord-peel
(sp (make-wff
  (rkq-tf 'ag '(IS-ABELIAN-GROUP ag)
    (rkq-tf 'n '(IN n NN)
      (rkq-tf 'f '(IN f (FUN (ORD-SEGMENT (succ n)) (CARR ag)))
        '(= (FINSUM ag f (ORD-SEGMENT (succ n)))
            ((OPR ag) (FINSUM ag f (ORD-SEGMENT n)) (f n))))))))
(dk-peel!)
(let* ((nv  (rkq-nn-var))
       (gl  (dk-goal))
       (agv (cadr (cadr gl)))
       (fv  (caddr (cadr gl)))
       (sn  (list 'succ nv))
       (osn (list 'ORD-SEGMENT nv))
       (oss (list 'ORD-SEGMENT sn))
       (pr  (list 'PAIR nv nv))
       (un  (list 'UNION osn pr)))
  (display ";; rkq ord-peel vars: ") (display (list agv nv fv)) (newline)
  (dk-fact! 'nn-succ-closed nv)
  (dk-fact! 'nn-subset-ord nv)
  (dk-fact! 'membership-implies-sethood nv 'NN)
  (dk-fact! 'ord-segment-is-set nv)
  (dk-fact! 'card-segment nv)                        ; (= (CARD osn) n)
  (have! (list 'IN (list 'CARD osn) 'NN)
         (lambda () (subst (list '= (list 'CARD osn) nv)) (ass)))
  (dk-fact! 'ord-segment-self nv)                    ; (NOT (IN n osn))
  (dk-fact! 'ord-segment-insert nv)                  ; (= oss un)
  (have! (list 'IN fv (list 'FUN un (list 'CARR agv)))
         (lambda () (subst (list '= un oss)) (ass)))
  (dk-fact! 'finsum-insert-ag agv osn nv fv)
  (subst (list '= oss un))
  (ass))
(rkq-check! 'finsum-ord-peel)
(qed 'finsum-ord-peel)
(topic! 'finsum-ord-peel 'algebra)

;;; ------------------------------------------ the COMM-MONOID projections
;;; monoid-assoc, monoid-left-id and comm-monoid-opr-comm are UNWARRANTED
;;; `theory-add-axiom!'s (monoid.scm:17, :27, :61), so citing them bills
;;; `trust: none'.  They are conjuncts of the IS-COMM-MONOID definition, and the
;;; subtype-laws.scm `stl--project!' shape proves them: unfold IS-X, split,
;;; unfold the operation-property, cite.  comm-monoid-opr-comm is proved under
;;; ITS OWN name (nothing in the tree cites it and no view companion exists);
;;; the two monoid ones are proved at COMM-MONOID under new names, so the
;;; MONOID axioms and their view companions are left alone.
(define (rkq-cm-project! name goal propname prophead sided?)
  (sp (make-wff goal))
  (di) (di)
  (mac-h 'IS-COMM-MONOID (dk-pick (dk-head? 'IS-COMM-MONOID) "is-comm-monoid"))
  (dk-split-all!)
  (let ((unfolded (dk-landed-1 (lambda () (mac-h propname (dk-pick (dk-head? prophead)
                                                                  "the property"))))))
    (if sided?
        (let* ((typing (dk-landed-1 (lambda () (di))))
               (elt    (cadr typing))
               (inst-d (dk-landed-1 (lambda () (inst unfolded elt))))
               (both   (dk-landed-1 (lambda () (detach! inst-d)))))
          (dk-split! both))))
  (ass)
  (rkq-check! name)
  (qed name)
  (topic! name 'algebra))

(rkq-cm-project! 'comm-monoid-opr-comm
  '(FORALL s (IMPLIES (IS-COMM-MONOID s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (= ((OPR s) a b) ((OPR s) b a))))))))
  'is-commutative 'IS-COMMUTATIVE #f)

(rkq-cm-project! 'comm-monoid-assoc
  '(FORALL s (IMPLIES (IS-COMM-MONOID s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (FORALL c (IMPLIES (IN c (CARR s))
           (= ((OPR s) ((OPR s) a b) c) ((OPR s) a ((OPR s) b c)))))))))))
  'is-associative 'IS-ASSOCIATIVE #f)

(rkq-cm-project! 'comm-monoid-left-id
  '(FORALL s (IMPLIES (IS-COMM-MONOID s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (= ((OPR s) (IDEN s) a) a)))))
  'is-identity 'IS-IDENTITY #t)

;;; ------------------------------------------- comm-monoid-opr-interchange
;;; (a.b).(c.d) = (a.c).(b.d) in a commutative monoid: five rewrites, no
;;; inverses.  The abelian-group twin is abelian-group-opr-interchange
;;; (rake-finsum-laws.scm); this is the same proof with monoid-assoc and
;;; comm-monoid-opr-comm in place of the group facts.
(sp (make-wff
  (rkq-tf 's '(IS-COMM-MONOID s)
    (rkq-tf 'a '(IN a (CARR s))
      (rkq-tf 'b '(IN b (CARR s))
        (rkq-tf 'c '(IN c (CARR s))
          (rkq-tf 'd '(IN d (CARR s))
            '(= ((OPR s) ((OPR s) a b) ((OPR s) c d))
                ((OPR s) ((OPR s) a c) ((OPR s) b d))))))))))
(dk-peel!)
(let* ((gl  (dk-goal))
       (lhs (cadr gl))
       (mv  (cadr (car lhs)))
       (ab  (cadr lhs)) (cd (caddr lhs))
       (av (cadr ab)) (bv (caddr ab)) (cv (cadr cd)) (dv (caddr cd))
       (O  (lambda (x y) (rkq-o mv x y))))
  (dk-fact! 'comm-monoid-carrier-closed-opr mv cv dv)
  (dk-fact! 'comm-monoid-carrier-closed-opr mv bv dv)
  (dk-fact! 'comm-monoid-carrier-closed-opr mv bv cv)
  (dk-fact! 'comm-monoid-carrier-closed-opr mv cv bv)
  (dk-fact! 'comm-monoid-assoc mv av bv (O cv dv))
  (subst (list '= (O (O av bv) (O cv dv)) (O av (O bv (O cv dv)))))
  (dk-fact! 'comm-monoid-assoc mv bv cv dv)
  (subst (list '= (O bv (O cv dv)) (O (O bv cv) dv)))
  (dk-fact! 'comm-monoid-opr-comm mv bv cv)
  (subst (list '= (O bv cv) (O cv bv)))
  (dk-fact! 'comm-monoid-assoc mv cv bv dv)
  (subst (list '= (O (O cv bv) dv) (O cv (O bv dv))))
  (dk-fact! 'comm-monoid-assoc mv av cv (O bv dv))
  (subst (list '= (O (O av cv) (O bv dv)) (O av (O cv (O bv dv)))))
  (dk-fact! 'comm-monoid-carrier-closed-opr mv cv (O bv dv))
  (dk-fact! 'comm-monoid-carrier-closed-opr mv av (O cv (O bv dv)))
  (rfl))
(rkq-check! 'comm-monoid-opr-interchange)
(qed 'comm-monoid-opr-interchange)
(topic! 'comm-monoid-opr-interchange 'algebra)

;;; ------------------------------------ sum-ag-comm-monoid-type-ptwise
;;; sum-ag-comm-monoid-type-ind wants f in FUN(NN, CARR m); a back-peeled
;;; family is typed only on the segment, so this is the pointwise form.
(sp (make-wff
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL m (IMPLIES (IS-COMM-MONOID m)
     (FORALL g_ (IMPLIES (FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n)) (IN (g_ i_) (CARR m))))
       (IN (SUM-AG m g_ n) (CARR m))))))))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkq-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkq-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  (dk-focus! base)
  (dk-peel!)
  (let ((mv (cadr (rkq-pick-head 'IS-COMM-MONOID "IS-COMM-MONOID m"))))
    (mac 'sum-ag-zero)
    (dk-fact! 'comm-monoid-identity-in-carr mv)
    (ass))
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv (rkq-nn-var))
         (gl (dk-goal))
         (mv (cadr (cadr gl)))
         (gv (caddr (cadr gl)))
         (typ (dk-pick (lambda (f) (rkq-guarded-forall? f rkq-seg-dom?)) "the typing"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (not (rkq-guarded-forall? f rkq-seg-dom?))))
                       "the IH")))
    (have! (list 'IN nv (list 'ORD-SEGMENT (list 'succ nv)))
           (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! typ nv)
    (rkq-restrict! typ nv (lambda (i) (list 'IN (list gv i) (list 'CARR mv))))
    (mac 'sum-ag-succ)
    (dk-apply! ih mv gv)
    (dk-fact! 'comm-monoid-carrier-closed-opr mv (list 'SUM-AG mv gv nv) (list gv nv))
    (ass)))
(rkq-check! 'sum-ag-comm-monoid-type-ptwise)
(qed 'sum-ag-comm-monoid-type-ptwise)
(topic! 'sum-ag-comm-monoid-type-ptwise 'algebra)

;;; ----------------------------------------------- sum-ag-comm-monoid-add-ind
(define rkq-cmadd-ind-stmt
  (rkq-foralls '(n)
    (rkq-imps '(IN n NN)
      (rkq-foralls '(m)
        (rkq-imps '(IS-COMM-MONOID m)
          (rkq-foralls '(ga_ gb_ gc_)
            (rkq-imps '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n)) (IN (ga_ i_) (CARR m))))
                      '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n)) (IN (gb_ i_) (CARR m))))
                      '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                          (== (gc_ i_) ((OPR m) (ga_ i_) (gb_ i_)))))
                      '(= (SUM-AG m gc_ n)
                          ((OPR m) (SUM-AG m ga_ n) (SUM-AG m gb_ n))))))))))
(sp (make-wff rkq-cmadd-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkq-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkq-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  (dk-focus! base)
  (dk-peel!)
  (let ((mv (cadr (rkq-pick-head 'IS-COMM-MONOID "IS-COMM-MONOID m"))))
    (mac 'sum-ag-zero)
    (dk-fact! 'comm-monoid-identity-in-carr mv)
    (dk-fact! 'comm-monoid-left-id mv (list 'IDEN mv))
    (subst (list '= (rkq-o mv (list 'IDEN mv) (list 'IDEN mv)) (list 'IDEN mv)))
    (rfl))
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (rkq-nn-var))
         (gl  (dk-goal))
         (mv  (cadr (cadr gl)))
         (gcv (caddr (cadr gl)))
         (rhs (caddr gl))
         (gav (caddr (cadr rhs)))
         (gbv (caddr (caddr rhs)))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (O   (lambda (x y) (rkq-o mv x y)))
         (typA (dk-pick (lambda (f) (rkq-guarded-forall-inner? f rkq-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN) (pair? (cadr i))
                                   (eq? (car (cadr i)) gav))))) "the typing of ga_"))
         (typB (dk-pick (lambda (f) (rkq-guarded-forall-inner? f rkq-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN) (pair? (cadr i))
                                   (eq? (car (cadr i)) gbv))))) "the typing of gb_"))
         (agree (dk-pick (lambda (f) (rkq-guarded-forall-inner? f rkq-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) '==))))) "the pointwise hypothesis"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (not (rkq-guarded-forall? f rkq-seg-dom?))))
                       "the IH")))
    (display ";; rkq cm-add step: ") (display (list nv mv gav gbv gcv)) (newline)
    (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! typA nv)
    (dk-apply! typB nv)
    (dk-apply! agree nv)
    (rkq-restrict! typA nv (lambda (i) (list 'IN (list gav i) (list 'CARR mv))))
    (rkq-restrict! typB nv (lambda (i) (list 'IN (list gbv i) (list 'CARR mv))))
    (rkq-restrict! agree nv (lambda (i) (list '== (list gcv i)
                                              (O (list gav i) (list gbv i)))))
    (mac 'sum-ag-succ)
    (subst (list '== (list gcv nv) (O (list gav nv) (list gbv nv))))
    (dk-apply! ih mv gav gbv gcv)
    (subst (list '= (list 'SUM-AG mv gcv nv)
                    (O (list 'SUM-AG mv gav nv) (list 'SUM-AG mv gbv nv))))
    (dk-fact! 'sum-ag-comm-monoid-type-ptwise nv mv gav)
    (dk-fact! 'sum-ag-comm-monoid-type-ptwise nv mv gbv)
    (dk-fact! 'comm-monoid-opr-interchange mv
              (list 'SUM-AG mv gav nv) (list 'SUM-AG mv gbv nv)
              (list gav nv) (list gbv nv))
    (ass)))
(rkq-check! 'sum-ag-comm-monoid-add-ind)
(qed 'sum-ag-comm-monoid-add-ind)
(topic! 'sum-ag-comm-monoid-add-ind 'algebra)

;;; ------------------------------------------------------------- finsum-add
;;; theorem-library/finsum-additive.scm:136, copied literally.
(define rkq-add-stmt
  (rkq-tf 'm '(IS-COMM-MONOID m)
    (rkq-tfin 'S
      (rkq-tf 'f '(IN f (FUN S (CARR m)))
        (rkq-tf 'h '(IN h (FUN S (CARR m)))
          (list '=
            (list 'FINSUM 'm (list 'VNB-LAMBDA 'z 'S (list '(OPR m) '(f z) '(h z))) 'S)
            (list '(OPR m) (list 'FINSUM 'm 'f 'S) (list 'FINSUM 'm 'h 'S))))))))
(sp (make-wff rkq-add-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (lhs (cadr gl))
       (mv  (cadr lhs)) (lam (caddr lhs)) (sv (cadddr lhs))
       (rhs (caddr gl))
       (fv  (caddr (cadr rhs))) (hv (caddr (caddr rhs)))
       (nc  (list 'CARD sv))
       (phi (list 'FIN-ENUM sv))
       (seg (list 'ORD-SEGMENT nc))
       (fam (lambda (u) (list 'ENUM-FAM mv u phi nc)))
       (O   (lambda (x y) (rkq-o mv x y))))
  (display ";; rkq finsum-add vars: ") (display (list mv sv fv hv)) (newline)
  (mac 'FINSUM)

  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (dk-fact! 'enum-fam-comm-monoid-in-fun nc mv sv phi fv)
  (dk-fact! 'enum-fam-comm-monoid-in-fun nc mv sv phi hv)
  (rkq-ptwise-from-fun! (fam fv) nc mv)
  (rkq-ptwise-from-fun! (fam hv) nc mv)
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
           (list '== (list (fam lam) 'i_) (O (list (fam fv) 'i_) (list (fam hv) 'i_)))))
         (lambda ()
           (let* ((landed (dk-peel!)) (iv (rkq-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c phi seg sv iv)
             (dk-fact! 'enum-fam-value nc mv lam phi iv)
             (dk-fact! 'enum-fam-value nc mv fv  phi iv)
             (dk-fact! 'enum-fam-value nc mv hv  phi iv)
             (subst (list '== (list (fam lam) iv) (list lam (list phi iv))))
             (subst (list '== (list (fam fv) iv) (list fv (list phi iv))))
             (subst (list '== (list (fam hv) iv) (list hv (list phi iv))))
             (lam-b)
             (qrfl))))
  (dk-fact! 'sum-ag-comm-monoid-add-ind nc mv (fam fv) (fam hv) (fam lam))
  (ass))
(rkq-check! 'finsum-add)
(qed 'finsum-add)
(topic! 'finsum-add 'algebra)

;; the module prep: both abelian groups and all six read-offs
(define (rkq-mod-prep! mdv)
  (let ((sr (list 'SCAL mdv)))
    (dk-fact! 'module-scalar-ring mdv)
    (dk-fact! 'ring-additive-ag-is-abelian-group sr)
    (dk-fact! 'module-vector-ag-is-abelian-group mdv)
    (dk-fact! 'abelian-group-is-group (list 'RING-ADDITIVE-AG sr))
    (dk-fact! 'abelian-group-is-group (list 'MODULE-VECTOR-AG mdv))
    (dk-fact! 'ras-carr sr) (dk-fact! 'ras-op sr) (dk-fact! 'ras-id sr)
    (dk-fact! 'mvag-carr mdv) (dk-fact! 'mvag-op mdv) (dk-fact! 'mvag-id mdv)))

;; 0 . x = 0_V, inlined (module-zero-act lives at load position 309, far below
;; this file's window; the derivation is its own, four lines).
(define (rkq-zero-act! mdv xv)
  (let* ((sr (list 'SCAL mdv))
         (zz (list 'ZERO sr))
         (aa (list (list 'ACT mdv) zz xv)))
    (dk-fact! 'module-scalar-zero-in mdv)
    (dk-fact! 'module-act-type mdv zz xv)
    (dk-fact! 'module-act-distrib-scalar mdv zz zz xv)
    (dk-fact! 'ring-add-left-id sr zz)
    (have! (list '= (list (list 'VADD mdv) aa aa) aa)
           (lambda ()
             (subst (list '= (list (list 'VADD mdv) aa aa)
                             (list (list 'ACT mdv) (list (list 'ADD sr) zz zz) xv)))
             (subst (list '= (list (list 'ADD sr) zz zz) zz))
             (rfl)))
    (dk-fact! 'abelian-group-idempotent-is-id-module-vector-ag mdv aa)
    aa))

;;; ------------------------------------------------ sum-ag-act-collect-ind
(define rkq-acc-ind-stmt
  (rkq-foralls '(n)
    (rkq-imps '(IN n NN)
      (rkq-foralls '(md)
        (rkq-imps '(IS-MODULE md)
          (rkq-foralls '(x)
            (rkq-imps '(IN x (VEC md))
              (rkq-foralls '(gc_ gv_)
                (rkq-imps '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (IN (gc_ i_) (CARR (SCAL md)))))
                          '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n))
                             (== (gv_ i_) ((ACT md) (gc_ i_) x))))
                          '(= (SUM-AG (MODULE-VECTOR-AG md) gv_ n)
                              ((ACT md) (SUM-AG (RING-ADDITIVE-AG (SCAL md)) gc_ n) x)))))))))))

(sp (make-wff rkq-acc-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkq-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkq-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base ---------------------------------------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl   (dk-goal))
         (mvag (cadr (cadr gl)))
         (mdv  (cadr mvag))
         (xv   (caddr (caddr gl)))
         (sr   (list 'SCAL mdv))
         (rag  (list 'RING-ADDITIVE-AG sr)))
    (display ";; rkq acc base: ") (display (list mdv xv)) (newline)
    (rkq-mod-prep! mdv)
    (dk-fact! 'module-vzero-in mdv)
    (rkq-zero-act! mdv xv)
    (mac 'sum-ag-zero)
    (subst (list '= (list 'IDEN mvag) (list 'VZERO mdv)))
    (subst (list '= (list 'IDEN rag) (list 'ZERO sr)))
    (subst (list '= (list (list 'ACT mdv) (list 'ZERO sr) xv) (list 'VZERO mdv)))
    (rfl))
  ;; ---- step ---------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv   (rkq-nn-var))
         (gl   (dk-goal))
         (mvag (cadr (cadr gl)))
         (mdv  (cadr mvag))
         (gvv  (caddr (cadr gl)))
         (act  (caddr gl))                       ; ((ACT md) (SUM-AG rag gc succ n) x)
         (gcv  (caddr (cadr act)))
         (xv   (caddr act))
         (sr   (list 'SCAL mdv))
         (rag  (list 'RING-ADDITIVE-AG sr))
         (csr  (list 'CARR sr))
         (crag (list 'CARR rag))
         (segS (list 'ORD-SEGMENT (list 'succ nv)))
         (sc   (list 'SUM-AG rag gcv nv))
         (typC (dk-pick (lambda (f) (rkq-guarded-forall-inner? f rkq-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) 'IN))))) "typing of gc_"))
         (agree (dk-pick (lambda (f) (rkq-guarded-forall-inner? f rkq-seg-dom?
                  (lambda (i) (and (pair? i) (eq? (car i) '==))))) "pointwise hypothesis"))
         (ih   (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (not (rkq-guarded-forall? f rkq-seg-dom?))))
                        "the IH")))
    (display ";; rkq acc step: ") (display (list nv mdv xv gcv gvv)) (newline)
    (rkq-mod-prep! mdv)
    (have! (list 'IN nv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! typC nv)
    (dk-apply! agree nv)
    (rkq-restrict! typC nv (lambda (i) (list 'IN (list gcv i) csr)))
    (rkq-restrict! agree nv (lambda (i) (list '== (list gvv i)
                                              (list (list 'ACT mdv) (list gcv i) xv))))
    ;; the fold's typing, through the view carrier
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nv))
                                   (list 'IN (list gcv 'i_) crag)))
           (lambda ()
             (let* ((landed (dk-peel!)) (iv (rkq-seg-var landed)))
               (subst (list '= crag csr))
               (dk-apply! (dk-pick (lambda (f) (rkq-guarded-forall-inner? f rkq-seg-dom?
                                     (lambda (i) (and (pair? i) (eq? (car i) 'IN)
                                                      (equal? (caddr i) csr)
                                                      (pair? (cadr i))
                                                      (eq? (car (cadr i)) gcv)))))
                                   "restricted typing of gc_")
                          iv)
               (ass))))
    (dk-fact! 'sum-ag-type-ptwise nv rag gcv)
    (rkq-carr-bridge! sc crag csr)
    (mac 'sum-ag-succ)
    (subst (list '== (list gvv nv) (list (list 'ACT mdv) (list gcv nv) xv)))
    (dk-apply! ih mdv xv gcv gvv)
    (subst (list '= (list 'SUM-AG mvag gvv nv) (list (list 'ACT mdv) sc xv)))
    (mac 'mvag-op)
    (mac 'ras-op)
    (dk-fact! 'module-act-distrib-scalar mdv sc (list gcv nv) xv)
    (dk-fact! 'equality-symmetry
              (list (list 'ACT mdv) (list (list 'ADD sr) sc (list gcv nv)) xv)
              (list (list 'VADD mdv) (list (list 'ACT mdv) sc xv)
                                     (list (list 'ACT mdv) (list gcv nv) xv)))
    (ass)))
(rkq-check! 'sum-ag-act-collect-ind)
(qed 'sum-ag-act-collect-ind)
(topic! 'sum-ag-act-collect-ind 'algebra)

;;; ------------------------------------------------- finsum-act-collect-gen
;;; structure-library/mod-seq.scm:149, copied literally.
(define rkq-acc-stmt
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL x (IMPLIES (IN x (VEC md))
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL c (IMPLIES (IN c (FUN S (CARR (SCAL md))))
       (= ((ACT md) (FINSUM (RING-ADDITIVE-AG (SCAL md)) c S) x)
          (FINSUM (MODULE-VECTOR-AG md)
                  (VNB-LAMBDA z S ((ACT md) (c z) x))
                  S))))))))))))
(sp (make-wff rkq-acc-stmt))
(dk-peel!)
(let* ((gl   (dk-goal))
       (lhs  (cadr gl))
       (mdv  (cadr (car lhs)))
       (fsL  (cadr lhs))
       (cv   (caddr fsL))
       (sv   (cadddr fsL))
       (xv   (caddr lhs))
       (rhs  (caddr gl))
       (mvag (cadr rhs))
       (lam  (caddr rhs))
       (sr   (list 'SCAL mdv))
       (rag  (list 'RING-ADDITIVE-AG sr))
       (csr  (list 'CARR sr))
       (crag (list 'CARR rag))
       (nc   (list 'CARD sv))
       (phi  (list 'FIN-ENUM sv))
       (seg  (list 'ORD-SEGMENT nc))
       (famc (list 'ENUM-FAM rag cv phi nc))
       (famv (list 'ENUM-FAM mvag lam phi nc)))
  (display ";; rkq acc-gen vars: ") (display (list mdv xv sv cv)) (newline)
  (rkq-mod-prep! mdv)
  (mac 'FINSUM)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! (list 'IN cv (list 'FUN sv crag))
         (lambda () (subst (list '= crag csr)) (ass)))
  (dk-fact! 'enum-fam-in-fun nc rag sv phi cv)
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list 'IN (list famc 'i_) csr)))
         (lambda ()
           (let* ((landed (dk-peel!)) (iv (rkq-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c famc 'NN crag iv)
             (subst (list '= csr crag))
             (ass))))
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list '== (list famv 'i_)
                                           (list (list 'ACT mdv) (list famc 'i_) xv))))
         (lambda ()
           (let* ((landed (dk-peel!)) (iv (rkq-seg-var landed)))
             (dk-fact! 'ord-segment-nn-subset nc iv)
             (dk-fact! 'fun-apply-type-c phi seg sv iv)
             (dk-fact! 'enum-fam-value nc mvag lam phi iv)
             (dk-fact! 'enum-fam-value nc rag cv phi iv)
             (subst (list '== (list famv iv) (list lam (list phi iv))))
             (subst (list '== (list famc iv) (list cv (list phi iv))))
             (lam-b)
             (qrfl))))
  (dk-fact! 'sum-ag-act-collect-ind nc mdv xv famc famv)
  (dk-fact! 'equality-symmetry
            (list 'SUM-AG mvag famv nc)
            (list (list 'ACT mdv) (list 'SUM-AG rag famc nc) xv))
  (ass))
(rkq-check! 'finsum-act-collect-gen)
(qed 'finsum-act-collect-gen)
(topic! 'finsum-act-collect-gen 'algebra)

;;; ===================================================== sum-ag-fubini-ind
;;; The DOUBLE FOLD interchange, with every family a VARIABLE:
;;;   ff_  the rectangle, curried:   ((ff_ i) j)
;;;   gg_  its transpose:            ((gg_ j) i) == ((ff_ i) j)
;;;   rs_  the row sums:             rs_(i) == SUM-AG(ag, ff_ i, n)
;;;   cs_  the column sums:          cs_(j) == SUM-AG(ag, gg_ j, m)
;;; Induction on m (OUTERMOST, so `ni' fires).  Base: every column sum is the
;;; empty fold, so the whole right side is IDEN (sum-ag-all-id-ind).  Step:
;;; peel the top ROW off the left with sum-ag-succ, peel the top ENTRY off every
;;; column sum, and split the right side with sum-ag-add-ind.

;;; ---------------------------------------------------------------------------
;;; rkq-sumag-type-inline! -- sum-ag-type-ptwise, proved INLINE at a FIXED family.
;;;
;;; 2026-09-18 (the LUTINS instantiation rule).  The fubini step needs the
;;; typing of a column fold SUM-AG(ag, (gg_ j), m), where `gg_' is one of the
;;; statement's own VARIABLES.  CITING `sum-ag-type-ptwise' instantiates its
;;; family variable at the term (gg_ j) -- an application of an untyped
;;; variable, which the definedness certificate refuses and never can accept --
;;; so forall-elim owes the side sequent (gg_ j) = (gg_ j).  Nothing in the
;;; tree closes it: the context knows ((gg_ j) m) is defined (trans + typ), and
;;; strictness through the OPERATOR position of an application is exactly what
;;; the certificate does not read (see the group's report, CERTIFICATE GAP 2).
;;;
;;; The same statement proved HERE, with the family a free TERM rather than an
;;; instantiated variable, owes nothing: `sum-ag-zero' and `sum-ag-succ' are
;;; MACETES (goal rewrites, no instantiation), and the only terms instantiated
;;; are the induction variable and the index, both variables.
;;;
;;; Returns the statement, for the caller to `dk-apply!' at its own bound.
(define (rkq-sumag-type-inline! agv fam ca)
  (let* ((ptk  (lambda (k) (rkq-gf 'i_ (rkq-seg k) (rkq-in (list fam 'i_) ca))))
         (stmt (list 'FORALL 'k_
                 (rkq-imps '(IN k_ NN)
                           (ptk 'k_)
                           (rkq-in (list 'SUM-AG agv fam 'k_) ca)))))
    (have! stmt
      (lambda ()
        (let* ((ls   (dk-opened (lambda () (ni))))
               (base (rkq-leaf ls (lambda (g) (not (dk-contains? g 'succ))) "inline base"))
               (step (rkq-leaf ls (lambda (g) (dk-contains? g 'succ))       "inline step")))
          (dk-focus! base)
          (dk-peel!)
          (mac 'sum-ag-zero)
          (ass)
          (dk-focus! step)
          (dk-peel!)
          ;; the eigenvariable comes off the GOAL (IN (SUM-AG ag fam (succ k)) ca);
          ;; the context carries several NN typings, so a finder would be ambiguous.
          (let* ((kv (cadr (cadddr (cadr (dk-goal)))))
                 (p1 (ptk (list 'succ kv)))
                 (ih (rkq-imps (ptk kv) (rkq-in (list 'SUM-AG agv fam kv) ca))))
            (have! (ptk kv)
              (lambda ()
                (let ((iv (dk-di-var!)))
                  (have! (rkq-in iv (rkq-seg (list 'succ kv)))
                         (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
                  (dk-apply! p1 iv)
                  (ass))))
            (detach! ih)
            (have! (rkq-in kv (rkq-seg (list 'succ kv)))
                   (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
            (dk-apply! p1 kv)
            (mac 'sum-ag-succ)
            (dk-fact! 'group-carrier-closed-opr agv
                      (list 'SUM-AG agv fam kv) (list fam kv))
            (ass)))))
    stmt))


;;; rkq-sumag-add-inline! -- sum-ag-add-ind, proved INLINE at FIXED families.
;;; Same reason as rkq-sumag-type-inline! above: the fubini step's second
;;; summand family is (ff_ m), an application of an untyped VARIABLE, which the
;;; definedness certificate refuses, so CITING sum-ag-add-ind at it owes
;;; (ff_ m) = (ff_ m) and nothing closes that.  The proof below is
;;; rake-finsum-laws.scm's sum-ag-add-ind driver with ga_/gb_/gc_ replaced by
;;; the caller's TERMS; the only instantiations are at the induction variable
;;; and the index.  Returns the statement for the caller to `dk-apply!'.
(define (rkq-sumag-add-inline! agv fF fG fH ca)
  (let* ((pt  (lambda (fam k) (rkq-gf 'i_ (rkq-seg k) (rkq-in (list fam 'i_) ca))))
         (rel (lambda (k) (rkq-gf 'i_ (rkq-seg k)
                            (list '== (list fH 'i_)
                                      (rkq-o agv (list fF 'i_) (list fG 'i_))))))
         (cc  (lambda (k) (list '= (list 'SUM-AG agv fH k)
                                   (rkq-o agv (list 'SUM-AG agv fF k)
                                              (list 'SUM-AG agv fG k)))))
         (stmt (list 'FORALL 'k_
                 (rkq-imps '(IN k_ NN) (pt fF 'k_) (pt fG 'k_) (rel 'k_) (cc 'k_)))))
    (have! stmt
      (lambda ()
        (let* ((ls   (dk-opened (lambda () (ni))))
               (base (rkq-leaf ls (lambda (g) (not (dk-contains? g 'succ))) "add-ind base"))
               (step (rkq-leaf ls (lambda (g) (dk-contains? g 'succ))       "add-ind step")))
          (dk-focus! base)
          (dk-peel!)
          (mac 'sum-ag-zero)
          (dk-fact! 'group-left-id agv (list 'IDEN agv))
          (subst (list '= (rkq-o agv (list 'IDEN agv) (list 'IDEN agv)) (list 'IDEN agv)))
          (rfl)
          (dk-focus! step)
          (dk-peel!)
          (let* ((kv   (cadr (cadddr (cadr (dk-goal)))))
                 (ptF1 (pt fF (list 'succ kv)))
                 (ptG1 (pt fG (list 'succ kv)))
                 (rel1 (rel (list 'succ kv)))
                 (ih   (rkq-imps (pt fF kv) (pt fG kv) (rel kv) (cc kv))))
            (have! (rkq-in kv (rkq-seg (list 'succ kv)))
                   (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
            (dk-apply! ptF1 kv)
            (dk-apply! ptG1 kv)
            (dk-apply! rel1 kv)
            (rkq-restrict! ptF1 kv (lambda (i) (rkq-in (list fF i) ca)))
            (rkq-restrict! ptG1 kv (lambda (i) (rkq-in (list fG i) ca)))
            (rkq-restrict! rel1 kv (lambda (i) (list '== (list fH i)
                                                     (rkq-o agv (list fF i) (list fG i)))))
            (mac 'sum-ag-succ)
            (subst (list '== (list fH kv) (rkq-o agv (list fF kv) (list fG kv))))
            (let loop ((r ih))
              (if (and (pair? r) (eq? (car r) 'IMPLIES))
                  (loop (dk-landed-1 (lambda () (detach! r))))))
            (subst (cc kv))
            (dk-apply! (rkq-sumag-type-inline! agv fF ca) kv)
            (dk-apply! (rkq-sumag-type-inline! agv fG ca) kv)
            (dk-fact! 'abelian-group-opr-interchange agv
                      (list 'SUM-AG agv fF kv) (list 'SUM-AG agv fG kv)
                      (list fF kv) (list fG kv))
            (ass)))))
    stmt))

(define rkq-fub-ind-stmt
  (rkq-foralls '(m)
    (rkq-imps '(IN m NN)
      (rkq-foralls '(ag)
        (rkq-imps '(IS-ABELIAN-GROUP ag)
          (rkq-foralls '(n)
            (rkq-imps '(IN n NN)
              (rkq-foralls '(ff_ gg_ rs_ cs_)
                (rkq-imps
                  '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT m))
                     (FORALL j_ (IMPLIES (IN j_ (ORD-SEGMENT n))
                       (IN ((ff_ i_) j_) (CARR ag))))))
                  '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT m))
                     (FORALL j_ (IMPLIES (IN j_ (ORD-SEGMENT n))
                       (== ((gg_ j_) i_) ((ff_ i_) j_))))))
                  '(FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT m))
                     (== (rs_ i_) (SUM-AG ag (ff_ i_) n))))
                  '(FORALL j_ (IMPLIES (IN j_ (ORD-SEGMENT n))
                     (== (cs_ j_) (SUM-AG ag (gg_ j_) m))))
                  '(= (SUM-AG ag rs_ m) (SUM-AG ag cs_ n)))))))))))

(sp (make-wff rkq-fub-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkq-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkq-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base: m = 0.  Every column sum is the empty fold. -------------------
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl   (dk-goal))
         (agv  (cadr (cadr gl)))
         (rsv  (caddr (cadr gl)))
         (csv  (caddr (caddr gl)))
         (nv   (cadddr (caddr gl)))
         (cols (dk-pick (lambda (f) (rkq-guarded-forall-inner? f (rkq-seg nv)
                          (lambda (i) (and (pair? i) (eq? (car i) '==)))))
                        "the column-sum hypothesis"))
         (ggv  (car (caddr (caddr (caddr (caddr cols)))))))
    (display ";; rkq fub base: ") (display (list agv nv rsv csv)) (newline)
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)
    (have! (rkq-gf 'j_ (rkq-seg nv) (list '= (list csv 'j_) (list 'IDEN agv)))
           (lambda ()
             (let ((jv (dk-di-var!)))
               (dk-apply! cols jv)
               (subst (list '== (list csv jv) (list 'SUM-AG agv (list ggv jv) 0)))
               (mac 'sum-ag-zero)
               (rfl))))
    (dk-fact! 'sum-ag-all-id-ind nv agv csv)
    (mac 'sum-ag-zero)
    (subst (list '= (list 'SUM-AG agv csv nv) (list 'IDEN agv)))
    (rfl))
  ;; ---- step ---------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((gl   (dk-goal))
         (lhs  (cadr gl))
         (agv  (cadr lhs)) (rsv (caddr lhs))
         (mv   (cadr (cadddr lhs)))
         (rhs  (caddr gl))
         (csv  (caddr rhs)) (nv (cadddr rhs))
         (segM (rkq-seg mv)) (segS (rkq-seg (list 'succ mv))) (segN (rkq-seg nv))
         (ca   (list 'CARR agv))
         (typ  (dk-pick (lambda (f) (rkq-guarded-forall-inner? f segS
                  (lambda (i) (and (pair? i) (eq? (car i) 'FORALL)
                                   (eq? (car (caddr (caddr i))) 'IN)))))
                        "the rectangle typing"))
         (trans (dk-pick (lambda (f) (rkq-guarded-forall-inner? f segS
                  (lambda (i) (and (pair? i) (eq? (car i) 'FORALL)
                                   (eq? (car (caddr (caddr i))) '==)))))
                         "the transpose hypothesis"))
         (rows (dk-pick (lambda (f) (rkq-guarded-forall-inner? f segS
                  (lambda (i) (and (pair? i) (eq? (car i) '==)))))
                        "the row-sum hypothesis"))
         (cols (dk-pick (lambda (f) (rkq-guarded-forall-inner? f segN
                  (lambda (i) (and (pair? i) (eq? (car i) '==)))))
                        "the column-sum hypothesis"))
         (ffv  (car (caddr (caddr (caddr (caddr rows))))))
         (ggv  (car (caddr (caddr (caddr (caddr cols))))))
         (ih   (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (not (rkq-guarded-forall? f rkq-seg-dom?))))
                        "the IH"))
         (csp  (list 'VNB-LAMBDA 'j_ segN (list 'SUM-AG agv (list ggv 'j_) mv))))
    (display ";; rkq fub step: ") (display (list mv nv agv ffv ggv rsv csv)) (newline)
    (dk-fact! 'abelian-group-is-group agv)
    (dk-fact! 'group-identity-in agv)
    (have! (rkq-in mv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    ;; --- the four hypotheses cut down to ORD-SEGMENT(m) --------------------
    (have! (rkq-gf 'i_ segM (rkq-gf 'j_ segN
              (rkq-in (list (list ffv 'i_) 'j_) ca)))
           (lambda ()
             (let* ((landed (dk-peel!))
                    (iv (rkq-seg-var landed))
                    (jv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                        (symbol? (cadr f))
                                                        (equal? (caddr f) segN)))
                                       "j in OS(n)"))))
               (have! (rkq-in iv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! (dk-apply! typ iv) jv)
               (ass))))
    (have! (rkq-gf 'i_ segM (rkq-gf 'j_ segN
              (list '== (list (list ggv 'j_) 'i_) (list (list ffv 'i_) 'j_))))
           (lambda ()
             (let* ((landed (dk-peel!))
                    (iv (rkq-seg-var landed))
                    (jv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                        (symbol? (cadr f))
                                                        (equal? (caddr f) segN)))
                                       "j in OS(n)"))))
               (have! (rkq-in iv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! (dk-apply! trans iv) jv)
               (ass))))
    (have! (rkq-gf 'i_ segM (list '== (list rsv 'i_) (list 'SUM-AG agv (list ffv 'i_) nv)))
           (lambda ()
             (let ((iv (dk-di-var!)))
               (have! (rkq-in iv segS) (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! rows iv)
               (ass))))
    (have! (rkq-gf 'j_ segN (list '== (list csp 'j_) (list 'SUM-AG agv (list ggv 'j_) mv)))
           (lambda ()
             (dk-di-var!)
             (lam-b)
             (qrfl)))
    (let ((cols-m (dk-pick (lambda (f) (equal? f (rkq-gf 'j_ segN
                              (list '== (list csp 'j_)
                                        (list 'SUM-AG agv (list ggv 'j_) mv)))))
                           "the truncated column sums"))
          (trans-m (dk-pick (lambda (f) (equal? f (rkq-gf 'i_ segM (rkq-gf 'j_ segN
                               (list '== (list (list ggv 'j_) 'i_)
                                         (list (list ffv 'i_) 'j_))))))
                            "the restricted transpose"))
          (typ-m (dk-pick (lambda (f) (equal? f (rkq-gf 'i_ segM (rkq-gf 'j_ segN
                             (rkq-in (list (list ffv 'i_) 'j_) ca)))))
                          "the restricted typing")))
      ;; --- the IH at the truncated column sums -----------------------------
      (dk-apply! ih agv nv ffv ggv rsv csp)
      ;; --- pointwise typings for sum-ag-add-ind ----------------------------
      (have! (rkq-gf 'j_ segN (rkq-in (list csp 'j_) ca))
             (lambda ()
               (let ((jv (dk-di-var!)))
                 (dk-apply! cols-m jv)
                 (subst (list '== (list csp jv) (list 'SUM-AG agv (list ggv jv) mv)))
                 (have! (rkq-gf 'i_ segM (rkq-in (list (list ggv jv) 'i_) ca))
                        (lambda ()
                          (let ((iv (dk-di-var!)))
                            (dk-apply! (dk-apply! trans-m iv) jv)
                            (dk-apply! (dk-apply! typ-m iv) jv)
                            (subst (list '== (list (list ggv jv) iv)
                                             (list (list ffv iv) jv)))
                            (ass))))
                 ;; NOT (dk-fact! 'sum-ag-type-ptwise ...): the family is an
                 ;; application of the VARIABLE gg_, which the definedness
                 ;; certificate cannot accept.  Proved inline instead.
                 (dk-apply! (rkq-sumag-type-inline! agv (list ggv jv) ca) mv)
                 (ass))))
      (have! (rkq-gf 'j_ segN (rkq-in (list (list ffv mv) 'j_) ca))
             (lambda ()
               (let ((jv (dk-di-var!)))
                 (dk-apply! (dk-apply! typ mv) jv)
                 (ass))))
      ;; --- the column sums split ------------------------------------------
      (have! (rkq-gf 'j_ segN (list '== (list csv 'j_)
                                    (rkq-o agv (list csp 'j_) (list (list ffv mv) 'j_))))
             (lambda ()
               (let ((jv (dk-di-var!)))
                 (dk-apply! cols jv)
                 (subst (list '== (list csv jv) (list 'SUM-AG agv (list ggv jv)
                                                      (list 'succ mv))))
                 (mac 'sum-ag-succ)
                 (dk-apply! cols-m jv)
                 (subst (list '== (list csp jv) (list 'SUM-AG agv (list ggv jv) mv)))
                 (dk-apply! (dk-apply! trans mv) jv)
                 (subst (list '== (list (list ggv jv) mv) (list (list ffv mv) jv)))
                 (qrfl))))
      ;; NOT (dk-fact! 'sum-ag-add-ind ...): the second family is (ff_ m), an
      ;; application of the VARIABLE ff_, which the definedness certificate
      ;; cannot accept.  Proved inline instead.
      (dk-apply! (rkq-sumag-add-inline! agv csp (list ffv mv) csv ca) nv)
      ;; --- and the left side peels ----------------------------------------
      (mac 'sum-ag-succ)
      (dk-apply! rows mv)
      (subst (list '== (list rsv mv) (list 'SUM-AG agv (list ffv mv) nv)))
      (subst (list '= (list 'SUM-AG agv rsv mv) (list 'SUM-AG agv csp nv)))
      (dk-fact! 'equality-symmetry
                (list 'SUM-AG agv csv nv)
                (rkq-o agv (list 'SUM-AG agv csp nv) (list 'SUM-AG agv (list ffv mv) nv)))
      (ass))))
(rkq-check! 'sum-ag-fubini-ind)
(qed 'sum-ag-fubini-ind)
(topic! 'sum-ag-fubini-ind 'algebra)

;;; ================================================== finsum-fubini
;;; theorem-library/finsum-fubini.scm:19, copied literally.
(define rkq-fub-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL Y (IMPLIES (AND (IN Y SET) (IN (CARD Y) NN))
     (FORALL f (IMPLIES (IN f (FUN (CARTESIAN X Y) (CARR ag)))
       (= (FINSUM ag (VNB-LAMBDA i X (FINSUM ag (VNB-LAMBDA j Y (f (LIST i j))) Y)) X)
          (FINSUM ag (VNB-LAMBDA j Y (FINSUM ag (VNB-LAMBDA i X (f (LIST i j))) X)) Y)))))))))))
(sp (make-wff rkq-fub-stmt))
(dk-peel!)
(dk-split-all!)
(mac 'FINSUM)
(let* ((gl   (dk-goal))
       (lhs  (cadr gl))  (rhs (caddr gl))
       (agv  (cadr lhs))
       (rsT  (caddr lhs)) (mm (cadddr lhs))
       (csT  (caddr rhs)) (nn (cadddr rhs))
       (lami (caddr rsT)) (phiX (cadddr rsT))
       (lamj (caddr csT)) (phiY (cadddr csT))
       (iv0  (cadr lami)) (xv (caddr lami)) (bodyI (cadddr lami))
       (jv0  (cadr lamj)) (yv (caddr lamj)) (bodyJ (cadddr lamj))
       (lini (caddr bodyI))                ; (VNB-LAMBDA j Y (f (LIST i j)))
       (linj (caddr bodyJ))                ; (VNB-LAMBDA i X (f (LIST i j)))
       (fv   (car (cadddr lini)))          ; the f in (f (LIST i j))
       (segM (rkq-seg mm)) (segN (rkq-seg nn))
       (ca   (list 'CARR agv))
       (cart (list 'CARTESIAN xv yv))
       (liP  (lambda (iv) (subst-free iv0 (list phiX iv) lini)))
       (ljP  (lambda (jv) (subst-free jv0 (list phiY jv) linj)))
       (ffT  (list 'VNB-LAMBDA 'i_ segM
                   (list 'ENUM-FAM agv (liP 'i_) phiY nn)))
       (ggT  (list 'VNB-LAMBDA 'j_ segN
                   (list 'ENUM-FAM agv (ljP 'j_) phiX mm)))
       (entry (lambda (iv jv) (list fv (list 'LIST (list phiX iv) (list phiY jv))))))
  (display ";; rkq fubini vars: ") (display (list agv xv yv fv)) (newline)
  (dk-fact! 'abelian-group-is-group agv)
  (dk-fact! 'group-identity-in agv)
  (let ((bx (dk-fact! 'fin-enum-is-bijection xv)))
    (mac-h 'bijection-membership-iff bx) (dk-split-all!))
  (let ((by (dk-fact! 'fin-enum-is-bijection yv)))
    (mac-h 'bijection-membership-iff by) (dk-split-all!))
  ;; (ffT i)(j) and (ggT j)(i) both reduce to f([phiX i, phiY j]).
  (define (rkq-red-ff! iv jv)
    (let ((li (liP iv)))
      (have! (list '== (list (list ffT iv) jv) (entry iv jv))
             (lambda ()
               (lam-b)
               (dk-fact! 'enum-fam-value nn agv li phiY jv)
               (subst (list '== (list (list 'ENUM-FAM agv li phiY nn) jv)
                                (list li (list phiY jv))))
               (lam-b)
               (qrfl)))))
  (define (rkq-red-gg! iv jv)
    (let ((lj (ljP jv)))
      (have! (list '== (list (list ggT jv) iv) (entry iv jv))
             (lambda ()
               (lam-b)
               (dk-fact! 'enum-fam-value mm agv lj phiX iv)
               (subst (list '== (list (list 'ENUM-FAM agv lj phiX mm) iv)
                                (list lj (list phiX iv))))
               (lam-b)
               (qrfl)))))
  ;; --- (1) the rectangle typing ------------------------------------------
  (have! (rkq-gf 'i_ segM (rkq-gf 'j_ segN (rkq-in (list (list ffT 'i_) 'j_) ca)))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                      (symbol? (cadr f))
                                                      (equal? (caddr f) segM)))
                                     "i in OS(m)")))
                  (jv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                      (symbol? (cadr f))
                                                      (equal? (caddr f) segN)))
                                     "j in OS(n)"))))
             (dk-fact! 'fun-apply-type-c phiX segM xv iv)
             (dk-fact! 'fun-apply-type-c phiY segN yv jv)
             (rkq-red-ff! iv jv)
             (subst (list '== (list (list ffT iv) jv) (entry iv jv)))
             (dk-fact! 'pair-in-cartesian xv yv (list phiX iv) (list phiY jv))
             (dk-fact! 'fun-apply-type-c fv cart ca (list 'LIST (list phiX iv) (list phiY jv)))
             (ass))))
  ;; --- (2) the transpose --------------------------------------------------
  (have! (rkq-gf 'i_ segM (rkq-gf 'j_ segN
            (list '== (list (list ggT 'j_) 'i_) (list (list ffT 'i_) 'j_))))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                      (symbol? (cadr f))
                                                      (equal? (caddr f) segM)))
                                     "i in OS(m)")))
                  (jv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                      (symbol? (cadr f))
                                                      (equal? (caddr f) segN)))
                                     "j in OS(n)"))))
             (dk-fact! 'fun-apply-type-c phiX segM xv iv)
             (dk-fact! 'fun-apply-type-c phiY segN yv jv)
             (rkq-red-ff! iv jv)
             (rkq-red-gg! iv jv)
             (subst (list '== (list (list ffT iv) jv) (entry iv jv)))
             (subst (list '== (list (list ggT jv) iv) (entry iv jv)))
             (qrfl))))
  ;; --- (3) the row sums ---------------------------------------------------
  (have! (rkq-gf 'i_ segM (list '== (list rsT 'i_) (list 'SUM-AG agv (list ffT 'i_) nn)))
         (lambda ()
           (let ((iv (dk-di-var!)))
             (dk-fact! 'fun-apply-type-c phiX segM xv iv)
             (dk-fact! 'enum-fam-value mm agv lami phiX iv)
             (subst (list '== (list rsT iv) (list lami (list phiX iv))))
             (lam-b)
             (mac 'FINSUM)
             (qrfl))))
  ;; --- (4) the column sums ------------------------------------------------
  (have! (rkq-gf 'j_ segN (list '== (list csT 'j_) (list 'SUM-AG agv (list ggT 'j_) mm)))
         (lambda ()
           (let ((jv (dk-di-var!)))
             (dk-fact! 'fun-apply-type-c phiY segN yv jv)
             (dk-fact! 'enum-fam-value nn agv lamj phiY jv)
             (subst (list '== (list csT jv) (list lamj (list phiY jv))))
             (lam-b)
             (mac 'FINSUM)
             (qrfl))))
  (dk-fact! 'sum-ag-fubini-ind mm agv nn ffT ggT rsT csT)
  (ass))
(rkq-check! 'finsum-fubini)
(qed 'finsum-fubini)
(topic! 'finsum-fubini 'algebra)

;;; ------------------------------------------------------ view read-offs
;;; ras-inv: INV(RING-ADDITIVE-AG A) = NEG A -- the FOURTH slot of the additive
;;; view.  theorem-library/ag-view-read-offs.scm proves CARR / OPR / IDEN and
;;; stops; the inverse slot is what the negative branch of ZZ-ACT needs.
(sp (make-wff '(FORALL A (IMPLIES (IS-RING A) (= (INV (RING-ADDITIVE-AG A)) (NEG A))))))
(di) (di)
(mac-h 'is-ring (dk-pick (dk-head? 'IS-RING) "is-ring"))
(dk-split-all!)
(slot 'INV)
(mac 'RING-ADDITIVE-AG)
(nth-r)
(rfl)
(rkq-check! 'ras-inv)
(qed 'ras-inv)
(topic! 'ras-inv 'algebra)

;;; commutative-ring-mul-comm: the `law' conjunct of IS-COMMUTATIVE-RING,
;;; surfaced (the subtype-laws.scm stl--project! shape).
(sp (make-wff '(FORALL s (IMPLIES (IS-COMMUTATIVE-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (= ((MUL s) a b) ((MUL s) b a))))))))))
(di) (di)
(mac-h 'is-commutative-ring-def (dk-pick (dk-head? 'IS-COMMUTATIVE-RING) "is-commutative-ring"))
(dk-split-all!)
(ass)
(rkq-check! 'commutative-ring-mul-comm)
(qed 'commutative-ring-mul-comm)
(topic! 'commutative-ring-mul-comm 'algebra)

;;; ------------------------------------------------- the ZZ-scalar law
(define (rkq-crprep! rngv)
  (dk-fact! 'commutative-ring-is-ring rngv)
  (dk-fact! 'ring-additive-ag-is-abelian-group rngv)
  (dk-fact! 'ras-carr rngv)
  (dk-fact! 'ras-op rngv)
  (dk-fact! 'ras-id rngv))
(define (rkq-to-rag! t rngv)
  (have! (rkq-in t (list 'CARR (list 'RING-ADDITIVE-AG rngv)))
         (lambda () (subst (list '= (list 'CARR (list 'RING-ADDITIVE-AG rngv))
                                    (list 'CARR rngv)))
                    (ass))))

;;; ring-scalar-zz-nn: the law for a NATURAL scalar, by induction on it.
(define rkq-szn-stmt
  '(FORALL k (IMPLIES (IN k NN)
     (FORALL rng (IMPLIES (IS-COMMUTATIVE-RING rng)
     (FORALL r (IMPLIES (IN r (CARR rng))
     (FORALL a (IMPLIES (IN a (CARR rng))
       (= ((MUL rng) r (ZZ-ACT (RING-ADDITIVE-AG rng) k a))
          (ZZ-ACT (RING-ADDITIVE-AG rng) k ((MUL rng) r a))))))))))))
(sp (make-wff rkq-szn-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkq-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkq-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  ;; ---- base --------------------------------------------------------------
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl   (dk-goal))
         (mul  (cadr gl))
         (rngv (cadr (car mul)))
         (rv   (cadr mul))
         (av   (cadddr (caddr mul)))
         (rag  (list 'RING-ADDITIVE-AG rngv))
         (ra   (list (list 'MUL rngv) rv av)))
    (display ";; rkq szn base: ") (display (list rngv rv av)) (newline)
    (rkq-crprep! rngv)
    (dk-fact! 'ring-carrier-closed-mul rngv rv av)
    (rkq-to-rag! av rngv)
    (rkq-to-rag! ra rngv)
    (dk-fact! 'zz-act-zero rag av)
    (dk-fact! 'zz-act-zero rag ra)
    (subst (list '= (list 'ZZ-ACT rag 0 av) (list 'IDEN rag)))
    (subst (list '= (list 'ZZ-ACT rag 0 ra) (list 'IDEN rag)))
    (subst (list '= (list 'IDEN rag) (list 'ZERO rngv)))
    (dk-fact! 'ring-mul-zero-right rngv rv)
    (ass))
  ;; ---- step --------------------------------------------------------------
  (dk-focus! step)
  (dk-peel!)
  (let* ((kv   (rkq-nn-var))
         (gl   (dk-goal))
         (mul  (cadr gl))
         (rngv (cadr (car mul)))
         (rv   (cadr mul))
         (av   (cadddr (caddr mul)))
         (rag  (list 'RING-ADDITIVE-AG rngv))
         (ra   (list (list 'MUL rngv) rv av))
         (A    (lambda (x y) (list (list 'ADD rngv) x y)))
         (Z    (lambda (t x) (list 'ZZ-ACT rag t x)))
         (ih   (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) "the IH")))
    (display ";; rkq szn step: ") (display (list kv rngv rv av)) (newline)
    (rkq-crprep! rngv)
    (dk-fact! 'ring-carrier-closed-mul rngv rv av)
    (rkq-to-rag! av rngv)
    (rkq-to-rag! ra rngv)
    (dk-fact! 'nn-subset-zz kv)
    (dk-fact! 'zz-one-in)
    (dk-fact! 'nn-succ-plus-one kv)                 ; (= (succ k) (+ k 1))
    (subst (list '= (list 'succ kv) (list '+ kv 1)))
    (dk-fact! 'zz-act-add rag kv 1 av)
    (dk-fact! 'zz-act-add rag kv 1 ra)
    (dk-fact! 'zz-act-one rag av)
    (dk-fact! 'zz-act-one rag ra)
    (subst (list '= (Z (list '+ kv 1) av) (rkq-o rag (Z kv av) (Z 1 av))))
    (subst (list '= (Z (list '+ kv 1) ra) (rkq-o rag (Z kv ra) (Z 1 ra))))
    (subst (list '= (Z 1 av) av))
    (subst (list '= (Z 1 ra) ra))
    (mac 'ras-op)
    (dk-fact! 'zz-act-type rag kv av)
    (have! (rkq-in (Z kv av) (list 'CARR rngv))
           (lambda () (subst (list '= (list 'CARR rngv)
                                      (list 'CARR rag)))
                      (ass)))
    (dk-fact! 'ring-left-dist rngv rv (Z kv av) av)
    (subst (list '= (list (list 'MUL rngv) rv (A (Z kv av) av))
                    (A (list (list 'MUL rngv) rv (Z kv av))
                       (list (list 'MUL rngv) rv av))))
    (dk-apply! ih rngv rv av)
    (subst (list '= (list (list 'MUL rngv) rv (Z kv av)) (Z kv ra)))
    (dk-fact! 'zz-act-type rag kv ra)
    (have! (rkq-in (Z kv ra) (list 'CARR rngv))
           (lambda () (subst (list '= (list 'CARR rngv) (list 'CARR rag))) (ass)))
    (dk-fact! 'ring-add-closed rngv (Z kv ra) ra)
    (rfl)))
(rkq-check! 'ring-scalar-zz-nn)
(qed 'ring-scalar-zz-nn)
(topic! 'ring-scalar-zz-nn 'algebra)

;;; ----------------------------------------------- finsum-ring-scalar-zz
;;; theorem-library/finsum-additive.scm:221, copied literally.
(define rkq-szz-stmt
  (list 'FORALL 'rng (list 'IMPLIES '(IS-COMMUTATIVE-RING rng)
    (list 'FORALL 'r (list 'IMPLIES '(IN r (CARR rng))
      (list 'FORALL 'c (list 'IMPLIES '(IN c ZZ)
        (list 'FORALL 'a (list 'IMPLIES '(IN a (CARR rng))
          (list '=
            (list '(MUL rng) 'r (list 'ZZ-ACT rkq-cra 'c 'a))
            (list 'ZZ-ACT rkq-cra 'c (list '(MUL rng) 'r 'a))))))))))))
(sp (make-wff rkq-szz-stmt))
(dk-peel!)
(let* ((gl   (dk-goal))
       (mul  (cadr gl))
       (rngv (cadr (car mul)))
       (rv   (cadr mul))
       (zz   (caddr mul))
       (crav (cadr zz)) (cv (caddr zz)) (av (cadddr zz))
       (rag  (list 'RING-ADDITIVE-AG rngv))
       (ra   (list (list 'MUL rngv) rv av))
       (N    (lambda (x) (list (list 'NEG rngv) x)))
       (M    (lambda (x y) (list (list 'MUL rngv) x y)))
       (Z    (lambda (t x) (list 'ZZ-ACT rag t x))))
  (display ";; rkq szz vars: ") (display (list rngv rv cv av)) (newline)
  (rkq-crprep! rngv)
  (dk-fact! 'cra-is-rag rngv)
  (subst (list '== crav rag))
  (dk-fact! 'ring-carrier-closed-mul rngv rv av)
  (rkq-to-rag! av rngv)
  (rkq-to-rag! ra rngv)
  (let* ((ex (dk-fact! 'zz-generated-by-nn cv))
         (nv (dk-skolem! ex))
         (orf (list 'OR (list '= cv nv) (list '= cv (list '- nv)))))
    (display ";; rkq szz witness: ") (display nv) (newline)
    (dk-fact! 'nn-subset-zz nv)
    (use-cases orf
      ;; ---- c = n ---------------------------------------------------------
      (lambda ()
        (subst (list '= cv nv))
        (dk-fact! 'ring-scalar-zz-nn nv rngv rv av)
        (ass))
      ;; ---- c = -n --------------------------------------------------------
      (lambda ()
        (subst (list '= cv (list '- nv)))
        (dk-fact! 'zz-act-neg-sign rag nv av)
        (dk-fact! 'zz-act-neg-sign rag nv ra)
        (subst (list '= (Z (list '- nv) av) (list (list 'INV rag) (Z nv av))))
        (subst (list '= (Z (list '- nv) ra) (list (list 'INV rag) (Z nv ra))))
        (dk-fact! 'ras-inv rngv)
        (subst (list '= (list 'INV rag) (list 'NEG rngv)))
        (dk-fact! 'zz-act-type rag nv av)
        (dk-fact! 'zz-act-type rag nv ra)
        (have! (rkq-in (Z nv av) (list 'CARR rngv))
               (lambda () (subst (list '= (list 'CARR rngv) (list 'CARR rag))) (ass)))
        (have! (rkq-in (Z nv ra) (list 'CARR rngv))
               (lambda () (subst (list '= (list 'CARR rngv) (list 'CARR rag))) (ass)))
        (dk-fact! 'ring-neg-in-carr rngv (Z nv av))
        (dk-fact! 'ring-neg-in-carr rngv (Z nv ra))
        (dk-fact! 'commutative-ring-mul-comm rngv rv (N (Z nv av)))
        (subst (list '= (M rv (N (Z nv av))) (M (N (Z nv av)) rv)))
        (dk-fact! 'ring-neg-mul-left rngv (Z nv av) rv)
        (subst (list '= (M (N (Z nv av)) rv) (N (M (Z nv av) rv))))
        (dk-fact! 'commutative-ring-mul-comm rngv (Z nv av) rv)
        (subst (list '= (M (Z nv av) rv) (M rv (Z nv av))))
        (dk-fact! 'ring-scalar-zz-nn nv rngv rv av)
        (subst (list '= (M rv (Z nv av)) (Z nv ra)))
        (rfl)))))
(rkq-check! 'finsum-ring-scalar-zz)
(qed 'finsum-ring-scalar-zz)
(topic! 'finsum-ring-scalar-zz 'algebra)
