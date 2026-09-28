;;; hom-laws.scm -- the models of a structure form a CATEGORY: identity arrows,
;;; composition, and the hom-set as a set.
;;;
;;; For every declared structure NAME with ONE independent carrier C (every
;;; structure in the tree but SETOID, which has two), structures.scm installs
;;; the hom-set HOM-NAME(a, b) = {f in FUN(C a, C b) | IS-HOM-NAME(a, b, f)}
;;; (`install-hom-set!').  This file PROVES, per structure:
;;;
;;;   hom-NAME-member-iff  f in HOM-NAME(a, b) iff f in FUN(C a, C b) and IS-HOM-NAME(a, b, f)
;;;   hom-NAME-id          IS-NAME(a) => IS-HOM-NAME(a, a, ID-FUN(C a))
;;;   hom-NAME-compose     IS-HOM-NAME(a, b, f) => IS-HOM-NAME(b, c, g)
;;;                        => IS-HOM-NAME(a, c, COMPOSE(g, f))
;;;   hom-NAME-in-set      IS-NAME(a) => IS-NAME(b) => HOM-NAME(a, b) in SET
;;;
;;; by GENERIC drivers that read the structure record, not by one proof per
;;; structure.  Three cases:
;;;
;;; (1) a SHAPE structure with a GENERATED hom (preservation of slots,
;;;     build-hom-axiom): the hom definition is unfolded in the goal and every
;;;     conjunct is closed by the one closer below, whatever the slot kind --
;;;     a substructure or non-carrier constant (N a = N c: rewrite by the f
;;;     clause, the g clause is then the goal), a carrier constant, an operation
;;;     with carrier or non-carrier arguments and range.  The rewriting is
;;;     compose-apply (resp. id-fun-apply) at arguments TYPED first: the
;;;     eigenvariables by their guards, an applied operation by its FUN typing
;;;     (the IS-NAME conjunct) through fun-apply-type-c, with apply-tupling-2 and
;;;     pair-in-cartesian for a binary one.
;;; (2) a REFINEMENT (same-shape-as P): IS-HOM-NAME is IS-NAME(a), IS-NAME(b)
;;;     and IS-HOM-P; the laws of P are cited.
;;; (3) an OVERRIDDEN hom (declare-hom!): proved by hand in the second half
;;;     of this file (TOP-SPACE, METRIZABLE-TOP-SPACE: continuity by preimages;
;;;     RINGOID: a ring hom of the underlying rings preserving the ideal).
;;;
;;; Nothing is asserted; every qed is expected modulo 0.  Batch 33 (2026-09-25).

;;; --- the structure record ------------------------------------------------
(define (hml-carrier name)
  (let* ((sd (find-shape-structure name))
         (cs (map car (filter (lambda (s) (eq? (cadr s) 'carrier)) (structure-def-slots sd)))))
    (if (= (length cs) 1) (car cs) (error "hml-carrier: not a single-carrier structure" name))))
(define (hml-shape? name) (if (lookup-structure name) #t #f))
(define (hml-parent name) (definitional-structure-parent (lookup-definitional-structure name)))
(define (hml-is name) (symbol-append 'IS- name))
(define (hml-hom name) (structure-hom-name name))
(define (hml-hom-def name) (symbol-append (structure-hom-name name) '-def))
(define (hml-set name) (symbol-append 'HOM- name))
(define (hml-is-def name) (if (hml-shape? name) (hml-is name) (symbol-append 'is- name '-def)))
(define (hml-thm name suffix) (symbol-append 'hom- name suffix))

;;; --- formula utilities ---------------------------------------------------
(define (hml-inst thm . terms)
  (let loop ((f (lookup-theorem thm)) (ts terms))
    (if (null? ts) f
        (loop (subst-free (quantifier-var f) (car ts) (quantifier-body f)) (cdr ts)))))
(define (hml-conjuncts f)
  (if (dk-head-is? f 'AND)
      (append (hml-conjuncts (cadr f)) (hml-conjuncts (caddr f)))
      (list f)))
(define (hml-and fs)
  (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (hml-and (cdr fs)))))
(define (hml-subterm pred e)
  (cond ((pred e) e)
        ((pair? e)
         (let loop ((l e))
           (cond ((not (pair? l)) #f)
                 ((hml-subterm pred (car l)))
                 (#t (loop (cdr l))))))
        (#t #f)))
(define (hml-occurs? sub e) (if (hml-subterm (lambda (x) (equal? x sub)) e) #t #f))
(define (hml-redex-of head)
  (lambda (e) (and (pair? e) (= (length e) 2) (pair? (car e)) (eq? (caar e) head))))
(define (hml-index g lst)
  (let loop ((l lst) (i 0))
    (cond ((null? l) #f)
          ((eq? #t (vnb-guard (lambda () (alpha-equiv? (car l) g)))) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (hml-guards f)                  ; guard classes of a guarded FORALL chain
  (if (and (dk-head-is? f 'FORALL) (dk-head-is? (caddr f) 'IMPLIES)
           (dk-head-is? (cadr (caddr f)) 'IN))
      (cons (caddr (cadr (caddr f))) (hml-guards (caddr (caddr f))))
      '()))
(define (hml-ctx f who)
  (or (dk-ctx-form f) (error "hom-laws: not in context --" who (expression->string f))))
(define (hml-done! name)
  (if (proof-done? *ps*) (qed name) (error "hom-laws: failed to prove" name)))

;;; --- typing facts --------------------------------------------------------
;;; The slot typings (IN (ACC v) X) among the conjuncts of IS-NAME(v), NAME a
;;; shape: the carrier's sethood, each constant's and each operation's typing;
;;; and the PIN (= (N v) X) of each DERIVED carrier N (FIELD's NON-ZERO).
(define (hml-derived-slots name)
  (map car (filter (lambda (s) (eq? (cadr s) 'derived))
                   (structure-def-slots (find-shape-structure name)))))
(define (hml-typings name v)
  (let ((accs (map car (structure-def-slots (lookup-structure name))))
        (drv  (hml-derived-slots name)))
    (filter (lambda (c) (or (and (dk-head-is? c 'IN) (pair? (cadr c)) (= (length (cadr c)) 2)
                                 (memq (car (cadr c)) accs) (equal? (cadr (cadr c)) v))
                            (and (dk-head-is? c '=) (pair? (cadr c)) (= (length (cadr c)) 2)
                                 (memq (car (cadr c)) drv) (equal? (cadr (cadr c)) v))))
            (hml-conjuncts (caddr (hml-inst (hml-is name) v))))))

;;; land them, IS-NAME(v) surviving (the unfold runs in a lane)
(define (hml-land-typings! name v)
  (let ((ts (filter (lambda (t) (not (dk-asm? t))) (hml-typings name v))))
    (if (pair? ts)
        (let ((conj (hml-and ts)))
          (dk-have! conj
            (lambda ()
              (mac-h (hml-is name) (hml-ctx (list (hml-is name) v) "IS-NAME"))
              (dk-split-all!)
              (dk-conj-close!)))
          (if (pair? (cdr ts)) (dk-split-all! (list (hml-ctx conj "typings"))))))))

;;; a conjunct LAW of IS-NAME(v), NAME a shape, landed in a lane (IS-NAME(v)
;;; survives); returned as held
(define (hml-project! name v law)
  (if (not (dk-asm? law))
      (dk-have! law
        (lambda ()
          (mac-h (hml-is name) (hml-ctx (list (hml-is name) v) "IS-NAME"))
          (dk-split-all!)
          (ass))))
  (hml-ctx law "projection"))

;;; (IN (C v) SET), down the refinement chain to the shape, in a lane
(define (hml-carrier-set! name v)
  (let ((goal (list 'IN (list (hml-carrier name) v) 'SET)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (let loop ((nm name))
              (mac-h (hml-is-def nm) (hml-ctx (list (hml-is nm) v) "IS-NAME"))
              (dk-split-all!)
              (if (not (hml-shape? nm)) (loop (hml-parent nm))))
            (ass))))))

;;; the FUN typing of the operation OPV in context, or #f
(define (hml-op-typing opv)
  (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) opv)
                               (dk-head-is? (caddr f) 'FUN) (= (length (caddr f)) 3)))
              (dk-asms)))

;;; type the applied operation T = ((OP v) x ...) in its range, the arguments
;;; typed in context; returns the typing as held
(define (hml-op-type! t)
  (let* ((opv  (car t)) (args (cdr t))
         (ty   (or (hml-op-typing opv) (error "hml-op-type!: no FUN typing for" (expression->string opv))))
         (dom  (cadr (caddr ty))) (rng (caddr (caddr ty)))
         (goal (list 'IN t rng)))
    (cond ((dk-asm? goal) (dk-ctx-form goal))
          ((= (length args) 1) (dk-cite! 'fun-apply-type-c opv dom rng (car args)))
          ((= (length args) 2)
           (let ((lst (list 'LIST (car args) (cadr args))))
             (dk-have! goal
               (lambda ()
                 (fact 'apply-tupling-2 opv (car args) (cadr args))
                 (subst (list '== t (list opv lst)))
                 (fact 'pair-in-cartesian (cadr dom) (caddr dom) (car args) (cadr args))
                 (fact 'fun-apply-type-c opv dom rng lst)
                 (ass)))
             (hml-ctx goal "op typing")))
          (#t (error "hml-op-type!: arity" (expression->string t))))))

(define (hml-op-app? e)
  (and (pair? e) (pair? (car e)) (= (length (car e)) 2) (hml-op-typing (car e)) #t))

;;; T typed in a DERIVED carrier D = (N v), pinned (= D (DIFFERENCE CV X)):
;;; land (IN T CV) -- difference-membership, in a lane
(define (hml-lift! t cv)
  (let* ((pin (or (find-first (lambda (f) (and (dk-head-is? f '=) (dk-head-is? (caddr f) 'DIFFERENCE)
                                               (equal? (cadr (caddr f)) cv)
                                               (dk-asm? (list 'IN t (cadr f)))))
                              (dk-asms))
                  (error "hml-lift!: no derived typing for" (expression->string t))))
         (dif (caddr pin))
         (td  (list 'IN t dif)))
    (dk-have! (list 'IN t cv)
      (lambda ()
        (dk-have! td (lambda () (subst (list '= dif (cadr pin))) (ass)))
        (mac-h 'difference-membership (hml-ctx td "difference typing"))
        (dk-split-all!)
        (ass)))))

;;; (IN T CV) in context: already, or by the operation's typing, or lifted from
;;; a derived carrier
(define (hml-ensure-typed! t cv)
  (let ((goal (list 'IN t cv)))
    (if (not (dk-asm? goal))
        (begin
          (if (hml-op-app? t) (hml-op-type! t))
          (if (not (dk-asm? goal)) (hml-lift! t cv))))))

;;; --- (1) SHAPE, generated hom -----------------------------------------------

;;; hom-NAME-id
(define (hml-id-close! cv)
  (let ((g (dk-goal)))
    (cond ((dk-asm? g) (ass))
          ((and (dk-head-is? g 'IN) (dk-head-is? (cadr g) 'ID-FUN))
           (dk-cite! 'id-fun-type cv) (ass))
          (#t
           (if (dk-head-is? g 'FORALL) (dk-peel!))
           (let loop ()
             (let ((r (hml-subterm (hml-redex-of 'ID-FUN) (dk-goal))))
               (if r
                   (let ((t (cadr r)))
                     (hml-ensure-typed! t cv)
                     (subst (dk-cite! 'id-fun-apply cv t))
                     (loop)))))
           (let ((l (cadr (dk-goal))))
             (if (hml-op-app? l) (hml-op-type! l)))
           (rfl)))))

(define (hml-prove-id-shape! name)
  (let ((cacc (hml-carrier name)))
    (sp (make-wff `(FORALL a (IMPLIES (,(hml-is name) a)
                     (,(hml-hom name) a a (ID-FUN (,cacc a)))))))
    (dk-peel!)
    (let* ((v (cadr (dk-goal))) (cv (list cacc v)))
      (hml-land-typings! name v)
      (mac (hml-hom-def name))
      (dk-conj-close! (lambda () (hml-id-close! cv)))
      (hml-done! (hml-thm name '-id)))))

;;; hom-NAME-compose
;;; the argument of the g clause at the eigenvariable E whose guard in the g
;;; clause is GK: (f E) when GK is the carrier C(b), else E itself, its typing
;;; transported from a to b by the f clauses' equations N(a) = N(b).
(define (hml-transport! e gk ideqs)
  (let ((goal (list 'IN e gk)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (for-each (lambda (eq)
                        (if (hml-occurs? (caddr eq) (dk-goal))
                            (subst (list '= (caddr eq) (cadr eq)))))
                      ideqs)
            (ass))))))

(define (hml-h-args! h0 es vf ca cb ideqs dmaps)
  (let loop ((gs (hml-guards h0)) (es es) (acc '()))
    (if (or (null? gs) (null? es))
        (reverse acc)
        (let* ((gk (car gs)) (ek (car es))
               (dm (and (pair? gk) (assq (car gk) dmaps))))
          (cond ((equal? gk cb)
                 (if (not (dk-asm? (list 'IN (list vf ek) cb)))
                     (dk-cite! 'fun-apply-type-c vf ca cb ek))
                 (loop (cdr gs) (cdr es) (cons (list vf ek) acc)))
                ;; a DERIVED carrier rides the carrier's map: f sends N(a) into
                ;; N(b) -- a THEOREM (hom-NAME-N), cited before the unfold
                (dm
                 (if (not (dk-asm? (list 'IN (list vf ek) gk)))
                     (dk-apply! (cdr dm) ek))
                 (loop (cdr gs) (cdr es) (cons (list vf ek) acc)))
                (#t
                 (hml-transport! ek gk ideqs)
                 (loop (cdr gs) (cdr es) (cons ek acc))))))))

(define (hml-comp-close! cu vf vg ca cb cc fconj gconj cconj ideqs dmaps)
  (let* ((g (dk-goal)))
    (cond ((dk-asm? g) (ass))
          ((and (dk-head-is? g 'IN) (dk-head-is? (cadr g) 'COMPOSE))
           (dk-cite! 'compose-type ca cb cc vg vf) (ass))
          (#t
           (let* ((i  (or (hml-index g cconj) (error "hml-comp-close!: unknown conjunct" (expression->string g))))
                  (f0 (hml-ctx (list-ref fconj i) "f clause"))
                  (h0 (hml-ctx (list-ref gconj i) "g clause"))
                  (fi (if (dk-head-is? g 'FORALL)
                          (let* ((landed (dk-peel!))
                                 (es (map cadr (filter (lambda (x) (and (dk-head-is? x 'IN) (symbol? (cadr x))))
                                                       landed)))
                                 (fi0 (apply dk-apply! f0 es))
                                 (hargs (hml-h-args! h0 es vf ca cb ideqs dmaps)))
                            (apply dk-apply! h0 hargs)
                            fi0)
                          f0)))
             (let loop ()
               (let ((r (hml-subterm (hml-redex-of 'COMPOSE) (dk-goal))))
                 (if r
                     (let ((t (cadr r)))
                       (hml-ensure-typed! t ca)
                       (subst (dk-apply! cu t))
                       (loop)))))
             (subst fi)
             (ass))))))

(define (hml-prove-compose-shape! name)
  (let ((cacc (hml-carrier name)) (hom (hml-hom name)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL f (FORALL g
           (IMPLIES (,hom a b f) (IMPLIES (,hom b c g) (,hom a c (COMPOSE g f)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (va (cadr gl)) (vc (caddr gl)) (gf (cadddr gl))
           (vg (cadr gf)) (vf (caddr gf))
           (hf (dk-pick (lambda (x) (and (dk-head-is? x hom) (equal? (cadddr x) vf))) "the f hom"))
           (vb (caddr hf))
           (hg (hml-ctx (list hom vb vc vg) "the g hom"))
           (ca (list cacc va)) (cb (list cacc vb)) (cc (list cacc vc))
           (fconj (hml-conjuncts (caddr (hml-inst (hml-hom-def name) va vb vf))))
           (gconj (hml-conjuncts (caddr (hml-inst (hml-hom-def name) vb vc vg))))
           (cconj (hml-conjuncts (caddr (hml-inst (hml-hom-def name) va vc gf))))
           (ideqs (filter (lambda (c) (and (dk-head-is? c '=) (pair? (cadr c)) (pair? (caddr c))
                                            (= (length (cadr c)) 2) (symbol? (car (cadr c)))
                                            (equal? (cadr (cadr c)) va)
                                            (equal? (caddr c) (list (car (cadr c)) vb))))
                          fconj)))
      ;; the derived-carrier lemmas need the hom hypothesis: cite them first
      (let ((dmaps (map (lambda (n)
                          (cons n (dk-cite! (hml-thm name (symbol-append '- n)) va vb vf)))
                        (hml-derived-slots name))))
      (mac-h (hml-hom-def name) hf)
      (mac-h (hml-hom-def name) hg)
      (dk-split-all!)
      (hml-land-typings! name va)
      (dk-have! (list 'AND (list 'IN vf (list 'FUN ca cb)) (list 'IN vg (list 'FUN cb cc))))
      (let ((cu (dk-cite! 'compose-apply ca cb cc vg vf)))
        (mac (hml-hom-def name))
        (dk-conj-close! (lambda () (hml-comp-close! cu vf vg ca cb cc fconj gconj cconj ideqs dmaps)))))
      (hml-done! (hml-thm name '-compose)))))

;;; --- (2) REFINEMENT: cite the parent's law ---------------------------------
(define (hml-prove-id-refinement! name)
  (let ((cacc (hml-carrier name)) (p (hml-parent name)))
    (sp (make-wff `(FORALL a (IMPLIES (,(hml-is name) a)
                     (,(hml-hom name) a a (ID-FUN (,cacc a)))))))
    (dk-peel!)
    (let ((v (cadr (dk-goal))))
      (dk-have! (list (hml-is p) v)
        (lambda ()
          (mac-h (hml-is-def name) (hml-ctx (list (hml-is name) v) "IS-NAME"))
          (dk-split-all!)
          (ass)))
      (dk-cite! (hml-thm p '-id) v)
      (mac (hml-hom-def name))
      (dk-conj-close!)
      (hml-done! (hml-thm name '-id)))))

(define (hml-prove-compose-refinement! name)
  (let ((hom (hml-hom name)) (p (hml-parent name)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL f (FORALL g
           (IMPLIES (,hom a b f) (IMPLIES (,hom b c g) (,hom a c (COMPOSE g f)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (va (cadr gl)) (vc (caddr gl)) (gf (cadddr gl))
           (vg (cadr gf)) (vf (caddr gf))
           (hf (dk-pick (lambda (x) (and (dk-head-is? x hom) (equal? (cadddr x) vf))) "the f hom"))
           (vb (caddr hf))
           (hg (hml-ctx (list hom vb vc vg) "the g hom")))
      (mac-h (hml-hom-def name) hf)
      (mac-h (hml-hom-def name) hg)
      (dk-split-all!)
      (dk-cite! (hml-thm p '-compose) va vb vc vf vg)
      (mac (hml-hom-def name))
      (dk-conj-close!)
      (hml-done! (hml-thm name '-compose)))))

;;; --- every single-carrier structure: membership and sethood ------------------
(define (hml-prove-member-iff! name)
  (let ((cacc (hml-carrier name)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL f
           (IFF (IN f (,(hml-set name) a b))
                (AND (IN f (FUN (,cacc a) (,cacc b))) (,(hml-hom name) a b f))))))))
    (dk-peel!)
    (mac (hml-set name))
    (for-each
      (lambda (lf)
        (dk-focus! lf)
        (if (dk-head-is? (dk-goal) 'AND)
            (begin
              (sep-me (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (dk-head-is? (caddr x) 'SEP)))
                               "the SEP membership"))
              (dk-conj-close!))
            (begin
              (dk-split-all!)
              (in-sep! (lambda () (ass)) (lambda () (ass))))))
      (dk-opened (lambda () (di))))
    (hml-done! (hml-thm name '-member-iff))))

(define (hml-prove-in-set! name)
  (sp (make-wff `(FORALL a (FORALL b (IMPLIES (,(hml-is name) a) (IMPLIES (,(hml-is name) b)
                   (IN (,(hml-set name) a b) SET)))))))
  (dk-peel!)
  (let* ((hs (cadr (dk-goal))) (va (cadr hs)) (vb (caddr hs)))
    (hml-carrier-set! name va)
    (hml-carrier-set! name vb)
    (mac (hml-set name))
    (sep-set)
    (mac 'fun-set-iff)
    (dk-conj-close!)
    (hml-done! (hml-thm name '-in-set))))

;;; the four laws for a structure with a GENERATED hom
(define (hml-prove-for! name)
  (hml-prove-member-iff! name)
  (if (hml-shape? name)
      (begin (hml-prove-id-shape! name) (hml-prove-compose-shape! name))
      (begin (hml-prove-id-refinement! name) (hml-prove-compose-refinement! name)))
  (hml-prove-in-set! name))

(define *hml-generated*
  '(SEMIGROUP MONOID COMM-MONOID GROUP ABELIAN-GROUP
    RING COMMUTATIVE-RING INTEGRAL-DOMAIN EUCLIDEAN-RING PID FIELD-RING
    NORMED-AG NORMED-FIELD MODULE VECTOR-SPACE NORMED-VECTOR-SPACE
    COMPLEX-INNER-PRODUCT-SPACE METRIC-SPACE PSEUDOMETRIC-SPACE C-METRIC-SPACE
    ;; MEASURABLE-SPACE and MEASURE-SPACE left this list 2026-09-28 (batch 39): their
    ;; arrows are now the family and family-fun kinds' pullback clauses, proven by
    ;; hand in theorem-library/hom-kinds.scm.
    ))
(for-each hml-prove-for! *hml-generated*)

;;; --- FIELD: its derived carrier -------------------------------------------------
;;;
;;; hom-field-non-zero:  IS-HOM-FIELD(a, b, f) => f sends NON-ZERO(a) into NON-ZERO(b).
;;;
;;; The field hom has ONE map, typed on the carrier; its MUL-INV clause is
;;; guarded on NON-ZERO(a), and the g clause of a composite is guarded on
;;; NON-ZERO(b) -- so composing needs f(x) /= 0 for x /= 0.  A field hom kills
;;; nothing: were f(x) = 0, then 1 = f(1) = f(x * x^-1) = f(x) * f(x^-1)
;;; = 0 * f(x^-1) = 0 in b, against 0 /= 1 (IS-FIELD).  The product with zero is
;;; ring-mul-zero-left read through the view FIELD-AS-INTEGRAL-DOMAIN
;;; (field-id-mul / field-id-zero / field-id-carr).  This is also the typing
;;; lemma FIELD-MULTIPLICATIVE-GROUP's functoriality was owed
;;; (structure-library/functoriality.scm; see hom-views.scm).
(sp (make-wff '(FORALL a (FORALL b (FORALL f (IMPLIES (IS-HOM-FIELD a b f)
       (FORALL x (IMPLIES (IN x (NON-ZERO a)) (IN (f x) (NON-ZERO b))))))))))
(dk-peel!)
(let* ((gl   (dk-goal)) (fx (cadr gl)) (vf (car fx)) (vx (cadr fx)) (vb (cadr (caddr gl)))
       (hf   (dk-pick (lambda (h) (and (dk-head-is? h 'IS-HOM-FIELD) (equal? (cadddr h) vf)))
                      "the field hom"))
       (va   (cadr hf))
       (ca   (list 'CARR va)) (cb (list 'CARR vb))
       (inv  (list (list 'MUL-INV va) vx))
       (finv (list vf inv))
       (fconj (hml-conjuncts (caddr (hml-inst 'IS-HOM-FIELD-def va vb vf))))
       (fmul (find-first (lambda (c) (and (dk-head-is? c 'FORALL) (hml-occurs? (list 'MUL va) c))) fconj))
       (fone (find-first (lambda (c) (hml-occurs? (list 'ONE va) c)) fconj))
       (law1 (find-first (lambda (c) (and (dk-head-is? c 'FORALL) (hml-occurs? 'MUL-INV c)))
                         (hml-conjuncts (caddr (hml-inst 'IS-FIELD va)))))
       (law2 (find-first (lambda (c) (dk-head-is? c 'NOT))
                         (hml-conjuncts (caddr (hml-inst 'IS-FIELD vb)))))
       (faid (list 'FIELD-AS-INTEGRAL-DOMAIN vb))
       (m0   (list (list 'MUL vb) (list 'ZERO vb) finv)))
  (mac-h 'IS-HOM-FIELD-def hf)
  (dk-split-all!)
  (hml-land-typings! 'FIELD va)
  (hml-land-typings! 'FIELD vb)
  (hml-ensure-typed! vx ca)
  (hml-ensure-typed! inv ca)
  (dk-cite! 'fun-apply-type-c vf ca cb vx)
  (dk-cite! 'fun-apply-type-c vf ca cb inv)
  (let* ((l1 (hml-project! 'FIELD va law1))
         (l2 (hml-project! 'FIELD vb law2))
         (e1 (dk-apply! l1 vx))                                   ; x * x^-1 = 1
         (e2 (dk-apply! (hml-ctx fmul "f mul clause") vx inv))    ; f(x * x^-1) = f(x) * f(x^-1)
         (e3 (hml-ctx fone "f one clause")))                      ; f(1) = 1
    ;; 0 * f(x^-1) = 0 in b, through the integral-domain view of b
    (dk-cite! 'field-as-integral-domain-is-integral-domain vb)
    (dk-cite! 'integral-domain-is-commutative-ring faid)
    (dk-cite! 'commutative-ring-is-ring faid)
    (dk-cite! 'field-id-carr vb)
    (dk-cite! 'field-id-mul vb)
    (dk-cite! 'field-id-zero vb)
    (dk-have! (list 'IN finv (list 'CARR faid))
      (lambda () (subst (list '== (list 'CARR faid) cb)) (ass)))
    (let ((z (dk-apply! (dk-cite! 'ring-mul-zero-left faid) finv)))
      (dk-have! (list '= m0 (list 'ZERO vb))
        (lambda ()
          (subst (list '== (list 'MUL vb) (list 'MUL faid)))
          (subst (list '== (list 'ZERO vb) (list 'ZERO faid)))
          (ass))))
    ;; the goal: f(x) in CARR(b) minus {0}
    (subst (list '= (list 'NON-ZERO vb) (list 'DIFFERENCE cb (list 'SINGLETON (list 'ZERO vb)))))
    (mac 'difference-membership)
    (dk-conj-close!
      (lambda ()
        (if (not (dk-head-is? (dk-goal) 'NOT))
            (ass)
            (let ((sg (dk-landed-1 (lambda () (di)))))   ; f(x) in {0}; goal FALSITY
              (mac-h 'singleton-membership sg)
              (dk-split-all!)
              ;; f(x) * f(x^-1) = 1 with f(x) = 0 ...
              (dk-have! (list '= m0 (list 'ONE vb))
                (lambda ()
                  (subst (list '= (list 'ZERO vb) fx))
                  (subst (list '= (caddr e2) (cadr e2)))
                  (subst e1)
                  (ass)))
              ;; ... so 0 = 1 in b
              (dk-have! (list '= (list 'ZERO vb) (list 'ONE vb))
                (lambda ()
                  (subst (list '= (list 'ONE vb) m0))
                  (subst (list '= m0 (list 'ZERO vb)))
                  (rfl)))
              (ai l2)))))))
(hml-done! 'hom-field-non-zero)

(hml-prove-for! 'FIELD)

;;; --- (3) OVERRIDDEN homs ----------------------------------------------------------
;;;
;;; membership and sethood are the generic ones (they see only the predicate);
;;; the identity and composition laws are proved here, by hand.

;;; x in B from A in POWER(B) and x in A (power-set-membership, in a lane)
(define (hml-sub-elt! x a-set b-set)
  (let ((goal (list 'IN x b-set)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (mac-h 'power-set-membership (hml-ctx (list 'IN a-set (list 'POWER b-set)) "power typing"))
            (dk-split-all!)
            (dk-apply! (hml-ctx (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z a-set) (list 'IN 'z b-set)))
                                "the inclusion")
                       x)
            (ass))))
    (hml-ctx goal "sub-element")))

;;; replace every occurrence of S by T in E
(define (hml-replace e s t)
  (cond ((equal? e s) t)
        ((pair? e) (map (lambda (x) (hml-replace x s t)) e))
        (#t e)))

;;; the hypothesis H with the equation EQ = (= S T) applied, landed: there is no
;;; hypothesis-side `subst', so H => H[S:=T] is proved on a lane (the `subst'
;;; rewrites both sides of the implication) and detached.
(define (hml-rewrite-hyp! h eq)
  (let* ((h2  (hml-replace h (cadr eq) (caddr eq)))
         (imp (list 'IMPLIES h h2)))
    (if (not (dk-asm? h2))
        (begin
          (dk-have! imp (lambda () (subst eq) (di) (ass)))
          (detach! (hml-ctx imp "the rewriting implication"))))
    (hml-ctx h2 "the rewritten hypothesis")))

;;; A = B for two classes, by class-extensionality: FWD proves x in B with x in A
;;; in context, BWD x in A with x in B; each gets x.  Returns the equation.
(define (hml-class-eq! a-cls b-cls fwd bwd)
  (let ((ch (dk-cite! 'class-extensionality a-cls b-cls)))
    (detach-with! ch
      (lambda ()
        (di)                                   ; the unguarded universal
        (let ((x (cadr (cadr (dk-goal)))))     ; (IFF (IN x A) (IN x B))
          (for-each (lambda (lf)
                      (dk-focus! lf)
                      (if (equal? (caddr (dk-goal)) b-cls) (fwd x) (bwd x)))
                    (dk-opened (lambda () (di)))))))
    (hml-ctx (list '= a-cls b-cls) "the class equation")))

;;; close a membership goal through PREIMAGE and AND layers, then CLOSER
(define (hml-preimage-close! closer)
  (let ((g (dk-goal)))
    (cond ((dk-asm? g) (ass))
          ((dk-head-is? g 'AND) (dk-conj-close! (lambda () (hml-preimage-close! closer))))
          ((and (dk-head-is? g 'IN) (dk-head-is? (caddr g) 'PREIMAGE))
           (mac 'preimage-membership)
           (hml-preimage-close! closer))
          (#t (closer)))))

;;; IS-TOP-SPACE(v) in context (METRIZABLE-TOP-SPACE is a refinement of it)
(define (hml-to-top! name v)
  (if (not (eq? name 'TOP-SPACE))
      (dk-have! (list 'IS-TOP-SPACE v)
        (lambda ()
          (mac-h (hml-is-def name) (hml-ctx (list (hml-is name) v) "IS-NAME"))
          (dk-split-all!)
          (ass)))))

;;; TOP-SPACE, METRIZABLE-TOP-SPACE: the identity is continuous --
;;; PREIMAGE(s, ID, u) = u for u open (u is a subset of PTS(s)).
(define (hml-prove-top-id! name)
  (sp (make-wff `(FORALL s (IMPLIES (,(hml-is name) s) (,(hml-hom name) s s (ID-FUN (PTS s)))))))
  (dk-peel!)
  (let* ((v (cadr (dk-goal))) (pv (list 'PTS v)) (idf (list 'ID-FUN pv)))
    (hml-to-top! name v)
    (hml-land-typings! 'TOP-SPACE v)
    (mac (hml-hom-def name))
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond ((dk-asm? g) (ass))
                ((dk-head-is? g 'IN) (dk-cite! 'id-fun-type pv) (ass))  ; ID typing
                (#t
                 (dk-peel!)
                 (let* ((pre (cadr (dk-goal)))               ; PREIMAGE(s, ID, u)
                        (u   (cadddr pre)))
                   (hml-sub-elt! u (list 'OPENS v) (list 'POWER pv))
                   (let ((e (hml-class-eq! pre u
                              (lambda (x)                      ; x in PREIMAGE => x in u
                                (mac-h 'preimage-membership (hml-ctx (list 'IN x pre) "x in preimage"))
                                (dk-split-all!)
                                (hml-rewrite-hyp! (list 'IN (list idf x) u)
                                                  (dk-cite! 'id-fun-apply pv x))
                                (ass))
                              (lambda (x)                      ; x in u => x in PREIMAGE
                                (hml-sub-elt! x u pv)
                                (hml-preimage-close!
                                  (lambda ()
                                    (subst (dk-cite! 'id-fun-apply pv x))
                                    (ass)))))))
                     (subst e)
                     (ass))))))))
    (hml-done! (hml-thm name '-id))))

;;; ... and the composite of continuous maps is continuous --
;;; PREIMAGE(s, g o f, u) = PREIMAGE(s, f, PREIMAGE(t, g, u)).
(define (hml-prove-top-compose! name)
  (let ((hom (hml-hom name)))
    (sp (make-wff `(FORALL s (FORALL t (FORALL w (FORALL f (FORALL g
           (IMPLIES (,hom s t f) (IMPLIES (,hom t w g) (,hom s w (COMPOSE g f)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (vs (cadr gl)) (vw (caddr gl)) (gf (cadddr gl))
           (vg (cadr gf)) (vf (caddr gf))
           (hf (dk-pick (lambda (x) (and (dk-head-is? x hom) (equal? (cadddr x) vf))) "the f hom"))
           (vt (caddr hf))
           (hg (hml-ctx (list hom vt vw vg) "the g hom"))
           (ps (list 'PTS vs)) (pt (list 'PTS vt)) (pw (list 'PTS vw))
           (fconj (hml-conjuncts (caddr (hml-inst (hml-hom-def name) vs vt vf))))
           (gconj (hml-conjuncts (caddr (hml-inst (hml-hom-def name) vt vw vg)))))
      (mac-h (hml-hom-def name) hf)
      (mac-h (hml-hom-def name) hg)
      (dk-split-all!)
      (hml-to-top! name vs)
      (hml-land-typings! 'TOP-SPACE vs)
      (dk-have! (list 'AND (list 'IN vf (list 'FUN ps pt)) (list 'IN vg (list 'FUN pt pw))))
      (let ((cu (dk-cite! 'compose-apply ps pt pw vg vf))
            (uf (hml-ctx (list-ref fconj (- (length fconj) 1)) "f continuity"))
            (ug (hml-ctx (list-ref gconj (- (length gconj) 1)) "g continuity")))
        (mac (hml-hom-def name))
        (dk-conj-close!
          (lambda ()
            (let ((g (dk-goal)))
              (cond ((dk-asm? g) (ass))
                    ((dk-head-is? g 'IN) (dk-cite! 'compose-type ps pt pw vg vf) (ass))
                    (#t
                     (dk-peel!)
                     (let* ((pre (cadr (dk-goal)))           ; PREIMAGE(s, g o f, u)
                            (u   (cadddr pre))
                            (pg  (list 'PREIMAGE vt vg u))
                            (pfg (list 'PREIMAGE vs vf pg)))
                       (dk-apply! ug u)                      ; PREIMAGE(t, g, u) open in t
                       (dk-apply! uf pg)                     ; its f-preimage open in s
                       (let ((e (hml-class-eq! pre pfg
                                  (lambda (x)
                                    (mac-h 'preimage-membership (hml-ctx (list 'IN x pre) "x in preimage"))
                                    (dk-split-all!)
                                    (let ((ex (dk-apply! cu x)))
                                      (hml-rewrite-hyp! (list 'IN (list gf x) u) ex))
                                    (dk-cite! 'fun-apply-type-c vf ps pt x)
                                    (hml-preimage-close! (lambda () (ass))))
                                  (lambda (x)
                                    (mac-h 'preimage-membership (hml-ctx (list 'IN x pfg) "x in preimage"))
                                    (dk-split-all!)
                                    (mac-h 'preimage-membership (hml-ctx (list 'IN (list vf x) pg) "f x in preimage"))
                                    (dk-split-all!)
                                    (hml-preimage-close!
                                      (lambda ()
                                        (subst (dk-apply! cu x))
                                        (ass)))))))
                         (subst e)
                         (ass)))))))))
      (hml-done! (hml-thm name '-compose)))))

;;; RINGOID: a ring hom of the underlying rings preserving the ideal.  The ring
;;; clause is the RING law read through the view RINGOID-AS-RING, whose carrier
;;; is the ringoid's: CARR(RINGOID-AS-RING a) == CARR(a) by the slot read-off.
(define (hml-prove-ringoid-id!)
  (sp (make-wff '(FORALL a (IMPLIES (IS-RINGOID a) (IS-HOM-RINGOID a a (ID-FUN (CARR a)))))))
  (dk-peel!)
  (let* ((v (cadr (dk-goal))) (cv (list 'CARR v)) (rv (list 'RINGOID-AS-RING v))
         (crv (list 'CARR rv)))
    (hml-land-typings! 'RINGOID v)
    (dk-cite! 'ringoid-as-ring-is-ring v)
    (dk-cite! 'hom-ring-id rv)
    (dk-have! (list '== crv cv)
      (lambda () (slot 'CARR) (mac 'RINGOID-AS-RING) (nth-r) (slot 'CARR) (qrfl)))
    (mac 'IS-HOM-RINGOID-def)
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond ((dk-asm? g) (ass))
                ((dk-head-is? g 'IN) (dk-cite! 'id-fun-type cv) (ass))
                ((dk-head-is? g 'IS-HOM-RING) (subst (list '== cv crv)) (ass))
                (#t
                 (let* ((landed (dk-peel!))
                        (x (cadr (car landed))))
                   (hml-sub-elt! x (list 'IDL v) cv)
                   (subst (dk-cite! 'id-fun-apply cv x))
                   (ass)))))))
    (hml-done! 'hom-ringoid-id)))

(define (hml-prove-ringoid-compose!)
  (sp (make-wff '(FORALL a (FORALL b (FORALL c (FORALL f (FORALL g
         (IMPLIES (IS-HOM-RINGOID a b f) (IMPLIES (IS-HOM-RINGOID b c g)
           (IS-HOM-RINGOID a c (COMPOSE g f)))))))))))
  (dk-peel!)
  (let* ((gl (dk-goal)) (va (cadr gl)) (vc (caddr gl)) (gf (cadddr gl))
         (vg (cadr gf)) (vf (caddr gf))
         (hf (dk-pick (lambda (x) (and (dk-head-is? x 'IS-HOM-RINGOID) (equal? (cadddr x) vf))) "the f hom"))
         (vb (caddr hf))
         (hg (hml-ctx (list 'IS-HOM-RINGOID vb vc vg) "the g hom"))
         (ca (list 'CARR va)) (cb (list 'CARR vb)) (cc (list 'CARR vc))
         (fconj (hml-conjuncts (caddr (hml-inst 'IS-HOM-RINGOID-def va vb vf))))
         (gconj (hml-conjuncts (caddr (hml-inst 'IS-HOM-RINGOID-def vb vc vg)))))
    (mac-h 'IS-HOM-RINGOID-def hf)
    (mac-h 'IS-HOM-RINGOID-def hg)
    (dk-split-all!)
    (hml-land-typings! 'RINGOID va)
    (dk-cite! 'hom-ring-compose (list 'RINGOID-AS-RING va) (list 'RINGOID-AS-RING vb)
              (list 'RINGOID-AS-RING vc) vf vg)
    (dk-have! (list 'AND (list 'IN vf (list 'FUN ca cb)) (list 'IN vg (list 'FUN cb cc))))
    (let ((cu (dk-cite! 'compose-apply ca cb cc vg vf))
          (uf (hml-ctx (list-ref fconj (- (length fconj) 1)) "f ideal clause"))
          (ug (hml-ctx (list-ref gconj (- (length gconj) 1)) "g ideal clause")))
      (mac 'IS-HOM-RINGOID-def)
      (dk-conj-close!
        (lambda ()
          (let ((g (dk-goal)))
            (cond ((dk-asm? g) (ass))
                  ((dk-head-is? g 'IN) (dk-cite! 'compose-type ca cb cc vg vf) (ass))
                  (#t
                   (let* ((landed (dk-peel!))
                          (x (cadr (car landed))))
                     (hml-sub-elt! x (list 'IDL va) ca)
                     (subst (dk-apply! cu x))
                     (dk-apply! uf x)
                     (dk-apply! ug (list vf x))
                     (ass))))))))
    (hml-done! 'hom-ringoid-compose)))

(for-each (lambda (name)
            (hml-prove-member-iff! name)
            (hml-prove-top-id! name)
            (hml-prove-top-compose! name)
            (hml-prove-in-set! name))
          '(TOP-SPACE METRIZABLE-TOP-SPACE))
(hml-prove-member-iff! 'RINGOID)
(hml-prove-ringoid-id!)
(hml-prove-ringoid-compose!)
(hml-prove-in-set! 'RINGOID)
