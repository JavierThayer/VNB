;;; rake-ip-normed-ag.scm -- rake batch 5b E: the induced norm of a complex
;;; inner product makes the additive group of its vectors a NORMED ABELIAN
;;; GROUP.  The support proved here is
;;;
;;;   ip-normed-ag-is-normed-ag   structure-library/complex-inner-product.scm:311
;;;
;;; and with it six bricks that the tree did not have, each stated for its own
;;; sake:
;;;
;;;   ip-norm-unfold        (IP-NORM v x) == SQRT(ip(v)(x,x)) as a citable
;;;                         equation -- a def-functoid installs a macete and no
;;;                         theorem, so `mac-h' cannot open IP-NORM in a
;;;                         HYPOTHESIS by its own name (CLAUDE.md, the functoid
;;;                         trap).  One line; everything below uses it.
;;;   cips-vneg-type        vneg(v)(x) is a vector
;;;   cips-vadd-vneg        x + (-x) = 0
;;;   cips-ip-zero-left     <0, z> = 0
;;;   cips-ip-neg-left      <-x, z> = -<x,z>
;;;   cips-ip-neg-self      <-x,-x> = <x,x>          THE missing clause
;;;
;;; WHY THE ROUTE IS SHORTER THAN THE ONE WRITTEN DOWN.  rake-norm-metrics.scm's
;;; closing block (B) routes the inverse-invariance clause through conjugate
;;; symmetry: <-x,z> = -<x,z> in the FIRST argument, then conjugation to move it
;;; to the second.  No conjugation is needed.  Additivity in the SECOND argument
;;; is already PROVEN (cips-ip-add-right, complex-inner-product-laws.scm), so
;;;
;;;     <-x, x + (-x)> = <-x,x> + <-x,-x>
;;;
;;; with the left side <-x, 0> = 0 (cips-ip-zero-right) and <-x,x> = -<x,x>
;;; (cips-ip-neg-left) gives <-x,-x> = <x,x> by one `crs'.  The whole file
;;; touches `conjugate' nowhere.
;;;
;;; THE PACKAGING.  IS-NORMED-AG of the LIST tuple unfolds to ten conjuncts:
;;; the length, five slot typings, the four abelian-group properties and
;;; is-group-norm.  Nine of the ten are LITERAL conjuncts of the
;;; IS-COMPLEX-INNER-PRODUCT-SPACE unfold once the slots are read off the LIST
;;; (`slot' + `nth-r'), and the tenth -- is-group-norm for x |-> SQRT(<x,x>) --
;;; has four clauses: nonnegativity (sqrt-nonneg), definiteness (sqrt-sq and
;;; sqrt-char with cips-ip-zero-vector), inverse-invariance (cips-ip-neg-self,
;;; above) and subadditivity, which IS `cips-minkowski', proven in
;;; theorem-library/inner-product-inequalities.scm.
;;;
;;; Since `mac-h' REPLACES the assumption it unfolds, and every cips-* projection
;;; is guarded on IS-COMPLEX-INNER-PRODUCT-SPACE, the unfold never happens in the
;;; main branch: `r6e-shape!' lands the nine conjuncts as ONE conjunction proved
;;; on a `have!' lane and splits that, leaving the predicate itself intact.
;;;
;;; LOAD WINDOW [393, end).  lo is forced by `cips-minkowski'
;;; (theorem-library/inner-product-inequalities, position 392); then
;;; complex-inner-product-laws (391, cips-ip-add-right / cips-ip-zero-right),
;;; sqrt-defined (388, sqrt-nonneg / sqrt-sq / sqrt-char), fun-apply-type-proof
;;; (162, fun-apply-type-c), equality-basics (148), and the structure files
;;; complex-inner-product (69, the cips-* projections and IP-NORM / IP-NORMED-AG),
;;; normed-ag (59, IS-NORMED-AG) and operation-properties (14, is-group-norm /
;;; has-inverses).  Nothing proven cites ip-normed-ag-is-normed-ag, so nothing
;;; forces hi.
;;;
;;; TWO DRIVER FINDINGS, both paid for in runs.
;;; * PEEL AND TYPE FIRST, THEN BETA, at the level of the DRIVE LOOP.  The loop
;;;   first beta-reduced the focus goal and only then decided whether to peel it.
;;;   On the is-group-norm body that fires `lam-b' under the still-unpeeled
;;;   `forall u in carr', so the reduction owes (IN (vneg(v))(u), vec(v)) at a
;;;   node where `u' is not yet typed, and the citation that would close it does
;;;   not detach.  The loop now peels FORALL/IMPLIES/AND/IFF first and betas only
;;;   at a leaf whose binders are all landed.
;;; * `rfl' NEEDS THE TERM TYPED, since the LUTINS rule.  The inverse-invariance
;;;   clause ends at SQRT(<u,u>) = SQRT(<u,u>) and `rfl' refused it with
;;;   "goal is not (= a a)" printing two identical sides -- the message means
;;;   "this term is not certified defined".  One `sqrt-nonneg' citation above the
;;;   `rfl' closes it.
;;;
;;; Dependencies: interactive, proof-debt, driver-kit (dk-peel!/dk-have!/...).

;;; ---- file-local driver (the `r6e-' prefix) --------------------------

;;; The nine conjuncts of the IS-COMPLEX-INNER-PRODUCT-SPACE unfold that the
;;; packaging needs, landed WITHOUT destroying the predicate: they are proved
;;; as one conjunction on a `have!' lane (where the unfold may be destructive)
;;; and split in the main branch.
(define r6e-shape-claim
  '(AND (IN (VEC v) SET)
   (AND (IN (VADD v) (FUN (CARTESIAN (VEC v) (VEC v)) (VEC v)))
   (AND (IN (VZERO v) (VEC v))
   (AND (IN (VNEG v) (FUN (VEC v) (VEC v)))
   (AND (is-associative (VADD v) (VEC v))
   (AND (is-identity (VADD v) (VZERO v) (VEC v))
   (AND (has-inverses (VADD v) (VZERO v) (VNEG v) (VEC v))
        (is-commutative (VADD v) (VEC v))))))))))

(define (r6e-unfold-cips!)
  (dk-split-all!
   (dk-landed* (lambda () (mac-h 'IS-COMPLEX-INNER-PRODUCT-SPACE
                                 '(IS-COMPLEX-INNER-PRODUCT-SPACE v))))))

(define (r6e-shape!)
  (dk-split! (dk-landed-1
              (lambda ()
                (dk-have! r6e-shape-claim
                          (lambda ()
                            (r6e-unfold-cips!)
                            (dk-conj-close! (lambda () (ass)))))))))

;;; =====================================================================
;;; (1) ip-norm-unfold -- the functoid's defining equation, citable
;;; =====================================================================

(sp (make-wff '(FORALL v (FORALL x
     (== (IP-NORM v x) (SQRT ((IP v) x x)))))))
(di)
(mac 'IP-NORM)
(qrfl)
(qed 'ip-norm-unfold)
(topic! 'ip-norm-unfold 'plumbing)
(gloss! 'ip-norm-unfold
  "The induced norm IP-NORM(v,x) is SQRT(ip(v)(x,x)), as a citable equation.
   Cite it with mac-h to open an induced norm in a HYPOTHESIS -- a def-functoid
   installs only a rewrite macete, so the functoid's own name cannot.")

;;; =====================================================================
;;; (2) cips-vneg-type -- negation closes on the vectors
;;; =====================================================================

(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
     (FORALL x_ (IMPLIES (IN x_ (VEC v))
       (IN ((VNEG v) x_) (VEC v))))))))
(dk-peel!)
(dk-have! '(IN (VNEG v) (FUN (VEC v) (VEC v)))
          (lambda () (r6e-unfold-cips!) (ass)))
(fact 'fun-apply-type-c '(VNEG v) '(VEC v) '(VEC v) 'x_)
(ass)
(qed 'cips-vneg-type)
(topic! 'cips-vneg-type 'algebra)

;;; =====================================================================
;;; (3) cips-vadd-vneg -- x + (-x) = 0
;;; =====================================================================

(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
     (FORALL x_ (IMPLIES (IN x_ (VEC v))
       (= ((VADD v) x_ ((VNEG v) x_)) (VZERO v))))))))
(dk-peel!)
(dk-have! '(has-inverses (VADD v) (VZERO v) (VNEG v) (VEC v))
          (lambda () (r6e-unfold-cips!) (ass)))
(dk-split-all!
 (dk-landed* (lambda () (mac-h 'has-inverses
                               '(has-inverses (VADD v) (VZERO v) (VNEG v) (VEC v))))))
(dk-split! (dk-apply! (dk-pick (dk-head? 'FORALL) "the inverse universal") 'x_))
(ass)
(qed 'cips-vadd-vneg)
(topic! 'cips-vadd-vneg 'algebra)

;;; =====================================================================
;;; (4) cips-ip-zero-left -- <0, z> = 0
;;; =====================================================================
;;; The mirror of cips-ip-zero-right (complex-inner-product-laws.scm), in the
;;; FIRST argument and off cips-ip-add-left: <0,z> + <0,z> = <0+0, z> = <0,z>.

(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
     (FORALL z_ (IMPLIES (IN z_ (VEC v))
       (= ((IP v) (VZERO v) z_) 0)))))))
(dk-peel!)
(fact 'cips-vzero-in 'v)
(fact 'cips-ip-type 'v '(VZERO v) 'z_)
(fact 'cips-vadd-vzero 'v '(VZERO v))
(fact 'cips-ip-add-left 'v '(VZERO v) '(VZERO v) 'z_)
(have! '(= (+ ((IP v) (VZERO v) z_) ((IP v) (VZERO v) z_)) ((IP v) (VZERO v) z_))
       (lambda ()
         (subst '(= (+ ((IP v) (VZERO v) z_) ((IP v) (VZERO v) z_))
                    ((IP v) ((VADD v) (VZERO v) (VZERO v)) z_)))
         (subst '(= ((VADD v) (VZERO v) (VZERO v)) (VZERO v)))
         (crs)))
(have! '(= ((IP v) (VZERO v) z_)
           (+ (+ ((IP v) (VZERO v) z_) ((IP v) (VZERO v) z_))
              (- ((IP v) (VZERO v) z_))))
       (lambda () (crs)))
(subst '(= ((IP v) (VZERO v) z_)
           (+ (+ ((IP v) (VZERO v) z_) ((IP v) (VZERO v) z_))
              (- ((IP v) (VZERO v) z_)))))
(subst '(= (+ ((IP v) (VZERO v) z_) ((IP v) (VZERO v) z_)) ((IP v) (VZERO v) z_)))
(crs)
(qed 'cips-ip-zero-left)
(topic! 'cips-ip-zero-left 'algebra)
(alias! 'cips-ip-zero-left "the inner product of the zero vector vanishes")

;;; =====================================================================
;;; (5) cips-ip-neg-left -- <-x, z> = -<x,z>
;;; =====================================================================

(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
     (FORALL x_ (IMPLIES (IN x_ (VEC v))
     (FORALL z_ (IMPLIES (IN z_ (VEC v))
       (= ((IP v) ((VNEG v) x_) z_) (- ((IP v) x_ z_)))))))))))
(dk-peel!)
(fact 'cips-vneg-type 'v 'x_)
(fact 'cips-ip-type 'v 'x_ 'z_)
(fact 'cips-ip-type 'v '((VNEG v) x_) 'z_)
(fact 'cips-vadd-vneg 'v 'x_)
(fact 'cips-ip-add-left 'v 'x_ '((VNEG v) x_) 'z_)
(fact 'cips-ip-zero-left 'v 'z_)
(have! '(= (+ ((IP v) x_ z_) ((IP v) ((VNEG v) x_) z_)) 0)
       (lambda ()
         (subst '(= (+ ((IP v) x_ z_) ((IP v) ((VNEG v) x_) z_))
                    ((IP v) ((VADD v) x_ ((VNEG v) x_)) z_)))
         (subst '(= ((VADD v) x_ ((VNEG v) x_)) (VZERO v)))
         (ass)))
(have! '(= ((IP v) ((VNEG v) x_) z_)
           (+ (+ ((IP v) x_ z_) ((IP v) ((VNEG v) x_) z_)) (- ((IP v) x_ z_))))
       (lambda () (crs)))
(subst '(= ((IP v) ((VNEG v) x_) z_)
           (+ (+ ((IP v) x_ z_) ((IP v) ((VNEG v) x_) z_)) (- ((IP v) x_ z_)))))
(subst '(= (+ ((IP v) x_ z_) ((IP v) ((VNEG v) x_) z_)) 0))
(crs)
(qed 'cips-ip-neg-left)
(topic! 'cips-ip-neg-left 'algebra)
(alias! 'cips-ip-neg-left "the inner product is additive-inverting in its first argument")

;;; =====================================================================
;;; (6) cips-ip-neg-self -- <-x,-x> = <x,x>
;;; =====================================================================
;;; Additivity in the SECOND argument at (x, -x), the zero law, and (5).

(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
     (FORALL x_ (IMPLIES (IN x_ (VEC v))
       (= ((IP v) ((VNEG v) x_) ((VNEG v) x_)) ((IP v) x_ x_))))))))
(dk-peel!)
(fact 'cips-vneg-type 'v 'x_)
(fact 'cips-ip-type 'v 'x_ 'x_)
(fact 'cips-ip-type 'v '((VNEG v) x_) 'x_)
(fact 'cips-ip-type 'v '((VNEG v) x_) '((VNEG v) x_))
(fact 'cips-vadd-vneg 'v 'x_)
(fact 'cips-ip-add-right 'v '((VNEG v) x_) 'x_ '((VNEG v) x_))
(fact 'cips-ip-zero-right 'v '((VNEG v) x_))
(fact 'cips-ip-neg-left 'v 'x_ 'x_)
(have! '(= (+ ((IP v) ((VNEG v) x_) x_) ((IP v) ((VNEG v) x_) ((VNEG v) x_))) 0)
       (lambda ()
         (subst '(= (+ ((IP v) ((VNEG v) x_) x_) ((IP v) ((VNEG v) x_) ((VNEG v) x_)))
                    ((IP v) ((VNEG v) x_) ((VADD v) x_ ((VNEG v) x_)))))
         (subst '(= ((VADD v) x_ ((VNEG v) x_)) (VZERO v)))
         (ass)))
(have! '(= ((IP v) ((VNEG v) x_) ((VNEG v) x_))
           (+ (+ ((IP v) ((VNEG v) x_) x_) ((IP v) ((VNEG v) x_) ((VNEG v) x_)))
              (- ((IP v) ((VNEG v) x_) x_))))
       (lambda () (crs)))
(subst '(= ((IP v) ((VNEG v) x_) ((VNEG v) x_))
           (+ (+ ((IP v) ((VNEG v) x_) x_) ((IP v) ((VNEG v) x_) ((VNEG v) x_)))
              (- ((IP v) ((VNEG v) x_) x_)))))
(subst '(= (+ ((IP v) ((VNEG v) x_) x_) ((IP v) ((VNEG v) x_) ((VNEG v) x_))) 0))
(subst '(= ((IP v) ((VNEG v) x_) x_) (- ((IP v) x_ x_))))
(crs)
(qed 'cips-ip-neg-self)
(topic! 'cips-ip-neg-self 'algebra)
(alias! 'cips-ip-neg-self "the inner product is invariant under negating both arguments")

;;; =====================================================================
;;; (7) ip-normed-ag-is-normed-ag -- the packaging
;;; =====================================================================
;;; structure-library/complex-inner-product.scm:311, statement unchanged.

(define r6e-v 'v)                       ; the eigenvariable, read off the context

(define (r6e-ip a b) (list (list 'IP r6e-v) a b))
(define (r6e-nrm a)  (list 'IP-NORM r6e-v a))

(define (r6e-open)
  (filter (lambda (s) (and (not (sequent-node-grounded? s))
                           (null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))

;;; beta to a fixpoint, guarded on progress (`lam-b' only warns with no redex).
;;; Every argument is typed by the guarded universal peeled above it, so no
;;; beta here owes a membership leaf (CLAUDE.md: PEEL AND TYPE FIRST).
(define (r6e-beta!)
  (let loop ((n 0))
    (let ((before (dk-goal)))
      (if (< n 12)
          (begin (quietly (lambda () (lam-b)))
                 (if (not (equal? before (dk-goal))) (loop (+ n 1))))))))

;;; <u,u> is a nonnegative real, and so is its square root.
(define (r6e-diag-facts! u)
  (fact 'cips-ip-self-real r6e-v u)
  (fact 'cips-ip-self-nonneg r6e-v u)
  (dk-have! (list 'AND (list 'IN (r6e-ip u u) 'RR) (list '<= 0 (r6e-ip u u)))))

(define (r6e-sqrt-facts! u)
  (r6e-diag-facts! u)
  (fact 'sqrt-nonneg (r6e-ip u u))
  (dk-split! (list 'AND (list 'IN (list 'SQRT (r6e-ip u u)) 'RR)
                        (list '<= 0 (list 'SQRT (r6e-ip u u))))))

;;; ||u|| is a real / is nonnegative -- the same two facts, through the unfold.
(define (r6e-norm-real! u)   (r6e-sqrt-facts! u) (mac 'IP-NORM) (ass))
(define (r6e-norm-nonneg! u) (r6e-sqrt-facts! u) (mac 'IP-NORM) (ass))

;;; ||-u|| = ||u|| -- cips-ip-neg-self under the square root.
(define (r6e-neg! u)
  (fact 'cips-vneg-type r6e-v u)
  (fact 'cips-ip-neg-self r6e-v u)
  ;; the closing `rfl' certifies SQRT(<u,u>) off this typing: under the LUTINS
  ;; rule a bare `rfl' on an uncertified term answers "goal is not (= a a)"
  ;; with two identical sides.
  (r6e-sqrt-facts! u)
  (mac 'IP-NORM)
  (subst (list '= (r6e-ip (list (list 'VNEG r6e-v) u) (list (list 'VNEG r6e-v) u))
                  (r6e-ip u u)))
  (rfl))

;;; ||u|| = 0  =>  u = 0.  ||u||*||u|| = <u,u> by sqrt-sq, so <u,u> = 0.
(define (r6e-definite-forward! u)
  ;; the vanishing norm is a HYPOTHESIS, so its redex is on that side and the
  ;; goal-side beta cannot reach it.
  (let ((red (find-first (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (caddr f) 0)
                                          (pair? (cadr f)) (pair? (car (cadr f)))
                                          (eq? (car (car (cadr f))) 'VNB-LAMBDA)))
                         (dk-asms))))
    (if red (lam-b-h red)))
  (r6e-diag-facts! u)
  (dk-have! (list '= (r6e-ip u u) 0)
    (lambda ()
      (fact 'sqrt-sq (r6e-ip u u))
      (dk-have! (list '== (list 'SQRT (r6e-ip u u)) (r6e-nrm u))
                (lambda () (mac 'IP-NORM) (qrfl)))
      (subst (list '= (r6e-ip u u)
                   (list '* (list 'SQRT (r6e-ip u u)) (list 'SQRT (r6e-ip u u)))))
      (subst (list '== (list 'SQRT (r6e-ip u u)) (r6e-nrm u)))
      (subst (list '= (r6e-nrm u) 0))
      (crs)))
  (fact 'cips-ip-zero-vector r6e-v u)
  (ass))

;;; u = 0  =>  ||u|| = 0.  <0,0> = 0 (cips-ip-zero-left) and SQRT(0) = 0.
(define (r6e-definite-backward! u)
  (fact 'cips-vzero-in r6e-v)
  (fact 'cips-ip-zero-left r6e-v (list 'VZERO r6e-v))
  (mac 'IP-NORM)
  (subst (list '= u (list 'VZERO r6e-v)))
  (subst (list '= (r6e-ip (list 'VZERO r6e-v) (list 'VZERO r6e-v)) 0))
  (dk-have! '(AND (IN 0 RR) (<= 0 0)) (lambda () (arith)))
  (dk-have! '(= (* 0 0) 0) (lambda () (arith)))
  (fact 'sqrt-char 0 0)
  (ass))

;;; ||u + w|| <= ||u|| + ||w|| -- cips-minkowski, verbatim.
(define (r6e-minkowski! u w)
  (fact 'cips-minkowski r6e-v u w)
  (ass))

;;; The membership a `lam-b' owes when the norm is applied to a CONSTRUCTED
;;; vector: the two clauses that do that are inverse-invariance (at -u) and
;;; subadditivity (at u + w), and neither argument is typed by the universal
;;; the driver peeled.
(define (r6e-vec-type! t)
  (cond ((and (pair? t) (pair? (car t)) (eq? (car (car t)) 'VNEG))
         (fact 'cips-vneg-type r6e-v (cadr t)) (ass))
        ((and (pair? t) (pair? (car t)) (eq? (car (car t)) 'VADD))
         (fact 'cips-vadd-type r6e-v (cadr t) (caddr t)) (ass))
        (#t (ass))))

(define (r6e-close!)
  (let ((g (dk-goal)))
    (cond
     ((member g (dk-asms)) (ass))
     ((and (eq? (car g) 'IN) (equal? (caddr g) (list 'VEC r6e-v)))
      (r6e-vec-type! (cadr g)))
     ((and (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl))
     ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
      (len-r) (arith))
     ((and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
      (lam-t))
     ((and (eq? (car g) 'IN) (equal? (caddr g) 'RR))
      (r6e-norm-real! (caddr (cadr g))))
     ((eq? (car g) 'is-group-norm) (mac 'is-group-norm))
     ((and (eq? (car g) '<=) (equal? (cadr g) 0))
      (r6e-norm-nonneg! (caddr (caddr g))))
     ((eq? (car g) '<=)
      (r6e-minkowski! (caddr (cadr (caddr g))) (caddr (caddr (caddr g)))))
     ((and (eq? (car g) '=) (pair? (caddr g)) (eq? (car (caddr g)) 'VZERO))
      (r6e-definite-forward! (cadr g)))
     ((and (eq? (car g) '=) (equal? (caddr g) 0))
      (r6e-definite-backward! (caddr (cadr g))))
     ((eq? (car g) '=) (r6e-neg! (caddr (caddr g))))
     (#t (error "r6e-close!: unexpected leaf" (expression->string g))))))

;;; Focus every open leaf, beta it, peel it or close it.  Guarded on PROGRESS,
;;; as r5r-drive! is: a leaf that neither moves nor closes would otherwise be
;;; re-focused for ever.
(define (r6e-drive!)
  (let loop ((fuel 400) (prev #f))
    (let ((s (find-first (lambda (s) #t) (r6e-open))))
      (cond ((not s) #t)
            ((<= fuel 0) (error "r6e-drive!: out of fuel"))
            (#t
             (dk-focus! s)
             (let ((mark (cons s (dk-goal))))
               (if (equal? mark prev)
                   (error "r6e-drive!: no progress on" (expression->string (dk-goal))))
               (if (memq (car (dk-goal)) '(FORALL IMPLIES AND IFF))
                   (di)                 ; PEEL AND TYPE FIRST, THEN BETA: a
                                        ; `lam-b' under an unpeeled binder owes
                                        ; the domain membership at a node where
                                        ; the variable is not yet typed.
                   (begin (r6e-beta!) (r6e-close!)))
               (loop (- fuel 1) mark)))))))

(sp (make-wff '(FORALL v (IMPLIES (IS-COMPLEX-INNER-PRODUCT-SPACE v)
     (IS-NORMED-AG (IP-NORMED-AG v))))))
(dk-peel!)
(set! r6e-v (cadr (dk-pick (dk-head? 'IS-COMPLEX-INNER-PRODUCT-SPACE)
                           "the inner product space")))
(r6e-shape!)
(mac 'IP-NORMED-AG)
(mac 'IS-NORMED-AG)
(slot 'CARR)
(slot 'OPR)
(slot 'IDEN)
(slot 'INV)
(slot 'NRM)
(let loop ((n 0))
  (let ((before (dk-goal)))
    (quietly (lambda () (nth-r)))
    (if (and (< n 12) (not (equal? before (dk-goal)))) (loop (+ n 1)))))
(r6e-drive!)
(qed 'ip-normed-ag-is-normed-ag)
(topic! 'ip-normed-ag-is-normed-ag 'analysis)
(gloss! 'ip-normed-ag-is-normed-ag
  "For every complex inner product space v, the additive group of its vectors,
   carrying the induced norm ||x|| = SQRT(<x,x>), is a normed abelian group.")
(alias! 'ip-normed-ag-is-normed-ag
        "the induced norm of an inner product is a group norm")
