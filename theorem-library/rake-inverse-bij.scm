;;; theorem-library/rake-inverse-bij.scm -- rake batch N (2026-09-17), part 1 of 2.
;;; ---------------------------------------------------------------------------
;;; NOTE, 2026-09-20 (batch 9-B).  This file was written while cardinality was
;;; AXIOMATISED under the name CARD and the defined constant was its companion
;;; CARD-STAR.  On 2026-09-20 the user made the swap: CARD is the DEFINED
;;; cardinal (structure-library/cardinality.scm), the eight `primitive' axioms
;;; about it are gone, and every proof below now speaks of CARD.  The prose in
;;; this header that contrasts "the axiomatised CARD" with "the defined
;;; cardinal" is HISTORY; the surgery is docs/card-defined-2026-09-20.md.
;;; ---------------------------------------------------------------------------
;;;
;;; THE FOUR INVERSE-BIJ AXIOMS OF structure-library/bijection.scm, PROVEN, plus
;;; fin-enum-is-bijection.  All five are `modulo 0'.
;;;
;;;   inverse-bij-right        phi(INVERSE-BIJ(phi,X,Y)(y)) = y      for y in Y
;;;   inverse-bij-left         INVERSE-BIJ(phi,X,Y)(phi(x)) = x      for x in X
;;;   inverse-bij-in-fun       INVERSE-BIJ(phi,X,Y) in FUN(Y,X)
;;;   inverse-bij-is-bijection INVERSE-BIJ(phi,X,Y) in BIJECTION(Y,X)
;;;   fin-enum-is-bijection    FIN-ENUM(S) in BIJECTION(OS(CARD S), S), S finite
;;;
;;; All four INVERSE-BIJ statements were `theory-add-axiom!' with NO warrant --
;;; i.e. `trust: none' to any citer -- which is why the permutation-invariance
;;; development (part 2, theorem-library/rake-finsum-welldef.scm) could not
;;; simply cite them.  Nothing in the tree cited them, so retiring them costs no
;;; call site.
;;;
;;; THE ARGUMENT, for all four.  INVERSE-BIJ(phi,X,Y) is
;;;     VNB-LAMBDA y_ in Y. CHOICE {x_ in X : phi(x_) = y_},
;;; so each is one `mac INVERSE-BIJ' + `lam-b' + the choice axiom on a SEP that
;;; the bijection's own surjectivity (right, in-fun) or the given point (left)
;;; inhabits.  `inverse-bij-in-fun' is the one with a hidden obligation: `lam-t'
;;; owes the SETHOOD of the lambda's domain Y, and the statement is unguarded --
;;; rightly so, since a bijection X -> Y forces both to be sets.  X is a set by
;;; `fun-domain-in-set' and Y is covered by IMAGE(phi,X), a set by replacement.
;;;
;;; CITATIONS and their load positions (0-based over load.scm's quoted files):
;;;   theory.scm (primitive): choice-axiom, membership-implies-sethood, subset-def
;;;   structure-library/bijection (81, definitional): bijection-membership-iff
;;;   structure-library/cardinality (82, primitive): card-finite-bij
;;;   structure-library/injection (83, primitive/asserted): image-set,
;;;     image-membership-iff
;;;   structure-library/finsum (93): the FIN-ENUM functoid unfold
;;;   theorem-library/fun-apply-type-proof (163): fun-apply-type-c
;;;   theorem-library/subset-lemmas (193): subclass-of-set-is-set
;;;   theorem-library/rake-analysis2 (194): fun-domain-in-set    -- the LATEST
;;;
;;; LOAD WINDOW [195, 201).  lo = after rake-analysis2 (194).  hi is forced by
;;; theorem-library/finsum-type-proof (201), which cites fin-enum-is-bijection:
;;; that name is proven today ONLY inside theorem-library/finsum-insert (155), and
;;; finsum-insert has to MOVE past part 2 (it cites finsum-well-defined).  So the
;;; slot immediately after structure-library/subtype-laws (199) / op-typing (200).
;;;
;;; FOR THE INTEGRATOR: retire the four axioms at structure-library/bijection.scm
;;; :84 (inverse-bij-in-fun), :93 (inverse-bij-left), :104 (inverse-bij-right),
;;; :113 (inverse-bij-is-bijection); delete the fin-enum-is-bijection block at
;;; theorem-library/finsum-insert.scm:174-188 (that file moves BELOW part 2, so
;;; its copy would be a duplicate install AND would come too late for
;;; finsum-type-proof, which cites the name).
;;;
;;; Helper prefix: rkn-.

(define (rkn-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkn: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkn: proof not complete" name))))

(define (rkn-head? f h) (and (pair? f) (eq? (car f) h)))

;; close every leaf a branching tactic opened, by `ass'
(define (rkn-close-opened! thunk)
  (for-each (lambda (l)
              (dk-focus! l)
              (let ((g (dk-goal)))
                (if (and (rkn-head? g '=) (equal? (cadr g) (caddr g))) (rfl) (ass))))
            (dk-opened thunk)))

;; unfold (IN PH (BIJECTION D C)) in the context and split; return the three
;; conjuncts as (fun injective surjective).
(define (rkn-open-bijection! f)
  (let ((atoms (dk-split-all! (dk-landed* (lambda () (mac-h 'bijection-membership-iff f))))))
    (list (dk-pick (lambda (a) (rkn-head? a 'IN)) "the FUN typing")
          (dk-pick (lambda (a) (and (rkn-head? a 'FORALL)
                                    (rkn-head? (caddr a) 'IMPLIES)
                                    (rkn-head? (caddr (caddr a)) 'FORALL)))
                   "injectivity")
          (dk-pick (lambda (a) (and (rkn-head? a 'FORALL)
                                    (rkn-head? (caddr a) 'IMPLIES)
                                    (rkn-head? (caddr (caddr a)) 'FORSOME)))
                   "surjectivity"))))

;;; ===========================================================================
;;; 1.  INVERSE-BIJ:  the four axioms of structure-library/bijection.scm.
;;;
;;;   INVERSE-BIJ(phi,X,Y) = VNB-LAMBDA y_ in Y. CHOICE {x_ in X : phi(x_) = y_}
;;;
;;; Each is one `mac INVERSE-BIJ' + `lam-b' + the choice axiom on a SEP the
;;; bijection's own surjectivity (resp. the given point) inhabits.
;;; ===========================================================================

;;; inverse-bij-right:  phi(INVERSE-BIJ(phi,dm,cod)(y)) = y   for y in cod.
(sp (make-wff
     '(FORALL dm (FORALL cod (FORALL phi
         (IMPLIES (IN phi (BIJECTION dm cod))
                  (FORALL y
                    (IMPLIES (IN y cod)
                             (= (phi ((INVERSE-BIJ phi dm cod) y)) y)))))))))
(dk-peel!)
(mac 'INVERSE-BIJ)
(lam-b)
(let* ((sep   (cadr (cadr (cadr (dk-goal)))))          ; {x_ in dm : phi(x_) = y}
       (parts (rkn-open-bijection! '(IN phi (BIJECTION dm cod))))
       (z     (dk-skolem! (dk-apply! (caddr parts) 'y))))
  (have! (list 'FORSOME 'q_ (list 'IN 'q_ sep))
         (lambda () (ew z) (rkn-close-opened! sep-mi)))
  (sep-me (dk-fact! 'choice-axiom sep))
  (ass))
(rkn-check! 'inverse-bij-right)
(qed 'inverse-bij-right)
(gloss! 'inverse-bij-right
  "phi(INVERSE-BIJ(phi,X,Y)(y)) = y for y in Y.  The inverse picks, by CHOICE, a
   member of {x in X : phi(x) = y}; surjectivity makes that set inhabited, so the
   choice axiom applies and its defining property is the equation wanted.")
(topic! 'inverse-bij-right 'plumbing)

;;; inverse-bij-left:  INVERSE-BIJ(phi,dm,cod)(phi(x)) = x   for x in dm.
(sp (make-wff
     '(FORALL dm (FORALL cod (FORALL phi
         (IMPLIES (IN phi (BIJECTION dm cod))
                  (FORALL x
                    (IMPLIES (IN x dm)
                             (= ((INVERSE-BIJ phi dm cod) (phi x)) x)))))))))
(dk-peel!)
(let ((parts (rkn-open-bijection! '(IN phi (BIJECTION dm cod)))))
  (dk-fact! 'fun-apply-type-c 'phi 'dm 'cod 'x)         ; (IN (phi x) cod), for lam-b
  (mac 'INVERSE-BIJ)
  (lam-b)
  (let ((sep (cadr (cadr (dk-goal)))))                  ; {x_ in dm : phi(x_) = phi(x)}
    (have! (list 'FORSOME 'q_ (list 'IN 'q_ sep))
           (lambda () (ew 'x) (rkn-close-opened! (lambda () (sep-mi)))))
    (sep-me (dk-fact! 'choice-axiom sep))
    (dk-apply! (cadr parts) (list 'CHOICE sep) 'x)
    (ass)))
(rkn-check! 'inverse-bij-left)
(qed 'inverse-bij-left)
(gloss! 'inverse-bij-left
  "INVERSE-BIJ(phi,X,Y)(phi(x)) = x for x in X.  The chosen pre-image of phi(x)
   lies in {x_ in X : phi(x_) = phi(x)}, which x itself inhabits, so injectivity
   identifies the two.")
(topic! 'inverse-bij-left 'plumbing)

;;; inverse-bij-in-fun:  INVERSE-BIJ(phi,X,Y) in FUN(Y,X).
;;; `lam-t' owes the SETHOOD of the lambda's domain Y, and the statement is
;;; unguarded -- rightly so: a bijection X -> Y forces BOTH to be sets.  X is a
;;; set by fun-domain-in-set, and Y is included in IMAGE(phi,X) by surjectivity,
;;; so replacement (image-set) plus subclass-of-set-is-set delivers it.
(sp (make-wff
     '(FORALL X (FORALL Y (FORALL phi
         (IMPLIES (IN phi (BIJECTION X Y))
                  (IN (INVERSE-BIJ phi X Y) (FUN Y X))))))))
(dk-peel!)
(define rkn-ibf-parts (rkn-open-bijection! '(IN phi (BIJECTION x y))))
(define rkn-ibf-surj (caddr rkn-ibf-parts))
(fact 'fun-domain-in-set 'x 'y 'phi)                    ; (IN x SET)
(fact 'image-set 'phi 'x)                               ; (IN (IMAGE phi x) SET)
(have! '(SUBSET y (IMAGE phi x))
  (lambda ()
    (mac 'subset-def)
    (let* ((mem (car (dk-peel!)))                       ; (IN w y)
           (w   (cadr mem))
           (z   (dk-skolem! (dk-apply! rkn-ibf-surj w))))
      (mac 'image-membership-iff)
      (ew z)
      (dk-conj-close! (lambda () (ass))))))
(fact 'subclass-of-set-is-set 'y '(IMAGE phi x))        ; (IN y SET)
(mac 'INVERSE-BIJ)
(dk-lam-t!)
(let* ((mem (car (dk-peel!)))                           ; (IN y_ y)
       (yv  (cadr mem))
       (sep (cadr (cadr (dk-goal))))                    ; {x_ in x : phi(x_) = y_}
       (z   (dk-skolem! (dk-apply! rkn-ibf-surj yv))))
  (have! (list 'FORSOME 'q_ (list 'IN 'q_ sep))
         (lambda () (ew z) (rkn-close-opened! sep-mi)))
  (sep-me (dk-fact! 'choice-axiom sep))
  (ass))
(rkn-check! 'inverse-bij-in-fun)
(qed 'inverse-bij-in-fun)
(gloss! 'inverse-bij-in-fun
  "The inverse of a bijection X -> Y is a function Y -> X.  The sethood of Y the
   lambda's typing rule owes is not a hypothesis and does not need to be: Y is
   covered by IMAGE(phi,X), a set by replacement.")
(topic! 'inverse-bij-in-fun 'plumbing)

;;; inverse-bij-is-bijection:  INVERSE-BIJ(phi,X,Y) in BIJECTION(Y,X).
;;; Injective because phi is a left inverse of it (inverse-bij-right); surjective
;;; because phi(w) is a pre-image of w (inverse-bij-left).
(sp (make-wff
     '(FORALL X (FORALL Y (FORALL phi
         (IMPLIES (IN phi (BIJECTION X Y))
                  (IN (INVERSE-BIJ phi X Y) (BIJECTION Y X))))))))
(dk-peel!)
(define rkn-ibb-inv '(INVERSE-BIJ phi x y))

(define (rkn-ibb-inj!)
  (let* ((landed (dk-peel!))
         (gl     (dk-goal))                             ; (= a b)
         (av     (cadr gl)) (bv (caddr gl))
         (ia     (list rkn-ibb-inv av)) (ib (list rkn-ibb-inv bv))
         (e3     (dk-pick (lambda (f) (equal? f (list '= ia ib))) "inv a = inv b"))
         (e1     (dk-fact! 'inverse-bij-right 'x 'y 'phi av))
         (e2     (dk-fact! 'inverse-bij-right 'x 'y 'phi bv)))
    (have! (list '= av (list 'phi ia))
           (lambda () (dk-fact! 'eq-sym (list 'phi ia) av) (ass)))
    (have! (list '= (list 'phi ia) (list 'phi ib))
           (lambda () (subst e3) (rfl)))
    (dk-fact! 'eq-trans av (list 'phi ia) (list 'phi ib))
    (dk-fact! 'eq-trans av (list 'phi ib) bv)
    (ass)))

(define (rkn-ibb-surj!)
  (let* ((mem (car (dk-peel!)))                         ; (IN w x)
         (w   (cadr mem)))
    (dk-fact! 'fun-apply-type-c 'phi 'x 'y w)           ; (IN (phi w) y)
    (dk-fact! 'inverse-bij-left 'x 'y 'phi w)           ; inv(phi w) = w
    (ew (list 'phi w))
    (dk-conj-close! (lambda () (ass)))))

;; the FUN projection in a HAVE! lane: `mac-h' REPLACES the assumption it
;; unfolds, and (IN phi (BIJECTION x y)) is what the two inverse facts detach
;; against.
(have! '(IN phi (FUN x y))
       (lambda () (rkn-open-bijection! '(IN phi (BIJECTION x y))) (ass)))
(fact 'inverse-bij-in-fun 'x 'y 'phi)
(mac 'bijection-membership-iff)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((rkn-head? g 'IN) (ass))
           ((rkn-head? (caddr (caddr g)) 'FORALL) (rkn-ibb-inj!))
           (#t (rkn-ibb-surj!))))))
(rkn-check! 'inverse-bij-is-bijection)
(qed 'inverse-bij-is-bijection)
(gloss! 'inverse-bij-is-bijection
  "The inverse of a bijection X -> Y is a bijection Y -> X.")
(topic! 'inverse-bij-is-bijection 'plumbing)

;;; fin-enum-is-bijection was proven HERE until 2026-09-20; it rests on card-finite-bij
;;; and so is now proven in theorem-library/rake-fin-enum.scm, which loads after
;;; theorem-library/card-laws.scm (batch 9-B, CARD := CARD-STAR).

;;; ------------------------------------------------------------------
;;; ord-segment-self -- moved here from rake-finsum-welldef.scm (2026-09-17): finsum-single-
;;; support (202) cites it and part 2 loads after that.  Cites nn-subset-ord,
;;; ord-segment-membership, ord-lt-iff only.
(define (rkn-mac-h! name hyp)
  (let* ((g0    (dk-goal))
         (new   (dk-opened (lambda () (mac-h name hyp))))
         (sides (filter (lambda (l) (not (alpha-equiv? (dk-goal-of l) g0))) new))
         (mains (filter (lambda (l) (alpha-equiv? (dk-goal-of l) g0)) new)))
    (for-each (lambda (s) (dk-focus! s) (ass)) sides)
    (if (null? mains) (error "rkn-mac-h!: no main branch after" name))
    (dk-focus! (car mains))))

;;; ord-segment-self:  n in NN => n not in ORD-SEGMENT(n).
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n)))))))
(let* ((nv  (dk-di-var!))
       (hyp (dk-landed-1 (lambda () (di)))))
  (dk-fact! 'nn-subset-ord nv)
  (rkn-mac-h! 'ord-segment-membership hyp)
  (rkn-mac-h! 'ord-lt-iff (dk-pick (dk-head? 'ORD-LT) "ORD-LT n n"))
  (dk-split! (dk-pick (dk-head? 'AND) "ord-lt-iff conjunction"))
  (have! (list '= nv nv) (lambda () (rfl)))
  (ai (list 'NOT (list '= nv nv))))
(rkn-check! 'ord-segment-self)
(qed 'ord-segment-self)
