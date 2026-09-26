;;; id-fun-laws.scm -- the identity map and the composition laws over FUN.
;;;
;;;   id-fun-type       a in SET => ID-FUN(a) in FUN(a, a)
;;;   id-fun-apply      x in a   => ID-FUN(a)(x) = x
;;;   compose-id-left   a in SET => b in SET => f in FUN(a, b) => COMPOSE(ID-FUN(b), f) = f
;;;   compose-id-right  a in SET => f in FUN(a, b) => COMPOSE(f, ID-FUN(a)) = f
;;;   compose-assoc     a in SET => b in SET => f in FUN(a, b) => g in FUN(b, c) =>
;;;                     h in FUN(c, u) => COMPOSE(h, COMPOSE(g, f)) = COMPOSE(COMPOSE(h, g), f)
;;;
;;; The three composition laws are strict equalities of FUNCTIONS, by
;;; fun-domain-extensionality (library.scm: f in FUN(a), g in FUN(a), pointwise
;;; equal on a => f = g), through the kit's dk-fun-ext!.  What that asks for is
;;; what the hypotheses are: both sides typed in FUN(dom, cod) -- compose-type,
;;; which is guarded on its DOMAIN being a set, hence `a in SET' everywhere, and
;;; `b in SET' where a composite with domain b (ID-FUN(b), COMPOSE(h, g)) must be
;;; typed -- and the pointwise equation, which is compose-apply and id-fun-apply
;;; at an argument typed first.
;;;
;;; ID-FUN is structure-library/id-fun.scm.  Batch 33 (2026-09-25).
;;; Window: after compose-apply-proof (compose-apply, compose-type) and
;;; fun-apply-type-proof (fun-apply-type-c); fun-domain-extensionality is
;;; primitive (library.scm).

;;; the equation (= ((COMPOSE outer inner) t) (outer (inner t))), read off
;;; compose-apply at the typing inner : A -> B, outer : B -> C, t in A.
(define (ifl-comp-at! A B C outer inner t)
  (dk-have! (list 'AND (list 'IN inner (list 'FUN A B)) (list 'IN outer (list 'FUN B C))))
  (dk-apply! (dk-cite! 'compose-apply A B C outer inner) t))

;;; (IN (fn t) B) off fun-apply-type-c, fn : A -> B, t in A (returned as held).
(define (ifl-app-type! fn A B t)
  (dk-cite! 'fun-apply-type-c fn A B t))

;;; the composite outer o inner typed in FUN(A, C) off compose-type.
(define (ifl-comp-type! A B C outer inner)
  (dk-have! (list 'AND (list 'IN inner (list 'FUN A B)) (list 'IN outer (list 'FUN B C))))
  (dk-cite! 'compose-type A B C outer inner))

(define (ifl-done! name)
  (if (proof-done? *ps*) (qed name) (error "id-fun-laws: failed to prove" name)))

;;; -----------------------------------------------------------------------
;;; id-fun-type: lam-t, the pointwise typing is the guard itself.
(sp (make-wff '(FORALL a (IMPLIES (IN a SET) (IN (ID-FUN a) (FUN a a))))))
(dk-peel!)
(mac 'ID-FUN)
(dk-lam-type! (lambda () (dk-peel!) (ass)))
(ifl-done! 'id-fun-type)

;;; -----------------------------------------------------------------------
;;; id-fun-apply: lam-b at the typed argument, then rfl.
(sp (make-wff '(FORALL a (FORALL x (IMPLIES (IN x a) (= ((ID-FUN a) x) x))))))
(dk-peel!)
(mac 'ID-FUN)
(if (not (dk-lam-b!)) (rfl))
(ifl-done! 'id-fun-apply)

;;; -----------------------------------------------------------------------
;;; compose-id-left: COMPOSE(ID-FUN(b), f) = f.
(sp (make-wff '(FORALL a (FORALL b (FORALL f
   (IMPLIES (IN a SET) (IMPLIES (IN b SET) (IMPLIES (IN f (FUN a b))
     (= (COMPOSE (ID-FUN b) f) f)))))))))
(dk-peel!)
(let* ((g (dk-goal)) (lhs (cadr g)) (f (caddr g))
       (id (cadr lhs)) (b (cadr id))
       (a (cadr (caddr (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (equal? (cadr x) f)))
                               "the typing of f")))))
  (dk-cite! 'id-fun-type b)
  (dk-fun-ext! lhs f a b
    (lambda () (ifl-comp-type! a b b id f) (ass))
    (lambda () (ass))
    (lambda (z)
      (subst (ifl-comp-at! a b b id f z))
      (ifl-app-type! f a b z)
      (subst (dk-cite! 'id-fun-apply b (list f z)))
      (rfl))))
(ifl-done! 'compose-id-left)

;;; -----------------------------------------------------------------------
;;; compose-id-right: COMPOSE(f, ID-FUN(a)) = f.
(sp (make-wff '(FORALL a (FORALL b (FORALL f
   (IMPLIES (IN a SET) (IMPLIES (IN f (FUN a b))
     (= (COMPOSE f (ID-FUN a)) f))))))))
(dk-peel!)
(let* ((g (dk-goal)) (lhs (cadr g)) (f (caddr g))
       (id (caddr lhs)) (a (cadr id))
       (b (caddr (caddr (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (equal? (cadr x) f)))
                                "the typing of f")))))
  (dk-cite! 'id-fun-type a)
  (dk-fun-ext! lhs f a b
    (lambda () (ifl-comp-type! a a b f id) (ass))
    (lambda () (ass))
    (lambda (z)
      (subst (ifl-comp-at! a a b f id z))
      (subst (dk-cite! 'id-fun-apply a z))
      (ifl-app-type! f a b z)
      (rfl))))
(ifl-done! 'compose-id-right)

;;; -----------------------------------------------------------------------
;;; compose-assoc: h o (g o f) = (h o g) o f.
(sp (make-wff '(FORALL a (FORALL b (FORALL c (FORALL u (FORALL f (FORALL g (FORALL h
   (IMPLIES (IN a SET) (IMPLIES (IN b SET)
     (IMPLIES (IN f (FUN a b)) (IMPLIES (IN g (FUN b c)) (IMPLIES (IN h (FUN c u))
       (= (COMPOSE h (COMPOSE g f)) (COMPOSE (COMPOSE h g) f))))))))))))))))
(dk-peel!)
(let* ((gl (dk-goal)) (lhs (cadr gl)) (rhs (caddr gl))
       (h (cadr lhs)) (gf (caddr lhs)) (g (cadr gf)) (f (caddr gf))
       (hg (cadr rhs))
       (typ (lambda (fn) (caddr (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (equal? (cadr x) fn)
                                                           (dk-head-is? (caddr x) 'FUN)))
                                         "a typing"))))
       (fab (typ f)) (fbc (typ g)) (fcu (typ h))
       (a (cadr fab)) (b (caddr fab)) (c (caddr fbc)) (u (caddr fcu)))
  (ifl-comp-type! a b c g f)
  (ifl-comp-type! b c u h g)
  (dk-fun-ext! lhs rhs a u
    (lambda () (ifl-comp-type! a c u h gf) (ass))
    (lambda () (ifl-comp-type! a b u hg f) (ass))
    (lambda (z)
      (ifl-app-type! f a b z)
      (ifl-app-type! g b c (list f z))
      (ifl-app-type! h c u (list g (list f z)))
      (subst (ifl-comp-at! a c u h gf z))
      (subst (ifl-comp-at! a b c g f z))
      (subst (ifl-comp-at! a b u hg f z))
      (subst (ifl-comp-at! b c u h g (list f z)))
      (rfl))))
(ifl-done! 'compose-assoc)
