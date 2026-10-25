;;; la-z6-pullback.scm -- a monoid automorphism induces a ring automorphism of the monoid algebra
;;; (LA-Z6, 2026-10-25).  The general mechanism under linear algebra 3.15.
;;;
;;; THE THEOREM.  monalg-pullback-iso: A a ring, M a monoid, ph a monoid endomorphism of M (it preserves
;;; OPR and IDEN) with a two-sided inverse ps in FUN(CARR M, CARR M).  Then
;;;     f |-> MONALG-PULLBACK(A, M, ph, f) = (x |-> f(ph x))
;;; is a ring isomorphism of MONALG(A, M) onto itself (IS-ISO-RING).  3.15 is the case M = the multi-indices
;;; on [1, n], ph = (beta |-> beta o sigma) (theorem-library/la-z6-mpoly).
;;;
;;; THE PROOF.  Write PB(f) for the pullback.
;;;   * typing: PB(f) is a function on CARR M (lam-t), and its support lies in IMAGE(ps, SUPP f) -- z in
;;;     supp PB(f) gives ph z in supp f and z = ps(ph z) -- a finite set (card-image-finite).
;;;   * PB preserves +, -, 0 pointwise (monalg-add-apply ...), and 1 because ph z = IDEN iff z = IDEN.
;;;   * PB preserves the convolution.  (PB f * PB g)(x) is a FINSUM over I(PB f, PB g, x) = {q in supp PB f
;;;     x supp PB g : q1 q2 = x} and PB(f * g)(x) = (f * g)(ph x) one over I(f, g, ph x).  The map
;;;     q |-> [ph q1, ph q2] is a bijection of the first index set onto the second, with inverse
;;;     p |-> [ps p1, ps p2] (ph is multiplicative; ps undoes it); finsum-reindex-ag carries the sum
;;;     across and the summands agree, f(ph q1) g(ph q2) on both sides.
;;;   * PB_ps is a two-sided inverse of PB_ph (monalg-ext), so the map is a bijection
;;;     (bijection-from-inverse).
;;;
;;; LOAD WINDOW: after "theorem-library/monalg-is-ring" (load.scm:1740, primary tree of 2026-10-25) -- the latest
;;; citations are monalg-is-ring, monalg-carr, the slot read-offs, monalg-mul-apply, monalg-mul-fun,
;;; monalg-ext, card-cartesian-nn, cartesian-pair-eq, bijection-from-inverse, lambda-compose-value (all
;;; there); then poly-zero (1739), monalg-laws (1726), finsum-fiber (1716) -- and after the vocabulary
;;; la-z6-vocab.  Nothing in the tree cites it but la-z6-mpoly.
;;; Library: algebra.  No axiom, support or stamp.  Helper prefix: lz6p-.
;;; Statement variables a_ m_ ph_ ps_ f_ g_ x_ z_; binders pbu_ pbv_ (the inverse laws), pbz_ (inclusion),
;;; q_ (index maps), p (the convolution's own binder, as polynomial.scm spells it).

(define (lz6p-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-z6-pullback: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

;;; ---- the hypotheses, spelled once ----
(define lz6p-C '(CARR m_))
(define lz6p-A '(CARR a_))
(define lz6p-F '(FINSUPP a_ m_))
(define lz6p-HR '(IS-RING a_))
(define lz6p-HM '(IS-MONOID m_))
(define (lz6p-Hfun h) (list 'IN h '(FUN (CARR m_) (CARR m_))))
(define (lz6p-Hinv h k)                 ; k(h u) = u on CARR m_
  (list 'FORALL 'pbu_ (list 'IMPLIES '(IN pbu_ (CARR m_)) (list '= (list k (list h 'pbu_)) 'pbu_))))
(define lz6p-Hop
  '(FORALL pbu_ (IMPLIES (IN pbu_ (CARR m_)) (FORALL pbv_ (IMPLIES (IN pbv_ (CARR m_))
     (= (ph_ ((OPR m_) pbu_ pbv_)) ((OPR m_) (ph_ pbu_) (ph_ pbv_))))))))
(define lz6p-Hid '(= (ph_ (IDEN m_)) (IDEN m_)))
(define (lz6p-PB h f) (list 'MONALG-PULLBACK 'a_ 'm_ h f))
(define (lz6p-supp f) (list 'SUPP 'a_ 'm_ f))

;;; ---- small kit ----
(define (lz6p-typ! t cls)
  (if (not (dk-asm? (list 'IN t cls)))
      (dk-have! (list 'IN t cls) dk-typ-close!)))
;; (IN (h t) CARR) from h in FUN(C, C) and t in C
(define (lz6p-app! h t) (if (not (dk-asm? (list 'IN (list h t) lz6p-C))) (fact 'fun-apply-type-c h lz6p-C lz6p-C t)))
(define (lz6p-carr-set!) (if (not (dk-asm? (list 'IN lz6p-C 'SET))) (fact 'monoid-carrier-is-set 'm_)))
;; the two halves of z in SUPP(a_, m_, f), on lanes
(define (lz6p-supp-parts! z f)
  (let ((hyp (list 'IN z (lz6p-supp f))))
    (dk-project! (list 'IN z lz6p-C) 'supp-membership hyp)
    (dk-project! (list 'NOT (list '= (list f z) '(ZERO a_))) 'supp-membership hyp)))
;; f in FUN(C, A) off f in FINSUPP, on a lane
(define (lz6p-fun-of! f)
  (dk-project! (list 'IN f (list 'FUN lz6p-C lz6p-A)) 'finsupp-membership (list 'IN f lz6p-F)))
(define (lz6p-card-of! f)
  (dk-project! (list 'IN (list 'CARD (lz6p-supp f)) 'NN) 'finsupp-membership (list 'IN f lz6p-F)))

;;; =====================================================================
;;; pb-apply: (PB f)(x) == f(ph x) for x in CARR m_.
;;; =====================================================================
(sp (make-wff (forall-guarded '(a_ m_ ph_ f_ x_) (list '(IN x_ (CARR m_)))
  (list '== (list (lz6p-PB 'ph_ 'f_) 'x_) '(f_ (ph_ x_))))))
(dk-peel!)
(mac 'MONALG-PULLBACK)
(dk-lam-b!)
(if (not (proof-done? *ps*)) (qrfl))
(lz6p-done! 'monalg-pullback-apply)
(topic! 'monalg-pullback-apply 'algebra)

;;; =====================================================================
;;; pb-fun: PB f is a function on CARR m_ into CARR a_.
;;; =====================================================================
(sp (make-wff (forall-guarded '(a_ m_ ph_ f_)
  (list lz6p-HM (lz6p-Hfun 'ph_) (list 'IN 'f_ (list 'FUN lz6p-C lz6p-A)))
  (list 'IN (lz6p-PB 'ph_ 'f_) (list 'FUN lz6p-C lz6p-A)))))
(dk-peel!)
(lz6p-carr-set!)
(mac 'MONALG-PULLBACK)
(dk-lam-type!
  (lambda ()
    (let ((z (dk-di-var!)))
      (lz6p-app! 'ph_ z)
      (fact 'fun-apply-type-c 'f_ lz6p-C lz6p-A (list 'ph_ z))
      (ass)))
  (lambda () (ass)))
(lz6p-done! 'monalg-pullback-fun)
(topic! 'monalg-pullback-fun 'algebra)

;;; =====================================================================
;;; pb-supp-fwd: z in supp PB(f)  =>  ph z in supp f.
;;; =====================================================================
(sp (make-wff (forall-guarded '(a_ m_ ph_ f_ z_)
  (list lz6p-HM (lz6p-Hfun 'ph_) (list 'IN 'f_ (list 'FUN lz6p-C lz6p-A))
        (list 'IN 'z_ (lz6p-supp (lz6p-PB 'ph_ 'f_))))
  (list 'IN '(ph_ z_) (lz6p-supp 'f_)))))
(dk-peel!)
(fact 'monalg-pullback-fun 'a_ 'm_ 'ph_ 'f_)
(lz6p-supp-parts! 'z_ (lz6p-PB 'ph_ 'f_))
(lz6p-app! 'ph_ 'z_)
(fact 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'f_ 'z_)
(mac 'supp-membership)
(dk-conj-close!
  (lambda ()
    (if (eq? (car (dk-goal)) 'NOT)
        (begin (subst (list '= '(f_ (ph_ z_)) (list (lz6p-PB 'ph_ 'f_) 'z_))) (ass))
        (ass))))
(lz6p-done! 'monalg-pullback-supp-fwd)
(topic! 'monalg-pullback-supp-fwd 'algebra)

;;; =====================================================================
;;; pb-supp-bwd: p in supp f and ph(ps p) = p  =>  ps p in supp PB(f).
;;; =====================================================================
(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ z_)
  (list lz6p-HM (lz6p-Hfun 'ph_) (lz6p-Hfun 'ps_) (lz6p-Hinv 'ps_ 'ph_) (list 'IN 'f_ (list 'FUN lz6p-C lz6p-A))
        (list 'IN 'z_ (lz6p-supp 'f_)))
  (list 'IN '(ps_ z_) (lz6p-supp (lz6p-PB 'ph_ 'f_))))))
(dk-peel!)
(fact 'monalg-pullback-fun 'a_ 'm_ 'ph_ 'f_)
(lz6p-supp-parts! 'z_ 'f_)
(lz6p-app! 'ps_ 'z_)
(dk-apply! (lz6p-Hinv 'ps_ 'ph_) 'z_)
(fact 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'f_ '(ps_ z_))
(mac 'supp-membership)
(dk-conj-close!
  (lambda ()
    (if (eq? (car (dk-goal)) 'NOT)
        (begin (subst (list '= (list (lz6p-PB 'ph_ 'f_) '(ps_ z_)) '(f_ (ph_ (ps_ z_)))))
               (subst '(= (ph_ (ps_ z_)) z_))
               (ass))
        (ass))))
(lz6p-done! 'monalg-pullback-supp-bwd)
(topic! 'monalg-pullback-supp-bwd 'algebra)

;;; =====================================================================
;;; pb-finsupp: PB f is finitely supported -- supp PB(f) lies in IMAGE(ps, supp f).
;;; =====================================================================
(define lz6p-Hpp (lz6p-Hinv 'ph_ 'ps_))        ; ps(ph u) = u
(define lz6p-Hqq (lz6p-Hinv 'ps_ 'ph_))        ; ph(ps v) = v
(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_)
  (list lz6p-HM (lz6p-Hfun 'ph_) (lz6p-Hfun 'ps_) lz6p-Hpp (list 'IN 'f_ lz6p-F))
  (list 'IN (lz6p-PB 'ph_ 'f_) lz6p-F))))
(dk-peel!)
(lz6p-carr-set!)
(lz6p-fun-of! 'f_)
(lz6p-card-of! 'f_)
(fact 'monalg-pullback-fun 'a_ 'm_ 'ph_ 'f_)
(let* ((sf  (lz6p-supp 'f_))
       (pbf (lz6p-PB 'ph_ 'f_))
       (sp_ (lz6p-supp pbf))
       (img (list 'IMAGE 'ps_ sf)))
  (fact 'supp-in-set 'a_ 'm_ 'f_)
  (fact 'supp-in-set 'a_ 'm_ pbf)
  (fact 'image-set 'ps_ sf)
  (fact 'card-image-finite 'ps_ sf)
  (dk-have! (list 'AND (list 'IN img 'SET) (list 'IN (list 'CARD img) 'NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
  (dk-have! (list 'AND (list 'IN sp_ 'SET)
                  (list 'FORALL 'pbz_ (list 'IMPLIES (list 'IN 'pbz_ sp_) (list 'IN 'pbz_ img))))
    (lambda ()
      (dk-conj-close!
        (lambda ()
          (if (eq? (car (dk-goal)) 'IN)
              (ass)
              (let ((z (dk-di-var!)))
                (fact 'monalg-pullback-supp-fwd 'a_ 'm_ 'ph_ 'f_ z)
                (lz6p-supp-parts! z pbf)
                (dk-apply! lz6p-Hpp z)
                (fact 'membership-implies-sethood z lz6p-C)
                (mac 'image-membership-iff)
                (dk-conj-close!
                  (lambda ()
                    (if (eq? (car (dk-goal)) 'FORSOME)
                        (begin (ew (list 'ph_ z)) (dk-conj-close! (lambda () (ass))))
                        (ass))))))))))
  (fact 'card-subset-nn img sp_)
  (mac 'finsupp-membership)
  (dk-conj-close! (lambda () (ass))))
(lz6p-done! 'monalg-pullback-finsupp)
(topic! 'monalg-pullback-finsupp 'algebra)

;;; ---- function equality in FINSUPP by monalg-ext; PTWISE proves (= (lhs x) (rhs x)) for a typed x ----
(define (lz6p-ext! lhs rhs ptwise)
  (dk-have! (list 'FORALL 'pbx_ (list 'IMPLIES (list 'IN 'pbx_ lz6p-C) (list '= (list lhs 'pbx_) (list rhs 'pbx_))))
    (lambda () (ptwise (dk-di-var!))))
  (fact 'monalg-ext 'a_ 'm_ lhs rhs)
  (ass))
;; rewrite the goal by the equation E (== or =, left to right).  ONE recording call per form: the
;; callers sequence (lz6p-sub! (dk-cite! ...)) steps in a `begin', never several citations in one
;; argument list (MIT's argument order differs between compiled and interpreted code).
(define (lz6p-sub! e) (subst (list '= (cadr e) (caddr e))))
(define lz6p-H6 (list lz6p-HR lz6p-HM (lz6p-Hfun 'ph_) (lz6p-Hfun 'ps_) lz6p-Hpp))
(define (lz6p-H6-setup!)
  (dk-peel!)
  (lz6p-carr-set!))
(define (lz6p-pbfs! f)                 ; PB f in FINSUPP and in FUN, f in FUN
  (lz6p-fun-of! f)
  (fact 'monalg-pullback-finsupp 'a_ 'm_ 'ph_ 'ps_ f)
  (fact 'monalg-pullback-fun 'a_ 'm_ 'ph_ f))
(define (lz6p-val! f x)                ; f(x) in CARR a_, f in FUN(C, A) in context
  (if (not (dk-asm? (list 'IN (list f x) lz6p-A))) (fact 'fun-apply-type-c f lz6p-C lz6p-A x)))

;;; =====================================================================
;;; pb-add / pb-neg / pb-zero.
;;; =====================================================================
(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_)
  (append lz6p-H6 (list (list 'IN 'f_ lz6p-F) (list 'IN 'g_ lz6p-F)))
  (list '= (lz6p-PB 'ph_ '(MONALG-ADD a_ m_ f_ g_))
           (list 'MONALG-ADD 'a_ 'm_ (lz6p-PB 'ph_ 'f_) (lz6p-PB 'ph_ 'g_))))))
(lz6p-H6-setup!)
(fact 'monalg-add-fun 'a_ 'm_ 'f_ 'g_)
(lz6p-pbfs! 'f_) (lz6p-pbfs! 'g_) (lz6p-pbfs! '(MONALG-ADD a_ m_ f_ g_))
(fact 'monalg-add-fun 'a_ 'm_ (lz6p-PB 'ph_ 'f_) (lz6p-PB 'ph_ 'g_))
(lz6p-ext! (lz6p-PB 'ph_ '(MONALG-ADD a_ m_ f_ g_)) (list 'MONALG-ADD 'a_ 'm_ (lz6p-PB 'ph_ 'f_) (lz6p-PB 'ph_ 'g_))
  (lambda (x)
    (let ((phx (list 'ph_ x)))
      (lz6p-app! 'ph_ x)
      (lz6p-val! 'f_ phx) (lz6p-val! 'g_ phx)
      (begin (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ '(MONALG-ADD a_ m_ f_ g_) x))
             (lz6p-sub! (dk-cite! 'monalg-add-apply 'a_ 'm_ 'f_ 'g_ phx))
             (lz6p-sub! (dk-cite! 'monalg-add-apply 'a_ 'm_ (lz6p-PB 'ph_ 'f_) (lz6p-PB 'ph_ 'g_) x))
             (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'f_ x))
             (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'g_ x))
             (rfl)))))
(lz6p-done! 'monalg-pullback-add)
(topic! 'monalg-pullback-add 'algebra)

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_)
  (append lz6p-H6 (list (list 'IN 'f_ lz6p-F)))
  (list '= (lz6p-PB 'ph_ '(MONALG-NEG a_ m_ f_)) (list 'MONALG-NEG 'a_ 'm_ (lz6p-PB 'ph_ 'f_))))))
(lz6p-H6-setup!)
(fact 'monalg-neg-fun 'a_ 'm_ 'f_)
(lz6p-pbfs! 'f_) (lz6p-pbfs! '(MONALG-NEG a_ m_ f_))
(fact 'monalg-neg-fun 'a_ 'm_ (lz6p-PB 'ph_ 'f_))
(lz6p-ext! (lz6p-PB 'ph_ '(MONALG-NEG a_ m_ f_)) (list 'MONALG-NEG 'a_ 'm_ (lz6p-PB 'ph_ 'f_))
  (lambda (x)
    (let ((phx (list 'ph_ x)))
      (lz6p-app! 'ph_ x)
      (lz6p-val! 'f_ phx)
      (begin (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ '(MONALG-NEG a_ m_ f_) x))
             (lz6p-sub! (dk-cite! 'monalg-neg-apply 'a_ 'm_ 'f_ phx))
             (lz6p-sub! (dk-cite! 'monalg-neg-apply 'a_ 'm_ (lz6p-PB 'ph_ 'f_) x))
             (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'f_ x))
             (rfl)))))
(lz6p-done! 'monalg-pullback-neg)
(topic! 'monalg-pullback-neg 'algebra)

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_) lz6p-H6
  (list '= (lz6p-PB 'ph_ '(MONALG-ZERO a_ m_)) '(MONALG-ZERO a_ m_)))))
(lz6p-H6-setup!)
(fact 'monalg-zero-in 'a_ 'm_)
(lz6p-pbfs! '(MONALG-ZERO a_ m_))
(fact 'ring-zero-in 'a_)
(lz6p-ext! (lz6p-PB 'ph_ '(MONALG-ZERO a_ m_)) '(MONALG-ZERO a_ m_)
  (lambda (x)
    (let ((phx (list 'ph_ x)))
      (lz6p-app! 'ph_ x)
      (begin (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ '(MONALG-ZERO a_ m_) x))
             (lz6p-sub! (dk-cite! 'monalg-zero-apply 'a_ 'm_ phx))
             (lz6p-sub! (dk-cite! 'monalg-zero-apply 'a_ 'm_ x))
             (rfl)))))
(lz6p-done! 'monalg-pullback-zero)
(topic! 'monalg-pullback-zero 'algebra)

;;; =====================================================================
;;; pb-one: ph z = IDEN iff z = IDEN, so the indicator of IDEN pulls back to itself.
;;; =====================================================================
(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_) (append lz6p-H6 (list lz6p-Hid))
  (list '= (lz6p-PB 'ph_ '(MONALG-ONE a_ m_)) '(MONALG-ONE a_ m_)))))
(lz6p-H6-setup!)
(fact 'monalg-one-in 'a_ 'm_)
(lz6p-pbfs! '(MONALG-ONE a_ m_))
(fact 'ring-zero-in 'a_)
(fact 'ring-one-in 'a_)
(fact 'monoid-identity-in 'm_)
(lz6p-app! 'ps_ '(IDEN m_))
(dk-apply! lz6p-Hpp '(IDEN m_))
(dk-rewrite-h! '(= (ps_ (ph_ (IDEN m_))) (IDEN m_)) '(ph_ (IDEN m_)) '(IDEN m_))
(lz6p-ext! (lz6p-PB 'ph_ '(MONALG-ONE a_ m_)) '(MONALG-ONE a_ m_)
  (lambda (x)
    (let* ((phx (list 'ph_ x))
           (rif (list 'IF (list '= x '(IDEN m_)) '(ONE a_) '(ZERO a_))))
      (lz6p-app! 'ph_ x)
      (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ '(MONALG-ONE a_ m_) x))
      (lz6p-sub! (dk-cite! 'monalg-one-apply 'a_ 'm_ phx))
      (lz6p-sub! (dk-cite! 'monalg-one-apply 'a_ 'm_ x))
      (dk-case-if! rif
        (lambda (true? val)
          (if true?
              (begin
                (subst (list '= x '(IDEN m_)))
                (dk-if-branch! #t '(IF (= (ph_ (IDEN m_)) (IDEN m_)) (ONE a_) (ZERO a_)) #f (lambda () (rfl))))
              (dk-if-branch! #f (list 'IF (list '= phx '(IDEN m_)) '(ONE a_) '(ZERO a_))
                (lambda ()
                  (di)
                  (let ((e1 (dk-apply! lz6p-Hpp x)))
                    (dk-rewrite-h! e1 phx '(IDEN m_))
                    (dk-have! (list '= x '(IDEN m_))
                      (lambda () (subst (list '= x '(ps_ (IDEN m_)))) (ass)))
                    (dk-only! (list '= x '(IDEN m_)) (list 'NOT (list '= x '(IDEN m_))))
                    (prop)))
                (lambda () (rfl)))))))))
(lz6p-done! 'monalg-pullback-one)
(topic! 'monalg-pullback-one 'algebra)

;;; =====================================================================
;;; THE CONVOLUTION.  Index sets and the two index maps.
;;;   I(f, g, y) = { p in supp f x supp g : p1 . p2 = y }            (polynomial.scm's spelling)
;;;   PHI = q_ in I(PB f, PB g, x) |-> [ph q1, ph q2]   into I(f, g, ph x)
;;;   PSI = q_ in I(f, g, ph x)    |-> [ps q1, ps q2]   back
;;; =====================================================================
(define (lz6p-P f g) (list 'CARTESIAN (lz6p-supp f) (lz6p-supp g)))
(define (lz6p-I f g y)
  (list 'SEP 'p (lz6p-P f g) (list '= (list '(OPR m_) '(NTH 1 p) '(NTH 2 p)) y)))
(define lz6p-pf (lz6p-PB 'ph_ 'f_))
(define lz6p-pg (lz6p-PB 'ph_ 'g_))
(define lz6p-T (lz6p-I lz6p-pf lz6p-pg 'x_))
(define lz6p-S (lz6p-I 'f_ 'g_ '(ph_ x_)))
(define (lz6p-map h dom) (list 'VNB-LAMBDA 'q_ dom (list 'LIST (list h '(NTH 1 q_)) (list h '(NTH 2 q_)))))
(define lz6p-PHI (lz6p-map 'ph_ lz6p-T))
(define lz6p-PSI (lz6p-map 'ps_ lz6p-S))
(define (lz6p-opr s t) (list '(OPR m_) s t))
(define (lz6p-nth k q) (list 'NTH k q))
(define lz6p-HX (append lz6p-H6 (list lz6p-Hqq lz6p-Hop (list 'IN 'f_ lz6p-F) (list 'IN 'g_ lz6p-F) '(IN x_ (CARR m_)))))
(define (lz6p-HX-setup!)
  (dk-peel!)
  (lz6p-carr-set!)
  (lz6p-fun-of! 'f_) (lz6p-fun-of! 'g_)
  (fact 'monalg-pullback-fun 'a_ 'm_ 'ph_ 'f_)
  (fact 'monalg-pullback-fun 'a_ 'm_ 'ph_ 'g_)
  (lz6p-app! 'ph_ 'x_))

(define (lz6p-any-sub? pred t)
  (let loop ((x t))
    (cond ((not (pair? x)) #f)
          ((pred x) #t)
          (#t (let scan ((l x)) (cond ((not (pair? l)) #f) ((loop (car l)) #t) (#t (scan (cdr l)))))))))
(define (lz6p-nth-redex? x)
  (and (eq? (car x) 'NTH) (= (length x) 3) (pair? (caddr x)) (eq? (car (caddr x)) 'LIST)))
(define (lz6p-nth-all!)
  (let lp ((n 0)) (if (and (< n 8) (lz6p-any-sub? lz6p-nth-redex? (dk-goal)))
                      (begin (nth-r) (lp (+ n 1))))))
;; goal (= (LIST q1 q2) q) for q in CARTESIAN(A, B)
(define (lz6p-pair-close! q A B)
  (fact 'cartesian-pair-eq q A B)
  (fact 'eq-sym q (list 'LIST (lz6p-nth 1 q) (lz6p-nth 2 q)))
  (ass))

;; sethood of I(f, g, y) (CARR m_ in SET in context)
(define (lz6p-index-set! f g y)
  (let ((P (lz6p-P f g)) (I (lz6p-I f g y)))
    (if (not (dk-asm? (list 'IN (lz6p-supp f) 'SET))) (fact 'supp-in-set 'a_ 'm_ f))
    (if (not (dk-asm? (list 'IN (lz6p-supp g) 'SET))) (fact 'supp-in-set 'a_ 'm_ g))
    (if (not (dk-asm? (list 'IN P 'SET)))
        (dk-have! (list 'IN P 'SET) (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass))))))
    (if (not (dk-asm? (list 'IN I 'SET)))
        (dk-have! (list 'IN I 'SET)
          (lambda () (let ((leaf (proof-state-focus *ps*))) (sep-set) (if (not (sequent-node-grounded? leaf)) (ass))))))))

;; ass on LEAF unless something already grounded it (a dk-have! of a claim equal to the focus goal
;; proves it in place and moves the focus to a sibling)
(define (lz6p-ass-on! leaf)
  (if (not (sequent-node-grounded? leaf)) (begin (dk-focus! leaf) (ass))))

;; close the focus goal (IN I(f, g, y) SET)
(define (lz6p-set-goal! f g y)
  (if (dk-asm? (dk-goal)) (ass) (lz6p-index-set! f g y)))

;; the two halves of q in I(f, g, y), on lanes (sep-me consumes what it opens)
(define (lz6p-open-idx! f g y q)
  (let ((mem (list 'IN q (lz6p-I f g y))))
    (dk-have! (list 'IN q (lz6p-P f g))
      (lambda () (dk-split-all! (dk-landed (lambda () (sep-me mem)))) (ass)))
    (dk-have! (list '= (lz6p-opr (lz6p-nth 1 q) (lz6p-nth 2 q)) y)
      (lambda () (dk-split-all! (dk-landed (lambda () (sep-me mem)))) (ass)))
    (dk-split! (dk-fact! 'cartesian-nth q (lz6p-supp f) (lz6p-supp g)))
    (lz6p-supp-parts! (lz6p-nth 1 q) f)
    (lz6p-supp-parts! (lz6p-nth 2 q) g)))

;; close the goal (IN (LIST u v) (I f g y)), given u in supp f, v in supp g and EQ-CLOSER for u . v = y
(define (lz6p-idx-close! f g u v eq-closer)
  (for-each
   (lambda (n)
     (dk-focus! n)
     (if (eq? (car (dk-goal)) 'IN)
         (begin (fact 'pair-in-cartesian (lz6p-supp f) (lz6p-supp g) u v) (ass))
         (begin (lz6p-nth-all!)
                (eq-closer))))
   (dk-opened (lambda () (sep-mi)))))

;; for q in T: [ph q1, ph q2] in S, landed
(define (lz6p-phi-mem! q)
  (let ((q1 (lz6p-nth 1 q)) (q2 (lz6p-nth 2 q)))
    (lz6p-open-idx! lz6p-pf lz6p-pg 'x_ q)
    (fact 'monalg-pullback-supp-fwd 'a_ 'm_ 'ph_ 'f_ q1)
    (fact 'monalg-pullback-supp-fwd 'a_ 'm_ 'ph_ 'g_ q2)
    (lz6p-app! 'ph_ q1) (lz6p-app! 'ph_ q2)
    (let ((hop (dk-apply! lz6p-Hop q1 q2)))
      (dk-have! (list 'IN (list 'LIST (list 'ph_ q1) (list 'ph_ q2)) lz6p-S)
        (lambda ()
          (lz6p-idx-close! 'f_ 'g_ (list 'ph_ q1) (list 'ph_ q2)
            (lambda ()
              (subst (list '= (lz6p-opr (list 'ph_ q1) (list 'ph_ q2)) (list 'ph_ (lz6p-opr q1 q2))))
              (subst (list '= (lz6p-opr q1 q2) 'x_))
              (rfl))))))))

;; for p in S: [ps p1, ps p2] in T, landed
(define (lz6p-psi-mem! p)
  (let* ((p1 (lz6p-nth 1 p)) (p2 (lz6p-nth 2 p))
         (u (list 'ps_ p1)) (v (list 'ps_ p2)) (w (lz6p-opr u v)))
    (lz6p-open-idx! 'f_ 'g_ '(ph_ x_) p)
    (fact 'monalg-pullback-supp-bwd 'a_ 'm_ 'ph_ 'ps_ 'f_ p1)
    (fact 'monalg-pullback-supp-bwd 'a_ 'm_ 'ph_ 'ps_ 'g_ p2)
    (lz6p-app! 'ps_ p1) (lz6p-app! 'ps_ p2)
    (dk-have! (list 'AND lz6p-HM (list 'AND (list 'IN u lz6p-C) (list 'IN v lz6p-C)))
      (lambda () (dk-conj-close! (lambda () (ass)))))
    (fact 'monoid-carrier-closed-opr 'm_ u v)
    (lz6p-app! 'ph_ w)
    (let* ((hop (dk-apply! lz6p-Hop u v))
           (h1 (dk-apply! lz6p-Hqq p1))
           (h2 (dk-apply! lz6p-Hqq p2))
           (e1 (dk-rewrite-h! hop (list 'ph_ u) p1))
           (e2 (dk-rewrite-h! e1 (list 'ph_ v) p2))
           (e3 (dk-rewrite-h! e2 (lz6p-opr p1 p2) '(ph_ x_)))
           (hw (dk-apply! lz6p-Hpp w))
           (hx (dk-apply! lz6p-Hpp 'x_)))
      (dk-have! (list 'IN (list 'LIST u v) lz6p-T)
        (lambda ()
          (lz6p-idx-close! lz6p-pf lz6p-pg u v
            (lambda ()
              (subst (list '= w (list 'ps_ (list 'ph_ w))))
              (subst (list '= (list 'ph_ w) '(ph_ x_)))
              (ass))))))))

;;; ---- the two maps are typed ----
(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_ x_) lz6p-HX
  (list 'IN lz6p-PHI (list 'FUN lz6p-T lz6p-S)))))
(lz6p-HX-setup!)
(dk-lam-type!
  (lambda ()
    (let* ((q (dk-di-var!)) (leaf (proof-state-focus *ps*)))
      (lz6p-phi-mem! q)
      (lz6p-ass-on! leaf)))
  (lambda () (lz6p-set-goal! lz6p-pf lz6p-pg 'x_)))
(lz6p-done! 'monalg-pullback-index-fun)
(topic! 'monalg-pullback-index-fun 'algebra)

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_ x_) lz6p-HX
  (list 'IN lz6p-PSI (list 'FUN lz6p-S lz6p-T)))))
(lz6p-HX-setup!)
(dk-lam-type!
  (lambda ()
    (let* ((q (dk-di-var!)) (leaf (proof-state-focus *ps*)))
      (lz6p-psi-mem! q)
      (lz6p-ass-on! leaf)))
  (lambda () (lz6p-set-goal! 'f_ 'g_ '(ph_ x_))))
(lz6p-done! 'monalg-pullback-index-inv-fun)
(topic! 'monalg-pullback-index-inv-fun 'algebra)

;;; ---- the round trips ----


(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_ x_) lz6p-HX
  (list 'FORALL 'pbq_ (list 'IMPLIES (list 'IN 'pbq_ lz6p-T) (list '= (list lz6p-PSI (list lz6p-PHI 'pbq_)) 'pbq_))))))
(lz6p-HX-setup!)
(let* ((q (caddr (dk-goal))) (q1 (lz6p-nth 1 q)) (q2 (lz6p-nth 2 q)))
  (lz6p-phi-mem! q)
  (fact 'monalg-pullback-index-fun 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
  (fact 'fun-apply-type-c lz6p-PHI lz6p-T lz6p-S q)
  (dk-lam-b!)
  (lz6p-nth-all!)
  (subst (dk-apply! lz6p-Hpp q1))
  (subst (dk-apply! lz6p-Hpp q2))
  (lz6p-pair-close! q (lz6p-supp lz6p-pf) (lz6p-supp lz6p-pg)))
(lz6p-done! 'monalg-pullback-index-left)
(topic! 'monalg-pullback-index-left 'algebra)

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_ x_) lz6p-HX
  (list 'FORALL 'pbq_ (list 'IMPLIES (list 'IN 'pbq_ lz6p-S) (list '= (list lz6p-PHI (list lz6p-PSI 'pbq_)) 'pbq_))))))
(lz6p-HX-setup!)
(let* ((q (caddr (dk-goal))) (q1 (lz6p-nth 1 q)) (q2 (lz6p-nth 2 q)))
  (lz6p-psi-mem! q)
  (fact 'monalg-pullback-index-inv-fun 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
  (fact 'fun-apply-type-c lz6p-PSI lz6p-S lz6p-T q)
  (dk-lam-b!)
  (lz6p-nth-all!)
  (subst (dk-apply! lz6p-Hqq q1))
  (subst (dk-apply! lz6p-Hqq q2))
  (lz6p-pair-close! q (lz6p-supp 'f_) (lz6p-supp 'g_)))
(lz6p-done! 'monalg-pullback-index-right)
(topic! 'monalg-pullback-index-right 'algebra)

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_ x_) lz6p-HX
  (list 'IN lz6p-PHI (list 'BIJECTION lz6p-T lz6p-S)))))
(dk-peel!)
(fact 'monalg-pullback-index-fun 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
(fact 'monalg-pullback-index-inv-fun 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
(fact 'monalg-pullback-index-left 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
(fact 'monalg-pullback-index-right 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
(fact 'bijection-from-inverse lz6p-T lz6p-S lz6p-PHI lz6p-PSI)
(ass)
(lz6p-done! 'monalg-pullback-index-bijection)
(topic! 'monalg-pullback-index-bijection 'algebra)

;;; =====================================================================
;;; pb-mul-at / pb-mul: the pullback preserves the convolution.
;;; =====================================================================
(define lz6p-ag '(RING-ADDITIVE-AG a_))
(define (lz6p-L f g y)
  (list 'VNB-LAMBDA 'p (lz6p-I f g y) (list '(MUL a_) (list f '(NTH 1 p)) (list g '(NTH 2 p)))))

;; I(f, g, y) is a finite set and the convolution's summand is typed on it (f, g in FINSUPP in context)
(define (lz6p-idx-facts! f g y)
  (let ((P (lz6p-P f g)) (I (lz6p-I f g y)) (L (lz6p-L f g y)))
    (lz6p-index-set! f g y)
    (lz6p-fun-of! f) (lz6p-fun-of! g)
    (lz6p-card-of! f) (lz6p-card-of! g)
    (fact 'card-cartesian-nn (lz6p-supp f) (lz6p-supp g))
    (dk-have! (list 'AND (list 'IN P 'SET) (list 'IN (list 'CARD P) 'NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
    (if (memq 'zc_ (free-vars I)) (error "lz6p-idx-facts!: zc_ is free in the index set"))
    (dk-have! (list 'AND (list 'IN I 'SET) (list 'FORALL 'zc_ (list 'IMPLIES (list 'IN 'zc_ I) (list 'IN 'zc_ P))))
      (lambda ()
        (dk-conj-close!
          (lambda ()
            (if (eq? (car (dk-goal)) 'IN)
                (ass)
                (let ((zv (dk-di-var!)))
                  (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN zv I)))))
                  (ass)))))))
    (fact 'card-subset-nn P I)
    (dk-have! (list 'AND (list 'IN I 'SET) (list 'IN (list 'CARD I) 'NN)) (lambda () (dk-conj-close! (lambda () (ass)))))
    (dk-have! (list 'IN L (list 'FUN I lz6p-A))
      (lambda ()
        (dk-lam-type!
          (lambda ()
            (let ((pv (dk-di-var!)))
              (lz6p-open-idx! f g y pv)
              (lz6p-val! f (lz6p-nth 1 pv))
              (lz6p-val! g (lz6p-nth 2 pv))
              (fact 'ring-carrier-closed-mul 'a_ (list f (lz6p-nth 1 pv)) (list g (lz6p-nth 2 pv)))
              (ass)))
          (lambda () (ass)))))
    (dk-have! (list 'IN L (list 'FUN I (list 'CARR lz6p-ag)))
      (lambda () (mac 'raag-carr) (ass)))))

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_ x_) lz6p-HX
  (list '= (list (lz6p-PB 'ph_ '(MONALG-MUL a_ m_ f_ g_)) 'x_)
           (list (list 'MONALG-MUL 'a_ 'm_ lz6p-pf lz6p-pg) 'x_)))))
(lz6p-HX-setup!)
(fact 'ring-additive-ag-is-abelian-group 'a_)
(fact 'monalg-pullback-finsupp 'a_ 'm_ 'ph_ 'ps_ 'f_)
(fact 'monalg-pullback-finsupp 'a_ 'm_ 'ph_ 'ps_ 'g_)
(lz6p-idx-facts! 'f_ 'g_ '(ph_ x_))
(lz6p-idx-facts! lz6p-pf lz6p-pg 'x_)
(subst (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ '(MONALG-MUL a_ m_ f_ g_) 'x_))
(subst (dk-cite! 'monalg-mul-apply 'a_ 'm_ 'f_ 'g_ '(ph_ x_)))
(subst (dk-cite! 'monalg-mul-apply 'a_ 'm_ lz6p-pf lz6p-pg 'x_))
(let* ((S lz6p-S) (T lz6p-T)
       (LS (lz6p-L 'f_ 'g_ '(ph_ x_)))
       (LT (lz6p-L lz6p-pf lz6p-pg 'x_)))
  (fact 'monalg-pullback-index-bijection 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
  (let* ((req (dk-fact! 'finsum-reindex-ag lz6p-ag S T lz6p-PHI LS))
         (lam (caddr (caddr req))))
    (subst req)
    (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ T) (list '= (list lam 'z_) (list LT 'z_))))
      (lambda ()
        (let* ((zv (dk-di-var!)) (z1 (lz6p-nth 1 zv)) (z2 (lz6p-nth 2 zv)))
          (lz6p-phi-mem! zv)
          (fact 'monalg-pullback-index-fun 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ 'x_)
          (fact 'fun-apply-type-c lz6p-PHI T S zv)
          (lz6p-val! 'f_ (list 'ph_ z1))
          (lz6p-val! 'g_ (list 'ph_ z2))
          (let ((lcv (dk-cite! 'lambda-compose-value LS lz6p-PHI T zv)))
            (subst (list '= (cadr lcv) (caddr lcv))))
          (dk-lam-b!)
          (lz6p-nth-all!)
          (subst (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'f_ z1))
          (subst (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'g_ z2))
          (fact 'ring-carrier-closed-mul 'a_ (list 'f_ (list 'ph_ z1)) (list 'g_ (list 'ph_ z2)))
          (rfl))))
    (subst (dk-fact! 'finsum-congruence-q lz6p-ag T lam LT))
    (fact 'finsum-type lz6p-ag T LT)
    (rfl)))
(lz6p-done! 'monalg-pullback-mul-at)
(topic! 'monalg-pullback-mul-at 'algebra)

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_ g_)
  (append lz6p-H6 (list lz6p-Hqq lz6p-Hop (list 'IN 'f_ lz6p-F) (list 'IN 'g_ lz6p-F)))
  (list '= (lz6p-PB 'ph_ '(MONALG-MUL a_ m_ f_ g_)) (list 'MONALG-MUL 'a_ 'm_ lz6p-pf lz6p-pg)))))
(lz6p-H6-setup!)
(fact 'monalg-mul-fun 'a_ 'm_ 'f_ 'g_)
(lz6p-pbfs! 'f_) (lz6p-pbfs! 'g_) (lz6p-pbfs! '(MONALG-MUL a_ m_ f_ g_))
(fact 'monalg-mul-fun 'a_ 'm_ lz6p-pf lz6p-pg)
(lz6p-ext! (lz6p-PB 'ph_ '(MONALG-MUL a_ m_ f_ g_)) (list 'MONALG-MUL 'a_ 'm_ lz6p-pf lz6p-pg)
  (lambda (x)
    (fact 'monalg-pullback-mul-at 'a_ 'm_ 'ph_ 'ps_ 'f_ 'g_ x)
    (ass)))
(lz6p-done! 'monalg-pullback-mul)
(topic! 'monalg-pullback-mul 'algebra)

;;; =====================================================================
;;; The inverse, the ring map and its bijectivity.
;;; =====================================================================
(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_ f_)
  (append lz6p-H6 (list lz6p-Hqq (list 'IN 'f_ lz6p-F)))
  (list '= (lz6p-PB 'ps_ (lz6p-PB 'ph_ 'f_)) 'f_))))
(lz6p-H6-setup!)
(lz6p-pbfs! 'f_)
(fact 'monalg-pullback-finsupp 'a_ 'm_ 'ps_ 'ph_ lz6p-pf)
(lz6p-ext! (lz6p-PB 'ps_ lz6p-pf) 'f_
  (lambda (x)
    (lz6p-app! 'ps_ x)
    (lz6p-val! 'f_ x)
    (begin (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ps_ lz6p-pf x))
           (lz6p-sub! (dk-cite! 'monalg-pullback-apply 'a_ 'm_ 'ph_ 'f_ (list 'ps_ x)))
           (lz6p-sub! (dk-apply! lz6p-Hqq x))
           (rfl))))
(lz6p-done! 'monalg-pullback-inverse)
(topic! 'monalg-pullback-inverse 'algebra)

(define (lz6p-TM h) (list 'VNB-LAMBDA 'pbf_ lz6p-F (lz6p-PB h 'pbf_)))

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_) lz6p-H6
  (list 'IN (lz6p-TM 'ph_) (list 'FUN lz6p-F lz6p-F)))))
(lz6p-H6-setup!)
(fact 'finsupp-in-set 'a_ 'm_)
(dk-lam-type!
  (lambda ()
    (let ((u (dk-di-var!)))
      (fact 'monalg-pullback-finsupp 'a_ 'm_ 'ph_ 'ps_ u)
      (ass)))
  (lambda () (ass)))
(lz6p-done! 'monalg-pullback-map-fun)
(topic! 'monalg-pullback-map-fun 'algebra)

(define (lz6p-round-trip! h k)
  (dk-have! (list 'FORALL 'pbu_ (list 'IMPLIES (list 'IN 'pbu_ lz6p-F)
              (list '= (list (lz6p-TM k) (list (lz6p-TM h) 'pbu_)) 'pbu_)))
    (lambda ()
      (let ((u (dk-di-var!)))
        (fact 'fun-apply-type-c (lz6p-TM h) lz6p-F lz6p-F u)
        (fact 'monalg-pullback-finsupp 'a_ 'm_ h k u)
        (dk-lam-b!)
        (fact 'monalg-pullback-inverse 'a_ 'm_ h k u)
        (ass)))))
(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_) (append lz6p-H6 (list lz6p-Hqq))
  (list 'IN (lz6p-TM 'ph_) (list 'BIJECTION lz6p-F lz6p-F)))))
(lz6p-H6-setup!)
(fact 'monalg-pullback-map-fun 'a_ 'm_ 'ph_ 'ps_)
(fact 'monalg-pullback-map-fun 'a_ 'm_ 'ps_ 'ph_)
(lz6p-round-trip! 'ph_ 'ps_)
(lz6p-round-trip! 'ps_ 'ph_)
(fact 'bijection-from-inverse lz6p-F lz6p-F (lz6p-TM 'ph_) (lz6p-TM 'ps_))
(ass)
(lz6p-done! 'monalg-pullback-map-bijection)
(topic! 'monalg-pullback-map-bijection 'algebra)

;;; =====================================================================
;;; monalg-pullback-iso: the headline.
;;; =====================================================================
(define lz6p-MA '(MONALG a_ m_))
;; one clause of the unfolded IS-HOM-RING, after the MONALG slot read-offs
(define (lz6p-hom-clause!)
  (let ((g (dk-goal)))
    (cond
      ((dk-head-is? g 'IS-RING) (fact 'monalg-is-ring 'a_ 'm_) (ass))
      ((dk-head-is? g 'IN) (fact 'monalg-pullback-map-fun 'a_ 'm_ 'ph_ 'ps_) (ass))
      ((dk-head-is? g 'FORALL)
       (let* ((landed (dk-peel!))
              (vs (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) lz6p-F))) landed)))
              (law (cond ((dk-contains? g 'MONALG-ADD) 'add) ((dk-contains? g 'MONALG-MUL) 'mul) (#t 'neg))))
         (for-each (lambda (v) (fact 'monalg-pullback-finsupp 'a_ 'm_ 'ph_ 'ps_ v)) vs)
         (case law
           ((add) (fact 'monalg-add-fun 'a_ 'm_ (car vs) (cadr vs))
                  (fact 'monalg-add-fun 'a_ 'm_ (lz6p-PB 'ph_ (car vs)) (lz6p-PB 'ph_ (cadr vs))))
           ((mul) (fact 'monalg-mul-fun 'a_ 'm_ (car vs) (cadr vs))
                  (fact 'monalg-mul-fun 'a_ 'm_ (lz6p-PB 'ph_ (car vs)) (lz6p-PB 'ph_ (cadr vs))))
           (else  (fact 'monalg-neg-fun 'a_ 'm_ (car vs))
                  (fact 'monalg-neg-fun 'a_ 'm_ (lz6p-PB 'ph_ (car vs)))))
         (dk-lam-b!)
         (case law
           ((add) (fact 'monalg-pullback-add 'a_ 'm_ 'ph_ 'ps_ (car vs) (cadr vs)))
           ((mul) (fact 'monalg-pullback-mul 'a_ 'm_ 'ph_ 'ps_ (car vs) (cadr vs)))
           (else  (fact 'monalg-pullback-neg 'a_ 'm_ 'ph_ 'ps_ (car vs))))
         (ass)))
      ((dk-contains? g 'MONALG-ZERO)
       (fact 'monalg-zero-in 'a_ 'm_)
       (dk-lam-b!)
       (fact 'monalg-pullback-zero 'a_ 'm_ 'ph_ 'ps_)
       (ass))
      (#t
       (fact 'monalg-one-in 'a_ 'm_)
       (dk-lam-b!)
       (fact 'monalg-pullback-one 'a_ 'm_ 'ph_ 'ps_)
       (ass)))))

(sp (make-wff (forall-guarded '(a_ m_ ph_ ps_) (append lz6p-H6 (list lz6p-Hqq lz6p-Hop lz6p-Hid))
  (list 'IS-ISO-RING lz6p-MA lz6p-MA (lz6p-TM 'ph_)))))
(lz6p-H6-setup!)
(mac 'IS-ISO-RING)
(dk-conj-close!
  (lambda ()
    (if (dk-head-is? (dk-goal) 'IN)
        (begin (mac 'monalg-carr)
               (fact 'monalg-pullback-map-bijection 'a_ 'm_ 'ph_ 'ps_)
               (ass))
        (begin (mac 'is-hom-ring-def)
               (mac 'monalg-carr) (mac 'monalg-add-op) (mac 'monalg-mul-op) (mac 'monalg-neg-op)
               (mac 'monalg-zero-slot) (mac 'monalg-one-slot)
               (dk-conj-close! lz6p-hom-clause!)))))
(lz6p-done! 'monalg-pullback-iso)
(topic! 'monalg-pullback-iso 'algebra)
(gloss! 'monalg-pullback-iso
  "A monoid automorphism ph of M (a hom of M with a two-sided inverse ps) induces a ring automorphism of
   the monoid algebra A[M]: f |-> (x |-> f(ph x)).  The convolution is carried across by the bijection
   (q1, q2) |-> (ph q1, ph q2) of the index sets.")
