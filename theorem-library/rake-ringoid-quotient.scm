;;; rake-ringoid-quotient.scm -- MUL and NEG compute on R/I.
;;;
;;; THE TWO STATEMENTS (rake batch 5c-N; the twins of rq-add-computes, proven in
;;; theorem-library/rake-ringoid.scm, whose statement shape they copy):
;;;
;;;   rq-mul-computes   r a ringoid, a, b in CARR(r)
;;;                       =>  (MUL RINGOID-QUOTIENT-RING(r))([a],[b]) = [ (MUL r)(a,b) ]
;;;   rq-neg-computes   r a ringoid, a in CARR(r)
;;;                       =>  (NEG RINGOID-QUOTIENT-RING(r))([a])     = [ (NEG r)(a) ]
;;;
;;; Neither was ever asserted: structure-library/ringoid.scm's descend block held
;;; rq-add-computes alone (retired 2026-09-18), and its comment promised "one per
;;; operation".  These are the other two, so there is no support to retire for them.
;;;
;;; THE ROUTE is rake-ringoid.scm's, once per operation: the definitional read-off
;;; (`rq-mul' / `rq-neg') rewrites the accessor in OPERATOR position to a
;;; DESCEND2 / DESCEND of the class-of-<op> map; that map is typed (`lam-t') and
;;; RESPECTS2 / RESPECTS the congruence; then descend2-computes / descend-computes
;;; IS the conclusion and `lam-b-h' reduces the landed equation's right side.
;;; The congruence is read out of and into RELATED by r6b-related-out /
;;; r6b-related-in (theorem-library/rake-ringoid.scm).
;;;
;;; WHAT IS NEW HERE is the multiplicative half of the ringoid's own ring
;;; arithmetic, which rake-ringoid-additive.scm did for ADD/NEG and nothing did
;;; for MUL.  The view RINGOID-AS-RING supplies assoc / the two identities / the
;;; two distributive laws and NOTHING ELSE: there is no ring-mul-closed-,
;;; ring-mul-zero-left- or ring-one-in-ringoid-as-ring companion (the view
;;; specializer ran before those were proven), so each is re-derived at (MUL r):
;;;
;;;   r7n-rmul-type        (MUL r)(a,b) in CARR(r)     -- IS-RINGOID's own FUN
;;;   r7n-rone-type        ONE(r) in CARR(r)              typings, through
;;;                                                       apply-tupling-2
;;;   r7n-radd-idem-zero   a + a = a  =>  a = 0       -- the additive group again
;;;   r7n-rzero-mul-left   0.b = 0                    -- (0+0).b = 0.b + 0.b
;;;   r7n-rmul-zero-right  a.0 = 0
;;;   r7n-rneg-mul-left    (-a).b = -(a.b)            -- inverses are unique
;;;   r7n-rmul-neg-right   a.(-b) = -(a.b)
;;;   r7n-rdiff-mul        a.b - u.v = (a-u).b + u.(b-v)
;;;
;;; r7n-rdiff-mul is the identity a congruence modulo a two-sided ideal needs:
;;; the first summand is I.R, the second R.I, so ringoid-ideal-mul-right,
;;; ringoid-ideal-mul-left and ringoid-ideal-add carry the difference into IDL(r).
;;; Its own proof is the two distributive laws plus ringoid-diff-telescope at
;;; (a.b, u.b, u.v).
;;;
;;; LOAD WINDOW [<theorem-library/rake-ringoid>+1, end).
;;;   lo: the latest citation is r6b-related-out / r6b-related-in /
;;;       r6b-rq-add-lam-type's neighbours in theorem-library/rake-ringoid (which
;;;       itself sits just below theorem-library/ringoid-setoid-proof).  Then
;;;       descend-computes / descend2-computes / class-eq-iff / class-in-quotient /
;;;       class-self / respects-unfold / respects2-unfold (rake-setoid2,
;;;       rake-setoid), the additive bricks (rake-ringoid-additive), eq-sym
;;;       (equality-basics), apply-tupling-2 (axioms), pair-in-cartesian
;;;       (pair-tuple-sethood), fun-apply-type-c (fun-apply-type-proof) and
;;;       ringoid.scm's own read-offs.
;;;   hi = end: nothing loaded cites either theorem (the only citer of the family
;;;       is theorem-library/ringoid-quotient-ring-proof.scm, which is NOT in
;;;       load.scm).
;;;
;;; Helper prefix: r7n-.

(define (r7n-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'set-quotient))
      (begin
        (display "\n*** rake-ringoid-quotient: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-ringoid-quotient: unfinished" name))))

;;; ---- MUL closes on the carrier ---------------------------------------
;;; rake-ringoid-additive.scm's r6b-radd-type, at MUL: the IS-RINGOID unfold in a
;;; `have!' lane (mac-h REPLACES the hypothesis every later citation is guarded
;;; on), then the apply-tupling-2 bridge, since a structure operation eats a PAIR.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(IN ((MUL r) a b) (CARR r))))))
(dk-peel!)
(have! '(IN (MUL r) (FUN (CARTESIAN (CARR r) (CARR r)) (CARR r)))
  (lambda ()
    (let ((u (dk-landed-1 (lambda () (mac-h 'IS-RINGOID '(IS-RINGOID r))))))
      (dk-split-all! (list u)))
    (ass)))
(fact 'apply-tupling-2 '(MUL r) 'a 'b)
(subst '(== ((MUL r) a b) ((MUL r) (LIST a b))))
(fact 'pair-in-cartesian '(CARR r) '(CARR r) 'a 'b)
(fact 'fun-apply-type-c '(MUL r) '(CARTESIAN (CARR r) (CARR r)) '(CARR r) '(LIST a b))
(ass)
(r7n-qed! 'r7n-rmul-type)

;;; ---- ONE lands in the carrier ----------------------------------------
;;; The (constant ONE CARR) conjunct of IS-RINGOID; there is no
;;; ring-one-in-ringoid-as-ring companion.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r)) '(IN (ONE r) (CARR r)))))
(dk-peel!)
(let ((u (dk-landed-1 (lambda () (mac-h 'IS-RINGOID '(IS-RINGOID r))))))
  (dk-split-all! (list u)))
(ass)
(r7n-qed! 'r7n-rone-type)

;;; ---- an idempotent of the additive group is the zero -------------------
;;; a = 0 + a = ((-a) + a) + a = (-a) + (a + a) = (-a) + a = 0.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a) '((IN a (CARR r)))
    '(IMPLIES (= ((ADD r) a a) a) (= a (ZERO r)))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'a)
(fact 'r6b-radd-type 'r '((NEG r) a) 'a)
(fact 'ring-add-left-id-ringoid-as-ring 'r 'a)
(fact 'ring-add-left-inv-ringoid-as-ring 'r 'a)
(fact 'ring-add-assoc-ringoid-as-ring 'r '((NEG r) a) 'a 'a)
(subst '(= a ((ADD r) (ZERO r) a)))
(subst '(= (ZERO r) ((ADD r) ((NEG r) a) a)))
(subst '(= ((ADD r) ((ADD r) ((NEG r) a) a) a) ((ADD r) ((NEG r) a) ((ADD r) a a))))
(subst '(= ((ADD r) a a) a))
(rfl)
(r7n-qed! 'r7n-radd-idem-zero)

;;; ---- 0.b = 0 ----------------------------------------------------------
;;; 0.b = (0+0).b = 0.b + 0.b, and an idempotent is the zero.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(b) '((IN b (CARR r)))
    '(= ((MUL r) (ZERO r) b) (ZERO r))))))
(dk-peel!)
(fact 'ring-zero-in-ringoid-as-ring 'r)
(fact 'r7n-rmul-type 'r '(ZERO r) 'b)
(have! '(= ((ADD r) ((MUL r) (ZERO r) b) ((MUL r) (ZERO r) b)) ((MUL r) (ZERO r) b))
  (lambda ()
    (fact 'ring-right-dist-ringoid-as-ring 'r '(ZERO r) '(ZERO r) 'b)
    (subst '(= ((ADD r) ((MUL r) (ZERO r) b) ((MUL r) (ZERO r) b))
               ((MUL r) ((ADD r) (ZERO r) (ZERO r)) b)))
    (fact 'ring-add-left-id-ringoid-as-ring 'r '(ZERO r))
    (subst '(= ((ADD r) (ZERO r) (ZERO r)) (ZERO r)))
    (rfl)))
(fact 'r7n-radd-idem-zero 'r '((MUL r) (ZERO r) b))
(ass)
(r7n-qed! 'r7n-rzero-mul-left)

;;; ---- a.0 = 0 ----------------------------------------------------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a) '((IN a (CARR r)))
    '(= ((MUL r) a (ZERO r)) (ZERO r))))))
(dk-peel!)
(fact 'ring-zero-in-ringoid-as-ring 'r)
(fact 'r7n-rmul-type 'r 'a '(ZERO r))
(have! '(= ((ADD r) ((MUL r) a (ZERO r)) ((MUL r) a (ZERO r))) ((MUL r) a (ZERO r)))
  (lambda ()
    (fact 'ring-left-dist-ringoid-as-ring 'r 'a '(ZERO r) '(ZERO r))
    (subst '(= ((ADD r) ((MUL r) a (ZERO r)) ((MUL r) a (ZERO r)))
               ((MUL r) a ((ADD r) (ZERO r) (ZERO r)))))
    (fact 'ring-add-left-id-ringoid-as-ring 'r '(ZERO r))
    (subst '(= ((ADD r) (ZERO r) (ZERO r)) (ZERO r)))
    (rfl)))
(fact 'r7n-radd-idem-zero 'r '((MUL r) a (ZERO r)))
(ass)
(r7n-qed! 'r7n-rmul-zero-right)

;;; ---- (-a).b = -(a.b) --------------------------------------------------
;;; a.b + (-a).b = (a + -a).b = 0.b = 0, and inverses are unique
;;; (r6b-rinv-unique, rake-ringoid-additive.scm).
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(= ((MUL r) ((NEG r) a) b) ((NEG r) ((MUL r) a b)))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'a)
(fact 'r7n-rmul-type 'r 'a 'b)
(fact 'r7n-rmul-type 'r '((NEG r) a) 'b)
(have! '(= ((ADD r) ((MUL r) a b) ((MUL r) ((NEG r) a) b)) (ZERO r))
  (lambda ()
    (fact 'ring-right-dist-ringoid-as-ring 'r 'a '((NEG r) a) 'b)
    (subst '(= ((ADD r) ((MUL r) a b) ((MUL r) ((NEG r) a) b))
               ((MUL r) ((ADD r) a ((NEG r) a)) b)))
    (fact 'ringoid-add-right-inv 'r 'a)
    (subst '(= ((ADD r) a ((NEG r) a)) (ZERO r)))
    (fact 'r7n-rzero-mul-left 'r 'b)
    (ass)))
(fact 'r6b-rinv-unique 'r '((MUL r) a b) '((MUL r) ((NEG r) a) b))
(ass)
(r7n-qed! 'r7n-rneg-mul-left)

;;; ---- a.(-b) = -(a.b) --------------------------------------------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(= ((MUL r) a ((NEG r) b)) ((NEG r) ((MUL r) a b)))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'b)
(fact 'r7n-rmul-type 'r 'a 'b)
(fact 'r7n-rmul-type 'r 'a '((NEG r) b))
(have! '(= ((ADD r) ((MUL r) a b) ((MUL r) a ((NEG r) b))) (ZERO r))
  (lambda ()
    (fact 'ring-left-dist-ringoid-as-ring 'r 'a 'b '((NEG r) b))
    (subst '(= ((ADD r) ((MUL r) a b) ((MUL r) a ((NEG r) b)))
               ((MUL r) a ((ADD r) b ((NEG r) b)))))
    (fact 'ringoid-add-right-inv 'r 'b)
    (subst '(= ((ADD r) b ((NEG r) b)) (ZERO r)))
    (fact 'r7n-rmul-zero-right 'r 'a)
    (ass)))
(fact 'r6b-rinv-unique 'r '((MUL r) a b) '((MUL r) a ((NEG r) b)))
(ass)
(r7n-qed! 'r7n-rmul-neg-right)

;;; ---- a.b - u.v = (a-u).b + u.(b-v) ------------------------------------
;;; THE identity a congruence modulo a TWO-SIDED ideal needs: distribute each
;;; factor over the difference, then telescope at (a.b, u.b, u.v).
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b u v)
      '((IN a (CARR r)) (IN b (CARR r)) (IN u (CARR r)) (IN v (CARR r)))
    '(= ((ADD r) ((MUL r) a b) ((NEG r) ((MUL r) u v)))
        ((ADD r) ((MUL r) ((ADD r) a ((NEG r) u)) b)
                 ((MUL r) u ((ADD r) b ((NEG r) v)))))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'u)
(fact 'r6b-rneg-type 'r 'v)
(fact 'r7n-rmul-type 'r 'a 'b)
(fact 'r7n-rmul-type 'r 'u 'b)
(fact 'r7n-rmul-type 'r 'u 'v)
(fact 'ring-right-dist-ringoid-as-ring 'r 'a '((NEG r) u) 'b)
(subst '(= ((MUL r) ((ADD r) a ((NEG r) u)) b)
           ((ADD r) ((MUL r) a b) ((MUL r) ((NEG r) u) b))))
(fact 'r7n-rneg-mul-left 'r 'u 'b)
(subst '(= ((MUL r) ((NEG r) u) b) ((NEG r) ((MUL r) u b))))
(fact 'ring-left-dist-ringoid-as-ring 'r 'u 'b '((NEG r) v))
(subst '(= ((MUL r) u ((ADD r) b ((NEG r) v)))
           ((ADD r) ((MUL r) u b) ((MUL r) u ((NEG r) v)))))
(fact 'r7n-rmul-neg-right 'r 'u 'v)
(subst '(= ((MUL r) u ((NEG r) v)) ((NEG r) ((MUL r) u v))))
(fact 'ringoid-diff-telescope 'r '((MUL r) a b) '((MUL r) u b) '((MUL r) u v))
(fact 'eq-sym '((ADD r) ((ADD r) ((MUL r) a b) ((NEG r) ((MUL r) u b)))
                        ((ADD r) ((MUL r) u b) ((NEG r) ((MUL r) u v))))
              '((ADD r) ((MUL r) a b) ((NEG r) ((MUL r) u v))))
(ass)
(r7n-qed! 'r7n-rdiff-mul)

;;; ---- the two descended maps, as terms ---------------------------------
(define r7n-set '(RINGOID-SETOID r))
(define r7n-mul-lam                              ; rq-mul's right-hand map
  '(VNB-LAMBDA (LIST a b) (CARTESIAN (CARR r) (CARR r))
     (CLASS (RINGOID-SETOID r) ((MUL r) a b))))
(define r7n-mul-d2 (list 'DESCEND2 r7n-set r7n-mul-lam))
(define r7n-neg-lam                              ; rq-neg's right-hand map
  '(VNB-LAMBDA a (CARR r) (CLASS (RINGOID-SETOID r) ((NEG r) a))))
(define r7n-neg-d (list 'DESCEND r7n-set r7n-neg-lam))

;;; ---- the class-of-product map is a function into the quotient ----------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (list 'IN r7n-mul-lam
        (list 'FUN (list 'CARTESIAN '(PTS (RINGOID-SETOID r)) '(PTS (RINGOID-SETOID r)))
              '(QUOTIENT (RINGOID-SETOID r)))))))
(dk-peel!)
(fact 'ringoid-setoid-is-setoid 'r)
(fact 'ringoid-carr-in-set 'r)
(mac 'ringoid-setoid-pts)
(let ((ls (dk-opened (lambda () (lam-t)))))
  (dk-focus! (or (any-pred (lambda (n) (let ((g (dk-goal-of n)))
                                         (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
                           ls)
                 (error "rake-ringoid-quotient: no sethood leaf")))
  (mac 'cartesian-set-iff)
  (dk-conj-close! (lambda () (ass)))
  (dk-focus! (or (any-pred (lambda (n) (let ((g (dk-goal-of n)))
                                         (not (and (pair? g) (eq? (car g) 'IN)
                                                   (eq? (caddr g) 'SET)))))
                           ls)
                 (error "rake-ringoid-quotient: no pointwise leaf")))
  (dk-peel!)
  (let* ((g (dk-goal))                          ; (IN (CLASS s ((MUL r) x y)) (QUOTIENT s))
         (t (caddr (cadr g))))                  ; ((MUL r) x y)
    (fact 'r7n-rmul-type 'r (cadr t) (caddr t))
    (have! (list 'IN t '(PTS (RINGOID-SETOID r)))
           (lambda () (mac 'ringoid-setoid-pts) (ass)))
    (fact 'class-in-quotient r7n-set t)
    (ass)))
(r7n-qed! 'r7n-rq-mul-lam-type)

;;; ---- the class-of-product map respects the congruence ------------------
;;; The content: (a.b) - (u.v) = (a-u).b + u.(b-v) lands in IDL because the
;;; ideal is TWO-SIDED -- ringoid-ideal-mul-right on the first summand, -mul-left
;;; on the second, then ringoid-ideal-add.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (list 'RESPECTS2 r7n-set r7n-mul-lam))))
(dk-peel!)
(mac 'respects2-unfold)
(mac 'ringoid-setoid-pts)
(let ((landed (dk-peel!)))
  (dk-split-all! landed))
(let* ((g   (dk-goal))                          ; (= (lam x y) (lam u v))
       (l1  (cadr g)) (l2 (caddr g))
       (x   (cadr l1)) (y (caddr l1))
       (u   (cadr l2)) (v (caddr l2)))
  (fact 'r6b-related-out 'r x u)
  (fact 'r6b-related-out 'r y v)
  (fact 'r6b-rneg-type 'r u)
  (fact 'r6b-rneg-type 'r v)
  (fact 'r6b-radd-type 'r x (list '(NEG r) u))
  (fact 'r6b-radd-type 'r y (list '(NEG r) v))
  (fact 'r7n-rmul-type 'r x y)
  (fact 'r7n-rmul-type 'r u v)
  (fact 'ringoid-ideal-mul-right 'r (list '(ADD r) x (list '(NEG r) u)) y)
  (fact 'ringoid-ideal-mul-left  'r u (list '(ADD r) y (list '(NEG r) v)))
  (fact 'ringoid-ideal-add 'r
        (list '(MUL r) (list '(ADD r) x (list '(NEG r) u)) y)
        (list '(MUL r) u (list '(ADD r) y (list '(NEG r) v))))
  (fact 'r7n-rdiff-mul 'r x y u v)
  (have! (list 'IN (list '(ADD r) (list '(MUL r) x y)
                         (list '(NEG r) (list '(MUL r) u v)))
               '(IDL r))
         (lambda ()
           (subst (list '= (list '(ADD r) (list '(MUL r) x y)
                                 (list '(NEG r) (list '(MUL r) u v)))
                        (list '(ADD r)
                              (list '(MUL r) (list '(ADD r) x (list '(NEG r) u)) y)
                              (list '(MUL r) u (list '(ADD r) y (list '(NEG r) v))))))
           (ass)))
  (fact 'r6b-related-in 'r (list '(MUL r) x y) (list '(MUL r) u v))
  (lam-b)                                       ; reduces BOTH redexes
  (fact 'ringoid-setoid-is-setoid 'r)
  (have! (list 'IN (list '(MUL r) x y) '(PTS (RINGOID-SETOID r)))
         (lambda () (mac 'ringoid-setoid-pts) (ass)))
  (have! (list 'IN (list '(MUL r) u v) '(PTS (RINGOID-SETOID r)))
         (lambda () (mac 'ringoid-setoid-pts) (ass)))
  (fact 'class-eq-iff r7n-set (list '(MUL r) x y) (list '(MUL r) u v))
  (let ((iff (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IFF))) "the class-eq iff"))
        (rel (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'RELATED)
                                       (pair? (caddr f)) (equal? (car (caddr f)) '(MUL r))))
                      "the RELATED conclusion")))
    (dk-only! iff rel)
    (prop)))
(r7n-qed! 'r7n-mul-respects2)

;;; =====================================================================
;;; rq-mul-computes.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(r) '((IS-RINGOID r))
    (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
      '(= ((MUL (RINGOID-QUOTIENT-RING r))
           (CLASS (RINGOID-SETOID r) a) (CLASS (RINGOID-SETOID r) b))
          (CLASS (RINGOID-SETOID r) ((MUL r) a b)))))))
(dk-peel!)
(fact 'ringoid-setoid-is-setoid 'r)
(fact 'r7n-rq-mul-lam-type 'r)
(fact 'r7n-mul-respects2 'r)
(have! '(IN a (PTS (RINGOID-SETOID r))) (lambda () (mac 'ringoid-setoid-pts) (ass)))
(have! '(IN b (PTS (RINGOID-SETOID r))) (lambda () (mac 'ringoid-setoid-pts) (ass)))
(fact 'rq-mul 'r)
(subst (list '== '(MUL (RINGOID-QUOTIENT-RING r)) r7n-mul-d2))
(let ((e (dk-fact! 'descend2-computes r7n-set '(QUOTIENT (RINGOID-SETOID r)) r7n-mul-lam 'a 'b)))
  (lam-b-h e)
  (ass))
(r7n-qed! 'rq-mul-computes)

;;; ---- the class-of-negative map is a function into the quotient ---------
;;; The unary twin: `lam-t' opens the pointwise typing and the SETHOOD of the
;;; domain, which here is CARR(r) itself (ringoid-carr-in-set), not a CARTESIAN.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (list 'IN r7n-neg-lam
        (list 'FUN '(PTS (RINGOID-SETOID r)) '(QUOTIENT (RINGOID-SETOID r)))))))
(dk-peel!)
(fact 'ringoid-setoid-is-setoid 'r)
(fact 'ringoid-carr-in-set 'r)
(mac 'ringoid-setoid-pts)
(let ((ls (dk-opened (lambda () (lam-t)))))
  (dk-focus! (or (any-pred (lambda (n) (let ((g (dk-goal-of n)))
                                         (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
                           ls)
                 (error "rake-ringoid-quotient: no sethood leaf")))
  (ass)
  (dk-focus! (or (any-pred (lambda (n) (let ((g (dk-goal-of n)))
                                         (not (and (pair? g) (eq? (car g) 'IN)
                                                   (eq? (caddr g) 'SET)))))
                           ls)
                 (error "rake-ringoid-quotient: no pointwise leaf")))
  (dk-peel!)
  (let* ((g (dk-goal))                          ; (IN (CLASS s ((NEG r) x)) (QUOTIENT s))
         (t (caddr (cadr g))))                  ; ((NEG r) x)
    (fact 'r6b-rneg-type 'r (cadr t))
    (have! (list 'IN t '(PTS (RINGOID-SETOID r)))
           (lambda () (mac 'ringoid-setoid-pts) (ass)))
    (fact 'class-in-quotient r7n-set t)
    (ass)))
(r7n-qed! 'r7n-rq-neg-lam-type)

;;; ---- the class-of-negative map respects the congruence -----------------
;;; (-x) - (-y) = y - x = -(x - y): ringoid-ideal-neg on the congruence, then
;;; ringoid-neg-diff and r6b-rneg-neg put it in the shape r6b-related-in wants.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (list 'RESPECTS r7n-set r7n-neg-lam))))
(dk-peel!)
(mac 'respects-unfold)
(mac 'ringoid-setoid-pts)
(dk-peel!)
(let* ((g   (dk-goal))                          ; (= (lam x) (lam y))
       (x   (cadr (cadr g)))
       (y   (cadr (caddr g))))
  (fact 'r6b-related-out 'r x y)
  (fact 'r6b-rneg-type 'r x)
  (fact 'r6b-rneg-type 'r y)
  (fact 'r6b-radd-type 'r x (list '(NEG r) y))
  (fact 'ringoid-ideal-neg 'r (list '(ADD r) x (list '(NEG r) y)))
  (fact 'ringoid-neg-diff 'r x y)
  (fact 'r6b-rneg-neg 'r y)
  (fact 'ring-add-comm-ringoid-as-ring 'r (list '(NEG r) x) y)
  (have! (list 'IN (list '(ADD r) (list '(NEG r) x)
                         (list '(NEG r) (list '(NEG r) y)))
               '(IDL r))
         (lambda ()
           (subst (list '= (list '(NEG r) (list '(NEG r) y)) y))
           (subst (list '= (list '(ADD r) (list '(NEG r) x) y)
                           (list '(ADD r) y (list '(NEG r) x))))
           (subst (list '= (list '(ADD r) y (list '(NEG r) x))
                           (list '(NEG r) (list '(ADD r) x (list '(NEG r) y)))))
           (ass)))
  (fact 'r6b-related-in 'r (list '(NEG r) x) (list '(NEG r) y))
  (lam-b)
  (fact 'ringoid-setoid-is-setoid 'r)
  (have! (list 'IN (list '(NEG r) x) '(PTS (RINGOID-SETOID r)))
         (lambda () (mac 'ringoid-setoid-pts) (ass)))
  (have! (list 'IN (list '(NEG r) y) '(PTS (RINGOID-SETOID r)))
         (lambda () (mac 'ringoid-setoid-pts) (ass)))
  (fact 'class-eq-iff r7n-set (list '(NEG r) x) (list '(NEG r) y))
  (let ((iff (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IFF))) "the class-eq iff"))
        (rel (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'RELATED)
                                       (pair? (caddr f)) (equal? (car (caddr f)) '(NEG r))))
                      "the RELATED conclusion")))
    (dk-only! iff rel)
    (prop)))
(r7n-qed! 'r7n-neg-respects)

;;; =====================================================================
;;; rq-neg-computes.  descend-computes packs its two hypotheses into ONE
;;; conjunctive antecedent (rake-setoid2.scm), which `fact' will not split --
;;; hence the AND is assembled by `have!' before the citation.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(r) '((IS-RINGOID r))
    (forall-guarded '(a) '((IN a (CARR r)))
      '(= ((NEG (RINGOID-QUOTIENT-RING r)) (CLASS (RINGOID-SETOID r) a))
          (CLASS (RINGOID-SETOID r) ((NEG r) a)))))))
(dk-peel!)
(fact 'ringoid-setoid-is-setoid 'r)
(fact 'r7n-rq-neg-lam-type 'r)
(fact 'r7n-neg-respects 'r)
(have! '(IN a (PTS (RINGOID-SETOID r))) (lambda () (mac 'ringoid-setoid-pts) (ass)))
(have! (list 'AND
             (list 'IN r7n-neg-lam
                   (list 'FUN '(PTS (RINGOID-SETOID r)) '(QUOTIENT (RINGOID-SETOID r))))
             (list 'RESPECTS r7n-set r7n-neg-lam))
       (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'rq-neg 'r)
(subst (list '== '(NEG (RINGOID-QUOTIENT-RING r)) r7n-neg-d))
(let ((e (dk-fact! 'descend-computes r7n-set '(QUOTIENT (RINGOID-SETOID r)) r7n-neg-lam 'a)))
  (lam-b-h e)
  (ass))
(r7n-qed! 'rq-neg-computes)

;;; =====================================================================
;;; ringoid-quotient-is-ring -- R/I is a ring.
;;; Statement copied from structure-library/ringoid.scm:153 unchanged.
;;;
;;; The shape is mat-ring-proof.scm's: unfold the auto-generated IS-RING iff
;;; into its 14 conjuncts (a length clause, six slot typings, seven property
;;; clauses), split, and discharge each on its own leaf.  What is different --
;;; and what the ten hand-written instances of ringoid-quotient-ring-proof.scm
;;; would have been -- is that the elements of the carrier are CLASSES, so a law
;;; conjunct is not a citation but a COMPUTE-DOWN:
;;;
;;;   quotient-rep gives each quotient variable a representative and rewrites it
;;;   to that representative's class (r7n-rep!); rq-add-computes / -mul- / -neg-
;;;   then push every descended operation through the class map, innermost
;;;   first, typing each intermediate result as it goes (r7n-compute-down!);
;;;   the leaf is then [X] = [Y] for two ring terms in the representatives, and
;;;   the ring's OWN law -- ring-*-ringoid-as-ring, the view companions -- makes
;;;   X and Y the same term (r7n-close!).
;;;
;;; So one driver serves all seven laws and the per-conjunct data is just the
;;; list of ring laws to land.  The three read-offs rq-zero / rq-one / rq-carr
;;; are fired only where the goal holds the term, so no `mac' declines.
;;; =====================================================================

(define r7n-rqr '(RINGOID-QUOTIENT-RING r))
(define r7n-add-lam                              ; rq-add's right-hand map
  '(VNB-LAMBDA (LIST a b) (CARTESIAN (CARR r) (CARR r))
     (CLASS (RINGOID-SETOID r) ((ADD r) a b))))
(define (r7n-quot) (list 'QUOTIENT r7n-set))

(define (r7n-leaves) (proof-leaves))
(define (r7n-focus! pred)
  (let lp ((ls (r7n-leaves)))
    (cond ((null? ls) (error "rake-ringoid-quotient: no open leaf matches"))
          ((pred (dk-goal-of (car ls))) (dk-focus! (car ls)) (car ls))
          (#t (lp (cdr ls))))))
(define (r7n-is? h oph)
  (lambda (g) (and (pair? g) (eq? (car g) h)
                   (let ((a1 (cadr g))) (and (pair? a1) (eq? (car a1) oph))))))

(define (r7n-all? p l) (cond ((null? l) #t) ((p (car l)) (r7n-all? p (cdr l))) (#t #f)))
(define (r7n-class? t) (and (pair? t) (eq? (car t) 'CLASS) (equal? (cadr t) r7n-set)))
(define (r7n-subterm? f pred)
  (cond ((pred f) #t)
        ((pair? f) (let lp ((l f)) (cond ((null? l) #f)
                                         ((r7n-subterm? (car l) pred) #t)
                                         (#t (lp (cdr l))))))
        (#t #f)))
(define (r7n-acc? acc) (lambda (t) (and (pair? t) (eq? (car t) acc) (pair? (cdr t))
                                        (equal? (cadr t) r7n-rqr))))
(define (r7n-redex? f)
  (and (pair? f) (pair? (car f)) (memq (caar f) '(ADD MUL NEG))
       (pair? (cdr (car f))) (equal? (cadr (car f)) r7n-rqr)
       (r7n-all? r7n-class? (cdr f))))
;;; innermost redex first: a descended operation all of whose arguments are
;;; already classes.
(define (r7n-find-redex f)
  (and (pair? f)
       (or (let lp ((l (cdr f)))
             (cond ((null? l) #f)
                   ((r7n-find-redex (car l)) => (lambda (x) x))
                   (#t (lp (cdr l)))))
           (and (r7n-redex? f) f))))

(define (r7n-flatten f)
  (if (pair? f)
      (let lp ((l f) (acc '()))
        (if (null? l) acc (lp (cdr l) (append acc (r7n-flatten (car l))))))
      (list f)))

;;; the quotient-typed variables of the current goal, in first-occurrence order
;;; (read off the GOAL, never off the context: dk-asms order is not the peel
;;; order and the ring laws are not symmetric in their arguments).
(define (r7n-goal-vars)
  (let ((cands (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                  (symbol? (cadr f))
                                                  (equal? (caddr f) (r7n-quot))))
                                 (dk-asms)))))
    (delete-duplicates (filter (lambda (s) (memq s cands)) (r7n-flatten (dk-goal))))))

;;; x |-> a representative p with x = [p], the goal rewritten and (IN p (CARR r))
;;; in context (mac-h converts the PTS typing quotient-rep lands; it REPLACES it,
;;; which is what we want -- nothing below needs the PTS form).
(define (r7n-rep! x)
  (let* ((ex (dk-fact! 'quotient-rep r7n-set x))
         (p  (dk-skolem! ex)))
    (mac-h 'ringoid-setoid-pts (list 'IN p '(PTS (RINGOID-SETOID r))))
    (subst (list '= x (list 'CLASS r7n-set p)))
    p))

;;; push every descended operation through the class map, innermost first.
(define (r7n-compute-down!)
  (let lp ((n 0))
    (if (> n 40) (error "r7n-compute-down!: runaway"))
    (let ((rx (r7n-find-redex (dk-goal))))
      (if rx
          (let* ((op   (caar rx))
                 (args (map caddr (cdr rx)))       ; the representatives
                 (res  (cons (list op 'r) args)))
            (cond ((eq? op 'ADD) (fact 'r6b-radd-type 'r (car args) (cadr args))
                                 (fact 'rq-add-computes 'r (car args) (cadr args)))
                  ((eq? op 'MUL) (fact 'r7n-rmul-type 'r (car args) (cadr args))
                                 (fact 'rq-mul-computes 'r (car args) (cadr args)))
                  (#t            (fact 'r6b-rneg-type 'r (car args))
                                 (fact 'rq-neg-computes 'r (car args))))
            (subst (list '= rx (list 'CLASS r7n-set res)))
            (lp (+ n 1)))))))

;;; [X] = [Y] with X = Y already in context (in either orientation): rewrite and
;;; close.  The class of a typed element is typed, which is what `rfl' wants.
(define (r7n-close!)
  (let ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) '=) (r7n-class? (cadr g)) (r7n-class? (caddr g))))
        (error "r7n-close!: not a class equation" (expression->string g)))
    (let ((x (caddr (cadr g))) (y (caddr (caddr g))))
      (have! (list 'IN y '(PTS (RINGOID-SETOID r)))
             (lambda () (mac 'ringoid-setoid-pts) (ass)))
      (fact 'class-in-quotient r7n-set y)
      (if (not (equal? x y)) (subst (list '= x y)))
      (rfl))))

;;; one property conjunct: unfold it, read the carrier off, decompose to atomic
;;; equations, and on each -- representatives, compute down, land the ring laws,
;;; close.  FACTERS take the representative list.
(define (r7n-conj! prop facters)
  (mac prop)
  (mac 'rq-carr)
  (let* ((focus  (proof-state-focus *ps*))
         (before (filter (lambda (l) (not (eq? l focus))) (r7n-leaves)))
         (mine   (lambda () (filter (lambda (l) (not (memq l before))) (r7n-leaves)))))
    (let lp ()
      (let ((ds (filter (lambda (l) (let ((g (dk-goal-of l)))
                                      (and (pair? g) (memq (car g) '(FORALL IMPLIES AND)))))
                        (mine))))
        (if (pair? ds) (begin (dk-focus! (car ds)) (di) (lp)))))
    (for-each (lambda (lf)
                (dk-focus! lf)
                (let ((reps (map r7n-rep! (r7n-goal-vars))))
                  (if (r7n-subterm? (dk-goal) (r7n-acc? 'ZERO)) (mac 'rq-zero))
                  (if (r7n-subterm? (dk-goal) (r7n-acc? 'ONE))  (mac 'rq-one))
                  (r7n-compute-down!)
                  (for-each (lambda (f) (f reps)) facters))
                (r7n-close!))
              (mine))))

;;; ---------------------------------------------------------------------
(sp (make-wff '(FORALL r (IMPLIES (IS-RINGOID r) (IS-RING (RINGOID-QUOTIENT-RING r))))))
;; IS-RINGOID is a PREDICATE, not a typing, so the universal is UNGUARDED: one
;; `di' peels the quantifier and lands nothing.  dk-peel! loops until the head
;; changes (the first draft used a single `di' and mac'd IS-RING under a still
;; standing IMPLIES, so the conjunct split found nothing to split).
(dk-peel!)
;; landed once, above the split, so every one of the 14 leaves inherits them
(fact 'ringoid-setoid-is-setoid 'r)
(fact 'ringoid-carr-in-set 'r)
(fact 'ring-zero-in-ringoid-as-ring 'r)
(fact 'r7n-rone-type 'r)
(fact 'r6b-rq-add-lam-type 'r)
(fact 'r6b-add-respects2 'r)
(fact 'r7n-rq-mul-lam-type 'r)
(fact 'r7n-mul-respects2 'r)
(fact 'r7n-rq-neg-lam-type 'r)
(fact 'r7n-neg-respects 'r)
(mac 'IS-RING)
;; split the right-nested 14-conjunct AND into one leaf per conjunct
(let lp ()
  (let ((l (any-pred (lambda (nd) (let ((g (dk-goal-of nd)))
                                    (and (pair? g) (eq? (car g) 'AND))))
                     (r7n-leaves))))
    (if l (begin (dk-focus! l) (di) (lp)))))

;; ---- 1. length(ringoid-quotient-ring(r)) = 6 ----
(r7n-focus! (r7n-is? '= 'LENGTH))
(mac 'RINGOID-QUOTIENT-RING)
(len-r)
(rfl)

;; ---- 2. the carrier is a set ----
(r7n-focus! (r7n-is? 'IN 'CARR))
(mac 'rq-carr)
(fact 'quotient-is-set r7n-set)
(ass)

;; ---- 3. ADD is a function on the quotient ----
(r7n-focus! (r7n-is? 'IN 'ADD))
(mac 'rq-carr)
(mac 'rq-add)
(fact 'descend2-in-fun r7n-set (r7n-quot) r7n-add-lam)
(ass)

;; ---- 4. MUL is a function on the quotient ----
(r7n-focus! (r7n-is? 'IN 'MUL))
(mac 'rq-carr)
(mac 'rq-mul)
(fact 'descend2-in-fun r7n-set (r7n-quot) r7n-mul-lam)
(ass)

;; ---- 5. NEG is a function on the quotient (descend-in-fun packs its two
;;         hypotheses into one AND antecedent) ----
(r7n-focus! (r7n-is? 'IN 'NEG))
(mac 'rq-carr)
(mac 'rq-neg)
(have! (list 'AND
             (list 'IN r7n-neg-lam (list 'FUN '(PTS (RINGOID-SETOID r)) (r7n-quot)))
             (list 'RESPECTS r7n-set r7n-neg-lam))
       (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'descend-in-fun r7n-set (r7n-quot) r7n-neg-lam)
(ass)

;; ---- 6. [0] is in the quotient ----
(r7n-focus! (r7n-is? 'IN 'ZERO))
(mac 'rq-carr)
(mac 'rq-zero)
(have! '(IN (ZERO r) (PTS (RINGOID-SETOID r)))
       (lambda () (mac 'ringoid-setoid-pts) (ass)))
(fact 'class-in-quotient r7n-set '(ZERO r))
(ass)

;; ---- 7. [1] is in the quotient ----
(r7n-focus! (r7n-is? 'IN 'ONE))
(mac 'rq-carr)
(mac 'rq-one)
(have! '(IN (ONE r) (PTS (RINGOID-SETOID r)))
       (lambda () (mac 'ringoid-setoid-pts) (ass)))
(fact 'class-in-quotient r7n-set '(ONE r))
(ass)

;; ---- 8. addition is associative ----
(r7n-focus! (r7n-is? 'is-associative 'ADD))
(r7n-conj! 'is-associative
  (list (lambda (v) (fact 'ring-add-assoc-ringoid-as-ring 'r (car v) (cadr v) (caddr v)))))

;; ---- 9. addition is commutative ----
(r7n-focus! (r7n-is? 'is-commutative 'ADD))
(r7n-conj! 'is-commutative
  (list (lambda (v) (fact 'ring-add-comm-ringoid-as-ring 'r (car v) (cadr v)))))

;; ---- 10. [0] is the additive identity ----
(r7n-focus! (r7n-is? 'is-identity 'ADD))
(r7n-conj! 'is-identity
  (list (lambda (v) (fact 'ring-add-left-id-ringoid-as-ring 'r (car v)))
        (lambda (v) (fact 'r6b-radd-right-id 'r (car v)))))

;; ---- 11. [-a] is the additive inverse of [a] ----
(r7n-focus! (r7n-is? 'has-inverses 'ADD))
(r7n-conj! 'has-inverses
  (list (lambda (v) (fact 'ring-add-left-inv-ringoid-as-ring 'r (car v)))
        (lambda (v) (fact 'ringoid-add-right-inv 'r (car v)))))

;; ---- 12. multiplication is associative ----
(r7n-focus! (r7n-is? 'is-associative 'MUL))
(r7n-conj! 'is-associative
  (list (lambda (v) (fact 'ring-mul-assoc-ringoid-as-ring 'r (car v) (cadr v) (caddr v)))))

;; ---- 13. [1] is the multiplicative identity ----
(r7n-focus! (r7n-is? 'is-identity 'MUL))
(r7n-conj! 'is-identity
  (list (lambda (v) (fact 'ring-mul-left-id-ringoid-as-ring 'r (car v)))
        (lambda (v) (fact 'ring-mul-right-id-ringoid-as-ring 'r (car v)))))

;; ---- 14. multiplication distributes over addition ----
(r7n-focus! (r7n-is? 'is-distributive 'ADD))
(r7n-conj! 'is-distributive
  (list (lambda (v) (fact 'ring-left-dist-ringoid-as-ring 'r (car v) (cadr v) (caddr v)))
        (lambda (v) (fact 'ring-right-dist-ringoid-as-ring 'r (car v) (cadr v) (caddr v)))))

(r7n-qed! 'ringoid-quotient-is-ring)
