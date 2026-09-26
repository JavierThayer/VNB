;;; rake-ringoid-additive.scm -- the additive group of a RINGOID, proven.
;;;
;;; WHY THIS FILE EXISTS, and why it is not part of rake-ringoid.scm.  The
;;; assignment was `rq-add-computes' (structure-library/ringoid.scm:139), which
;;; needs `ringoid-setoid-is-setoid' (theorem-library/ringoid-setoid-proof.scm,
;;; load position 495) and so must load BELOW it.  But that theorem's own bill is
;;; {ringoid-neg-diff, ringoid-diff-telescope} -- two asserted `well-known'
;;; supports in ringoid.scm, warranted there with "crs normalizes surface +/* but
;;; does NOT reach a structure's abstract (ADD s)/(NEG s)".  That is true of `crs'
;;; and irrelevant: the two identities are four rewrites each off the ringoid's
;;; OWN additive laws, which the RINGOID-AS-RING view already states at (ADD r) /
;;; (NEG r) directly (ring-add-assoc-ringoid-as-ring and its four siblings,
;;; installed `definitional' by view-as-auto-specialize! when ringoid.scm loads).
;;; So the two supports are provable, and proving them ABOVE position 495 is what
;;; takes ringoid-rel-is-equivalence, ringoid-setoid-is-setoid and hence
;;; rq-add-computes to `modulo 0'.  Hence a second file, and this one is it.
;;;
;;; WHAT IS HERE.  The additive-group facts a ringoid never had, each the exact
;;; twin of a proven RING fact (theorem-library/rake-algebra2.scm) with (ADD r) /
;;; (NEG r) / (ZERO r) / (CARR r) in place of a ring's:
;;;
;;;   r6b-radd-type          (ADD r)(a,b) in CARR(r)       -- IS-RINGOID's own
;;;   r6b-rneg-type          (NEG r)(a)   in CARR(r)          FUN typings, through
;;;                                                           apply-tupling-2
;;;   r6b-radd-right-id      a + 0 = a
;;;   r6b-radd-interchange   (a+b)+(c+d) = (a+c)+(b+d)     -- assoc/comm, 5 steps
;;;   r6b-rinv-unique        a + b = 0  =>  b = -a
;;;   r6b-rneg-neg           -(-a) = a
;;;   r6b-rneg-add           -(a+b) = (-a)+(-b)
;;;   r6b-rdiff-add          (a+b) - (u+v) = (a-u) + (b-v)  -- what a congruence
;;;                                                           on an ideal needs
;;;   ringoid-neg-diff       -(a-b) = b-a                  -- WAS a support,
;;;   ringoid-diff-telescope (a-b)+(b-c) = a-c                ringoid.scm:219,224
;;;
;;; The last two are stated here BYTE-IDENTICALLY to the supports they replace
;;; (the `forall-guarded' call is copied), so install-theorem! reports
;;; "re-installing the same statement" and every citer is unaffected.
;;;
;;; LOAD WINDOW [165, 495).
;;;   lo = 165: the latest citation is `pair-in-cartesian'
;;;             (theorem-library/pair-tuple-sethood, 164).  Then fun-apply-type-c
;;;             (theorem-library/fun-apply-type-proof, 162), eq-sym
;;;             (theorem-library/equality-basics, 148), apply-tupling-2
;;;             (theorem-library/axioms, 15) and everything the RINGOID
;;;             declaration installs (structure-library/ringoid, 26).
;;;   hi = 495: theorem-library/ringoid-setoid-proof cites ringoid-neg-diff and
;;;             ringoid-diff-telescope; the supports are retired, so the theorems
;;;             must already be installed when it loads.
;;;
;;; Helper prefix: r6b-.

(define (r6b-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'algebra))
      (begin
        (display "\n*** rake-ringoid-additive: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-ringoid-additive: unfinished" name))))

;;; ---- ADD closes on the carrier ---------------------------------------
;;; The IS-RINGOID unfold gives (ADD r) in FUN(CARTESIAN(CARR,CARR), CARR); a
;;; structure operation eats a PAIR while the parser writes (f a b), so the
;;; apply-tupling-2 bridge comes first (op-typing.scm's driver).  The unfold is
;;; done in a `have!' LANE: mac-h REPLACES the hypothesis, and every later
;;; citation here is guarded on IS-RINGOID.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(IN ((ADD r) a b) (CARR r))))))
(dk-peel!)
(have! '(IN (ADD r) (FUN (CARTESIAN (CARR r) (CARR r)) (CARR r)))
  (lambda ()
    (let ((u (dk-landed-1 (lambda () (mac-h 'IS-RINGOID '(IS-RINGOID r))))))
      (dk-split-all! (list u)))
    (ass)))
(fact 'apply-tupling-2 '(ADD r) 'a 'b)
(subst '(== ((ADD r) a b) ((ADD r) (LIST a b))))
(fact 'pair-in-cartesian '(CARR r) '(CARR r) 'a 'b)
(fact 'fun-apply-type-c '(ADD r) '(CARTESIAN (CARR r) (CARR r)) '(CARR r) '(LIST a b))
(ass)
(r6b-qed! 'r6b-radd-type)

;;; ---- NEG closes on the carrier ---------------------------------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a) '((IN a (CARR r)))
    '(IN ((NEG r) a) (CARR r))))))
(dk-peel!)
(have! '(IN (NEG r) (FUN (CARR r) (CARR r)))
  (lambda ()
    (let ((u (dk-landed-1 (lambda () (mac-h 'IS-RINGOID '(IS-RINGOID r))))))
      (dk-split-all! (list u)))
    (ass)))
(fact 'fun-apply-type-c '(NEG r) '(CARR r) '(CARR r) 'a)
(ass)
(r6b-qed! 'r6b-rneg-type)

;;; ---- a + 0 = a -------------------------------------------------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a) '((IN a (CARR r)))
    '(= ((ADD r) a (ZERO r)) a)))))
(dk-peel!)
(fact 'ring-zero-in-ringoid-as-ring 'r)
(fact 'ring-add-comm-ringoid-as-ring 'r 'a '(ZERO r))
(fact 'ring-add-left-id-ringoid-as-ring 'r 'a)
(subst '(= ((ADD r) a (ZERO r)) ((ADD r) (ZERO r) a)))
(ass)
(r6b-qed! 'r6b-radd-right-id)

;;; ---- (a+b)+(c+d) = (a+c)+(b+d) ---------------------------------------
;;; There is no abelian-group normalizer that reaches a structure's operation
;;; (`crs' is commutative RINGS on the surface operators), so the interchange is
;;; hand-chained: assoc right, re-associate the middle, commute b and c,
;;; re-associate back.  Only the second step needs turning round (eq-sym); the
;;; last rewrites the goal's RIGHT side, after which both sides are the same term.
;;; Every intermediate sum is typed first -- instantiation owes definedness.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b c d)
      '((IN a (CARR r)) (IN b (CARR r)) (IN c (CARR r)) (IN d (CARR r)))
    '(= ((ADD r) ((ADD r) a b) ((ADD r) c d))
        ((ADD r) ((ADD r) a c) ((ADD r) b d)))))))
(dk-peel!)
(fact 'r6b-radd-type 'r 'a 'b)
(fact 'r6b-radd-type 'r 'c 'd)
(fact 'r6b-radd-type 'r 'b 'c)
(fact 'r6b-radd-type 'r 'c 'b)
(fact 'r6b-radd-type 'r 'b 'd)
(fact 'r6b-radd-type 'r 'a 'c)
(fact 'r6b-radd-type 'r 'b '((ADD r) c d))
(fact 'r6b-radd-type 'r '((ADD r) b c) 'd)
(fact 'r6b-radd-type 'r '((ADD r) c b) 'd)
(fact 'r6b-radd-type 'r 'c '((ADD r) b d))
(fact 'ring-add-assoc-ringoid-as-ring 'r 'a 'b '((ADD r) c d))
(subst '(= ((ADD r) ((ADD r) a b) ((ADD r) c d))
           ((ADD r) a ((ADD r) b ((ADD r) c d)))))
(fact 'ring-add-assoc-ringoid-as-ring 'r 'b 'c 'd)
(fact 'eq-sym '((ADD r) ((ADD r) b c) d) '((ADD r) b ((ADD r) c d)))
(subst '(= ((ADD r) b ((ADD r) c d)) ((ADD r) ((ADD r) b c) d)))
(fact 'ring-add-comm-ringoid-as-ring 'r 'b 'c)
(subst '(= ((ADD r) b c) ((ADD r) c b)))
(fact 'ring-add-assoc-ringoid-as-ring 'r 'c 'b 'd)
(subst '(= ((ADD r) ((ADD r) c b) d) ((ADD r) c ((ADD r) b d))))
(fact 'ring-add-assoc-ringoid-as-ring 'r 'a 'c '((ADD r) b d))
(subst '(= ((ADD r) ((ADD r) a c) ((ADD r) b d))
           ((ADD r) a ((ADD r) c ((ADD r) b d)))))
(rfl)
(r6b-qed! 'r6b-radd-interchange)

;;; ---- a + b = 0 forces b = -a -----------------------------------------
;;; b = 0 + b = ((-a) + a) + b = (-a) + (a + b) = (-a) + 0 = -a.
;;; rake-algebra2.scm's ring-add-inverse-unique, verbatim at the ringoid.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(IMPLIES (= ((ADD r) a b) (ZERO r)) (= b ((NEG r) a)))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'a)
(fact 'ring-add-left-id-ringoid-as-ring 'r 'b)
(fact 'ring-add-left-inv-ringoid-as-ring 'r 'a)
(fact 'ring-add-assoc-ringoid-as-ring 'r '((NEG r) a) 'a 'b)
(fact 'r6b-radd-right-id 'r '((NEG r) a))
(subst '(= b ((ADD r) (ZERO r) b)))
(subst '(= (ZERO r) ((ADD r) ((NEG r) a) a)))
(subst '(= ((ADD r) ((ADD r) ((NEG r) a) a) b) ((ADD r) ((NEG r) a) ((ADD r) a b))))
(subst '(= ((ADD r) a b) (ZERO r)))
(subst '(= ((ADD r) ((NEG r) a) (ZERO r)) ((NEG r) a)))
(rfl)
(r6b-qed! 'r6b-rinv-unique)

;;; ---- -(a+b) = (-a) + (-b) --------------------------------------------
;;; (a+b) + ((-a)+(-b)) = (a + -a) + (b + -b) = 0 + 0 = 0 by the interchange,
;;; and inverses are unique.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(= ((NEG r) ((ADD r) a b)) ((ADD r) ((NEG r) a) ((NEG r) b)))))))
(dk-peel!)
(fact 'ring-zero-in-ringoid-as-ring 'r)
(fact 'r6b-rneg-type 'r 'a)
(fact 'r6b-rneg-type 'r 'b)
(fact 'r6b-radd-type 'r 'a 'b)
(fact 'r6b-radd-type 'r '((NEG r) a) '((NEG r) b))
(have! '(= ((ADD r) ((ADD r) a b) ((ADD r) ((NEG r) a) ((NEG r) b))) (ZERO r))
  (lambda ()
    (fact 'r6b-radd-interchange 'r 'a 'b '((NEG r) a) '((NEG r) b))
    (subst '(= ((ADD r) ((ADD r) a b) ((ADD r) ((NEG r) a) ((NEG r) b)))
               ((ADD r) ((ADD r) a ((NEG r) a)) ((ADD r) b ((NEG r) b)))))
    (fact 'ringoid-add-right-inv 'r 'a)
    (subst '(= ((ADD r) a ((NEG r) a)) (ZERO r)))
    (fact 'ringoid-add-right-inv 'r 'b)
    (subst '(= ((ADD r) b ((NEG r) b)) (ZERO r)))
    (fact 'ring-add-left-id-ringoid-as-ring 'r '(ZERO r))
    (ass)))
(dk-focus-having! '(= ((ADD r) ((ADD r) a b) ((ADD r) ((NEG r) a) ((NEG r) b))) (ZERO r)))
(fact 'r6b-rinv-unique 'r '((ADD r) a b) '((ADD r) ((NEG r) a) ((NEG r) b)))
(fact 'eq-sym '((ADD r) ((NEG r) a) ((NEG r) b)) '((NEG r) ((ADD r) a b)))
(ass)
(r6b-qed! 'r6b-rneg-add)

;;; ---- -(-a) = a -------------------------------------------------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a) '((IN a (CARR r)))
    '(= ((NEG r) ((NEG r) a)) a)))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'a)
(fact 'ring-add-left-inv-ringoid-as-ring 'r 'a)
(fact 'r6b-rinv-unique 'r '((NEG r) a) 'a)
(fact 'eq-sym 'a '((NEG r) ((NEG r) a)))
(ass)
(r6b-qed! 'r6b-rneg-neg)

;;; ---- (a+b) - (u+v) = (a-u) + (b-v) -----------------------------------
;;; THE identity a congruence modulo an ideal needs: distribute the negation
;;; over the sum, then interchange.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b u v)
      '((IN a (CARR r)) (IN b (CARR r)) (IN u (CARR r)) (IN v (CARR r)))
    '(= ((ADD r) ((ADD r) a b) ((NEG r) ((ADD r) u v)))
        ((ADD r) ((ADD r) a ((NEG r) u)) ((ADD r) b ((NEG r) v))))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'u)
(fact 'r6b-rneg-type 'r 'v)
(fact 'r6b-rneg-add 'r 'u 'v)
(subst '(= ((NEG r) ((ADD r) u v)) ((ADD r) ((NEG r) u) ((NEG r) v))))
(fact 'r6b-radd-interchange 'r 'a 'b '((NEG r) u) '((NEG r) v))
(ass)
(r6b-qed! 'r6b-rdiff-add)

;;; =====================================================================
;;; The two supports.  Statements copied from structure-library/ringoid.scm
;;; (:219 and :224) unchanged, so the citers in ringoid-setoid-proof.scm see
;;; the same formula they see today.
;;; =====================================================================

;;; ringoid-neg-diff:  -(a - b) = b - a.
(sp (make-wff (forall-guarded '(r a b) '((IS-RINGOID r) (IN a (CARR r)) (IN b (CARR r)))
  '(= ((NEG r) ((ADD r) a ((NEG r) b))) ((ADD r) b ((NEG r) a))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'a)
(fact 'r6b-rneg-type 'r 'b)
(fact 'r6b-rneg-add 'r 'a '((NEG r) b))
(subst '(= ((NEG r) ((ADD r) a ((NEG r) b)))
           ((ADD r) ((NEG r) a) ((NEG r) ((NEG r) b)))))
(fact 'r6b-rneg-neg 'r 'b)
(subst '(= ((NEG r) ((NEG r) b)) b))
(fact 'ring-add-comm-ringoid-as-ring 'r '((NEG r) a) 'b)
(ass)
(r6b-qed! 'ringoid-neg-diff)

;;; ringoid-diff-telescope:  (a - b) + (b - c) = a - c.
(sp (make-wff (forall-guarded '(r a b c)
    '((IS-RINGOID r) (IN a (CARR r)) (IN b (CARR r)) (IN c (CARR r)))
  '(= ((ADD r) ((ADD r) a ((NEG r) b)) ((ADD r) b ((NEG r) c)))
      ((ADD r) a ((NEG r) c))))))
(dk-peel!)
(fact 'r6b-rneg-type 'r 'b)
(fact 'r6b-rneg-type 'r 'c)
(fact 'r6b-radd-type 'r 'b '((NEG r) c))
(fact 'ring-add-assoc-ringoid-as-ring 'r 'a '((NEG r) b) '((ADD r) b ((NEG r) c)))
(subst '(= ((ADD r) ((ADD r) a ((NEG r) b)) ((ADD r) b ((NEG r) c)))
           ((ADD r) a ((ADD r) ((NEG r) b) ((ADD r) b ((NEG r) c))))))
(fact 'ring-add-assoc-ringoid-as-ring 'r '((NEG r) b) 'b '((NEG r) c))
(fact 'eq-sym '((ADD r) ((ADD r) ((NEG r) b) b) ((NEG r) c))
              '((ADD r) ((NEG r) b) ((ADD r) b ((NEG r) c))))
(subst '(= ((ADD r) ((NEG r) b) ((ADD r) b ((NEG r) c)))
           ((ADD r) ((ADD r) ((NEG r) b) b) ((NEG r) c))))
(fact 'ring-add-left-inv-ringoid-as-ring 'r 'b)
(subst '(= ((ADD r) ((NEG r) b) b) (ZERO r)))
(fact 'ring-add-left-id-ringoid-as-ring 'r '((NEG r) c))
(subst '(= ((ADD r) (ZERO r) ((NEG r) c)) ((NEG r) c)))
(rfl)
(r6b-qed! 'ringoid-diff-telescope)
