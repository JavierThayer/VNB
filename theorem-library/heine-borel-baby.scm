;;; heine-borel-baby.scm -- a closed real interval has the FINITE SUBCOVER
;;; property, PROVEN, with no metric-subspace machinery.
;;;
;;;   a, b in RR,  a <= b,
;;;   every U in F is open in RR-MS,
;;;   [a,b] subset (union of F)
;;;     =>  forsome G.  G subset F,  G a set,  CARD(G) in NN,
;;;                     [a,b] subset (union of G).
;;;
;;; WHY IT IS NOT STATED WITH IS-COMPACT.  `IS-COMPACT' and `IS-OPEN-COVER'
;;; (structure-library/compactness.scm) are predicates on a metric-space
;;; STRUCTURE, and IS-OPEN-COVER(s,C) demands that the union of C be all of
;;; PTS(s).  Saying "[a,b] is compact" therefore needs a metric SUBSPACE
;;; constructor, which does not exist in the tree.  The statement above avoids
;;; the question: every symbol in it exists today, the open sets are open in
;;; RR-MS itself, and the cover is only required to contain [a,b].
;;;
;;; WHY `IN G SET' IS IN THE CONCLUSION.  `CARD' is total on classes but the
;;; cardinality axioms (structure-library/cardinality.scm) are all guarded on
;;; `IN A SET' -- card-in-ord, card-insert, card-empty's companions -- so
;;; "CARD(G) in NN" says nothing about a G that is not known to be a set, and
;;; the induction cannot carry it.  Sethood is not an extra hypothesis but an
;;; extra CONCLUSION: the theorem is stronger for carrying it, and a finite
;;; subcover is a set.  F itself is NOT required to be a set.
;;;
;;; THE ROUTE: one more instance of `ccint-creep' (theorem-library/ccint-creep).
;;; The creeping set is
;;;
;;;   G_set = { x in RR : a <= x and x <= b and
;;;                       forsome H. H subset F, H a set, CARD(H) in NN,
;;;                                  [a,x] subset (union of H) }
;;;
;;; so the obligations are exactly ccint-creep's: G_set subset RR, a in G_set,
;;; b an upper bound, and the LOCAL STEP.  The supremum bookkeeping is done
;;; once, in ccint-creep, and not repeated here.
;;;
;;; THE LOCAL STEP, and the one place it is not what the sketch says.  At t in
;;; [a,b] the point lies in the union, so some U in F contains it, and
;;; IS-OPEN(RR-MS,U) (structure-library/metric-open-sets.scm:32) unfolds to
;;; "some r > 0 has BALL(RR-MS,t,r) subset U" -- the radius is handed over by
;;; the definition, with no epsilon/delta work at all.
;;;
;;; BUT THE CREEP RADIUS CANNOT BE r.  The creep's consequent quantifies over
;;; y with `y <= t + d' and the inner point z with `z <= y', both NON-STRICT,
;;; while BALL is the OPEN ball: `y in BALL(s,x,r)' is `DIST(s)(x,y) < r'
;;; (structure-library/metric-topology.scm:71).  With d = r the point z = t + r
;;; sits on the sphere and is not in the ball.  So the creep radius is the
;;; HALF: `rr-pos-halvable' (theorem-library/rr-halving.scm, proven modulo 0
;;; the same day) gives d > 0 with d + d = r, hence d < r, and then
;;; t - d < z <= t + d gives |t - z| <= d < r strictly.  `rr-le-lt-trans'
;;; (theorem-library/rr-order-basics) is what turns the non-strict bound into
;;; the strict one; that pair -- halve, then le-lt-trans -- is the whole of the
;;; friction, and it is the same friction `ball-mem-from-le' was written for.
;;; This file does not cite `ball-mem-from-le': that is a warranted support and
;;; would put itself on the bill.  `mac' on the BALL functoid plus the kernel
;;; `sep-mi' does the same work and costs nothing.
;;;
;;; Then, if some w in G_set exceeds t - d, w carries a finite H covering
;;; [a,w]; the enlarged cover is H' = {U} u H.  For y in [a,b] with y <= t + d
;;; and any z in [a,y], either z <= w -- and [a,w] subset (union H) subset
;;; (union H') -- or w <= z, and then t - d < w <= z <= y <= t + d puts z in
;;; the ball, hence in U, hence in the union of H'.
;;;
;;; THE TWO CARDINALITY WRINKLES, and how they turned out.
;;;
;;;   * FRESHNESS.  `card-insert' (cardinality.scm:53) is guarded on
;;;     NOT (IN x A): U may already be in H.  So a case split on `U in H' is
;;;     unavoidable -- but it is not written here.  It is written once, in
;;;     `card-union-singleton-nn' below, whose YES branch collapses the union
;;;     by `union-singleton-absorb' and whose NO branch is card-insert proper.
;;;     That is the same shape as `card-union-singleton-bound'
;;;     (theorem-library/makeset-card-bound.scm:198) and this lemma is that
;;;     lemma with its second conjunct dropped -- which is exactly why it is
;;;     re-proved rather than cited: the `<= succ(CARD S)' conjunct is the
;;;     only thing in it that needs `nn-le-succ', an asserted well-known
;;;     support, and citing it would put nn-le-succ on this bill.  Dropping a
;;;     conjunct nobody needs buys `modulo 0'.
;;;
;;;   * succ_ORD BACK INTO NN.  `card-insert' yields succ_ORD(CARD A);
;;;     `ord-succ-nn' (structure-library/ordinals.scm, primitive) says succ_ORD
;;;     and succ agree on NN and `nn-succ-closed' (primitive) closes NN under
;;;     succ.  Both are trusted base, so the round trip is free.
;;;
;;;   * THE BASE CASE is the same lemma at S = EMPTY-SET, so the singleton
;;;     {U_a} is written UNION(PAIR(U_a,U_a), EMPTY-SET) throughout and never
;;;     collapsed.  `card-singleton' (theorem-library/card-singleton.scm) is a
;;;     warranted support and `union-empty-left' likewise; collapsing the
;;;     union would have cost both.  Carrying the EMPTY-SET costs nothing and
;;;     makes the base case a literal instance of the step.
;;;
;;; ELIMINATING A BIG-UNION MEMBERSHIP is the kernel rule `bu-me'
;;; (interactive.scm:4106 -> pi-big-union-mem-elim!, primitive-inferences.scm:1228):
;;; from (IN x (BIG-UNION z A body)) it produces an eigenvariable e with
;;; (IN e A) and (IN x body[z:=e]), and REMOVES the membership.  `bu-mi' is its
;;; introduction twin, taking the witness.  No axiom is needed and none is added.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.  Six small lemmas are proved here
;;; first, all `modulo 0'.  The bill reads `[oracles: ineq arith crs]': `ineq'
;;; is the only one this file calls, and `arith' and `crs' arrive transitively
;;; through `rr-pos-halvable', whose witness is eps * recip(1+1).
;;;
;;; Loads after ccint-creep, ccint-basics (ccint-membership), extreme-value
;;; (CCINT), rr-halving (rr-pos-halvable), rr-order-basics (rr-le-lt-trans,
;;; rr-le-ne-lt), rr-abs-basics (rr-abs-bound, rr-abs-closed), rr-ms-dist,
;;; subset-lemmas (subset-mem-fwd), makeset-card-bound (union-comm,
;;; union-singleton-absorb), structure-library/metric-open-sets (IS-OPEN),
;;; structure-library/cardinality, and driver-kit.

;;; ---- file-local driver helpers (the `hb-' prefix) --------------------

(define (hb-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (hb-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "hb-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (hb-pick-in l set-expr)
  (let loop ((l l))
    (cond ((null? l) (error "hb-pick-in: no membership in" set-expr))
          ((and (pair? (car l)) (eq? (caar l) 'IN) (equal? (caddr (car l)) set-expr))
           (car l))
          (else (loop (cdr l))))))

(define (hb-mem-in set-expr) (hb-pick-in (dk-asms) set-expr))

;;; `ineq' wants 1-based assumption indices, and the premises are named ONE BY
;;; ONE: a membership premise whose atoms cannot be certified in RR poisons the
;;; whole call.
(define (hb-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "hb-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (hb-ineq . forms) (apply ineq (map hb-idx forms)))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (hb-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (hb-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `ai' every context conjunction, to exhaustion.
(define (hb-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 20)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; `di' until an ASSUMPTION lands.  A GUARDED universal goes whole under one
;;; `di'; an unguarded one whose antecedent is a conjunction peels the binder
;;; and lands NOTHING, so counting `di's is not a way to reach a goal.
(define (hb-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "hb-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (hb-di-landed-1!)
  (let ((new (hb-di-landed!)))
    (if (null? (cdr new))
        (car new)
        (error "hb-di-landed-1!: expected 1 landing, got"
               (map expression->string new)))))

(define (hb-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME that is ALREADY in the context.  `obtain' cannot do
;;; this -- it recognises only an existential its own lane just landed -- and it
;;; swallows the error, reporting "nothing obtained".  The eigenvariable is read
;;; off by free-variable set difference and a miss ERRORS.
(define (hb-skolem! ex)
  (let* ((fv0 (hb-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (hb-fvs (dk-asms)))))
      (if (null? fresh)
          (error "hb-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (hb-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "hb-obtain: nothing obtained for" what))
    v))

;;; Skolemize a BIG-UNION membership: `bu-me' lands (IN e FAM) and (IN x e);
;;; return e, taken from the landing that is a membership in FAM rather than by
;;; shape.
(define (hb-bu-skolem! mem fam)
  (let ((new (dk-landed (lambda () (bu-me mem)))))
    (cadr (hb-pick-in new fam))))

;;; The cover written as a BIG-UNION over the family itself.
(define (hb-un h) (list 'BIG-UNION 'u_ h 'u_))

;;; H with U inserted, in the PAIR spelling `card-insert' speaks.
(define (hb-insert u h) (list 'UNION (list 'PAIR u u) h))

;;; ======================================================================
;;; SIX SMALL LEMMAS.  Each is general, each is `modulo 0', and each exists
;;; because the main driver would otherwise repeat it inline three times.
;;; ======================================================================

;;; ---- empty-subset-any:  EMPTY-SET subset B, for any class B ----------
;;; Needed only because the base case's cover is {U_a} u EMPTY-SET.

(quietly (lambda ()
  (sp (make-wff '(FORALL b_ (SUBSET EMPTY-SET b_))))
  (di)
  (mac 'subset-def)
  (let ((m (hb-di-landed-1!)))
    (fact 'empty-set-has-no-members (cadr m))
    (prop))))
(qed 'empty-subset-any)
(topic! 'empty-subset-any 'plumbing)

;;; ---- union-singleton-mem:  y in {y} u S ------------------------------

(quietly (lambda ()
  (sp (make-wff '(FORALL y_ (FORALL s_ (IMPLIES (IN y_ SET)
                   (IN y_ (UNION (PAIR y_ y_) s_)))))))
  (hb-peel!)
  (mac 'union-membership)
  (oi-l)
  (have! '(AND (IN y_ SET) (IN y_ SET)))
  (fact 'pairing-membership 'y_ 'y_ 'y_)
  (have! '(= y_ y_) (lambda () (rfl)))
  (prop)))
(qed 'union-singleton-mem)
(topic! 'union-singleton-mem 'plumbing)

;;; ---- union-right-subset:  S subset A u S -----------------------------

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL s_ (SUBSET s_ (UNION a_ s_))))))
  (hb-peel!)
  (mac 'subset-def)
  (hb-di-landed-1!)
  (mac 'union-membership)
  (oi-r)
  (ass)))
(qed 'union-right-subset)
(topic! 'union-right-subset 'plumbing)

;;; ---- union-singleton-subset:  y in B, S subset B  =>  {y} u S subset B

(quietly (lambda ()
  (sp (make-wff '(FORALL b_ (FORALL y_ (FORALL s_
       (IMPLIES (IN y_ b_) (IMPLIES (SUBSET s_ b_)
         (SUBSET (UNION (PAIR y_ y_) s_) b_))))))))
  (hb-peel!)
  (fact 'membership-implies-sethood 'y_ 'b_)
  (mac 'subset-def)
  (let* ((m (hb-di-landed-1!))
         (v (cadr m)))
    (mac-h 'union-membership m)
    (have! '(AND (IN y_ SET) (IN y_ SET)))
    (fact 'pairing-membership 'y_ 'y_ v)
    (have! (list 'IMPLIES (list '= v 'y_) (list 'IN v 'b_))
           (lambda () (di) (subst (list '= v 'y_)) (ass)))
    (fact 'subset-mem-fwd 's_ 'b_ v)
    ;; (prop) has an atom cap and `fact' lands its whole instantiation chain,
    ;; so the four premises that decide the goal are named explicitly.
    (for-each
     (lambda (f)
       (if (not (member f (list (list 'OR (list 'IN v '(PAIR y_ y_)) (list 'IN v 's_))
                                (list 'IFF (list 'IN v '(PAIR y_ y_))
                                      (list 'OR (list '= v 'y_) (list '= v 'y_)))
                                (list 'IMPLIES (list '= v 'y_) (list 'IN v 'b_))
                                (list 'IMPLIES (list 'IN v 's_) (list 'IN v 'b_)))))
           (wk f)))
     (dk-asms))
    (prop))))
(qed 'union-singleton-subset)
(topic! 'union-singleton-subset 'plumbing)

;;; ---- big-union-mono:  A subset B  =>  union(A) subset union(B) -------
;;; The body of the BIG-UNION is the bound variable itself, so this is an
;;; ordinary first-order statement and not a schema.

(quietly (lambda ()
  (sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'b_
       (list 'IMPLIES '(SUBSET a_ b_)
             (list 'SUBSET (hb-un 'a_) (hb-un 'b_)))))))
  (hb-peel!)
  (mac 'subset-def)
  (let* ((m (hb-di-landed-1!))
         (e (hb-bu-skolem! m 'a_)))
    (fact 'subset-mem-fwd 'a_ 'b_ e)
    (for-each (lambda (k) (dk-focus! k) (ass))
              (dk-opened (lambda () (bu-mi e)))))))
(qed 'big-union-mono)
(topic! 'big-union-mono 'plumbing)

;;; ---- card-union-singleton-nn:  inserting one element keeps a finite set
;;; finite.  This is `card-union-singleton-bound' (makeset-card-bound.scm:198)
;;; with the `<= succ(CARD S)' conjunct dropped: that conjunct, and only that
;;; conjunct, wants `nn-le-succ', which is an asserted well-known support.
;;; The case split on `y in S' is the FRESHNESS guard of card-insert and is
;;; unavoidable; it is written once, here.

(quietly (lambda ()
  (sp (make-wff '(FORALL s_ (IMPLIES (IN s_ SET)
     (FORALL y_ (IMPLIES (IN y_ SET)
       (IMPLIES (IN (CARD s_) NN)
                (IN (CARD (UNION (PAIR y_ y_) s_)) NN))))))))
  (hb-peel!)
  (use-em '(IN y_ s_)
    ;; y_ is already in S: the union IS S.
    (lambda ()
      (fact 'union-singleton-absorb 's_ 'y_)
      (subst '(= (UNION (PAIR y_ y_) s_) s_))
      (ass))
    ;; y_ is fresh: card-insert gives the exact value, succ_ORD(CARD S).
    (lambda ()
      (have! '(AND (IN y_ SET) (NOT (IN y_ s_))))
      (fact 'card-insert 's_ 'y_)
      (fact 'union-comm '(PAIR y_ y_) 's_)
      (fact 'ord-succ-nn '(CARD s_))
      (subst '(= (UNION (PAIR y_ y_) s_) (UNION s_ (PAIR y_ y_))))
      (subst '(= (CARD (UNION s_ (PAIR y_ y_))) (succ_ORD (CARD s_))))
      (subst '(= (succ_ORD (CARD s_)) (succ (CARD s_))))
      (fact 'nn-succ-closed '(CARD s_))
      (ass)))))
(qed 'card-union-singleton-nn)
(topic! 'card-union-singleton-nn 'combinatorial)

;;; ======================================================================
;;; THE STATEMENT, and the set the creep runs along.
;;; ======================================================================

;;; A finite subcover of [a, UPPER].  Built from flat lists rather than
;;; hand-nested: a formula this deep is where a miscounted parenthesis reads as
;;; a different theorem.
(define (hb-fincov upper)
  (list 'FORSOME 'g_
    (list 'AND '(SUBSET g_ f_)
      (list 'AND '(IN g_ SET)
        (list 'AND '(IN (CARD g_) NN)
              (list 'SUBSET (list 'CCINT 'a upper) (hb-un 'g_)))))))

(define hb-set
  (list 'SEP 'x_ 'RR
        (list 'AND (list 'AND '(<= a x_) '(<= x_ b)) (hb-fincov 'x_))))

;;; The family quantifier binds `v_', not `u_': `u_' is the BIG-UNION's own
;;; bound variable throughout, and two binders spelled alike in one formula is
;;; the trap the working brief keeps naming.
(define hb-stmt
  (forall-guarded '(a b f_)
    (list '(IN a RR) '(IN b RR) '(<= a b)
          '(FORALL v_ (IMPLIES (IN v_ f_) (IS-OPEN RR-MS v_)))
          (list 'SUBSET '(CCINT a b) (hb-un 'f_)))
    (hb-fincov 'b)))

;;; The local step, in the exact shape ccint-creep's last hypothesis takes when
;;; its a, b and G are instantiated here.
(define hb-local
  (list 'FORALL 't_
    (list 'IMPLIES '(IN t_ (CCINT a b))
      (list 'FORSOME 'd_
        (list 'AND '(IN d_ RR)
          (list 'AND '(< 0 d_)
            (list 'IMPLIES
              (list 'FORSOME 'w_ (list 'AND (list 'IN 'w_ hb-set) '(< (- t_ d_) w_)))
              (list 'FORALL 'y_
                (list 'IMPLIES (list 'AND '(IN y_ (CCINT a b)) '(<= y_ (+ t_ d_)))
                      (list 'IN 'y_ hb-set))))))))))

;;; ---- eigenvariables set as the proof runs ----------------------------
;;; NEVER distinguished by CASE: MIT folds symbols, so `hb-E' would BE `hb-e'.
(define hb-e0    #f)   ; the member of F containing a
(define hb-t     #f)   ; the point of [a,b] the local step is at
(define hb-e     #f)   ; the member of F containing t
(define hb-r     #f)   ; the radius openness of that member supplies at t
(define hb-d     #f)   ; the creep radius: the HALF of hb-r
(define hb-w     #f)   ; the member of G just to the left of t
(define hb-h     #f)   ; the finite cover of [a,w] that w carries
(define hb-prime #f)   ; the enlarged cover {U} u H
(define hb-y     #f)   ; the point of [a, t+d] being placed in G

;;; ---- context finders -------------------------------------------------

;;; forall v. v in F => IS-OPEN(RR-MS, v) -- discriminated on its CONSEQUENT.
(define (hb-family)
  (hb-find 'family
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body))
                            (eq? (car (caddr body)) 'IS-OPEN)))))))

;;; forall y in U. forsome r > 0. BALL(RR-MS,y,r) subset U -- the interior
;;; clause of the unfolded IS-OPEN, told from the family universal by the BALL.
(define (hb-interior)
  (hb-find 'interior
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'BALL)))))

;;; ---- the innermost argument: one point z of [a,y] -------------------

;;; z <= w: z lies in the part already conquered, and H covers it.
(define (hb-left! z)
  (have! (list 'IN z (list 'CCINT 'a hb-w))
    (lambda () (mac 'ccint-membership) (from-context!)))
  (fact 'subset-mem-fwd (list 'CCINT 'a hb-w) (hb-un hb-h) z)
  (fact 'subset-mem-fwd (hb-un hb-h) (hb-un hb-prime) z)
  (ass))

;;; w <= z: then t - d < w <= z <= y <= t + d, so |t - z| <= d < r and z is in
;;; the OPEN r-ball round t, hence in U, hence in the union of H'.
(define (hb-right! z)
  (fact 'rr-sub-in-rr hb-t z)
  (fact 'rr-abs-closed (list '- hb-t z))
  (have! (list '<= (list 'abs (list '- hb-t z)) hb-d)
    (lambda ()
      (mac 'rr-abs-bound)
      (hb-goal-and!
       (lambda () (hb-ineq (list '< (list '- hb-t hb-d) hb-w)
                           (list '<= hb-w z)
                           (list '<= z hb-y)
                           (list '<= hb-y (list '+ hb-t hb-d)))))))
  (have! (list 'AND (list '<= (list 'abs (list '- hb-t z)) hb-d)
                    (list '< hb-d hb-r)))
  (fact 'rr-le-lt-trans (list 'abs (list '- hb-t z)) hb-d hb-r)
  (mac-h '< (list '< (list 'abs (list '- hb-t z)) hb-r))
  (dk-split! (list 'AND (list '<= (list 'abs (list '- hb-t z)) hb-r)
                        (list 'NOT (list '= (list 'abs (list '- hb-t z)) hb-r))))
  ;; The BALL functoid is unfolded and met with the kernel `sep-mi'.  Citing
  ;; `ball-membership' or `ball-mem-from-le' instead would be one line shorter
  ;; and would put a warranted support on the bill.
  (have! (list 'IN z (list 'BALL 'RR-MS hb-t hb-r))
    (lambda ()
      (mac 'BALL)
      (for-each (lambda (k)
                  (dk-focus! k)
                  (if (eq? (car (dk-goal)) 'IN)
                      (begin (slot 'PTS) (ass))
                      (begin (mac 'rr-ms-dist) (from-context!))))
                (dk-opened (lambda () (sep-mi))))))
  (fact 'subset-mem-fwd (list 'BALL 'RR-MS hb-t hb-r) hb-e z)
  (for-each (lambda (k) (dk-focus! k) (ass))
            (dk-opened (lambda () (bu-mi hb-e)))))

;;; goal: [a,y] subset union(H').
(define (hb-cover-interval!)
  (mac 'subset-def)
  (let* ((m (hb-di-landed-1!))
         (z (cadr m)))
    (mac-h 'ccint-membership m)
    (hb-split!)
    (have! (list 'AND (list 'IN z 'RR) (list 'IN hb-w 'RR)))
    (fact 'rr-leq-total z hb-w)
    (use-cases (list (list '<= z hb-w) (list '<= hb-w z))
      (lambda () (hb-left! z))
      (lambda () (hb-right! z)))))

;;; goal: forsome G. G subset F, G a set, CARD(G) in NN, [a,y] subset union(G).
;;; The witness is H'.
(define (hb-cov-y!)
  (ew hb-prime)
  (hb-goal-and!
   (lambda ()
     (let ((g (dk-goal)))
       (if (and (eq? (car g) 'SUBSET) (equal? (cadr g) (list 'CCINT 'a hb-y)))
           (hb-cover-interval!)
           (ass))))))

;;; goal: (IN y G), with y in [a,b] and y <= t + d in context.
(define (hb-y-in-set!)
  (mac-h 'ccint-membership (list 'IN hb-y '(CCINT a b)))
  (hb-split!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'IN)
         (ass)                                     ; (IN y RR)
         (hb-goal-and!                             ; a <= y, y <= b, the cover
          (lambda () (if (eq? (car (dk-goal)) 'FORSOME) (hb-cov-y!) (ass))))))
   (dk-opened (lambda () (sep-mi)))))

;;; goal: forall y in [a,b] with y <= t+d. y in G -- under the assumption that
;;; some member of G already exceeds t - d.
(define (hb-reach!)
  (di)
  (set! hb-w (hb-skolem! (hb-find 'reach
              (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                               (dk-contains? f hb-set))))))
  (sep-me (hb-mem-in hb-set))
  (hb-split!)
  (set! hb-h (hb-skolem! (hb-find 'inherited
              (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                               (dk-contains? f (list 'CCINT 'a hb-w)))))))
  (set! hb-prime (hb-insert hb-e hb-h))
  ;; H' = {U} u H is a set, is still inside F, is still finite, and contains
  ;; both U and the whole of H.
  (fact 'membership-implies-sethood hb-e 'f_)
  (have! (list 'AND (list 'IN hb-e 'SET) (list 'IN hb-e 'SET)))
  (fact 'pairing hb-e hb-e)
  (have! (list 'AND (list 'IN (list 'PAIR hb-e hb-e) 'SET) (list 'IN hb-h 'SET)))
  (fact 'union-set-closure (list 'PAIR hb-e hb-e) hb-h)
  (fact 'card-union-singleton-nn hb-h hb-e)
  (fact 'union-singleton-subset 'f_ hb-e hb-h)
  (fact 'union-singleton-mem hb-e hb-h)
  (fact 'union-right-subset (list 'PAIR hb-e hb-e) hb-h)
  (fact 'big-union-mono hb-h hb-prime)
  (let ((and-y (hb-di-landed-1!)))
    (set! hb-y (cadr (cadr and-y)))
    (dk-split! and-y))
  (hb-y-in-set!))

;;; ======================================================================
;;; THE PROOF
;;; ======================================================================

(sp (make-wff hb-stmt))
(hb-peel!)

;;; ---- G is a subset of RR ---------------------------------------------

(have! (list 'SUBSET hb-set 'RR)
  (lambda () (mac 'subset-def) (di) (sep-me (hb-mem-in hb-set)) (ass)))

;;; ---- a is in G:  [a,a] is covered by the single U that contains a ----

(fact 'rr-leq-reflexive 'a)
(have! '(IN a (CCINT a b)) (lambda () (mac 'ccint-membership) (from-context!)))
(fact 'subset-mem-fwd '(CCINT a b) (hb-un 'f_) 'a)
(set! hb-e0 (hb-bu-skolem! (list 'IN 'a (hb-un 'f_)) 'f_))

(fact 'membership-implies-sethood hb-e0 'f_)
(ta 'empty-set-is-set)
(have! (list 'AND (list 'IN hb-e0 'SET) (list 'IN hb-e0 'SET)))
(fact 'pairing hb-e0 hb-e0)
(have! (list 'AND (list 'IN (list 'PAIR hb-e0 hb-e0) 'SET) '(IN EMPTY-SET SET)))
(fact 'union-set-closure (list 'PAIR hb-e0 hb-e0) 'EMPTY-SET)
(ta 'card-empty)
(ta 'nn-zero-in)
(have! '(IN (CARD EMPTY-SET) NN)
       (lambda () (subst '(= (CARD EMPTY-SET) 0)) (ass)))
(fact 'card-union-singleton-nn 'EMPTY-SET hb-e0)
(fact 'empty-subset-any 'f_)
(fact 'union-singleton-subset 'f_ hb-e0 'EMPTY-SET)
(fact 'union-singleton-mem hb-e0 'EMPTY-SET)

(have! (list 'IN 'a hb-set)
  (lambda ()
    (for-each
     (lambda (k)
       (dk-focus! k)
       (if (eq? (car (dk-goal)) 'IN)
           (ass)
           (hb-goal-and!
            (lambda ()
              (if (eq? (car (dk-goal)) 'FORSOME)
                  (begin
                    (ew (hb-insert hb-e0 'EMPTY-SET))
                    (hb-goal-and!
                     (lambda ()
                       (let ((g (dk-goal)))
                         (if (and (eq? (car g) 'SUBSET)
                                  (equal? (cadr g) '(CCINT a a)))
                             ;; the only point of [a,a] is a itself
                             (begin
                               (mac 'subset-def)
                               (let* ((m (hb-di-landed-1!)) (z (cadr m)))
                                 (mac-h 'ccint-membership m)
                                 (hb-split!)
                                 (have! (list 'AND (list 'IN z 'RR) '(IN a RR)))
                                 (have! (list 'AND (list '<= z 'a) (list '<= 'a z)))
                                 (fact 'rr-leq-antisymmetric z 'a)
                                 (subst (list '= z 'a))
                                 (for-each (lambda (j) (dk-focus! j) (ass))
                                           (dk-opened (lambda () (bu-mi hb-e0))))))
                             (ass))))))
                  (ass))))))
     (dk-opened (lambda () (sep-mi))))))

;;; ---- b is an upper bound of G ----------------------------------------

(have! (list 'RR-UPPER-BOUND hb-set 'b)
  (lambda ()
    (mac 'rr-upper-bound)
    (for-each (lambda (k)
                (dk-focus! k)
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (begin (di) (sep-me (hb-mem-in hb-set)) (hb-split!) (ass))))
              (dk-opened (lambda () (di))))))

;;; ---- the local step --------------------------------------------------

(have! hb-local
  (lambda ()
    (let ((mem (hb-di-landed-1!)))
      (set! hb-t (cadr mem))
      ;; cite the cover BEFORE unfolding the interval membership: `mac-h'
      ;; REPLACES the assumption it unfolds.
      (fact 'subset-mem-fwd '(CCINT a b) (hb-un 'f_) hb-t)
      (mac-h 'ccint-membership mem)
      (hb-split!))
    (set! hb-e (hb-bu-skolem! (list 'IN hb-t (hb-un 'f_)) 'f_))
    (inst+ (hb-family) hb-e)
    (mac-h 'is-open (list 'IS-OPEN 'RR-MS hb-e))
    (hb-split!)
    (set! hb-r (hb-obtain 'radius (lambda () (inst+ (hb-interior) hb-t))))
    (hb-split!)
    ;; HALVE the radius: BALL is the OPEN ball, so a creep radius equal to r
    ;; would put the endpoint t + r on the sphere and outside U.  The halving
    ;; comes BEFORE the POS-RR unfolds, which consume the hypothesis.
    (set! hb-d (hb-obtain 'half (lambda () (fact 'rr-pos-halvable hb-r))))
    (hb-split!)
    (mac-h 'pos-rr (list 'POS-RR hb-d))
    (hb-split!)
    (mac-h 'pos-rr (list 'POS-RR hb-r))
    (hb-split!)
    (have! (list 'AND (list '<= 0 hb-d) (list 'NOT (list '= 0 hb-d))))
    (fact 'rr-le-ne-lt 0 hb-d)                      ; 0 < d
    ;; d < r.  The `<=' half is linear in d + d = r; the disequality is the
    ;; observation that d = r would force d + d = d, i.e. d = 0.
    (have! (list '< hb-d hb-r)
      (lambda ()
        (mac '<)
        (hb-goal-and!
         (lambda ()
           (if (eq? (car (dk-goal)) 'NOT)
               (begin
                 (di)
                 (have! (list '= 0 hb-d)
                        (lambda () (hb-ineq (list '= (list '+ hb-d hb-d) hb-r)
                                            (list '= hb-d hb-r))))
                 (ai (list 'NOT (list '= 0 hb-d))))
               (hb-ineq (list '= (list '+ hb-d hb-d) hb-r)
                        (list '<= 0 hb-d)))))))
    (ew hb-d)
    (hb-goal-and!
     (lambda () (if (eq? (car (dk-goal)) 'IMPLIES) (hb-reach!) (ass))))))

;;; ---- creep, and read the cover at b off the result --------------------

(let ((at-b (dk-fact! 'ccint-creep 'a 'b hb-set)))
  (sep-me at-b)
  (hb-split!)
  (ass))

(qed 'heine-borel-baby)
(topic! 'heine-borel-baby 'topology)
(alias! 'heine-borel-baby "Heine-Borel" "baby Heine-Borel"
                          "a closed interval has the finite subcover property")
