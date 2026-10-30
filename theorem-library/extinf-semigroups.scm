;;; extinf-semigroups.scm -- extended addition on (-inf, +inf] and on [-inf, +inf), and the
;;; order of each line: the laws, stated and proven SYMMETRICALLY.  Agent EXT-INF, 2026-10-26
;;; (the user's decision of the day: neg-inf-below-reals, "but the semigroup properties
;;; should be clearly stated for both").
;;; DESTINATION: theorem-library/extinf-semigroups.scm.  Library: analysis (the library of
;;; structure-library/extended-reals and extended-reals-pos).
;;;
;;; Vocabulary (scratchpad/extinf/extinf-vocab.scm): RR-EXT-UP = RR u {POS-INF},
;;; RR-EXT-DOWN = RR u {NEG-INF}, EPLUS-UP / EPLUS-DOWN by cases through IF on the absorbing
;;; point.  POS-INF + NEG-INF is never mentioned: every law is guarded by membership in the
;;; operation's own line.
;;;
;;;   (-inf, +inf] = RR-EXT-UP, EPLUS-UP          [-inf, +inf) = RR-EXT-DOWN, EPLUS-DOWN
;;;   ---------------------------------------     -----------------------------------------
;;;   rr-ext-up-membership                         rr-ext-down-membership
;;;   rr-in-rr-ext-up                              rr-in-rr-ext-down
;;;   pos-inf-in-rr-ext-up                         neg-inf-in-rr-ext-down
;;;   rr-ext-up-in-rr-star                         rr-ext-down-in-rr-star
;;;   rr-ext-up-below-pos-inf     x <= +inf        rr-ext-down-above-neg-inf   -inf <= x
;;;   rr-ext-up-le-real-in-rr     x <= t real      rr-ext-down-ge-real-in-rr   t <= x, t real
;;;                               => x real                                    => x real
;;;   rr-ext-up-le-refl / -trans / -antisymm       rr-ext-down-le-refl / -trans / -antisymm
;;;   eplus-up-real               x + y real sum   eplus-down-real
;;;   eplus-up-pos-inf-left/-right ABSORBING       eplus-down-neg-inf-left/-right ABSORBING
;;;   eplus-up-closed             CLOSURE          eplus-down-closed
;;;   eplus-up-comm               COMMUTATIVITY    eplus-down-comm
;;;   eplus-up-assoc              ASSOCIATIVITY    eplus-down-assoc
;;;   eplus-up-zero-left/-right   0 NEUTRAL        eplus-down-zero-left/-right
;;;   eplus-up-mono               x <= y =>        eplus-down-mono
;;;                               x + z <= y + z
;;;   rr-pos-star-in-rr-ext-up, eplus-up-agrees-eplus  (the bridge: on [0, +inf] EPLUS-UP IS
;;;                               the library's eplus, so nothing is duplicated)
;;;
;;; WHERE EACH INFINITY AXIOM IS USED.  `pos-inf-above-reals' carries rr-ext-up-le-real-in-rr
;;; and through it the order laws and eplus-up-mono; `neg-inf-below-reals' (the new primitive)
;;; carries rr-ext-down-ge-real-in-rr and the same three laws and eplus-down-mono.  The
;;; algebraic laws need only that the infinity is not a real (pos-inf-not-in-rr,
;;; neg-inf-not-in-rr-proven).
;;;
;;; CITATIONS (their files): number-systems (rr-zero-in, rr-leq-reflexive,
;;; rr-leq-antisymmetric, rr-add-closed, rr-add-comm, rr-add-assoc, rr-add-zero);
;;; extended-reals (rr-star-membership, pos-inf-upper-bound, neg-inf-lower-bound,
;;; pos-inf-above-reals, neg-inf-below-reals); extended-reals-pos (rr-pos-star-membership);
;;; the vocabulary (rr-ext-up-def, rr-ext-down-def); set vocabulary (union-membership,
;;; singleton-membership, membership-implies-sethood); theorem-library/rake-infinity-points
;;; (pos-inf-not-in-rr, pos-inf-in-rr-star, neg-inf-in-rr-star); extinf-points
;;; (neg-inf-not-in-rr-proven); rake-eplus-defined (eplus-real-defined, eplus-pos-inf-left,
;;; eplus-pos-inf-right); numeric-instances (binplus-apply).  Tactics: prop, driver-kit, the
;;; ineq oracle (calc).  LOAD WINDOW: after theorem-library/rake-eplus-defined, calc and
;;; extinf-points; no citer.
;;; Helper prefix: eis-.

;;; ---------------------------------------------------------------------------
;;; THE TWO SIDES, as data, so the two lists are proven by the same driver.
(define (eis-side up?)
  (if up?
      (list 'RR-EXT-UP 'POS-INF 'EPLUS-UP 'rr-ext-up-membership 'rr-ext-up-def
            'pos-inf-not-in-rr 'pos-inf-in-rr-star)
      (list 'RR-EXT-DOWN 'NEG-INF 'EPLUS-DOWN 'rr-ext-down-membership 'rr-ext-down-def
            'neg-inf-not-in-rr 'neg-inf-in-rr-star)))
(define (eis-cls s)  (list-ref s 0))
(define (eis-inf s)  (list-ref s 1))
(define (eis-op s)   (list-ref s 2))
(define (eis-memb s) (list-ref s 3))
(define (eis-def s)  (list-ref s 4))
(define (eis-nrr s)  (list-ref s 5))
(define (eis-star s) (list-ref s 6))
(define (eis-nm up? stem) (string->symbol (string-append (if up? "rr-ext-up-" "rr-ext-down-") stem)))
(define (eis-on up? stem) (string->symbol (string-append (if up? "eplus-up-" "eplus-down-") stem)))

;;; the eigenvariables of the typings a peel landed, in order
(define (eis-vars landed)
  (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)))) landed)))

(define (eis-and fs) (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (eis-and (cdr fs)))))
;;; land the conjunction of FS (each in context): the antecedent of a conjunctive citation
(define (eis-and! . fs)
  (let ((c (eis-and fs)))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (ass))))))))

;;; use-cases that skips a branch hash-consing already grounded
(define (eis-use-cases! disjuncts . bodies)
  (let* ((result (use-cases disjuncts))
         (ob     (cases-obligation result))
         (cs     (cdr (assq 'cases result))))
    (if ob (error "eis-use-cases!: the disjunction is not in context" disjuncts))
    (if (not (= (length cs) (length bodies)))
        (error "eis-use-cases!: branch count" (length cs) (length bodies)))
    (for-each (lambda (mc body)
                (if (not (sequent-node-grounded? (cdr mc)))
                    (begin (dk-focus! (cdr mc)) (body))))
              cs bodies)))

;;; TM in the side's class in context: split on (TM in RR) or (TM = inf)
(define (eis-cases! s tm real-body inf-body)
  (let ((d (list 'OR (list 'IN tm 'RR) (list '= tm (eis-inf s)))))
    (if (not (dk-asm? d))
        (dk-have! d
          (lambda ()
            (let ((i (dk-cite! (eis-memb s) tm)))
              (if (dk-only! i (list 'IN tm (eis-cls s))) (prop))))))
    (eis-use-cases! (list (list 'IN tm 'RR) (list '= tm (eis-inf s))) real-body inf-body)))

;;; (IN TM cls) from (TM in RR) or (TM = inf) in context (KEEPER): the -close! form for a
;;; leaf whose goal IS that membership, the -have! form for a lane
(define (eis-close-in! s tm keeper)
  (let ((i (dk-cite! (eis-memb s) tm)))
    (if (dk-only! i keeper) (prop))))
(define (eis-in! s tm keeper)
  (if (not (dk-asm? (list 'IN tm (eis-cls s))))
      (dk-have! (list 'IN tm (eis-cls s)) (lambda () (eis-close-in! s tm keeper)))))

;;; (= C C) for an atomic constant
(define (eis-refl! c)
  (if (not (dk-asm? (list '= c c))) (dk-have! (list '= c c) (lambda () (rfl)))))

;;; rewrite the goal by the equation THM yields at ARGS (cited; antecedents in context)
(define (eis-rw! thm . args)
  (let ((eq (apply dk-cite! thm args)))
    (if (not (memq (car eq) '(= ==)))
        (error "eis-rw!: the citation did not detach to an equation" thm (expression->string eq)))
    (subst eq)))


;;; A proof opened and closed from inside a helper goes through dk-sp-qed!, so the certified
;;; loader installs it (CLAUDE.md: a helper never calls bare sp).
(define (eis-prove! name stmt steps!)
  (dk-sp-qed! (make-wff stmt) steps! name)
  (topic! name 'analysis))

;;; ===========================================================================
;;; (1) THE LINES.  Membership, the points, the inclusion in RR-STAR, the bound.

(define (eis-membership! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)))
    (eis-prove! (eis-memb s)
      (list 'FORALL 'x (list 'IFF (list 'IN 'x (eis-cls s)) (list 'OR '(IN x RR) (list '= 'x inf))))
      (lambda ()
        (di)
        (mac (eis-def s))
        (let ((x (cadr (cadr (dk-goal)))))
          (fact (eis-star s))
          (fact 'membership-implies-sethood inf 'RR-STAR)
          (fact 'union-membership 'RR (list 'SINGLETON inf) x)
          (fact 'singleton-membership inf x)
          (dk-have! (list 'IMPLIES (list '= x inf) (list 'IN x 'SET))
            (lambda () (di) (subst (list '= x inf)) (ass)))
          (prop))))))
(eis-membership! #t)
(eis-membership! #f)

(define (eis-inf-in-name up?) (if up? 'pos-inf-in-rr-ext-up 'neg-inf-in-rr-ext-down))
(define (eis-bound-name up?) (if up? 'rr-ext-up-below-pos-inf 'rr-ext-down-above-neg-inf))

(define (eis-points! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (cls (eis-cls s)))
    ;; every real is on the line
    (eis-prove! (if up? 'rr-in-rr-ext-up 'rr-in-rr-ext-down)
      (list 'FORALL 'x (list 'IMPLIES '(IN x RR) (list 'IN 'x cls)))
      (lambda ()
        (let ((x (car (eis-vars (dk-peel!)))))
          (eis-close-in! s x (list 'IN x 'RR)))))
    ;; the infinity is on the line
    (eis-prove! (eis-inf-in-name up?)
      (list 'IN inf cls)
      (lambda ()
        (eis-refl! inf)
        (eis-close-in! s inf (list '= inf inf))))
    ;; the line is part of RR-STAR
    (eis-prove! (eis-nm up? "in-rr-star")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls) '(IN x RR-STAR)))
      (lambda ()
        (let* ((x (car (eis-vars (dk-peel!))))
               (i1 (dk-cite! (eis-memb s) x))
               (i2 (dk-cite! 'rr-star-membership x)))
          (if (dk-only! i1 i2 (list 'IN x cls)) (prop)))))
    ;; the infinity bounds the line
    (eis-prove! (eis-bound-name up?)
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls) (if up? '(<= x POS-INF) '(<= NEG-INF x))))
      (lambda ()
        (let ((x (car (eis-vars (dk-peel!)))))
          (dk-cite! (eis-nm up? "in-rr-star") x)
          (dk-cite! (if up? 'pos-inf-upper-bound 'neg-inf-lower-bound) x)
          (ass))))))
(eis-points! #t)
(eis-points! #f)

;;; ===========================================================================
;;; (2) THE ORDER.  The one step where the infinity axiom is used: an element of the line
;;; on the far side of a REAL from the infinity is a real.
;;;   up:   x in U, t in RR, x <= t  =>  x in RR      (pos-inf-above-reals)
;;;   down: x in D, t in RR, t <= x  =>  x in RR      (neg-inf-below-reals)

(define (eis-real-side-name up?) (if up? 'rr-ext-up-le-real-in-rr 'rr-ext-down-ge-real-in-rr))

(define (eis-real-side! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (cls (eis-cls s)))
    (eis-prove! (eis-real-side-name up?)
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list 'FORALL 'y (list 'IMPLIES '(IN y RR)
          (list 'IMPLIES (if up? '(<= x y) '(<= y x)) '(IN x RR))))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs))
               (bad (if up? (list '<= inf y) (list '<= y inf))))
          (eis-cases! s x
            (lambda () (ass))
            (lambda ()
              (dk-have! bad (lambda () (subst (list '= inf x)) (ass)))
              (fact (if up? 'pos-inf-above-reals 'neg-inf-below-reals) y)
              (ai (list 'NOT bad)))))))))
(eis-real-side! #t)
(eis-real-side! #f)

;;; reflexivity
(define (eis-refl-law! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (cls (eis-cls s)))
    (eis-prove! (eis-nm up? "le-refl")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls) '(<= x x)))
      (lambda ()
        (let ((x (car (eis-vars (dk-peel!)))))
          (eis-cases! s x
            (lambda () (fact 'rr-leq-reflexive x) (ass))
            (lambda ()
              (subst (list '= x inf))
              (fact (eis-inf-in-name up?))
              (dk-cite! (eis-bound-name up?) inf)
              (ass))))))))
(eis-refl-law! #t)
(eis-refl-law! #f)

;;; transitivity.  up: split on z (z = +inf is the top); down: split on x (x = -inf is the
;;; bottom).  Otherwise the real-side lemma makes all three real and ineq closes.
(define (eis-trans-law! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (cls (eis-cls s)))
    (eis-prove! (eis-nm up? "le-trans")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list 'FORALL 'y (list 'IMPLIES (list 'IN 'y cls)
          (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z cls)
            '(IMPLIES (<= x y) (IMPLIES (<= y z) (<= x z)))))))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs)) (z (caddr vs))
               (pivot (if up? z x)))
          (eis-cases! s pivot
            (lambda ()
              (if up?
                  (begin (dk-cite! (eis-real-side-name up?) y z)
                         (dk-cite! (eis-real-side-name up?) x y))
                  (begin (dk-cite! (eis-real-side-name up?) y x)
                         (dk-cite! (eis-real-side-name up?) z y)))
              (dk-ineq! (list 'IN x 'RR) (list 'IN y 'RR) (list 'IN z 'RR)
                        (list '<= x y) (list '<= y z)))
            (lambda ()
              (subst (list '= pivot inf))
              (dk-cite! (eis-bound-name up?) (if up? x z))
              (ass))))))))
(eis-trans-law! #t)
(eis-trans-law! #f)

;;; antisymmetry
(define (eis-antisymm-law! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (cls (eis-cls s))
         (ax (if up? 'pos-inf-above-reals 'neg-inf-below-reals)))
    (eis-prove! (eis-nm up? "le-antisymm")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list 'FORALL 'y (list 'IMPLIES (list 'IN 'y cls)
          '(IMPLIES (<= x y) (IMPLIES (<= y x) (= x y)))))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs))
               (p (if up? y x)) (q (if up? x y)))
          ;; up splits on y (the larger), down on x (the smaller): the real case makes the
          ;; other real by the real-side lemma
          (eis-cases! s p
            (lambda ()
              (if up?
                  (dk-cite! (eis-real-side-name up?) x y)
                  (dk-cite! (eis-real-side-name up?) y x))
              (eis-and! (list 'IN x 'RR) (list 'IN y 'RR))
              (eis-and! (list '<= x y) (list '<= y x))
              (dk-cite! 'rr-leq-antisymmetric x y)
              (ass))
            (lambda ()
              (eis-cases! s q
                (lambda ()
                  ;; up: y = +inf <= x real; down: y real <= x = -inf
                  (let ((bad (if up? (list '<= inf x) (list '<= y inf))))
                    (dk-have! bad (lambda () (subst (list '= inf p)) (ass)))
                    (fact ax q)
                    (ai (list 'NOT bad))))
                (lambda ()
                  (subst (list '= x inf))
                  (subst (list '= y inf))
                  (rfl))))))))))
(eis-antisymm-law! #t)
(eis-antisymm-law! #f)

;;; ===========================================================================
;;; (3) THE VALUES of the operation: real + real, and the infinity absorbing on each side.

;;; (NOT (= TM inf)) from (TM in RR): the infinity is not a real
(define (eis-not-inf! s tm)
  (let ((g (list 'NOT (list '= tm (eis-inf s)))))
    (if (not (dk-asm? g))
        (dk-have! g
          (lambda ()
            (di)
            (dk-have! (list 'IN (eis-inf s) 'RR) (lambda () (subst (list '= (eis-inf s) tm)) (ass)))
            (fact (eis-nrr s))
            (ai (list 'NOT (list 'IN (eis-inf s) 'RR))))))))

(define (eis-goal-if) (cadr (dk-goal)))   ; the goal is (= (IF ...) rhs) after the unfold

(define (eis-real-value! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (op (eis-op s)))
    (eis-prove! (eis-on up? "real")
      (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
        (list 'FORALL 'y (list 'IMPLIES '(IN y RR)
          (list '= (list op 'x 'y) '(+ x y))))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs)))
          (eis-not-inf! s x)
          (eis-not-inf! s y)
          (dk-have! (list 'NOT (list 'OR (list '= x inf) (list '= y inf))) (lambda () (prop)))
          (mac op)
          (dk-if-branch! #f (eis-goal-if) #f (lambda () (rfl))))))))
(eis-real-value! #t)
(eis-real-value! #f)

(define (eis-left-name up?)  (eis-on up? (if up? "pos-inf-left" "neg-inf-left")))
(define (eis-right-name up?) (eis-on up? (if up? "pos-inf-right" "neg-inf-right")))

;;; inf + y = inf and y + inf = inf, for y on the line
(define (eis-absorb! up? left?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (op (eis-op s)) (cls (eis-cls s)))
    (eis-prove! (if left? (eis-left-name up?) (eis-right-name up?))
      (list 'FORALL 'y (list 'IMPLIES (list 'IN 'y cls)
        (list '= (if left? (list op inf 'y) (list op 'y inf)) inf)))
      (lambda ()
        (let ((y (car (eis-vars (dk-peel!)))))
          (eis-refl! inf)
          (dk-have! (if left?
                        (list 'OR (list '= inf inf) (list '= y inf))
                        (list 'OR (list '= y inf) (list '= inf inf)))
                    (lambda () (prop)))
          (mac op)
          (dk-if-branch! #t (eis-goal-if) #f (lambda () (rfl))))))))
(eis-absorb! #t #t)
(eis-absorb! #t #f)
(eis-absorb! #f #t)
(eis-absorb! #f #f)

;;; ===========================================================================
;;; (4) THE SEMIGROUP LAWS.

;;; closure
(define (eis-closed-law! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (op (eis-op s)) (cls (eis-cls s)))
    (eis-prove! (eis-on up? "closed")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list 'FORALL 'y (list 'IMPLIES (list 'IN 'y cls)
          (list 'IN (list op 'x 'y) cls)))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs)))
          (eis-cases! s x
            (lambda ()
              (eis-cases! s y
                (lambda ()
                  (eis-rw! (eis-on up? "real") x y)
                  (eis-and! (list 'IN x 'RR) (list 'IN y 'RR))
                  (dk-cite! 'rr-add-closed x y)
                  (eis-close-in! s (list '+ x y) (list 'IN (list '+ x y) 'RR)))
                (lambda ()
                  (subst (list '= y inf))
                  (eis-rw! (eis-right-name up?) x)
                  (fact (eis-inf-in-name up?))
                  (ass))))
            (lambda ()
              (subst (list '= x inf))
              (eis-rw! (eis-left-name up?) y)
              (fact (eis-inf-in-name up?))
              (ass))))))))
(eis-closed-law! #t)
(eis-closed-law! #f)

;;; commutativity
(define (eis-comm-law! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (op (eis-op s)) (cls (eis-cls s)))
    (eis-prove! (eis-on up? "comm")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list 'FORALL 'y (list 'IMPLIES (list 'IN 'y cls)
          (list '= (list op 'x 'y) (list op 'y 'x))))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs)))
          (eis-cases! s x
            (lambda ()
              (eis-cases! s y
                (lambda ()
                  (eis-rw! (eis-on up? "real") x y)
                  (eis-rw! (eis-on up? "real") y x)
                  (eis-and! (list 'IN x 'RR) (list 'IN y 'RR))
                  (dk-cite! 'rr-add-comm x y)
                  (ass))
                (lambda ()
                  (subst (list '= y inf))
                  (eis-rw! (eis-right-name up?) x)
                  (eis-rw! (eis-left-name up?) x)
                  (rfl))))
            (lambda ()
              (subst (list '= x inf))
              (eis-rw! (eis-left-name up?) y)
              (eis-rw! (eis-right-name up?) y)
              (rfl))))))))
(eis-comm-law! #t)
(eis-comm-law! #f)

;;; associativity
(define (eis-assoc-law! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (op (eis-op s)) (cls (eis-cls s)))
    (eis-prove! (eis-on up? "assoc")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list 'FORALL 'y (list 'IMPLIES (list 'IN 'y cls)
          (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z cls)
            (list '= (list op (list op 'x 'y) 'z) (list op 'x (list op 'y 'z)))))))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs)) (z (caddr vs))
               (xy (list op x y)) (yz (list op y z)))
          (dk-cite! (eis-on up? "closed") x y)
          (dk-cite! (eis-on up? "closed") y z)
          (eis-cases! s x
            (lambda ()
              (eis-cases! s y
                (lambda ()
                  (eis-cases! s z
                    (lambda ()
                      (eis-rw! (eis-on up? "real") x y)
                      (eis-rw! (eis-on up? "real") y z)
                      (eis-and! (list 'IN x 'RR) (list 'IN y 'RR))
                      (dk-cite! 'rr-add-closed x y)
                      (eis-and! (list 'IN y 'RR) (list 'IN z 'RR))
                      (dk-cite! 'rr-add-closed y z)
                      (eis-rw! (eis-on up? "real") (list '+ x y) z)
                      (eis-rw! (eis-on up? "real") x (list '+ y z))
                      (eis-and! (list 'IN x 'RR) (list 'IN y 'RR) (list 'IN z 'RR))
                      (dk-cite! 'rr-add-assoc x y z)
                      (ass))
                    (lambda ()
                      ;; (x + y) + inf = inf = x + inf = x + (y + inf)
                      (subst (list '= z inf))
                      (eis-rw! (eis-right-name up?) xy)
                      (eis-rw! (eis-right-name up?) y)
                      (eis-rw! (eis-right-name up?) x)
                      (rfl))))
                (lambda ()
                  ;; (x + inf) + z = inf + z = inf = x + inf = x + (inf + z)
                  (subst (list '= y inf))
                  (eis-rw! (eis-right-name up?) x)
                  (eis-rw! (eis-left-name up?) z)
                  (eis-rw! (eis-right-name up?) x)
                  (rfl))))
            (lambda ()
              ;; (inf + y) + z = inf + z = inf = inf + (y + z)
              (subst (list '= x inf))
              (eis-rw! (eis-left-name up?) y)
              (eis-rw! (eis-left-name up?) yz)
              (eis-rw! (eis-left-name up?) z)
              (rfl))))))))
(eis-assoc-law! #t)
(eis-assoc-law! #f)

;;; 0 is neutral on both sides
(define (eis-zero-law! up? left?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (op (eis-op s)) (cls (eis-cls s)))
    (eis-prove! (eis-on up? (if left? "zero-left" "zero-right"))
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list '= (if left? (list op 0 'x) (list op 'x 0)) 'x)))
      (lambda ()
        (let ((x (car (eis-vars (dk-peel!)))))
          (fact 'rr-zero-in)
          (eis-cases! s x
            (lambda ()
              (if left?
                  (begin
                    (eis-rw! (eis-on up? "real") 0 x)
                    (eis-and! '(IN 0 RR) (list 'IN x 'RR))
                    (eis-rw! 'rr-add-comm 0 x))
                  (eis-rw! (eis-on up? "real") x 0))
              (dk-cite! 'rr-add-zero x)
              (ass))
            (lambda ()
              (subst (list '= x inf))
              (eis-in! s 0 '(IN 0 RR))
              (if left?
                  (eis-rw! (eis-right-name up?) 0)
                  (eis-rw! (eis-left-name up?) 0))
              (rfl))))))))
(eis-zero-law! #t #t)
(eis-zero-law! #t #f)
(eis-zero-law! #f #t)
(eis-zero-law! #f #f)

;;; ORDER COMPATIBILITY: x <= y  =>  x + z <= y + z.
;;; up:   z = +inf: both sides +inf.  z real, y = +inf: the right side is +inf, the top.
;;;       z, y real: x is real (rr-ext-up-le-real-in-rr) and ineq closes.
;;; down: z = -inf: both sides -inf.  z real, x = -inf: the left side is -inf, the bottom.
;;;       z, x real: y is real (rr-ext-down-ge-real-in-rr) and ineq closes.
(define (eis-mono-law! up?)
  (let* ((s (eis-side up?)) (inf (eis-inf s)) (op (eis-op s)) (cls (eis-cls s)))
    (eis-prove! (eis-on up? "mono")
      (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x cls)
        (list 'FORALL 'y (list 'IMPLIES (list 'IN 'y cls)
          (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z cls)
            (list 'IMPLIES '(<= x y) (list '<= (list op 'x 'z) (list op 'y 'z)))))))))
      (lambda ()
        (let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs)) (z (caddr vs))
               (piv (if up? y x)))
          (dk-cite! (eis-on up? "closed") x z)
          (dk-cite! (eis-on up? "closed") y z)
          (eis-cases! s z
            (lambda ()
              (eis-cases! s piv
                (lambda ()
                  (if up?
                      (dk-cite! (eis-real-side-name up?) x y)
                      (dk-cite! (eis-real-side-name up?) y x))
                  (eis-rw! (eis-on up? "real") x z)
                  (eis-rw! (eis-on up? "real") y z)
                  (dk-ineq! (list 'IN x 'RR) (list 'IN y 'RR) (list 'IN z 'RR) (list '<= x y)))
                (lambda ()
                  (subst (list '= piv inf))
                  (eis-rw! (eis-left-name up?) z)
                  (dk-cite! (eis-bound-name up?) (list op (if up? x y) z))
                  (ass))))
            (lambda ()
              (subst (list '= z inf))
              (eis-rw! (eis-right-name up?) x)
              (eis-rw! (eis-right-name up?) y)
              (fact (eis-inf-in-name up?))
              (dk-cite! (eis-nm up? "le-refl") inf)
              (ass))))))))
(eis-mono-law! #t)
(eis-mono-law! #f)

;;; ===========================================================================
;;; (5) THE BRIDGE: on [0, +inf] EPLUS-UP is the library's eplus.

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR) (IN x RR-EXT-UP)))))
(let* ((x (car (eis-vars (dk-peel!))))
       (i1 (dk-cite! 'rr-pos-star-membership x))
       (i2 (dk-cite! 'rr-ext-up-membership x)))
  (if (dk-only! i1 i2 (list 'IN x 'RR-POS-STAR)) (prop)))
(qed 'rr-pos-star-in-rr-ext-up)
(topic! 'rr-pos-star-in-rr-ext-up 'analysis)

(define (eis-pos-cases! tm real-body inf-body)
  (let ((rc (list 'AND (list 'IN tm 'RR) (list '<= 0 tm)))
        (ic (list '= tm 'POS-INF)))
    (dk-have! (list 'OR rc ic)
      (lambda ()
        (let ((i (dk-cite! 'rr-pos-star-membership tm)))
          (if (dk-only! i (list 'IN tm 'RR-POS-STAR)) (prop)))))
    (eis-use-cases! (list rc ic)
      (lambda () (dk-split! rc) (real-body))
      inf-body)))

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR)
                 (FORALL y (IMPLIES (IN y RR-POS-STAR)
                   (= (EPLUS-UP x y) (eplus x y))))))))
(let* ((vs (eis-vars (dk-peel!))) (x (car vs)) (y (cadr vs)))
  (dk-cite! 'rr-pos-star-in-rr-ext-up x)
  (dk-cite! 'rr-pos-star-in-rr-ext-up y)
  (eis-pos-cases! x
    (lambda ()
      (eis-pos-cases! y
        (lambda ()
          (eis-rw! 'eplus-up-real x y)
          (eis-rw! 'eplus-real-defined x y)
          (eis-rw! 'binplus-apply x y)
          (rfl))
        (lambda ()
          (subst (list '= y 'POS-INF))
          (eis-rw! 'eplus-up-pos-inf-right x)
          (eis-rw! 'eplus-pos-inf-right x)
          (rfl))))
    (lambda ()
      (subst (list '= x 'POS-INF))
      (eis-rw! 'eplus-up-pos-inf-left y)
      (eis-rw! 'eplus-pos-inf-left y)
      (rfl))))
(qed 'eplus-up-agrees-eplus)
(topic! 'eplus-up-agrees-eplus 'analysis)
