;;; rake-nf-norm.scm -- rake batch 5b-D: the norm of a negative, and the metric
;;; space underlying a normed field.
;;;
;;;   nf-norm-neg                      NEW.  In a normed field,
;;;                                    ||-a|| = ||a||.
;;;   nf-metric-space-is-metric-space  structure-library/normed-field-metric.scm:73
;;;                                    (support, warrant at founder-warrants.scm:46)
;;;
;;; WHY THE FIRST IS NEEDED.  `is-group-norm' (operation-properties.scm:74) has
;;; five clauses and `is-norm' (:59) has four of them; the fifth, INVERSE
;;; INVARIANCE
;;;
;;;     forall a in CARR(nf).  FNRM(nf)((NEG nf) a) = FNRM(nf)(a),
;;;
;;; is absent from `is-norm' because a FIELD norm gets it from MULTIPLICATIVITY
;;; instead of carrying it.  With it, nf-metric-space-is-metric-space is the
;;; generic lemma `ag-norm-metric-is-metric-space' (theorem-library/
;;; rake-norm-metrics.scm) at the view NORMED-FIELD-ADDITIVE-AG(nf) -- exactly
;;; the ten lines that file's section (6) spends on the NORMED-AG instance.
;;;
;;; THE ROUTE IS THE SQUARE, NOT THE UNIT.  rake-norm-metrics.scm's closing note
;;; routes ||-a|| = ||a|| through ||1||: -a = (-1).a, so ||-a|| = ||-1||.||a||,
;;; and ||-1|| = 1 needs ||1|| = 1, which is FALSE in the degenerate normed field
;;; where ONE = ZERO -- hence that route's case split, and hence its warning that
;;; citing `normed-field-zero-not-one' (an UNWARRANTED axiom) to avoid the split
;;; would make the result `trust: none'.  The square route needs neither:
;;;
;;;     ||-a||.||-a||  =  ||(-a).(-a)||  =  ||a.a||  =  ||a||.||a||
;;;
;;; by multiplicativity at both ends and (-a).(-a) = a.a in the middle, and then
;;; `sqrt-unique' (theorem-library/sqrt-defined.scm:189 -- 0 <= x, 0 <= y,
;;; x.x = y.y => x = y) closes it, the two norms being nonnegative.  ONE is never
;;; mentioned, there is no case split, and nothing unwarranted is cited: the bill
;;; is `modulo 0'.  (-a).(-a) = a.a is four citations in the ring world, reached
;;; through NORMED-FIELD-AS-COMMUTATIVE-RING -- a normed field is a 7-tuple and
;;; the ring predicates pin length 6, so the ring facts hold of the PROJECTION and
;;; are carried back by the three slot read-offs proved here.
;;;
;;; LOAD WINDOW [472, end), i.e. immediately after theorem-library/
;;; rake-norm-metrics (position 471), which is what `ag-norm-metric-is-metric-space'
;;; forces.  The next constraints down are sqrt-defined (388, sqrt-unique),
;;; rake-finsum-core (248, commutative-ring-mul-comm), rake-algebra2 (229,
;;; ring-neg-neg / ring-neg-mul-left), op-typing (201, ring-neg-in-carr /
;;; ring-carrier-closed-mul), subtype-laws (200, commutative-ring-is-ring),
;;; fun-apply-type-proof (162, fun-apply-type-c), equality-basics (148, eq-sym),
;;; and the structure files views (60, the two view typing axioms) /
;;; normed-field-metric (61, NF-METRIC-SPACE).  No proven theorem cites
;;; nf-metric-space-is-metric-space, so nothing forces hi.
;;;
;;; Dependencies: interactive, proof-debt, driver-kit.

;;; ---- file-local driver (the `r6d-' prefix) ---------------------------

(define r6d-ring '(NORMED-FIELD-AS-COMMUTATIVE-RING nf))
(define r6d-ag   '(NORMED-FIELD-ADDITIVE-AG nf))

(define (r6d-mulr x y) (list (list 'MUL r6d-ring) x y))
(define (r6d-negr x)   (list (list 'NEG r6d-ring) x))
(define (r6d-mulf x y) (list '(MUL nf) x y))
(define (r6d-negf x)   (list '(NEG nf) x))
(define (r6d-nrm x)    (list '(FNRM nf) x))

(define (r6d-find lst pred what)
  (or (find-first pred lst) (error "r6d-find: missing" what)))

;;; A def-functor view's slot read-off, in whichever orientation is asked for.
;;; After r5r-slot-close! (theorem-library/rake-norm-metrics.scm), widened to a
;;; view whose TARGET accessor differs from its SOURCE accessor (OPR read off
;;; ADD): both are offered at each turn, and where the two coincide (CARR off
;;; CARR) the LIST element `slot' exposes is itself an accessor application, so
;;; one slot + nth-r does not settle it -- iterate to a fixpoint.
(define (r6d-slot-close! view . accs)
  (mac view)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (< n 8) (not (equal? (cadr g) (caddr g))))
          (begin (for-each (lambda (acc) (quietly (lambda () (slot acc)))) accs)
                 (quietly (lambda () (nth-r)))
                 (if (not (equal? (dk-goal) g)) (loop (+ n 1)))))))
  (qrfl))

;;; (r6d-readoff! TACC SACC SRC VIEW) -- both orientations of
;;; TACC(VIEW(SRC)) == SACC(SRC), landed as context assumptions.
(define (r6d-readoff! tacc sacc src view)
  (let ((lhs (list tacc (list view src)))
        (rhs (list sacc src))
        (accs (if (eq? tacc sacc) (list tacc) (list tacc sacc))))
    (dk-have! (list '== lhs rhs)
              (lambda () (apply r6d-slot-close! view accs)))
    (dk-have! (list '== rhs lhs)
              (lambda () (apply r6d-slot-close! view accs)))))

;;; the universal of the `is-norm' unfold -- named by its CONSEQUENT (an AND
;;; whose first conjunct is 0 <= nm(a)), never by its head.
(define (r6d-nu)
  (dk-pick (lambda (f)
             (and (pair? f) (eq? (car f) 'FORALL)
                  (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                  (pair? (caddr (caddr f))) (eq? (car (caddr (caddr f))) 'AND)
                  (let ((c1 (cadr (caddr (caddr f)))))
                    (and (pair? c1) (eq? (car c1) '<=) (equal? (cadr c1) 0)))))
           "the is-norm universal"))

;;; the norm facts at u: 0 <= ||u||, the definiteness IFF, and the b-universal.
(define (r6d-norm-at! u)
  (dk-split! (dk-apply! (r6d-nu) u)))

;;; ||u.u|| = ||u||.||u||, from the b-universal of the norm facts at u.
(define (r6d-mult-at! u)
  (let* ((atoms (r6d-norm-at! u))
         (inner (r6d-find atoms (dk-head? 'FORALL) "the is-norm b-universal")))
    (dk-split! (dk-apply! inner u))
    (list '= (r6d-nrm (r6d-mulf u u)) (list '* (r6d-nrm u) (r6d-nrm u)))))

;;; =====================================================================
;;; (1) nf-norm-neg -- ||-a|| = ||a|| in a normed field.
;;; =====================================================================

(sp (make-wff '(FORALL nf (IMPLIES (IS-NORMED-FIELD nf)
     (FORALL a_ (IMPLIES (IN a_ (CARR nf))
       (= ((FNRM nf) ((NEG nf) a_)) ((FNRM nf) a_))))))))
(dk-peel!)

;;; (1a) the ring world.  The view typing axiom FIRST: `mac-h' REPLACES
;;; IS-NORMED-FIELD below, and that hypothesis is the axiom's antecedent.
(fact 'normed-field-as-commutative-ring-is-commutative-ring 'nf)
(fact 'commutative-ring-is-ring r6d-ring)
(for-each (lambda (acc) (r6d-readoff! acc acc 'nf 'NORMED-FIELD-AS-COMMUTATIVE-RING))
          '(CARR MUL NEG))
(dk-have! (list 'IN 'a_ (list 'CARR r6d-ring))
          (lambda () (subst (list '== (list 'CARR r6d-ring) '(CARR nf))) (ass)))

;;; (1b) (-a).(-a) = a.a, in the ring view.
(fact 'ring-neg-in-carr r6d-ring 'a_)
(fact 'ring-carrier-closed-mul r6d-ring 'a_ 'a_)
(fact 'ring-neg-mul-left r6d-ring 'a_ (r6d-negr 'a_))
(fact 'commutative-ring-mul-comm r6d-ring 'a_ (r6d-negr 'a_))
(fact 'ring-neg-mul-left r6d-ring 'a_ 'a_)
(fact 'ring-neg-neg r6d-ring (r6d-mulr 'a_ 'a_))
(dk-have! (list '= (r6d-mulr (r6d-negr 'a_) (r6d-negr 'a_)) (r6d-mulr 'a_ 'a_))
  (lambda ()
    (subst (list '= (r6d-mulr (r6d-negr 'a_) (r6d-negr 'a_))
                    (r6d-negr (r6d-mulr 'a_ (r6d-negr 'a_)))))
    (subst (list '= (r6d-mulr 'a_ (r6d-negr 'a_)) (r6d-mulr (r6d-negr 'a_) 'a_)))
    (subst (list '= (r6d-mulr (r6d-negr 'a_) 'a_) (r6d-negr (r6d-mulr 'a_ 'a_))))
    (subst (list '= (r6d-negr (r6d-negr (r6d-mulr 'a_ 'a_))) (r6d-mulr 'a_ 'a_)))
    (rfl)))

;;; (1c) the same equation on the normed field's own accessors.
(dk-have! (list '= (r6d-mulf (r6d-negf 'a_) (r6d-negf 'a_)) (r6d-mulf 'a_ 'a_))
  (lambda ()
    (subst (list '== '(MUL nf) (list 'MUL r6d-ring)))
    (subst (list '== '(NEG nf) (list 'NEG r6d-ring)))
    (ass)))

;;; (1d) the norm.  Unfolding IS-NORMED-FIELD is destructive and everything
;;; above is already landed, so this is where it goes.
(dk-split-all! (dk-landed* (lambda () (mac-h 'is-normed-field '(IS-NORMED-FIELD nf)))))
(dk-split-all!
 (dk-landed* (lambda () (mac-h 'is-norm '(is-norm (FNRM nf) (ADD nf) (MUL nf)
                                                  (ZERO nf) (CARR nf))))))
(dk-have! (list 'IN (r6d-negf 'a_) '(CARR nf))
          (lambda () (fact 'fun-apply-type-c '(NEG nf) '(CARR nf) '(CARR nf) 'a_) (ass)))
(fact 'fun-apply-type-c '(FNRM nf) '(CARR nf) 'RR 'a_)
(fact 'fun-apply-type-c '(FNRM nf) '(CARR nf) 'RR (r6d-negf 'a_))

;;; (1e) multiplicativity at a and at -a, and the square equation between them.
(let* ((na  (r6d-nrm 'a_))
       (nna (r6d-nrm (r6d-negf 'a_)))
       (e2  (r6d-mult-at! 'a_))
       (e1  (r6d-mult-at! (r6d-negf 'a_))))
  (fact 'eq-sym (cadr e1) (caddr e1))
  (dk-have! (list '= (list '* nna nna) (list '* na na))
    (lambda ()
      (subst (list '= (caddr e1) (cadr e1)))
      (subst (list '= (r6d-mulf (r6d-negf 'a_) (r6d-negf 'a_)) (r6d-mulf 'a_ 'a_)))
      (subst e2)
      (rfl)))
  (have! (list 'AND (list 'IN nna 'RR) (list 'IN na 'RR)))
  (have! (list 'AND (list '<= 0 nna) (list '<= 0 na)))
  (fact 'sqrt-unique nna na)
  (ass))
(qed 'nf-norm-neg)
(topic! 'nf-norm-neg 'algebra)
(alias! 'nf-norm-neg "the norm of a negative" "||-a|| = ||a|| in a normed field")

;;; =====================================================================
;;; (2) nf-metric-space-is-metric-space -- the generic norm-metric lemma at
;;; the view NORMED-FIELD-ADDITIVE-AG(nf)
;;; =====================================================================

;;; is-group-norm(FNRM nf, ADD nf, NEG nf, ZERO nf, CARR nf), from the four
;;; clauses of `is-norm' plus nf-norm-neg.  UNIV is the nf-norm-neg universal,
;;; already detached in the context.
(define (r6d-group-norm! univ)
  (mac 'is-group-norm)
  (for-each
   (lambda (k)
     (dk-focus! k)
     (if (eq? (car (dk-goal)) 'IN)
         (ass)                                  ; the FNRM typing conjunct
         (let* ((landed (dk-peel!))
                (u (cadr (r6d-find landed (dk-head? 'IN)
                                   "the typing of the bound element"))))
           (dk-have! (list 'IN (r6d-negf u) '(CARR nf))
                     (lambda ()
                       (fact 'fun-apply-type-c '(NEG nf) '(CARR nf) '(CARR nf) u)
                       (ass)))
           (let* ((atoms (r6d-norm-at! u))
                  (inner (r6d-find atoms (dk-head? 'FORALL)
                                   "the is-norm b-universal")))
             (dk-apply! univ u)                 ; ||-u|| = ||u||
             (dk-conj-close!
              (lambda ()
                (if (eq? (car (dk-goal)) 'FORALL)
                    (let* ((lv (dk-peel!))
                           (v (cadr (r6d-find lv (dk-head? 'IN)
                                              "the typing of the second element"))))
                      (dk-split! (dk-apply! inner v))
                      (ass))
                    (ass))))))))
   (dk-opened (lambda () (di)))))

(sp (make-wff '(FORALL nf
     (IMPLIES (IS-NORMED-FIELD nf)
       (IS-METRIC-SPACE (NF-METRIC-SPACE nf))))))
(dk-peel-to! 'IS-METRIC-SPACE)
;; the view typing axiom and nf-norm-neg FIRST: both have IS-NORMED-FIELD as
;; their antecedent, and `mac-h' REPLACES it.
(fact 'normed-field-additive-ag-is-abelian-group 'nf)
(let ((univ (dk-fact! 'nf-norm-neg 'nf)))
  (dk-split-all! (dk-landed* (lambda () (mac-h 'is-normed-field '(IS-NORMED-FIELD nf)))))
  (dk-split-all!
   (dk-landed* (lambda () (mac-h 'is-norm '(is-norm (FNRM nf) (ADD nf) (MUL nf)
                                                    (ZERO nf) (CARR nf))))))
  (for-each (lambda (p) (r6d-readoff! (car p) (cadr p) 'nf 'NORMED-FIELD-ADDITIVE-AG))
            '((CARR CARR) (OPR ADD) (IDEN ZERO) (INV NEG)))
  (dk-have! (list 'is-group-norm '(FNRM nf) (list 'OPR r6d-ag) (list 'INV r6d-ag)
                  (list 'IDEN r6d-ag) (list 'CARR r6d-ag))
    (lambda ()
      (for-each (lambda (p) (subst (list '== (list (car p) r6d-ag) (list (cadr p) 'nf))))
                '((OPR ADD) (INV NEG) (IDEN ZERO) (CARR CARR)))
      (r6d-group-norm! univ))))
(dk-fact! 'ag-norm-metric-is-metric-space r6d-ag '(FNRM nf))
(mac 'NF-METRIC-SPACE)
(for-each (lambda (p) (subst (list '== (list (cadr p) 'nf) (list (car p) r6d-ag))))
          '((OPR ADD) (INV NEG) (CARR CARR)))
(ass)
(qed 'nf-metric-space-is-metric-space)
(topic! 'nf-metric-space-is-metric-space 'constructions)
