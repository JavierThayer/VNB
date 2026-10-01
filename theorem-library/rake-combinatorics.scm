;;; rake-combinatorics.scm -- BATCH P of the 2026-09-17 rake: NN combinatorics,
;;; the ring powers, the powerset insert-split, and the two CHOOSE boundary
;;; values.  Seventeen asserted supports, PROVEN; every statement is copied
;;; LITERALLY from its site.
;;;
;;;   bt-mul-comm            theorem-library/binomial.scm:61  (the proof was
;;;                          REMOVED 2026-09-20: a duplicate of
;;;                          commutative-ring-mul-comm)
;;;   succ-nn-ord            theorem-library/succ-nn-ord.scm:10
;;;   union-empty-left       theorem-library/union-empty-left.scm:9
;;;   ord-segment-trans      theorem-library/ord-segment-trans.scm:9
;;;   power-zero-base        theorem-library/taylor-proof.scm:391   (add-to-pss)
;;;   ring-power-one         structure-library/ring-power.scm:34
;;;   ring-power-succ        theorem-library/finsum-additive.scm:116
;;;   ring-power-add         structure-library/ring-power.scm:44
;;;   ring-power-mult        structure-library/ring-power.scm:56
;;;   prod-ring-empty        theorem-library/prod-of-sums.scm:139
;;;   prod-ring-singleton    theorem-library/prod-of-sums.scm:149
;;;   prod-ring-insert       theorem-library/prod-of-sums.scm:162
;;;   power-insert-cover     theorem-library/prod-of-sums.scm:95
;;;   power-insert-disjoint  theorem-library/prod-of-sums.scm:110
;;;   card-power-nn          theorem-library/prod-of-sums.scm:79
;;;   choose-n-0             structure-library/injection.scm:287
;;;   choose-0-succ          structure-library/injection.scm:289
;;;
;;; BILLS: fifteen are `proven modulo 0'.  prod-ring-insert and
;;; prod-ring-singleton bill `{finsum-comm-monoid-well-defined}' [informal] --
;;; they ARE finsum-insert at the multiplicative view, and finsum-insert
;;; (theorem-library/finsum-insert.scm) bills that one leaf.  It is batch N's.
;;;
;;; NOT PROVEN HERE: choose-succ (Pascal's rule, structure-library/
;;; injection.scm:291).  See the batch report; the two halves of the insert
;;; split it needs are `power-insert-cover' / `power-insert-disjoint', proved
;;; here, but the rule itself wants the split at the level of CHOOSE-SET (the
;;; (k+1)-subsets of a segment), i.e. a bijection between the k-subsets of
;;; ORD-SEGMENT(n) and the (k+1)-subsets of ORD-SEGMENT(succ n) that contain n,
;;; plus card-union-disjoint and card-image-injection -- injectivity of
;;; S |-> S u {n} is a further set-surgery argument.  A separate assignment.
;;;
;;; TEN AUXILIARY THEOREMS are installed beside them, each the rung the tree
;;; was missing:
;;;
;;;   crmcm-op / crmcm-iden      the multiplicative view's OPR / IDEN read-offs,
;;;                              the twins of `crmcm-carr' (theorem-library/
;;;                              rake-finsum-typing.scm).  `def-functor'
;;;                              installs no per-slot projection, so every view
;;;                              slot needs one; this file needed two more.
;;;   ring-power-succ-left       x^(succ n) = x * x^n -- mpow-succ read through
;;;                              the view.  The `=' half of it is bought from
;;;                              ring-power-type + ring-carrier-closed-mul; the
;;;                              equation itself is proved as a `==' in a lane
;;;                              and substituted into the goal.
;;;   ring-mul-interchange       (a*b)*(c*d) = (a*c)*(b*d) in a commutative
;;;                              ring.  `crs' does NOT reach it -- the
;;;                              normalizer knows surface + and *, not (MUL R)
;;;                              -- and abelian-group-opr-interchange (rake-
;;;                              finsum-laws.scm) wants inverses the
;;;                              multiplicative monoid has not got.
;;;   ring-power-add-ind         ring-power-add with the EXPONENT k outermost,
;;;   ring-power-mult-ind        ring-power-mult with n outermost: `ni' tests
;;;                              the goal's SHAPE, and both supports quantify
;;;                              the ring first.  One `fact' recovers the
;;;                              site's binder order.
;;;   choose-set-unfold          the CHOOSE-SET functoid's unfold as a THEOREM,
;;;                              so `mac-h' can open a CHOOSE-SET membership in
;;;                              a HYPOTHESIS (CLAUDE.md, the def-functoid
;;;                              mac-h trap).  One line.
;;;   card-zero-is-empty         REMOVED 2026-09-20 (batch 9-B): the same statement is
;;;                              proven far above, in
;;;                              theorem-library/rake-card-star-laws.scm, without any
;;;                              induction -- and keeping both made the citation graph
;;;                              circular once `finite-set-induction' became a theorem
;;;                              of the DEFINED CARD.  See section (21) below.
;;;   subset-of-empty-is-empty   a subclass of EMPTY-SET is EMPTY-SET.
;;;   power-of-empty             POWER(EMPTY-SET) = {EMPTY-SET}.
;;;
;;; THE ONE MOVE WITH CONTENT is in power-insert-cover: a subset A of X u {k}
;;; that CONTAINS k is the image of A \ {k}, i.e. A = (A \ {k}) u {k}.  That is
;;; the set surgery CLAUDE.md records as blocked for finsum-embed, and it is
;;; NOT blocked here: `difference-membership' (theorem-library/
;;; difference-laws.scm) plus set extensionality does it, with `prop' on a
;;; context TRIMMED by dk-only! -- untrimmed, prop's atom cap drops the pair it
;;; needs.  What finsum-embed additionally wants is a CONVERSE of card-insert,
;;; which is still missing; the cardinality side of the same surgery is not.
;;;
;;; THREE DRIVER TRAPS, each of which cost a probe:
;;;   * `fact' of a membership IFF lands BOTH the instance and the universal,
;;;     and dk-deepest cannot tell them apart (neither contains the other), so
;;;     dk-only! -- which compares with `member' -- may keep the wrong one and
;;;     `prop' then reports a countermodel naming the UNIVERSAL as an opaque
;;;     atom.  the kit's `iff-for' names the instance by its left-hand side.
;;;   * `pairing-membership' has its guard BETWEEN its binders (forall a, b.
;;;     a,b in SET => forall x. ...), so `fact' stops at the detached
;;;     `forall x' and the element has to be supplied by `inst*!'
;;;     (`rkp-pairmem!').  And a preceding `dk-split-all!' consumes the
;;;     conjoined guard, so it has to be re-assembled.
;;;   * `rfl' on a term whose head is not in `*total-term-heads*' needs a
;;;     membership WITNESS in context, so the typing facts must be landed
;;;     BEFORE the `lam-b' / the final reflexivity, not after.
;;;
;;; LOAD WINDOW [251, 375) -- the file may occupy any slot in it.
;;;   lo = 251: the latest citation is `card-union-nn', PROVEN in
;;;             theorem-library/card-inequalities (position 250).  Next latest:
;;;             card-image-finite (241), crmcm-carr / ring-power-type
;;;             (rake-finsum-typing, 229), nn-succ-nonzero (nn-parity-proof,
;;;             213), ring-one-in / ring-power-zero (ring-zero-one-power, 211),
;;;             ring-carrier-closed-mul (op-typing, 200), commutative-ring-is-ring
;;;             (subtype-laws, 199), difference-membership / difference-set
;;;             (difference-laws, 192), fun-apply-type-c (fun-apply-type-proof,
;;;             163), card-singleton (card-singleton-proof, 156), finsum-empty /
;;;             finsum-insert (finsum-insert, 155), eq-sym / eq-trans
;;;             (equality-basics, 148).  Everything else is primitive or
;;;             definitional (library.scm, number-systems, ordinals, cardinality,
;;;             injection, views, monoid-power, ring-power, finprod, ring).
;;;   hi = 375: theorem-library/binomial-proof cites `ring-power-succ' (:92,
;;;             via macm); theorem-library/bernstein-basis (393) cites it too.
;;;             NO OTHER leaf in this file has a citer anywhere in the tree.
;;;
;;; Helper prefix `rkp-'.  All helpers are file-local.

(define (rkp-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkp: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkp: proof not complete" name))))

(define (rkp-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rkp-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rkp-leaf: ambiguous leaf for" what))
          (#t (car hits)))))
;; base / step of an `ni': the base goal is not a FORALL.
(define (rkp-base leaves) (rkp-leaf leaves (lambda (g) (not (eq? (car g) 'FORALL))) "base"))
(define (rkp-step leaves) (rkp-leaf leaves (lambda (g) (eq? (car g) 'FORALL)) "step"))
;; the other discriminator: the step goal mentions `succ', the base does not.
(define (rkp-base-s leaves) (rkp-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "base"))
(define (rkp-step-s leaves) (rkp-leaf leaves (lambda (g) (dk-contains? g 'succ)) "step"))
;; `fact' of a membership IFF lands BOTH the instance and the universal, and
;; dk-deepest cannot tell them apart (neither contains the other), so name the
;; instance by its left-hand side -- dk-only! compares with `member', so a
;; reconstruction would be weakened away.
;; (iff-for retired 2026-09-25: the kit's `iff-for')
(define (rkp-mem-iff! lhs . args)
  (apply fact args)
  (iff-for lhs))
;; pairing-membership's guard sits BETWEEN its binders (forall a, b. a,b in SET
;; => forall x. ...), and `fact' stops at the detached FORALL x rather than
;; instantiating it, so the element has to be supplied by `inst*!'.
(define (rkp-pairmem! kk v)
  ;; a preceding dk-split-all! may have consumed the conjoined guard
  (let ((g (list 'AND (list 'IN kk 'SET) (list 'IN kk 'SET))))
    (if (not (any-pred (lambda (f) (alpha-equiv? f g)) (dk-asms))) (have! g)))
  (fact 'pairing-membership kk kk)
  (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                    (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                    (equal? (caddr (cadr (caddr f))) (list 'PAIR kk kk))))
                   "the pairing universal")
          v)
  (iff-for (list 'IN v (list 'PAIR kk kk))))

(define rkp-view '(COMMUTATIVE-RING-MULTIPLICATIVE-CM R))
(define (rkp-mul a b) (list '(MUL R) a b))
(define (rkp-pw t n) (list 'RING-POWER 'R t n))

;;; =====================================================================
;;; (1) bt-mul-comm -- the LAW conjunct of IS-COMMUTATIVE-RING; REMOVED
;;; 2026-09-20 (batch 11, proven-duplicate-audit).  It was proved here from
;;; the IS-COMMUTATIVE-RING unfold, and again -- same statement, ring named s
;;; instead of R -- as `commutative-ring-mul-comm'
;;; (theorem-library/rake-finsum-core.scm:1321), which loads before this file.
;;; The three citations below name that one.
;;; =====================================================================

;;; =====================================================================
;;; (2) succ-nn-ord
;;; =====================================================================
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (succ n) (succ_ORD n))))))
(dk-peel!)
(fact 'ord-succ-nn 'n)
(fact 'eq-sym '(succ_ORD n) '(succ n))
(ass)
(rkp-check! 'succ-nn-ord)
(qed 'succ-nn-ord)
(topic! 'succ-nn-ord 'plumbing)

;;; =====================================================================
;;; (3) union-empty-left
;;; =====================================================================
(sp (make-wff '(FORALL A (IMPLIES (IN A SET) (= (UNION EMPTY-SET A) A)))))
(dk-peel!)
(fact 'empty-set-is-set)
(have! '(AND (IN EMPTY-SET SET) (IN A SET)))
(fact 'union-set-closure 'EMPTY-SET 'A)
(have! '(AND (IN (UNION EMPTY-SET A) SET) (IN A SET)))
(fact 'extensionality '(UNION EMPTY-SET A) 'A)
(have! '(FORALL x_ (IFF (IN x_ (UNION EMPTY-SET A)) (IN x_ A)))
  (lambda ()
    (let ((xv (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (mac 'union-membership)
      (fact 'empty-set-has-no-members xv)
      (prop))))
(prop)
(rkp-check! 'union-empty-left)
(qed 'union-empty-left)
(topic! 'union-empty-left 'plumbing)

;;; =====================================================================
;;; (4) ord-segment-trans
;;; =====================================================================
(sp (make-wff
 '(FORALL m (IMPLIES (IN m NN)
    (FORALL k (FORALL i
      (IMPLIES (AND (IN i (ORD-SEGMENT k)) (IN k (ORD-SEGMENT m)))
               (IN i (ORD-SEGMENT m)))))))))
(dk-peel!)
(dk-split-all!)
(fact 'nn-subset-ord 'm)
(fact 'ord-segment-membership 'm 'k)
(have! '(ORD-LT k m) (lambda () (prop)))
(fact 'ord-lt-iff 'k 'm)
(have! '(AND (ORD-LE k m) (NOT (= k m))) (lambda () (prop)))
(dk-split-all!)
(fact 'ord-le-closure 'k 'm)
(dk-split-all!)
(fact 'ord-segment-membership 'k 'i)
(have! '(ORD-LT i k) (lambda () (prop)))
(fact 'ord-lt-iff 'i 'k)
(have! '(AND (ORD-LE i k) (NOT (= i k))) (lambda () (prop)))
(dk-split-all!)
(have! '(AND (ORD-LE i k) (ORD-LE k m)))
(fact 'ord-le-trans 'i 'k 'm)
(have! '(NOT (= i m))
  (lambda ()
    (di)
    (fact 'eq-sym 'i 'm)
    (have! '(ORD-LE m k) (lambda () (subst '(= m i)) (ass)))
    (have! '(AND (ORD-LE m k) (ORD-LE k m)))
    (fact 'ord-le-antisymm 'm 'k)
    (fact 'eq-sym 'm 'k)
    (ai '(NOT (= k m)))))
(have! '(AND (ORD-LE i m) (NOT (= i m))))
(fact 'ord-lt-iff 'i 'm)
(have! '(ORD-LT i m) (lambda () (prop)))
(fact 'ord-segment-membership 'm 'i)
(prop)
(rkp-check! 'ord-segment-trans)
(qed 'ord-segment-trans)
(topic! 'ord-segment-trans 'plumbing)

;;; =====================================================================
;;; (5) power-zero-base
;;; =====================================================================
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (power 0 (succ n)) 0)))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkp-base leaves))
       (step (rkp-step leaves)))
  (dk-focus! base)
  (have! '(AND (IN 0 CC) (IN 0 NN)))
  (fact 'power-succ 0 0)
  (subst '(= (power 0 (succ 0)) (* 0 (power 0 0))))
  (fact 'power-zero 0)
  (subst '(= (power 0 0) 1))
  (arith)
  (dk-focus! step)
  (dk-peel!)
  (let ((nv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                            (eq? (caddr f) 'NN)))
                           "n in NN"))))
    (fact 'nn-succ-closed nv)
    (have! (list 'AND '(IN 0 CC) (list 'IN (list 'succ nv) 'NN)))
    (fact 'power-succ 0 (list 'succ nv))
    (subst (list '= (list 'power 0 (list 'succ (list 'succ nv)))
                 (list '* 0 (list 'power 0 (list 'succ nv)))))
    (subst (list '= (list 'power 0 (list 'succ nv)) 0))
    (arith)))
(rkp-check! 'power-zero-base)
(qed 'power-zero-base)
(topic! 'power-zero-base 'analysis)

;;; =====================================================================
;;; (6) the multiplicative view's read-offs
;;; =====================================================================
(sp (make-wff (list 'FORALL 'R (list 'IMPLIES '(IS-COMMUTATIVE-RING R)
                                     (list '= (list 'OPR rkp-view) '(MUL R))))))
(di) (di)
(mac-h 'is-commutative-ring-def '(IS-COMMUTATIVE-RING R))
(dk-split-all!)
(mac-h 'is-ring '(IS-RING R))
(dk-split-all!)
(slot 'OPR) (mac 'COMMUTATIVE-RING-MULTIPLICATIVE-CM) (nth-r) (rfl)
(rkp-check! 'crmcm-op)
(qed 'crmcm-op)
(topic! 'crmcm-op 'algebra)

(sp (make-wff (list 'FORALL 'R (list 'IMPLIES '(IS-COMMUTATIVE-RING R)
                                     (list '= (list 'IDEN rkp-view) '(ONE R))))))
(di) (di)
(mac-h 'is-commutative-ring-def '(IS-COMMUTATIVE-RING R))
(dk-split-all!)
(mac-h 'is-ring '(IS-RING R))
(dk-split-all!)
(slot 'IDEN) (mac 'COMMUTATIVE-RING-MULTIPLICATIVE-CM) (nth-r) (rfl)
(rkp-check! 'crmcm-iden)
(qed 'crmcm-iden)
(topic! 'crmcm-iden 'algebra)

;;; =====================================================================
;;; (7) ring-power-succ-left (AUX): x^(succ n) = x * x^n -- mpow-succ read
;;;     through the view.
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
    (FORALL x (IMPLIES (IN x (CARR R))
      (FORALL n (IMPLIES (IN n NN)
        (= (RING-POWER R x (succ n)) ((MUL R) x (RING-POWER R x n)))))))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'ring-power-type 'R 'x 'n)
(fact 'ring-carrier-closed-mul 'R 'x (rkp-pw 'x 'n))
(have! (list '== (rkp-pw 'x '(succ n)) (rkp-mul 'x (rkp-pw 'x 'n)))
  (lambda ()
    (mac 'RING-POWER)
    (mac 'mpow-succ)
    (fact 'crmcm-op 'R)
    (subst (list '= (list 'OPR rkp-view) '(MUL R)))
    (qrfl)))
(subst (list '== (rkp-pw 'x '(succ n)) (rkp-mul 'x (rkp-pw 'x 'n))))
(rfl)
(rkp-check! 'ring-power-succ-left)
(qed 'ring-power-succ-left)
(topic! 'ring-power-succ-left 'algebra)

;;; =====================================================================
;;; (8) ring-power-one
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
    (FORALL x (IMPLIES (IN x (CARR R))
      (= (RING-POWER R x 1) x)))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(fact 'ring-power-succ-left 'R 'x 0)
(subst (list '= (rkp-pw 'x '(succ 0)) (rkp-mul 'x (rkp-pw 'x 0))))
(fact 'ring-power-zero 'R 'x)
(subst (list '== (rkp-pw 'x 0) '(ONE R)))
(fact 'ring-mul-right-id 'R 'x)
(ass)
(rkp-check! 'ring-power-one)
(qed 'ring-power-one)
(topic! 'ring-power-one 'algebra)

;;; =====================================================================
;;; (9) ring-power-succ
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
    (FORALL x (IMPLIES (IN x (CARR R))
      (FORALL n (IMPLIES (IN n NN)
        (= (RING-POWER R x (succ n)) ((MUL R) (RING-POWER R x n) x))))))))))
(dk-peel!)
(fact 'ring-power-type 'R 'x 'n)
(fact 'ring-power-succ-left 'R 'x 'n)
(subst (list '= (rkp-pw 'x '(succ n)) (rkp-mul 'x (rkp-pw 'x 'n))))
(fact 'commutative-ring-mul-comm 'R 'x (rkp-pw 'x 'n))
(ass)
(rkp-check! 'ring-power-succ)
(qed 'ring-power-succ)
(topic! 'ring-power-succ 'algebra)

;;; =====================================================================
;;; (10) ring-mul-interchange (AUX): (a*b)*(c*d) = (a*c)*(b*d).
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
    (FORALL a (IMPLIES (IN a (CARR R))
      (FORALL b (IMPLIES (IN b (CARR R))
        (FORALL c (IMPLIES (IN c (CARR R))
          (FORALL d (IMPLIES (IN d (CARR R))
            (= ((MUL R) ((MUL R) a b) ((MUL R) c d))
               ((MUL R) ((MUL R) a c) ((MUL R) b d)))))))))))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(for-each (lambda (p) (fact 'ring-carrier-closed-mul 'R (car p) (cadr p)))
          '((a b) (c d) (b c) (c b) (b d) (a c)))
(fact 'ring-carrier-closed-mul 'R '((MUL R) a c) '((MUL R) b d))
;; (a*b)*(c*d) = a*(b*(c*d))
(fact 'ring-mul-assoc 'R 'a 'b '((MUL R) c d))
(subst '(= ((MUL R) ((MUL R) a b) ((MUL R) c d)) ((MUL R) a ((MUL R) b ((MUL R) c d)))))
;; b*(c*d) = (b*c)*d
(fact 'ring-mul-assoc 'R 'b 'c 'd)
(fact 'eq-sym '((MUL R) ((MUL R) b c) d) '((MUL R) b ((MUL R) c d)))
(subst '(= ((MUL R) b ((MUL R) c d)) ((MUL R) ((MUL R) b c) d)))
;; b*c = c*b
(fact 'commutative-ring-mul-comm 'R 'b 'c)
(subst '(= ((MUL R) b c) ((MUL R) c b)))
;; (c*b)*d = c*(b*d)
(fact 'ring-mul-assoc 'R 'c 'b 'd)
(subst '(= ((MUL R) ((MUL R) c b) d) ((MUL R) c ((MUL R) b d))))
;; a*(c*(b*d)) = (a*c)*(b*d)
(fact 'ring-mul-assoc 'R 'a 'c '((MUL R) b d))
(fact 'eq-sym '((MUL R) ((MUL R) a c) ((MUL R) b d)) '((MUL R) a ((MUL R) c ((MUL R) b d))))
(subst '(= ((MUL R) a ((MUL R) c ((MUL R) b d))) ((MUL R) ((MUL R) a c) ((MUL R) b d))))
(rfl)
(rkp-check! 'ring-mul-interchange)
(qed 'ring-mul-interchange)
(gloss! 'ring-mul-interchange
  "In a commutative ring, (a*b)*(c*d) = (a*c)*(b*d): the multiplicative twin of
   abelian-group-opr-interchange.  Assoc/comm bookkeeping, once.")
(topic! 'ring-mul-interchange 'algebra)

;;; =====================================================================
;;; (11) ring-power-add-ind (AUX) -- the EXPONENT k outermost, so `ni' fires.
;;; =====================================================================
(sp (make-wff
 '(FORALL k (IMPLIES (IN k NN)
    (FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL x (IMPLIES (IN x (CARR R))
        (FORALL j (IMPLIES (IN j NN)
          (= (RING-POWER R x (+ j k))
             ((MUL R) (RING-POWER R x j) (RING-POWER R x k)))))))))))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkp-base-s leaves))
       (step (rkp-step-s leaves)))
  ;; ---- base k = 0
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl (dk-goal)) (t (cadr gl))
         (rv (cadr t)) (xv (caddr t)) (jv (cadr (cadddr t))))
    (fact 'commutative-ring-is-ring rv)
    (fact 'ring-power-type rv xv jv)
    (fact 'nn-add-zero jv)
    (subst (list '= (list '+ jv 0) jv))
    (fact 'ring-power-zero rv xv)
    (subst (list '== (list 'RING-POWER rv xv 0) (list 'ONE rv)))
    (fact 'ring-mul-right-id rv (list 'RING-POWER rv xv jv))
    (subst (list '= (list (list 'MUL rv) (list 'RING-POWER rv xv jv) (list 'ONE rv))
                 (list 'RING-POWER rv xv jv)))
    (rfl))
  ;; ---- step
  (dk-focus! step)
  (dk-peel!)
  (let* ((gl (dk-goal)) (t (cadr gl))
         (rv (cadr t)) (xv (caddr t)) (e (cadddr t))
         (jv (cadr e)) (kv (cadr (caddr e)))
         (mu (lambda (a b) (list (list 'MUL rv) a b)))
         (pw (lambda (n) (list 'RING-POWER rv xv n)))
         (ih (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                       (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                       (equal? (cadr (caddr f)) (list 'IS-COMMUTATIVE-RING (cadr f)))))
                      "the IH")))
    (fact 'commutative-ring-is-ring rv)
    (have! (list 'AND (list 'IN jv 'NN) (list 'IN kv 'NN)))
    (fact 'nn-add-closed jv kv)
    (fact 'ring-power-type rv xv jv)
    (fact 'ring-power-type rv xv kv)
    (fact 'ring-carrier-closed-mul rv xv (pw kv))
    (fact 'ring-carrier-closed-mul rv (pw jv) xv)
    (fact 'ring-carrier-closed-mul rv (mu (pw jv) xv) (pw kv))
    ;; j + succ k = succ (j + k)
    (fact 'nn-add-succ jv kv)
    (subst (list '= (list '+ jv (list 'succ kv)) (list 'succ (list '+ jv kv))))
    ;; x^(succ (j+k)) = x * x^(j+k)
    (fact 'ring-power-succ-left rv xv (list '+ jv kv))
    (subst (list '= (pw (list 'succ (list '+ jv kv))) (mu xv (pw (list '+ jv kv)))))
    ;; IH: x^(j+k) = x^j * x^k
    (dk-apply! ih rv xv jv)
    (subst (list '= (pw (list '+ jv kv)) (mu (pw jv) (pw kv))))
    ;; x^(succ k) = x * x^k
    (fact 'ring-power-succ-left rv xv kv)
    (subst (list '= (pw (list 'succ kv)) (mu xv (pw kv))))
    ;; goal now  x*(x^j*x^k) = x^j*(x*x^k)
    (fact 'ring-mul-assoc rv xv (pw jv) (pw kv))
    (fact 'eq-sym (mu (mu xv (pw jv)) (pw kv)) (mu xv (mu (pw jv) (pw kv))))
    (subst (list '= (mu xv (mu (pw jv) (pw kv))) (mu (mu xv (pw jv)) (pw kv))))
    (fact 'ring-mul-assoc rv (pw jv) xv (pw kv))
    (fact 'eq-sym (mu (mu (pw jv) xv) (pw kv)) (mu (pw jv) (mu xv (pw kv))))
    (subst (list '= (mu (pw jv) (mu xv (pw kv))) (mu (mu (pw jv) xv) (pw kv))))
    (fact 'commutative-ring-mul-comm rv xv (pw jv))
    (subst (list '= (mu xv (pw jv)) (mu (pw jv) xv)))
    (rfl)))
(rkp-check! 'ring-power-add-ind)
(qed 'ring-power-add-ind)
(topic! 'ring-power-add-ind 'algebra)

;;; =====================================================================
;;; (12) ring-power-add -- the site's binder order.
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
    (FORALL x (IMPLIES (IN x (CARR R))
      (FORALL j (IMPLIES (IN j NN)
        (FORALL k (IMPLIES (IN k NN)
          (= (RING-POWER R x (+ j k))
             ((MUL R) (RING-POWER R x j) (RING-POWER R x k)))))))))))))
(dk-peel!)
(fact 'ring-power-add-ind 'k 'R 'x 'j)
(ass)
(rkp-check! 'ring-power-add)
(qed 'ring-power-add)
(topic! 'ring-power-add 'algebra)

;;; =====================================================================
;;; (13) ring-power-mult-ind (AUX) -- the EXPONENT n outermost.
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL x (IMPLIES (IN x (CARR R))
        (FORALL y (IMPLIES (IN y (CARR R))
          (= (RING-POWER R ((MUL R) x y) n)
             ((MUL R) (RING-POWER R x n) (RING-POWER R y n)))))))))))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkp-base-s leaves))
       (step (rkp-step-s leaves)))
  ;; ---- base n = 0:  (xy)^0 = 1 = 1*1 = x^0*y^0
  (dk-focus! base)
  (dk-peel!)
  (let* ((gl (dk-goal)) (t (cadr gl))
         (rv (cadr t)) (pr (caddr t)) (xv (cadr pr)) (yv (caddr pr)))
    (fact 'commutative-ring-is-ring rv)
    (fact 'ring-one-in rv)
    ;; 2026-09-18 (LUTINS instantiation): `fact ring-power-zero' is cited at
    ;; the product ((MUL r) x y); landing its typing first certifies the term
    ;; from the context (asm-establishes-defined?) instead of sending the
    ;; certificate through its applied-structure-operation clause.  The step
    ;; case below already cites this typing for its own reasons.
    (fact 'ring-carrier-closed-mul rv xv yv)
    (fact 'ring-power-zero rv pr)
    (subst (list '== (list 'RING-POWER rv pr 0) (list 'ONE rv)))
    (fact 'ring-power-zero rv xv)
    (subst (list '== (list 'RING-POWER rv xv 0) (list 'ONE rv)))
    (fact 'ring-power-zero rv yv)
    (subst (list '== (list 'RING-POWER rv yv 0) (list 'ONE rv)))
    (fact 'ring-mul-right-id rv (list 'ONE rv))
    (subst (list '= (list (list 'MUL rv) (list 'ONE rv) (list 'ONE rv)) (list 'ONE rv)))
    (rfl))
  ;; ---- step
  (dk-focus! step)
  (dk-peel!)
  (let* ((gl (dk-goal)) (t (cadr gl))
         (rv (cadr t)) (pr (caddr t)) (xv (cadr pr)) (yv (caddr pr))
         (nv (cadr (cadddr t)))
         (mu (lambda (a b) (list (list 'MUL rv) a b)))
         (pwx (list 'RING-POWER rv xv nv))
         (pwy (list 'RING-POWER rv yv nv))
         (ih (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                       (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                       (equal? (cadr (caddr f)) (list 'IS-COMMUTATIVE-RING (cadr f)))))
                      "the IH")))
    (fact 'commutative-ring-is-ring rv)
    (fact 'ring-carrier-closed-mul rv xv yv)
    (fact 'ring-power-type rv xv nv)
    (fact 'ring-power-type rv yv nv)
    (fact 'ring-carrier-closed-mul rv xv pwx)
    (fact 'ring-carrier-closed-mul rv yv pwy)
    (fact 'ring-carrier-closed-mul rv (mu xv pwx) (mu yv pwy))
    ;; (xy)^(succ n) = (xy) * (xy)^n
    (fact 'ring-power-succ-left rv pr nv)
    (subst (list '= (list 'RING-POWER rv pr (list 'succ nv)) (mu pr (list 'RING-POWER rv pr nv))))
    ;; IH: (xy)^n = x^n * y^n
    (dk-apply! ih rv xv yv)
    (subst (list '= (list 'RING-POWER rv pr nv) (mu pwx pwy)))
    ;; x^(succ n) = x * x^n  and  y^(succ n) = y * y^n
    (fact 'ring-power-succ-left rv xv nv)
    (subst (list '= (list 'RING-POWER rv xv (list 'succ nv)) (mu xv pwx)))
    (fact 'ring-power-succ-left rv yv nv)
    (subst (list '= (list 'RING-POWER rv yv (list 'succ nv)) (mu yv pwy)))
    ;; (x*y)*(x^n*y^n) = (x*x^n)*(y*y^n)
    (fact 'ring-mul-interchange rv xv yv pwx pwy)
    (ass)))
(rkp-check! 'ring-power-mult-ind)
(qed 'ring-power-mult-ind)
(topic! 'ring-power-mult-ind 'algebra)

;;; =====================================================================
;;; (14) ring-power-mult -- the site's binder order.
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
    (FORALL x (IMPLIES (IN x (CARR R))
      (FORALL y (IMPLIES (IN y (CARR R))
        (FORALL n (IMPLIES (IN n NN)
          (= (RING-POWER R ((MUL R) x y) n)
             ((MUL R) (RING-POWER R x n) (RING-POWER R y n)))))))))))))
(dk-peel!)
(fact 'ring-power-mult-ind 'n 'R 'x 'y)
(ass)
(rkp-check! 'ring-power-mult)
(qed 'ring-power-mult)
(topic! 'ring-power-mult 'algebra)

;;; =====================================================================
;;; (15) prod-ring-empty -- the empty product is ONE(R).
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL f (= (PROD-RING R f EMPTY-SET) (ONE R)))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'ring-one-in 'R)
(have! (list '== '(PROD-RING R f EMPTY-SET) '(ONE R))
  (lambda ()
    (mac 'PROD-RING)
    (mac 'FINPROD)
    (fact 'finsum-empty rkp-view 'f)
    (subst (list '== (list 'FINSUM rkp-view 'f 'EMPTY-SET) (list 'IDEN rkp-view)))
    (fact 'crmcm-iden 'R)
    (subst (list '= (list 'IDEN rkp-view) '(ONE R)))
    (qrfl)))
(subst (list '== '(PROD-RING R f EMPTY-SET) '(ONE R)))
(rfl)
(rkp-check! 'prod-ring-empty)
(qed 'prod-ring-empty)
(topic! 'prod-ring-empty 'algebra)

;;; =====================================================================
;;; (16) prod-ring-insert -- finsum-insert at the multiplicative view.
;;; The `=' is taken FROM finsum-insert (a strict equation, so both sides
;;; denote); the goal is driven DOWN to that instance rather than a `=='
;;; being lifted up, because nothing types f on the smaller index set X and
;;; the tree has no restriction of a set-function to a subset.
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
     (FORALL k (IMPLIES (AND (IN k SET) (NOT (IN k X)))
     (FORALL f (IMPLIES (IN f (FUN (UNION X (PAIR k k)) (CARR R)))
       (= (PROD-RING R f (UNION X (PAIR k k)))
          ((MUL R) (PROD-RING R f X) (f k)))))))))))))
(dk-peel!)
(dk-split-all!)
(fact 'crmcm-carr 'R)
(fact 'crmcm-op 'R)
(fact 'eq-sym (list 'OPR rkp-view) '(MUL R))
(fact 'commutative-ring-multiplicative-cm-is-comm-monoid 'R)
(have! (list 'IN 'f (list 'FUN '(UNION X (PAIR k k)) (list 'CARR rkp-view)))
       (lambda () (subst (list '= (list 'CARR rkp-view) '(CARR R))) (ass)))
(have! '(AND (IN X SET) (IN (CARD X) NN)))
(have! '(AND (IN k SET) (NOT (IN k X))))
(fact 'finsum-insert rkp-view 'X 'k 'f)
(mac 'PROD-RING)
(mac 'FINPROD)
(subst (list '= '(MUL R) (list 'OPR rkp-view)))
(ass)
(rkp-check! 'prod-ring-insert)
(qed 'prod-ring-insert)
(topic! 'prod-ring-insert 'algebra)

;;; =====================================================================
;;; (17) prod-ring-singleton -- the one-point product is the single factor.
;;; {x} = EMPTY-SET u {x} (union-empty-left, proved above), so this is
;;; finsum-insert at X := EMPTY-SET on top of finsum-empty.
;;; =====================================================================
(sp (make-wff
 '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
     (FORALL x (IMPLIES (IN x SET)
     (FORALL f (IMPLIES (IN f (FUN (PAIR x x) (CARR R)))
       (= (PROD-RING R f (PAIR x x)) (f x))))))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'crmcm-carr 'R)
(fact 'crmcm-op 'R)
(fact 'crmcm-iden 'R)
(fact 'commutative-ring-multiplicative-cm-is-comm-monoid 'R)
(fact 'empty-set-is-set)
(have! '(IN (CARD EMPTY-SET) NN)
       (lambda () (fact 'card-empty) (subst '(= (CARD EMPTY-SET) 0)) (arith)))
(have! '(AND (IN EMPTY-SET SET) (IN (CARD EMPTY-SET) NN)))
(fact 'empty-set-has-no-members 'x)
(have! '(AND (IN x SET) (NOT (IN x EMPTY-SET))))
(have! '(AND (IN x SET) (IN x SET)))
(fact 'pairing 'x 'x)
(fact 'union-empty-left '(PAIR x x))
(fact 'eq-sym '(UNION EMPTY-SET (PAIR x x)) '(PAIR x x))
;; f is a function on EMPTY-SET u {x} into the view's carrier
(have! (list 'IN 'f (list 'FUN '(UNION EMPTY-SET (PAIR x x)) (list 'CARR rkp-view)))
       (lambda ()
         (subst (list '= (list 'CARR rkp-view) '(CARR R)))
         (subst '(= (UNION EMPTY-SET (PAIR x x)) (PAIR x x)))
         (ass)))
(fact 'finsum-insert rkp-view 'EMPTY-SET 'x 'f)
(fact 'finsum-empty rkp-view 'f)
;; f(x) lies in the carrier
(fact 'pairing-membership 'x 'x 'x)
(have! '(= x x) (lambda () (rfl)))
(have! '(IN x (PAIR x x)) (lambda () (prop)))
(fact 'fun-apply-type-c 'f '(PAIR x x) '(CARR R) 'x)
(fact 'ring-mul-left-id 'R '(f x))
;; drive the goal down to the finsum-insert instance
(mac 'PROD-RING)
(mac 'FINPROD)
(subst '(= (PAIR x x) (UNION EMPTY-SET (PAIR x x))))
(subst (list '= (list 'FINSUM rkp-view 'f '(UNION EMPTY-SET (PAIR x x)))
             (list (list 'OPR rkp-view) (list 'FINSUM rkp-view 'f 'EMPTY-SET) '(f x))))
(subst (list '== (list 'FINSUM rkp-view 'f 'EMPTY-SET) (list 'IDEN rkp-view)))
(subst (list '= (list 'OPR rkp-view) '(MUL R)))
(subst (list '= (list 'IDEN rkp-view) '(ONE R)))
(ass)
(rkp-check! 'prod-ring-singleton)
(qed 'prod-ring-singleton)
(topic! 'prod-ring-singleton 'algebra)

;;; =====================================================================
;;; (18) power-insert-disjoint -- the two halves of the insert split meet
;;;      nowhere: every member of POWER(X) omits k, every member of the image
;;;      contains it.
;;; =====================================================================
(define rkp-ins-lam '(VNB-LAMBDA S (POWER X) (UNION S (PAIR k k))))
(sp (make-wff
 (list 'FORALL 'X (list 'IMPLIES '(IN X SET)
   (list 'FORALL 'k (list 'IMPLIES '(AND (IN k SET) (NOT (IN k X)))
     (list '= (list 'INTERSECTION '(POWER X) (list 'IMAGE rkp-ins-lam '(POWER X)))
              'EMPTY-SET)))))))
(dk-peel!)
(dk-split-all!)
(fact 'power-set 'X)
(fact 'empty-set-is-set)
(have! (list 'OR '(IN (POWER X) SET) (list 'IN (list 'IMAGE rkp-ins-lam '(POWER X)) 'SET))
       (lambda () (prop)))
(fact 'intersection-set-closure '(POWER X) (list 'IMAGE rkp-ins-lam '(POWER X)))
(have! (list 'AND (list 'IN (list 'INTERSECTION '(POWER X) (list 'IMAGE rkp-ins-lam '(POWER X))) 'SET)
             '(IN EMPTY-SET SET)))
(fact 'extensionality (list 'INTERSECTION '(POWER X) (list 'IMAGE rkp-ins-lam '(POWER X))) 'EMPTY-SET)
(have! (list 'FORALL 'w_
         (list 'IFF (list 'IN 'w_ (list 'INTERSECTION '(POWER X) (list 'IMAGE rkp-ins-lam '(POWER X))))
                    '(IN w_ EMPTY-SET)))
  (lambda ()
    (let ((wv (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (fact 'empty-set-has-no-members wv)
      (fact 'intersection-membership '(POWER X) (list 'IMAGE rkp-ins-lam '(POWER X)) wv)
      (have! (list 'NOT (list 'IN wv (list 'INTERSECTION '(POWER X)
                                           (list 'IMAGE rkp-ins-lam '(POWER X)))))
        (lambda ()
          (di)                                      ; assume it; goal FALSITY
          (have! (list 'AND (list 'IN wv '(POWER X))
                       (list 'IN wv (list 'IMAGE rkp-ins-lam '(POWER X))))
                 (lambda () (prop)))
          (dk-split-all!)
          ;; from the IMAGE half: a witness S0 in POWER(X) with S0 u {k} = w
          (fact 'image-membership-iff rkp-ins-lam '(POWER X) wv)
          (have! (list 'FORSOME 'x_ (list 'AND '(IN x_ (POWER X))
                                          (list '= (list rkp-ins-lam 'x_) wv)))
                 (lambda () (prop)))
          (let* ((ex (dk-pick (dk-head? 'FORSOME) "the image witness"))
                 (landed (dk-split! (dk-landed-1 (lambda () (ai ex)))))
                 (mem (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                 (equal? (caddr f) '(POWER X))
                                                 (not (equal? (cadr f) wv))))
                                landed))
                 (sv  (cadr mem))
                 (eqn (any-pred (lambda (f) (and (pair? f) (eq? (car f) '=))) landed)))
            (lam-b-h eqn)
            (let ((beta (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                  (pair? (cadr f))
                                                  (eq? (car (cadr f)) 'UNION)))
                                 "the beta-reduced equation")))
              ;; k lies in S0 u {k}
              (have! '(= k k) (lambda () (rfl)))
              (have! '(AND (IN k SET) (IN k SET)))
              (fact 'pairing-membership 'k 'k 'k)
              (fact 'union-membership sv '(PAIR k k) 'k)
              (have! (list 'IN 'k (list 'UNION sv '(PAIR k k))) (lambda () (prop)))
              ;; ... hence in w, which POWER(X) forbids
              (fact 'eq-sym (list 'UNION sv '(PAIR k k)) wv)
              (have! (list 'IN 'k wv)
                     (lambda () (subst (list '= wv (list 'UNION sv '(PAIR k k)))) (ass)))
              (fact 'power-set-membership 'X wv)
              (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ wv) '(IN z_ X)))
                     (lambda () (prop)))
              (dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                   (pair? (caddr f))
                                                   (eq? (car (caddr f)) 'IMPLIES)
                                                   (equal? (caddr (caddr f)) '(IN z_ X))))
                                  "the subset universal")
                         'k)
              (ai '(NOT (IN k X)))))))
      (prop))))
(prop)
(rkp-check! 'power-insert-disjoint)
(qed 'power-insert-disjoint)
(topic! 'power-insert-disjoint 'plumbing)

;;; =====================================================================
;;; (19) choose-set-unfold (AUX) -- the functoid's unfold as a THEOREM, so
;;;      `mac-h' can open a CHOOSE-SET membership in a HYPOTHESIS (a
;;;      def-functoid's own name cannot: CLAUDE.md, the mac-h trap).
;;; =====================================================================
(sp (make-wff
 '(FORALL n_ (FORALL m_
    (== (CHOOSE-SET n_ m_)
        (SEP A (POWER (ORD-SEGMENT n_)) (= (CARD A) m_)))))))
(di) (di)
(mac 'CHOOSE-SET)
(qrfl)
(rkp-check! 'choose-set-unfold)
(qed 'choose-set-unfold)
(topic! 'choose-set-unfold 'plumbing)

;;; =====================================================================
;;; (20) choose-0-succ -- ORD-SEGMENT(0) is empty, so it has no subset of
;;;      cardinality succ k: the separated set is EMPTY-SET and its cardinal 0.
;;; =====================================================================
(sp (make-wff '(FORALL k (IMPLIES (IN k NN) (= (CHOOSE 0 (succ k)) 0)))))
(dk-peel!)
(fact 'ord-segment-zero)
(fact 'eq-sym '(ORD-SEGMENT 0) 'EMPTY-SET)
(fact 'empty-set-is-set)
(fact 'power-set 'EMPTY-SET)
(fact 'nn-succ-nonzero 'k)
(fact 'card-empty)
(have! '(IN (CHOOSE-SET 0 (succ k)) SET)
  (lambda () (mac 'CHOOSE-SET) (subst '(= (ORD-SEGMENT 0) EMPTY-SET)) (sep-set) (ass)))
(have! '(AND (IN (CHOOSE-SET 0 (succ k)) SET) (IN EMPTY-SET SET)))
(fact 'extensionality '(CHOOSE-SET 0 (succ k)) 'EMPTY-SET)
(have! '(FORALL w_ (IFF (IN w_ (CHOOSE-SET 0 (succ k))) (IN w_ EMPTY-SET)))
  (lambda ()
    (let ((wv (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (fact 'empty-set-has-no-members wv)
      (have! (list 'NOT (list 'IN wv '(CHOOSE-SET 0 (succ k))))
        (lambda ()
          (di)                                   ; assume it; goal FALSITY
          (mac-h 'choose-set-unfold (list 'IN wv '(CHOOSE-SET 0 (succ k))))
          (sep-me (list 'IN wv (list 'SEP 'A '(POWER (ORD-SEGMENT 0))
                                     '(= (CARD A) (succ k)))))
          (dk-split-all!)
          (have! (list 'IN wv '(POWER EMPTY-SET))
                 (lambda () (subst '(= EMPTY-SET (ORD-SEGMENT 0))) (ass)))
          (fact 'power-set-membership 'EMPTY-SET wv)
          (have! (list 'IN wv 'SET) (lambda () (prop)))
          (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ wv) '(IN z_ EMPTY-SET)))
                 (lambda () (prop)))
          (have! (list 'AND (list 'IN wv 'SET) '(IN EMPTY-SET SET)))
          (fact 'extensionality wv 'EMPTY-SET)
          (have! (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ wv) '(IN y_ EMPTY-SET)))
            (lambda ()
              (let ((yv (dk-di-var! (lambda (g) (cadr (cadr g))))))
                (fact 'empty-set-has-no-members yv)
                (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                  (pair? (caddr f))
                                                  (eq? (car (caddr f)) 'IMPLIES)
                                                  (equal? (caddr (caddr f)) '(IN z_ EMPTY-SET))))
                                 "the subset universal")
                        yv)
                (prop))))
          (have! (list '= wv 'EMPTY-SET) (lambda () (prop)))
          (have! (list '= (list 'CARD wv) 0)
                 (lambda () (subst (list '= wv 'EMPTY-SET)) (ass)))
          (fact 'eq-sym (list 'CARD wv) '(succ k))
          (fact 'eq-trans '(succ k) (list 'CARD wv) 0)
          (ai '(NOT (= (succ k) 0)))))
      (prop))))
(have! '(= (CHOOSE-SET 0 (succ k)) EMPTY-SET) (lambda () (prop)))
(mac 'CHOOSE)
(subst '(= (CHOOSE-SET 0 (succ k)) EMPTY-SET))
(ass)
(rkp-check! 'choose-0-succ)
(qed 'choose-0-succ)
(topic! 'choose-0-succ 'combinatorial)

;;; =====================================================================
;;; (21) card-zero-is-empty -- REMOVED 2026-09-20 (batch 9-B).  It was proven here
;;;      from `finite-set-induction' when that was a PRIMITIVE axiom.  CARD is now
;;;      DEFINED and `finite-set-induction' is itself a THEOREM, proven in
;;;      theorem-library/rake-card-star-laws.scm -- FROM card-zero-is-empty.  Keeping
;;;      both proofs made the citation graph circular
;;;      (finite-set-induction -> card-finite-induction-aux -> card-zero-is-empty ->
;;;      finite-set-induction), which proof-cycle-check refuses, and rightly.
;;;      The statement is alpha-identical to the one rake-card-star-laws.scm proves
;;;      (far above, and with no induction at all: it reads the enumeration of a set of
;;;      cardinal 0 off well-ordering-principle), so the name still denotes the same
;;;      fact and the `fact' of it below is unchanged.  The block is in
;;;      archive/2026-09-20-card-defined/rake-combinatorics-before-cze-cut.scm.
;;; =====================================================================

;;; =====================================================================
;;; (22) choose-n-0 -- the unique 0-element subset is EMPTY-SET.
;;; =====================================================================
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (CHOOSE n 0) (succ 0))))))
(dk-peel!)
(fact 'nn-subset-ord 'n)
(fact 'ord-segment-is-set 'n)
(fact 'power-set '(ORD-SEGMENT n))
(fact 'empty-set-is-set)
(fact 'card-empty)
(fact 'empty-set-has-no-members 'EMPTY-SET)
(have! '(AND (IN EMPTY-SET SET) (IN EMPTY-SET SET)))
(fact 'pairing 'EMPTY-SET 'EMPTY-SET)
(have! '(FORALL z_ (IMPLIES (IN z_ EMPTY-SET) (IN z_ (ORD-SEGMENT n))))
  (lambda ()
    (let ((zv (dk-di-var! (lambda (g) (cadr g)))))
      (fact 'empty-set-has-no-members zv)
      (ai (list 'NOT (list 'IN zv 'EMPTY-SET))))))
(fact 'power-set-membership '(ORD-SEGMENT n) 'EMPTY-SET)
(have! '(IN EMPTY-SET (POWER (ORD-SEGMENT n))) (lambda () (prop)))
(have! '(IN (CHOOSE-SET n 0) SET)
       (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
(have! '(AND (IN (CHOOSE-SET n 0) SET) (IN (PAIR EMPTY-SET EMPTY-SET) SET)))
(fact 'extensionality '(CHOOSE-SET n 0) '(PAIR EMPTY-SET EMPTY-SET))
(have! '(FORALL w_ (IFF (IN w_ (CHOOSE-SET n 0)) (IN w_ (PAIR EMPTY-SET EMPTY-SET))))
  (lambda ()
    (let ((wv (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (fact 'pairing-membership 'EMPTY-SET 'EMPTY-SET wv)
      (have! (list 'IMPLIES (list 'IN wv '(CHOOSE-SET n 0)) (list '= wv 'EMPTY-SET))
        (lambda ()
          (di)
          (mac-h 'choose-set-unfold (list 'IN wv '(CHOOSE-SET n 0)))
          (sep-me (list 'IN wv (list 'SEP 'A '(POWER (ORD-SEGMENT n)) '(= (CARD A) 0))))
          (dk-split-all!)
          (fact 'power-set-membership '(ORD-SEGMENT n) wv)
          (have! (list 'IN wv 'SET) (lambda () (prop)))
          (fact 'card-zero-is-empty wv)
          (ass)))
      (have! (list 'IMPLIES (list '= wv 'EMPTY-SET) (list 'IN wv '(CHOOSE-SET n 0)))
        (lambda ()
          (di)
          (subst (list '= wv 'EMPTY-SET))
          (mac 'CHOOSE-SET)
          (for-each (lambda (leaf) (dk-focus! leaf) (ass))
                    (dk-opened (lambda () (sep-mi))))))
      (prop))))
(have! '(= (CHOOSE-SET n 0) (PAIR EMPTY-SET EMPTY-SET)) (lambda () (prop)))
(mac 'CHOOSE)
(subst '(= (CHOOSE-SET n 0) (PAIR EMPTY-SET EMPTY-SET)))
(fact 'union-empty-left '(PAIR EMPTY-SET EMPTY-SET))
(fact 'eq-sym '(UNION EMPTY-SET (PAIR EMPTY-SET EMPTY-SET)) '(PAIR EMPTY-SET EMPTY-SET))
(subst '(= (PAIR EMPTY-SET EMPTY-SET) (UNION EMPTY-SET (PAIR EMPTY-SET EMPTY-SET))))
(have! '(AND (IN EMPTY-SET SET) (NOT (IN EMPTY-SET EMPTY-SET))))
;; card-insert carries a FINITENESS guard since 2026-09-18
;; (structure-library/cardinality.scm); card-empty, landed above, discharges it.
(fact 'nn-zero-in)
(have! '(IN (CARD EMPTY-SET) NN)
       (lambda () (subst '(= (CARD EMPTY-SET) 0)) (ass)))
(fact 'card-insert 'EMPTY-SET 'EMPTY-SET)
(subst '(= (CARD (UNION EMPTY-SET (PAIR EMPTY-SET EMPTY-SET))) (succ_ORD (CARD EMPTY-SET))))
(subst '(= (CARD EMPTY-SET) 0))
(fact 'ord-succ-nn 0)
(subst '(= (succ_ORD 0) (succ 0)))
(rfl)
(rkp-check! 'choose-n-0)
(qed 'choose-n-0)
(topic! 'choose-n-0 'combinatorial)

;;; =====================================================================
;;; (23) power-insert-cover -- POWER(X u {k}) is POWER(X) together with the
;;;      image of POWER(X) under S |-> S u {k}.
;;;
;;;      The one move with content is the surgery A = (A \ {k}) u {k} for a
;;;      subset A of X u {k} that CONTAINS k; it is set extensionality plus
;;;      difference-membership, and `prop' on a TRIMMED context (dk-only!) --
;;;      untrimmed, prop's atom cap drops the pair it needs.
;;; =====================================================================
(define rkp-pic-lam '(VNB-LAMBDA S (POWER X) (UNION S (PAIR k k))))
(define rkp-pic-U   '(UNION X (PAIR k k)))
(define rkp-pic-P   '(POWER X))
(define rkp-pic-IM  (list 'IMAGE rkp-pic-lam rkp-pic-P))
(define rkp-pic-RHS (list 'UNION rkp-pic-P rkp-pic-IM))

(sp (make-wff
 (list 'FORALL 'X (list 'IMPLIES '(IN X SET)
   (list 'FORALL 'k (list 'IMPLIES '(AND (IN k SET) (NOT (IN k X)))
     (list '= (list 'POWER rkp-pic-U) rkp-pic-RHS)))))))
(dk-peel!)
(dk-split-all!)
(have! '(AND (IN k SET) (IN k SET)))
(fact 'pairing 'k 'k)
(have! '(AND (IN X SET) (IN (PAIR k k) SET)))
(fact 'union-set-closure 'X '(PAIR k k))
(fact 'power-set rkp-pic-U)
(fact 'power-set 'X)
(fact 'image-set rkp-pic-lam rkp-pic-P)
(have! (list 'AND (list 'IN rkp-pic-P 'SET) (list 'IN rkp-pic-IM 'SET)))
(fact 'union-set-closure rkp-pic-P rkp-pic-IM)
(have! (list 'AND (list 'IN (list 'POWER rkp-pic-U) 'SET) (list 'IN rkp-pic-RHS 'SET)))
(define rkp-pic-ext
  (iff-for (begin (fact 'extensionality (list 'POWER rkp-pic-U) rkp-pic-RHS)
                      (list '= (list 'POWER rkp-pic-U) rkp-pic-RHS))))
(have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ (list 'POWER rkp-pic-U))
                               (list 'IN 'w_ rkp-pic-RHS)))
  (lambda ()
    (let* ((A  (dk-di-var! (lambda (g) (cadr (cadr g)))))
           (pu (rkp-mem-iff! (list 'IN A (list 'POWER rkp-pic-U)) 'power-set-membership rkp-pic-U A))
           (px (rkp-mem-iff! (list 'IN A rkp-pic-P) 'power-set-membership 'X A))
           (um (rkp-mem-iff! (list 'IN A rkp-pic-RHS) 'union-membership rkp-pic-P rkp-pic-IM A))
           (im (rkp-mem-iff! (list 'IN A rkp-pic-IM) 'image-membership-iff rkp-pic-lam rkp-pic-P A))
           (inU (list 'IN A (list 'POWER rkp-pic-U)))
           (inR (list 'IN A rkp-pic-RHS))
           (inP (list 'IN A rkp-pic-P))
           (inI (list 'IN A rkp-pic-IM))
           (D   (list 'DIFFERENCE A '(PAIR k k))))
      ;; ---------------- forward
      (have! (list 'IMPLIES inU inR)
        (lambda ()
          (di)
          (have! (list 'AND (list 'IN A 'SET)
                       (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ rkp-pic-U))))
                 (lambda () (dk-only! pu inU) (prop)))
          (dk-split-all!)
          (let ((sub (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                               (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                               (equal? (caddr (caddr f)) (list 'IN 'z_ rkp-pic-U))))
                              "A subset X u {k}")))
            (use-em (list 'IN 'k A)
              ;; ---- k in A: A is the image of A \ {k}
              (lambda ()
                (fact 'difference-set A '(PAIR k k))
                (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ D) (list 'IN 'z_ 'X)))
                  (lambda ()
                    (let* ((zv  (dk-di-var! (lambda (g) (cadr g))))
                           (dm  (rkp-mem-iff! (list 'IN zv (list 'DIFFERENCE A '(PAIR k k))) 'difference-membership A '(PAIR k k) zv))
                           (pmz (rkp-pairmem! 'k zv))
                           (umz (rkp-mem-iff! (list 'IN zv rkp-pic-U) 'union-membership 'X '(PAIR k k) zv))
                           (sz  (inst*! sub zv)))
                      (dk-only! dm pmz umz sz (list 'IN zv D))
                      (prop))))
                (let ((dsub (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                      (pair? (caddr f))
                                                      (eq? (car (caddr f)) 'IMPLIES)
                                                      (equal? (cadr (caddr f)) (list 'IN 'z_ D))))
                                     "A \\ {k} subset X"))
                      (pd (rkp-mem-iff! (list 'IN D rkp-pic-P) 'power-set-membership 'X D)))
                  (have! (list 'IN D rkp-pic-P)
                         (lambda () (dk-only! pd (list 'IN D 'SET) dsub) (prop)))
                  (have! (list 'AND (list 'IN D 'SET) '(IN (PAIR k k) SET)))
                  (fact 'union-set-closure D '(PAIR k k))
                  ;; beta: L(A \ {k}) = (A \ {k}) u {k}
                  (have! (list '= (list rkp-pic-lam D) (list 'UNION D '(PAIR k k)))
                         (lambda () (lam-b) (rfl)))
                  ;; (A \ {k}) u {k} = A
                  (have! (list 'AND (list 'IN (list 'UNION D '(PAIR k k)) 'SET) (list 'IN A 'SET)))
                  (fact 'extensionality (list 'UNION D '(PAIR k k)) A)
                  (have! (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ (list 'UNION D '(PAIR k k)))
                                                 (list 'IN 'y_ A)))
                    (lambda ()
                      (let* ((yv  (dk-di-var! (lambda (g) (cadr (cadr g)))))
                             (umy (rkp-mem-iff! (list 'IN yv (list 'UNION D '(PAIR k k))) 'union-membership D '(PAIR k k) yv))
                             (dmy (rkp-mem-iff! (list 'IN yv (list 'DIFFERENCE A '(PAIR k k))) 'difference-membership A '(PAIR k k) yv))
                             (pmy (rkp-pairmem! 'k yv))
                             (kay (list 'IMPLIES (list '= yv 'k) (list 'IN yv A))))
                        (have! kay (lambda () (di) (subst (list '= yv 'k)) (ass)))
                        (dk-only! umy dmy pmy kay)
                        (prop))))
                  (have! (list '= (list 'UNION D '(PAIR k k)) A)
                         (lambda () (dk-only! (dk-pick (dk-head? 'IFF) "the extensionality iff")
                                              (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ (list 'UNION D '(PAIR k k)))
                                                                      (list 'IN 'y_ A))))
                                    (prop)))
                  (fact 'eq-trans (list rkp-pic-lam D) (list 'UNION D '(PAIR k k)) A)
                  (have! (list 'FORSOME 'x_ (list 'AND (list 'IN 'x_ rkp-pic-P)
                                                  (list '= (list rkp-pic-lam 'x_) A)))
                         (lambda () (ew D) (prop)))
                  (dk-only! im um (list 'IN A 'SET)          ; the iff's sethood conjunct (2026-09-30)
                            (list 'FORSOME 'x_ (list 'AND (list 'IN 'x_ rkp-pic-P)
                                                     (list '= (list rkp-pic-lam 'x_) A))))
                  (prop)))
              ;; ---- k not in A: A is a subset of X
              (lambda ()
                (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ 'X)))
                  (lambda ()
                    (let* ((zv  (dk-di-var! (lambda (g) (cadr g))))
                           (pmz (rkp-pairmem! 'k zv))
                           (umz (rkp-mem-iff! (list 'IN zv rkp-pic-U) 'union-membership 'X '(PAIR k k) zv))
                           (sz  (inst*! sub zv))
                           (kz  (list 'IMPLIES (list '= zv 'k) (list 'IN 'k A))))
                      (have! kz (lambda () (di) (fact 'eq-sym zv 'k) (subst (list '= 'k zv)) (ass)))
                      (dk-only! pmz umz sz kz (list 'IN zv A) (list 'NOT (list 'IN 'k A)))
                      (prop))))
                (dk-only! px um (list 'IN A 'SET)
                          (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ 'X))))
                (prop))))))
      ;; ---------------- backward
      (have! (list 'IMPLIES inR inU)
        (lambda ()
          (di)
          (have! (list 'OR inP inI) (lambda () (dk-only! um inR) (prop)))
          (use-cases (list 'OR inP inI)
            (lambda ()                                   ; A in POWER(X)
              (have! (list 'AND (list 'IN A 'SET)
                           (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ 'X))))
                     (lambda () (dk-only! px inP) (prop)))
              (dk-split-all!)
              (let ((sx (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                  (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                                  (equal? (caddr (caddr f)) '(IN z_ X))))
                                 "A subset X")))
                (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ rkp-pic-U)))
                  (lambda ()
                    (let* ((zv (dk-di-var! (lambda (g) (cadr g))))
                           (sz (inst*! sx zv))
                           (umz (rkp-mem-iff! (list 'IN zv rkp-pic-U) 'union-membership 'X '(PAIR k k) zv)))
                      (dk-only! sz umz (list 'IN zv A))
                      (prop))))
                (dk-only! pu (list 'IN A 'SET)
                          (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ rkp-pic-U))))
                (prop)))
            (lambda ()                                   ; A in the image
              (have! (list 'FORSOME 'x_ (list 'AND (list 'IN 'x_ rkp-pic-P)
                                              (list '= (list rkp-pic-lam 'x_) A)))
                     (lambda () (dk-only! im inI) (prop)))
              (let* ((ex (dk-pick (dk-head? 'FORSOME) "the image witness"))
                     (landed (dk-split! (dk-landed-1 (lambda () (ai ex)))))
                     (mem (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                     (equal? (caddr f) rkp-pic-P)
                                                     (not (equal? (cadr f) A))))
                                    landed))
                     (S0 (cadr mem))
                     (eqn (any-pred (lambda (f) (and (pair? f) (eq? (car f) '=))) landed)))
                (lam-b-h eqn)
                (let* ((beta (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                       (pair? (cadr f))
                                                       (eq? (car (cadr f)) 'UNION)))
                                      "the beta-reduced equation"))
                       (SU (cadr beta))
                       (pS (rkp-mem-iff! (list 'IN S0 rkp-pic-P) 'power-set-membership 'X S0)))
                  (fact 'eq-sym SU A)
                  (have! (list 'AND (list 'IN S0 'SET)
                               (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ S0) '(IN z_ X))))
                         (lambda () (dk-only! pS (list 'IN S0 rkp-pic-P)) (prop)))
                  (dk-split-all!)
                  (have! (list 'AND (list 'IN S0 'SET) '(IN (PAIR k k) SET)))
                  (fact 'union-set-closure S0 '(PAIR k k))
                  (have! (list 'IN A 'SET)
                         (lambda () (subst (list '= A SU)) (ass)))
                  (let ((s0sub (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                         (pair? (caddr f))
                                                         (eq? (car (caddr f)) 'IMPLIES)
                                                         (equal? (cadr (caddr f)) (list 'IN 'z_ S0))))
                                        "S0 subset X")))
                    (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ rkp-pic-U)))
                      (lambda ()
                        (let* ((zv (dk-di-var! (lambda (g) (cadr g)))))
                          (have! (list 'IN zv SU)
                                 (lambda () (subst beta) (ass)))
                          (let ((umz0 (rkp-mem-iff! (list 'IN zv (list 'UNION S0 '(PAIR k k))) 'union-membership S0 '(PAIR k k) zv))
                                (sz   (inst*! s0sub zv))
                                (umz  (rkp-mem-iff! (list 'IN zv rkp-pic-U) 'union-membership 'X '(PAIR k k) zv)))
                            (dk-only! umz0 sz umz (list 'IN zv SU))
                            (prop)))))
                    (dk-only! pu (list 'IN A 'SET)
                              (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ A) (list 'IN 'z_ rkp-pic-U))))
                    (prop))))))))
      (dk-only! (list 'IMPLIES inU inR) (list 'IMPLIES inR inU))
      (prop))))
(dk-only! rkp-pic-ext
          (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ (list 'POWER rkp-pic-U))
                                  (list 'IN 'w_ rkp-pic-RHS))))
(prop)
(rkp-check! 'power-insert-cover)
(qed 'power-insert-cover)
(topic! 'power-insert-cover 'plumbing)

;;; =====================================================================
;;; (24) subset-of-empty-is-empty (AUX) and power-of-empty (AUX).
;;; =====================================================================
(sp (make-wff
 '(FORALL w_ (IMPLIES (IN w_ SET)
    (IMPLIES (FORALL z_ (IMPLIES (IN z_ w_) (IN z_ EMPTY-SET)))
             (= w_ EMPTY-SET))))))
(di) (di) (di)
(let ((sub (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) "the inclusion")))
  (bc* 'class-extensionality)
  (let* ((v (dk-di-var! (lambda (g) (cadr (cadr g))))))
    (inst*! sub v)
    (fact 'empty-set-has-no-members v)
    (prop)))
(rkp-check! 'subset-of-empty-is-empty)
(qed 'subset-of-empty-is-empty)
(topic! 'subset-of-empty-is-empty 'plumbing)

(sp (make-wff '(= (POWER EMPTY-SET) (PAIR EMPTY-SET EMPTY-SET))))
(fact 'empty-set-is-set)
(fact 'power-set 'EMPTY-SET)
(have! '(AND (IN EMPTY-SET SET) (IN EMPTY-SET SET)))
(fact 'pairing 'EMPTY-SET 'EMPTY-SET)
(have! '(AND (IN (POWER EMPTY-SET) SET) (IN (PAIR EMPTY-SET EMPTY-SET) SET)))
(fact 'extensionality '(POWER EMPTY-SET) '(PAIR EMPTY-SET EMPTY-SET))
(have! '(FORALL w_ (IFF (IN w_ (POWER EMPTY-SET)) (IN w_ (PAIR EMPTY-SET EMPTY-SET))))
  (lambda ()
    (let* ((wv (dk-di-var! (lambda (g) (cadr (cadr g)))))
           (pw (rkp-mem-iff! (list 'IN wv '(POWER EMPTY-SET))
                             'power-set-membership 'EMPTY-SET wv))
           (pm (rkp-pairmem! 'EMPTY-SET wv)))
      (have! (list 'IMPLIES (list 'IN wv '(POWER EMPTY-SET)) (list '= wv 'EMPTY-SET))
        (lambda ()
          (di)
          (have! (list 'AND (list 'IN wv 'SET)
                       (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ wv) '(IN z_ EMPTY-SET))))
                 (lambda () (dk-only! pw (list 'IN wv '(POWER EMPTY-SET))) (prop)))
          (dk-split-all!)
          (fact 'subset-of-empty-is-empty wv)
          (ass)))
      (have! (list 'IMPLIES (list '= wv 'EMPTY-SET) (list 'IN wv '(POWER EMPTY-SET)))
        (lambda ()
          (di)
          (subst (list '= wv 'EMPTY-SET))
          (have! '(FORALL z_ (IMPLIES (IN z_ EMPTY-SET) (IN z_ EMPTY-SET)))
                 (lambda () (di) (ass)))
          (dk-only! (rkp-mem-iff! '(IN EMPTY-SET (POWER EMPTY-SET))
                                  'power-set-membership 'EMPTY-SET 'EMPTY-SET)
                    '(IN EMPTY-SET SET)
                    '(FORALL z_ (IMPLIES (IN z_ EMPTY-SET) (IN z_ EMPTY-SET))))
          (prop)))
      (dk-only! pm
                (list 'IMPLIES (list 'IN wv '(POWER EMPTY-SET)) (list '= wv 'EMPTY-SET))
                (list 'IMPLIES (list '= wv 'EMPTY-SET) (list 'IN wv '(POWER EMPTY-SET))))
      (prop))))
(prop)
(rkp-check! 'power-of-empty)
(qed 'power-of-empty)
(topic! 'power-of-empty 'plumbing)

;;; =====================================================================
;;; (25) card-power-nn -- the powerset of a finite set is finite.
;;;      finite-set-induction at C = { x | CARD(POWER x) in NN }; the step is
;;;      power-insert-cover (above) plus card-image-finite and card-union-nn.
;;;      Disjointness is NOT needed -- card-union-nn does not ask for it.
;;; =====================================================================
(define rkp-cpn-class '(COMP x_ (IN (CARD (POWER x_)) NN)))
(define rkp-cpn-step
  `(FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (IN S ,rkp-cpn-class)))
     (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x S)))
       (IN (UNION S (PAIR x x)) ,rkp-cpn-class))))))

(define (rkp-cpn-base!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (equal? (dk-goal) '(in empty-set set))
         (begin (fact 'empty-set-is-set) (ass))
         (begin
           (fact 'power-of-empty)
           (subst '(= (POWER EMPTY-SET) (PAIR EMPTY-SET EMPTY-SET)))
           (fact 'empty-set-is-set)
           (fact 'card-singleton 'EMPTY-SET)
           (subst '(= (CARD (PAIR EMPTY-SET EMPTY-SET)) (succ 0)))
           (fact 'nn-zero-in)
           (fact 'nn-succ-closed 0)
           (ass))))
   (dk-opened (lambda () (comp-mi)))))

(define (rkp-cpn-step!)
  (let* ((landed (dk-peel!))
         (g (dk-goal))
         (S (cadr (cadr g)))
         (x (cadr (caddr (cadr g))))
         (U (list 'UNION S (list 'PAIR x x))))
    (dk-split-all! landed)
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN S rkp-cpn-class)))
                              (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (pair? (cadr f)) (eq? (car (cadr f)) 'CARD))))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (equal? (dk-goal) (list 'in U 'set))
             (begin (have! (list 'AND (list 'IN x 'SET) (list 'IN x 'SET)))
                    (fact 'pairing x x)
                    (have! (list 'AND (list 'IN S 'SET) (list 'IN (list 'PAIR x x) 'SET)))
                    (fact 'union-set-closure S (list 'PAIR x x))
                    (ass))
             (begin
               (have! (list 'AND (list 'IN x 'SET) (list 'NOT (list 'IN x S))))
               (fact 'power-insert-cover S x)
               (let* ((eq (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                    (equal? (cadr f) (list 'POWER U))))
                                   "the insert-split equation"))
                      (rhs (caddr eq))
                      (P   (cadr rhs))
                      (IM  (caddr rhs))
                      (L   (cadr IM)))
                 (fact 'power-set S)
                 (fact 'card-image-finite L P)
                 (fact 'image-set L P)
                 (fact 'card-union-nn P IM)
                 (subst eq)
                 (ass)))))
       (dk-opened (lambda () (comp-mi)))))))

(quietly (lambda ()
  (sp (make-wff '(FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
                   (IN (CARD (POWER X)) NN)))))
  (have! (list 'IN 'EMPTY-SET rkp-cpn-class) rkp-cpn-base!)
  (have! rkp-cpn-step rkp-cpn-step!)
  (have! (list 'AND (list 'IN 'EMPTY-SET rkp-cpn-class) rkp-cpn-step))
  (let ((ind (dk-fact! 'finite-set-induction rkp-cpn-class)))
    (dk-peel!)
    (let ((Xv (cadr (cadr (cadr (dk-goal))))))     ; goal (IN (CARD (POWER X)) NN)
      (let ((gd (list 'AND (list 'IN Xv 'SET) (list 'IN (list 'CARD Xv) 'NN))))
        (if (not (any-pred (lambda (f) (alpha-equiv? f gd)) (dk-asms))) (have! gd)))
      (let ((inx (dk-apply! ind Xv)))
        (dk-landed-find (lambda () (comp-me inx))
                        (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                         (pair? (cadr f)) (eq? (car (cadr f)) 'CARD))))
        (ass))))))
(rkp-check! 'card-power-nn)
(qed 'card-power-nn)
(topic! 'card-power-nn 'combinatorial)
