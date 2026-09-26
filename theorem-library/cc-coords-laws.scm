;;; cc-coords-laws.scm -- CC and cartesian(RR, RR), explicitly.
;;;
;;; The laws of the two maps defined in structure-library/cc-coords.scm:
;;;
;;;     CC-COORDS    z     |-> [real-part(z), imag-part(z)]
;;;     CC-OF-PAIR   [a,b] |-> a + b*i
;;;
;;; Design note: docs/paths-and-line-integrals-2026-09-21.md, section 3.1.
;;;
;;; THE ORDER, which is the order of the design note:
;;;   1. value laws and FUN typings of both maps;
;;;   2. each is the inverse of the other, hence both are bijections;
;;;   3. the missing COORDINATE laws (real and imaginary part of a sum, of a
;;;      real multiple, of a product) and the additivity / real-homogeneity of
;;;      the two maps that follow from them;
;;;   4. the two-sided estimate between |z - w| and the coordinate distances;
;;;   5. the three transfer equivalences: convergence, continuity, derivative.
;;;
;;; ON THE METRIC COMPARISON (step 4).  The design note asks for the estimate
;;; "stated as a comparison of CC-MS with the product metric on
;;; cartesian(RR,RR)".  THERE IS NO BINARY PRODUCT OF TWO METRIC SPACES IN THE
;;; TREE: structure-library/product-metric.scm builds only the COUNTABLE product
;;; PRODUCT-METRIC(ms) of a sequence `ms' of metric spaces, over the carrier
;;; PRODUCT-CARRIER(ms) of SEQUENCES, with the weighted series distance.  A pair
;;; is not a sequence, so nothing in that file applies to cartesian(RR,RR), and
;;; making it apply would mean either a binary product construction of its own or
;;; an embedding of pairs into eventually-constant sequences.  So the comparison
;;; is stated DIRECTLY, as the two inequalities between magnitude(z - w) and the
;;; coordinate distances |re z - re w| and |im z - im w| -- which is what every
;;; consumer of it (the convergence and continuity transfers below) actually
;;; uses.  Recorded as a finding, not worked around silently.
;;;
;;; WHAT WAS MISSING and is proven here: real-part / imag-part of a SUM, of a
;;; REAL MULTIPLE and of a PRODUCT.  The tree had only cc-re-sub / cc-im-sub
;;; (difference) and the decomposition.  All five are one citation of
;;; `cc-re-im-of' at the coordinates plus one `crs'.
;;;
;;; LOAD WINDOW.  lo = 2387: `deriv-scalar-mult' (theorem-library/deriv-polynomial,
;;; load.scm 2387) is the LATEST citation, not the CC one a reading of the subject
;;; matter would guess.  The next-latest are `cc-converges-of-coords', `cc-re-sub',
;;; `cc-im-sub', `cc-abs-re/im-le-magnitude' and `cc-magnitude-le-re-im'
;;; (cc-complete-proof, 2267) and `cc-ms-dist' (dominated-convergence, 2254);
;;; everything else -- deriv-sum / deriv-product (deriv-sum-product, 1854),
;;; diff-transfer-ptwise-eq (diff-transfer, 1844), cartesian-pair-eq and
;;; bijection-from-inverse (monalg-is-ring, 1654), op-typing's metric-dist-real
;;; (1000), nth1-pair / nth2-pair (mat-basics, 762), rr-min-pos (rr-order-basics,
;;; 781), rr-pos-halvable (rr-halving, 848), rr-pos-rr-of-lt (pos-rr-of-lt, 841) --
;;; is far above.  hi is unconstrained: nothing cites these yet, so the file goes
;;; at the END of the theorem block.  It also needs
;;; structure-library/cc-coords.scm, which wants a slot just after
;;; structure-library/derivative (load.scm 335, for IS-DIFF-AT).
;;;
;;; Helper prefix: `ccc-'.

;;; =====================================================================
;;; File-local driver helpers.
;;; =====================================================================

;;; Peel ONE guarded universal and return the eigenvariable, read off the GOAL
;;; before the step (never off the context order).  The goal must be a FORALL.
(define (ccc-peel-var!)
  (let ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) 'FORALL)))
        (error "ccc-peel-var!: focus goal is not a FORALL" (expression->string g)))
    (let ((v (cadr g)))
      (di)
      v)))

;;; The defining equations, as `subst' arguments (subst takes `==' as `=' and
;;; rewrites in operator position, so this unfolds (CC-COORDS t) as well as a
;;; bare CC-COORDS).
(define CCC-COORDS-BODY
  '(VNB-LAMBDA zv_ CC (LIST (real-part zv_) (imag-part zv_))))
(define CCC-OF-PAIR-BODY
  '(VNB-LAMBDA pv_ (CARTESIAN RR RR) (+ (NTH 1 pv_) (* (NTH 2 pv_) +i))))

;;; A defining equation for a CONSTANT that denotes a FUNCTION unfolds in
;;; ARGUMENT position by a plain `subst' -- (IN CC-COORDS (FUN ...)) is rewritten
;;; the way rr-bounded-ms-def is -- but NOT in APPLIED position: `subst' goes
;;; through replace-term -> subst-free, whose general-compound branch substitutes
;;; a symbol head only when it is NOT a registered constant (expressions.scm:627),
;;; and `def-constant' registers the head.  The macete engine declines for the
;;; same reason.  Leibniz at the level of the APPLICATION is the way in; that is
;;; what `apply-congruence-2' (theorem-library/rake-eplus-defined.scm) does for
;;; `eplus' and `etimes', and the UNARY case it needs is proved below.
(define (ccc-unfold-coords!)
  (fact 'cc-coords-def)
  (subst (list '= 'CC-COORDS CCC-COORDS-BODY)))

(define (ccc-unfold-of-pair!)
  (fact 'cc-of-pair-def)
  (subst (list '= 'CC-OF-PAIR CCC-OF-PAIR-BODY)))

;;; Type a complex number's two coordinates in RR and in CC, and `+i' too --
;;; the standing preamble of every `crs' call below (crs reads its generators
;;; from the context, and wants (IN t CC) standalone, never conjoined).
(define (ccc-type-coords! z)
  (fact 'real-part-in-rr z)
  (fact 'imag-part-in-rr z)
  (fact 'rr-subset-cc (list 'real-part z))
  (fact 'rr-subset-cc (list 'imag-part z))
  (fact 'cc-i-in))

;;; a in RR, b in RR  |-  [a, b] in CARTESIAN(RR, RR)
(define (ccc-pair-in! a b)
  (fact 'pair-in-cartesian 'RR 'RR a b))

;;; a in RR, b in RR  |-  a + b*i in CC.
(define (ccc-combination-in-cc! a b)
  (fact 'rr-subset-cc a)
  (fact 'rr-subset-cc b)
  (fact 'cc-i-in)
  (have! (list 'AND (list 'IN b 'CC) '(IN +i CC)))
  (fact 'cc-mul-closed b '+i)
  (have! (list 'AND (list 'IN a 'CC) (list 'IN (list '* b '+i) 'CC)))
  (fact 'cc-add-closed a (list '* b '+i)))

;;; =====================================================================
;;; 0.  THE UNARY APPLICATION CONGRUENCE.
;;;
;;; f == g  =>  f(u) == g(u).  The unary twin of `apply-congruence-2'
;;; (theorem-library/rake-eplus-defined.scm:170), proved the same way and for the
;;; same reason: it is the ONLY route from a defining equation for a
;;; function-valued CONSTANT to that constant's VALUES, since no rewriter in the
;;; tree rewrites a registered constant head in applied position.  With f and g
;;; VARIABLES the same subst-free branch does substitute the head, and `==' is
;;; reflexive unconditionally.
;;;
;;; Its macete form is automatically INERT, as apply-congruence-2's is: the
;;; schema variable g occurs in the condition and the replacement but not in the
;;; source pattern, which is S-10's test.  That is what one wants -- the source
;;; pattern (f u) matches every unary application in the library.
;;;
;;; It belongs beside apply-congruence-2; it is here because this file is the
;;; first consumer and a proof agent writes new files only.
;;; =====================================================================

(sp (make-wff '(FORALL f (FORALL g (IMPLIES (== f g)
                 (FORALL u (== (f u) (g u))))))))
(dk-peel!)
(subst '(== f g))
(qrfl)
(qed 'apply-congruence-1)
(topic! 'apply-congruence-1 'plumbing)
(gloss! 'apply-congruence-1
  "Quasi-equal function terms have quasi-equal values: f == g implies
   f(u) == g(u).  The unary twin of apply-congruence-2, and the bridge a
   defining equation for a function-valued CONSTANT needs, since no rewriter in
   the tree rewrites a registered constant head in applied position.")

;;; Unfold a defined function CONSTANT at an argument: land (== (K t) (BODY t))
;;; and rewrite the goal by it, then beta-reduce.  `t' must already be typed in
;;; the lambda's domain (lam-b owes the argument typing, and dk-lam-b! closes it
;;; from the context).
(define (ccc-apply-at! defname konst body t)
  (fact defname)
  (let ((eq (dk-fact! 'apply-congruence-1 konst body t)))
    (subst eq)
    (dk-lam-b!)))

;;; =====================================================================
;;; 1.  VALUE LAWS AND TYPINGS.
;;; =====================================================================

;;; CC-COORDS at a complex number.
(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
      (== (CC-COORDS z) (LIST (real-part z) (imag-part z)))))))
(dk-peel!)
(ccc-apply-at! 'cc-coords-def 'CC-COORDS CCC-COORDS-BODY 'z)
(qrfl)
(qed 'cc-coords-apply)
(topic! 'cc-coords-apply 'algebra)
(alias! 'cc-coords-apply "the coordinate map sends z to the pair of its real and imaginary parts")

;;; CC-COORDS is a function CC -> cartesian(RR, RR).
(sp (make-wff '(IN CC-COORDS (FUN CC (CARTESIAN RR RR)))))
(ccc-unfold-coords!)
(dk-lam-t!)
(let ((v (ccc-peel-var!)))
  (fact 'real-part-in-rr v)
  (fact 'imag-part-in-rr v)
  (ccc-pair-in! (list 'real-part v) (list 'imag-part v))
  (ass))
(qed 'cc-coords-in-fun)
(topic! 'cc-coords-in-fun 'algebra)

;;; CC-OF-PAIR at a literal pair of reals.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
      (FORALL b (IMPLIES (IN b RR)
        (== (CC-OF-PAIR (LIST a b)) (+ a (* b +i)))))))))
(dk-peel!)
(ccc-pair-in! 'a 'b)
(ccc-apply-at! 'cc-of-pair-def 'CC-OF-PAIR CCC-OF-PAIR-BODY '(LIST a b))
(mac 'nth1-pair)
(mac 'nth2-pair)
(qrfl)
(qed 'cc-of-pair-apply)
(topic! 'cc-of-pair-apply 'algebra)
(alias! 'cc-of-pair-apply "the pair map sends [a, b] to a + b i")

;;; CC-OF-PAIR is a function cartesian(RR, RR) -> CC.
;;; `dk-lam-t!' closes the sethood leaf through `dk-set-close!', whose CARTESIAN
;;; branch cites `cartesian-set-iff' -- an IFF, which `fact' lands whole and does
;;; not detach -- and then calls (ass).  So the sethood is put in context HERE,
;;; on its own lane, and dk-set-close!'s final (ass) finds it.
(sp (make-wff '(IN CC-OF-PAIR (FUN (CARTESIAN RR RR) CC))))
(ccc-unfold-of-pair!)
(fact 'rr-is-set)
(have! '(AND (IN RR SET) (IN RR SET)))
(have! '(IN (CARTESIAN RR RR) SET)
  (lambda () (fact 'cartesian-set-iff 'RR 'RR) (prop)))
;; NOT `dk-lam-t!': its `dk-set-close!' recurses into the CARTESIAN factors and
;; runs (ass) on each recursive call, which fires on a SIBLING leaf once the
;; sethood one is grounded -- two warnings and a step on the wrong node.  Visit
;; the two leaves explicitly instead.
(dk-each-leaf! (lambda () (lam-t))
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORALL)
       (let ((v (ccc-peel-var!)))
         (dk-split! (dk-fact! 'cartesian-nth v 'RR 'RR))
         (ccc-combination-in-cc! (list 'NTH 1 v) (list 'NTH 2 v))
         (ass))
       (ass))))
(qed 'cc-of-pair-in-fun)
(topic! 'cc-of-pair-in-fun 'algebra)

;;; =====================================================================
;;; 2.  EACH IS THE INVERSE OF THE OTHER; BOTH ARE BIJECTIONS.
;;; =====================================================================

;;; CC-OF-PAIR(CC-COORDS(z)) = z.
(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
      (= (CC-OF-PAIR (CC-COORDS z)) z)))))
(dk-peel!)
(ccc-type-coords! 'z)
(fact 'cc-coords-apply 'z)
(subst (list '= '(CC-COORDS z) '(LIST (real-part z) (imag-part z))))
(fact 'cc-of-pair-apply '(real-part z) '(imag-part z))
(subst '(= (CC-OF-PAIR (LIST (real-part z) (imag-part z)))
           (+ (real-part z) (* (imag-part z) +i))))
;; normalise b*i to i*b, which is the shape cc-re-im-decompose produces
(have! '(= (+ (real-part z) (* (imag-part z) +i))
           (+ (real-part z) (* +i (imag-part z))))
  (lambda () (crs)))
(subst '(= (+ (real-part z) (* (imag-part z) +i))
           (+ (real-part z) (* +i (imag-part z)))))
(fact 'cc-re-im-decompose 'z)
;; the decomposition used BACKWARDS:  re z + i im z  ->  z
(subst '(= (+ (real-part z) (* +i (imag-part z))) z))
(rfl)
(qed 'cc-of-pair-of-coords)
(topic! 'cc-of-pair-of-coords 'algebra)
(alias! 'cc-of-pair-of-coords "reassembling a complex number from its coordinates returns it")

;;; CC-COORDS(CC-OF-PAIR(p)) = p.
(sp (make-wff '(FORALL pr_ (IMPLIES (IN pr_ (CARTESIAN RR RR))
      (= (CC-COORDS (CC-OF-PAIR pr_)) pr_)))))
(dk-peel!)
(dk-split! (dk-fact! 'cartesian-nth 'pr_ 'RR 'RR))
(let ((aa '(NTH 1 pr_)) (bb '(NTH 2 pr_)))
  (let ((zz (list '+ aa (list '* bb '+i))))
    (ccc-pair-in! aa bb)
    (fact 'cartesian-pair-eq 'pr_ 'RR 'RR)
    ;; CC-OF-PAIR(pr_) = CC-OF-PAIR([a,b]) = a + b i
    (subst (list '= 'pr_ (list 'LIST aa bb)))
    (fact 'cc-of-pair-apply aa bb)
    (subst (list '= (list 'CC-OF-PAIR (list 'LIST aa bb)) zz))
    ;; its coordinates are a and b
    (ccc-combination-in-cc! aa bb)
    (fact 'cc-coords-apply zz)
    (subst (list '= (list 'CC-COORDS zz)
                 (list 'LIST (list 'real-part zz) (list 'imag-part zz))))
    (have! (list '= zz zz) (lambda () (rfl)))
    (dk-split! (dk-fact! 'cc-re-im-of zz aa bb))
    (subst (list '= (list 'real-part zz) aa))
    (subst (list '= (list 'imag-part zz) bb))
    (rfl)))
(qed 'cc-coords-of-pair)
(topic! 'cc-coords-of-pair 'algebra)
(alias! 'cc-coords-of-pair "taking the coordinates of a + b i returns the pair [a, b]")

;;; ... hence both are bijections.
(sp (make-wff '(IN CC-COORDS (BIJECTION CC (CARTESIAN RR RR)))))
(fact 'cc-coords-in-fun)
(fact 'cc-of-pair-in-fun)
(have! '(FORALL u_ (IMPLIES (IN u_ CC) (= (CC-OF-PAIR (CC-COORDS u_)) u_)))
  (lambda ()
    (let ((v (ccc-peel-var!)))
      (fact 'cc-of-pair-of-coords v)
      (ass))))
(have! '(FORALL v_ (IMPLIES (IN v_ (CARTESIAN RR RR)) (= (CC-COORDS (CC-OF-PAIR v_)) v_)))
  (lambda ()
    (let ((v (ccc-peel-var!)))
      (fact 'cc-coords-of-pair v)
      (ass))))
(fact 'bijection-from-inverse 'CC '(CARTESIAN RR RR) 'CC-COORDS 'CC-OF-PAIR)
(ass)
(qed 'cc-coords-is-bijection)
(topic! 'cc-coords-is-bijection 'algebra)
(alias! 'cc-coords-is-bijection "the coordinate map is a bijection from CC onto the plane")

(sp (make-wff '(IN CC-OF-PAIR (BIJECTION (CARTESIAN RR RR) CC))))
(fact 'cc-coords-in-fun)
(fact 'cc-of-pair-in-fun)
(have! '(FORALL u_ (IMPLIES (IN u_ (CARTESIAN RR RR)) (= (CC-COORDS (CC-OF-PAIR u_)) u_)))
  (lambda ()
    (let ((v (ccc-peel-var!)))
      (fact 'cc-coords-of-pair v)
      (ass))))
(have! '(FORALL v_ (IMPLIES (IN v_ CC) (= (CC-OF-PAIR (CC-COORDS v_)) v_)))
  (lambda ()
    (let ((v (ccc-peel-var!)))
      (fact 'cc-of-pair-of-coords v)
      (ass))))
(fact 'bijection-from-inverse '(CARTESIAN RR RR) 'CC 'CC-OF-PAIR 'CC-COORDS)
(ass)
(qed 'cc-of-pair-is-bijection)
(topic! 'cc-of-pair-is-bijection 'algebra)
(alias! 'cc-of-pair-is-bijection "the pair map is a bijection from the plane onto CC")

;;; =====================================================================
;;; 3.  THE MISSING COORDINATE LAWS.
;;;
;;; The tree had real-part / imag-part of a DIFFERENCE (cc-re-sub, cc-im-sub)
;;; and the decomposition, and nothing else: no sum, no real multiple, no
;;; product.  All six are the same three moves --
;;;
;;;   1. cc-generated-by-rr gives z = x1 + y1 i and w = x2 + y2 i for
;;;      eigenvariables x1, y1, x2, y2 in RR, and cc-re-im-of identifies the
;;;      projections of z and w with them;
;;;   2. the compound term is rewritten into the SAME x + y i shape by `crs'
;;;      (which knows `+i' as an exact Scheme complex, so i^2 = -1 cancels in
;;;      the coefficient arithmetic), on a lane where no `real-part' occurs --
;;;      substituting z |-> x1 + y1 i in a goal that still mentions real-part(z)
;;;      would rewrite z inside its own projection;
;;;   3. cc-re-im-of at the compound term reads its coordinates off.
;;; =====================================================================

;;; The two coordinates of z as EIGENVARIABLES, with z's decomposition and the
;;; two projection equations landed; returns (list x y).
(define (ccc-witnesses! z)
  (let* ((ex  (dk-fact! 'cc-generated-by-rr z))
         (cx  (dk-skolem! ex))
         (ex2 (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                        (dk-contains? f cx)))
                       "the inner existential of cc-generated-by-rr"))
         (cy  (dk-skolem! ex2)))
    (dk-split! (dk-fact! 'cc-re-im-of z cx cy))
    (list cx cy)))

;;; Type a list of reals in CC as well (crs reads its generators off the context
;;; and wants each (IN t CC) STANDALONE, never conjoined).
(define (ccc-in-cc! ts)
  (for-each (lambda (t) (fact 'rr-subset-cc t)) ts)
  (fact 'cc-i-in))

;;; (IN (+ a b) RR) from a, b in RR; likewise the product.
(define (ccc-rr-add! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-add-closed a b))
(define (ccc-rr-mul! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-mul-closed a b))
(define (ccc-cc-add! a b)
  (have! (list 'AND (list 'IN a 'CC) (list 'IN b 'CC)))
  (fact 'cc-add-closed a b))
(define (ccc-cc-mul! a b)
  (have! (list 'AND (list 'IN a 'CC) (list 'IN b 'CC)))
  (fact 'cc-mul-closed a b))

;;; TM in CC, AA and BB in RR, and the decompositions of z / w in context:
;;; lands (= (real-part TM) AA) and (= (imag-part TM) BB).  `decomps' is the
;;; list of decomposition equations to substitute before `crs'.
(define (ccc-coords-of! tm aa bb decomps)
  (have! (list '= tm (list '+ aa (list '* bb '+i)))
    (lambda ()
      (for-each (lambda (e) (subst e)) decomps)
      (crs)))
  (dk-split! (dk-fact! 'cc-re-im-of tm aa bb)))

;;; ---- sum ----------------------------------------------------------------

(define (ccc-add-law! name proj pick)
  (sp (make-wff (list 'FORALL 'z (list 'IMPLIES '(IN z CC)
        (list 'FORALL 'w (list 'IMPLIES '(IN w CC)
          (list '= (list proj '(+ z w))
                   (list '+ (list proj 'z) (list proj 'w)))))))))
  (dk-peel!)
  (let* ((wz (ccc-witnesses! 'z)) (ww (ccc-witnesses! 'w))
         (x1 (car wz)) (y1 (cadr wz)) (x2 (car ww)) (y2 (cadr ww))
         (sx (list '+ x1 x2)) (sy (list '+ y1 y2)))
    (ccc-in-cc! (list x1 y1 x2 y2))
    (ccc-rr-add! x1 x2)
    (ccc-rr-add! y1 y2)
    (ccc-cc-add! 'z 'w)
    (ccc-coords-of! '(+ z w) sx sy
      (list (list '= 'z (list '+ x1 (list '* y1 '+i)))
            (list '= 'w (list '+ x2 (list '* y2 '+i)))))
    (subst (list '= (list proj '(+ z w)) (pick sx sy)))
    (subst (list '= (list proj 'z) (pick x1 y1)))
    (subst (list '= (list proj 'w) (pick x2 y2)))
    (rfl))
  (qed name)
  (topic! name 'algebra))

(ccc-add-law! 'cc-re-add 'real-part (lambda (a b) a))
(alias! 'cc-re-add "the real part of a sum is the sum of the real parts")
(ccc-add-law! 'cc-im-add 'imag-part (lambda (a b) b))
(alias! 'cc-im-add "the imaginary part of a sum is the sum of the imaginary parts")

;;; ---- real multiple ------------------------------------------------------

(define (ccc-real-mul-law! name proj pick)
  (sp (make-wff (list 'FORALL 'c_ (list 'IMPLIES '(IN c_ RR)
        (list 'FORALL 'z (list 'IMPLIES '(IN z CC)
          (list '= (list proj '(* c_ z))
                   (list '* 'c_ (list proj 'z)))))))))
  (dk-peel!)
  (let* ((wz (ccc-witnesses! 'z))
         (x1 (car wz)) (y1 (cadr wz))
         (sx (list '* 'c_ x1)) (sy (list '* 'c_ y1)))
    (ccc-in-cc! (list x1 y1 'c_))
    (ccc-rr-mul! 'c_ x1)
    (ccc-rr-mul! 'c_ y1)
    (ccc-cc-mul! 'c_ 'z)
    (ccc-coords-of! '(* c_ z) sx sy
      (list (list '= 'z (list '+ x1 (list '* y1 '+i)))))
    (subst (list '= (list proj '(* c_ z)) (pick sx sy)))
    (subst (list '= (list proj 'z) (pick x1 y1)))
    (rfl))
  (qed name)
  (topic! name 'algebra))

(ccc-real-mul-law! 'cc-re-real-mul 'real-part (lambda (a b) a))
(alias! 'cc-re-real-mul "the real part of a real multiple is that multiple of the real part")
(ccc-real-mul-law! 'cc-im-real-mul 'imag-part (lambda (a b) b))
(alias! 'cc-im-real-mul "the imaginary part of a real multiple is that multiple of the imaginary part")

;;; ---- product ------------------------------------------------------------

(define (ccc-mul-law! name proj pick)
  (sp (make-wff (list 'FORALL 'z (list 'IMPLIES '(IN z CC)
        (list 'FORALL 'w (list 'IMPLIES '(IN w CC)
          (list '= (list proj '(* z w))
                   (pick '(- (* (real-part z) (real-part w))
                             (* (imag-part z) (imag-part w)))
                         '(+ (* (real-part z) (imag-part w))
                             (* (imag-part z) (real-part w)))))))))))
  (dk-peel!)
  (let* ((wz (ccc-witnesses! 'z)) (ww (ccc-witnesses! 'w))
         (x1 (car wz)) (y1 (cadr wz)) (x2 (car ww)) (y2 (cadr ww))
         (sx (list '- (list '* x1 x2) (list '* y1 y2)))
         (sy (list '+ (list '* x1 y2) (list '* y1 x2))))
    (ccc-in-cc! (list x1 y1 x2 y2))
    (ccc-rr-mul! x1 x2) (ccc-rr-mul! y1 y2)
    (ccc-rr-mul! x1 y2) (ccc-rr-mul! y1 x2)
    (have! (list 'IN sx 'RR)
      (lambda () (fact 'rr-sub-in-rr (list '* x1 x2) (list '* y1 y2)) (ass)))
    (ccc-rr-add! (list '* x1 y2) (list '* y1 x2))
    (ccc-cc-mul! 'z 'w)
    (ccc-coords-of! '(* z w) sx sy
      (list (list '= 'z (list '+ x1 (list '* y1 '+i)))
            (list '= 'w (list '+ x2 (list '* y2 '+i)))))
    (subst (list '= (list proj '(* z w)) (pick sx sy)))
    (subst (list '= (list 'real-part 'z) x1))
    (subst (list '= (list 'imag-part 'z) y1))
    (subst (list '= (list 'real-part 'w) x2))
    (subst (list '= (list 'imag-part 'w) y2))
    (rfl))
  (qed name)
  (topic! name 'algebra))

(ccc-mul-law! 'cc-re-mul 'real-part (lambda (a b) a))
(alias! 'cc-re-mul "the real part of a product is re z re w - im z im w")
(ccc-mul-law! 'cc-im-mul 'imag-part (lambda (a b) b))
(alias! 'cc-im-mul "the imaginary part of a product is re z im w + im z re w")

;;; =====================================================================
;;; 4.  ADDITIVITY AND REAL-SCALAR COMPATIBILITY OF THE TWO MAPS.
;;;
;;; Each is the corresponding coordinate law of section 3, read through the two
;;; value laws of section 1.  (Neither map is multiplicative for the PRODUCT of
;;; pairs, and nothing here claims it is: cartesian(RR,RR) carries no ring
;;; structure in this tree.  The complex product in coordinates is cc-re-mul /
;;; cc-im-mul above.)
;;; =====================================================================

(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
     (FORALL w (IMPLIES (IN w CC)
       (= (CC-COORDS (+ z w))
          (LIST (+ (real-part z) (real-part w))
                (+ (imag-part z) (imag-part w))))))))))
(dk-peel!)
(ccc-type-coords! 'z)
(ccc-type-coords! 'w)
(ccc-cc-add! 'z 'w)
(fact 'cc-coords-apply '(+ z w))
(subst '(= (CC-COORDS (+ z w)) (LIST (real-part (+ z w)) (imag-part (+ z w)))))
(fact 'cc-re-add 'z 'w)
(fact 'cc-im-add 'z 'w)
(subst '(= (real-part (+ z w)) (+ (real-part z) (real-part w))))
(subst '(= (imag-part (+ z w)) (+ (imag-part z) (imag-part w))))
(rfl)
(qed 'cc-coords-add)
(topic! 'cc-coords-add 'algebra)
(alias! 'cc-coords-add "the coordinate map is additive")

(sp (make-wff '(FORALL c_ (IMPLIES (IN c_ RR)
     (FORALL z (IMPLIES (IN z CC)
       (= (CC-COORDS (* c_ z))
          (LIST (* c_ (real-part z)) (* c_ (imag-part z))))))))))
(dk-peel!)
(ccc-type-coords! 'z)
(fact 'rr-subset-cc 'c_)
(ccc-cc-mul! 'c_ 'z)
(fact 'cc-coords-apply '(* c_ z))
(subst '(= (CC-COORDS (* c_ z)) (LIST (real-part (* c_ z)) (imag-part (* c_ z)))))
(fact 'cc-re-real-mul 'c_ 'z)
(fact 'cc-im-real-mul 'c_ 'z)
(subst '(= (real-part (* c_ z)) (* c_ (real-part z))))
(subst '(= (imag-part (* c_ z)) (* c_ (imag-part z))))
(rfl)
(qed 'cc-coords-real-mul)
(topic! 'cc-coords-real-mul 'algebra)
(alias! 'cc-coords-real-mul "the coordinate map commutes with multiplication by a real number")

(sp (make-wff '(FORALL a1_ (IMPLIES (IN a1_ RR)
     (FORALL b1_ (IMPLIES (IN b1_ RR)
     (FORALL a2_ (IMPLIES (IN a2_ RR)
     (FORALL b2_ (IMPLIES (IN b2_ RR)
       (= (CC-OF-PAIR (LIST (+ a1_ a2_) (+ b1_ b2_)))
          (+ (CC-OF-PAIR (LIST a1_ b1_)) (CC-OF-PAIR (LIST a2_ b2_))))))))))))))
(dk-peel!)
(ccc-rr-add! 'a1_ 'a2_)
(ccc-rr-add! 'b1_ 'b2_)
(ccc-in-cc! '(a1_ b1_ a2_ b2_))
(fact 'cc-of-pair-apply '(+ a1_ a2_) '(+ b1_ b2_))
(fact 'cc-of-pair-apply 'a1_ 'b1_)
(fact 'cc-of-pair-apply 'a2_ 'b2_)
(subst '(= (CC-OF-PAIR (LIST (+ a1_ a2_) (+ b1_ b2_)))
           (+ (+ a1_ a2_) (* (+ b1_ b2_) +i))))
(subst '(= (CC-OF-PAIR (LIST a1_ b1_)) (+ a1_ (* b1_ +i))))
(subst '(= (CC-OF-PAIR (LIST a2_ b2_)) (+ a2_ (* b2_ +i))))
(crs)
(qed 'cc-of-pair-add)
(topic! 'cc-of-pair-add 'algebra)
(alias! 'cc-of-pair-add "the pair map is additive")

(sp (make-wff '(FORALL c_ (IMPLIES (IN c_ RR)
     (FORALL a_ (IMPLIES (IN a_ RR)
     (FORALL b_ (IMPLIES (IN b_ RR)
       (= (CC-OF-PAIR (LIST (* c_ a_) (* c_ b_)))
          (* c_ (CC-OF-PAIR (LIST a_ b_)))))))))))) 
(dk-peel!)
(ccc-rr-mul! 'c_ 'a_)
(ccc-rr-mul! 'c_ 'b_)
(ccc-in-cc! '(c_ a_ b_))
(fact 'cc-of-pair-apply '(* c_ a_) '(* c_ b_))
(fact 'cc-of-pair-apply 'a_ 'b_)
(subst '(= (CC-OF-PAIR (LIST (* c_ a_) (* c_ b_))) (+ (* c_ a_) (* (* c_ b_) +i))))
(subst '(= (CC-OF-PAIR (LIST a_ b_)) (+ a_ (* b_ +i))))
(crs)
(qed 'cc-of-pair-real-mul)
(topic! 'cc-of-pair-real-mul 'algebra)
(alias! 'cc-of-pair-real-mul "the pair map commutes with multiplication by a real number")

;;; =====================================================================
;;; 5.  THE TWO-SIDED ESTIMATE.
;;;
;;;     max(|re z - re w|, |im z - im w|)  <=  |z - w|
;;;                                        <=  |re z - re w| + |im z - im w|
;;;
;;; stated as the three inequalities, for the reason given in the header: the
;;; tree has no BINARY product of metric spaces to state it as a comparison of
;;; metrics.  Each is one coordinate bound of cc-magnitude.scm read through
;;; cc-re-sub / cc-im-sub.
;;; =====================================================================

(define (ccc-sub-rewrites!)
  (fact 'cc-re-sub 'z 'w)
  (fact 'cc-im-sub 'z 'w)
  ;; guarded on the GOAL: a `subst' with nothing to rewrite is a no-op that warns
  ;; and is not recorded, and two of the three estimates mention one coordinate.
  (if (dk-contains? (dk-goal) 'real-part)
      (subst '(= (- (real-part z) (real-part w)) (real-part (- z w)))))
  (if (dk-contains? (dk-goal) 'imag-part)
      (subst '(= (- (imag-part z) (imag-part w)) (imag-part (- z w))))))

(define (ccc-estimate! name stmt cited)
  (sp (make-wff stmt))
  (dk-peel!)
  (fact 'cc-sub-in-cc 'z 'w)
  (fact cited '(- z w))
  (ccc-sub-rewrites!)
  (ass)
  (qed name)
  (topic! name 'inequalities))

(ccc-estimate! 'cc-re-dist-le
  '(FORALL z (IMPLIES (IN z CC)
     (FORALL w (IMPLIES (IN w CC)
       (<= (abs (- (real-part z) (real-part w))) (magnitude (- z w)))))))
  'cc-abs-re-le-magnitude)
(alias! 'cc-re-dist-le "the distance between the real parts is at most the distance in CC")

(ccc-estimate! 'cc-im-dist-le
  '(FORALL z (IMPLIES (IN z CC)
     (FORALL w (IMPLIES (IN w CC)
       (<= (abs (- (imag-part z) (imag-part w))) (magnitude (- z w)))))))
  'cc-abs-im-le-magnitude)
(alias! 'cc-im-dist-le "the distance between the imaginary parts is at most the distance in CC")

(ccc-estimate! 'cc-dist-le-coords
  '(FORALL z (IMPLIES (IN z CC)
     (FORALL w (IMPLIES (IN w CC)
       (<= (magnitude (- z w))
           (+ (abs (- (real-part z) (real-part w)))
              (abs (- (imag-part z) (imag-part w)))))))))
  'cc-magnitude-le-re-im)
(alias! 'cc-dist-le-coords "the distance in CC is at most the sum of the two coordinate distances")

;;; =====================================================================
;;; 6.  TRANSFER (a): A SEQUENCE IN CC CONVERGES IFF ITS COORDINATE SEQUENCES DO.
;;;
;;; TRANSFER FORM, like `cc-converges-of-coords' itself: the caller supplies two
;;; real sequences agreeing POINTWISE with the coordinates, rather than the
;;; theorem concluding about lambdas it built -- a conclusion about a literal
;;; VNB-LAMBDA can only be applied to that lambda, and every use then owes a
;;; beta-reduction under a binder (the design note of
;;; theorem-library/cc-complete-proof.scm).
;;;
;;; The BACKWARD half is `cc-converges-of-coords', proven 2026-08-24.  The
;;; FORWARD half is proven here and is the shorter of the two: no halving and no
;;; MAX, because ONE threshold serves both coordinates --
;;;
;;;     |g(n) - Re L|  =  |Re(f(n)) - Re L|  <=  |f(n) - L|  <=  eps
;;;
;;; the middle step being `cc-re-dist-le' of section 5.
;;; =====================================================================

(define (ccc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ccc-find: no context formula" what))
          ((pred (car l)) (car l))
          (#t (loop (cdr l))))))

;;; Split an AND goal to exhaustion and run CLOSER on each atomic leaf.
(define (ccc-and-goal! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ccc-and-goal! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an ASSUMPTION lands: an UNGUARDED universal peels the quantifier
;;; and lands nothing, so loop on the LANDING, never on a `di' count.
(define (ccc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "ccc-di-landed!: di landed no assumption"))
            (#t (loop (+ n 1)))))))
(define (ccc-di-landed-1!)
  (let ((new (ccc-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "ccc-di-landed-1!: expected 1" (map expression->string new)))))

;;; (IN x RR) from (POS-RR x) BY CITATION -- `mac-h' would consume the POS-RR the
;;; next detachment needs.
(define (ccc-pos-in-rr! x)
  (fact 'rr-pos-rr-in-rr x))

;;; THE FORWARD HALF.
(sp (make-wff "forall([f in fun(nn,cc), g in fun(nn,rr), q_ in fun(nn,rr), lv in cc],
     forall([n_ in nn], real-part(f(n_)) = g(n_)) implies
     forall([n_ in nn], imag-part(f(n_)) = q_(n_)) implies
     converges-to(cc-ms, f, lv) implies
     converges-to(rr-ms, g, real-part(lv)) and converges-to(rr-ms, q_, imag-part(lv)))"))
(dk-peel!)
(define ccv-re (ccc-find 're (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                              (dk-contains? a 'real-part)))))
(define ccv-im (ccc-find 'im (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                              (dk-contains? a 'imag-part)))))
(dk-split! (dk-landed-find
            (lambda () (mac-h 'converges-to '(CONVERGES-TO CC-MS f lv)))
            (lambda (a) (eq? (car a) 'AND))))
(define ccv-tail (ccc-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                  (dk-contains? a 'POS-RR)))))
(fact 'real-part-in-rr 'lv)
(fact 'imag-part-in-rr 'lv)

;;; One coordinate branch: `seq' the real sequence, `proj' the projection,
;;; `ptwise' the pointwise hypothesis, `bound' the coordinate estimate.
(define (ccv-branch! seq proj ptwise bound)
  (mac 'converges-to)
  (ccc-and-goal!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
             ((eq? (car gl) 'IN)
              ;; `slot' takes (PTS RR-MS) to RR, but for a VARIABLE s it unfolds
              ;; the ACCESSOR, (PTS s) -> NTH(1, s), and the goal stops matching
              ;; the context.  So close what the context already holds first.
              (if (dk-ctx-form gl) (ass) (begin (slot 'PTS) (ass))))
             (#t
              (let* ((epsf (ccc-di-landed-1!))
                     (eps  (cadr epsf))
                     (ex   (dk-deepest (lambda () (inst+ ccv-tail eps))))
                     (thr  (dk-skolem! ex))
                     (inner (ccc-find 'inner
                              (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                               (dk-contains? a thr)
                                               (dk-contains? a 'f))))))
                (ccc-pos-in-rr! eps)
                (ew thr)
                (ccc-and-goal!
                 (lambda ()
                   (if (eq? (car (dk-goal)) 'IN)
                       (ass)
                       (let* ((tyf (ccc-di-landed-1!))
                              (nx  (cadr tyf)))
                         (ccc-di-landed!)                     ; (thr <= nx)
                         (let* ((fnx (list 'f nx))
                                (dif (list '- fnx 'lv))
                                (est (dk-apply! inner nx)))
                           (fact 'fun-apply-type-c 'f 'NN 'CC nx)
                           (fact 'fun-apply-type-c seq 'NN 'RR nx)
                           (fact 'cc-sub-in-cc fnx 'lv)
                           (fact 'cc-magnitude-closed dif)
                           (fact 'real-part-in-rr fnx)
                           (fact 'imag-part-in-rr fnx)
                           (mac-h 'cc-ms-dist est)
                           (mac 'rr-ms-dist)
                           (inst+ ptwise nx)
                           (subst (list '= (list seq nx) (list proj fnx)))
                           (fact bound fnx 'lv)
                           (dk-ineq!
                            (list '<= (list 'abs (list '- (list proj fnx) (list proj 'lv)))
                                      (list 'magnitude dif))
                            (list '<= (list 'magnitude dif) eps))))))))))))))

(ccc-and-goal!
 (lambda ()
   (if (dk-contains? (dk-goal) 'real-part)
       (ccv-branch! 'g 'real-part ccv-re 'cc-re-dist-le)
       (ccv-branch! 'q_ 'imag-part ccv-im 'cc-im-dist-le))))
(qed 'cc-coords-of-converges)
(topic! 'cc-coords-of-converges 'analysis)
(alias! 'cc-coords-of-converges
  "if a sequence converges in CC then both coordinate sequences converge to the coordinates of the limit")

;;; THE EQUIVALENCE.  Backward is `cc-converges-of-coords', forward is the
;;; theorem just proved.
(sp (make-wff "forall([f in fun(nn,cc), g in fun(nn,rr), q_ in fun(nn,rr), lv in cc],
     forall([n_ in nn], real-part(f(n_)) = g(n_)) implies
     forall([n_ in nn], imag-part(f(n_)) = q_(n_)) implies
     (converges-to(cc-ms, f, lv) iff
      converges-to(rr-ms, g, real-part(lv)) and converges-to(rr-ms, q_, imag-part(lv))))"))
(dk-peel!)
;; `di' on an IFF GOAL does not produce two implications: it lands one side as an
;; ASSUMPTION and leaves the other as the goal.  So the leaf whose GOAL is the
;; conjunction is the FORWARD half, and nothing is to be peeled inside either.
(dk-iff!
 (lambda (gl) (dk-head-is? gl 'AND))
 (lambda ()                                   ; CC convergence => coordinates
   (fact 'cc-coords-of-converges 'f 'g 'q_ 'lv)
   (ass))
 (lambda ()                                   ; coordinates => CC convergence
   (dk-split-all!)
   (fact 'cc-converges-of-coords 'f 'g 'q_ 'lv)
   (ass)))
(qed 'cc-converges-iff-coords)
(topic! 'cc-converges-iff-coords 'analysis)
(alias! 'cc-converges-iff-coords
  "a sequence converges in CC exactly when both coordinate sequences converge in RR")

;;; =====================================================================
;;; 7.  TRANSFER (b): CONTINUITY INTO CC IS CONTINUITY OF BOTH COORDINATES.
;;;
;;; TRANSFER FORM again: `fr' and `fi' are given, agreeing pointwise with
;;; re o f and im o f, so no consumer owes a beta-reduction under a binder.
;;;
;;; FORWARD is one threshold and `cc-re-dist-le' / `cc-im-dist-le'.  BACKWARD
;;; halves eps (rr-pos-halvable) and takes a positive delta below both of the
;;; coordinates' deltas -- by `rr-min-pos', which HANDS one over as an
;;; existential, so no MIN term and no case split on rr-min-cases is needed --
;;; and closes with `cc-dist-le-coords'.
;;; =====================================================================

(define (ccc-cont-tail! form)
  ;; unfold an IS-CONTINUOUS-AT hypothesis and return its eps-tail
  (dk-split! (dk-landed-find (lambda () (mac-h 'is-continuous-at form))
                             (lambda (a) (eq? (car a) 'AND))))
  (ccc-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                   (dk-contains? a 'POS-RR)
                                   (dk-contains? a (cadddr form))))))

(sp (make-wff "forall([s, f, fr, fi, a],
     is-metric-space(s) implies
     f in fun(pts(s), cc) implies
     fr in fun(pts(s), rr) implies
     fi in fun(pts(s), rr) implies
     a in pts(s) implies
     forall([u_ in pts(s)], real-part(f(u_)) = fr(u_)) implies
     forall([u_ in pts(s)], imag-part(f(u_)) = fi(u_)) implies
     (is-continuous-at(s, cc-ms, f, a) iff
      is-continuous-at(s, rr-ms, fr, a) and is-continuous-at(s, rr-ms, fi, a)))"))
(dk-peel!)
(define ccb-re (ccc-find 're (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                              (dk-contains? x 'real-part)))))
(define ccb-im (ccc-find 'im (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                              (dk-contains? x 'imag-part)))))
(fact 'cc-is-metric-space)
(fact 'rr-is-metric-space)

;;; ---- the FORWARD branch, one coordinate at a time -----------------------
(define (ccb-fwd-branch! tail seq proj ptwise bound)
  (mac 'is-continuous-at)
  (ccc-and-goal!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
             ((eq? (car gl) 'IN)
              ;; `slot' takes (PTS RR-MS) to RR, but for a VARIABLE s it unfolds
              ;; the ACCESSOR, (PTS s) -> NTH(1, s), and the goal stops matching
              ;; the context.  So close what the context already holds first.
              (if (dk-ctx-form gl) (ass) (begin (slot 'PTS) (ass))))
             (#t
              (let* ((epsf (ccc-di-landed-1!))
                     (eps  (cadr epsf))
                     (ex   (dk-deepest (lambda () (inst+ tail eps))))
                     (del  (dk-skolem! ex))
                     (inner (ccc-find 'inner
                              (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                               (dk-contains? x del)
                                               (dk-contains? x 'f))))))
                (ccc-pos-in-rr! eps)
                (ew del)
                (ccc-and-goal!
                 (lambda ()
                   (if (eq? (car (dk-goal)) 'POS-RR)
                       (ass)
                       (let* ((tyf (ccc-di-landed-1!))
                              (bx  (cadr tyf)))
                         (ccc-di-landed!)                 ; dist(s)(a, bx) <= del
                         (let* ((fa  '(f a))
                                (fb  (list 'f bx))
                                (dif (list '- fa fb))
                                (est (dk-apply! inner bx)))
                           (fact 'fun-apply-type-c 'f '(PTS s) 'CC 'a)
                           (fact 'fun-apply-type-c 'f '(PTS s) 'CC bx)
                           (fact 'fun-apply-type-c seq '(PTS s) 'RR 'a)
                           (fact 'fun-apply-type-c seq '(PTS s) 'RR bx)
                           (fact 'cc-sub-in-cc fa fb)
                           (fact 'cc-magnitude-closed dif)
                           (fact 'real-part-in-rr fa) (fact 'real-part-in-rr fb)
                           (fact 'imag-part-in-rr fa) (fact 'imag-part-in-rr fb)
                           (mac-h 'cc-ms-dist est)
                           (mac 'rr-ms-dist)
                           (inst+ ptwise 'a)
                           (inst+ ptwise bx)
                           (subst (list '= (list seq 'a) (list proj fa)))
                           (subst (list '= (list seq bx) (list proj fb)))
                           (fact bound fa fb)
                           (dk-ineq!
                            (list '<= (list 'abs (list '- (list proj fa) (list proj fb)))
                                      (list 'magnitude dif))
                            (list '<= (list 'magnitude dif) eps))))))))))))))

;;; ---- the BACKWARD branch ------------------------------------------------
(define (ccb-bwd!)
  (let* ((hyps  (dk-split-all!))
         (hre   (ccc-find 'cont-re
                  (lambda (x) (and (pair? x) (eq? (car x) 'IS-CONTINUOUS-AT)
                                   (eq? (cadddr x) 'fr)))))
         (him   (ccc-find 'cont-im
                  (lambda (x) (and (pair? x) (eq? (car x) 'IS-CONTINUOUS-AT)
                                   (eq? (cadddr x) 'fi)))))
         (tre   (ccc-cont-tail! hre))
         (tim   (ccc-cont-tail! him)))
    (mac 'is-continuous-at)
    (ccc-and-goal!
     (lambda ()
       (let ((gl (dk-goal)))
         (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
               ((eq? (car gl) 'IN)
              ;; `slot' takes (PTS RR-MS) to RR, but for a VARIABLE s it unfolds
              ;; the ACCESSOR, (PTS s) -> NTH(1, s), and the goal stops matching
              ;; the context.  So close what the context already holds first.
              (if (dk-ctx-form gl) (ass) (begin (slot 'PTS) (ass))))
               (#t
                (let* ((epsf (ccc-di-landed-1!))
                       (eps  (cadr epsf))
                       (hlf  (dk-halve! eps))
                       (exr  (dk-deepest (lambda () (inst+ tre hlf))))
                       (dr   (dk-skolem! exr))
                       (innr (ccc-find 'inner-re
                               (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                                (dk-contains? x dr)
                                                (dk-contains? x 'fr)))))
                       (exi  (dk-deepest (lambda () (inst+ tim hlf))))
                       (di_  (dk-skolem! exi))
                       (inni (ccc-find 'inner-im
                               (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                                (dk-contains? x di_)
                                                (dk-contains? x 'fi))))))
                  (ccc-pos-in-rr! eps)
                  (ccc-pos-in-rr! dr) (ccc-pos-in-rr! di_)
                  (fact 'rr-lt-of-pos-rr dr) (fact 'rr-lt-of-pos-rr di_)
                  (let* ((exw (dk-fact! 'rr-min-pos dr di_))
                         (wv  (dk-skolem! exw)))
                    (have! (list 'POS-RR wv)
                      (lambda () (fact 'rr-pos-rr-of-lt wv) (ass)))
                    (ew wv)
                    (ccc-and-goal!
                     (lambda ()
                       (if (eq? (car (dk-goal)) 'POS-RR)
                           (ass)
                           (let* ((tyf (ccc-di-landed-1!))
                                  (bx  (cadr tyf)))
                             (let* ((dle  (car (ccc-di-landed!)))   ; dist(s)(a,bx) <= wv
                                    (dsab (cadr dle)))
                               (fact 'metric-dist-real 's 'a bx)
                               (have! (list '<= dsab dr)
                                 (lambda () (dk-ineq! dle (list '<= wv dr))))
                               (have! (list '<= dsab di_)
                                 (lambda () (dk-ineq! dle (list '<= wv di_))))
                               (let* ((fa  '(f a))
                                      (fb  (list 'f bx))
                                      (dif (list '- fa fb))
                                      (er  (dk-apply! innr bx))
                                      (ei  (dk-apply! inni bx)))
                                 (fact 'fun-apply-type-c 'f '(PTS s) 'CC 'a)
                                 (fact 'fun-apply-type-c 'f '(PTS s) 'CC bx)
                                 (fact 'fun-apply-type-c 'fr '(PTS s) 'RR 'a)
                                 (fact 'fun-apply-type-c 'fr '(PTS s) 'RR bx)
                                 (fact 'fun-apply-type-c 'fi '(PTS s) 'RR 'a)
                                 (fact 'fun-apply-type-c 'fi '(PTS s) 'RR bx)
                                 (fact 'cc-sub-in-cc fa fb)
                                 (fact 'cc-magnitude-closed dif)
                                 (fact 'real-part-in-rr fa) (fact 'real-part-in-rr fb)
                                 (fact 'imag-part-in-rr fa) (fact 'imag-part-in-rr fb)
                                 (mac-h 'rr-ms-dist er)
                                 (mac-h 'rr-ms-dist ei)
                                 (mac 'cc-ms-dist)
                                 (inst+ ccb-re 'a) (inst+ ccb-re bx)
                                 (inst+ ccb-im 'a) (inst+ ccb-im bx)
                                 (fact 'cc-dist-le-coords fa fb)
                                 ;; There is no hypothesis-side `subst', and the two
                                 ;; estimates that came out of mac-h speak of fr / fi
                                 ;; while cc-dist-le-coords speaks of real-part / imag-part.
                                 ;; So the bridge is cut as a CLAIM, where `subst' reaches
                                 ;; the terms, and the oracle then sees one vocabulary.
                                 (let ((bnd (list '<= (list 'magnitude dif)
                                              (list '+ (list 'abs (list '- (list 'fr 'a)
                                                                           (list 'fr bx)))
                                                       (list 'abs (list '- (list 'fi 'a)
                                                                           (list 'fi bx)))))))
                                   (have! bnd
                                     (lambda ()
                                       (subst (list '= (list 'fr 'a) (list 'real-part fa)))
                                       (subst (list '= (list 'fr bx) (list 'real-part fb)))
                                       (subst (list '= (list 'fi 'a) (list 'imag-part fa)))
                                       (subst (list '= (list 'fi bx) (list 'imag-part fb)))
                                       (ass)))
                                   (dk-ineq!
                                    bnd
                                    (list '<= (list 'abs (list '- (list 'fr 'a) (list 'fr bx))) hlf)
                                    (list '<= (list 'abs (list '- (list 'fi 'a) (list 'fi bx))) hlf)
                                    (list '= (list '+ hlf hlf) eps))))))))))))))))))

(dk-iff!
 (lambda (gl) (dk-head-is? gl 'AND))
 (lambda ()                                   ; CC continuity => coordinates
   (let ((tail (ccc-cont-tail! '(IS-CONTINUOUS-AT s CC-MS f a))))
     (ccc-and-goal!
      (lambda ()
        (if (dk-contains? (dk-goal) 'fr)
            (ccb-fwd-branch! tail 'fr 'real-part ccb-re 'cc-re-dist-le)
            (ccb-fwd-branch! tail 'fi 'imag-part ccb-im 'cc-im-dist-le))))))
 ccb-bwd!)
(qed 'cc-continuous-at-iff-coords)
(topic! 'cc-continuous-at-iff-coords 'analysis)
(alias! 'cc-continuous-at-iff-coords
  "a map into CC is continuous at a point exactly when both coordinate maps are")

;;; =====================================================================
;;; 8.  TRANSFER (c): DIFFERENTIABILITY OF A CC-VALUED FUNCTION OF A REAL
;;;     VARIABLE.
;;;
;;; WHICH NOTION OF DERIVATIVE.  None of the three in the tree covers a map
;;; RR -> CC (the reasons are written out at the definition,
;;; structure-library/cc-coords.scm): IS-DIFF-AT has codomain RR, IS-DIFF-ON
;;; needs an OPEN domain in a normed field and RR is not open in CC, and
;;; IS-DIFF-AT-V would fit but there is no NORMED-VECTOR-SPACE instance on CC.
;;; So IS-CC-DIFF-AT is DEFINED coordinatewise, and this section is its
;;; elementary theory.
;;;
;;; The equivalence below is the definition read in TRANSFER form -- the caller
;;; supplies gr and gi agreeing pointwise with the coordinates -- so that no
;;; consumer has to beta-reduce under a binder.  The bridge is
;;; `diff-transfer-ptwise-eq' (theorem-library/differentiation.scm): two
;;; functions of FUN(RR,RR) that agree pointwise are differentiable together.
;;; =====================================================================

(sp (make-wff "forall([g in fun(rr,cc), gr in fun(rr,rr), gi in fun(rr,rr), tv_ in rr, lv in cc],
     forall([x_ in rr], real-part(g(x_)) = gr(x_)) implies
     forall([x_ in rr], imag-part(g(x_)) = gi(x_)) implies
     (is-cc-diff-at(g, tv_, lv) iff
      is-diff-at(gr, tv_, real-part(lv)) and is-diff-at(gi, tv_, imag-part(lv))))"))
(dk-peel!)
(define ccd-re (ccc-find 're (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                              (dk-contains? x 'real-part)))))
(define ccd-im (ccc-find 'im (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                              (dk-contains? x 'imag-part)))))

;;; forall x_ in RR.  (A x_) == (B x_),  proved from the pointwise hypothesis
;;; `ptw' (which is stated the other way round, real-part(g(x)) = gr(x)).
(define (ccd-agree! a b ptw)
  (let ((claim (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                                       (list '== (list a 'x_) (list b 'x_))))))
    (have! claim
      (lambda ()
        (di)
        (dk-lam-b!)
        (inst+ ptw 'x_)
        (let ((gl (dk-goal)))
          (subst (list '= (cadr gl) (caddr gl))))
        (qrfl)))
    claim))

(dk-iff!
 (lambda (gl) (dk-head-is? gl 'AND))
 (lambda ()                                   ; IS-CC-DIFF-AT => the coordinates
   (dk-split! (dk-landed-find
               (lambda () (mac-h 'is-cc-diff-at '(IS-CC-DIFF-AT g tv_ lv)))
               (lambda (x) (eq? (car x) 'AND))))
   (let ((hre (ccc-find 'dre (lambda (x) (and (pair? x) (eq? (car x) 'IS-DIFF-AT)
                                              (dk-contains? x 'real-part)))))
         (him (ccc-find 'dim (lambda (x) (and (pair? x) (eq? (car x) 'IS-DIFF-AT)
                                              (dk-contains? x 'imag-part))))))
     (ccc-and-goal!
      (lambda ()
        (let* ((gl  (dk-goal))
               (fn  (cadr gl))
               (hyp (if (dk-contains? gl 'real-part) hre him))
               (ptw (if (dk-contains? gl 'real-part) ccd-re ccd-im))
               (lam (cadr hyp)))
          (ccd-agree! fn lam ptw)
          (fact 'diff-transfer-ptwise-eq fn lam 'tv_ (cadddr gl))
          (ass))))))
 (lambda ()                                   ; the coordinates => IS-CC-DIFF-AT
   (dk-split-all!)
   (mac 'is-cc-diff-at)
   (ccc-and-goal!
    (lambda ()
      (let ((gl (dk-goal)))
        (if (eq? (car gl) 'IN)
            (ass)
            (let* ((lam (cadr gl))
                   (dl  (cadddr gl))
                   (rl? (dk-contains? dl 'real-part))
                   (fn  (if rl? 'gr 'gi))
                   (ptw (if rl? ccd-re ccd-im)))
              (have! (list 'IN lam '(FUN RR RR))
                (lambda ()
                  (dk-lam-t!)
                  (let ((v (ccc-peel-var!)))
                    (fact 'fun-apply-type-c 'g 'RR 'CC v)
                    (if rl?
                        (fact 'real-part-in-rr (list 'g v))
                        (fact 'imag-part-in-rr (list 'g v)))
                    (ass))))
              (ccd-agree! lam fn ptw)
              (fact 'diff-transfer-ptwise-eq lam fn 'tv_ dl)
              (ass)))))))) 
(qed 'cc-diff-at-iff-coords)
(topic! 'cc-diff-at-iff-coords 'analysis)
(alias! 'cc-diff-at-iff-coords
  "a CC-valued function of a real variable is differentiable exactly when both coordinate functions are")

;;; =====================================================================
;;; 9.  THE ELEMENTARY LAWS OF IS-CC-DIFF-AT.
;;;
;;; Each is stated in TRANSFER form -- the combined function is a PARAMETER,
;;; agreeing pointwise with the combination -- so that no statement mentions a
;;; VNB-LAMBDA and no consumer owes a beta-reduction.  Each proof is the same
;;; four moves: unfold the hypotheses into their coordinate IS-DIFF-ATs, rewrite
;;; the target derivative by the coordinate law of section 3, run the REAL
;;; differentiation law (deriv-sum / deriv-scalar-mult / deriv-product,
;;; theorem-library/differentiation.scm) on the coordinates, and move the
;;; conclusion onto the wanted function by `diff-transfer-ptwise-eq'.
;;; =====================================================================

;;; The coordinate IS-DIFF-AT hypothesis of FN for the projection PROJ.
(define (ccd-diff-of fn proj)
  (ccc-find (list 'diff-of fn proj)
    (lambda (x) (and (pair? x) (eq? (car x) 'IS-DIFF-AT)
                     (dk-contains? x fn) (dk-contains? x proj)))))

(define (ccd-unfold! form)
  (dk-split! (dk-landed-find (lambda () (mac-h 'is-cc-diff-at form))
                             (lambda (x) (eq? (car x) 'AND)))))

;;; (IN LAM (FUN RR RR)) for LAM = vnb-lambda(sv_, rr, PROJ(FN(sv_))).
(define (ccd-lam-in-fun! lam fn proj)
  (have! (list 'IN lam '(FUN RR RR))
    (lambda ()
      (dk-lam-t!)
      (let ((v (ccc-peel-var!)))
        (fact 'fun-apply-type-c fn 'RR 'CC v)
        (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr)
              (list fn v))
        (ass)))))

;;; ---- sum ----------------------------------------------------------------

(sp (make-wff "forall([g in fun(rr,cc), h in fun(rr,cc), sm in fun(rr,cc), tv_ in rr,
                       lv in cc, mv in cc],
     forall([x_ in rr], sm(x_) = g(x_) + h(x_)) implies
     is-cc-diff-at(g, tv_, lv) implies
     is-cc-diff-at(h, tv_, mv) implies
     is-cc-diff-at(sm, tv_, lv + mv))"))
(dk-peel!)
(define ccs-ptw (ccc-find 'ptw (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                                (dk-contains? x 'sm)))))
(ccd-unfold! '(IS-CC-DIFF-AT g tv_ lv))
(ccd-unfold! '(IS-CC-DIFF-AT h tv_ mv))
(have! '(AND (IN lv CC) (IN mv CC)))
(fact 'cc-add-closed 'lv 'mv)
(fact 'cc-re-add 'lv 'mv)
(fact 'cc-im-add 'lv 'mv)
(mac 'is-cc-diff-at)
(ccc-and-goal!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (car gl) 'IN)
         (ass)
         (let* ((lam  (cadr gl))
                (dl   (cadddr gl))
                (proj (if (dk-contains? gl 'real-part) 'real-part 'imag-part))
                (dg   (ccd-diff-of 'g proj))
                (dh   (ccd-diff-of 'h proj)))
           (subst (list '= dl (list '+ (list proj 'lv) (list proj 'mv))))
           (have! (list 'AND dg dh))
           (let* ((res (dk-fact! 'deriv-sum (cadr dg) (cadr dh) 'tv_
                                 (cadddr dg) (cadddr dh)))
                  (sl  (cadr res)))
             (ccd-lam-in-fun! lam 'sm proj)
             (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                          (list '== (list lam 'x_) (list sl 'x_))))
               (lambda ()
                 (di)
                 (fact 'fun-apply-type-c 'g 'RR 'CC 'x_)
                 (fact 'fun-apply-type-c 'h 'RR 'CC 'x_)
                 (fact 'fun-apply-type-c 'sm 'RR 'CC 'x_)
                 (dk-lam-b!)
                 (inst+ ccs-ptw 'x_)
                 (subst '(= (sm x_) (+ (g x_) (h x_))))
                 (fact (if (eq? proj 'real-part) 'cc-re-add 'cc-im-add)
                       '(g x_) '(h x_))
                 (subst (list '= (list proj '(+ (g x_) (h x_)))
                              (list '+ (list proj '(g x_)) (list proj '(h x_)))))
                 (qrfl)))
             (fact 'diff-transfer-ptwise-eq lam sl 'tv_ (cadddr res))
             (ass)))))))
(qed 'cc-diff-at-sum)
(topic! 'cc-diff-at-sum 'analysis)
(alias! 'cc-diff-at-sum "the sum of two differentiable CC-valued functions is differentiable")

;;; ---- multiplication by a real constant ----------------------------------

(sp (make-wff "forall([c_ in rr, g in fun(rr,cc), pd in fun(rr,cc), tv_ in rr, lv in cc],
     forall([x_ in rr], pd(x_) = c_ * g(x_)) implies
     is-cc-diff-at(g, tv_, lv) implies
     is-cc-diff-at(pd, tv_, c_ * lv))"))
(dk-peel!)
(define ccm-ptw (ccc-find 'ptw (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                                (dk-contains? x 'pd)))))
(ccd-unfold! '(IS-CC-DIFF-AT g tv_ lv))
(fact 'rr-subset-cc 'c_)
(have! '(AND (IN c_ CC) (IN lv CC)))
(fact 'cc-mul-closed 'c_ 'lv)
(fact 'cc-re-real-mul 'c_ 'lv)
(fact 'cc-im-real-mul 'c_ 'lv)
(mac 'is-cc-diff-at)
(ccc-and-goal!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (car gl) 'IN)
         (ass)
         (let* ((lam  (cadr gl))
                (dl   (cadddr gl))
                (proj (if (dk-contains? gl 'real-part) 'real-part 'imag-part))
                (dg   (ccd-diff-of 'g proj)))
           (subst (list '= dl (list '* 'c_ (list proj 'lv))))
           (let* ((res (dk-fact! 'deriv-scalar-mult 'c_ (cadr dg) 'tv_ (cadddr dg)))
                  (sl  (cadr res)))
             (ccd-lam-in-fun! lam 'pd proj)
             (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
                          (list '== (list lam 'x_) (list sl 'x_))))
               (lambda ()
                 (di)
                 (fact 'fun-apply-type-c 'g 'RR 'CC 'x_)
                 (fact 'fun-apply-type-c 'pd 'RR 'CC 'x_)
                 (dk-lam-b!)
                 (inst+ ccm-ptw 'x_)
                 (subst '(= (pd x_) (* c_ (g x_))))
                 (fact (if (eq? proj 'real-part) 'cc-re-real-mul 'cc-im-real-mul)
                       'c_ '(g x_))
                 (subst (list '= (list proj '(* c_ (g x_)))
                              (list '* 'c_ (list proj '(g x_)))))
                 (qrfl)))
             (fact 'diff-transfer-ptwise-eq lam sl 'tv_ (cadddr res))
             (ass)))))))
(qed 'cc-diff-at-real-mul)
(topic! 'cc-diff-at-real-mul 'analysis)
(alias! 'cc-diff-at-real-mul "a real multiple of a differentiable CC-valued function is differentiable")

;;; ---- product ------------------------------------------------------------
;;;
;;; The coordinates' product rule, which is what section 3.2 of the design note
;;; will use.  Re(gh) = Re g Re h - Im g Im h and Im(gh) = Re g Im h + Im g Re h
;;; (cc-re-mul / cc-im-mul of section 3), so the REAL coordinate is a sum of two
;;; products with a MINUS.  The tree has no difference rule for IS-DIFF-AT, so
;;; the second product enters through `deriv-scalar-mult' at -1 and then
;;; `deriv-sum'; the IMAGINARY coordinate is a plain sum of two products.

(define (ccp-prod! u v du dv)
  (have! (list 'AND (list 'IS-DIFF-AT u 'tv_ du) (list 'IS-DIFF-AT v 'tv_ dv)))
  (dk-fact! 'deriv-product u v 'tv_ du dv))

(sp (make-wff "forall([g in fun(rr,cc), h in fun(rr,cc), pr_ in fun(rr,cc), tv_ in rr,
                       lv in cc, mv in cc],
     forall([x_ in rr], pr_(x_) = g(x_) * h(x_)) implies
     is-cc-diff-at(g, tv_, lv) implies
     is-cc-diff-at(h, tv_, mv) implies
     is-cc-diff-at(pr_, tv_, lv * h(tv_) + g(tv_) * mv))"))
(dk-peel!)
(define ccp-ptw (ccc-find 'ptw (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                                (dk-contains? x 'pr_)))))
(ccd-unfold! '(IS-CC-DIFF-AT g tv_ lv))
(ccd-unfold! '(IS-CC-DIFF-AT h tv_ mv))
(fact 'fun-apply-type-c 'g 'RR 'CC 'tv_)
(fact 'fun-apply-type-c 'h 'RR 'CC 'tv_)
(ccc-type-coords! 'lv) (ccc-type-coords! 'mv)
(ccc-type-coords! '(g tv_)) (ccc-type-coords! '(h tv_))
(ccc-cc-mul! 'lv '(h tv_))
(ccc-cc-mul! '(g tv_) 'mv)
(ccc-cc-add! '(* lv (h tv_)) '(* (g tv_) mv))
(have! '(IN -1 RR) (lambda () (in-rr)))
;; the four coordinate lambdas of g and of h
(define ccp-are (cadr (ccd-diff-of 'g 'real-part)))
(define ccp-aim (cadr (ccd-diff-of 'g 'imag-part)))
(define ccp-bre (cadr (ccd-diff-of 'h 'real-part)))
(define ccp-bim (cadr (ccd-diff-of 'h 'imag-part)))

;;; The common tail: rewrite the goal's derivative to VAL, type the target
;;; lambda, prove it agrees pointwise with SL, and transfer.
(define (ccp-finish! lam dl proj sl val ptw-thunk)
  (subst (list '= dl val))
  (ccd-lam-in-fun! lam 'pr_ proj)
  (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
               (list '== (list lam 'x_) (list sl 'x_))))
    ptw-thunk)
  (fact 'diff-transfer-ptwise-eq lam sl 'tv_ val)
  (ass))

(mac 'is-cc-diff-at)
(ccc-and-goal!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (car gl) 'IN)
         (ass)
         (let* ((lam (cadr gl))
                (dl  (cadddr gl))
                (rl? (dk-contains? gl 'real-part))
                (proj (if rl? 'real-part 'imag-part)))
           (if rl?
               ;; Re(gh) = Re g Re h + (-1) * (Im g Im h)
               (let* ((r1 (ccp-prod! ccp-are ccp-bre '(real-part lv) '(real-part mv)))
                      (r2 (ccp-prod! ccp-aim ccp-bim '(imag-part lv) '(imag-part mv)))
                      (r3 (dk-fact! 'deriv-scalar-mult -1 (cadr r2) 'tv_ (cadddr r2)))
                      (r4 (begin (have! (list 'AND r1 r3))
                                 (dk-fact! 'deriv-sum (cadr r1) (cadr r3) 'tv_
                                           (cadddr r1) (cadddr r3))))
                      (val (cadddr r4)))
                 (have! (list '= dl val)
                   (lambda ()
                     (dk-lam-b!)
                     (fact 'cc-re-add '(* lv (h tv_)) '(* (g tv_) mv))
                     (subst '(= (real-part (+ (* lv (h tv_)) (* (g tv_) mv)))
                                (+ (real-part (* lv (h tv_))) (real-part (* (g tv_) mv)))))
                     (fact 'cc-re-mul 'lv '(h tv_))
                     (fact 'cc-re-mul '(g tv_) 'mv)
                     (subst '(= (real-part (* lv (h tv_)))
                                (- (* (real-part lv) (real-part (h tv_)))
                                   (* (imag-part lv) (imag-part (h tv_))))))
                     (subst '(= (real-part (* (g tv_) mv))
                                (- (* (real-part (g tv_)) (real-part mv))
                                   (* (imag-part (g tv_)) (imag-part mv)))))
                     (crs)))
                 (ccp-finish! lam dl proj (cadr r4) val
                   (lambda ()
                     (di)
                     (fact 'fun-apply-type-c 'g 'RR 'CC 'x_)
                     (fact 'fun-apply-type-c 'h 'RR 'CC 'x_)
                     (fact 'fun-apply-type-c 'pr_ 'RR 'CC 'x_)
                     (ccc-type-coords! '(g x_)) (ccc-type-coords! '(h x_))
                     (ccc-cc-mul! '(g x_) '(h x_))
                     (dk-lam-b!)
                     (inst+ ccp-ptw 'x_)
                     (subst '(= (pr_ x_) (* (g x_) (h x_))))
                     (fact 'cc-re-mul '(g x_) '(h x_))
                     (subst '(= (real-part (* (g x_) (h x_)))
                                (- (* (real-part (g x_)) (real-part (h x_)))
                                   (* (imag-part (g x_)) (imag-part (h x_))))))
                     (have! '(= (- (* (real-part (g x_)) (real-part (h x_)))
                                   (* (imag-part (g x_)) (imag-part (h x_))))
                                (+ (* (real-part (g x_)) (real-part (h x_)))
                                   (* -1 (* (imag-part (g x_)) (imag-part (h x_))))))
                       (lambda () (crs)))
                     (subst '(= (- (* (real-part (g x_)) (real-part (h x_)))
                                   (* (imag-part (g x_)) (imag-part (h x_))))
                                (+ (* (real-part (g x_)) (real-part (h x_)))
                                   (* -1 (* (imag-part (g x_)) (imag-part (h x_)))))))
                     (qrfl))))
               ;; Im(gh) = Re g Im h + Im g Re h
               (let* ((r1 (ccp-prod! ccp-are ccp-bim '(real-part lv) '(imag-part mv)))
                      (r2 (ccp-prod! ccp-aim ccp-bre '(imag-part lv) '(real-part mv)))
                      (r3 (begin (have! (list 'AND r1 r2))
                                 (dk-fact! 'deriv-sum (cadr r1) (cadr r2) 'tv_
                                           (cadddr r1) (cadddr r2))))
                      (val (cadddr r3)))
                 (have! (list '= dl val)
                   (lambda ()
                     (dk-lam-b!)
                     (fact 'cc-im-add '(* lv (h tv_)) '(* (g tv_) mv))
                     (subst '(= (imag-part (+ (* lv (h tv_)) (* (g tv_) mv)))
                                (+ (imag-part (* lv (h tv_))) (imag-part (* (g tv_) mv)))))
                     (fact 'cc-im-mul 'lv '(h tv_))
                     (fact 'cc-im-mul '(g tv_) 'mv)
                     (subst '(= (imag-part (* lv (h tv_)))
                                (+ (* (real-part lv) (imag-part (h tv_)))
                                   (* (imag-part lv) (real-part (h tv_))))))
                     (subst '(= (imag-part (* (g tv_) mv))
                                (+ (* (real-part (g tv_)) (imag-part mv))
                                   (* (imag-part (g tv_)) (real-part mv)))))
                     (crs)))
                 (ccp-finish! lam dl proj (cadr r3) val
                   (lambda ()
                     (di)
                     (fact 'fun-apply-type-c 'g 'RR 'CC 'x_)
                     (fact 'fun-apply-type-c 'h 'RR 'CC 'x_)
                     (fact 'fun-apply-type-c 'pr_ 'RR 'CC 'x_)
                     (ccc-type-coords! '(g x_)) (ccc-type-coords! '(h x_))
                     (ccc-cc-mul! '(g x_) '(h x_))
                     (dk-lam-b!)
                     (inst+ ccp-ptw 'x_)
                     (subst '(= (pr_ x_) (* (g x_) (h x_))))
                     (fact 'cc-im-mul '(g x_) '(h x_))
                     (subst '(= (imag-part (* (g x_) (h x_)))
                                (+ (* (real-part (g x_)) (imag-part (h x_)))
                                   (* (imag-part (g x_)) (real-part (h x_))))))
                     (qrfl))))))))))
(qed 'cc-diff-at-product)
(topic! 'cc-diff-at-product 'analysis)
(alias! 'cc-diff-at-product
  "the product of two differentiable CC-valued functions of a real variable is differentiable, with the Leibniz derivative")
