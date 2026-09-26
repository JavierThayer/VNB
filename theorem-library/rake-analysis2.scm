;;; rake-analysis2.scm -- rake batch L (2026-09-17): five asserted leaves of the
;;; analysis / sets area, plus the general lemma that unblocked one of them.
;;;
;;;   fun-domain-in-set            NEW.  f in FUN(A,B)  =>  A in SET
;;;   bijection-compose            the composite of two bijections is a bijection
;;;                                (structure-library/bijection.scm:123, an AXIOM)
;;;   subseq-is-fun                a subsequence of an PTS(s)-sequence is one
;;;                                (theorem-library/cauchy-subsequence.scm:106)
;;;   metric-hom-is-continuous     an isometry is continuous (delta = eps)
;;;                                (structure-library/metric-continuity.scm:139)
;;;   le-bound-mono                p <= a*n, a <= b, 0 <= n  =>  p <= b*n
;;;                                (theorem-library/hahn-banach-full-proof.scm:138)
;;;   centre-set-contains-choice   the chosen centre of a ball of the family is in
;;;                                CENTRE-SET -- RE-STATED WITH A GUARD, because the
;;;                                support it replaces (structure-library/
;;;                                compactness.scm:159) was UNDERDETERMINED; see below.
;;;
;;; Every statement but the last is copied LITERALLY from its site.  The last is the
;;; guarded RE-STATEMENT, installed under the original name by the integrator's
;;; decision of 2026-09-17; the support is retired and its one citer is repaired.
;;;
;;; ---------------------------------------------------------------------------
;;; fun-domain-in-set -- WHY IT IS HERE, AND WHY THE TREE LACKED IT
;;;
;;; `bijection-compose' concludes that a VNB-LAMBDA over X lies in BIJECTION(X,Z),
;;; and the ONLY route to a lambda's FUN-membership is the kernel rule `lam-t',
;;; which owes (IN X SET).  Nothing in the tree derived that from the hypothesis
;;; `phi in BIJECTION(X,Y)': `fun-set-iff' runs the other way, `dom-of-fun' already
;;; assumes (IN A SET), and FUN(A) over a proper class A is deliberately allowed to
;;; be inhabited (library.scm's fun-no-junk note).  So the axiom looked as though it
;;; needed a sethood GUARD.  It does not.  A member of a class is a set
;;; (membership-implies-sethood), so f is a set; `fun-no-junk' says f IS its graph;
;;; hence A embeds in the first-coordinate image of f, which is a set by replacement
;;; (image-set).  `subclass-of-set-is-set' finishes.  The lemma is general and
;;; belongs beside dom-of-fun; it is proven here because this is where it was needed.
;;;
;;; ---------------------------------------------------------------------------
;;; centre-set-contains-choice WAS UNDERDETERMINED, and now carries a GUARD.
;;;
;;;   forall s, r, F, U.  U in F  =>  CHOICE(CENTRES(s,U,r)) in CENTRE-SET(s,r,F)
;;;
;;; CENTRE-SET(s,r,F) is IMAGE(B |-> CHOICE(CENTRES s B r), F), so by
;;; image-membership-iff the conclusion needs the EQUATION
;;; (B |-> ...)(U) = CHOICE(CENTRES s U r) -- and `=' in VNB is the definedness
;;; predicate, so it asserts that CHOICE(CENTRES s U r) DENOTES.  `choice-axiom'
;;; (library.scm) defines CHOICE only on an inhabited class, and the statement puts
;;; no condition whatever on U: at any U in F that is not an r-ball of s at all --
;;; F = {EMPTY-SET}, U = EMPTY-SET, r > 0 -- CENTRES(s,U,r) is empty and the term is
;;; unspecified.  Nothing REFUTES the statement (CHOICE of the empty class is
;;; unspecified, not required to be undefined); it is underdetermined, exactly as
;;; `ball-mem-from-le' was before it was guarded (rake-balls.scm's header).
;;; The proof below therefore carries the weakest guard that does the job --
;;; CENTRES(s,U,r) is inhabited -- under the name `centre-set-contains-choice'.
;;; The guard was FREE at the one call site, and that repair is DONE (2026-09-17):
;;; calculus/finite-ball-subcover-proof.scm reached the citation with the chosen
;;; centre already in PTS(s) and BALL(.,r) = u* -- `chosen-centre-is-centre', four
;;; lines above it -- which is exactly `centres-mem-build''s pair of premises, so
;;; three lines exhibit the centre and land the conjunction.  That proof's bill did
;;; not merely survive the guard: it went from
;;;   modulo {centre-set-contains-choice} [trust: well-known]   to   modulo 0.
;;; LOAD CONSEQUENCE: finite-ball-subcover-proof is at table position 252, so this
;;; file must load BELOW 252.
;;;
;;; ---------------------------------------------------------------------------
;;; PROOFS, one line each.
;;;   fun-domain-in-set   above.
;;;   bijection-compose   bijection-membership-iff on both hypotheses and on the
;;;     goal; the FUN typing by `lam-t' (sethood from fun-domain-in-set) plus
;;;     fun-apply-type-c twice; injectivity by `lam-b-h' on the landed equation then
;;;     psi's and phi's injectivity in turn; surjectivity by psi's then phi's, and
;;;     one `lam-b' + `subst'.
;;;   subseq-is-fun       `mac' the SUBSEQ functoid, `dk-lam-t!', fun-apply-type-c
;;;     twice.  phi's typing comes off the STRICTLY-MONO-NN unfold.
;;;   metric-hom-is-continuous  unfold the generated hom (is-hom-metric-space-def);
;;;     delta := eps, and the isometry equation rewrites the target distance into the
;;;     source distance the hypothesis already bounds.
;;;   le-bound-mono       0 <= b - a, rr-leq-mul-nonneg at (b-a, n), `crs' for
;;;     (b*n - a*n) = (b-a)*n, one Farkas call.  EVERY typing must be landed BEFORE
;;;     the `fact' that needs it: rr-mul-closed's antecedent is a CONJUNCTION, which
;;;     `fact' will not split, so each product wants a `have!' of the AND first --
;;;     without it the implication lands silently and the oracle then refuses the
;;;     goal for want of an (IN (* a n) RR) certificate, blaming the goal.
;;;   centre-set-contains-choice  choice-axiom, image-membership-iff, `lam-b',
;;;     `rfl' (which is licensed exactly by the choice membership the guard buys).
;;;
;;; CITATIONS, with the 0-based load position of the file that installs each:
;;;   primitive/base (library.scm, number-systems.scm, cardinality.scm): choice-axiom,
;;;     class membership (membership-implies-sethood), fun-codomain-iff, fun-no-junk,
;;;     subset-def, rr-leq-mul-nonneg, rr-mul-closed.
;;;   definitional: the IS-X / functoid unfolds (is-hom-metric-space-def 45,
;;;     strictly-mono-nn + SUBSEQ 90, CENTRES + CENTRE-SET 48, bijection-membership-iff 81).
;;;   proven: image-set + image-membership-iff 83 (structure-library/injection),
;;;     eq-sym 148 (equality-basics), rr-sub-in-rr 162 (binary-minus-laws),
;;;     fun-apply-type-c 163 (fun-apply-type-proof), pair-in-cartesian 165
;;;     (pair-tuple-sethood), subclass-of-set-is-set 193 (subset-lemmas).
;;;   oracles: ineq, crs.
;;;
;;; LOAD WINDOW [194, 252).
;;;   lo = 194: subset-lemmas (193) is the latest citation.
;;;   hi = 252: calculus/finite-ball-subcover-proof, which now cites the GUARDED
;;;     centre-set-contains-choice.  (Its own ceiling, theorem-library/card-finite
;;;     at 259, cites bijection-compose at its line 156 and would have given [194,
;;;     259) had that repair not been made.)
;;;     The other citers are further down: cauchy-subseq-proof 269 (subseq-is-fun),
;;;     hahn-banach-full-proof 450 (le-bound-mono, an add-to-pss in its own head),
;;;     metric-top-functorial-proof 474 (metric-hom-is-continuous).
;;;   continuous-implies-open-preimage, the sixth leaf of this batch, does NOT fit
;;;   here -- it cites ball-membership / ball-mem-from-le (rake-balls, 261) -- and is
;;;   in theorem-library/rake-cont-preimage.scm, window [262, 279).
;;;
;;; Helper prefix: rkl-.

;;; --- file-local helpers (rkl-) -------------------------------------------

(define (rkl-head? f h) (and (pair? f) (eq? (car f) h)))
(define (rkl-in? f set) (and (rkl-head? f 'IN) (equal? (caddr f) set)))

;; 1-based context index of FORM, for `ineq' (ineq-oracle.scm:206).  Named by
;; FORMULA, never by shape: a set equation is `='-headed and poisons the oracle.
(define (rkl-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rkl-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (rkl-ineq* . fs) (apply ineq (map rkl-idx fs)))

;; the in-context guarded universal whose guard ranges over SET and whose
;; consequent has head INNER.  Four of bijection-membership-iff's universals are
;; in context at once and two of them share a guard, so BOTH keys are needed.
(define (rkl-univ set inner what)
  (dk-pick (lambda (p)
             (and (rkl-head? p 'FORALL) (rkl-head? (caddr p) 'IMPLIES)
                  (rkl-in? (cadr (caddr p)) set)
                  (rkl-head? (caddr (caddr p)) inner)))
           what))

;;; =====================================================================
;;; fun-domain-in-set -- the domain of a set-function is a set
;;; =====================================================================

(define rkl-dlam '(VNB-LAMBDA z_ f (NTH 1 z_)))

(sp (make-wff '(FORALL A (FORALL B (FORALL f
     (IMPLIES (IN f (FUN A B)) (IN A SET)))))))
(dk-peel!)
(dk-split! (dk-landed-1 (lambda () (mac-h 'fun-codomain-iff '(IN f (FUN a b))))))
;; capture the pointwise typing universal BEFORE any `fact': a citation lands its
;; whole instantiation chain, and image-set's own guarded universal matches too.
(define rkl-ptw
  (dk-pick (lambda (p) (and (rkl-head? p 'FORALL) (rkl-head? (caddr p) 'IMPLIES)))
           "the pointwise typing universal of f"))
(fact 'membership-implies-sethood 'f '(FUN a))
(fact 'image-set rkl-dlam 'f)
(have! (list 'SUBSET 'a (list 'IMAGE rkl-dlam 'f))
  (lambda ()
    (mac 'subset-def)
    (let* ((mem (dk-landed-1 (lambda () (di))))
           (w   (cadr mem))
           (pr  (list 'LIST w (list 'f w)))
           (ig  (list 'FORSOME 'x_ (list 'FORSOME 'y_
                      (list 'AND (list '= pr (list 'LIST 'x_ 'y_))
                            (list 'AND (list 'IN 'x_ 'a) (list '= (list 'f 'x_) 'y_)))))))
      (dk-apply! rkl-ptw w)                       ; (IN (f w) b)
      ;; the pair is a MEMBER of a cartesian product, which is what licenses the
      ;; `rfl' below: LIST is a total head but (f w) is not self-defined.
      (fact 'pair-in-cartesian 'a 'b w (list 'f w))
      (let* ((nj   (dk-fact! 'fun-no-junk 'a 'f))
             (ifff (dk-apply! nj pr)))
        (have! ig
          (lambda ()
            (ew w) (ew (list 'f w))
            (dk-conj-close! (lambda () (if (rkl-head? (dk-goal) '=) (rfl) (ass))))))
        (dk-only! ifff ig mem)                    ; prop has an atom cap
        (have! (list 'IN pr 'f) (lambda () (prop))))
      (mac 'image-membership-iff)
      (ew pr)
      (dk-conj-close!
       (lambda ()
         (if (rkl-head? (dk-goal) 'IN) (ass) (begin (lam-b) (nth-r) (rfl))))))))
(fact 'subclass-of-set-is-set 'a (list 'IMAGE rkl-dlam 'f))
(ass)
(qed 'fun-domain-in-set)
(gloss! 'fun-domain-in-set
  "The domain of a function that lies in FUN(A,B) is a set.  A member of a class
   is a set, a function IS its graph (fun-no-junk), and the first coordinates of a
   set are a set by replacement -- so the sethood a VNB-LAMBDA's typing rule owes
   can be read off any function already typed over the same domain.")
(topic! 'fun-domain-in-set 'plumbing)

;;; =====================================================================
;;; bijection-compose
;;; =====================================================================

(sp (make-wff '(FORALL X (FORALL Y (FORALL Z (FORALL phi (FORALL psi
      (IMPLIES (AND (IN phi (BIJECTION X Y))
                    (IN psi (BIJECTION Y Z)))
               (IN (VNB-LAMBDA x_ X (psi (phi x_)))
                   (BIJECTION X Z))))))))))
(dk-peel!)
(dk-split! '(AND (IN phi (BIJECTION x y)) (IN psi (BIJECTION y z))))
(dk-split! (dk-landed-1
            (lambda () (mac-h 'bijection-membership-iff '(IN phi (BIJECTION x y))))))
(dk-split! (dk-landed-1
            (lambda () (mac-h 'bijection-membership-iff '(IN psi (BIJECTION y z))))))
(define rkl-phi-inj  (rkl-univ 'x 'FORALL  "phi injective"))
(define rkl-phi-surj (rkl-univ 'y 'FORSOME "phi surjective"))
(define rkl-psi-inj  (rkl-univ 'y 'FORALL  "psi injective"))
(define rkl-psi-surj (rkl-univ 'z 'FORSOME "psi surjective"))
(fact 'fun-domain-in-set 'x 'y 'phi)              ; (IN x SET), for lam-t

(define (rkl-comp-fun!)
  (dk-lam-t!)
  (let ((a (dk-di-var!)))
    (fact 'fun-apply-type-c 'phi 'x 'y a)
    (fact 'fun-apply-type-c 'psi 'y 'z (list 'phi a))
    (ass)))

(define (rkl-comp-inj!)
  (let* ((landed (dk-peel!))
         (eqn (or (find-first (lambda (q) (rkl-head? q '=)) landed)
                  (error "bijection-compose: no lambda equation landed"
                         (map expression->string landed))))
         (a (cadr (cadr eqn)))
         (b (cadr (caddr eqn))))
    (lam-b-h eqn)                                  ; psi(phi a) = psi(phi b)
    (fact 'fun-apply-type-c 'phi 'x 'y a)
    (fact 'fun-apply-type-c 'phi 'x 'y b)
    (dk-apply! rkl-psi-inj (list 'phi a) (list 'phi b))
    (dk-apply! rkl-phi-inj a b)
    (ass)))

(define (rkl-comp-surj!)
  (let* ((mem (car (dk-peel!)))                    ; (IN w z)
         (w   (cadr mem))
         (v   (dk-skolem! (dk-apply! rkl-psi-surj w)))
         (u   (dk-skolem! (dk-apply! rkl-phi-surj v))))
    (ew u)
    (dk-conj-close!
     (lambda ()
       (if (rkl-head? (dk-goal) 'IN)
           (ass)
           (begin (lam-b) (subst (list '= (list 'phi u) v)) (ass)))))))

(mac 'bijection-membership-iff)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((rkl-head? g 'IN) (rkl-comp-fun!))
           ((rkl-head? (caddr (caddr g)) 'FORALL) (rkl-comp-inj!))
           (#t (rkl-comp-surj!))))))
(qed 'bijection-compose)
(gloss! 'bijection-compose
  "The composite x |-> psi(phi x) of a bijection X -> Y and a bijection Y -> Z is a
   bijection X -> Z.  Was an axiom of structure-library/bijection.scm.")
(topic! 'bijection-compose 'plumbing)

;;; =====================================================================
;;; subseq-is-fun
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL f (FORALL phi
     (IMPLIES (AND (IN f (FUN NN (PTS s))) (STRICTLY-MONO-NN phi))
              (IN (SUBSEQ f phi) (FUN NN (PTS s)))))))))
(dk-peel!)
(dk-split! '(AND (IN f (FUN NN (PTS s))) (STRICTLY-MONO-NN phi)))
(dk-split! (dk-landed-1 (lambda () (mac-h 'strictly-mono-nn '(STRICTLY-MONO-NN phi)))))
(mac 'SUBSEQ)
(dk-lam-t!)                                        ; the NN-sethood leaf goes with it
(define rkl-k (dk-di-var!))
(fact 'fun-apply-type-c 'phi 'NN 'NN rkl-k)
(fact 'fun-apply-type-c 'f 'NN '(PTS s) (list 'phi rkl-k))
(ass)
(qed 'subseq-is-fun)
(gloss! 'subseq-is-fun
  "A subsequence SUBSEQ(f, phi) = k |-> f(phi k) of a sequence in PTS(s), reindexed
   by a strictly monotone phi : NN -> NN, is again a sequence in PTS(s).")
(topic! 'subseq-is-fun 'analysis)

;;; =====================================================================
;;; metric-hom-is-continuous
;;; =====================================================================

(sp (make-wff (forall-guarded '(s t f) '((IS-HOM-METRIC-SPACE s t f))
                              '(IS-CONTINUOUS s t f))))
(dk-peel!)
(dk-split! (dk-landed-1
            (lambda () (mac-h 'is-hom-metric-space-def '(IS-HOM-METRIC-SPACE s t f)))))
(define rkl-iso
  (dk-pick (lambda (a) (and (rkl-head? a 'FORALL) (rkl-head? (caddr a) 'IMPLIES)
                            (rkl-in? (cadr (caddr a)) '(PTS s))))
           "the isometry universal"))

;; goal (<= ((DIST t) (f a) (f b)) eps), with (<= ((DIST s) a b) eps) in context.
(define (rkl-iso-close! a b)
  (let ((eqn (dk-apply! rkl-iso a b)))             ; d(s)(a,b) = d(t)(f a, f b)
    (fact 'eq-sym (cadr eqn) (caddr eqn))
    (subst (list '= (caddr eqn) (cadr eqn)))
    (ass)))

(mac 'is-continuous)
(dk-conj-close!
 (lambda ()
   (if (not (rkl-head? (dk-goal) 'FORALL))
       (ass)
       (let ((a (dk-di-var!)))
         (mac 'is-continuous-at)
         (dk-conj-close!
          (lambda ()
            (if (not (rkl-head? (dk-goal) 'FORALL))
                (ass)
                (let ((eps (cadr (car (dk-peel!)))))    ; landed (POS-RR eps)
                  (ew eps)                              ; delta := eps
                  (dk-conj-close!
                   (lambda ()
                     (if (rkl-head? (dk-goal) 'POS-RR)
                         (ass)
                         (let ((b (dk-di-var!)))
                           (dk-peel!)
                           (rkl-iso-close! a b)))))))))))))
(qed 'metric-hom-is-continuous)
(gloss! 'metric-hom-is-continuous
  "An isometry between metric spaces is continuous: delta = eps works at every
   point, because the map preserves distance exactly.")
(topic! 'metric-hom-is-continuous 'topology)

;;; =====================================================================
;;; le-bound-mono
;;; =====================================================================

(sp (make-wff '(FORALL p (FORALL a (FORALL b (FORALL n
     (IMPLIES (IN p RR) (IMPLIES (IN a RR) (IMPLIES (IN b RR) (IMPLIES (IN n RR)
       (IMPLIES (<= 0 n) (IMPLIES (<= p (* a n)) (IMPLIES (<= a b)
        (<= p (* b n)))))))))))))))
(dk-peel!)
(fact 'rr-sub-in-rr 'b 'a)
;; rr-mul-closed's antecedent is a CONJUNCTION; `fact' will not split one, so the
;; AND must be in context FIRST or the implication lands and the typing does not.
(have! '(AND (IN a RR) (IN n RR)))
(fact 'rr-mul-closed 'a 'n)
(have! '(AND (IN b RR) (IN n RR)))
(fact 'rr-mul-closed 'b 'n)
(have! '(<= 0 (- b a)) (lambda () (rkl-ineq* '(<= a b))))
(have! '(AND (IN (- b a) RR) (IN n RR)))
(fact 'rr-mul-closed '(- b a) 'n)
(have! '(AND (<= 0 (- b a)) (<= 0 n)))
(fact 'rr-leq-mul-nonneg '(- b a) 'n)
(have! '(= (- (* b n) (* a n)) (* (- b a) n)) (lambda () (crs)))
(rkl-ineq* '(<= 0 (* (- b a) n))
           '(= (- (* b n) (* a n)) (* (- b a) n))
           '(<= p (* a n)))
(qed 'le-bound-mono)
(gloss! 'le-bound-mono
  "Reals: p <= a*n, a <= b and 0 <= n give p <= b*n.  The monotone-compose step of
   the bounded-functional estimates.")
(topic! 'le-bound-mono 'analysis)

;;; =====================================================================
;;; centre-set-contains-choice -- GUARDED (the unguarded support at
;;; structure-library/compactness.scm:159 was UNDERDETERMINED; see the header)
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL r (FORALL F (FORALL U
     (IMPLIES (AND (IN U F) (FORSOME c (IN c (CENTRES s U r))))
       (IN (CHOICE (CENTRES s U r)) (CENTRE-SET s r F)))))))))
(dk-peel!)
(dk-split! '(AND (IN u f) (FORSOME c (IN c (CENTRES s u r)))))
;; 2026-09-18 (LUTINS instantiation): `fact choice-axiom' at CENTRES(s,u,r)
;; owes its definedness.  The functoid body is SEP over PTS(s) and `s' carries
;; NO structure hypothesis here, so the certificate refuses it.  Skolemizing
;; the guard first lands the atomic `IN c_ (CENTRES s u r)', in which the term
;; occurs outside every binder -- the strictness certificate -- so the
;; instantiation owes nothing.  The FORSOME stays in context for the detach.
(let ((c0 (dk-skolem! '(FORSOME c (IN c (CENTRES s u r))))))
  ;; `ai' REPLACES the existential it opens, and `fact' detaches against it,
  ;; so put the guard back from the eigenvariable before citing choice-axiom.
  (have! '(FORSOME c (IN c (CENTRES s u r))) (lambda () (ew c0) (ass))))
(fact 'choice-axiom '(CENTRES s u r))    ; the guard IS choice-axiom's antecedent
(mac 'CENTRE-SET)
(mac 'image-membership-iff)
(ew 'u)
(dk-conj-close!
 (lambda ()
   (if (rkl-head? (dk-goal) 'IN)
       (ass)
       (begin (lam-b) (rfl)))))          ; rfl is licensed by the choice membership
(qed 'centre-set-contains-choice)
(gloss! 'centre-set-contains-choice
  "The chosen centre of U is in CENTRE-SET(s,r,F) when U is in F AND U has a centre
   at radius r.  The second hypothesis is what makes CHOICE(CENTRES(s,U,r)) denote;
   without it the conclusion asserts the definedness of an unspecified term.")
(topic! 'centre-set-contains-choice 'topology)
