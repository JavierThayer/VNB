;;; order-predicates.scm -- derived order predicates on the kernel <=.
;;;
;;; The kernel has <= as a primitive predicate but no strict <, and the
;;; "eps > 0 for eps in RR" idiom (used pervasively in analytic axioms
;;; like cc-complete) is verbose:
;;;
;;;   (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
;;;
;;; Two named definitions so future axioms (and proofs) read cleanly:
;;;
;;;   (< x y)       <=>  (AND (<= x y) (NOT (= x y)))
;;;   (POS-RR r)    <=>  (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
;;;
;;; Existing axioms keep the verbose form (opt-in retrofit deferred).
;;; See [[feedback-no-closure-axiom-proliferation]] -- these are
;;; definitional, not closure axioms, so they pass the bar.
;;;
;;; Not extended to arith-eval: ground decisions on `<` still go through
;;; the unfold via the iff.  A future pass may dispatch arith-eval on
;;; `<` directly.
;;; RETIRED 2026-09-14 (proven): nn-unbounded-in-rr -- theorem-library/nn-unbounded-in-rr.scm
;;; RETIRED 2026-09-14 (proven): nn-recip-succ-small -- theorem-library/nn-recip-succ-small.scm

(def-predicate '< '(x y)
  '(AND (<= x y) (NOT (= x y))))

(def-predicate 'POS-RR '(r)
  '(AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r)))))

;;; --------------------------------------------------------------------
;;; The "eps can shrink" facts of the real line.  The static order axioms
;;; (rr-leq-reflexive/antisym/transitive/total/add-compat/mul-nonneg in
;;; number-systems.scm) say nothing about positive reals having no floor --
;;; yet every eps-argument in analysis (uniqueness of limits, convergent =>
;;; Cauchy, limit arithmetic) bottoms out on exactly that.  The first three
;;; below are the order-density face of that gap; the last two (added
;;; 2026-08-01) are the archimedean face proper.  All five are accepted as
;;; warranted PSS supports rather than asserted from a deeper RR
;;; axiomatisation.
;;;
;;; WHY THEY ARE ASSERTED, and what changed the same day.  When these five were
;;; written, number-systems.scm axiomatised RR as an ORDERED FIELD and stopped:
;;; no least-upper-bound axiom, no nested intervals, no completeness of any kind,
;;; despite the section header calling RR a "complete ordered field".  Every
;;; ordered field satisfied those axioms, including non-archimedean ones (the
;;; rational functions ordered at infinity), so the archimedean property was
;;; INDEPENDENT of what was written down.
;;;
;;; Later on 2026-08-01 that gap was closed: number-systems.scm now carries
;;; rr-sup-in / rr-sup-upper / rr-sup-least (order completeness, SUP).  So all
;;; five facts below are now DERIVABLE, and each is a theorem waiting for a
;;; driver rather than a permanent assertion:
;;;
;;;   nn-unbounded-in-rr   if NN were bounded above, s = SUP(NN) exists; s - 1 is
;;;                        not an upper bound, so n > s - 1 for some n, so
;;;                        n + 1 > s with n + 1 in NN.  Contradiction.
;;;   nn-recip-succ-*      the reciprocal reading of that, see their warrants.
;;;   rr-le-all-pos-nonpos ) consequences of archimedean plus the ordered-field
;;;   rr-pos-halvable      ) axioms; halvable and shrink need only the field
;;;   rr-pos-shrink        ) axioms (eps * recip(1+1)), not completeness at all.
;;;
;;; Only `nn-unbounded-in-rr' has had its tier moved to `informal' to match (a
;;; rigorous paper proof now exists from the axioms present, which is what
;;; `informal' means).  The other four are left at `well-known' deliberately:
;;; re-tiering a fact moves the reported trust of every bill that cites it, and
;;; that is a ledger decision, not a drive-by edit.

;;; rr-le-all-pos-nonpos MOVED 2026-08-31 to theorem-library/rr-le-all-pos.scm,
;;; where it is PROVEN `modulo 0' -- a real below every positive real is
;;; non-positive, by halving.  It stood here as a `well-known' support, and the
;;; list above already said it was derivable.  What it was waiting for was not
;;; an axiom but `rr-pos-halvable' (rr-halving.scm, proven 2026-08-17): if x
;;; were positive it would be <= its own half, which is a contradiction in the
;;; ordered field alone -- completeness is not used, so the "archimedean face
;;; of completeness" reading in the list above overstates what the fact costs.
;;; The statement it had is reproduced verbatim there, so every citer is
;;; unaffected.  It was the SOLE asserted leaf of 20 bills, the largest single
;;; leaf in the library at the time it was proven.

;;; rr-pos-halvable MOVED 2026-08-17 to theorem-library/rr-halving.scm, where it
;;; is PROVEN `modulo 0' -- every positive real splits into two equal positive
;;; halves, witness eps * recip(1+1).  It stood here as a `well-known' support,
;;; and the list above already said it was derivable ("halvable and shrink need
;;; only the field axioms (eps * recip(1+1)), not completeness at all").  What
;;; it was waiting for was not an axiom but rr-mul-pos / rr-recip-pos
;;; (theorem-library/rr-recip-order.scm, 2026-08-04): nothing in the tree said a
;;; reciprocal of a positive is positive.  The statement it had is reproduced
;;; verbatim there, so every citer is unaffected.

;;; Below every positive real sits a smaller positive real.  The form the
;;; continuity / open-preimage argument actually wants: openness of V gives a
;;; STRICT eps-ball, but continuity only yields a non-strict bound d(.,.) <= d;
;;; instantiating continuity at a d < eps (this lemma) makes the non-strict
;;; bound land strictly inside the eps-ball (cf. ball-mem-from-le).  The strict
;;; sibling of rr-pos-halvable (take d = eps/2; eps/2 < eps).
;;; rr-pos-shrink RETIRED 2026-09-18 (rake batch 5): proven modulo 0 in theorem-library/rake-inequalities.scm

;;; --------------------------------------------------------------------
;;; The archimedean property (added 2026-08-01).
;;;
;;; WHY IT IS HERE.  `compact-metric-is-separable' (separable.scm) is a
;;; warranted support whose route is "for each n take a finite 1/(n+1)-net; the
;;; union is dense".  Density needs, for a given eps > 0, an n with
;;; 1/(n+1) < eps.  Nothing in the tree said that: the three facts above are
;;; RR-only and never mention NN, and nothing else relates the two sets by
;;; SIZE (nn-in-rr, order-lemmas.scm:39, embeds NN in RR and says nothing
;;; about magnitude).  The only thing that came close was
;;; `null-rr-seq-exists' (cauchy-subsequence.scm:127), which asserts a
;;; positive null SEQUENCE exists -- serviceable, but it hides the
;;; archimedean content inside an existential over sequences instead of
;;; naming it, and it cannot be used to talk about 1/(n+1) specifically.
;;;
;;; SPELLING.  The radius is written `(recip (+ n 1))', NOT `(/ 1 (+ n 1))'.
;;; `/' is SURFACE SYNTAX ONLY: parser.scm:278-293 desugars the infix x / y to
;;; (* x (recip y)), and `recip' is what number-systems.scm axiomatises
;;; (rr-recip-closed :273, rr-recip-inverse :278) and what arith-eval.scm:53
;;; evaluates.  A quoted s-expression `(/ a b)' written directly in Scheme
;;; source bypasses the parser and leaves the head `/', which no axiom and no
;;; evaluator rule mentions.  (Several existing supports do exactly that --
;;; bdd-fn-nonneg/lt-one/le-arg in scalar-inequalities.scm, the weights in
;;; product-metric.scm:61,145, young-inequality in real-powers.scm:180 -- so
;;; they are about an uninterpreted binary operator.  Not unsound, but no
;;; proof can connect them to recip.  Recorded, not fixed here.)

;;; The reciprocal reading, in the two pieces a net argument consumes.  Kept
;;; SEPARATE because the consumer uses them at different moments: positivity is
;;; needed to instantiate TOTALLY-BOUNDED at scale n (its radius condition is
;;; "r in RR, 0 <= r, r /= 0" -- compactness.scm:113 -- i.e. POS-RR unfolded),
;;; and that happens for EVERY n, before any eps is in play; smallness is needed
;;; later, once eps is given.  Folding them into one conjunction would force the
;;; driver to produce an eps it does not yet have.
;;; nn-recip-succ-pos MOVED 2026-09-02 to theorem-library/pos-rr-of-lt.scm,
;;; where it is PROVEN `modulo 0' as a four-line instance of the general bridge
;;; `rr-pos-rr-of-lt' (0 < x implies POS-RR(x)) -- which the tree did not have,
;;; and whose absence is why this was asserted.  The retired warrant ended "Not
;;; mechanised: it needs recip-order lemmas the tree does not have yet"; the
;;; tree has had them since theorem-library/rr-recip-order.scm (`rr-recip-pos'
;;; is the lemma it names) and nothing went back to collect.  Statement
;;; unchanged, so every citer sees the formula it always saw.


;;; --------------------------------------------------------------------
;;; QQ is dense in RR (item (c) of the 2026-08-01 arithmetic-base cleanup).
;;;
;;; SITED HERE, not in number-systems.scm with the other base axioms, for one
;;; reason: it is naturally stated with STRICT inequalities and a positive eps,
;;; and neither `<' nor `POS-RR' exists until this file defines them at the top.
;;; number-systems.scm is load.scm:110, this file is :124.  The alternative --
;;; spelling both out as (AND (<= u v) (NOT (= u v))) up there -- would state the
;;; axiom in a form no consumer writes, and every citation would need a macete
;;; step to reach it.  The head comment of number-systems.scm's completeness
;;; block records that this axiom lives here.
;;;
;;; Approximation form, per the user's spelling: every real is caught within any
;;; positive tolerance by a rational.  Equivalent to the between-two-reals form
;;; given archimedean, and equivalent to a nested-rational-interval form given a
;;; null sequence of tolerances (nn-recip-succ-small supplies one).
;;;
;;; DERIVABLE, like everything else in this file: with order completeness
;;; (rr-sup-in/upper/least), qq-is-fraction and zz-generated-by-nn it is the
;;; standard argument -- take n with 1/n < eps (archimedean), then the least
;;; integer m with m/n > x - eps.  Asserted because that argument is not
;;; mechanised, not because it is unavailable.
(add-axiom! *library* 'qq-dense-in-rr
  (forall-guarded '(eps x)
    (list '(POS-RR eps) '(IN x RR))
    (forsome-guarded 'a '(IN a QQ)
      (conjuncts->and
        (list '(< (- a eps) x)
              '(< x (+ a eps)))))))
(warrant! 'qq-dense-in-rr 'reference
  "QQ is dense in RR: for every real x and every positive eps there is a
   rational a with a - eps < x < a + eps.  Standard; derivable from order
   completeness plus the fraction and generation axioms, not yet mechanised.")
(topic! 'qq-dense-in-rr 'inequalities)
(rests-on 'qq-dense-in-rr '(nn-unbounded-in-rr))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'POS-RR                'kind 'predicate 'arity 1 'noun "positive real" 'article "a")
(notation! 'NEG-RR                'kind 'predicate 'arity 1 'noun "negative real" 'article "a")
(notation! 'NONNEG-RR             'kind 'predicate 'arity 1 'noun "nonnegative real" 'article "a")
