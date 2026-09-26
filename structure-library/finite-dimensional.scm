;;; finite-dimensional.scm -- finite-dimensional vector spaces, Zorn-free.
;;;
;;; Following the user's plan (no linear algebra needed for the definition):
;;;   * a MODULE is NOETHERIAN if it satisfies the ascending chain condition
;;;     (ACC) on submodules -- every nondecreasing chain of submodules is
;;;     eventually constant;
;;;   * a VECTOR SPACE is a module whose scalars form a field (IS-FIELD-RING
;;;     of the 6-slot scalar ring -- see the declaration below);
;;;   * a vector space is FINITE-DIMENSIONAL iff it is noetherian.
;;;
;;; No basis, no dimension count -- just the chain condition.  This is exactly
;;; what makes Hahn-Banach for finite-dimensional real normed spaces Zorn-free:
;;; one extends a bounded linear functional one dimension higher at a time, and
;;; ACC bounds the iteration.  (Zorn is kept for the general case, later.)
;;;
;;; Builds on module.scm (MODULE/IS-MODULE/SCAL/VEC/VADD/VZERO/VNEG/ACT) and
;;; field.scm (IS-FIELD-RING).  POWER is the kernel powerset former; SUBSET the
;;; kernel subset predicate.  Bound vars carry trailing underscores to dodge
;;; case-fold collisions with the module accessors (per module.scm convention).

;;; A vector space is a module over a field: same shape as MODULE, one more law.
;;;
;;; THE LAW SAYS `is-field-ring', NOT `is-field', AND THE DIFFERENCE IS A DEFECT
;;; THIS FILE CARRIED FROM THE DAY IT WAS WRITTEN UNTIL 2026-08-23.
;;;
;;; `(same-shape-as MODULE)' inherits MODULE's `(substructure SCAL RING)', hence
;;; the conjunct (IS-RING (SCAL s)), and IS-RING pins length(scal(s)) = 6.
;;; IS-FIELD pins the SAME term to 8 -- FIELD is its own 8-slot shape, carrying
;;; NON-ZERO and MUL-INV as data (field.scm).  Six against eight: IS-VECTOR-SPACE
;;; was UNSATISFIABLE, IS-FINITE-DIMENSIONAL below inherited the emptiness, and
;;; every theorem carrying either as a hypothesis was VACUOUSLY true --
;;; hb-good-has-maximal, hahn-banach, norm-as-sup, norm-attained-by-functional,
;;; vector-taylor-remainder-bound, and the two asserted supports
;;; nvs-taylor-remainder-bound and vspace-vec-is-set.  The derivation of falsity
;;; is scratchpad/vs-falsity-probe.scm and the standing check is a must-not-prove
;;; entry (test-suite-negative.scm, section 2d).
;;;
;;; AND THE SAME NUMBER BITES ONE LEVEL UP, which this repair does NOT touch:
;;; IS-VECTOR-SPACE pins length(m) = 6, so IS-FINITE-DIMENSIONAL(m) does too --
;;; and IS-NORMED-VECTOR-SPACE(m) pins it to SEVEN (MODULE's six slots plus
;;; VNRM).  Five results conjoined the two predicates on ONE m and were vacuous
;;; for that second, independent reason: hahn-banach, norm-as-sup,
;;; norm-attained-by-functional, vector-taylor-remainder-bound and
;;; nvs-taylor-remainder-bound.  They now say
;;; IS-FINITE-DIMENSIONAL(NORMED-VECTOR-SPACE-AS-MODULE(m)) -- "finite
;;; dimensional AS A MODULE", which is what was meant.  Nothing in THIS file
;;; changes: the predicate is applied to a different term, not redefined.  The
;;; gate is `statement-satisfiability-audit' (audit.scm), which reads whole
;;; HYPOTHESES rather than one declaration, and follows a def-predicate into its
;;; defining IFF -- the only way this predicate's pin is reachable at all.
;;; Standing check: test-suite-negative.scm section 2e.
;;;
;;; IS-FIELD-RING (field.scm) is fieldhood stated of a SIX-slot ring: a
;;; commutative ring, nontrivial, every nonzero element invertible.  Six against
;;; six.  The alternative repair -- an existential, `forsome fld. is-field(fld)
;;; and scal(s) = field-as-integral-domain(fld)', the shape this morning's
;;; NORMED-VECTOR-SPACE repair took -- was declined for three reasons, in
;;; increasing order of weight: it puts a FORSOME in the defining IFF that every
;;; unfolding proof must skolemize; the satisfiability audit does not descend
;;; into a FORSOME, so the slot's pin would stop being watched; and it DEMANDS an
;;; 8-tuple FIELD instance to exhibit any vector space at all, where the tree has
;;; only QQ-FIELD -- the reals reach the ring world exclusively through
;;; NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD), a 6-tuple, which
;;; IS-FIELD-RING can speak about and IS-FIELD cannot.
(declare-structure VECTOR-SPACE
  (instance-var s)
  (same-shape-as MODULE)
  (law "is-field-ring(scal(s))"))

;;; S is a submodule of m: a subset of the vectors that contains the zero vector
;;; and is closed under vector addition, negation, and the scalar action.
(def-predicate 'IS-SUBMODULE '(m s)
  '(AND (SUBSET s (VEC m))
   (AND (IN (VZERO m) s)
   (AND (FORALL x_ (IMPLIES (IN x_ s)
          (FORALL y_ (IMPLIES (IN y_ s) (IN ((VADD m) x_ y_) s)))))
   (AND (FORALL x_ (IMPLIES (IN x_ s) (IN ((VNEG m) x_) s)))
        (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
          (FORALL x_ (IMPLIES (IN x_ s) (IN ((ACT m) r_ x_) s))))))))))

;;; The four closure conjuncts of IS-SUBMODULE, surfaced as standalone citable
;;; theorems so a proof `fact's each directly instead of unfolding IS-SUBMODULE
;;; (which mac-h would DELETE, taking the hypothesis every other `fact' guarded
;;; on IS-SUBMODULE needs).  Definitional: each is a projection of the IFF above,
;;; exactly as module.scm surfaces module-vadd-type / module-act-type from
;;; IS-MODULE.  submodule-subset is the fifth projection, stamped the same way.
;;; (This comment said until 2026-09-16 that it was "a proven theorem in
;;; submodule-fg-proof.scm"; that file only CITES it.)
(fluid-let ((*current-provenance* 'definitional))
  (add-axiom! *library* 'submodule-subset
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s) (SUBSET s (VEC m))))))
  (add-axiom! *library* 'submodule-vzero-in
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s) (IN (VZERO m) s)))))
  (add-axiom! *library* 'submodule-vadd-closed
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s)
       (FORALL x_ (IMPLIES (IN x_ s)
         (FORALL y_ (IMPLIES (IN y_ s) (IN ((VADD m) x_ y_) s)))))))))
  (add-axiom! *library* 'submodule-vneg-closed
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s)
       (FORALL x_ (IMPLIES (IN x_ s) (IN ((VNEG m) x_) s)))))))
  (add-axiom! *library* 'submodule-act-closed
    '(FORALL m (FORALL s (IMPLIES (IS-SUBMODULE m s)
       (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
         (FORALL x_ (IMPLIES (IN x_ s) (IN ((ACT m) r_ x_) s))))))))))

;;; m is NOETHERIAN: it is a module, and every nondecreasing chain of submodules
;;; f : NN -> POWER(VEC m) is eventually constant (the ascending chain condition).
(def-predicate 'IS-NOETHERIAN '(m)
  '(AND (IS-MODULE m)
     (FORALL f_ (IMPLIES (IN f_ (FUN NN (POWER (VEC m))))
       (IMPLIES (AND (FORALL n_ (IMPLIES (IN n_ NN) (IS-SUBMODULE m (f_ n_))))
                     (FORALL n_ (IMPLIES (IN n_ NN) (SUBSET (f_ n_) (f_ (succ n_))))))
         (FORSOME k_ (AND (IN k_ NN)
            (FORALL n_ (IMPLIES (AND (IN n_ NN) (<= k_ n_))
              (= (f_ n_) (f_ k_)))))))))))

;;; A finite-dimensional vector space is a noetherian vector space.
(def-predicate 'IS-FINITE-DIMENSIONAL '(m)
  '(AND (IS-VECTOR-SPACE m) (IS-NOETHERIAN m)))

;;; A subspace of a (real) vector space is exactly a submodule.
(def-predicate 'IS-SUBSPACE '(m s)
  '(IS-SUBMODULE m s))

;;; SPAN-ADD-ONE(m, s, v) = s + RR.v = { x + r.v : x in s, r in RR }: the
;;; subspace spanned by s together with one more vector v -- the "one dimension
;;; higher" domain of the Hahn-Banach extension step.
(def-functoid 'SPAN-ADD-ONE '(m s v)
  '(SEP y_ (VEC m)
     (FORSOME x_ (AND (IN x_ s)
       (FORSOME r_ (AND (IN r_ RR)
         (= y_ ((VADD m) x_ ((ACT m) r_ v)))))))))

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'IS-SUBMODULE 'kind 'predicate 'arity 2
           'english "$2 is a submodule of $1")
(notation! 'IS-SUBSPACE 'kind 'predicate 'arity 2
           'english "$2 is a subspace of $1")
(notation! 'IS-NOETHERIAN 'kind 'predicate 'arity 1
           'english "$1 is Noetherian")
(notation! 'IS-FINITE-DIMENSIONAL 'kind 'predicate 'arity 1
           'english "$1 is finite dimensional")
