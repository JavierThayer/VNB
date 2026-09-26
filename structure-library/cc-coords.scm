;;; cc-coords.scm -- CC and cartesian(RR, RR), as VOCABULARY.
;;;
;;;   CC-COORDS    z   |-> [real-part(z), imag-part(z)]   : CC -> CARTESIAN(RR,RR)
;;;   CC-OF-PAIR   [a,b] |-> a + b*i                      : CARTESIAN(RR,RR) -> CC
;;;   IS-CC-DIFF-AT(g, a, L)   g : RR -> CC is differentiable at a, derivative L
;;;
;;; Design note: docs/paths-and-line-integrals-2026-09-21.md, section 3.1.
;;; Nothing is proven here; the laws are theorem-library/cc-coords-laws.scm.
;;;
;;; WHY def-constant AND NOT def-functoid.  Both maps take NO parameters: they
;;; are single functions, elements of FUN(CC, CARTESIAN(RR,RR)) and of
;;; FUN(CARTESIAN(RR,RR), CC).  `def-functoid' REFUSES an empty parameter list
;;; (CLAUDE.md, "Where a definition lives"), and before it did it installed the
;;; dead macete (NAME ()) and left the constant uninterpreted -- the RR-BOUNDED-MS
;;; defect of 2026-09-18.  A parameterless defined object is a `def-constant',
;;; which installs the defining equation as a citable THEOREM (definitional, so
;;; it contributes {} to every bill) and registers the head.
;;;
;;; The defining equations are written with `==' (quasi-equality), as CC-MS's and
;;; RR-BOUNDED-MS's are: an unconditional equation introducing a NAME claims no
;;; definedness of its own.
;;;
;;; BINDERS.  `zv_' and `pv_', not `z' / `p': a binder of a term the DRIVER will
;;; rebuild must be spelled like nothing any predicate body binds, or subst-free
;;; renames it and every later `equal?' lookup silently misses (CLAUDE.md,
;;; "Writing proof drivers").  `z' is the binder of real-part-def / imag-part-def
;;; and of most of the CC library; `p' is the binder of half the CARTESIAN
;;; separations in the monoid-algebra files.
;;;
;;; WHERE IT LOADS.  After structure-library/derivative (IS-DIFF-AT) and
;;; structure-library/numeric-instances (RR, RR-MS); CC, real-part, imag-part,
;;; `+i', CARTESIAN, NTH and VNB-LAMBDA are all in number-systems / the kernel.
;;; Nothing below derivative.scm is needed.

;;; -----------------------------------------------------------------------
;;; The two maps.

;;; CC-COORDS : CC -> CARTESIAN(RR, RR).
(def-constant 'CC-COORDS
  (list 'cc-coords-def
        '(== CC-COORDS
             (VNB-LAMBDA zv_ CC (LIST (real-part zv_) (imag-part zv_))))))

;;; CC-OF-PAIR : CARTESIAN(RR, RR) -> CC.  Written a + b*i (and not i*b) to match
;;; cc-generated-by-rr, whose witnesses are `z = x + y * 1i'; cc-re-im-of, the
;;; lemma that identifies the coordinates, has the same shape.
(def-constant 'CC-OF-PAIR
  (list 'cc-of-pair-def
        '(== CC-OF-PAIR
             (VNB-LAMBDA pv_ (CARTESIAN RR RR)
               (+ (NTH 1 pv_) (* (NTH 2 pv_) +i))))))

;;; -----------------------------------------------------------------------
;;; Differentiability of a CC-valued function of a REAL variable.
;;;
;;; WHY A NEW PREDICATE.  The library has three notions of derivative and not
;;; one of them covers a map RR -> CC:
;;;
;;;   * IS-DIFF-AT(f, a, L)          demands f in FUN(RR, RR)  -- codomain wrong.
;;;   * IS-DIFF-ON(K, U, f, a, L)    demands U OPEN in NF-METRIC-SPACE(K) and
;;;                                  f in FUN(U, CARR(K)).  For K = CC-NORMED-FIELD
;;;                                  the domain would have to be an open subset of
;;;                                  CC; RR is a subset of CC (rr-subset-cc) but is
;;;                                  not open in it, so the real line is not a legal
;;;                                  domain.  For K = RR-NORMED-FIELD the codomain
;;;                                  is RR again.
;;;   * IS-DIFF-AT-V(m, f, a, L)     DOES have the right shape -- f in FUN(RR, VEC(m))
;;;                                  for a normed vector space m -- but there is no
;;;                                  instance of NORMED-VECTOR-SPACE on CC in the
;;;                                  tree (the only one is `rr-nvs'), and building
;;;                                  one means a seven-slot structure plus the whole
;;;                                  of IS-NORMED-VECTOR-SPACE.  That is a separate
;;;                                  piece of work, and it is worth doing later:
;;;                                  when CC-NVS exists, `is-cc-diff-at' and
;;;                                  `is-diff-at-v(CC-NVS, ...)' should be proven
;;;                                  equivalent and this predicate kept as the
;;;                                  coordinate presentation.
;;;
;;; So the definition is COORDINATEWISE, which is also exactly the transfer
;;; principle section 3.1 of the design note asks for -- equation (44) of the
;;; user's notes defines the CC-valued integral the same way.  Stating it as the
;;; definition rather than as a theorem makes the equivalence of (c) a one-line
;;; unfolding and leaves the CONTENT in the elementary laws (sum, real multiple,
;;; product), which is where it belongs.
;;;
;;; The parameters are (g a L), mirroring IS-DIFF-AT's (f a L); `a' and `L' are
;;; the binders IS-DIFF-AT already uses, so neither can collide with a class name.
(def-predicate 'IS-CC-DIFF-AT '(g a L)
  '(AND (IN g (FUN RR CC))
   (AND (IN a RR)
   (AND (IN L CC)
   (AND (IS-DIFF-AT (VNB-LAMBDA sv_ RR (real-part (g sv_))) a (real-part L))
        (IS-DIFF-AT (VNB-LAMBDA sv_ RR (imag-part (g sv_))) a (imag-part L)))))))

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of the predicate, read by wff->english and the proof
;;; reader (operators.scm).  A def-predicate's reading cannot be derived, so it
;;; is written here, beside what it means.
(notation! 'IS-CC-DIFF-AT 'kind 'predicate 'arity 3
           'english "$1 is differentiable at $2 as a complex-valued function of a real variable, with derivative $3")
