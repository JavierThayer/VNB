;;; summability.scm -- unconditional summability of a normed-AG-valued function
;;;
;;; For a NORMED-AG grp and a function f : DOM(f) -> (A grp) on an arbitrary
;;; index set DOM(f), SUMS-TO(grp, f, r) says the finite partial sums of f
;;; converge to r in the Moore-Smith sense over the finite subsets of DOM(f)
;;; directed by inclusion:
;;;
;;;   for every eps > 0 there is a finite fin <= DOM(f) such that for EVERY
;;;   finite ext with fin <= ext <= DOM(f),   norm(r - sum(f over ext)) < eps.
;;;
;;; The universal "for every larger ext" is essential.  The weaker
;;; "exists fin close" (r merely a cluster point of partial sums) does NOT
;;; pin r: in RR with f(n) = (-1)^n/(n+1) the finite SUBSET sums are dense,
;;; so every r would qualify and uniqueness would fail.  The net form gives
;;; uniqueness (sums-to-unique below).
;;;
;;; "Unconditional" is automatic and needs no separate clause: the partial
;;; sum is FINSUM over the underlying abelian group, which sums over a finite
;;; SET and never sees an enumeration, so the value cannot depend on order
;;; (finsum-well-defined / sum-ag-permutation-invariance).
;;;
;;; Parameter economy (user's question): the index set is NOT a separate
;;; parameter -- it is DOM(f).  The group grp IS needed and cannot be
;;; dropped: f and r only name elements of a carrier set; the convergence is
;;; measured by grp's norm NRM and operation MUL, which the bare carrier does
;;; not determine.  So the minimal signature is (grp, f, r).
;;;
;;; The difference r - sum is ((MUL grp) r ((INV grp) sum)); since
;;; is-group-norm makes the norm inverse-invariant, norm(r - s) = norm(s - r),
;;; so the order of subtraction is immaterial.
;;;
;;; Dependencies: normed-ag.scm (NORMED-AG, NRM/MUL/INV/A), views.scm
;;; (NORMED-AG-AS-ABELIAN-GROUP), finsum.scm + finsum-well-defined (FINSUM),
;;; order-predicates.scm (POS-RR, <), cardinality (CARD/NN finiteness idiom).

;;; -----------------------------------------------------------------------
;;; SUMS-TO: f sums to r (unconditionally) in grp.

(def-predicate 'SUMS-TO '(grp f r)
  '(FORALL eps
     (IMPLIES (POS-RR eps)
       (FORSOME fin
         (AND (IN fin SET)
              (IN (CARD fin) NN)
              (SUBSET fin (DOM f))
              (FORALL ext
                (IMPLIES (AND (IN ext SET)
                              (IN (CARD ext) NN)
                              (SUBSET fin ext)
                              (SUBSET ext (DOM f)))
                  (< ((NRM grp)
                        ((MUL grp) r
                           ((INV grp)
                              (FINSUM (NORMED-AG-AS-ABELIAN-GROUP grp) f ext))))
                     eps))))))))

;;; -----------------------------------------------------------------------
;;; IS-SUMMABLE: f is summable in grp iff it sums to some r in the carrier.

(def-predicate 'IS-SUMMABLE '(grp f)
  '(FORSOME r (AND (IN r (A grp)) (SUMS-TO grp f r))))

;;; -----------------------------------------------------------------------
;;; IS-ABSOLUTELY-SUMMABLE: the sum of the norms is finite.
;;;
;;; The pointwise-norm function  i |-> NRM_grp(f(i))  carries DOM(f) into RR+*
;;; (each norm is a nonnegative real, so it lands in [0,+inf]).  Its unordered
;;; RR+* sum is exactly the norm series  sum_i ||f(i)||  in [0,+inf].  f is
;;; absolutely summable iff that sum is a real -- i.e. NOT +inf -- which by
;;; esum-finite-iff-bounded means the finite partial norm-sums are bounded
;;; above by some real M.  The inner function gets no name: it is just the
;;; lambda (VNB-LAMBDA i ((NRM grp) (f i))), typed into FUN(DOM f, RR+*) by
;;; pi-lambda-type! + norm-nonnegativity when a proof needs it.
(def-predicate 'IS-ABSOLUTELY-SUMMABLE '(grp f)
  '(IN (ESUM (VNB-LAMBDA i ((NRM grp) (f i)))) RR))

;;; -----------------------------------------------------------------------
;;; Uniqueness: f sums to at most one r.
;;;
;;; Provable from the net definition: given fin1, fin2 witnessing r1, r2 at
;;; eps/2, take ext = fin1 u fin2 (finite); both norm(ri - sum_ext f) < eps/2,
;;; so by the triangle inequality norm(r1 - r2) < eps for every eps, hence
;;; norm(r1 - r2) = 0, hence r1 = r2 by definiteness of the group norm.
;;; Asserted as an axiom for the current library-build phase; a candidate to
;;; promote to a proven theorem / PSS entry later.
(theory-add-axiom! *current-theory* 'sums-to-unique
  '(FORALL grp
     (IMPLIES (IS-NORMED-AG grp)
       (FORALL f
         (IMPLIES (IN f (FUN (DOM f) (A grp)))
           (FORALL r1
             (IMPLIES (IN r1 (A grp))
               (FORALL r2
                 (IMPLIES (IN r2 (A grp))
                   (IMPLIES (AND (SUMS-TO grp f r1) (SUMS-TO grp f r2))
                     (= r1 r2)))))))))))

(warrant! 'sums-to-unique 'informal
  "Given fin1, fin2 witnessing r1, r2 at eps/2, take ext = fin1 u fin2
   (finite, and a superset of each).  Both NRM(ri - sum_ext f) < eps/2, so by
   the triangle inequality NRM(r1 - r2) < eps for every eps, hence
   NRM(r1 - r2) = 0, hence r1 = r2 by definiteness of the group norm
   (is-group-norm).  A candidate to discharge into a formal `proof' later.")
