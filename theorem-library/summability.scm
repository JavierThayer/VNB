;;; summability.scm -- unconditional summability of a normed-AG-valued function
;;;
;;; For a NORMED-AG grp and a function f : DOM(f) -> (CARR grp) on an arbitrary
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
;;; The difference r - sum is ((OPR grp) r ((INV grp) sum)); since
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
         (AND (IN fin SET) (AND (IN (CARD fin) NN) (AND (SUBSET fin (DOM f)) (FORALL ext
                (IMPLIES (AND (IN ext SET) (AND (IN (CARD ext) NN) (AND (SUBSET fin ext) (SUBSET ext (DOM f)))))
                  (< ((NRM grp)
                        ((OPR grp) r
                           ((INV grp)
                              (FINSUM (NORMED-AG-AS-ABELIAN-GROUP grp) f ext))))
                     eps))))))))))

;;; -----------------------------------------------------------------------
;;; IS-SUMMABLE: f is summable in grp iff it sums to some r in the carrier.

(def-predicate 'IS-SUMMABLE '(grp f)
  '(FORSOME r (AND (IN r (CARR grp)) (SUMS-TO grp f r))))

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
         (IMPLIES (IN f (FUN (DOM f) (CARR grp)))
           (FORALL r1
             (IMPLIES (IN r1 (CARR grp))
               (FORALL r2
                 (IMPLIES (IN r2 (CARR grp))
                   (IMPLIES (AND (SUMS-TO grp f r1) (SUMS-TO grp f r2))
                     (= r1 r2)))))))))))

(warrant! 'sums-to-unique 'informal
  "Given fin1, fin2 witnessing r1, r2 at eps/2, take ext = fin1 u fin2
   (finite, and a superset of each).  Both NRM(ri - sum_ext f) < eps/2, so by
   the triangle inequality NRM(r1 - r2) < eps for every eps, hence
   NRM(r1 - r2) = 0, hence r1 = r2 by definiteness of the group norm
   (is-group-norm).  A candidate to discharge into a formal `proof' later.")

;;; -----------------------------------------------------------------------
;;; The payload: absolute summability implies (unconditional) summability,
;;; in a COMPLETE normed abelian group.
;;;
;;; Completeness is taken on the induced metric -- IS-COMPLETE(NAG-METRIC-
;;; SPACE grp), d(u,v) = ||u . v^-1|| (normed-ag-metric.scm) -- so this is the
;;; abstract Banach-space fact "absolutely convergent => unconditionally
;;; convergent."  Unconditionality needs no separate clause: IS-SUMMABLE is
;;; defined through the order-blind net SUMS-TO, which never sees an
;;; enumeration of the index set.
(support 'absolute-summable-implies-summable
  '(FORALL grp
     (IMPLIES (AND (IS-NORMED-AG grp)
                   (IS-COMPLETE (NAG-METRIC-SPACE grp)))
       (FORALL f
         (IMPLIES (AND (IN f (FUN (DOM f) (CARR grp)))
                       (IS-ABSOLUTELY-SUMMABLE grp f))
           (IS-SUMMABLE grp f))))))

(warrant! 'absolute-summable-implies-summable 'informal
  "Absolute summability makes the norm-tails vanish: ESUM(i |-> ||f(i)||) is a
   real, so by esum-finite-iff-bounded its finite partial sums are bounded and
   approach their sup -- for every eps there is a finite fin <= DOM f with
   Sum_{DOM f minus fin} ||f|| < eps.  Then for any finite ext with fin <= ext
   <= DOM f, ||Sum_ext f - Sum_fin f|| <= Sum_{ext minus fin} ||f|| < eps by
   the triangle inequality (subadditivity of the group norm).  Hence the net
   of finite partial sums is Cauchy in NAG-METRIC-SPACE(grp); completeness
   (IS-COMPLETE) supplies a limit r in the carrier, and that r witnesses
   SUMS-TO(grp, f, r), so IS-SUMMABLE(grp, f).  The sum is unconditional by
   construction (SUMS-TO is a net over finite subsets, not a series).  A
   candidate to discharge into a formal `proof' later.")

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'SUMS-TO 'kind 'predicate 'arity 3
           'english "$2 sums to $3 in $1")
(notation! 'IS-SUMMABLE 'kind 'predicate 'arity 2
           'english "$2 is summable in $1")
(notation! 'IS-ABSOLUTELY-SUMMABLE 'kind 'predicate 'arity 2
           'english "$2 is absolutely summable in $1")
