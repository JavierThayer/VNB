;;; theorem-library/cauchy-subsequence.scm
;;;
;;; Totally bounded  ==>  every sequence has a Cauchy subsequence.
;;; (The sequential-compactness half of compactness; calculus.pdf Prop 3.31.)
;;;
;;; This file supplies the missing SUBSEQUENCE vocabulary and assembles the
;;; classical diagonalisation argument out of pieces that already live in the
;;; library:
;;;
;;;   pigeonhole-infinite   (theorem-library/pigeonhole)   -- per-level fibre
;;;   diagonalization       (theorem-library/diagonalization) -- diagonal pull
;;;   ball-2r-triangle      (structure-library/metric-topology) -- Cauchy estimate
;;;   TOTALLY-BOUNDED/IS-R-NET/BALL (metric-topology)       -- finite r-nets
;;;   INF-SUBSETS           (structure-library/inf-subsets)
;;;   IS-CAUCHY-SEQ         (structure-library/metric-completeness)
;;;
;;; The comments in pigeonhole.scm and diagonalization.scm name THIS theorem as
;;; their intended consumer; here it finally gets stated and decomposed.
;;;
;;; Decomposition (each step a recognised standard fact, warranted PSS entry):
;;;
;;;   (A) block-family    : TB + a positive null radius sequence rad let us
;;;                         recursively pigeonhole the index set into a NESTED
;;;                         family S : NN -> INF-SUBSETS(NN), with every index in
;;;                         S(k) sending f into one common rad(k)-ball.
;;;   (B) diagonalization : the nested family yields a strictly monotone phi
;;;                         whose tail past k lies entirely in S(k).
;;;   (C) ball-2r-triangle: two tail terms f(phi m), f(phi n) (m,n >= k) live in
;;;                         the same rad(k)-ball, so d < 2 rad(k); rad -> 0 makes
;;;                         the subsequence Cauchy.
;;;
;;; (A) is the one genuinely new construction (a pigeonhole recursion, the
;;; analogue of cauchy-rapid-subsequence's NN-recursion); it is asserted with a
;;; sketch, library-build phase [[feedback-library-axioms-fine]].  The headline
;;; itself is then the (B)+(C) assembly -- the non-question-begging glue, posed
;;; as a proof target in calculus/ for the scout/tactic stress-test.

;;; =======================================================================
;;; 1.  Reindexing / subsequence vocabulary
;;; =======================================================================

;;; STRICTLY-MONO-NN(phi) -- phi : NN -> NN strictly increasing.  Factored out
;;; of the three inline copies in subsequence-capture, nn-enum-spec and
;;; cauchy-rapid-subsequence (those keep their inline forms for now; this is the
;;; named predicate going forward).
(def-predicate 'STRICTLY-MONO-NN '(phi)
  '(AND (IN phi (FUN NN NN))
        (FORALL m
          (IMPLIES (IN m NN)
            (FORALL n_
              (IMPLIES (IN n_ NN)
                (IMPLIES (< m n_) (< (phi m) (phi n_)))))))))

;;; SUBSEQ(f, phi) -- the reindexed sequence  k |-> f(phi k)  (= f o phi).
(def-functoid 'SUBSEQ '(f phi)
  '(VNB-LAMBDA k (f (phi k))))

;;; IS-SUBSEQUENCE(s, y, f) -- y is a subsequence of the X(s)-sequence f:
;;; y = f o phi for some strictly monotone reindexing phi.
(def-predicate 'IS-SUBSEQUENCE '(s y f)
  '(AND (IN f (FUN NN (X s)))
        (FORSOME phi
          (AND (STRICTLY-MONO-NN phi)
               (= y (SUBSEQ f phi))))))

;;; subseq-is-fun: a subsequence of an X(s)-sequence is again an X(s)-sequence.
;;; phi : NN -> NN and f : NN -> X(s), so f o phi : NN -> X(s).  Typing slice,
;;; directly backchainable (VNB macetes rewrite goals not hyps).
(support 'subseq-is-fun
  '(FORALL s (FORALL f (FORALL phi
     (IMPLIES (AND (IN f (FUN NN (X s))) (STRICTLY-MONO-NN phi))
              (IN (SUBSEQ f phi) (FUN NN (X s))))))))
(warrant! 'subseq-is-fun 'well-known
  "f : NN -> X(s) and phi : NN -> NN, so the composite SUBSEQ(f,phi) = k |-> f(phi
   k) is again a function NN -> X(s).  Pure composition typing.")

;;; IS-EPS-CAUCHY-SEQ(s, eps, y) -- y : NN -> X(s) is eps-Cauchy: EVERY pair of
;;; terms is within eps.  This is a FIXED eps and ALL pairs -- the global, no-
;;; threshold cousin of IS-CAUCHY-SEQ (which quantifies eps and only bounds the
;;; tail past some N).  An eps-Cauchy subsequence is the single-radius output of
;;; one pigeonhole step; the diagonal argument laces these together across
;;; eps = rad(k) into a genuine IS-CAUCHY-SEQ.
(def-predicate 'IS-EPS-CAUCHY-SEQ '(s eps y)
  '(AND (IS-METRIC-SPACE s)
   (AND (IN y (FUN NN (X s)))
        (FORALL m
          (IMPLIES (IN m NN)
            (FORALL n_
              (IMPLIES (IN n_ NN)
                (<= ((D s) (y m) (y n_)) eps))))))))

;;; =======================================================================
;;; 2.  Null radius sequences
;;; =======================================================================

;;; NULL-RR-SEQ(rad) -- rad : NN -> RR, pointwise positive, and rad(k) -> 0
;;; (stated elementarily, matching IS-CAUCHY-SEQ's own eps/N idiom rather than
;;; routing through RR-MS convergence).  Bundles the two properties the Cauchy
;;; assembly needs: each rad(k) is a legitimate ball radius, and the radii
;;; shrink below any eps eventually.
(def-predicate 'NULL-RR-SEQ '(rad)
  '(AND (IN rad (FUN NN RR))
        (AND (FORALL k (IMPLIES (IN k NN) (POS-RR (rad k))))
             (FORALL eps
               (IMPLIES (POS-RR eps)
                 (FORSOME N
                   (AND (IN N NN)
                        (FORALL k
                          (IMPLIES (AND (IN k NN) (<= N k))
                            (<= (rad k) eps))))))))))

;;; null-rr-seq-exists: a positive null real sequence exists (e.g. k |-> 2^-k,
;;; or k |-> 1/(k+1)).  Lets the parameter-free headline drop the rad argument.
(support 'null-rr-seq-exists
  '(FORSOME rad (NULL-RR-SEQ rad)))
(warrant! 'null-rr-seq-exists 'well-known
  "k |-> 2^-k is in FUN(NN,RR), is positive, and 2^-k -> 0 (Archimedean / geometric
   decay): given eps>0 pick N with 2^-N <= eps.  A concrete witness; no content.")

;;; =======================================================================
;;; 2.5  The single-pigeonhole base case  --  eps-Cauchy subsequence
;;; =======================================================================

;;; tb-has-eps-cauchy-subseq: total boundedness + a sequence + ONE radius eps
;;; gives a subsequence that is eps-Cauchy.  This is the heart of sequential
;;; compactness with the recursion stripped off:
;;;   * block-family is exactly this step applied recursively inside a shrinking
;;;     infinite block (replace NN by S(k), eps by rad(k));
;;;   * the headline (totally-bounded-has-cauchy-subseq) is this laced across
;;;     eps = rad(k) by diagonalization.
;;;
;;; Proof -- ONE pigeonhole; every cited piece is already PSS:
;;;   eps>0:  TOTALLY-BOUNDED at radius eps/2 gives a FINITE eps/2-net F for X(s)
;;;           (IS-R-NET s F (X s) (eps/2), CARD F in NN).
;;;   classifier:  CHOICE gives pi : NN -> F with pi(n) = a net point whose
;;;           eps/2-ball holds f(n) -- exists because F is an eps/2-net (every
;;;           f(n) in X(s) is within eps/2 of some net point).
;;;   pigeonhole:  NN infinite, F finite, pi : NN -> F, so pigeonhole-infinite
;;;           gives c in F with an INFINITE fibre I = { n : pi(n)=c } in
;;;           INF-SUBSETS(NN); every n in I has f(n) in BALL(s, c, eps/2).
;;;   enumerate:  nn-enum-spec gives phi = NN-ENUM(I) : NN -> I strictly
;;;           monotone, so f(phi k) in BALL(s, c, eps/2) for every k.
;;;   estimate:  f(phi m), f(phi n) lie in one eps/2-ball, so ball-2r-triangle
;;;           gives d(f(phi m), f(phi n)) <= 2*(eps/2) = eps.  SUBSEQ(f,phi) is
;;;           eps-Cauchy.  (IS-METRIC-SPACE s and the typing of SUBSEQ come from
;;;           TOTALLY-BOUNDED s and subseq-is-fun.)
(support 'tb-has-eps-cauchy-subseq
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (X s)))
           (FORALL eps
             (IMPLIES (POS-RR eps)
               (FORSOME phi
                 (AND (STRICTLY-MONO-NN phi)
                      (IS-EPS-CAUCHY-SEQ s eps (SUBSEQ f phi)))))))))))
(warrant! 'tb-has-eps-cauchy-subseq 'reference
  "Single pigeonhole step of sequential compactness (calculus.pdf Prop 3.31):
   finite eps/2-net (TOTALLY-BOUNDED) + classifier pi:NN->F (choice) +
   pigeonhole-infinite (infinite fibre I) + nn-enum-spec (strictly monotone phi
   enumerating I) + ball-2r-triangle (two terms in one eps/2-ball are <= eps
   apart).  Every cited piece is already PSS; the recursion-free core that
   block-family iterates.  Stated warranted during library-build; the forward
   assembly is the proof target.")

;;; =======================================================================
;;; 2.6  The relativized pigeonhole fibre  --  the shared primitive
;;; =======================================================================

;;; tb-block-step: within ANY infinite index block J, total boundedness at
;;; radius r pins an infinite SUB-block J_ subset J into a single r-ball.  This
;;; is the recursion-free primitive that BOTH headline routes rest on:
;;;   * tb-has-eps-cauchy-subseq = block-step at J = NN, then enumerate the fibre
;;;     (nn-enum-spec) and estimate (ball-2r-triangle);
;;;   * block-family = block-step RECURSED via dc-on-nn (X = INF-SUBSETS(NN),
;;;     a = NN, the step relation R(k,J,J_) = "J_ is the rad(k)-fibre tb-block-step
;;;     gives inside J"); its totality hypothesis IS this lemma at r = rad(k).
;;; The single pigeonhole: TOTALLY-BOUNDED at r gives a finite r-net F; CHOICE a
;;; classifier pi : J -> F sending i to a net point whose r-ball holds f(i);
;;; pigeonhole-infinite on the infinite J yields c with an infinite fibre
;;; J_ = { i in J : pi(i) = c } subset J, every f(i) (i in J_) in BALL(s,c,r).
(support 'tb-block-step
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (X s)))
           (FORALL r
             (IMPLIES (POS-RR r)
               (FORALL J
                 (IMPLIES (IN J (INF-SUBSETS NN))
                   (FORSOME J_
                     (AND (IN J_ (INF-SUBSETS NN))
                     (AND (SUBSET J_ J)
                          (FORSOME c
                            (AND (IN c (X s))
                                 (FORALL i
                                   (IMPLIES (IN i J_)
                                     (IN (f i) (BALL s c r))))))))))))))))))
(warrant! 'tb-block-step 'reference
  "Relativized single pigeonhole (calculus.pdf Prop 3.31, the per-level step):
   finite r-net (TOTALLY-BOUNDED) + classifier pi:J->F (choice) +
   pigeonhole-infinite on the infinite J (infinite fibre J_ subset J in one
   r-ball).  Same pieces as tb-has-eps-cauchy-subseq but over a sub-block J and
   producing the index set, not its enumeration.  The shared primitive of the
   eps-Cauchy lemma and block-family; see calculus/block-family-rederive.scm.")

;;; =======================================================================
;;; 3.  (A) The nested block family  --  pigeonhole recursion
;;; =======================================================================

;;; tb-rad-ball-cover: the metric-to-combinatorial BRIDGE.  Total boundedness
;;; turns a pointwise-positive radius sequence into a SEQUENCE OF FINITE COVERS
;;; of X(s) -- exactly the input block-family-combinatorial wants -- each of
;;; whose members is a rad(k)-ball about a centre in X(s).  (i) feeds the
;;; combinatorial recursion; (ii) lets its "U in cov(k)" capture be read back
;;; as the metric "some centre c in X(s)".  Only POS-RR(rad k) is used; rad's
;;; decay plays no part (it is consumed downstream, in the 2r estimate).
(support 'tb-rad-ball-cover
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL rad
         (IMPLIES (FORALL k (IMPLIES (IN k NN) (POS-RR (rad k))))
           (AND
             ;; carrier sethood -- the combinatorial engine needs V=(X s) in SET;
             ;; free here since TOTALLY-BOUNDED s gives IS-METRIC-SPACE s.
             (IN (X s) SET)
             (FORSOME cov
               (AND
                 (FORALL k
                   (IMPLIES (IN k NN) (IS-FINITE-COVER (cov k) (X s))))
                 (FORALL k
                   (IMPLIES (IN k NN)
                     (FORALL U
                       (IMPLIES (IN U (cov k))
                         (FORSOME c
                           (AND (IN c (X s))
                                (= U (BALL s c (rad k)))))))))))))))))
(warrant! 'tb-rad-ball-cover 'reference
  "cov(k) := IMAGE(c |-> BALL(s,c,rad k), F_k), F_k a finite rad(k)-net
   (TOTALLY-BOUNDED at rad k > 0; CHOICE picks one per k).  (i) cov(k) is a
   finite cover of X(s): image of the finite F_k is finite, and IS-R-NET makes
   every p in X(s) lie within rad(k) of some c in F_k, i.e. p in BALL(s,c,rad k)
   in cov(k) (IS-R-NET uses d<r, matching the open ball, so the balls truly
   cover).  (ii) every member is by construction BALL(s,c,rad k) with c in F_k
   subset X(s) (centres in X(s) by D(s) typing).  Also hands back (X s) in SET
   (free from IS-METRIC-SPACE s), the set V the combinatorial engine needs.
   The metric content total boundedness contributes to block-family, isolated
   in one bridge -- see calculus/cauchy-subseq-via-combinatorial.scm.")

;;; cauchy-block-estimate: the metric LEAF of the Cauchy estimate, folded into
;;; one fully-curried lemma so the headline proof closes by a single `fact'
;;; (no goal-only eq-subst gymnastics).  Two points y,z of one r-ball U =
;;; BALL(s,c,r), with r <= d and d+d = eps, are <= eps apart.
(support 'cauchy-block-estimate
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL c (IMPLIES (IN c (X s))
       (FORALL r (IMPLIES (POS-RR r)
         (FORALL U (IMPLIES (= U (BALL s c r))
           (FORALL y (IMPLIES (IN y U)
             (FORALL z (IMPLIES (IN z U)
               (FORALL d (IMPLIES (POS-RR d)
                 (FORALL eps (IMPLIES (IN eps RR)
                   (IMPLIES (<= r d)
                     (IMPLIES (= (+ d d) eps)
                       (<= ((D s) y z) eps))))))))))))))))))))
(warrant! 'cauchy-block-estimate 'proof
  "y,z in U = BALL(s,c,r): substitute U, ball-2r-triangle gives d(y,z) <= r+r.
   r <= d gives r+r <= d+d (rr-le-add), and d+d = eps, so r+r <= eps; rr-le-trans
   then gives d(y,z) <= eps.  Curried (no AND antecedents) so the headline proof
   discharges every premise by in-context `fact' auto-detach.")

;;; NOTE: the metric is inessential here.  block-family is the instance
;;;   V := X(s), cov(k) := { BALL(s,c,rad k) : c in a finite rad(k)-net }
;;; of block-family-combinatorial (theorem-library/block-family-combinatorial
;;; .scm), where total boundedness supplies only "cov(k) is a finite cover"
;;; and rad's positivity/nullity are used solely to MANUFACTURE that cover
;;; (and, downstream, the 2r Cauchy estimate) -- never in the construction.
;;;
;;; block-family: total boundedness lets us recursively pigeonhole the index
;;; set NN into a NESTED descending family of INFINITE index blocks, each block
;;; pinning f into a single small ball.
;;;
;;;   For TB s, f : NN -> X(s) and a positive null rad, there is
;;;     S : NN -> INF-SUBSETS(NN)  with
;;;       (nesting)  S(succ k) subset S(k)             for all k, and
;;;       (small)    for each k some centre c_k in X(s) has
;;;                  f(i) in BALL(s, c_k, rad k)        for every i in S(k).
;;;
;;; This is the recursive engine of the diagonal argument and the one new
;;; construction here.  Proof sketch (NN-recursion + choice, like
;;; cauchy-rapid-subsequence):
;;;   S(0) := NN (infinite).  Given S(k) infinite, TB at radius rad(k) gives a
;;;   finite rad(k)-net F_k for X(s); the map  i |-> (a net point whose rad(k)-
;;;   ball contains f(i))  sends the infinite S(k) into the finite F_k, so by
;;;   pigeonhole-infinite some centre c_k has an infinite fibre
;;;   S(k+1) := { i in S(k) : f(i) in BALL(s, c_k, rad k) }.  S(k+1) subset S(k)
;;;   and is infinite; choice picks c_k / the net.  Asserted during library-build
;;;   [[feedback-library-axioms-fine]] [[feedback-pss-over-proof-slog]].
(support 'block-family
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (X s)))
           (FORALL rad
             (IMPLIES (NULL-RR-SEQ rad)
               ;; family var is `blk', NOT `S': the reader case-folds, so an
               ;; `S' bound inside this `FORALL s' would capture the space s
               ;; [[feedback-no-case-variant-binders]].
               (FORSOME blk
                 (AND (IN blk (FUN NN (INF-SUBSETS NN)))
                 (AND (FORALL k
                        (IMPLIES (IN k NN) (SUBSET (blk (succ k)) (blk k))))
                      (FORALL k
                        (IMPLIES (IN k NN)
                          (FORSOME c
                            (AND (IN c (X s))
                                 (FORALL i
                                   (IMPLIES (IN i (blk k))
                                     (IN (f i) (BALL s c (rad k)))))))))))))))))))
(warrant! 'block-family 'reference
  "Nested-pigeonhole construction (calculus.pdf, proof of sequential compactness
   of a totally bounded space).  S(0)=NN; given infinite S(k), a finite rad(k)-net
   for X(s) sends f(S(k)) into finitely many balls, so pigeonhole-infinite yields
   an infinite fibre S(k+1) subset S(k) inside one rad(k)-ball.  CHOICE supplies
   the net and the fibre centre.  The hard core of the theorem; the headline below
   is the diagonalize-and-estimate assembly on top of this.")

;;; =======================================================================
;;; 4.  Headline -- (B) diagonalize + (C) 2r estimate
;;; =======================================================================

;;; totally-bounded-has-cauchy-subseq-rad: the rad-parametrised workhorse.  Given
;;; a positive null rad, every X(s)-sequence has a Cauchy subsequence.
;;;
;;; Assembly (the non-circular glue -- the scout/tactic stress target, posed as a
;;; goal in calculus/totally-bounded-cauchy-subseq.scm):
;;;   block-family gives the nested small-ball family S.  diagonalization gives a
;;;   strictly monotone phi with phi(j) in S(k) for all j >= k.  For m,n >= k the
;;;   terms f(phi m), f(phi n) both lie in BALL(s, c_k, rad k), so ball-2r-triangle
;;;   gives d(f(phi m), f(phi n)) < 2 rad(k).  Given eps>0, NULL-RR-SEQ at eps/2
;;;   supplies k with rad(k) <= eps/2, hence < eps: SUBSEQ(f,phi) is Cauchy.
(support 'totally-bounded-has-cauchy-subseq-rad
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (X s)))
           (FORALL rad
             (IMPLIES (NULL-RR-SEQ rad)
               (FORSOME phi
                 (AND (STRICTLY-MONO-NN phi)
                      (IS-CAUCHY-SEQ s (SUBSEQ f phi)))))))))))
(warrant! 'totally-bounded-has-cauchy-subseq-rad 'reference
  "block-family (nested small-ball blocks) + diagonalization (strictly monotone phi
   with tail past k inside S(k)) + ball-2r-triangle (two terms in one rad(k)-ball
   are < 2 rad(k) apart) + NULL-RR-SEQ (rad(k) <= eps/2 eventually).  calculus.pdf
   Prop 3.31; assembly posed as a proof goal for the engine in calculus/.")

;;; totally-bounded-has-cauchy-subsequence: the parameter-free headline.
;;; PROVEN (not asserted) -- see theorem-library/cauchy-subseq-proof.scm, which
;;; drives it to QED via the combinatorial route (null-rr-seq-exists for rad,
;;; tb-rad-ball-cover for the finite covers, block-family-combinatorial for the
;;; block witness, diagonalization for phi, cauchy-block-estimate for the 2r
;;; estimate).  The statement is reproduced there in its (sp ...).
