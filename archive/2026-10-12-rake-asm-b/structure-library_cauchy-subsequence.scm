;;; MOVED 2026-09-20 (batch 12-A) from theorem-library/: this file is VOCABULARY --
;;; definitions, notation and warranted supports, not one proof -- and every theorem
;;; stated with it had to load below it.  Its load.scm slot is unchanged.
;;; RETIRED 2026-09-17 (proven): subseq-is-fun -- theorem-library/rake-analysis2.scm
;;; RETIRED 2026-09-17 (proven): strictly-mono-ge-id -- theorem-library/rake-algebra.scm; cauchy-block-estimate -- theorem-library/rake-balls.scm
;;; structure-library/cauchy-subsequence.scm
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

;;; strictly-mono-ge-id: a strictly monotone reindexing of NN dominates the
;;; identity -- k <= phi(k) for all k.  The fundamental fact that lets a "tail
;;; past position k" of a subsequence reach index >= any threshold: if phi is
;;; strictly monotone then phi(k) >= k, so n >= N forces phi(n) >= N.  Used by
;;; subseq-of-convergent and every diagonal/tail estimate.

;;; SUBSEQ(f, phi) -- the reindexed sequence  k |-> f(phi k)  (= f o phi).
(def-functoid 'SUBSEQ '(f phi)
  '(VNB-LAMBDA k NN (f (phi k))))

;;; IS-SUBSEQUENCE(s, y, f) -- y is a subsequence of the PTS(s)-sequence f:
;;; y = f o phi for some strictly monotone reindexing phi.
(def-predicate 'IS-SUBSEQUENCE '(s y f)
  '(AND (IN f (FUN NN (PTS s)))
        (FORSOME phi
          (AND (STRICTLY-MONO-NN phi)
               (= y (SUBSEQ f phi))))))

;;; SUBSQN(y, f) -- "y is a subsequence of f", the SPACE-FREE relation (the
;;; user's proposal, 2026-08-20).
;;;
;;; IS-SUBSEQUENCE above conflates two different things: a TYPING
;;; (f : NN -> PTS(s)) and a RELATION (y reindexes f).  The relation needs no
;;; space at all -- "y = f o phi for a strictly monotone phi" is a statement
;;; about two sequences and nothing else -- and carrying `s' through it is what
;;; makes the predicate awkward to use.  Measured: IS-SUBSEQUENCE has ZERO
;;; citations in the whole tree.  Every theorem in the arc
;;; (totally-bounded-has-cauchy-subsequence, tb-has-eps-cauchy-subseq,
;;; cauchy-rapid-subsequence, coordinatewise-diagonal-subseq,
;;; subsequence-principle) writes `forsome([phi], strictly-mono-nn(phi) and ...)'
;;; out longhand instead, which is the predicate's own body with the typing
;;; dropped.  SUBSQN is that body, named.
;;;
;;; A `def-predicate', so it installs a citable defining IFF -- unlike a
;;; `def-functoid', which installs only a rewrite macete and cannot be unfolded
;;; in an ASSUMPTION by `mac-h'.
(def-predicate 'SUBSQN '(y f)
  '(FORSOME phi
     (AND (STRICTLY-MONO-NN phi)
          (= y (SUBSEQ f phi)))))

(notation! 'SUBSQN 'kind 'predicate 'arity 2
           'english "$1 is a subsequence of $2")

;;; The bridge -- IS-SUBSEQUENCE is the typing and SUBSQN together -- is PROVEN
;;; in theorem-library/subsqn-basics.scm, not here: this file loads at
;;; load.scm:314, long before `interactive' (465), so it has no `sp' / `qed'.

;;; subseq-is-fun: a subsequence of an PTS(s)-sequence is again an PTS(s)-sequence.
;;; phi : NN -> NN and f : NN -> PTS(s), so f o phi : NN -> PTS(s).  Typing slice,
;;; directly backchainable (VNB macetes rewrite goals not hyps).
;;; IS-EPS-CAUCHY-SEQ(s, eps, y) -- y : NN -> PTS(s) is eps-Cauchy: EVERY pair of
;;; terms is within eps.  This is a FIXED eps and ALL pairs -- the global, no-
;;; threshold cousin of IS-CAUCHY-SEQ (which quantifies eps and only bounds the
;;; tail past some N).  An eps-Cauchy subsequence is the single-radius output of
;;; one pigeonhole step; the diagonal argument laces these together across
;;; eps = rad(k) into a genuine IS-CAUCHY-SEQ.
(def-predicate 'IS-EPS-CAUCHY-SEQ '(s eps y)
  '(AND (IS-METRIC-SPACE s)
   (AND (IN y (FUN NN (PTS s)))
        (FORALL m
          (IMPLIES (IN m NN)
            (FORALL n_
              (IMPLIES (IN n_ NN)
                (<= ((DIST s) (y m) (y n_)) eps))))))))

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
;;; null-rr-seq-exists RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-subseq-leaves.scm

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
;;;   eps>0:  TOTALLY-BOUNDED at radius eps/2 gives a FINITE eps/2-net F for PTS(s)
;;;           (IS-R-NET s F (PTS s) (eps/2), CARD F in NN).
;;;   classifier:  CHOICE gives pi : NN -> F with pi(n) = a net point whose
;;;           eps/2-ball holds f(n) -- exists because F is an eps/2-net (every
;;;           f(n) in PTS(s) is within eps/2 of some net point).
;;;   pigeonhole:  NN infinite, F finite, pi : NN -> F, so pigeonhole-infinite
;;;           gives c in F with an INFINITE fibre I = { n : pi(n)=c } in
;;;           INF-SUBSETS(NN); every n in I has f(n) in BALL(s, c, eps/2).
;;;   enumerate:  nn-enum-spec gives phi = NN-ENUM(I) : NN -> I strictly
;;;           monotone, so f(phi k) in BALL(s, c, eps/2) for every k.
;;;   estimate:  f(phi m), f(phi n) lie in one eps/2-ball, so ball-2r-triangle
;;;           gives d(f(phi m), f(phi n)) <= 2*(eps/2) = eps.  SUBSEQ(f,phi) is
;;;           eps-Cauchy.  (IS-METRIC-SPACE s and the typing of SUBSEQ come from
;;;           TOTALLY-BOUNDED s and subseq-is-fun.)
;;; tb-has-eps-cauchy-subseq PROVEN modulo 0 in theorem-library/rake-offbill-combinatorial.scm (2026-09-19, batch 8)

;;; =======================================================================
;;; 2.6  The relativized pigeonhole fibre  --  the shared primitive
;;; =======================================================================

;;; tb-block-step: within ANY infinite index block J, total boundedness at
;;; radius r pins an infinite SUB-block J_ subset J into a single r-ball.  This
;;; is the recursion-free primitive that BOTH headline routes rest on:
;;;   * tb-has-eps-cauchy-subseq = block-step at J = NN, then enumerate the fibre
;;;     (nn-enum-spec) and estimate (ball-2r-triangle);
;;;   * block-family = block-step RECURSED via dc-on-nn (PTS = INF-SUBSETS(NN),
;;;     a = NN, the step relation R(k,J,J_) = "J_ is the rad(k)-fibre tb-block-step
;;;     gives inside J"); its totality hypothesis IS this lemma at r = rad(k).
;;; The single pigeonhole: TOTALLY-BOUNDED at r gives a finite r-net F; CHOICE a
;;; classifier pi : J -> F sending i to a net point whose r-ball holds f(i);
;;; pigeonhole-infinite on the infinite J yields c with an infinite fibre
;;; J_ = { i in J : pi(i) = c } subset J, every f(i) (i in J_) in BALL(s,c,r).
;;; tb-block-step PROVEN modulo 0 in theorem-library/rake-offbill-combinatorial.scm (2026-09-19, batch 8)

;;; =======================================================================
;;; 3.  (A) The nested block family  --  pigeonhole recursion
;;; =======================================================================

;;; tb-rad-ball-cover: the metric-to-combinatorial BRIDGE.  Total boundedness
;;; turns a pointwise-positive radius sequence into a SEQUENCE OF FINITE COVERS
;;; of PTS(s) -- exactly the input block-family-combinatorial wants -- each of
;;; whose members is a rad(k)-ball about a centre in PTS(s).  (i) feeds the
;;; combinatorial recursion; (ii) lets its "U in cov(k)" capture be read back
;;; as the metric "some centre c in PTS(s)".  Only POS-RR(rad k) is used; rad's
;;; decay plays no part (it is consumed downstream, in the 2r estimate).
;;; tb-rad-ball-cover RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-tb-leaves-2.scm, after IS-R-NET gained the clause F subseteq A

;;; cauchy-block-estimate: the metric LEAF of the Cauchy estimate, folded into
;;; one fully-curried lemma so the headline proof closes by a single `fact'
;;; (no goal-only eq-subst gymnastics).  Two points y,z of one r-ball U =
;;; BALL(s,c,r), with r <= d and d+d = eps, are <= eps apart.

;;; NOTE: the metric is inessential here.  block-family is the instance
;;;   V := PTS(s), cov(k) := { BALL(s,c,rad k) : c in a finite rad(k)-net }
;;; of block-family-combinatorial (theorem-library/block-family-combinatorial
;;; .scm), where total boundedness supplies only "cov(k) is a finite cover"
;;; and rad's positivity/nullity are used solely to MANUFACTURE that cover
;;; (and, downstream, the 2r Cauchy estimate) -- never in the construction.
;;;
;;; block-family: total boundedness lets us recursively pigeonhole the index
;;; set NN into a NESTED descending family of INFINITE index blocks, each block
;;; pinning f into a single small ball.
;;;
;;;   For TB s, f : NN -> PTS(s) and a positive null rad, there is
;;;     S : NN -> INF-SUBSETS(NN)  with
;;;       (nesting)  S(succ k) subset S(k)             for all k, and
;;;       (small)    for each k some centre c_k in PTS(s) has
;;;                  f(i) in BALL(s, c_k, rad k)        for every i in S(k).
;;;
;;; This is the recursive engine of the diagonal argument and the one new
;;; construction here.  Proof sketch (NN-recursion + choice, like
;;; cauchy-rapid-subsequence):
;;;   S(0) := NN (infinite).  Given S(k) infinite, TB at radius rad(k) gives a
;;;   finite rad(k)-net F_k for PTS(s); the map  i |-> (a net point whose rad(k)-
;;;   ball contains f(i))  sends the infinite S(k) into the finite F_k, so by
;;;   pigeonhole-infinite some centre c_k has an infinite fibre
;;;   S(k+1) := { i in S(k) : f(i) in BALL(s, c_k, rad k) }.  S(k+1) subset S(k)
;;;   and is infinite; choice picks c_k / the net.  Asserted during library-build
;;;   [[feedback-library-axioms-fine]] [[feedback-pss-over-proof-slog]].
;;; block-family PROVEN modulo 0 in theorem-library/rake-offbill-combinatorial.scm (2026-09-19, batch 8)

;;; =======================================================================
;;; 4.  Headline -- (B) diagonalize + (C) 2r estimate
;;; =======================================================================

;;; totally-bounded-has-cauchy-subseq-rad: the rad-parametrised workhorse.  Given
;;; a positive null rad, every PTS(s)-sequence has a Cauchy subsequence.
;;;
;;; Assembly (the non-circular glue -- the scout/tactic stress target, posed as a
;;; goal in archive/calculus-pre-rename/totally-bounded-cauchy-subseq.scm):
;;;   block-family gives the nested small-ball family S.  diagonalization gives a
;;;   strictly monotone phi with phi(j) in S(k) for all j >= k.  For m,n >= k the
;;;   terms f(phi m), f(phi n) both lie in BALL(s, c_k, rad k), so ball-2r-triangle
;;;   gives d(f(phi m), f(phi n)) < 2 rad(k).  Given eps>0, NULL-RR-SEQ at eps/2
;;;   supplies k with rad(k) <= eps/2, hence < eps: SUBSEQ(f,phi) is Cauchy.
;; Headline result (radius-indexed tb => Cauchy subsequence), not PSS plumbing;
;; the non-radius headline `totally-bounded-has-cauchy-subsequence' is already
;; proven and not in PSS.  Installed as a warranted ASSERTION, not a support.
(add-axiom! *library* 'totally-bounded-has-cauchy-subseq-rad
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (PTS s)))
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

;;; ----- Plain-English glosses (PSS review 2026-06-26): 3+-line statements -----
(gloss! 'tb-block-step
  "For a totally bounded space s, a sequence f of points of s, a radius r>0, and an infinite index block J: there is a smaller infinite block J' contained in J and a single centre c such that all f(i) for i in J' lie in the ball of radius r about c.  One relativized pigeonhole step over a sub-block.")
(gloss! 'tb-rad-ball-cover
  "For a totally bounded space s and a pointwise-positive radius sequence rad: the carrier PTS(s) is a set, and there is a sequence cov of finite covers of PTS(s) in which every member of cov(k) is a ball of radius rad(k) about some centre in PTS(s).  The bridge turning total boundedness into the finite-cover input the combinatorial block recursion consumes.")
(gloss! 'cauchy-block-estimate
  "For a metric space s, a ball U = BALL(s,c,r), two points y,z of U, and reals d,eps with r<=d and d+d=eps: the distance from y to z is at most eps.  The fully-curried 2r estimate -- two points in one r-ball are within 2r.")
(gloss! 'block-family
  "For a totally bounded space s, a sequence f of points of s, and a positive null radius sequence rad: there is a nested tower of infinite index blocks blk(0) >= blk(1) >= ... such that at each level k all the f(i) for i in blk(k) lie in a single ball of radius rad(k) about some centre.  Recursive pigeonhole into ever-smaller blocks -- the engine of the Cauchy-subsequence extraction.")

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'STRICTLY-MONO-NN 'kind 'predicate 'arity 1
           'english "$1 is a strictly increasing sequence of naturals")
(notation! 'IS-SUBSEQUENCE 'kind 'predicate 'arity 3
           'english "$2 is a subsequence of $3 in $1")
(notation! 'IS-EPS-CAUCHY-SEQ 'kind 'predicate 'arity 3
           'english "$3 is $2-Cauchy in $1")
(notation! 'NULL-RR-SEQ 'kind 'predicate 'arity 1
           'english "$1 is a sequence of positive reals tending to zero")
