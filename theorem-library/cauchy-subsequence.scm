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
;;; 3.  (A) The nested block family  --  pigeonhole recursion
;;; =======================================================================

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

;;; totally-bounded-has-cauchy-subsequence: the parameter-free headline.  Drop rad
;;; by null-rr-seq-exists + the rad-parametrised form.
(support 'totally-bounded-has-cauchy-subsequence
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (X s)))
           (FORSOME phi
             (AND (STRICTLY-MONO-NN phi)
                  (IS-CAUCHY-SEQ s (SUBSEQ f phi)))))))))
(warrant! 'totally-bounded-has-cauchy-subsequence 'reference
  "Instantiate totally-bounded-has-cauchy-subseq-rad at a null radius sequence
   supplied by null-rr-seq-exists.  The sequential-compactness consequence of total
   boundedness; calculus.pdf Prop 3.31.")
