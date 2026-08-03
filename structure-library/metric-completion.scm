;;; metric-completion.scm -- the completion of a metric space, CONCRETELY, as
;;; the quotient of its Cauchy sequences by the null-distance equivalence, and
;;; the facts that make it a complete metric space into which the original
;;; embeds isometrically.
;;;
;;; Design (project_metric_completion, feedback_concrete_universal_property):
;;; we do NOT define the completion by its universal property.  We give the
;;; CONCRETE object -- Cauchy sequences modulo `distance tends to 0' -- and then
;;; assert (library-phase) the properties it has, culminating in the universal
;;; property in a later increment.  The equivalence-class machinery is REUSED
;;; wholesale from setoid.scm: the completion's carrier is literally
;;; QUOTIENT(CAUCHY-SETOID(M)).
;;;
;;; The motivating example of an equivalence relation: two Cauchy sequences f, g
;;; are identified exactly when d(f_n, g_n) -> 0.  This is null-distance, the
;;; classic reason the setoid quotient was built.
;;;
;;; A sequence is a function f : NN -> PTS(M) (as in metric-completeness.scm).
;;; The real sequence n |-> d(f_n, g_n) is Cauchy in RR (triangle inequality),
;;; and RR is complete (rr-complete), so it has a unique limit -- the completion
;;; distance.  RR-MS (numeric-instances.scm) is that metric space on RR; this
;;; file therefore loads after numeric-instances.
;;;
;;; Bound-var hygiene (feedback_no_case_variant_binders, feedback_mit_case_fold):
;;; element points are u, v -- NOT x (the point-set accessor was `X' under case-
;;; fold when this was written; it is `PTS' now);
;;; sequences f, g; the index n; the class pair p; the real limit dval.
;;;
;;; Dependencies: setoid.scm (CLASS, QUOTIENT, PROJ, IS-SETOID), metric-space.scm
;;; (IS-METRIC-SPACE, PTS, DIST), metric-completeness.scm (IS-CAUCHY-SEQ, CONVERGES-TO,
;;; IS-COMPLETE), numeric-instances.scm (RR-MS), kernel (SEP, IMAGE, CARTESIAN,
;;; FUN, LIST, NTH, IOTA, VNB-LAMBDA, FORSOME).

;;; =======================================================================
;;; The real distance sequence and the null-distance equivalence.
;;; =======================================================================

;; DIST-SEQ(M,f,g) = the real sequence  n |-> d(f_n, g_n)  in RR.
(def-functoid 'DIST-SEQ '(M f g)
  '(VNB-LAMBDA n NN ((DIST M) (f n) (g n))))

;; CSEQ-EQUIV(M,f,g): f ~ g, i.e. d(f_n,g_n) -> 0.  This is the equivalence
;; relation underlying the completion -- null distance.  Stated as convergence
;; of DIST-SEQ to the real 0 in RR-MS.
(def-predicate 'CSEQ-EQUIV '(M f g)
  '(CONVERGES-TO RR-MS (DIST-SEQ M f g) 0))

;;; =======================================================================
;;; The setoid of Cauchy sequences.
;;; =======================================================================

;; CSEQ(M) = the set of Cauchy sequences of M = { f in FUN(NN,PTS(M)) : Cauchy }.
;; A subset of the function set FUN(NN,PTS(M)) (a set), hence a set by separation.
(def-functoid 'CSEQ '(M)
  '(SEP f (FUN NN (PTS M)) (IS-CAUCHY-SEQ M f)))

;; CREL(M) = the null-distance relation as an extensional SET: the pairs
;; (f,g) of Cauchy sequences with f ~ g.  A subset of CARTESIAN(CSEQ,CSEQ),
;; in the shape SETOID's REL slot wants.  p ranges over LIST-pairs; its
;; components are (NTH 1 p), (NTH 2 p).
(def-functoid 'CREL '(M)
  '(SEP p (CARTESIAN (CSEQ M) (CSEQ M))
        (CSEQ-EQUIV M (NTH 1 p) (NTH 2 p))))

;; CAUCHY-SETOID(M) = [CSEQ(M), CREL(M)] : a SETOID instance (PTS = CSEQ, REL =
;; CREL).  All of CLASS / QUOTIENT / PROJ / DESCEND and the quotient universal
;; property apply to it verbatim.
(def-functoid 'CAUCHY-SETOID '(M)
  '(LIST (CSEQ M) (CREL M)))

;; cauchy-setoid-is-setoid: CAUCHY-SETOID(M) really is a setoid -- CREL is an
;; equivalence relation on CSEQ.
(support 'cauchy-setoid-is-setoid
  '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IS-SETOID (CAUCHY-SETOID M)))))
(warrant! 'cauchy-setoid-is-setoid 'well-known
  "CREL(M) subset CARTESIAN(CSEQ,CSEQ) by construction, and null distance is an
   equivalence relation on Cauchy sequences: REFLEXIVE since d(f_n,f_n)=0 -> 0;
   SYMMETRIC since d is symmetric, so d(f_n,g_n) and d(g_n,f_n) are the same
   real sequence; TRANSITIVE since d(f_n,h_n) <= d(f_n,g_n)+d(g_n,h_n)
   (triangle), and a sum of two null real sequences is null.  So IS-SETOID
   (the is-equivalence property folded into it) holds.")

;;; =======================================================================
;;; The completion as a metric space, concretely.
;;; =======================================================================

;; COMPLETION-DIST(M) = the metric on the quotient.  On a pair p = ([f],[g]) of
;; classes it returns the unique real that is the limit of d(f_n,g_n) for SOME
;; representatives f, g -- representation-independent because ~ is null
;; distance, so any other representatives give the same limit.  IOTA (definite
;; description), not a chosen representative.
(def-functoid 'COMPLETION-DIST '(M)
  '(VNB-LAMBDA p (CARTESIAN (QUOTIENT (CAUCHY-SETOID M)) (QUOTIENT (CAUCHY-SETOID M)))
     (IOTA dval
       (FORSOME f (FORSOME g
         (AND (IN f (CSEQ M))
         (AND (IN g (CSEQ M))
         (AND (= (NTH 1 p) (CLASS (CAUCHY-SETOID M) f))
         (AND (= (NTH 2 p) (CLASS (CAUCHY-SETOID M) g))
              (CONVERGES-TO RR-MS (DIST-SEQ M f g) dval))))))))))

;; COMPLETION(M) = [ PTS(M)/~ , d-hat ] : the completion as a METRIC-SPACE
;; instance.  Carrier = QUOTIENT(CAUCHY-SETOID(M)); metric = COMPLETION-DIST(M).
(def-functoid 'COMPLETION '(M)
  '(LIST (QUOTIENT (CAUCHY-SETOID M)) (COMPLETION-DIST M)))

;; completion-is-metric-space: the construction yields a metric space.
(support 'completion-is-metric-space
  '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IS-METRIC-SPACE (COMPLETION M)))))
(warrant! 'completion-is-metric-space 'well-known
  "Carrier QUOTIENT(CAUCHY-SETOID(M)) is a set (quotient-is-set, setoid.scm).
   COMPLETION-DIST descends the real limit of d(f_n,g_n) through both class
   arguments: well-defined (the limit exists -- DIST-SEQ is Cauchy in the
   complete RR -- and is independent of representatives by null distance), and
   it inherits the metric laws from d -- nonnegativity and symmetry pointwise
   then in the limit; the triangle inequality in the limit; and d-hat([f],[g])=0
   iff d(f_n,g_n)->0 iff [f]=[g] (separation of points).")

;; completion-is-complete: THE payoff -- the completion is complete.
(support 'completion-is-complete
  '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IS-COMPLETE (COMPLETION M)))))
(warrant! 'completion-is-complete 'well-known
  "Standard diagonal argument.  A Cauchy sequence of classes lifts to a sequence
   of Cauchy sequences; choosing for each a representative term close to within
   1/2^k yields a diagonal sequence that is Cauchy in M, and the class of that
   diagonal is the limit of the original sequence of classes.  Completeness of
   RR enters only through the well-definedness of d-hat.  Asserted library-phase
   over the concrete CSEQ/QUOTIENT/COMPLETION-DIST machinery; no missing
   primitive, the diagonal construction is the deferred tactic grind.")

;;; =======================================================================
;;; The isometric embedding M -> COMPLETION(M).
;;; =======================================================================

;; EMBED-SEQ(M,u) = the constant sequence  n |-> u  -- trivially Cauchy.
(def-functoid 'EMBED-SEQ '(M u)
  '(VNB-LAMBDA n NN u))

;; EMBED(M) = u |-> [constant sequence u] : PTS(M) -> PTS(COMPLETION(M)).
(def-functoid 'EMBED '(M)
  '(VNB-LAMBDA u (PTS M) (CLASS (CAUCHY-SETOID M) (EMBED-SEQ M u))))

;; embed-in-fun: EMBED(M) maps PTS(M) into the completion's carrier.
(support 'embed-in-fun
  '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IN (EMBED M) (FUN (PTS M) (PTS (COMPLETION M)))))))
(warrant! 'embed-in-fun 'well-known
  "The constant sequence at u is Cauchy (d(u,u)=0 < eps for all n), so it lies
   in CSEQ(M) and its class lies in QUOTIENT(CAUCHY-SETOID(M)) = PTS(COMPLETION M)
   (class-in-quotient).  EMBED(M) is total on PTS(M).")

;; embed-isometry: EMBED preserves distance -- d-hat(embed u, embed v) = d(u,v).
;; So M sits inside its completion isometrically.
(support 'embed-isometry
  '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (FORALL u (IMPLIES (IN u (PTS M))
       (FORALL v (IMPLIES (IN v (PTS M))
         (= ((DIST (COMPLETION M)) (EMBED M u) (EMBED M v))
            ((DIST M) u v)))))))))
(warrant! 'embed-isometry 'well-known
  "For constant sequences the real distance sequence n |-> d(u,v) is constant,
   so its limit is d(u,v) itself.  Hence d-hat([const u],[const v]) = d(u,v),
   exactly the isometry condition; EMBED is an isometric (in particular
   injective) embedding of M into COMPLETION(M).")

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'CSEQ-EQUIV 'kind 'predicate 'arity 3
           'english "$2 and $3 are equivalent Cauchy sequences in $1")
