;;; strand-messages.scm -- THE MESSAGE ALGEBRA OF STRAND SPACES
;;; (Thayer, Herzog, Guttman, "Strand Spaces: Proving Security Protocols Correct",
;;;  ~/docs/jcs_strand_spaces.pdf, sections 2.3 and 2.4: texts, keys, inv, join, encr,
;;;  Axioms 1 and 2, Definition 2.11.)
;;; DEFINITIONS ONLY; every law is PROVEN in theorem-library/strand-messages-laws.scm.
;;; Agent S-1 of the October roadmap, week 3, 2026-10-04.  The design is
;;; docs/strand-spaces-design-2026-10-03.md (the user's decisions 1-5 of 2026-10-04).
;;;
;;; THE DECISION (design decision 1): the message algebra is BUILT, not axiomatised.
;;; The paper ASSUMES a set A with T, K inside it and two operators satisfying the
;;; freeness Axioms 1 and 2.  Here A is CONSTRUCTED from two given sets T (texts) and
;;; K (keys) as an inductive set of TAGGED LISTS, and Axioms 1 and 2 become THEOREMS:
;;;
;;;     ATOM(a)    = [0, a]       the atom a, for a in T u K
;;;     CAT(g, h)  = [1, g, h]    the concatenation (the paper's join, written g h)
;;;     ENC(g, k)  = [2, g, k]    the encryption {g}_k, for k in K
;;;
;;;     MSG-STAGE(T, K, 0)       = {0} x (T u K)
;;;     MSG-STAGE(T, K, succ n)  = A_n  u  ({1} x A_n x A_n)  u  ({2} x A_n x K)
;;;                                (A_n = MSG-STAGE(T, K, n)), by def-by-nn-recursion
;;;     MSG-SET(T, K)            = the union over n in NN of MSG-STAGE(T, K, n)
;;;
;;; The products are the tree's n-ary CARTESIAN, whose membership is the primitive
;;; `cartesian-decompose' schema: m in {1} x A_n x A_n iff m = [1, g, h] with g, h in A_n.
;;; So no SEP over triples is ever formed (the tree cannot form one), and each stage is
;;; a SET when T and K are (the ternary product's sethood is a THEOREM of the laws file,
;;; `cartesian3-set', by replacement over the binary product).
;;;
;;; ATOMS AND KEYS.  In the paper T and K are SUBSETS of A; here the message of a text
;;; or key a is the tagged atom ATOM(a) = [0, a], and an encryption carries the RAW key:
;;; ENC(g, k) = [2, g, k] with k in K, not [2, g, ATOM(k)].  Nothing is lost: the key k
;;; as a MESSAGE is ATOM(k), and the subterm relation below reaches ATOM(k) inside
;;; ENC(g, k) only through g, which is exactly the paper's remark after Definition 2.11
;;; ("K is a subterm of {g}_K only if K is a subterm of g").
;;;
;;; SETS OF SETS.  A list is DEFINED iff its components are sets (the list rule of
;;; 2026-10-01, docs/decisions-pending-2026-10-01.md).  Every element of a set is a set
;;; (`membership-implies-sethood'), so for sets T and K every [0, a] with a in T u K and
;;; every [2, g, k] with k in K denotes; T and K are sets OF SETS by the mere fact of
;;; being sets, and the numerals 0, 1, 2 are sets as members of NN.  The laws carry
;;; `T in SET' and `K in SET' only where SETHOOD of a stage or of A is used; the
;;; membership characterisations of the stages need neither.
;;;
;;; THE STRUCTURE (design 2.1): MESSAGE-ALGEBRA packages the parameters so that later
;;; statements quantify over ONE object alg:
;;;     carriers TEXTS, KEYS;  op KINV in FUN(KEYS, KEYS);
;;;     derived  MSGS = MSG-SET(TEXTS, KEYS)  (pinned by IS-MESSAGE-ALGEBRA; a derived
;;;              slot owes a homomorphism nothing, and the generated arrows of this
;;;              structure are not the point -- design 2.1);
;;;     law      TEXTS and KEYS are DISJOINT (the paper: "a set K ... disjoint from T");
;;;     law      KINV is an INVOLUTION on KEYS.
;;; The accessor is KINV, not INV: INV is GROUP's slot 4 and an accessor name denotes
;;; one slot index everywhere (CLAUDE.md, structures).  THE INVOLUTION LAW IS A
;;; DECISION, NOT A TRANSCRIPTION: the paper says inv is INJECTIVE, maps each member of
;;; an asymmetric key pair to the other and a symmetric key to itself.  Read literally
;;; that is a description of the intended model, not an axiom; the axiom it implies is
;;; inv(inv(k)) = k (and injectivity follows from it).  Stated as a law of the
;;; structure; `kinv-involution' and `kinv-injective' are its consequences.
;;; The free algebra depends on T and K only; KINV is extra structure, used first by
;;; the penetrator's decryption strand (S-3).  So the algebra's laws are stated over
;;; two SETS (T, K), and over alg through the one equation MSGS(alg) = MSG-SET(...).
;;;
;;; THE SUBTERM RELATION (Definition 2.11, "the smallest relation such that a @ a;
;;; a @ {g}_K if a @ g; a @ g h if a @ g or a @ h").  Defined as the INTERSECTION of
;;; the closed relations -- the device the design note prescribes for causal precedence
;;; (decision 4), chosen here for the same reasons: one definition, minimality is one
;;; citation, and the induction principle it gives (`subterm-least') is the one every
;;; inversion needs.  The relations range over SUBSETS of A x A (members of
;;; POWER(A x A)), which is what makes the intersection a set and lets a proof
;;; instantiate the family at a SEP of SUBTERM-REL itself.  The alternative, recursion
;;; on the rank of the right-hand side, would need a recursion over A whose value at a
;;; message is a SET OF MESSAGES -- a well-founded recursion the tree does not have
;;; (def-by-nn-recursion recurs on NN, not on A).
;;;
;;;     IS-SUBTERM-CLOSED(T, K, r)   r contains [a, a] for a in A, [a, ENC(g, k)] when
;;;                                  [a, g] in r and k in K, [a, CAT(g, h)] when [a, g]
;;;                                  in r and h in A, and when [a, h] in r and g in A
;;;     SUBTERM-REL(T, K)            { p in A x A : p in r for every closed r in POWER(A x A) }
;;;     IS-SUBTERM(T, K, a, b)       [a, b] in SUBTERM-REL(T, K)    (the paper's a @ b)
;;;
;;; THE RANK (design 2.1): MSG-RANK(T, K, m) is the least stage index containing m,
;;; as an IOTA over NN.  It denotes for every m in A (`msg-rank-prop' and its
;;; siblings); off A the description has no witness and the term does not denote.
;;;
;;; STATEMENT CHECKS (CLAUDE.md, the species of false or underdetermined support).
;;; (1) Every equation here is a definition (def-functoid, def-predicate, the two
;;;     recursion equations of def-by-nn-recursion as `==').  Nothing is asserted.
;;; (2) No index is left untyped: MSG-STAGE is read only at n in NN (its succ equation
;;;     is guarded so); MSG-SET quantifies the stage index over NN.
;;; (3) IOTA in MSG-RANK: its existence-and-uniqueness obligation is discharged in the
;;;     laws file for m in A; nothing here asserts that it denotes.
;;; (4) BINDERS: every parameter and bound variable is an sm*_ name, used by no other
;;;     body or driver in the tree; none folds onto a class name, an accessor or a
;;;     registered constant.  The structure's laws use smx_ / smy_ beside the
;;;     structure variable s.
;;;
;;; Dependencies: ordinals.scm (def-by-nn-recursion), structures.scm (declare-structure),
;;; the base theory (CARTESIAN, UNION, PAIR, BIG-UNION, POWER, SEP, IOTA, LIST).  Load
;;; slot: anywhere after structure-library/ordinals and structures (no proof is cited).

;;; -----------------------------------------------------------------------
;;; The three constructors.

(def-functoid 'ATOM '(sma_) '(LIST 0 sma_))
(notation! 'ATOM 'kind 'functoid 'arity 1 'english "the atomic message $1")

(def-functoid 'CAT '(smg_ smh_) '(LIST 1 smg_ smh_))
(notation! 'CAT 'kind 'functoid 'arity 2 'english "the concatenation of $1 and $2")

(def-functoid 'ENC '(smg_ smk_) '(LIST 2 smg_ smk_))
(notation! 'ENC 'kind 'functoid 'arity 2 'english "the encryption of $1 under the key $2")

;;; -----------------------------------------------------------------------
;;; The stages and the message set.

(def-by-nn-recursion 'MSG-STAGE '(smt_ smk_)
  '(CARTESIAN (PAIR 0 0) (UNION smt_ smk_))
  '(smn_ smv_)
  '(UNION smv_ (UNION (CARTESIAN (PAIR 1 1) smv_ smv_)
                      (CARTESIAN (PAIR 2 2) smv_ smk_))))
(notation! 'MSG-STAGE 'kind 'functoid 'arity 3
           'english "the stage $3 of the messages over the texts $1 and the keys $2")

(def-functoid 'MSG-SET '(smt_ smk_) '(BIG-UNION smn_ NN (MSG-STAGE smt_ smk_ smn_)))
(notation! 'MSG-SET 'kind 'functoid 'arity 2
           'english "the messages over the texts $1 and the keys $2")

;;; The least stage containing a message.
(def-functoid 'MSG-RANK '(smt_ smk_ smm_)
  '(IOTA smr_ (AND (IN smr_ NN)
                   (AND (IN smm_ (MSG-STAGE smt_ smk_ smr_))
                        (FORALL smj_ (IMPLIES (IN smj_ NN)
                                              (IMPLIES (IN smm_ (MSG-STAGE smt_ smk_ smj_))
                                                       (<= smr_ smj_))))))))
(notation! 'MSG-RANK 'kind 'functoid 'arity 3
           'english "the rank of the message $3 over the texts $1 and the keys $2")

;;; -----------------------------------------------------------------------
;;; The subterm relation (Definition 2.11).

(def-predicate 'IS-SUBTERM-CLOSED '(smt_ smk_ smr_)
  '(AND (FORALL sma_ (IMPLIES (IN sma_ (MSG-SET smt_ smk_)) (IN (LIST sma_ sma_) smr_)))
   (AND (FORALL sma_ (FORALL smg_ (FORALL smy_
          (IMPLIES (IN (LIST sma_ smg_) smr_)
                   (IMPLIES (IN smy_ smk_) (IN (LIST sma_ (ENC smg_ smy_)) smr_))))))
   (AND (FORALL sma_ (FORALL smg_ (FORALL smh_
          (IMPLIES (IN (LIST sma_ smg_) smr_)
                   (IMPLIES (IN smh_ (MSG-SET smt_ smk_)) (IN (LIST sma_ (CAT smg_ smh_)) smr_))))))
        (FORALL sma_ (FORALL smg_ (FORALL smh_
          (IMPLIES (IN (LIST sma_ smh_) smr_)
                   (IMPLIES (IN smg_ (MSG-SET smt_ smk_)) (IN (LIST sma_ (CAT smg_ smh_)) smr_))))))))))
(notation! 'IS-SUBTERM-CLOSED 'kind 'predicate 'arity 3
           'english "$3 is closed under the subterm clauses over the texts $1 and the keys $2")

(def-functoid 'SUBTERM-REL '(smt_ smk_)
  '(SEP smp_ (CARTESIAN (MSG-SET smt_ smk_) (MSG-SET smt_ smk_))
        (FORALL smq_ (IMPLIES (IN smq_ (POWER (CARTESIAN (MSG-SET smt_ smk_) (MSG-SET smt_ smk_))))
                              (IMPLIES (IS-SUBTERM-CLOSED smt_ smk_ smq_) (IN smp_ smq_))))))
(notation! 'SUBTERM-REL 'kind 'functoid 'arity 2
           'english "the subterm relation over the texts $1 and the keys $2")

(def-predicate 'IS-SUBTERM '(smt_ smk_ sma_ smb_) '(IN (LIST sma_ smb_) (SUBTERM-REL smt_ smk_)))
(notation! 'IS-SUBTERM 'kind 'predicate 'arity 4
           'english "$3 is a subterm of $4 over the texts $1 and the keys $2")

;;; -----------------------------------------------------------------------
;;; The structure.

(declare-structure MESSAGE-ALGEBRA
  (instance-var s)
  (carriers TEXTS KEYS)
  (op KINV KEYS KEYS)
  (derived MSGS TEXTS (MSG-SET TEXTS KEYS))
  (law (FORALL smx_ (IMPLIES (IN smx_ (TEXTS s)) (NOT (IN smx_ (KEYS s))))))
  (law (FORALL smy_ (IMPLIES (IN smy_ (KEYS s)) (= ((KINV s) ((KINV s) smy_)) smy_)))))

(notation! 'IS-MESSAGE-ALGEBRA 'noun "message algebra" 'article "a")
;; the generated arrows (an op-preserving map of the carriers; irrelevant to the
;; strand-space development, declared so that every predicate reads as English)
(notation! 'IS-HOM-MESSAGE-ALGEBRA 'kind 'predicate 'arity 3
           'english "$3 is a homomorphism of message algebras from $1 to $2")
