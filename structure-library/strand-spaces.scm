;;; strand-spaces.scm -- STRAND SPACES, NODES, BUNDLES ON THE USER'S MODEL
;;; (~/notes/notes-60.txt items (b)-(g); the user's decisions of 2026-10-06 recorded in
;;;  scratchpad/triage/WEEK3.md, section S-2; the paper's sections 2.1-2.4 supply the THEOREMS,
;;;  not the definitions: Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf.)
;;; DEFINITIONS ONLY; the laws are PROVEN in theorem-library/strand-space-laws.scm.
;;; Agent S-2 of the October roadmap, week 3, 2026-10-06; KEYS, KINV and the key parameter of the
;;; messages added by agent S-2b the same day (the user's decision of 16:40Z: encryption {m}_k as
;;; a third message case; S-2's version is archive/2026-10-06/s2b/strand-spaces.scm).  Messages,
;;; MSG-SET(T, K), IS-SUBTERM: structure-library/strand-messages.scm.  Binders carry the prefix ss-.
;;;
;;; DIRECTED MESSAGES (notes (c)).  A directed message is a list [dir, t], dir one of the two
;;; constants SENT and RECEIVED, t a message; its CONTENT is t.  SENT and RECEIVED are
;;; def-constants with the values 0 and 1 (a def-constant installs the defining equation as a
;;; theorem, `sent-def' / `received-def', so the two values are a citation away and the names
;;; print as words).  DIRECTED(T, K) = {SENT, RECEIVED} x MSG-SET(T, K), a CARTESIAN; DIR-OF and
;;; CONTENT-OF read the two components by NTH.
;;;
;;; STRANDS (notes (d)).  A strand is a list of directed messages:
;;; STRANDS(T, K) = TUPLES(DIRECTED(T, K)).
;;;
;;; THE STRAND SPACE (notes (d), "a mapping Sigma from agents to strands"; the user, 2026-10-06:
;;; the domain is a set of STRAND IDENTIFIERS, not agents).  A `declare-structure' with
;;;     carriers  TOKENS, IDS, KEYS
;;;     op        STRAND-MAP in FUN(IDS, STRANDS(TOKENS, KEYS))  (the user's Sigma)
;;;     op        KINV in FUN(KEYS, KEYS)                        (the paper's K^-1)
;;;     law       IS-TOKEN-SET(TOKENS)                           (tokens are not lists)
;;;     law       KEYS is a subset of TOKENS                     (a key is a token)
;;;     law       KINV(KINV(k)) = k for k in KEYS                (an involution)
;;; KEYS and KINV (S-2b): the paper's Definition 2.1 has the set K of keys with an injective inv
;;; mapping a member of an asymmetric pair to the other and a symmetric key to itself.  The law
;;; written is the involution (injectivity follows: kinv-injective); the symmetric keys are its
;;; fixpoints.  The accessor is KINV, not INV: INV is GROUP's slot and an accessor name denotes
;;; one slot everywhere (S-1 met the same clash).  KEYS inside TOKENS makes a key a message (a
;;; token), so the adversary can receive and send keys; ENCR(m, k) is a message for k in KEYS.
;;; The map is an `op' slot: a function from one carrier into a class built from the other is
;;; exactly what an op slot types, and the generated arrows (maps of tokens and identifiers
;;; commuting with the strand maps) are the natural ones.  The accessor is STRAND-MAP, not SIGMA:
;;; SIGMA is already the sigma-algebra slot of MEASURABLE-SPACE, and an accessor name denotes
;;; one slot everywhere.  The paper's non-injective trace map is several identifiers with equal
;;; strands; nothing here forbids that.
;;;
;;; NODES (notes (e)).  A node is a pair [k, a], k in NN, a in IDS, with 1 <= k <=
;;; LENGTH(Sigma(a)): NODES(sp) is that SEP of CARTESIAN(NN, IDS(sp)) (the user's order (k, a)).
;;; The user's "or undefined" was decided away (2026-10-06): CONTENT is read only on NODES, where
;;; it is TOTAL (a partial content would owe t = t at every instantiation under the LUTINS rule).
;;; INDEX-OF(n) = NTH(1, n) and ID-OF(n) = NTH(2, n) name the components; the BODIES below spell
;;; them as NTH 1 / NTH 2 so that unfolding a node predicate needs no second macete.
;;;     NODE-CONTENT(sp, n) = CONTENT-OF(NTH(INDEX-OF n, Sigma(ID-OF n)))
;;;     NODE-DIR(sp, n)     = DIR-OF(NTH(INDEX-OF n, Sigma(ID-OF n)))
;;; IS-SENT(sp, n) / IS-RECEIVED(sp, n): NODE-DIR(sp, n) is SENT / RECEIVED.
;;;
;;; THE TWO RELATIONS (notes (d), the user's `==>', and the edge `-->').
;;;   SAME-STRAND-BEFORE(sp, n, n')  both nodes, same identifier, INDEX(n) < INDEX(n')
;;;                                  -- the STRICT order: the user confirmed strictness (the
;;;                                  reflexive reading of notes (d) makes the entry-point clause
;;;                                  (g) contradictory: n ==> n would forbid CONTENT(n) in I).
;;;   SAME-STRAND-UPTO(sp, n, n')    the same with <=: the reflexive twin.
;;;   SENDS-TO(sp, n, n')            both nodes, n SENT, n' RECEIVED, equal contents (any two
;;;                                  strands, the same one included).
;;;   STRAND-NEXT(sp, n, n')         both nodes, same identifier, INDEX(n') = succ INDEX(n): the
;;;                                  bundle's NXT slot (the name NEXT is avoided: `next' is a
;;;                                  common driver-local name, and a registered constant may not be
;;;                                  spelled like a binder).
;;;
;;; OCCURRENCE AND ORIGINATION (notes (f), (g)).
;;;   OCCURS-IN-SPACE(sp, u)         u is a subterm of the content of some node.
;;;   IS-ENTRY-POINT(sp, n, I)       n is a node, SENT, CONTENT(n) in I, and CONTENT(n') notin I
;;;                                  for every n' ==> n (strict).  I is a set of UNDIRECTED
;;;                                  messages and CONTENT is undirected: the paper's clause 6
;;;                                  compared a SIGNED term with I (finding (a) of S-2).
;;;   ORIGINATES(sp, u, n)           n is an entry point into {m in MSG-SET(TOKENS, KEYS) : u @ m}.
;;;   UNIQUELY-ORIGINATES(sp, u)     u originates on exactly one node.
;;;
;;; BUNDLES (the paper's Definition 2.4 on the user's relations).  A `declare-structure' with
;;;     substructure BSPACE  a STRAND-SPACE (the space the bundle lives in)
;;;     carrier      BNODES  the bundle's nodes
;;;     relation     BSEND   on BNODES: the bundle's --> edges
;;;     relation     BNEXT   on BNODES: the bundle's => edges
;;; and the laws:
;;;   (1) every member of BNODES is a node of BSPACE;
;;;   (2) CARD(BNODES) in NN (the paper: "C is finite");
;;;   (3) every pair in BSEND satisfies SENDS-TO; (4) every pair in BNEXT satisfies STRAND-NEXT;
;;;   (5) every RECEIVED node of BNODES has EXACTLY ONE BSEND-predecessor (the paper's "unique";
;;;       carried as the paper has it -- see the laws file for where uniqueness is used);
;;;   (6) CLOSED UNDER ==>: if n in BNODES and n' ==> n then n' in BNODES -- ONE clause, since
;;;       ==> is the whole strict same-strand order; the paper's "apply clause 3 as many times as
;;;       necessary" in the proof of its Lemma 2.9 dissolves (finding (b));
;;;   (7) [n', n] in BNEXT whenever n in BNODES and STRAND-NEXT(n', n) (the paper's clause 3);
;;;   (8) ACYCLIC: no [n, n] in the strict causal precedence.
;;; The space is a SUBSTRUCTURE slot rather than a parameter: a bundle is an object (the user's
;;; standing rule: a structure is a declare-structure), every later statement quantifies over one
;;; c, and IS-BUNDLE(c) carries IS-STRAND-SPACE(BSPACE c).  BNODES, not NODES: NODES(sp) is the
;;; space's node set.
;;;
;;; CAUSAL PRECEDENCE (design decision 4: the intersection closure, S-1's device).  On loose data
;;; (sp, N, S) -- a space, a set of nodes, a set of send edges:
;;;   IS-PREC-CLOSED(sp, N, S, r)  r holds every pair of S, every [x, y] with x, y in N and
;;;                                x ==> y, and is transitive;
;;;   PREC-STRICT(sp, N, S)        the pairs of N x N in every closed r in POWER(N x N);
;;; and on a bundle c:
;;;   PRECEDES-STRICT(c) = PREC-STRICT(BSPACE c, BNODES c, BSEND c)   (the paper's "<")
;;;   PRECEDES(c)        = PRECEDES-STRICT(c) u the identity on BNODES(c)  (the paper's "<=")
;;; PREC-STRICT is stated on loose data because the acyclicity law (8) must name it BEFORE the
;;; structure exists.  The generator is BSEND u (==> on BNODES), NOT BSEND u BNEXT: the user's
;;; ==> is already transitive, and the two generate the same closure (BNEXT is inside ==> by
;;; law (4); each ==> pair is a chain of BNEXT steps by law (7) -- a chain the paper never
;;; needs once ==> is in the generator).
;;;
;;; STATEMENT CHECKS.  (1) Every equation here is a definition; nothing is asserted.  (2) No
;;; index untyped: NODES carries 1 <= k <= LENGTH, and k, a are typed by the CARTESIAN.
;;; (3) BINDERS: ss*_ names, used by no other body in the tree; none folds onto an accessor, a
;;; class name or a registered constant.
;;;
;;; Dependencies: structure-library/strand-messages (MSG-SET, IS-SUBTERM, IS-TOKEN-SET),
;;; structures.scm (declare-structure), cardinality (CARD).  No proof is cited.

;;; -----------------------------------------------------------------------
;;; Directed messages and strands.

;; (No notation! for the two constants: notation! on a head def-constant did not register as an
;; operator would re-register it as a `primitive'; the printer reads them as "sent", "received".)
(def-constant 'SENT '(sent-def (= SENT 0)))
(def-constant 'RECEIVED '(received-def (= RECEIVED 1)))

(def-functoid 'DIRECTED '(sst_ ssk_) '(CARTESIAN (PAIR SENT RECEIVED) (MSG-SET sst_ ssk_)))
(notation! 'DIRECTED 'kind 'functoid 'arity 2
           'english "the directed messages over the tokens $1 and the keys $2")

(def-functoid 'DIR-OF '(ssd_) '(NTH 1 ssd_))
(notation! 'DIR-OF 'kind 'functoid 'arity 1 'english "the direction of the directed message $1")

(def-functoid 'CONTENT-OF '(ssd_) '(NTH 2 ssd_))
(notation! 'CONTENT-OF 'kind 'functoid 'arity 1 'english "the content of the directed message $1")

(def-functoid 'STRANDS '(sst_ ssk_) '(TUPLES (DIRECTED sst_ ssk_)))
(notation! 'STRANDS 'kind 'functoid 'arity 2 'english "the strands over the tokens $1 and the keys $2")

;;; -----------------------------------------------------------------------
;;; The strand space.

(declare-structure STRAND-SPACE
  (instance-var s)
  (carriers TOKENS IDS KEYS)
  (op STRAND-MAP IDS (STRANDS TOKENS KEYS))
  (op KINV KEYS KEYS)
  (law (IS-TOKEN-SET (TOKENS s)))
  (law (FORALL ssx_ (IMPLIES (IN ssx_ (KEYS s)) (IN ssx_ (TOKENS s)))))
  (law (FORALL ssx_ (IMPLIES (IN ssx_ (KEYS s)) (= ((KINV s) ((KINV s) ssx_)) ssx_)))))

(notation! 'IS-STRAND-SPACE 'noun "strand space" 'article "a")
(notation! 'IS-HOM-STRAND-SPACE 'kind 'predicate 'arity 3
           'english "$3 is a morphism of strand spaces from $1 to $2")

;;; -----------------------------------------------------------------------
;;; Nodes.

(def-functoid 'NODES '(ssp_)
  '(SEP ssn_ (CARTESIAN NN (IDS ssp_))
        (AND (<= 1 (NTH 1 ssn_))
             (<= (NTH 1 ssn_) (LENGTH ((STRAND-MAP ssp_) (NTH 2 ssn_)))))))
(notation! 'NODES 'kind 'functoid 'arity 1 'english "the nodes of the strand space $1")

(def-functoid 'INDEX-OF '(ssn_) '(NTH 1 ssn_))
(notation! 'INDEX-OF 'kind 'functoid 'arity 1 'english "the index of the node $1")

(def-functoid 'ID-OF '(ssn_) '(NTH 2 ssn_))
(notation! 'ID-OF 'kind 'functoid 'arity 1 'english "the strand identifier of the node $1")

(def-functoid 'NODE-CONTENT '(ssp_ ssn_)
  '(NTH 2 (NTH (NTH 1 ssn_) ((STRAND-MAP ssp_) (NTH 2 ssn_)))))
(notation! 'NODE-CONTENT 'kind 'functoid 'arity 2
           'english "the content of the node $2 of $1")

(def-functoid 'NODE-DIR '(ssp_ ssn_)
  '(NTH 1 (NTH (NTH 1 ssn_) ((STRAND-MAP ssp_) (NTH 2 ssn_)))))
(notation! 'NODE-DIR 'kind 'functoid 'arity 2
           'english "the direction of the node $2 of $1")

(def-predicate 'IS-SENT '(ssp_ ssn_) '(= (NODE-DIR ssp_ ssn_) SENT))
(notation! 'IS-SENT 'kind 'predicate 'arity 2 'english "the node $2 of $1 is sent")

(def-predicate 'IS-RECEIVED '(ssp_ ssn_) '(= (NODE-DIR ssp_ ssn_) RECEIVED))
(notation! 'IS-RECEIVED 'kind 'predicate 'arity 2 'english "the node $2 of $1 is received")

;;; -----------------------------------------------------------------------
;;; The relations on nodes.

(def-predicate 'SAME-STRAND-BEFORE '(ssp_ ssn_ ssm_)
  '(AND (IN ssn_ (NODES ssp_))
        (AND (IN ssm_ (NODES ssp_))
             (AND (= (NTH 2 ssn_) (NTH 2 ssm_))
                  (< (NTH 1 ssn_) (NTH 1 ssm_))))))
(notation! 'SAME-STRAND-BEFORE 'kind 'predicate 'arity 3
           'english "$2 comes strictly before $3 on one strand of $1")

(def-predicate 'SAME-STRAND-UPTO '(ssp_ ssn_ ssm_)
  '(AND (IN ssn_ (NODES ssp_))
        (AND (IN ssm_ (NODES ssp_))
             (AND (= (NTH 2 ssn_) (NTH 2 ssm_))
                  (<= (NTH 1 ssn_) (NTH 1 ssm_))))))
(notation! 'SAME-STRAND-UPTO 'kind 'predicate 'arity 3
           'english "$2 comes at or before $3 on one strand of $1")

(def-predicate 'SENDS-TO '(ssp_ ssn_ ssm_)
  '(AND (IN ssn_ (NODES ssp_))
        (AND (IN ssm_ (NODES ssp_))
             (AND (IS-SENT ssp_ ssn_)
                  (AND (IS-RECEIVED ssp_ ssm_)
                       (= (NODE-CONTENT ssp_ ssn_) (NODE-CONTENT ssp_ ssm_)))))))
(notation! 'SENDS-TO 'kind 'predicate 'arity 3 'english "the node $2 of $1 sends to the node $3")

(def-predicate 'STRAND-NEXT '(ssp_ ssn_ ssm_)
  '(AND (IN ssn_ (NODES ssp_))
        (AND (IN ssm_ (NODES ssp_))
             (AND (= (NTH 2 ssn_) (NTH 2 ssm_))
                  (= (NTH 1 ssm_) (succ (NTH 1 ssn_)))))))
(notation! 'STRAND-NEXT 'kind 'predicate 'arity 3
           'english "$3 immediately follows $2 on one strand of $1")

;;; -----------------------------------------------------------------------
;;; Occurrence and origination.

(def-predicate 'OCCURS-IN-SPACE '(ssp_ ssu_)
  '(FORSOME ssn_ (AND (IN ssn_ (NODES ssp_))
                      (IS-SUBTERM (TOKENS ssp_) (KEYS ssp_) ssu_ (NODE-CONTENT ssp_ ssn_)))))
(notation! 'OCCURS-IN-SPACE 'kind 'predicate 'arity 2 'english "$2 occurs in the strand space $1")

(def-predicate 'IS-ENTRY-POINT '(ssp_ ssn_ ssi_)
  '(AND (IN ssn_ (NODES ssp_))
        (AND (IS-SENT ssp_ ssn_)
             (AND (IN (NODE-CONTENT ssp_ ssn_) ssi_)
                  (FORALL ssm_ (IMPLIES (SAME-STRAND-BEFORE ssp_ ssm_ ssn_)
                                        (NOT (IN (NODE-CONTENT ssp_ ssm_) ssi_))))))))
(notation! 'IS-ENTRY-POINT 'kind 'predicate 'arity 3
           'english "the node $2 of $1 is an entry point into $3")

(def-predicate 'ORIGINATES '(ssp_ ssu_ ssn_)
  '(IS-ENTRY-POINT ssp_ ssn_
     (SEP ssw_ (MSG-SET (TOKENS ssp_) (KEYS ssp_)) (IS-SUBTERM (TOKENS ssp_) (KEYS ssp_) ssu_ ssw_))))
(notation! 'ORIGINATES 'kind 'predicate 'arity 3 'english "$2 originates on the node $3 of $1")

(def-predicate 'UNIQUELY-ORIGINATES '(ssp_ ssu_)
  '(FORSOME ssn_ (AND (ORIGINATES ssp_ ssu_ ssn_)
                      (FORALL ssm_ (IMPLIES (ORIGINATES ssp_ ssu_ ssm_) (= ssm_ ssn_))))))
(notation! 'UNIQUELY-ORIGINATES 'kind 'predicate 'arity 2
           'english "$2 originates uniquely in the strand space $1")

;;; -----------------------------------------------------------------------
;;; Causal precedence on loose data.

(def-predicate 'IS-PREC-CLOSED '(spc_ snd_ ssd_ srl_)
  '(AND (FORALL ssx_ (FORALL ssy_ (IMPLIES (IN (LIST ssx_ ssy_) ssd_) (IN (LIST ssx_ ssy_) srl_))))
        (AND (FORALL ssx_ (IMPLIES (IN ssx_ snd_) (FORALL ssy_ (IMPLIES (IN ssy_ snd_)
               (IMPLIES (SAME-STRAND-BEFORE spc_ ssx_ ssy_) (IN (LIST ssx_ ssy_) srl_))))))
             (FORALL ssx_ (FORALL ssy_ (FORALL ssz_
               (IMPLIES (IN (LIST ssx_ ssy_) srl_) (IMPLIES (IN (LIST ssy_ ssz_) srl_)
                 (IN (LIST ssx_ ssz_) srl_)))))))))
(notation! 'IS-PREC-CLOSED 'kind 'predicate 'arity 4
           'english "$4 contains $3 and the strand order of $1 on $2, and is transitive")

(def-functoid 'PREC-STRICT '(spc_ snd_ ssd_)
  '(SEP ssp_ (CARTESIAN snd_ snd_)
        (FORALL ssq_ (IMPLIES (IN ssq_ (POWER (CARTESIAN snd_ snd_)))
                              (IMPLIES (IS-PREC-CLOSED spc_ snd_ ssd_ ssq_) (IN ssp_ ssq_))))))
(notation! 'PREC-STRICT 'kind 'functoid 'arity 3
           'english "the strict causal precedence on the nodes $2 of $1 generated by the edges $3")

;;; -----------------------------------------------------------------------
;;; Bundles.

(declare-structure BUNDLE
  (instance-var s)
  (substructure BSPACE STRAND-SPACE)
  (carriers BNODES)
  (relation BSEND BNODES)
  (relation BNEXT BNODES)
  (law (FORALL ssx_ (IMPLIES (IN ssx_ (BNODES s)) (IN ssx_ (NODES (BSPACE s))))))
  (law (IN (CARD (BNODES s)) NN))
  (law (FORALL ssx_ (FORALL ssy_ (IMPLIES (IN (LIST ssx_ ssy_) (BSEND s)) (SENDS-TO (BSPACE s) ssx_ ssy_)))))
  (law (FORALL ssx_ (FORALL ssy_ (IMPLIES (IN (LIST ssx_ ssy_) (BNEXT s)) (STRAND-NEXT (BSPACE s) ssx_ ssy_)))))
  (law (FORALL ssy_ (IMPLIES (IN ssy_ (BNODES s)) (IMPLIES (IS-RECEIVED (BSPACE s) ssy_)
         (FORSOME ssx_ (AND (IN (LIST ssx_ ssy_) (BSEND s))
                            (FORALL ssz_ (IMPLIES (IN (LIST ssz_ ssy_) (BSEND s)) (= ssz_ ssx_)))))))))
  (law (FORALL ssy_ (IMPLIES (IN ssy_ (BNODES s))
         (FORALL ssx_ (IMPLIES (SAME-STRAND-BEFORE (BSPACE s) ssx_ ssy_) (IN ssx_ (BNODES s)))))))
  (law (FORALL ssy_ (IMPLIES (IN ssy_ (BNODES s))
         (FORALL ssx_ (IMPLIES (STRAND-NEXT (BSPACE s) ssx_ ssy_) (IN (LIST ssx_ ssy_) (BNEXT s)))))))
  (law (FORALL ssx_ (NOT (IN (LIST ssx_ ssx_) (PREC-STRICT (BSPACE s) (BNODES s) (BSEND s)))))))

(notation! 'IS-BUNDLE 'noun "bundle" 'article "a")

(def-functoid 'PRECEDES-STRICT '(ssc_) '(PREC-STRICT (BSPACE ssc_) (BNODES ssc_) (BSEND ssc_)))
(notation! 'PRECEDES-STRICT 'kind 'functoid 'arity 1
           'english "the strict causal precedence of the bundle $1")

(def-functoid 'PRECEDES '(ssc_)
  '(UNION (PRECEDES-STRICT ssc_)
          (SEP ssp_ (CARTESIAN (BNODES ssc_) (BNODES ssc_)) (= (NTH 1 ssp_) (NTH 2 ssp_)))))
(notation! 'PRECEDES 'kind 'functoid 'arity 1 'english "the causal precedence of the bundle $1")
