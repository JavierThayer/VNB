;;; nsl.scm -- THE NEEDHAM-SCHROEDER-LOWE PROTOCOL ON THE USER'S STRAND MODEL: names, public keys,
;;; the initiator's and the responder's strands, NSL spaces.
;;; (Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf, section 5: the paper's Definition 5.1
;;;  and the term-algebra specialisation that precedes it; the model is docs/strand-spaces-2026-10-06.md
;;;  and the user's decisions of 2026-10-07 recorded in scratchpad/triage/S-3.md.)
;;; DEFINITIONS ONLY; the laws and the protocol's guarantees are PROVEN in theorem-library/nsl.scm.
;;; Agent S-3, 2026-10-07.  Binders: nl*_.
;;;
;;; THE PROTOCOL.
;;;     1. A -> B : {Na A}_KB          ENCR(LST([Na, A]), KB)
;;;     2. B -> A : {Na Nb B}_KA       ENCR(LST([Na, Nb, B]), KA)
;;;     3. A -> B : {Nb}_KB            ENCR(Nb, KB)        (a token under a key: the paper's term,
;;;                                                         not a one-element list; the user, 2026-10-07)
;;; B's private key is KINV(KB); "K_B^-1 is not in K_P" is (NOT (IN (KINV sp KB) (ADV-TOKENS isp))).
;;;
;;; NAMES AND PUBLIC KEYS (the paper: "a set of names Tname, a subset of T", and "a mapping
;;; K : Tname -> K ... we will assume that this function is injective").  A PUBLIC-KEY SPACE is
;;; a `declare-structure' refining INFILTRATED-SPACE the way INFILTRATED-SPACE refines
;;; STRAND-SPACE -- the refined structure is a SUBSTRUCTURE slot:
;;;     substructure  PK-INF   the infiltrated strand space (its space is ISPACE(PK-INF(nsp)))
;;;     carrier       NAMES    the principals' names
;;;     op            PUBKEY   in FUN(NAMES, KEYS(ISPACE(PK-INF)))   (the paper's K_A is PUBKEY(A))
;;;     law           every name is a TOKEN
;;;     law           NO NAME IS A KEY
;;;     law           PUBKEY is INJECTIVE
;;; Two of the laws are NOT the brief's, and both are the paper's:
;;;  * INJECTIVITY is used, by Proposition 5.2 (Lemma 5.7 reads A off K_A) and by Propositions
;;;    5.10, 5.13 (B off K_B).  The paper assumes it ("The protocol does not achieve its
;;;    authentication goals unless the mapping K is injective").
;;;  * NAMES ARE NOT KEYS, and neither are the nonces Na, Nb (a conjunct of the strand predicates
;;;    below).  The paper's names and nonces are TEXTS, members of T, and its T and K are
;;;    DISJOINT; in the user's model KEYS is a SUBSET of TOKENS, so the disjointness must be said.
;;;    Without it Proposition 5.2 is FALSE in the model: an initiator strand whose nonce Na' is
;;;    the private key KINV(K_A) of the responder's correspondent sends that key, under the public
;;;    key of a compromised name, and the adversary decrypts {Na Nb B}_KA with it (the D case of
;;;    Lemma 5.4 needs "K_A^-1 originates on no regular node", which the paper reads off the
;;;    shapes of the regular traces: "no initiator strand or responder strand originates K_A^-1").
;;;
;;; THE REGULAR STRANDS (Definition 5.1), PREDICATES ON A STRAND (a list of directed messages):
;;;   IS-INIT-STRAND(nsp, s, A, B, Na, Nb)  s = [[SENT, {Na A}_KB], [RECEIVED, {Na Nb B}_KA], [SENT, {Nb}_KB]]
;;;   IS-RESP-STRAND(nsp, s, A, B, Na, Nb)  s = [[RECEIVED, {Na A}_KB], [SENT, {Na Nb B}_KA], [RECEIVED, {Nb}_KB]]
;;; with A, B NAMES, Na, Nb TOKENS that are not KEYS, KA = PUBKEY(A), KB = PUBKEY(B), and
;;; Na not a name (initiator) / Nb not a name (responder), as the paper has it.  The paper's
;;; Init[A, B, Na, Nb] is the set of strand identifiers t with IS-INIT-STRAND(nsp, STRAND-MAP(t), ...).
;;;
;;; THE NSL SPACE (Definition 5.1: "Sigma is the union of three kinds of strands"):
;;;   IS-NSL-SPACE(nsp)  nsp is a public-key space and every strand identifier is an adversary
;;;                      identifier, or carries an initiator strand, or a responder strand, for
;;;                      SOME A, B, Na, Nb.
;;; A predicate, not a law of the structure: the strand predicates take the structure, so they
;;; are defined after it.  A REGULAR node (identifier not in ADV-IDS) therefore lies on an
;;; initiator or a responder strand.
;;;
;;; NOT DEFINED HERE, by design: "uniquely originating" is S-2's UNIQUELY-ORIGINATES(sp, u)
;;; (strand-spaces.scm: u originates on some node, and every node it originates on is that one),
;;; which is the brief's UNIQUELY-ORIGINATING word for word; a second name would be a duplicate.
;;; "C-height 3" for a strand t is written literally as (IN (LIST 3 t) (BNODES c)) (the first two
;;; nodes follow by bundle-ssb-closed).
;;;
;;; STATEMENT CHECKS.  (1) Nothing is asserted; three definitions and one structure.  (2) Every
;;; PUBKEY application is at a NAME (the strand predicates type A and B before the trace is read).
;;; (3) BINDERS: nl*_ names, used by no other body in the tree; none folds onto an accessor, a class
;;; name or a registered constant (a name A and a nonce a would fold: the binders are nla_, nlm_).
;;;
;;; Dependencies: strand-messages (LST, ENCR), strand-spaces (SENT, RECEIVED, STRAND-SPACE, KEYS,
;;; TOKENS, IDS, STRAND-MAP), strand-adversary (INFILTRATED-SPACE, ISPACE, ADV-IDS, ADV-TOKENS).

;;; -----------------------------------------------------------------------
;;; The public-key space.

(declare-structure PK-SPACE
  (instance-var s)
  (substructure PK-INF INFILTRATED-SPACE)
  (carriers NAMES)
  (op PUBKEY NAMES (KEYS (ISPACE PK-INF)))
  (law (FORALL nlx_ (IMPLIES (IN nlx_ (NAMES s)) (IN nlx_ (TOKENS (ISPACE (PK-INF s)))))))
  (law (FORALL nlx_ (IMPLIES (IN nlx_ (NAMES s)) (NOT (IN nlx_ (KEYS (ISPACE (PK-INF s))))))))
  (law (FORALL nlx_ (FORALL nly_ (IMPLIES (IN nlx_ (NAMES s)) (IMPLIES (IN nly_ (NAMES s))
         (IMPLIES (= ((PUBKEY s) nlx_) ((PUBKEY s) nly_)) (= nlx_ nly_))))))))

(notation! 'IS-PK-SPACE 'noun "public-key strand space" 'article "a")
(notation! 'IS-HOM-PK-SPACE 'kind 'predicate 'arity 3
           'english "$3 is a morphism of public-key strand spaces from $1 to $2")

;;; -----------------------------------------------------------------------
;;; The regular strands of the protocol.

(def-predicate 'IS-INIT-STRAND '(nlp_ nls_ nla_ nlb_ nlm_ nln_)
  '(AND (IN nla_ (NAMES nlp_))
   (AND (IN nlb_ (NAMES nlp_))
   (AND (IN nlm_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (IN nln_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (NOT (IN nlm_ (NAMES nlp_)))
   (AND (NOT (IN nlm_ (KEYS (ISPACE (PK-INF nlp_)))))
   (AND (NOT (IN nln_ (KEYS (ISPACE (PK-INF nlp_)))))
        (= nls_ (LIST (LIST SENT (ENCR (LST (LIST nlm_ nla_)) ((PUBKEY nlp_) nlb_)))
                      (LIST RECEIVED (ENCR (LST (LIST nlm_ nln_ nlb_)) ((PUBKEY nlp_) nla_)))
                      (LIST SENT (ENCR nln_ ((PUBKEY nlp_) nlb_)))))))))))))
(notation! 'IS-INIT-STRAND 'kind 'predicate 'arity 6
           'english "$2 is an initiator's strand of $1 for the names $3, $4 and the values $5, $6")

(def-predicate 'IS-RESP-STRAND '(nlp_ nls_ nla_ nlb_ nlm_ nln_)
  '(AND (IN nla_ (NAMES nlp_))
   (AND (IN nlb_ (NAMES nlp_))
   (AND (IN nlm_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (IN nln_ (TOKENS (ISPACE (PK-INF nlp_))))
   (AND (NOT (IN nln_ (NAMES nlp_)))
   (AND (NOT (IN nlm_ (KEYS (ISPACE (PK-INF nlp_)))))
   (AND (NOT (IN nln_ (KEYS (ISPACE (PK-INF nlp_)))))
        (= nls_ (LIST (LIST RECEIVED (ENCR (LST (LIST nlm_ nla_)) ((PUBKEY nlp_) nlb_)))
                      (LIST SENT (ENCR (LST (LIST nlm_ nln_ nlb_)) ((PUBKEY nlp_) nla_)))
                      (LIST RECEIVED (ENCR nln_ ((PUBKEY nlp_) nlb_)))))))))))))
(notation! 'IS-RESP-STRAND 'kind 'predicate 'arity 6
           'english "$2 is a responder's strand of $1 for the names $3, $4 and the values $5, $6")

;;; -----------------------------------------------------------------------
;;; The NSL space.

(def-predicate 'IS-NSL-SPACE '(nlp_)
  '(AND (IS-PK-SPACE nlp_)
        (FORALL nli_ (IMPLIES (IN nli_ (IDS (ISPACE (PK-INF nlp_))))
          (OR (IN nli_ (ADV-IDS (PK-INF nlp_)))
              (OR (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
                    (IS-INIT-STRAND nlp_ ((STRAND-MAP (ISPACE (PK-INF nlp_))) nli_) nla_ nlb_ nlm_ nln_)))))
                  (FORSOME nla_ (FORSOME nlb_ (FORSOME nlm_ (FORSOME nln_
                    (IS-RESP-STRAND nlp_ ((STRAND-MAP (ISPACE (PK-INF nlp_))) nli_) nla_ nlb_ nlm_ nln_)))))))))))
(notation! 'IS-NSL-SPACE 'kind 'predicate 'arity 1
           'english "$1 is a Needham-Schroeder-Lowe space")
