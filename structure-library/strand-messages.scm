;;; strand-messages.scm -- THE MESSAGES OF STRAND SPACES, ON THE USER'S MODEL, WITH ENCRYPTION
;;; (~/notes/notes-60.txt, item (a): "Let T be a set of tokens.  A message is a nested list of
;;;  tokens, i.e. a token is a message and any list of messages is a message.  Subterms are
;;;  defined recursively in the obvious way."  The user, 2026-10-06 16:40Z: "one more message
;;;  case beside tokens and lists -- {m}_k under a key token, disjoint from both by the token
;;;  law's device ... {m}_k = encr{m,k} is also a message.")
;;; DEFINITIONS ONLY; every law is PROVEN in theorem-library/strand-messages-laws.scm.
;;; Agent S-2 of the October roadmap, week 3, 2026-10-06; ENCRYPTION added by agent S-2b the
;;; same day.  S-1's algebra of the paper (ATOM / CAT / ENC) is archive/2026-10-06/
;;; strand-messages.scm; S-2's key-free version is archive/2026-10-06/s2b/strand-messages.scm.
;;;
;;; THE THREE CASES.  A message over the tokens T and the keys K is
;;;     a TOKEN t in T,
;;;     a LIST  LST(l)     = [1, l]     of a list l of messages,
;;;     an ENCRYPTION ENCR(m, k) = [2, m, k]  of a message m under a key k in K.
;;; The recursion on messages (subterm, rank, induction) needs the three cases pairwise
;;; DISJOINT, and in VNB every list is a set:
;;;  * TOKENS vs the rest -- THE TOKEN LAW (S-2's device, kept): IS-TOKEN-SET(T) says T is a set
;;;    and no member of T is in TUPLES(SET).  TUPLES(SET) is the class of all lists with set
;;;    components, i.e. (list rule of 2026-10-01) of all DEFINED lists, so "x notin TUPLES(SET)"
;;;    is the kernel-admissible spelling of "x is not a list".  LST(l) and ENCR(m, k) are literal
;;;    lists with set components, so the law separates tokens from both.  (The tree cannot prove
;;;    that any particular set satisfies the law: TUPLES has no characterisation beyond its
;;;    generation axioms.  The law is a hypothesis on T, carried by STRAND-SPACE.)
;;;  * LISTS vs ENCRYPTIONS -- TAGS, the token law's device one level down.  Both are lists as
;;;    sets, so a LAW cannot separate them (they are constructed, not given); the first entry
;;;    does: NTH(1, LST(l)) = 1 and NTH(1, ENCR(m, k)) = 2, and 1 /= 2 is arithmetic.  This
;;;    is S-1's device (CAT = [1, g, h], ENC = [2, g, k]).  No device keeping PLAIN lists was
;;;    found: an untagged encryption would have to be a set that is provably not a list of
;;;    messages, and "x notin TUPLES(A)" is unprovable for any particular x, which is exactly
;;;    why the token law had to be a law.  So S-2's plain lists became tagged lists: "l is a list
;;;    of messages" is still l in TUPLES(MSG-SET(T, K)), and the MESSAGE it makes is LST(l).
;;;  * KEYS.  ENCR(m, k) is a message only for k in K.  The key is carried RAW (k, not a message
;;;    built from it); in a strand space K is the carrier KEYS, a subset of TOKENS, so a key is
;;;    also a token and, as such, a message.  The inverse of a key (the paper's K^-1) is not
;;;    part of the message algebra: it is the op KINV of STRAND-SPACE (strand-spaces.scm).
;;;
;;; THE MESSAGES.  Stage 0 is T; stage n+1 adds every LST of a list of stage-n messages and
;;; every ENCR of a stage-n message under a key:
;;;
;;;     MSG-STAGE(T, K, 0)      = T
;;;     MSG-STAGE(T, K, succ n) = S_n  u  ({1} x TUPLES(S_n))  u  ({2} x S_n x K)
;;;                               (S_n = MSG-STAGE(T, K, n); def-by-nn-recursion)
;;;     MSG-SET(T, K)           = the union over n in NN of MSG-STAGE(T, K, n)
;;;
;;; The products are the tree's n-ary CARTESIAN (membership: the primitive
;;; `cartesian-decompose'); {1} is PAIR(1, 1).  The ternary product is a set by replacement
;;; (`cartesian3-set', S-1's proof, in the laws file), so every stage is a SET when T and K are.
;;;
;;; THE SUBTERM RELATION, as the INTERSECTION of the closed relations (S-1's device): a relation
;;; r on A = MSG-SET(T, K) is closed when
;;;     (i)   [a, a] in r for every message a ("a message is a subterm of itself");
;;;     (ii)  [a, LST(l)] in r whenever l is a list of messages, 1 <= i <= LENGTH(l) and
;;;           [a, NTH(i, l)] in r ("a subterm of a component is a subterm of the list");
;;;     (iii) [a, ENCR(g, k)] in r whenever g is a message, k in K and [a, g] in r ("a subterm of
;;;           the plaintext is a subterm of the encryption").
;;; THE KEY IS NOT A SUBTERM OF THE ENCRYPTION (the paper's Definition 2.11 and its remark: "K @
;;; {g}_K only if K @ g already"): no clause puts k, or anything of k, below ENCR(g, k).  A
;;; secret used only as a key therefore does not "occur" in the messages encrypted under it,
;;; which is what makes "t never originates on a regular node => t occurs nowhere" sound in the
;;; presence of the adversary's encryption trace.  THIS CONVENTION IS A DECISION FOR THE USER TO
;;; CONFIRM (it is the paper's, not yet stated in his notes).
;;; SUBTERM-REL(T, K) is the set of pairs of A x A lying in every closed member of
;;; POWER(A x A); IS-SUBTERM(T, K, a, b) is [a, b] in SUBTERM-REL(T, K).
;;;
;;; THE RANK: MSG-RANK(T, K, m) is the least stage index holding m, an IOTA over NN.
;;;
;;; STATEMENT CHECKS (CLAUDE.md, the species of false or underdetermined support).
;;; (1) Every equation here is a definition (def-functoid, def-predicate, the two recursion
;;;     equations of def-by-nn-recursion as `==').  Nothing is asserted.
;;; (2) No index is left untyped: MSG-STAGE is read only at n in NN; clause (ii) carries i in NN,
;;;     1 <= i <= LENGTH(l), and l in TUPLES(A) before the component is read; clause (iii)
;;;     types g in A and k in K.
;;; (3) The IOTA in MSG-RANK: its existence-and-uniqueness obligation is discharged in the laws
;;;     file for m in A; nothing here asserts that it denotes.
;;; (4) BINDERS: every parameter and bound variable is an sm*_ name, used by no other body or
;;;     driver in the tree; none folds onto a class name, an accessor or a registered constant.
;;;
;;; Dependencies: structure-library/ordinals (def-by-nn-recursion), the base theory (TUPLES,
;;; CARTESIAN, PAIR, LENGTH, NTH, UNION, BIG-UNION, POWER, SEP, IOTA, LIST).  No proof is cited.

;;; -----------------------------------------------------------------------
;;; The token law.

(def-predicate 'IS-TOKEN-SET '(smt_)
  '(AND (IN smt_ SET)
        (FORALL smx_ (IMPLIES (IN smx_ smt_) (NOT (IN smx_ (TUPLES SET)))))))
(notation! 'IS-TOKEN-SET 'kind 'predicate 'arity 1
           'english "$1 is a set of tokens, none of which is a list")

;;; -----------------------------------------------------------------------
;;; The two tagged constructors.

(def-functoid 'LST '(sml_) '(LIST 1 sml_))
(notation! 'LST 'kind 'functoid 'arity 1 'english "the list message of $1")

(def-functoid 'ENCR '(smg_ smk_) '(LIST 2 smg_ smk_))
(notation! 'ENCR 'kind 'functoid 'arity 2 'english "the encryption of $1 under the key $2")

;;; -----------------------------------------------------------------------
;;; The stages and the message set.

(def-by-nn-recursion 'MSG-STAGE '(smt_ smk_)
  'smt_
  '(smn_ smv_)
  '(UNION smv_ (UNION (CARTESIAN (PAIR 1 1) (TUPLES smv_))
                      (CARTESIAN (PAIR 2 2) smv_ smk_))))
(notation! 'MSG-STAGE 'kind 'functoid 'arity 3
           'english "the stage $3 of the messages over the tokens $1 and the keys $2")

(def-functoid 'MSG-SET '(smt_ smk_) '(BIG-UNION smn_ NN (MSG-STAGE smt_ smk_ smn_)))
(notation! 'MSG-SET 'kind 'functoid 'arity 2
           'english "the messages over the tokens $1 and the keys $2")

;;; The least stage containing a message.
(def-functoid 'MSG-RANK '(smt_ smk_ smm_)
  '(IOTA smr_ (AND (IN smr_ NN)
                   (AND (IN smm_ (MSG-STAGE smt_ smk_ smr_))
                        (FORALL smj_ (IMPLIES (IN smj_ NN)
                                              (IMPLIES (IN smm_ (MSG-STAGE smt_ smk_ smj_))
                                                       (<= smr_ smj_))))))))
(notation! 'MSG-RANK 'kind 'functoid 'arity 3
           'english "the rank of the message $3 over the tokens $1 and the keys $2")

;;; -----------------------------------------------------------------------
;;; The subterm relation.

(def-predicate 'IS-SUBTERM-CLOSED '(smt_ smk_ smr_)
  '(AND (FORALL sma_ (IMPLIES (IN sma_ (MSG-SET smt_ smk_)) (IN (LIST sma_ sma_) smr_)))
   (AND (FORALL sma_ (FORALL sml_ (FORALL smi_
          (IMPLIES (IN sml_ (TUPLES (MSG-SET smt_ smk_)))
           (IMPLIES (IN smi_ NN)
            (IMPLIES (<= 1 smi_)
             (IMPLIES (<= smi_ (LENGTH sml_))
              (IMPLIES (IN (LIST sma_ (NTH smi_ sml_)) smr_)
                       (IN (LIST sma_ (LST sml_)) smr_)))))))))
        (FORALL sma_ (FORALL smg_ (FORALL smy_
          (IMPLIES (IN smg_ (MSG-SET smt_ smk_))
           (IMPLIES (IN smy_ smk_)
            (IMPLIES (IN (LIST sma_ smg_) smr_)
                     (IN (LIST sma_ (ENCR smg_ smy_)) smr_))))))))))
(notation! 'IS-SUBTERM-CLOSED 'kind 'predicate 'arity 3
           'english "$3 is closed under the subterm clauses over the tokens $1 and the keys $2")

(def-functoid 'SUBTERM-REL '(smt_ smk_)
  '(SEP smp_ (CARTESIAN (MSG-SET smt_ smk_) (MSG-SET smt_ smk_))
        (FORALL smq_ (IMPLIES (IN smq_ (POWER (CARTESIAN (MSG-SET smt_ smk_) (MSG-SET smt_ smk_))))
                              (IMPLIES (IS-SUBTERM-CLOSED smt_ smk_ smq_) (IN smp_ smq_))))))
(notation! 'SUBTERM-REL 'kind 'functoid 'arity 2
           'english "the subterm relation over the tokens $1 and the keys $2")

(def-predicate 'IS-SUBTERM '(smt_ smk_ sma_ smb_) '(IN (LIST sma_ smb_) (SUBTERM-REL smt_ smk_)))
(notation! 'IS-SUBTERM 'kind 'predicate 'arity 4
           'english "$3 is a subterm of $4 over the tokens $1 and the keys $2")
