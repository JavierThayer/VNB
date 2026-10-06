;;; strand-messages.scm -- THE MESSAGES OF STRAND SPACES, ON THE USER'S MODEL
;;; (~/notes/notes-60.txt, item (a): "Let T be a set of tokens.  A message is a nested list of
;;;  tokens, i.e. a token is a message and any list of messages is a message.  Subterms are
;;;  defined recursively in the obvious way.")
;;; DEFINITIONS ONLY; every law is PROVEN in theorem-library/strand-messages-laws.scm.
;;; Agent S-2 of the October roadmap, week 3, 2026-10-06.  This file REPLACES, in place, S-1's
;;; algebra of the paper (Thayer, Herzog, Guttman, ~/docs/jcs_strand_spaces.pdf, 2.3-2.4: texts,
;;; keys, ATOM / CAT / ENC, MESSAGE-ALGEBRA); the original is archive/2026-10-06/strand-messages.scm.
;;; The user's decisions of 2026-10-06 (scratchpad/triage/WEEK3.md, S-2): no keys, no encryption,
;;; no concatenation; ONE n-ary constructor, the list.
;;;
;;; TOKENS ARE NOT LISTS -- THE TOKEN LAW.  In VNB a list is a set, so nothing prevents a member
;;; of T from being a list; the recursion on messages (subterm, content, induction) needs the two
;;; cases DISJOINT, so the disjointness is a HYPOTHESIS ON T, written as a predicate:
;;;
;;;     IS-TOKEN-SET(T)  iff  T is a set and no member of T is in TUPLES(SET)
;;;
;;; TUPLES(SET) is the class of all lists whose components are sets; since 2026-10-01 a list is
;;; DEFINED iff its components are sets (docs/decisions-pending-2026-10-01.md), so TUPLES(SET) is
;;; the class of all defined lists, and "x is not in TUPLES(SET)" is the kernel-admissible
;;; spelling of "x is not a list".  The kernel's `tuples-intro' puts a literal list with set
;;; components into TUPLES(SET); `tuples-mono' carries TUPLES(A) into TUPLES(SET) for any class A
;;; of sets.  This is the form the brief preferred; the fallback (S-1's tag, [0, t] / [1, l]) was
;;; NOT needed.  The law constrains T only; whether a given set satisfies it is the caller's
;;; business (no set is proved to satisfy it here: the tree cannot prove that any set is NOT a
;;; list, since TUPLES has no characterisation beyond its generation axioms).
;;;
;;; THE MESSAGES.  Stage 0 is T; stage n+1 adds every list of stage-n messages:
;;;
;;;     MSG-STAGE(T, 0)       = T
;;;     MSG-STAGE(T, succ n)  = MSG-STAGE(T, n)  u  TUPLES(MSG-STAGE(T, n))   (def-by-nn-recursion)
;;;     MSG-SET(T)            = the union over n in NN of MSG-STAGE(T, n)
;;;
;;; The list constructor is TUPLES itself: "l is a list of messages" is l in TUPLES(MSG-SET(T)),
;;; its components are NTH(i, l) for 1 <= i <= LENGTH(l).  No constructor functoid is needed.
;;; Every stage is a SET when T is (`tuples-sethood', `union-set-closure').
;;;
;;; THE SUBTERM RELATION, as the INTERSECTION of the closed relations (S-1's device, kept; the
;;; design note's decision 4 for causal precedence): a relation r on A = MSG-SET(T) is closed when
;;;     (i)  [a, a] in r for every message a ("a message is a subterm of itself");
;;;     (ii) [a, l] in r whenever l is a list of messages, 1 <= i <= LENGTH(l) and [a, NTH(i, l)]
;;;          in r ("a subterm of a component is a subterm of the list").
;;; SUBTERM-REL(T) is the set of pairs of A x A lying in every closed member of POWER(A x A);
;;; IS-SUBTERM(T, a, b) is [a, b] in SUBTERM-REL(T).  Recursion on the rank was the alternative;
;;; it would need a recursion over A whose value at a message is a set of messages, which the
;;; tree does not have (def-by-nn-recursion recurs on NN).
;;;
;;; THE RANK: MSG-RANK(T, m) is the least stage index holding m, an IOTA over NN, as in S-1.
;;;
;;; STATEMENT CHECKS (CLAUDE.md, the species of false or underdetermined support).
;;; (1) Every equation here is a definition (def-functoid, def-predicate, the two recursion
;;;     equations of def-by-nn-recursion as `==').  Nothing is asserted.
;;; (2) No index is left untyped: MSG-STAGE is read only at n in NN; the closure clause (ii)
;;;     carries i in NN, 1 <= i <= LENGTH(l), and l in TUPLES(A) before the component is read.
;;; (3) The IOTA in MSG-RANK: its existence-and-uniqueness obligation is discharged in the laws
;;;     file for m in A; nothing here asserts that it denotes.
;;; (4) BINDERS: every parameter and bound variable is an sm*_ name, used by no other body or
;;;     driver in the tree; none folds onto a class name, an accessor or a registered constant.
;;;
;;; Dependencies: structure-library/ordinals (def-by-nn-recursion), the base theory (TUPLES,
;;; LENGTH, NTH, UNION, BIG-UNION, POWER, SEP, IOTA, LIST).  No proof is cited.

;;; -----------------------------------------------------------------------
;;; The token law.

(def-predicate 'IS-TOKEN-SET '(smt_)
  '(AND (IN smt_ SET)
        (FORALL smx_ (IMPLIES (IN smx_ smt_) (NOT (IN smx_ (TUPLES SET)))))))
(notation! 'IS-TOKEN-SET 'kind 'predicate 'arity 1
           'english "$1 is a set of tokens, none of which is a list")

;;; -----------------------------------------------------------------------
;;; The stages and the message set.

(def-by-nn-recursion 'MSG-STAGE '(smt_)
  'smt_
  '(smn_ smv_)
  '(UNION smv_ (TUPLES smv_)))
(notation! 'MSG-STAGE 'kind 'functoid 'arity 2
           'english "the stage $2 of the messages over the tokens $1")

(def-functoid 'MSG-SET '(smt_) '(BIG-UNION smn_ NN (MSG-STAGE smt_ smn_)))
(notation! 'MSG-SET 'kind 'functoid 'arity 1
           'english "the messages over the tokens $1")

;;; The least stage containing a message.
(def-functoid 'MSG-RANK '(smt_ smm_)
  '(IOTA smr_ (AND (IN smr_ NN)
                   (AND (IN smm_ (MSG-STAGE smt_ smr_))
                        (FORALL smj_ (IMPLIES (IN smj_ NN)
                                              (IMPLIES (IN smm_ (MSG-STAGE smt_ smj_))
                                                       (<= smr_ smj_))))))))
(notation! 'MSG-RANK 'kind 'functoid 'arity 2
           'english "the rank of the message $2 over the tokens $1")

;;; -----------------------------------------------------------------------
;;; The subterm relation.

(def-predicate 'IS-SUBTERM-CLOSED '(smt_ smr_)
  '(AND (FORALL sma_ (IMPLIES (IN sma_ (MSG-SET smt_)) (IN (LIST sma_ sma_) smr_)))
        (FORALL sma_ (FORALL sml_ (FORALL smi_
          (IMPLIES (IN sml_ (TUPLES (MSG-SET smt_)))
           (IMPLIES (IN smi_ NN)
            (IMPLIES (<= 1 smi_)
             (IMPLIES (<= smi_ (LENGTH sml_))
              (IMPLIES (IN (LIST sma_ (NTH smi_ sml_)) smr_)
                       (IN (LIST sma_ sml_) smr_)))))))))))
(notation! 'IS-SUBTERM-CLOSED 'kind 'predicate 'arity 2
           'english "$2 is closed under the subterm clauses over the tokens $1")

(def-functoid 'SUBTERM-REL '(smt_)
  '(SEP smp_ (CARTESIAN (MSG-SET smt_) (MSG-SET smt_))
        (FORALL smq_ (IMPLIES (IN smq_ (POWER (CARTESIAN (MSG-SET smt_) (MSG-SET smt_))))
                              (IMPLIES (IS-SUBTERM-CLOSED smt_ smq_) (IN smp_ smq_))))))
(notation! 'SUBTERM-REL 'kind 'functoid 'arity 1
           'english "the subterm relation over the tokens $1")

(def-predicate 'IS-SUBTERM '(smt_ sma_ smb_) '(IN (LIST sma_ smb_) (SUBTERM-REL smt_)))
(notation! 'IS-SUBTERM 'kind 'predicate 'arity 3
           'english "$2 is a subterm of $3 over the tokens $1")
