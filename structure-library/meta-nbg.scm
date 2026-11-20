;;; meta-nbg.scm -- K2, agent METACORE (2026-10-29): the kernel forms of the ten C+ rows of the K2 ledger
;;; (scratchpad/K2-LEDGER.md of ~/prover-mf, section 1, rows 8, 10, 11, 13, 14, 15, 24, 26, 27, 51), TRANSCRIBED
;;; from their checkers of a320cb6f.  DEFINITIONS ONLY; the laws (the BRIDGES: each kernel form admissible over the
;;; core) are in theorem-library/meta-nbg-laws.scm, with the NBG controls of meta-core.scm 4.3a and the
;;; admissibility of the rules of rows 49 and 58.
;;; Conventions as structure-library/meta-ind.scm: a kernel sequent is well formed by construction, the conjunct
;;; (IN c SEQ-SET); contexts are compared as SETS, so "the context with f replaced by a, b" is the set equation
;;; CTX-ADD(CTX-ADD(DIFFERENCE(g, {f}), a), b); a named substitution p[x := t] is EXPR-OPEN(p, 0, t).
;;; THE DEFINEDNESS A CHECKER READS OFF THE CONTEXT (pi--defined?, chk-elim-certified?) is encoded as the
;;; CONTEXT CERTIFICATE: some member h of the context is in CERT-SET(T, g, t) (meta-def.scm section 8), the least
;;; set of sentences that certify t (a strict atom, a sentence made true, an opened existential, a predicate or
;;; class hypothesis through its definition).  The clauses of the certificate that read no context formula (a total
;;; constructor on certified arguments, a list of sets, a binder over a certified domain, ...) are the DEF rows of
;;; the K2 ledger's table 2, each admissible on its own; they are not restated here.
;;; Binders: mnk*_.

(define (mnk--ex vars body)
  (if (null? vars) body `(FORSOME ,(car vars) ,(mnk--ex (cdr vars) body))))
(define (mnk--and . fs)
  (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(apply mnk--and (cdr fs)))))
(define (mnk--rel! name note body)
  (def-predicate name '(mnkt_ mnkhs_ mnkc_) (mnk--and '(IN mnkc_ SEQ-SET) body))
  (notation! name 'kind 'predicate 'arity 3 'english note))
;; the context g with the formula f removed
(define (mnk--minus f) `(DIFFERENCE mnkg_ (PAIR ,f ,f)))

;; ROW 10. rule-checkers-logic.scm (and-elim): some (AND a b) in the context REPLACED by a and b; the same goal.
(mnk--rel! 'REL-AND-ELIM-K "the kernel's and-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-AND mnka_ mnkb_) mnkg_)
              `(= mnkhs_ (LIST (LIST (CTX-ADD (CTX-ADD ,(mnk--minus '(ENC-AND mnka_ mnkb_)) mnka_) mnkb_) mnkf_))))))

;; ROW 11. (or-elim): some (OR a b) in the context replaced, in two branches, by a and by b; the same goal.
(mnk--rel! 'REL-OR-ELIM-K "the kernel's or-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-OR mnka_ mnkb_) mnkg_)
              `(= mnkhs_ (LIST (LIST (CTX-ADD ,(mnk--minus '(ENC-OR mnka_ mnkb_)) mnka_) mnkf_)
                               (LIST (CTX-ADD ,(mnk--minus '(ENC-OR mnka_ mnkb_)) mnkb_) mnkf_))))))

;; ROW 13. (iff-elim): some (IFF a b) in the context replaced by (IMPLIES a b) and (IMPLIES b a).
(mnk--rel! 'REL-IFF-ELIM-K "the kernel's iff-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-IFF mnka_ mnkb_) mnkg_)
              `(= mnkhs_ (LIST (LIST (CTX-ADD (CTX-ADD ,(mnk--minus '(ENC-IFF mnka_ mnkb_)) (ENC-IMP mnka_ mnkb_))
                                              (ENC-IMP mnkb_ mnka_))
                                     mnkf_))))))

;; ROW 14. (forsome-elim): some (FORSOME x p) in the context REPLACED by p[x := y], y an eigenvariable free in
;; nothing else: not in the rest of the context, not in the goal, not in the existential itself.
(mnk--rel! 'REL-FORSOME-ELIM-K "the kernel's forsome-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkb_ mnky_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-EX mnkb_) mnkg_) '(IN mnky_ NN)
              `(NOT (IN mnky_ (UNION (CTX-FV ,(mnk--minus '(ENC-EX mnkb_))) (UNION (EXPR-FV mnkf_) (EXPR-FV (ENC-EX mnkb_))))))
              `(= mnkhs_ (LIST (LIST (CTX-ADD ,(mnk--minus '(ENC-EX mnkb_)) (EXPR-OPEN mnkb_ 0 (EFVAR mnky_))) mnkf_))))))

;; ROW 8. (forsome-intro, chk-instance-certifies?): the goal (FORSOME x p); one hypothesis, the same context,
;; p[x := t]; NO definedness sequent, the witness certified -- by the instance itself (a sentence it makes true
;; is a strict atom certifying t: TRUE-REACH, STRICT-ATOM of meta-def.scm 5; the kernel reads the top-level
;; conjuncts, a subset) or by the context (the context certificate).
(mnk--rel! 'REL-FORSOME-INTRO-K "the kernel's forsome-intro with a certified witness relates $2 to $3"
  (mnk--ex '(mnkg_ mnkb_ mnktm_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-EX mnkb_))) '(IN mnktm_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ (EXPR-OPEN mnkb_ 0 mnktm_))))
              '(OR (FORSOME mnkf2_ (AND (IN mnkf2_ (TRUE-REACH (EXPR-OPEN mnkb_ 0 mnktm_))) (STRICT-ATOM mnkf2_ mnktm_)))
                   (FORSOME mnkh_ (AND (IN mnkh_ mnkg_) (IN mnkh_ (CERT-SET mnkt_ mnkg_ mnktm_))))))))

;; ROW 15. (forall-elim, chk-elim-certified?): some (FORALL x p) in the context; one hypothesis, the same goal,
;; the context gaining p[x := t]; NO definedness sequent, t certified by the context.
(mnk--rel! 'REL-FORALL-ELIM-K "the kernel's forall-elim at a certified term relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkb_ mnktm_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-ALL mnkb_) mnkg_) '(IN mnktm_ CLT)
              '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnktm_))
              '(= mnkhs_ (LIST (LIST (CTX-ADD mnkg_ (EXPR-OPEN mnkb_ 0 mnktm_)) mnkf_))))))

;; ROW 24. (reflexivity): the goal t = t, no hypothesis, t certified by the context.
(mnk--rel! 'REL-REFLEXIVITY-K "the kernel's reflexivity at a certified term relates $2 to $3"
  (mnk--ex '(mnkg_ mnktm_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-EQ mnktm_ mnktm_))) '(IN mnktm_ CLT)
              '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnktm_)) '(= mnkhs_ (LIST)))))

;; ROWS 26, 27. (if-true / if-false through pi--if-equation, primitive-inferences.scm): two hypotheses, the
;; condition (its negation) and the main branch gaining the STRICT equation (IF p a b) = a (= b), the branch a
;; (b) certified by the context.  (When it is not certified the kernel hands over the quasi-equation, which is
;; CR-IF-TRUE / CR-IF-FALSE itself.)
(mnk--rel! 'REL-IF-TRUE-K "the kernel's if-true at a certified branch relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_ mnka_ mnkb_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnka_))
              '(IN (ENC-IF mnkp_ mnka_ mnkb_) CLT) '(IN mnka_ CLT) '(IN mnkb_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ mnkp_)
                               (LIST (CTX-ADD mnkg_ (ENC-EQ (ENC-IF mnkp_ mnka_ mnkb_) mnka_)) mnkf_))))))
(mnk--rel! 'REL-IF-FALSE-K "the kernel's if-false at a certified branch relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_ mnka_ mnkb_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnkb_))
              '(IN (ENC-IF mnkp_ mnka_ mnkb_) CLT) '(IN mnka_ CLT) '(IN mnkb_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ (ENC-NOT mnkp_))
                               (LIST (CTX-ADD mnkg_ (ENC-EQ (ENC-IF mnkp_ mnka_ mnkb_) mnkb_)) mnkf_))))))

;; ROW 51. rule-checkers-schema.scm (rcs-iota-in-elim, rcs--context-defines?): one hypothesis, the same goal, the
;; context gaining p[x := IOTA x. p]; the context establishes that the description denotes: a membership
;; (IN (IOTA x p) A) or an equation naming it, (= (IOTA x p) u) or (= u (IOTA x p)), is in the context.
(mnk--rel! 'REL-IOTA-IN-ELIM-K "the kernel's iota-in-elim relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_))
              '(OR (FORSOME mnka_ (IN (ENC-IN (ENC-IOTA mnkp_) mnka_) mnkg_))
                   (FORSOME mnku_ (OR (IN (ENC-EQ (ENC-IOTA mnkp_) mnku_) mnkg_) (IN (ENC-EQ mnku_ (ENC-IOTA mnkp_)) mnkg_))))
              '(= mnkhs_ (LIST (LIST (CTX-ADD mnkg_ (EXPR-OPEN mnkp_ 0 (ENC-IOTA mnkp_))) mnkf_))))))

;;; -----------------------------------------------------------------------
;;; D. THE CERTIFICATE AS A WHOLE (agent BRIDGE, 2026-11-19).  The kernel relations above read the definedness of
;;; t off ONE context member h (h in CERT-SET(T, g, t)).  The checkers accept more: chk-elim-certified?
;;; (rule-checkers-logic.scm, forall-elim, forsome-intro, if-true, if-false) and the reflexivity checker end in
;;; the builder's certificate pi--defined? (primitive-inferences.scm), whose clauses compose: an atom, a total
;;; constructor on certified arguments, a binder over a certified domain, a list of sets, NTH of a certified
;;; list, f(a) for typed f and a, a functoid with a certified instantiated body, the strict walks, the
;;; predicate-hypothesis readings, each applied to what the context holds.  Each clause is a DEF row
;;; (structure-library/meta-def.scm, meta-core.scm 4.7), admissible over the core.
;;; DEF-RULE is the disjunction of the rows that are DERIVED or ADMITTED (each has its closure law), together
;;; with the three core rules that start a reading: assumption (a context member), theorem-assumption (a member
;;; of T: the definitions the predicate rows read) and reflexivity (an atom).  DEF-DERIVABLE(T) is the least set
;;; of sequents closed under DEF-RULE (DERIVABLE's device, meta-core.scm 5): the sequents a certificate built
;;; from those rows reaches.  THE KERNEL FORMS -KD below take the definedness of t as "[g, t = t] is in
;;; DEF-DERIVABLE(T)", the form of the kernel's acceptance when every clause it used is a row of DEF-RULE.
;;; NOT IN DEF-RULE (the open rows; theorem-library/meta-nbg-laws.scm, section D, and ~/prover-w2/BRIDGE-REPORT.md):
;;;   - ground arithmetic and arithmetic on number-typed arguments (pi--number-class, *pi-arith-total-heads*,
;;;     chk-number-class): no head codes for the arithmetic heads (K3);
;;;   - LENGTH of a term typed in a class of TUPLES (pi--typed-in-tuples?): DEF-LEN-TUPLES (meta-def.scm 4a) covers the
;;;     direct form, a context membership t in TUPLES(A), over T holding the encoded length-in-nn; the forms
;;;     through SEP domains and functoid bodies (MAT -> MATRIX -> TUPLES) are not covered;
;;;   - the applied structure operation ((ACC s) a1 .. an) (pi--defined?, the op / family-fun arm);
;;;   - the view clause of pi--accessor-certified? (meta-def.scm 7: not admissible as a row);
;;;   - DEF-NTH-LIT (the pre-R4 clause, retired in the kernel) is deliberately not a disjunct.
;;; Binders: mnk*_ as above.

;; DEF-LEN-TUPLES and AX-LEN-NN: structure-library/meta-def.scm, section 4a.

(define mnk--def-rows
  '(CR-ASSUMPTION CR-THEOREM-ASSUMPTION CR-REFLEXIVITY
    DEF-STRICT-IN-L DEF-STRICT-IN-R DEF-STRICT-EQ-L DEF-STRICT-EQ-R DEF-STRICT-ARG DEF-STRICT-DOM
    DEF-TOTAL DEF-BINDER DEF-COMP DEF-LIST DEF-STRICT-HYP DEF-NTH-LIST DEF-STRICT-PRED DEF-STRUCT-HYP
    DEF-PRED-UNFOLD DEF-PRED-HYP DEF-FUN-INST DEF-FUN-STRICT DEF-FUN-NTH DEF-FUN-SEP
    DEF-PRED-UNFOLD-N DEF-PRED-HYP-N DEF-CERT-HYP))
(def-predicate 'DEF-RULE '(mnkt_ mnkhs_ mnkc_)
  (let loop ((ns mnk--def-rows))
    (if (null? ns)
        '(OR (AND (SUBSET mnkt_ CLF) (AND (IN AX-FUN-APP mnkt_) (DEF-APP mnkt_ mnkhs_ mnkc_)))
             (AND (SUBSET mnkt_ CLF) (AND (IN AX-LEN-NN mnkt_) (DEF-LEN-TUPLES mnkt_ mnkhs_ mnkc_))))
        `(OR (,(car ns) mnkt_ mnkhs_ mnkc_) ,(loop (cdr ns))))))
(notation! 'DEF-RULE 'kind 'predicate 'arity 3 'english "some definedness row over $1 relates $2 to $3")
(def-predicate 'DEF-CLOSED '(mnkt_ mnks_)
  '(FORALL mnkhs_ (FORALL mnkc_ (IMPLIES (DEF-RULE mnkt_ mnkhs_ mnkc_)
                                 (IMPLIES (HYPS-IN mnkhs_ mnks_)
                                  (IMPLIES (IN mnkc_ SEQ-SET) (IN mnkc_ mnks_)))))))
(notation! 'DEF-CLOSED 'kind 'predicate 'arity 2 'english "$2 is closed under the definedness rows over $1")
(def-functoid 'DEF-DERIVABLE '(mnkt_)
  '(SEP mnkq_ SEQ-SET (FORALL mnks_ (IMPLIES (IN mnks_ (POWER SEQ-SET)) (IMPLIES (DEF-CLOSED mnkt_ mnks_) (IN mnkq_ mnks_))))))
(notation! 'DEF-DERIVABLE 'kind 'functoid 'arity 1 'english "the sequents the definedness rows over $1 reach")

;; ROW 15, forall-elim, the instance certified by the rows: no definedness sequent.
(mnk--rel! 'REL-FORALL-ELIM-KD "the kernel's forall-elim at a term certified by the rows relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkb_ mnktm_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (ENC-ALL mnkb_) mnkg_) '(IN mnktm_ CLT)
              '(IN (LIST mnkg_ (ENC-EQ mnktm_ mnktm_)) (DEF-DERIVABLE mnkt_))
              '(= mnkhs_ (LIST (LIST (CTX-ADD mnkg_ (EXPR-OPEN mnkb_ 0 mnktm_)) mnkf_))))))
;; ROW 8, forsome-intro, the witness certified by the rows.
(mnk--rel! 'REL-FORSOME-INTRO-KD "the kernel's forsome-intro with a witness certified by the rows relates $2 to $3"
  (mnk--ex '(mnkg_ mnkb_ mnktm_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-EX mnkb_))) '(IN mnktm_ CLT)
              '(IN (LIST mnkg_ (ENC-EQ mnktm_ mnktm_)) (DEF-DERIVABLE mnkt_))
              '(= mnkhs_ (LIST (LIST mnkg_ (EXPR-OPEN mnkb_ 0 mnktm_)))))))
;; ROW 24, reflexivity at a term certified by the rows; and at TRUTH (the reflexivity checker accepts the goal
;; TRUTH with no hypothesis: since the retirement of the kernel op truth-intro, 2026-11-18, this is the kernel's
;; only door to CR-TRUTH-INTRO besides assumption).
(mnk--rel! 'REL-REFLEXIVITY-KD "the kernel's reflexivity at a term certified by the rows relates $2 to $3"
  (mnk--ex '(mnkg_ mnktm_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-EQ mnktm_ mnktm_)))
              '(IN (LIST mnkg_ (ENC-EQ mnktm_ mnktm_)) (DEF-DERIVABLE mnkt_)) '(= mnkhs_ (LIST)))))
(mnk--rel! 'REL-REFLEXIVITY-KT "the kernel's reflexivity at TRUTH relates $2 to $3"
  (mnk--ex '(mnkg_) (mnk--and '(= mnkc_ (LIST mnkg_ ENC-TRUTH)) '(= mnkhs_ (LIST)))))
;; ROWS 26, 27, if-true / if-false with the strict equation, the branch certified by the rows.
(mnk--rel! 'REL-IF-TRUE-KD "the kernel's if-true at a branch certified by the rows relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (LIST mnkg_ (ENC-EQ mnka_ mnka_)) (DEF-DERIVABLE mnkt_))
              '(IN (ENC-IF mnkp_ mnka_ mnkb_) CLT) '(IN mnka_ CLT) '(IN mnkb_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ mnkp_)
                               (LIST (CTX-ADD mnkg_ (ENC-EQ (ENC-IF mnkp_ mnka_ mnkb_) mnka_)) mnkf_))))))
(mnk--rel! 'REL-IF-FALSE-KD "the kernel's if-false at a branch certified by the rows relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkp_ mnka_ mnkb_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(IN (LIST mnkg_ (ENC-EQ mnkb_ mnkb_)) (DEF-DERIVABLE mnkt_))
              '(IN (ENC-IF mnkp_ mnka_ mnkb_) CLT) '(IN mnka_ CLT) '(IN mnkb_ CLT)
              '(= mnkhs_ (LIST (LIST mnkg_ (ENC-NOT mnkp_))
                               (LIST (CTX-ADD mnkg_ (ENC-EQ (ENC-IF mnkp_ mnka_ mnkb_) mnkb_)) mnkf_))))))
;; THE ADDS-NOTHING ARM (chk-adds-nothing?, rule-checkers-logic.scm; rcs-iota-in-elim's `added' empty): forall-elim,
;; forsome-elim, if-true and if-false accept, whatever else holds, a hypothesis with the conclusion's goal and a
;; context INCLUDED in the conclusion's (the formula the rule would add was already there); iota-in-elim the same with
;; the context unchanged.  Some entry i of hs is [d, f] with d a subset of g.
(mnk--rel! 'REL-ADDS-NOTHING-K "a kernel rule whose hypothesis adds nothing relates $2 to $3"
  (mnk--ex '(mnkg_ mnkf_ mnkd_ mnki_)
    (mnk--and '(= mnkc_ (LIST mnkg_ mnkf_)) '(SUBSET mnkd_ mnkg_)
              '(IN mnki_ NN) '(<= 1 mnki_) '(<= mnki_ (LENGTH mnkhs_))
              '(= (NTH mnki_ mnkhs_) (LIST mnkd_ mnkf_)))))

;;; -----------------------------------------------------------------------
;;; E. THE REWRITING RULES AT ANY FINITE SET OF POSITIONS (agent POSN, 2026-11-19; the K2 ledger's nine P1 rows,
;;; 36, 37, 38, 53, 54, 55, 56, 57, 58).  REWR(J, 7) (meta-cr.scm) is the ONE-POSITION relation: every clause has one
;;; premise, so a derivation is one path from the root to one TOP.  The kernel rewrites SEVERAL positions in one
;;; inference.  REWRS(J) is the least set of rewrite tuples holding REWR(J, 7) and closed under the composition of two
;;; formula rewrites in one context [2, g, a, b], [2, g, b, c] => [2, g, a, c], with the empty rewrite [2, g, e, e]:
;;; the finite chains of one-position rewrites of the whole formula.  An inference at n positions is a chain of n
;;; one-position steps, and its admissibility follows from the one-position law by induction on n (the least-set
;;; induction of REWRS, meta-nbg-laws.scm section E).
;;; WHY THE CHAIN IS THE KERNEL'S RELATION (read off rule-checkers-rewrite.scm rkw--walk / rkw--descend and
;;; rule-checkers-logic.scm chk-contracts-d?, and rule-checkers-schema.scm rcs-lambda-beta, in B1120).  The macete walk
;;; descends the conclusion's formula a and the hypothesis' formula b in parallel and stops at the first position
;;; where the pair is explained, so the positions are pairwise disjoint.  Each position's local context is read off a
;;; DIFFERENT side at AND and OR (the repair of 2026-10-09): the right conjunct under the ORIGINAL left, the left
;;; under the REWRITTEN right; the left disjunct under NOT the ORIGINAL right, the right under NOT the REWRITTEN left;
;;; the consequent of IMPLIES under the ORIGINAL antecedent; no increment elsewhere.  Order the positions so that,
;;; at every AND, those of the right conjunct come first, at every OR those of the left disjunct, at every IMPLIES
;;; those of the consequent; then the local context of the k-th step, computed by the clauses of REWR on the formula
;;; with the first k - 1 steps made, is the context the walk computed for that position (up to the flattening of a
;;; conjunction, which a derivability does not see), and each intermediate formula is a sentence.  The four
;;; reduction checkers (nth-reduce, length-reduce, functoid-beta, lambda-beta) read no local increment at all, and
;;; their reachability relation -- created redexes, contractions inside a contractum, innermost first -- is a chain
;;; of single contractions, each at the position where it sits in the term reached so far.  The decompositions are
;;; context-free (meta-ind.scm section 3).  What is NOT covered is what the one-position forms already leave out:
;;; a justification read from a binder's own hypothesis (lambda-beta licensed by x in A inside VNB-LAMBDA x A; the
;;; list-definedness reads of *rkw--binder-domains?*), because under a binder the clauses pass the AMBIENT context,
;;; and a justification outside the rule's J set (an owed obligation is a derivability of J, a minor premise of a
;;; macete is the condition derived in the local context).  Binders: mpo*_.

(def-predicate 'RWS-RULE '(mpoj_ mpos_ mpox_)
  '(OR (IN mpox_ (REWR mpoj_ 7))
       (OR (FORSOME mpog_ (FORSOME mpoe_
             (AND (IN mpog_ CTX-SET) (AND (IN mpoe_ CLF) (= mpox_ (LIST 2 mpog_ mpoe_ mpoe_))))))
           (FORSOME mpog_ (FORSOME mpoa_ (FORSOME mpob_ (FORSOME mpoc_
             (AND (IN mpog_ CTX-SET) (AND (IN mpoa_ EXPR-SET) (AND (IN mpob_ EXPR-SET) (AND (IN mpoc_ EXPR-SET)
                  (AND (= mpox_ (LIST 2 mpog_ mpoa_ mpoc_))
                       (AND (IN (LIST 2 mpog_ mpoa_ mpob_) mpos_) (IN (LIST 2 mpog_ mpob_ mpoc_) mpos_))))))))))))))
(notation! 'RWS-RULE 'kind 'predicate 'arity 3
           'english "$3 is a one-position rewrite justified by $1, an empty rewrite, or the composition of two rewrites in $2")
(def-predicate 'RWS-CLOSED '(mpoj_ mpos_)
  '(FORALL mpox_ (IMPLIES (IN mpox_ RW-UNIV) (IMPLIES (RWS-RULE mpoj_ mpos_ mpox_) (IN mpox_ mpos_)))))
(notation! 'RWS-CLOSED 'kind 'predicate 'arity 2
           'english "$2 holds the one-position rewrites justified by $1 and is closed under composing formula rewrites")
(def-functoid 'REWRS '(mpoj_)
  '(SEP mpox_ RW-UNIV (FORALL mpos_ (IMPLIES (IN mpos_ (POWER RW-UNIV)) (IMPLIES (RWS-CLOSED mpoj_ mpos_) (IN mpox_ mpos_))))))
(notation! 'REWRS 'kind 'functoid 'arity 1 'english "the rewrites at finitely many positions justified by $1")

;; The goal, or one assumption, rewritten at finitely many positions of any stage.
(def-predicate 'REL-REWRITE-S '(mpoj_ mpohs_ mpocc_)
  '(AND (IN mpocc_ SEQ-SET)
        (FORSOME mpog_ (FORSOME mpoa_ (FORSOME mpob_
          (AND (= mpocc_ (LIST mpog_ mpoa_)) (AND (= mpohs_ (LIST (LIST mpog_ mpob_)))
               (IN (LIST 2 mpog_ mpoa_ mpob_) (REWRS mpoj_)))))))))
(notation! 'REL-REWRITE-S 'kind 'predicate 'arity 3 'english "$2 is $3 with its goal rewritten at finitely many positions justified by $1")
(def-predicate 'REL-REWRITE-HYP-S '(mpoj_ mpohs_ mpocc_)
  '(AND (IN mpocc_ SEQ-SET)
        (FORSOME mpog_ (FORSOME mpof_ (FORSOME mpoa_ (FORSOME mpob_
          (AND (= mpocc_ (LIST mpog_ mpof_)) (AND (IN mpoa_ mpog_)
          (AND (= mpohs_ (LIST (LIST (CTX-ADD (DIFFERENCE mpog_ (PAIR mpoa_ mpoa_)) mpob_) mpof_)))
               (IN (LIST 2 mpog_ mpoa_ mpob_) (REWRS mpoj_)))))))))))
(notation! 'REL-REWRITE-HYP-S 'kind 'predicate 'arity 3 'english "$2 is $3 with one assumption rewritten at finitely many positions justified by $1")

;; The nine P1 rows at finitely many positions, each over the J set of its one-position form.
(for-each
  (lambda (e)
    (def-predicate (car e) '(mpot_ mpohs_ mpocc_) `(,(caddr e) (,(cadr e) mpot_) mpohs_ mpocc_))
    (notation! (car e) 'kind 'predicate 'arity 3 'english "the kernel rule, at finitely many positions, relates $2 to $3"))
  '((REL-NTH-REDUCE-S J-NTH REL-REWRITE-S) (REL-LENGTH-REDUCE-S J-LEN REL-REWRITE-S)
    (REL-FUNCTOID-BETA-S J-FB REL-REWRITE-S)
    (REL-LAMBDA-BETA-S J-LB REL-REWRITE-S) (REL-LAMBDA-BETA-HYP-S J-LB REL-REWRITE-HYP-S)
    (REL-MACETE-S J-MAC REL-REWRITE-S) (REL-MACETE-HYP-S J-MAC REL-REWRITE-HYP-S)
    (REL-MACETE-N-S J-MACN REL-REWRITE-S) (REL-MACETE-N-HYP-S J-MACN REL-REWRITE-HYP-S)
    (REL-UNION-DECOMPOSE-S J-UDEC REL-REWRITE-S) (REL-UNION-DECOMPOSE-HYP-S J-UDEC REL-REWRITE-HYP-S)
    (REL-INTERSECTION-DECOMPOSE-S J-IDEC REL-REWRITE-S) (REL-INTERSECTION-DECOMPOSE-HYP-S J-IDEC REL-REWRITE-HYP-S)
    (REL-CARTESIAN-DECOMPOSE-S J-CART REL-REWRITE-S) (REL-TUPLE-EQ-DECOMPOSE-S J-TEQ REL-REWRITE-S)))

;;; K1FIX (2026-11-19, the user's decision): the CERTIFIED forms of the two repaired kernel rules whose owed sequent
;;; concerns one term.  The kernel posts the owed definedness sequent only when its certificate does not accept the
;;; term; when it does, the figure has no such hypothesis and the term is certified by the context (CERT-SET, as rows
;;; 8, 15, 24).  tuples-intro at the empty tuple, A certified; lambda-type at one binder, the codomain B certified.
(mnk--rel! 'REL-TUPLES-INTRO-0K "the kernel's tuples-intro at the empty tuple, the class certified, relates $2 to $3"
  (mnk--ex '(mnkg_ mnkl_ mnka_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-IN (ENC-LIST mnkl_) (ENC-TUPLES mnka_)))) '(= (LENGTH mnkl_) 0)
              '(IN mnka_ CLT) '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnka_)) '(= mnkhs_ (LIST)))))
(mnk--rel! 'REL-LAMBDA-TYPE-K "the kernel's lambda-type at one binder, the codomain certified, relates $2 to $3"
  (mnk--ex '(mnkg_ mnka_ mnkb_ mnkd_ mnkh_)
    (mnk--and '(= mnkc_ (LIST mnkg_ (ENC-IN (ENC-LAM mnka_ mnkb_) (ENC-FUN mnka_ mnkd_)))) '(NBG-OK mnkb_)
              '(IN mnkd_ CLT) '(IN mnkh_ mnkg_) '(IN mnkh_ (CERT-SET mnkt_ mnkg_ mnkd_))
              '(= mnkhs_ (LIST (LIST mnkg_ (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 0) mnka_) (ENC-IN mnkb_ mnkd_))))
                               (LIST mnkg_ (ENC-IN mnka_ ENC-SETC)))))))
