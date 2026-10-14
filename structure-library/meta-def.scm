;;; meta-def.scm -- K2 PHASE 5: the clauses of the kernel's definedness certificate pi--defined?
;;; (primitive-inferences.scm 1164-1235 and its helpers, tree f7e2246, 2026-10-12), each TRANSCRIBED as a
;;; rule DEF-k over the encoding: hypotheses the context facts the clause reads, conclusion [g, t = t].
;;; (docs/meta-k2-admissibility-2026-10-08.md, section 4.7 and section 6, phase 5.)
;;; DEFINITIONS ONLY; the laws are in theorem-library/meta-def-laws.scm.  Agent META-5, 2026-10-12.
;;; Builds on structure-library/meta-syntax.scm, meta-core.scm, meta-ind.scm, which it does not edit.
;;; Every binder and parameter here is an md*_ name.
;;;
;;; CONVENTIONS (as meta-core.scm section 6, meta-ind.scm).  A DEF rule is a relation DEF-X(T, hs, c),
;;; c a sequent [g, (ENC-EQ t t)], hs the list of premise sequents, read as the kernel's clause read in
;;; the context g: a FACT "f in the context" of the certificate becomes the PREMISE [g, f] (the core
;;; derives [g, f] from f in g by assumption, so the rule is no weaker than the clause; it is stated on
;;; derivable premises so that its closure is a property of DERIVABLE).
;;;
;;; THE TABLE (each row: clause, line, the rule below or the reason it has none, its standing):
;;;   1166 atom (variable, constant, numeral)          core CR-REFLEXIVITY (EFVAR / ECONST)
;;;   1167 ground arithmetic (arith-eval)              DERIVED from T's closure laws + DEF-STRICT-IN-L; no codes
;;;   1168 asm-establishes-defined?: t in _ / t = _ / _ = t in context
;;;                                                    DEF-STRICT-IN-L (schema), DEF-STRICT-EQ-L (DERIVED),
;;;                                                    DEF-STRICT-EQ-R (schema)
;;;        accessor-certified? (IS-X(s) for ACC(s), the view clause)   as 1205
;;;   1169 strict-hyp: t outside binders in a true IN / = / <= / <   DEF-STRICT-IN-L/R, DEF-STRICT-EQ-L/R,
;;;                                                    then DEF-STRICT-ARG down the constructor heads.
;;;                                                    FINDING 0.1: the kernel walks def-functoid heads too.
;;;        RE-TRANSCRIBED against b25dd06 (META-7, 2026-10-14): see DEF-STRICT-HYP below (section 5).
;;;   1172 structure hypothesis IS-X(t) / t in X        strictness of a predicate application (head 10): schema
;;;                                                    DEF-STRICT-PRED (not encoded: no predicate codes)
;;;   1174 LIST / PAIR / SINGLETON, every entry a set   DEF-LIST (schema here; the doctrine of 2026-10-01)
;;;   1176 *total-term-heads* on certified arguments    DEF-TOTAL (schema: class comprehension), heads TOTAL-HEAD
;;;   1178 SEP / BIG-UNION / VNB-LAMBDA, certified domain   DEF-BINDER (schema: separation / union / graph)
;;;   1180 COMP                                         DEF-COMP (schema: class comprehension)
;;;   1181 NTH(k, LIST l), l_k certified                DEF-NTH-LIT as the kernel has it.  FINDING 0.2: the
;;;                                                    doctrine denies it; the sound rule needs the LIST certified
;;;        RE-TRANSCRIBED against b25dd06 (META-7): R4 made the clause read the LIST; see DEF-NTH-LIST (section 5).
;;;   1189 NTH(k, F(..)) through a functoid body        as 1181, through functoid beta (no functoid encoding)
;;;   1194 + - * min max abs succ ^ on number-typed args   DERIVED from T's closure laws + DEF-STRICT-IN-L; no codes
;;;   1197 nested arithmetic (pi--number-class)         DERIVED likewise, by induction on the term; no codes
;;;   1201 LENGTH(t), t typed in a class of tuples       DERIVED from the length typing law + DEF-STRICT-IN-L
;;;   1205 accessor ACC(s) under a structure hypothesis  DERIVED from the structure's IFF (typing conjunct) +
;;;                                                    DEF-STRICT-PRED + DEF-STRICT-IN-L; no codes
;;;   1210 applied structure operation on typed args    as DEF-APP, through the op's FUN typing conjunct
;;;   1226 f(a) with f in FUN(D, _), a in D             DEF-APP: DERIVED (fun-domain-apply-def), law adm-def-app
;;;   1229 a functoid with a certified instantiated body   functoid beta (schematic): no functoid encoding
;;;   1233 a predicate hypothesis's defining conjuncts  DERIVED: DEF-STRICT-PRED, the defining IFF (a member of
;;;                                                    T) instantiated at the parameters, and-elim, DEF-STRICT-*
;;;
;;; HEAD CODES ADDED (the translator of K3 must mirror them): CONST 11 = the predicate name <=, CONST 13 =
;;; the predicate name < (meta-ind.scm took 7 = ORD-LT and 9 = LIMIT-ORD).
;;;
;;; THE SCHEMAS ADMITTED (the user's decision, 2026-10-13; agent META-6).  DEF-STRICT-IN-L, DEF-STRICT-IN-R,
;;; DEF-TOTAL, DEF-BINDER, DEF-COMP and DEF-LIST entered the core as CR-DEF-STRICT-IN-L .. CR-DEF-LIST
;;; (structure-library/meta-core.scm, section 4.7, each with its claim); their admissibility is the closure
;;; law of the core relation (theorem-library/meta-def-laws.scm, section 4).  DEF-STRICT-EQ-R left the table
;;; of schemas: the core's eq-subst became two-way (CR-EQ-SUBST-SYM) and adm-def-strict-eq-r is DERIVED.
;;; Then still schemas: DEF-STRICT-ARG, DEF-STRICT-DOM (the walk down the strict constructors and into a
;;; binder's domain, row 1169) and the strictness of a predicate application (row 1172, not encoded).
;;;
;;; THE SCHEMAS ADMITTED (the user's decision, 2026-10-14; agent META-7).  DEF-STRICT-ARG and DEF-STRICT-DOM
;;; entered the core as CR-DEF-STRICT-ARG and CR-DEF-STRICT-DOM (meta-core.scm 4.7, (6) and (7), each with its
;;; claim); STRICT-HEAD moved to meta-core.scm with them.  Still a schema, not admitted: the strictness of a
;;; predicate application (DEF-STRICT-PRED, row 1172), which waits for predicate codes in the encoding.
;;;
;;; THE ROWS R4 CHANGED, RE-TRANSCRIBED against b25dd06's pi--defined? (primitive-inferences.scm 1194-1265 and
;;; its helpers; agent META-7, 2026-10-14; section 5 below):
;;;   1081-1112 strict-hyp, and the SEP-membership clause of pi--atom-certifies? (new in R4)
;;;        DEF-STRICT-HYP: a derivable sentence f; f2 reached from f by and-elimination and by reading a
;;;        membership y in SEP x D. P as P[x := y] (TRUE-REACH); f2 an IN or = atom; t reached from a side of
;;;        f2 by STRICT-STEP (down a strict constructor, into a binder's domain; STRICT-REACH).  ADMISSIBLE over
;;;        the core with CR-DEF-STRICT-IN-L/R, the derived strictness of =, CR-DEF-STRICT-ARG, CR-DEF-STRICT-DOM,
;;;        sep-mem, iff-elim, and-elim (meta-def-laws.scm, section 5).  NOT covered, and why:
;;;          - an atom <= or < (on its own or as a SEP conjunct): its sides are arguments of a predicate
;;;            application (head 10), so the first step needs DEF-STRICT-PRED (not admitted; stop);
;;;          - a def-functoid application, walked through its instantiated body (pi--sob-walk) or read as a
;;;            SEP through nested functoids (pi--sep-form): the encoding has no functoid records (as 1229);
;;;          - a head the encoding has no code for (PAIR, POWER, the arithmetic heads, ...): the translator's.
;;;   1217 NTH(k, LIST l), the LIST certified by pi--sets-defined? (R4)
;;;        DEF-NTH-LIST: one premise [g, e_i in SET] per entry, as DEF-LIST.  DERIVED: CR-DEF-LIST,
;;;        CR-DEF-STRICT-IN-L, CR-NTH-EQ and eq-subst (meta-def-laws.scm, def-nth-list-derived).  Finding 0.2 is
;;;        retired in the kernel; DEF-NTH-LIT is kept as the record of the clause before R4.
;;;   1225 NTH(k, F(..)) through a functoid body          unchanged: functoid beta, no functoid encoding.

;;; -----------------------------------------------------------------------
;;; 0. Helpers (as meta-ind.scm's mi--ex / mi--and, renamed).

(define (md--ex vars body)
  (if (null? vars) body `(FORSOME ,(car vars) ,(md--ex (cdr vars) body))))
(define (md--and . fs)
  (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(apply md--and (cdr fs)))))
(define md--rel-names '())
(define (md--rel! name note body)
  (def-predicate name '(mdt_ mdhs_ mdc_) (md--and '(IN mdc_ SEQ-SET) body))
  (notation! name 'kind 'predicate 'arity 3 'english note)
  (set! md--rel-names (append md--rel-names (list name))))

;;; -----------------------------------------------------------------------
;;; 1. The head classes the clauses name.

;; The constructor heads an application of which is STRICT in its arguments (1052-1068, the walk of
;; pi--subterm-outside-binders?, RESTRICTED to genuine constructors).  STRICT-HEAD is defined in
;; structure-library/meta-core.scm, section 4.7 (moved there 2026-10-14, META-7, when DEF-STRICT-ARG was
;; admitted into the core as CR-DEF-STRICT-ARG); its codes and the reading of 7 and 8 are recorded there.
;; The TOTAL class constructors (*total-term-heads*, 698): a class term on defined arguments denotes.
;; Encoded: 11 UNION, 12 INTERSECTION, 13 CARTESIAN, 14 TUPLES, 19 FUN, 30 succ, 31 succ_ORD.
;; TOTAL-HEAD is defined in structure-library/meta-core.scm, section 4.7 (moved there 2026-10-13, META-6,
;; when DEF-TOTAL was admitted into the core as CR-DEF-TOTAL).

;;; -----------------------------------------------------------------------
;;; 2. The DEF rules.

;; 1168 / 1169 (asm-establishes-defined?, pi--strict-hyp-certifies?): IN is strict.
(md--rel! 'DEF-STRICT-IN-L "the definedness rule strict-in-left relates $2 to $3"
  (md--ex '(mdg_ mdw_ mda_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mdw_ mdw_))) '(= mdhs_ (LIST (LIST mdg_ (ENC-IN mdw_ mda_)))))))
(md--rel! 'DEF-STRICT-IN-R "the definedness rule strict-in-right relates $2 to $3"
  (md--ex '(mdg_ mdw_ mda_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mda_ mda_))) '(= mdhs_ (LIST (LIST mdg_ (ENC-IN mdw_ mda_)))))))
;; = is strict (the same clauses).
(md--rel! 'DEF-STRICT-EQ-L "the definedness rule strict-eq-left relates $2 to $3"
  (md--ex '(mdg_ mds_ mdu_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mds_ mds_))) '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ mds_ mdu_)))))))
(md--rel! 'DEF-STRICT-EQ-R "the definedness rule strict-eq-right relates $2 to $3"
  (md--ex '(mdg_ mds_ mdu_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mdu_ mdu_))) '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ mds_ mdu_)))))))
;; 1052-1068: down a strict constructor: an argument of a defined application of a strict head is defined;
;; the DOMAIN of a defined SEP / BIG-UNION / VNB-LAMBDA (22 / 24 / 26) is defined.  ADMITTED 2026-10-14
;; (CR-DEF-STRICT-ARG, CR-DEF-STRICT-DOM, meta-core.scm 4.7).
(md--rel! 'DEF-STRICT-ARG "the definedness rule strict-argument relates $2 to $3"
  (md--ex '(mdg_ mdh_ mdl_ mdi_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (NTH mdi_ mdl_) (NTH mdi_ mdl_))))
             '(STRICT-HEAD mdh_) '(IN mdi_ NN) '(<= 1 mdi_) '(<= mdi_ (LENGTH mdl_))
             '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ (EAPP mdh_ mdl_) (EAPP mdh_ mdl_))))))))
(md--rel! 'DEF-STRICT-DOM "the definedness rule strict-domain relates $2 to $3"
  (md--ex '(mdg_ mdh_ mda_ mdb_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mda_ mda_)))
             '(OR (= mdh_ 22) (OR (= mdh_ 24) (= mdh_ 26)))
             '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ (EBIND mdh_ 1 (LIST mda_) mdb_) (EBIND mdh_ 1 (LIST mda_) mdb_))))))))
;; 1176: a total class constructor on defined arguments (one premise per argument).
(md--rel! 'DEF-TOTAL "the definedness rule total-constructor relates $2 to $3"
  (md--ex '(mdg_ mdh_ mdl_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (EAPP mdh_ mdl_) (EAPP mdh_ mdl_)))) '(TOTAL-HEAD mdh_)
             '(= (LENGTH mdhs_) (LENGTH mdl_))
             '(FORALL mdi_ (IMPLIES (IN mdi_ NN) (IMPLIES (<= 1 mdi_) (IMPLIES (<= mdi_ (LENGTH mdl_))
                (= (NTH mdi_ mdhs_) (LIST mdg_ (ENC-EQ (NTH mdi_ mdl_) (NTH mdi_ mdl_)))))))))))
;; 1178: SEP / BIG-UNION / VNB-LAMBDA over a defined domain.
(md--rel! 'DEF-BINDER "the definedness rule binder-domain relates $2 to $3"
  (md--ex '(mdg_ mdh_ mda_ mdb_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (EBIND mdh_ 1 (LIST mda_) mdb_) (EBIND mdh_ 1 (LIST mda_) mdb_))))
             '(OR (= mdh_ 22) (OR (= mdh_ 24) (= mdh_ 26)))
             '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ mda_ mda_)))))))
;; 1180: COMP, unconditionally.
(md--rel! 'DEF-COMP "the definedness rule comprehension relates $2 to $3"
  (md--ex '(mdg_ mdp_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (ENC-COMP mdp_) (ENC-COMP mdp_)))) '(= mdhs_ (LIST)))))
;; 1174 (pi--sets-defined?): a list every entry of which is a set (one premise per entry).
(md--rel! 'DEF-LIST "the definedness rule list relates $2 to $3"
  (md--ex '(mdg_ mdl_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (ENC-LIST mdl_) (ENC-LIST mdl_))))
             '(= (LENGTH mdhs_) (LENGTH mdl_))
             '(FORALL mdi_ (IMPLIES (IN mdi_ NN) (IMPLIES (<= 1 mdi_) (IMPLIES (<= mdi_ (LENGTH mdl_))
                (= (NTH mdi_ mdhs_) (LIST mdg_ (ENC-IN (NTH mdi_ mdl_) ENC-SETC))))))))))
;; 1181-1185, AS THE KERNEL HAS IT (finding 0.2): NTH(k, [l]) from the k-th entry alone.
(md--rel! 'DEF-NTH-LIT "the kernel's definedness clause nth-of-literal relates $2 to $3"
  (md--ex '(mdg_ mdl_ mdk_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (ENC-NTH (ENC-NUM mdk_) (ENC-LIST mdl_)) (ENC-NTH (ENC-NUM mdk_) (ENC-LIST mdl_)))))
             '(IN mdk_ NN) '(<= 1 mdk_) '(<= mdk_ (LENGTH mdl_))
             '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ (NTH mdk_ mdl_) (NTH mdk_ mdl_))))))))
;; 1226 (pi--fun-typed-app?): f(a) with f in FUN(D) and a in D.  FUN with one argument is FUN(D), the
;; functions with domain D (library.scm, fun-domain-apply-def); FUN(D, B) reaches it by fun-codomain-iff.
(def-functoid 'ENC-FUN1 '(mdp_) '(EAPP 19 (LIST mdp_)))
(notation! 'ENC-FUN1 'kind 'functoid 'arity 1 'english "the encoded functions with domain $1")
(md--rel! 'DEF-APP "the definedness rule application relates $2 to $3"
  (md--ex '(mdg_ mdf_ mdd_ mda_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (ENC-APPLY mdf_ mda_) (ENC-APPLY mdf_ mda_))))
             '(= mdhs_ (LIST (LIST mdg_ (ENC-IN mdf_ (ENC-FUN1 mdd_))) (LIST mdg_ (ENC-IN mda_ mdd_)))))))

;;; -----------------------------------------------------------------------
;;; 3. Admissibility of a rule, as a closure property of DERIVABLE(T) (the hypotheses-on-T form of
;;; meta-ind.scm section 4): ADM-X(T) says DERIVABLE(T) is closed under DEF-X.  A SCHEMA of the table is
;;; one whose ADM-X is not derivable over the core and enters the core (or T's hypotheses) by decision; a
;;; DERIVED one has its ADM-X proven in theorem-library/meta-def-laws.scm.
(define (md--adm! name rel)
  (def-predicate name '(mdt_)
    `(FORALL mdhs_ (FORALL mdc_ (IMPLIES (,rel mdt_ mdhs_ mdc_) (IMPLIES (HYPS-IN mdhs_ (DERIVABLE mdt_))
                                   (IN mdc_ (DERIVABLE mdt_)))))))
  (notation! name 'kind 'predicate 'arity 1 'english (string-append "the core over $1 is closed under " (symbol->string rel))))
(md--adm! 'ADM-DEF-STRICT-IN-L 'DEF-STRICT-IN-L)
(md--adm! 'ADM-DEF-COMP 'DEF-COMP)
(md--adm! 'ADM-DEF-STRICT-IN-R 'DEF-STRICT-IN-R)
(md--adm! 'ADM-DEF-STRICT-ARG 'DEF-STRICT-ARG)
(md--adm! 'ADM-DEF-STRICT-DOM 'DEF-STRICT-DOM)

;;; -----------------------------------------------------------------------
;;; 4. The encoded catalog axiom DEF-APP is derived from.
;;;  fun-domain-apply-def (library.scm 473):  forall A f x. f in FUN(A) => (f(x) = f(x) iff x in A)
;;;  (A = index 2, f = index 1, x = index 0 under the innermost binder).
(def-constant 'AX-FUN-APP
  '(ax-fun-app-def
     (== AX-FUN-APP
         (ENC-ALL (ENC-ALL (ENC-ALL (ENC-IMP (ENC-IN (EBVAR 1) (ENC-FUN1 (EBVAR 2)))
                                             (ENC-IFF (ENC-EQ (ENC-APPLY (EBVAR 1) (EBVAR 0)) (ENC-APPLY (EBVAR 1) (EBVAR 0)))
                                                      (ENC-IN (EBVAR 0) (EBVAR 2))))))))))
(notation! 'AX-FUN-APP 'kind 'constant 'arity 0 'english "the encoded axiom fun-domain-apply-def")

;;; -----------------------------------------------------------------------
;;; 5. THE ROWS R4 CHANGED, RE-TRANSCRIBED against b25dd06 (agent META-7, 2026-10-14).  Binders: md7*_.

;; THE WALK BELOW THE TOP OF AN ATOM (pi--sob-walk, 1061-1079).  One step: from an application of a strict
;; head to an argument, from a SEP / BIG-UNION / VNB-LAMBDA to its domain.  The kernel walks nothing else
;; that the encoding has a code for: not FORALL FORSOME IOTA COMP (20 21 25 23), not IF (27), not a binder's
;; body.
(def-predicate 'STRICT-STEP '(md7s_ md7t_)
  '(OR (FORSOME md7h_ (FORSOME md7l_ (FORSOME md7i_
         (AND (= md7s_ (EAPP md7h_ md7l_))
              (AND (STRICT-HEAD md7h_)
                   (AND (IN md7i_ NN) (AND (<= 1 md7i_) (AND (<= md7i_ (LENGTH md7l_)) (= md7t_ (NTH md7i_ md7l_))))))))))
       (FORSOME md7k_ (FORSOME md7a_ (FORSOME md7b_
         (AND (OR (= md7k_ 22) (OR (= md7k_ 24) (= md7k_ 26)))
              (AND (= md7s_ (EBIND md7k_ 1 (LIST md7a_) md7b_)) (= md7t_ md7a_))))))))
(notation! 'STRICT-STEP 'kind 'predicate 'arity 2 'english "$2 is one strict step below $1")
(def-predicate 'STRICT-CLOSED '(md7x_)
  '(FORALL md7p_ (FORALL md7q_ (IMPLIES (IN md7p_ md7x_) (IMPLIES (STRICT-STEP md7p_ md7q_) (IN md7q_ md7x_))))))
(notation! 'STRICT-CLOSED 'kind 'predicate 'arity 1 'english "$1 is closed under strict steps")
;; the expressions reached from e by strict steps (e included): the least closed subset of EXPR-SET with e
(def-functoid 'STRICT-REACH '(md7e_)
  '(SEP md7z_ EXPR-SET (FORALL md7w_ (IMPLIES (IN md7w_ (POWER EXPR-SET))
                          (IMPLIES (IN md7e_ md7w_) (IMPLIES (STRICT-CLOSED md7w_) (IN md7z_ md7w_)))))))
(notation! 'STRICT-REACH 'kind 'functoid 'arity 1 'english "the expressions reached from $1 by strict steps")

;; THE SENTENCES A TRUE SENTENCE MAKES TRUE, as the kernel reads them (pi--atom-certifies?, 1101-1112, the
;; SEP-membership clause of R4, and pi--and-conjuncts): a conjunct of a conjunction, and P[x := y] from a
;; membership y in SEP x D. P.  (The kernel starts from an atom and splits only P[x := y]; reading every
;; conjunction is a superset, sound by and-elim.)
(def-predicate 'TRUE-STEP '(md7f_ md7g_)
  '(OR (FORSOME md7c_ (FORSOME md7d_ (AND (= md7f_ (ENC-AND md7c_ md7d_)) (OR (= md7g_ md7c_) (= md7g_ md7d_)))))
       (FORSOME md7y_ (FORSOME md7o_ (FORSOME md7r_
         (AND (= md7f_ (ENC-IN md7y_ (ENC-SEP md7o_ md7r_))) (= md7g_ (EXPR-OPEN md7r_ 0 md7y_))))))))
(notation! 'TRUE-STEP 'kind 'predicate 'arity 2 'english "$2 is one step of truth below $1")
(def-predicate 'TRUE-CLOSED '(md7v_)
  '(FORALL md7m_ (FORALL md7n_ (IMPLIES (IN md7m_ md7v_) (IMPLIES (TRUE-STEP md7m_ md7n_) (IN md7n_ md7v_))))))
(notation! 'TRUE-CLOSED 'kind 'predicate 'arity 1 'english "$1 is closed under steps of truth")
(def-functoid 'TRUE-REACH '(md7j_)
  '(SEP md7zz_ EXPR-SET (FORALL md7ww_ (IMPLIES (IN md7ww_ (POWER EXPR-SET))
                           (IMPLIES (IN md7j_ md7ww_) (IMPLIES (TRUE-CLOSED md7ww_) (IN md7zz_ md7ww_)))))))
(notation! 'TRUE-REACH 'kind 'functoid 'arity 1 'english "the sentences reached from $1 by steps of truth")

;; An atom IN or = certifies the terms reached from either side (the kernel's atoms <= and < are predicate
;; applications, head 10: their sides need DEF-STRICT-PRED, which is not admitted).
(def-predicate 'STRICT-ATOM '(md7af_ md7at_)
  '(FORSOME md7ax_ (FORSOME md7ay_
     (AND (OR (= md7af_ (ENC-IN md7ax_ md7ay_)) (= md7af_ (ENC-EQ md7ax_ md7ay_)))
          (OR (IN md7at_ (STRICT-REACH md7ax_)) (IN md7at_ (STRICT-REACH md7ay_)))))))
(notation! 'STRICT-ATOM 'kind 'predicate 'arity 2 'english "the atom $1 certifies the term $2")

;; 1081-1112 (pi--strict-hyp-certifies?, pi--atom-certifies?), RE-TRANSCRIBED: the fact f (a premise, by the
;; conventions above), a sentence f2 it makes true, an atom, and a term below a side.
(md--rel! 'DEF-STRICT-HYP "the definedness rule strict-hypothesis relates $2 to $3"
  (md--ex '(mdg_ mdf_ md7h2_ mdw_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mdw_ mdw_))) '(= mdhs_ (LIST (LIST mdg_ mdf_)))
             '(IN md7h2_ (TRUE-REACH mdf_)) '(STRICT-ATOM md7h2_ mdw_))))
(md--adm! 'ADM-DEF-STRICT-HYP 'DEF-STRICT-HYP)

;; 1217-1221 (R4): NTH(k, [l]) when the LIST is certified, i.e. every entry a set (pi--sets-defined?, read
;; as DEF-LIST reads it: one premise per entry).
(md--rel! 'DEF-NTH-LIST "the definedness rule nth-of-list relates $2 to $3"
  (md--ex '(mdg_ mdl_ mdk_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (ENC-NTH (ENC-NUM mdk_) (ENC-LIST mdl_)) (ENC-NTH (ENC-NUM mdk_) (ENC-LIST mdl_)))))
             '(IN mdk_ NN) '(<= 1 mdk_) '(<= mdk_ (LENGTH mdl_))
             '(= (LENGTH mdhs_) (LENGTH mdl_))
             '(FORALL mdi_ (IMPLIES (IN mdi_ NN) (IMPLIES (<= 1 mdi_) (IMPLIES (<= mdi_ (LENGTH mdl_))
                (= (NTH mdi_ mdhs_) (LIST mdg_ (ENC-IN (NTH mdi_ mdl_) ENC-SETC))))))))))
(md--adm! 'ADM-DEF-NTH-LIST 'DEF-NTH-LIST)
