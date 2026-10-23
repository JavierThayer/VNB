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
;;;        ADMITTED 2026-10-17 (META-10): CR-DEF-STRICT-PRED with the predicate codes PRED-CODE; the clause is
;;;        DEF-STRUCT-HYP (section 6), DERIVED.
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
;;;        ENCODED 2026-10-17 (META-10) for a ONE-parameter predicate: DEF-PRED-UNFOLD and DEF-PRED-HYP
;;;        (section 6), DERIVED; the accessor clause (1205, 1239) is DEF-PRED-HYP at a structure predicate.
;;;        EXTENDED 2026-10-22 (K2-END, section 8): a predicate of ANY number of parameters (DEF-PRED-UNFOLD-N),
;;;        the body's FORSOMEs, the nested reading, the class form s in X and the parent chain (DEF-PRED-HYP-N,
;;;        DEF-CERT-HYP, through the least set CERT-SET), DERIVED.  Still a row of its own: the view clause.
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
;;; THE SCHEMA ADMITTED (the user's decision, 2026-10-17, "yes do the predicate case"; agent META-10).
;;; DEF-STRICT-PRED entered the core as CR-DEF-STRICT-PRED (meta-core.scm 4.7, (8), with its claim and the
;;; precondition of its soundness), and the encoding has PREDICATE CODES (PRED-CODE, meta-core.scm 4.7).
;;; With it (section 6 below; theorem-library/meta-ind-laws.scm section L, meta-def-laws.scm section 6):
;;;   - STRICT-ATOM gains the predicate atoms: the kernel's strict atoms <= and < (ENC-LE, ENC-LT below),
;;;     alone or as SEP conjuncts, are covered by DEF-STRICT-HYP;
;;;   - the structure-hypothesis clause (pi--structure-hyp, primitive-inferences.scm 989 / 1203) is
;;;     DEF-STRUCT-HYP, an instance of DEF-STRICT-PRED;
;;;   - the predicate-hypothesis clause (pi--via-pred-hyps?, 1170 / 1263) and the accessor clause
;;;     (pi--accessor-certified?, 836, and 1239) are DEF-PRED-HYP for a ONE-parameter predicate: the
;;;     definition (a derivable sentence: a member of T by theorem-assumption, or proven) instantiated at
;;;     the argument, whose definedness DEF-STRICT-PRED supplies, then iff-elim (DEF-PRED-UNFOLD), then the
;;;     walks of section 5.  NOT covered then: predicates of two or more parameters (the encoding has no iterated
;;;     instantiation; each further parameter is one more forall-elim of the same shape); the body's leading
;;;     FORSOMEs, which the kernel strips to fresh witnesses (a forsome-elim per binder); the view clause of
;;;     pi--accessor-certified? and every functoid row (no functoid encoding).  The first two are covered since
;;;     2026-10-22 (section 8), the functoid rows since 2026-10-21 (section 7).  The nested reading
;;;     (depth < 3: a conjunct that is itself a predicate hypothesis) is the composition of these admissible
;;;     steps: DEF-PRED-UNFOLD and adm-true-walk each take a derivable sequent to a derivable sequent.
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

;; An atom IN or = certifies the terms reached from either side.  SECOND DISJUNCT (agent META-10, 2026-10-17,
;; with DEF-STRICT-PRED admitted): a PREDICATE atom, head 10 with a predicate code first (the kernel's atoms
;; <= and <, ENC-LE / ENC-LT below; any def-predicate or structure predicate), certifies the terms reached from
;; each of its arguments.  (Before: "the kernel's atoms <= and < are predicate applications, head 10: their sides
;; need DEF-STRICT-PRED, which is not admitted.")  The kernel's pi--atom-certifies? reads IN = <= < only; the
;; relation reads every predicate atom, a superset, admissible as such.
(def-predicate 'STRICT-ATOM '(md7af_ md7at_)
  '(OR (FORSOME md7ax_ (FORSOME md7ay_
         (AND (OR (= md7af_ (ENC-IN md7ax_ md7ay_)) (= md7af_ (ENC-EQ md7ax_ md7ay_)))
              (OR (IN md7at_ (STRICT-REACH md7ax_)) (IN md7at_ (STRICT-REACH md7ay_))))))
       (FORSOME md7pl_ (FORSOME md7pk_ (FORSOME md7pi_
         (AND (= md7af_ (EAPP 10 md7pl_))
              (AND (= (NTH 1 md7pl_) (ECONST md7pk_))
                   (AND (PRED-CODE md7pk_)
                        (AND (IN md7pi_ NN)
                             (AND (<= 2 md7pi_)
                                  (AND (<= md7pi_ (LENGTH md7pl_))
                                       (IN md7at_ (STRICT-REACH (NTH md7pi_ md7pl_))))))))))))))
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

;;; -----------------------------------------------------------------------
;;; 6. DEF-STRICT-PRED AND THE CLAUSES THAT WAITED FOR IT (agent META-10, 2026-10-17).  Binders: md10*_.

;; 1172: the strictness of a predicate application, as the core has it (CR-DEF-STRICT-PRED, meta-core.scm 4.7
;; (8)): from [g, P(l)], P a predicate constant (PRED-CODE), [g, l_i = l_i] for i = 2 .. |l|.  ADMITTED.
(md--rel! 'DEF-STRICT-PRED "the definedness rule strict-predicate relates $2 to $3"
  (md--ex '(mdg_ mdl_ mdk_ mdi_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (NTH mdi_ mdl_) (NTH mdi_ mdl_))))
             '(= (NTH 1 mdl_) (ECONST mdk_)) '(PRED-CODE mdk_)
             '(IN mdi_ NN) '(<= 2 mdi_) '(<= mdi_ (LENGTH mdl_))
             '(= mdhs_ (LIST (LIST mdg_ (EAPP 10 mdl_)))))))
(md--adm! 'ADM-DEF-STRICT-PRED 'DEF-STRICT-PRED)

;; The encoded predicate atoms the clauses name.  CONST 11 = <=, CONST 13 = < (the codes of the header);
;; ENC-PRED1(n, p) is the atom of a ONE-parameter predicate whose name is the expression n (a CONST).
(def-functoid 'ENC-LE '(md10x_ md10y_) '(EAPP 10 (LIST (ECONST 11) md10x_ md10y_)))
(def-functoid 'ENC-LT '(md10x_ md10y_) '(EAPP 10 (LIST (ECONST 13) md10x_ md10y_)))
(def-functoid 'ENC-PRED1 '(md10n_ md10p_) '(EAPP 10 (LIST md10n_ md10p_)))
(notation! 'ENC-LE 'kind 'functoid 'arity 2 'english "the encoded atom $1 <= $2")
(notation! 'ENC-LT 'kind 'functoid 'arity 2 'english "the encoded atom $1 < $2")
(notation! 'ENC-PRED1 'kind 'functoid 'arity 2 'english "the encoded atom of the one-place predicate named $1 at $2")

;; 989 / 1203 (pi--structure-hyp): a structure hypothesis IS-X(s) certifies s.  The other form of the clause,
;; s in X, is DEF-STRICT-IN-L.  DERIVED: DEF-STRICT-PRED at i = 2 (meta-def-laws.scm, def-struct-hyp-derived).
(md--rel! 'DEF-STRUCT-HYP "the definedness rule structure-hypothesis relates $2 to $3"
  (md--ex '(mdg_ mdk_ mds_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mds_ mds_))) '(PRED-CODE mdk_)
             '(= mdhs_ (LIST (LIST mdg_ (ENC-PRED1 (ECONST mdk_) mds_)))))))
(md--adm! 'ADM-DEF-STRUCT-HYP 'DEF-STRUCT-HYP)

;; THE UNFOLDING OF A ONE-PARAMETER DEFINITION at a predicate hypothesis: from [g, P(s)] and the definition
;; [g, forall x. P(x) iff b] (derivable: a member of T, read by theorem-assumption, or a proven sentence),
;; [g, b[x := s]].  DERIVED (meta-ind-laws.scm, section L, def-pred-unfold-derived): the instance at s owes
;; s = s, which DEF-STRICT-PRED gives from P(s); then iff-elim.  Without DEF-STRICT-PRED the core cannot
;; instantiate the definition at a compound s at all.
(md--rel! 'DEF-PRED-UNFOLD "the definedness rule predicate-unfolding relates $2 to $3"
  (md--ex '(mdg_ mdk_ mds_ mdb_)
    (md--and '(= mdc_ (LIST mdg_ (EXPR-OPEN mdb_ 0 mds_))) '(PRED-CODE mdk_)
             '(= mdhs_ (LIST (LIST mdg_ (ENC-PRED1 (ECONST mdk_) mds_))
                             (LIST mdg_ (ENC-ALL (ENC-IFF (ENC-PRED1 (ECONST mdk_) (EBVAR 0)) mdb_))))))))
(md--adm! 'ADM-DEF-PRED-UNFOLD 'DEF-PRED-UNFOLD)

;; 1170 / 1263 (pi--via-pred-hyps?) and 836 / 1239 (the accessor clause, IS-X(s) certifying ACC(s): the
;; structure's IFF types the slot): a predicate hypothesis certifies what an atom its unfolded body makes true
;; certifies.  One parameter; the body's sentences read as section 5 reads them.  DERIVED (meta-def-laws.scm,
;; def-pred-hyp-derived: DEF-PRED-UNFOLD, adm-true-walk, adm-strict-atom).
(md--rel! 'DEF-PRED-HYP "the definedness rule predicate-hypothesis relates $2 to $3"
  (md--ex '(mdg_ mdk_ mds_ mdb_ md10f_ mdw_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mdw_ mdw_))) '(PRED-CODE mdk_)
             '(= mdhs_ (LIST (LIST mdg_ (ENC-PRED1 (ECONST mdk_) mds_))
                             (LIST mdg_ (ENC-ALL (ENC-IFF (ENC-PRED1 (ECONST mdk_) (EBVAR 0)) mdb_)))))
             '(IN md10f_ (TRUE-REACH (EXPR-OPEN mdb_ 0 mds_))) '(STRICT-ATOM md10f_ mdw_))))
(md--adm! 'ADM-DEF-PRED-HYP 'DEF-PRED-HYP)

;;; -----------------------------------------------------------------------
;;; 7. THE FUNCTOID ROWS (agent META-FUN, 2026-10-21; the user's decision B1: the functoid table FUN-DEF and
;;; the rule functoid-beta-eq, structure-library/meta-core.scm 4.10).  Re-transcribed against the CURRENT
;;; kernel's pi--defined? and its helpers (primitive-inferences.scm, md5 b2c1422a; rule-checkers-logic.scm,
;;; md5 02411d9b), the record rows against the repair running in parallel (an applied anonymous record walked
;;; through its contraction in pi--sob-walk and chk-sob; under a record binder a term mentioning the
;;; record's variable not certified).  A kernel functoid term is encoded as the application EAPP(h, l) of a
;;; row (h, |l|, b) of FUN-DEF, its instantiated body as OPENL(b, l, |l|) (a record lambda-lifted, its free
;;; variables the first entries of l).  Binders: md11*_.
;;;   F1  pi--defined?, the functoid clause: F(a) certified when its instantiated body is   DEF-FUN-INST
;;;   F2  pi--defined?, NTH(k, F(a)) certified when NTH(k, body[a]) is                     DEF-FUN-NTH
;;;   F3  pi--sob-walk (and chk-sob), the registry arm: a strict walk goes from F(a) into   DEF-FUN-STRICT
;;;       body[a]; with the repair, the same arm for an applied record (lambda-lifted)
;;;   F4  pi--sep-form (and the checker's): y in F(a) read as y in body[a], through nested DEF-FUN-SEP
;;;       functoids, until a SEP is reached (then TRUE-STEP's SEP reading)
;;; Each is DERIVED (theorem-library/meta-def-laws.scm, section 7): functoid-beta-eq gives F(l) == b[l], and
;;; eq-subst carries the premise along it.  Composed with the walks of section 5 they give the kernel's
;;; interleaved walks (each step takes a derivable sequent to a derivable sequent).  NOT a row: the view
;;; clause of pi--accessor-certified? (ACC(V(r)) certified when the corresponding component of V's LIST body
;;; is): it reads ONE component of a list whose definedness it does not establish, and over the core
;;; NTH(k, [..]) == the k-th entry needs the whole list to denote (CR-NTH-EQ); not admissible, not shown
;;; unsound, left as found (the user's instruction, 2026-10-21).
(md--rel! 'DEF-FUN-INST "the definedness rule functoid-instance relates $2 to $3"
  (md--ex '(mdg_ mdh_ mdl_ mdb_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (EAPP mdh_ mdl_) (EAPP mdh_ mdl_))))
             '(FUN-DEF mdh_ (LENGTH mdl_) mdb_)
             '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ (OPENL mdb_ mdl_ (LENGTH mdl_)) (OPENL mdb_ mdl_ (LENGTH mdl_)))))))))
(md--rel! 'DEF-FUN-STRICT "the definedness rule functoid-strict-step relates $2 to $3"
  (md--ex '(mdg_ mdh_ mdl_ mdb_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (OPENL mdb_ mdl_ (LENGTH mdl_)) (OPENL mdb_ mdl_ (LENGTH mdl_)))))
             '(FUN-DEF mdh_ (LENGTH mdl_) mdb_)
             '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ (EAPP mdh_ mdl_) (EAPP mdh_ mdl_))))))))
(md--rel! 'DEF-FUN-NTH "the definedness rule nth-of-functoid relates $2 to $3"
  (md--ex '(mdg_ mdh_ mdl_ mdb_ mdk_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ (ENC-NTH (ENC-NUM mdk_) (EAPP mdh_ mdl_)) (ENC-NTH (ENC-NUM mdk_) (EAPP mdh_ mdl_)))))
             '(FUN-DEF mdh_ (LENGTH mdl_) mdb_) '(IN mdk_ NN)
             '(= mdhs_ (LIST (LIST mdg_ (ENC-EQ (ENC-NTH (ENC-NUM mdk_) (OPENL mdb_ mdl_ (LENGTH mdl_)))
                                                (ENC-NTH (ENC-NUM mdk_) (OPENL mdb_ mdl_ (LENGTH mdl_))))))))))
(md--rel! 'DEF-FUN-SEP "the definedness rule functoid-membership relates $2 to $3"
  (md--ex '(mdg_ mdh_ mdl_ mdb_ md11y_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-IN md11y_ (OPENL mdb_ mdl_ (LENGTH mdl_)))))
             '(FUN-DEF mdh_ (LENGTH mdl_) mdb_)
             '(= mdhs_ (LIST (LIST mdg_ (ENC-IN md11y_ (EAPP mdh_ mdl_))))))))
(md--adm! 'ADM-DEF-FUN-INST 'DEF-FUN-INST)
(md--adm! 'ADM-DEF-FUN-STRICT 'DEF-FUN-STRICT)
(md--adm! 'ADM-DEF-FUN-NTH 'DEF-FUN-NTH)
(md--adm! 'ADM-DEF-FUN-SEP 'DEF-FUN-SEP)

;;; -----------------------------------------------------------------------
;;; 8. THE META-10 LEFTOVERS (agent K2-END, 2026-10-22): the predicate-hypothesis and accessor clauses for a
;;; predicate of ANY number of parameters, the body's FORSOMEs, the nested reading, the class form s in X and
;;; the parent chain.  Re-transcribed against the current kernel (primitive-inferences.scm: pi--pred-def-conjuncts,
;;; pi--raw-conjuncts-certify?, pi--via-pred-hyps?, pi--structure-hyp, pi--structure-def-for, pi--accessor-certified?
;;; first branch, and the accessor clause of pi--defined?).  Binders: md12*_.
;;;   K1  pi--pred-def-conjuncts: the definition  forall x1 .. xn. P(x1 .. xn) iff body  instantiated at the
;;;       arguments a1 .. an of the hypothesis P(a1 .. an), one FORALL per argument      INST-REACH, DEF-PRED-UNFOLD-N
;;;   K2  the same: the instantiated body's LEADING FORSOMEs stripped to fresh (uninterned) witnesses   CERT-STEP (c)
;;;   K3  pi--raw-conjuncts-certify?: a conjunct certifies by pi--atom-certifies? (IN = <= <, and the SEP reading),
;;;       by a structure predicate IS-Y(c) (c itself, and ACC(c) for a slot ACC of Y), or, at depth < 3, as a
;;;       predicate hypothesis in its turn, through ITS definition                          CERT-STEP (a), (b), (d)
;;;   K4  pi--structure-hyp, the class form  s in X  (X a structure's class name, the class axiom
;;;       forall s. s in X iff IS-X(s), structures.scm), read through the parent chain of
;;;       pi--structure-def-for (IS-COMMUTATIVE-RING -> RING: the refinement's IFF has the parent conjunct first)
;;;                                                                                          CERT-STEP (e), (d)
;;;   K5  the accessor clauses (pi--accessor-certified? first branch; pi--defined?, ACC(s) under pi--structure-hyp):
;;;       ACC(s) by the typing conjunct of the structure's IFF, directly or through the chain  DEF-PRED-HYP-N, DEF-CERT-HYP
;;; THE READING.  A sentence f "certifies" w in the context g when the kernel's walks reach, from f, an atom of
;;; which w is a strict subterm.  CERT-SET(T, g, w) is the LEAST set of expressions closed under the five steps
;;; of CERT-STEP: an atom that certifies w (STRICT-ATOM, section 5); a sentence f2 that f makes true
;;; (TRUE-REACH(f), section 5) and that certifies w; an existential whose body, opened at a name free neither in
;;; g + f nor in w = w, certifies w (the forsome-elim of a stripped FORSOME: the kernel's uninterned witness is
;;; such a name); a predicate atom P(l) whose definition, derivable in g, instantiated at the arguments gives
;;; P(l) iff b with b certifying w (K1, K3 at depth < 3, K4's chain); a membership s in A whose class axiom,
;;; derivable in g, instantiated at s gives (s in A) iff b with b certifying w (K4).  The relation reads every
;;; conjunction, every FORSOME and every nesting depth, where the kernel strips leading FORSOMEs only and nests to
;;; depth 3: a superset of the clauses, admissible as such (theorem-library/meta-def-laws.scm, section 8).
;;; The definitions are read as derivable sentences (a member of T by theorem-assumption, or proven), the
;;; kernel's "definitional, primitive or proven" entry (pi--pred-def-trusted?).
;; one instantiation of a universal at an ARGUMENT of the list l (an entry 2 .. |l|; for a predicate atom
;; EAPP(10, l) the entries after the name)
(def-predicate 'INST-STEP '(md12l_ md12f_ md12g_)
  '(FORSOME md12b_ (FORSOME md12i_
     (AND (= md12f_ (ENC-ALL md12b_))
          (AND (IN md12i_ NN) (AND (<= 2 md12i_) (AND (<= md12i_ (LENGTH md12l_))
               (= md12g_ (EXPR-OPEN md12b_ 0 (NTH md12i_ md12l_))))))))))
(notation! 'INST-STEP 'kind 'predicate 'arity 3 'english "$3 is $2 instantiated at an argument of $1")
(def-predicate 'INST-CLOSED '(md12l_ md12x_)
  '(FORALL md12p_ (FORALL md12q_ (IMPLIES (IN md12p_ md12x_) (IMPLIES (INST-STEP md12l_ md12p_ md12q_) (IN md12q_ md12x_))))))
(notation! 'INST-CLOSED 'kind 'predicate 'arity 2 'english "$2 is closed under instantiations at the arguments of $1")
;; the instances of d at arguments of l, d included: the least closed subset of EXPR-SET holding d
(def-functoid 'INST-REACH '(md12d_ md12l_)
  '(SEP md12z_ EXPR-SET (FORALL md12w_ (IMPLIES (IN md12w_ (POWER EXPR-SET))
      (IMPLIES (IN md12d_ md12w_) (IMPLIES (INST-CLOSED md12l_ md12w_) (IN md12z_ md12w_)))))))
(notation! 'INST-REACH 'kind 'functoid 'arity 2 'english "the instances of $1 at the arguments of $2")

;; K1: THE UNFOLDING OF A DEFINITION OF ANY NUMBER OF PARAMETERS at a predicate hypothesis: from [g, P(l)] and
;; a derivable definition d with (P(l) iff b) an instance of d at the arguments, [g, b].  DERIVED
;; (meta-def-laws.scm, def-pred-unfold-n-derived): each instance at an argument owes its definedness, which
;; CR-DEF-STRICT-PRED gives from P(l).  For one parameter it is DEF-PRED-UNFOLD (section 6).
(md--rel! 'DEF-PRED-UNFOLD-N "the definedness rule predicate-unfolding (any arity) relates $2 to $3"
  (md--ex '(mdg_ mdl_ mdk_ mdd_ mdb_)
    (md--and '(= mdc_ (LIST mdg_ mdb_)) '(= (NTH 1 mdl_) (ECONST mdk_)) '(PRED-CODE mdk_)
             '(IN (ENC-IFF (EAPP 10 mdl_) mdb_) (INST-REACH mdd_ mdl_))
             '(= mdhs_ (LIST (LIST mdg_ (EAPP 10 mdl_)) (LIST mdg_ mdd_))))))
(md--adm! 'ADM-DEF-PRED-UNFOLD-N 'DEF-PRED-UNFOLD-N)

;; K2-K5: one step of the reading, f certifying w in g (the steps (a) .. (e) of the header), X the set built so far
(def-predicate 'CERT-STEP '(md12t_ md12cg_ md12cw_ md12x_ md12f_)
  '(OR (STRICT-ATOM md12f_ md12cw_)
   (OR (FORSOME md12f2_ (AND (IN md12f2_ (TRUE-REACH md12f_)) (IN md12f2_ md12x_)))
   (OR (FORSOME md12b_ (FORSOME md12y_
         (AND (= md12f_ (ENC-EX md12b_))
              (AND (IN md12y_ NN)
                   (AND (NOT (IN md12y_ (UNION (CTX-FV (CTX-ADD md12cg_ md12f_)) (EXPR-FV (ENC-EQ md12cw_ md12cw_)))))
                        (IN (EXPR-OPEN md12b_ 0 (EFVAR md12y_)) md12x_))))))
   (OR (FORSOME md12l_ (FORSOME md12k_ (FORSOME md12d_ (FORSOME md12b2_
         (AND (= md12f_ (EAPP 10 md12l_))
              (AND (= (NTH 1 md12l_) (ECONST md12k_))
                   (AND (PRED-CODE md12k_)
                        (AND (IN (LIST md12cg_ md12d_) (DERIVABLE md12t_))
                             (AND (IN (ENC-IFF md12f_ md12b2_) (INST-REACH md12d_ md12l_))
                                  (IN md12b2_ md12x_))))))))))
       (FORSOME md12a_ (FORSOME md12s_ (FORSOME md12d3_ (FORSOME md12b3_
         (AND (= md12f_ (ENC-IN md12s_ md12a_))
              (AND (IN (LIST md12cg_ md12d3_) (DERIVABLE md12t_))
                   (AND (IN (ENC-IFF md12f_ md12b3_) (INST-REACH md12d3_ (LIST md12a_ md12s_)))
                        (IN md12b3_ md12x_)))))))))))))
(notation! 'CERT-STEP 'kind 'predicate 'arity 5 'english "$5 certifies $3 in $2 over $1 by one step into $4")
(def-predicate 'CERT-CLOSED '(md12t_ md12cg_ md12cw_ md12x_)
  '(FORALL md12e_ (IMPLIES (IN md12e_ EXPR-SET) (IMPLIES (CERT-STEP md12t_ md12cg_ md12cw_ md12x_ md12e_) (IN md12e_ md12x_)))))
(notation! 'CERT-CLOSED 'kind 'predicate 'arity 4 'english "$4 is closed under the steps certifying $3 in $2 over $1")
;; the sentences that certify w in g: the least closed subset of EXPR-SET
(def-functoid 'CERT-SET '(md12t_ md12cg_ md12cw_)
  '(SEP md12zz_ EXPR-SET (FORALL md12v_ (IMPLIES (IN md12v_ (POWER EXPR-SET))
      (IMPLIES (CERT-CLOSED md12t_ md12cg_ md12cw_ md12v_) (IN md12zz_ md12v_))))))
(notation! 'CERT-SET 'kind 'functoid 'arity 3 'english "the sentences certifying $3 in $2 over $1")

;; K1-K5 at a top-level predicate hypothesis: [g, P(l)] and its definition d derivable, b the instance of d's
;; body at the arguments, and b certifies w: [g, w = w].  It extends DEF-PRED-HYP (section 6) to any arity, to the
;; body's FORSOMEs and to the nested readings.  DERIVED (meta-def-laws.scm, def-pred-hyp-n-derived).
(md--rel! 'DEF-PRED-HYP-N "the definedness rule predicate-hypothesis (any arity) relates $2 to $3"
  (md--ex '(mdg_ mdl_ mdk_ mdd_ mdb_ mdw_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mdw_ mdw_))) '(= (NTH 1 mdl_) (ECONST mdk_)) '(PRED-CODE mdk_)
             '(IN (ENC-IFF (EAPP 10 mdl_) mdb_) (INST-REACH mdd_ mdl_))
             '(IN mdb_ (CERT-SET mdt_ mdg_ mdw_))
             '(= mdhs_ (LIST (LIST mdg_ (EAPP 10 mdl_)) (LIST mdg_ mdd_))))))
(md--adm! 'ADM-DEF-PRED-HYP-N 'DEF-PRED-HYP-N)
;; the reading at ANY derivable hypothesis f (an atom, a predicate hypothesis, a class membership): [g, f]
;; derivable and f certifying w give [g, w = w].  Its steps include the readings of DEF-STRICT-HYP (section 5),
;; DEF-STRUCT-HYP and DEF-PRED-HYP (section 6) and DEF-PRED-HYP-N.  DERIVED (meta-def-laws.scm, def-cert-hyp-derived).
(md--rel! 'DEF-CERT-HYP "the definedness rule certifying-hypothesis relates $2 to $3"
  (md--ex '(mdg_ mdf_ mdw_)
    (md--and '(= mdc_ (LIST mdg_ (ENC-EQ mdw_ mdw_))) '(IN mdf_ (CERT-SET mdt_ mdg_ mdw_))
             '(= mdhs_ (LIST (LIST mdg_ mdf_))))))
(md--adm! 'ADM-DEF-CERT-HYP 'DEF-CERT-HYP)

;;; -----------------------------------------------------------------------
;;; 9. THE MACETES OF ANY NUMBER OF SCHEMA VARIABLES, AT ONE POSITION (agent K2-END, 2026-10-22).  J-MAC
;;; (structure-library/meta-cr.scm, section 4) takes a member of T of ONE schema variable, ALL(c IMP (l == r)) or
;;; ALL(c IMP (l iff r)); an n-variable macete is an n-fold forall-elim (scratchpad/triage/META-3-REPORT.md, s.6,
;;; obstacle 3).  J-MACN reads the instance through INST-REACH (section 8): any sequence of instantiations of the
;;; member m at entries 2 .. |l| of a list l (the first entry is unread, as the predicate's name is at a predicate
;;; atom), each entry DENOTING in the local context (the macete door owes t = t for every value of the
;;; substitution, each element of a rest binding included: rule-checkers-rewrite.scm, rkw--sub-values).  The
;;; instance is the equation or equivalence itself (a macete with no condition, as the catalog's n-ary
;;; union-decompose and intersection-decompose) or an implication from one condition c (a conjunction of conditions
;;; is one formula), c derivable in the local context.  For one schema variable, J-MAC's instance OPEN(b, 0, e) is
;;; one INST-STEP from the member at the list [e0, e] (e0 unread).
;;; A RESTVAR schema of the catalog (library.scm: union-decompose, intersection-decompose) is a FAMILY of members of
;;; T, one per length of the rest binding: each of its instances is an instance of one member, at n + 1 entries.
;;; Binders: md13*_.
(def-functoid 'J-MACN '(md13t_)
  `(SEP md13x_ RW-UNIV
     ,(md--ex '(md13g_ md13m_ md13l_ md13i_ md13r_ md13a_ md13b_)
        (md--and '(IN md13m_ md13t_) '(IN md13m_ CLF) '(IN md13i_ (INST-REACH md13m_ md13l_))
                 '(FORALL md13j_ (IMPLIES (IN md13j_ NN) (IMPLIES (<= 2 md13j_) (IMPLIES (<= md13j_ (LENGTH md13l_))
                    (IN (LIST md13g_ (ENC-EQ (NTH md13j_ md13l_) (NTH md13j_ md13l_))) (DERIVABLE md13t_))))))
                 '(OR (= md13i_ md13r_)
                      (FORSOME md13c_ (AND (= md13i_ (ENC-IMP md13c_ md13r_)) (IN (LIST md13g_ md13c_) (DERIVABLE md13t_)))))
                 '(OR (AND (= md13r_ (ENC-QEQ md13a_ md13b_))
                           (AND (= md13x_ (LIST 1 md13g_ md13a_ md13b_)) (AND (IN md13a_ CLT) (IN md13b_ CLT))))
                      (AND (= md13r_ (ENC-IFF md13a_ md13b_))
                           (AND (= md13x_ (LIST 2 md13g_ md13a_ md13b_)) (AND (IN md13a_ CLF) (IN md13b_ CLF)))))))))
(notation! 'J-MACN 'kind 'functoid 'arity 1 'english "the local instances of the macetes of $1 of any number of schema variables, the condition derivable and every value denoting")
(def-predicate 'REL-MACETE-N-1 '(md13t_ md13hs_ md13c_) '(REL-REWRITE-1 (J-MACN md13t_) md13hs_ md13c_))
(def-predicate 'REL-MACETE-N-HYP-1 '(md13t_ md13hs_ md13c_) '(REL-REWRITE-HYP-1 (J-MACN md13t_) md13hs_ md13c_))
(def-predicate 'REL-MACETE-N-7 '(md13t_ md13hs_ md13c_) '(REL-REWRITE-7 (J-MACN md13t_) md13hs_ md13c_))
(def-predicate 'REL-MACETE-N-HYP-7 '(md13t_ md13hs_ md13c_) '(REL-REWRITE-HYP-7 (J-MACN md13t_) md13hs_ md13c_))
(for-each (lambda (n) (notation! n 'kind 'predicate 'arity 3 'english "the kernel's macete of any number of schema variables, at one position, relates $2 to $3"))
  '(REL-MACETE-N-1 REL-MACETE-N-HYP-1 REL-MACETE-N-7 REL-MACETE-N-HYP-7))

;;; -----------------------------------------------------------------------
;;; 10. THE CATALOG'S N-ARY DECOMPOSITIONS (agent K2-END, 2026-10-22; docs/meta-k2-admissibility-2026-10-08.md
;;; section 8, decision (a); scratchpad/triage/META-4-REPORT.md, section 5.2).  The catalog states the membership of
;;; an n-ary UNION and INTERSECTION once, as the primitive RESTVAR / SPLICE schemas union-decompose and
;;; intersection-decompose (library.scm 776, 781): an instance at x, S_1 .. S_n (n >= 1) is
;;;     x in UNION(S_1 .. S_n)  iff  x in S_1 or (x in S_2 or .. (x in S_n))
;;; the RIGHT-nested fold of the atoms, the last bare (n = 1: the atom alone), and likewise with AND for
;;; INTERSECTION.  The core's schemas CR-UNION-MEM and CR-INTERSECTION-MEM (meta-core.scm 4.6) state the LEFT-nested
;;; fold over FALSITY / TRUTH (ENC-ORL, ENC-ANDL).  RF-SET(h, x, l) holds the pairs [j, f] with f the right fold, by
;;; the connective head h (4 OR, 3 AND), of the atoms x in l_(j+1) .. x in l_|l|: the least set closed under the base
;;; [|l| - 1, x in l_|l|] and the step from [j + 1, f] to [j, h(x in l_(j+1), f)]; the catalog's instance is the f of
;;; the pair [0, f].  Every instance is DERIVABLE over the core with no member of T (meta-def-laws.scm section 10,
;;; der-union-decompose, der-intersection-decompose): the core does not need the two schemas, and the kernel's
;;; rewrite by either at one position is admissible (J-UDEC, J-IDEC, the relations below).  The binary axioms
;;; union-membership and intersection-membership are the instances at n = 2.  Binders: md14*_.
(def-predicate 'RF-CLOSED '(md14h_ md14x_ md14l_ md14s_)
  '(AND (FORALL md14j_ (IMPLIES (IN md14j_ NN) (IMPLIES (= (succ md14j_) (LENGTH md14l_))
           (IN (LIST md14j_ (ENC-IN md14x_ (NTH (succ md14j_) md14l_))) md14s_))))
        (FORALL md14k_ (FORALL md14f_ (IMPLIES (IN md14k_ NN) (IMPLIES (IN (LIST (succ md14k_) md14f_) md14s_)
           (IN (LIST md14k_ (EAPP md14h_ (LIST (ENC-IN md14x_ (NTH (succ md14k_) md14l_)) md14f_))) md14s_)))))))
(notation! 'RF-CLOSED 'kind 'predicate 'arity 4 'english "$4 is closed under the right folds by $1 of the memberships of $2 in the entries of $3")
(def-functoid 'RF-SET '(md14h_ md14x_ md14l_)
  '(SEP md14p_ (CARTESIAN NN EXPR-SET) (FORALL md14w_ (IMPLIES (IN md14w_ (POWER (CARTESIAN NN EXPR-SET)))
      (IMPLIES (RF-CLOSED md14h_ md14x_ md14l_ md14w_) (IN md14p_ md14w_))))))
(notation! 'RF-SET 'kind 'functoid 'arity 3 'english "the right folds by $1 of the memberships of $2 in the entries of $3 from an index on")
;; the local redexes of the two schemas: x in UNION(l) -> the right fold f, x in INTERSECTION(l) -> the right fold f
(def-functoid 'J-UDEC '(md14t_)
  '(SEP md14y_ RW-UNIV (FORSOME md14g_ (FORSOME md14x2_ (FORSOME md14l2_ (FORSOME md14f2_
     (AND (= md14y_ (LIST 2 md14g_ (ENC-IN md14x2_ (ENC-UNION md14l2_)) md14f2_))
          (AND (IN (LIST 0 md14f2_) (RF-SET 4 md14x2_ md14l2_))
               (AND (IN (ENC-IN md14x2_ (ENC-UNION md14l2_)) CLF) (IN md14f2_ CLF))))))))))
(def-functoid 'J-IDEC '(md14t_)
  '(SEP md14y_ RW-UNIV (FORSOME md14g_ (FORSOME md14x2_ (FORSOME md14l2_ (FORSOME md14f2_
     (AND (= md14y_ (LIST 2 md14g_ (ENC-IN md14x2_ (ENC-INTER md14l2_)) md14f2_))
          (AND (IN (LIST 0 md14f2_) (RF-SET 3 md14x2_ md14l2_))
               (AND (IN (ENC-IN md14x2_ (ENC-INTER md14l2_)) CLF) (IN md14f2_ CLF))))))))))
(notation! 'J-UDEC 'kind 'functoid 'arity 1 'english "the local instances over $1 of the catalog's union-decompose")
(notation! 'J-IDEC 'kind 'functoid 'arity 1 'english "the local instances over $1 of the catalog's intersection-decompose")
(def-predicate 'REL-UNION-DECOMPOSE-1 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-1 (J-UDEC md14t_) md14hs_ md14c_))
(def-predicate 'REL-UNION-DECOMPOSE-HYP-1 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-HYP-1 (J-UDEC md14t_) md14hs_ md14c_))
(def-predicate 'REL-UNION-DECOMPOSE-7 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-7 (J-UDEC md14t_) md14hs_ md14c_))
(def-predicate 'REL-UNION-DECOMPOSE-HYP-7 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-HYP-7 (J-UDEC md14t_) md14hs_ md14c_))
(def-predicate 'REL-INTERSECTION-DECOMPOSE-1 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-1 (J-IDEC md14t_) md14hs_ md14c_))
(def-predicate 'REL-INTERSECTION-DECOMPOSE-HYP-1 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-HYP-1 (J-IDEC md14t_) md14hs_ md14c_))
(def-predicate 'REL-INTERSECTION-DECOMPOSE-7 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-7 (J-IDEC md14t_) md14hs_ md14c_))
(def-predicate 'REL-INTERSECTION-DECOMPOSE-HYP-7 '(md14t_ md14hs_ md14c_) '(REL-REWRITE-HYP-7 (J-IDEC md14t_) md14hs_ md14c_))
(for-each (lambda (n) (notation! n 'kind 'predicate 'arity 3 'english "the kernel's rewrite by the catalog's n-ary decomposition, at one position, relates $2 to $3"))
  '(REL-UNION-DECOMPOSE-1 REL-UNION-DECOMPOSE-HYP-1 REL-UNION-DECOMPOSE-7 REL-UNION-DECOMPOSE-HYP-7
    REL-INTERSECTION-DECOMPOSE-1 REL-INTERSECTION-DECOMPOSE-HYP-1 REL-INTERSECTION-DECOMPOSE-7 REL-INTERSECTION-DECOMPOSE-HYP-7))
