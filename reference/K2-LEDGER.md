# K2 ledger

The per-rule ledger of K2 (manual, Part 2, chapter "Admissibility over the core"): the non-oracle kernel rules,
the form of each, the transcribed relation, the theorems that discharge it and what is open. Read from
`rule-checkers-*.scm`, `structure-library/meta-*.scm` and `theorem-library/meta-*-laws.scm`. Hand-written: update
it with any change to a checker, a core relation or a META theorem it names.

## 0. Counts

Top-level `register-rule-checker!` forms in the four checker files (the form inside `dg-check-arm-with!`,
rule-checkers-logic.scm 1902, and the one inside `rco-trust-oracle!`, rule-checkers-oracle.scm 1076, are
procedures, not registrations, and are not counted):

| file | 10-22 / a320cb6f | 11-19 base |
|---|---|---|
| rule-checkers-logic.scm | 41 | 40 (truth-intro retired; comment at line 690) |
| rule-checkers-schema.scm | 13 | 13 |
| rule-checkers-rewrite.scm | 4 | 4 |
| rule-checkers-oracle.scm | 7 | 7 |
| all | 65 | 64 |
| non-oracle | 58 | 57 |

The core: `CORE-RULE` (structure-library/meta-core.scm section 5) is the disjunction of 56 relations
(`mc--core-names`): the 55 of a320cb6f plus `CR-TUPLE-ETA` (4.11, W2B, 11-10). `CR-TRUTH-INTRO` stays in the
core although the kernel operation is retired. Each relation has a generated closure law
`derivable-<name>` (theorem-library/meta-core-laws.scm, `mc-closure-law!`, named by `dk-meta-law-name`).

META certificates (`certificates/theorem-library/meta-*-laws.cert`, the live tree of 11-20): 633 records, every bill
empty; 450 list the oracles `arith` and/or `ineq`, 183 list none.

## 1. Legend: the form letters

A rule R is written as a figure  G1 => A1 ... Gn => An / G => A  (hypotheses / conclusion). REL-R is the
relation its checker enforces, transcribed into VNB. "Admissible" means: whenever every hypothesis is in
DERIVABLE(T), so is the conclusion (meta-report Claim 1.2).

| letter | meaning | what the theorem is |
|---|---|---|
| C | The kernel figure IS a core figure (same hypotheses, same side conditions). | the closure law `derivable-<core rule>` |
| B | The kernel figure differs from a core figure by a small step (the BRIDGE): the kernel replaces a formula the core keeps, or omits a premise the core states. The kernel relation is transcribed (`REL-R-K`, meta-nbg.scm) and its admissibility is proven. | `adm-R-k` (meta-nbg-laws.scm section B) |
| B* | As B, when the omitted premise is the definedness  G => t = t  of a term the kernel certifies. Two kernel forms: `REL-R-K`, t certified by one member of the context (CERT-SET); `REL-R-KD`, [G, t = t] in DEF-DERIVABLE(T), the sequents the rows of section 3 reach. A certificate that uses an open row is not covered. | `adm-R-k`, `adm-R-kd` (meta-nbg-laws.scm sections B, D) |
| D | Not a core rule; transcribed as REL-R and DERIVED in full over the core. For rows 30, 32 and 52 the relation is the OWED form (the definedness of a class as a hypothesis, DS-53); the certified omission is a -K form or open (section 5). | `adm-R` (a derivation template) |
| PS | A rewriting rule admissible at ANY FINITE SET of positions of any stage (REL-R-S over REWRS(J), meta-nbg.scm section E): the kernel's simultaneous rewrite read as a chain of one-position rewrites in the order of the walk (right conjunct first at AND, left disjunct first at OR, consequent first at IMPLIES). The one-position forms `adm-R-1` (stages up to 5) and `adm-R-7` (all stages) stay. | `adm-R-s` (meta-nbg-laws.scm section E; from `adm-rewrite-s`, `adm-rewrite-hyp-s`, `crs-s`, `rewrs-*`) |
| S1 | (no row) Proven for a special case only. | -- |
| P1 | (no row) One rewrite at one position only. | -- |
| T | Transcribed, not proven. | none |

Former form C+ (10-22): "in the core up to a bridge that is derivable but not stated". All ten C+ rows now
have their bridge stated and proven (agent METACORE, 2026-10-29; landed with W1 in 2e287dbb): they are B or B*.

## 2. The 57 rules

`mc` = meta-core.scm, `mi` = meta-ind.scm, `md` = meta-def.scm, `mn` = meta-nbg.scm, `mr` = meta-cr.scm; L = the
laws file of the same name. "10-22" is the form in the old ledger; its row numbers are kept (row 9 was
truth-intro).

| # | rule | 10-22 | 11-20 | relation | discharging theorem(s) | open |
|---|---|---|---|---|---|---|
| 1 | and-intro | C | C | CR-AND-INTRO | derivable-and-intro | -- |
| 2 | or-intro-left | C | C | CR-OR-INTRO-LEFT | derivable-or-intro-left | -- |
| 3 | or-intro-right | C | C | CR-OR-INTRO-RIGHT | derivable-or-intro-right | -- |
| 4 | implies-intro | C | C | CR-IMPLIES-INTRO | derivable-implies-intro | -- |
| 5 | not-intro | C | C | CR-NOT-INTRO | derivable-not-intro | -- |
| 6 | iff-intro | C | C | CR-IFF-INTRO | derivable-iff-intro | -- |
| 7 | forall-intro | C | C | CR-FORALL-INTRO | derivable-forall-intro | eigenvariable condition in named vs locally nameless syntax (K3) |
| 8 | forsome-intro | C+ | B* | REL-FORSOME-INTRO-K, -KD (mn) | adm-forsome-intro-k (mnL; uses adm-true-walk, adm-strict-atom, adm-cert), adm-forsome-intro-kd; the owed form is CR-FORSOME-INTRO | the open rows of section 3 |
| 9 | truth-intro | C | retired | -- | (CR-TRUTH-INTRO stays in the core; derivable-truth-intro) | -- |
| 10 | and-elim | C+ | B | REL-AND-ELIM-K (mn) | adm-and-elim-k | -- |
| 11 | or-elim | C+ | B | REL-OR-ELIM-K (mn) | adm-or-elim-k | -- |
| 12 | not-elim | C | C | CR-NOT-ELIM | derivable-not-elim | -- |
| 13 | iff-elim | C+ | B | REL-IFF-ELIM-K (mn) | adm-iff-elim-k | -- |
| 14 | forsome-elim | C+ | B | REL-FORSOME-ELIM-K (mn), REL-ADDS-NOTHING-K | adm-forsome-elim-k, ctx-fv-minus, adm-adds-nothing-k | -- |
| 15 | forall-elim | C+ | B* | REL-FORALL-ELIM-K, -KD (mn), REL-ADDS-NOTHING-K; the owed form is CR-FORALL-ELIM | adm-forall-elim-k, adm-forall-elim-kd, adm-adds-nothing-k; derivable-forall-elim | the open rows of section 3; checker re-runs pi--defined? (K3) |
| 16 | assumption | C | C | CR-ASSUMPTION | derivable-assumption | -- |
| 17 | theorem-assumption | C | C | CR-THEOREM-ASSUMPTION | derivable-theorem-assumption | that T is the installed table (K5) |
| 18 | cut | C | C | CR-CUT | derivable-cut | -- |
| 19 | weakening | C | C | CR-WEAKENING | derivable-weakening | -- |
| 20 | detach | D | D | REL-DETACH (mc 6) | adm-detach (mcL) | -- |
| 21 | backchain | C | C | CR-BACKCHAIN | derivable-backchain | -- |
| 22 | proof-by-contradiction | C | C | CR-CONTRADICTION | derivable-contradiction | -- |
| 23 | eq-subst | C | C | CR-EQ-SUBST, CR-EQ-SUBST-SYM | derivable-eq-subst, derivable-eq-subst-sym | capture condition exists only in named syntax (K3) |
| 24 | reflexivity | C+ | B* | REL-REFLEXIVITY-K, -KD, -KT (mn); goal TRUTH is CR-TRUTH-INTRO | adm-reflexivity-k, adm-reflexivity-kd, adm-reflexivity-kt | the open rows of section 3; checker re-runs pi--defined? (K3) |
| 25 | quasi-reflexivity | C | C | CR-QUASI-REFLEXIVITY | derivable-quasi-reflexivity | -- |
| 26 | if-true | C+ | B* | REL-IF-TRUE-K, -KD (mn); the uncertified form is CR-IF-TRUE | adm-if-true-k, adm-if-true-kd, adm-adds-nothing-k | the open rows of section 3, for the branch |
| 27 | if-false | C+ | B* | REL-IF-FALSE-K, -KD (mn); the uncertified form is CR-IF-FALSE | adm-if-false-k, adm-if-false-kd, adm-adds-nothing-k | the open rows of section 3, for the branch |
| 28 | cartesian-intro | T | D | REL-CARTESIAN-INTRO (mi) | adm-cartesian-intro (miL; uses CR-TUPLES-MEM at SET, its premise SET = SET) | -- |
| 29 | cartesian-elim | T | D | REL-CARTESIAN-ELIM (mi) | adm-cartesian-elim (miL) | -- |
| 30 | tuples-intro | D | D | REL-TUPLES-INTRO (n >= 1), REL-TUPLES-INTRO-0 (the empty tuple, owed [g, A = A]) (mc 6); REL-TUPLES-INTRO-0K (mn, A certified by a context member) | adm-tuples-intro, adm-tuples-intro-0 (mcL), adm-tuples-intro-0k (mnL) | certified omission through a composition of the rows (no -KD form) |
| 31 | tuples-elim | D | D | REL-TUPLES-ELIM (mc 6) | adm-tuples-elim (mcL) | -- |
| 32 | union-intro | D | D | REL-UNION-INTRO (mc 6), the OWED form: the membership, then [g, S_i = S_i] for every entry | adm-union-intro (via derivable-union-mem-c); derivable-union-mem-u | OPEN: the certified omission (the kernel omits the k-th entry and every entry its certificate accepts; not transcribed) |
| 33 | union-elim | D | D | REL-UNION-ELIM (mc 6) | adm-union-elim | -- |
| 34 | intersection-intro | D | D | REL-INTERSECTION-INTRO (mc 6) | adm-intersection-intro | -- |
| 35 | intersection-elim | D | D | REL-INTERSECTION-ELIM (mc 6) | adm-intersection-elim | -- |
| 36 | nth-reduce | P1 | PS | REL-NTH-REDUCE-1/-7/-S over J-NTH | adm-nth-reduce-1, -7, adm-nth-reduce-s, j-nth-sub | binder-domain reads (list definedness under a binder) |
| 37 | length-reduce | P1 | PS | REL-LENGTH-REDUCE-1/-7/-S over J-LEN | adm-length-reduce-1, -7, adm-length-reduce-s, j-len-sub | as 36 |
| 38 | functoid-beta | P1 | PS | REL-FUNCTOID-BETA-1/-7/-S over J-FB | adm-functoid-beta-1, -7, adm-functoid-beta-s, j-fb-sub; CR-FUNCTOID-BETA-EQ | FUN-DEF rows and lambda-lifting (K3) |
| 39 | nn-induction | D | D | REL-NN-INDUCTION-NBG (mi) | adm-nn-induction, adm-nn-induction-core | encoded catalog axioms in T (K3/K5) |
| 40 | transfinite-induction | D | D | REL-TRANSFINITE-INDUCTION-NBG (mi) | adm-transfinite-induction, adm-transfinite-induction-core | as 39 |
| 41 | transfinite-induction-3cases | D | D | REL-TFI-3CASES-NBG (mi) | adm-tfi-3cases, adm-tfi-3cases-core | as 39 |
| 42 | sep-sethood | C | C | REL-SEP-SETHOOD (mi); CR-SEP-SETHOOD | adm-sep-sethood | -- |
| 43 | sep-mem-intro | D | D | REL-SEP-MEM-INTRO (mi) | adm-sep-mem-intro | -- |
| 44 | sep-mem-elim | D | D | REL-SEP-MEM-ELIM (mi) | adm-sep-mem-elim | -- |
| 45 | comp-mem-intro | D | D | REL-COMP-MEM-INTRO (mi) | adm-comp-mem-intro | -- |
| 46 | comp-mem-elim | D | D | REL-COMP-MEM-ELIM (mi) | adm-comp-mem-elim | -- |
| 47 | big-union-sethood | C | C | REL-BIG-UNION-SETHOOD (mi); CR-BIG-UNION-SETHOOD | adm-big-union-sethood | -- |
| 48 | big-union-mem-intro | D | D | REL-BIG-UNION-MEM-INTRO (mi) | adm-big-union-mem-intro, adm-big-union-mem-intro-core | -- |
| 49 | big-union-mem-elim | T | D | REL-BIG-UNION-MEM-ELIM (mi) | adm-big-union-mem-elim (miL) | -- |
| 50 | iota-def | C | C | CR-IOTA-DEF | derivable-iota-def | -- |
| 51 | iota-in-elim | C+ | B | REL-IOTA-IN-ELIM-K (mn), REL-ADDS-NOTHING-K | adm-iota-in-elim-k, adm-adds-nothing-k | -- |
| 52 | lambda-type | S1 | D | CR-LAMBDA-TYPE (one binder, premise [g, D = D]); REL-LAMBDA-TYPE-1 .. -4 and REL-LAMBDA-TYPE-N (mi, every n >= 1, owed [g, D = D]); REL-LAMBDA-TYPE-K (mn, one binder, D certified by a context member) | derivable-lambda-type; adm-lambda-type-1 .. -4, adm-lambda-type-n (miL sections O, O2; ltch-inst, ltch-open, ltop-succ); adm-lambda-type-k (mnL) | OPEN: the certified omission at a binder list; translator's encoding of a destructuring lambda, member of a product = list of its projections, encoded body predicative iff the body is (K3) |
| 53 | lambda-beta | P1 | PS | REL-LAMBDA-BETA-1/-7/-S over J-LB (the argument in the domain AND the value in SET derivable) | adm-lambda-beta-1, -7, adm-lambda-beta-s, j-lb-sub; CR-LAMBDA-BETA-EQ (premise: the value in SET) | binder-scope licence; destructuring binders; a value the kernel's value test accepts has its sethood derivable (K3) |
| 54 | lambda-beta-hyp | P1 | PS | REL-LAMBDA-BETA-HYP-1/-7/-S | adm-lambda-beta-hyp-1, -7, adm-lambda-beta-hyp-s | as 53 |
| 55 | macete | P1 | PS | REL-MACETE-1/-7/-S (J-MAC), REL-MACETE-N-1/-7/-S (J-MACN); the decompositions REL-UNION-/INTERSECTION-DECOMPOSE-* (J-UDEC: each entry's definedness derivable) | adm-macete-1, -7, adm-macete-s, adm-macete-n-1, -7, adm-macete-n-s, j-mac-sub, j-macn-sub, adm-union-decompose-* (der-union-decompose, der-union-binary, j-udec-sub), adm-intersection-decompose-* | chain of conditions; numeral/succ bridge; accessor and projection kinds (K3) |
| 56 | macete-hyp | P1 | PS | REL-MACETE-HYP-1/-7/-S, REL-MACETE-N-HYP-1/-7/-S | adm-macete-hyp-1, -7, adm-macete-hyp-s, adm-macete-n-hyp-1, -7, adm-macete-n-hyp-s, adm-*-decompose-hyp-* | as 55 |
| 57 | cartesian-decompose | T | PS | REL-CARTESIAN-DECOMPOSE-1/-7/-S over J-CART (mi) | der-cartesian-decompose, j-cart-sub, adm-cartesian-decompose-1, -7 (miL), adm-cartesian-decompose-s (mnL; T a set of sentences containing AX-MEM-SET); rests on CR-TUPLE-ETA | as 36 |
| 58 | tuple-equality-decompose | T | PS | REL-TUPLE-EQ-DECOMPOSE-1/-7/-S over J-TEQ (mi, re-transcribed with both definedness premises) | der-tuple-eq-decompose, j-teq-sub, adm-tuple-eq-decompose-1, -7 (mnL section C), adm-tuple-eq-decompose-s | as 36 |

## 3. The definedness rows: lemma (*)

Lemma (*): if the kernel's certificate `pi--defined?` accepts t in the context G through clauses that are rows of
DEF-RULE, then  G => t = t  is in DERIVABLE(T). It is the bridge of every B* row. Each clause is a relation DEF-x
(meta-def.scm), either a core schema (its closure law) or derived. DEF-RULE (meta-nbg.scm section D) is the
disjunction of the derived and admitted rows below, with CR-ASSUMPTION, CR-THEOREM-ASSUMPTION and CR-REFLEXIVITY;
DEF-APP and DEF-LEN-TUPLES enter guarded by their encoded axioms in T (AX-FUN-APP, AX-LEN-NN). DEF-DERIVABLE(T) is
the least set of sequents closed under DEF-RULE. `def-closed-derivable` (DERIVABLE(T) is closed under every row)
gives `def-derivable-sub`: DEF-DERIVABLE(T) is a subset of DERIVABLE(T), lemma (*) for every composition of the
rows. That the kernel's acceptance through rows puts [G, t = t] in DEF-DERIVABLE(T) is K3.

| clause of pi--defined? | relation | theorem | status 11-20 |
|---|---|---|---|
| atom (variable, constant) | CR-REFLEXIVITY | derivable-reflexivity | core |
| t in _ in context | CR-DEF-STRICT-IN-L | def-strict-in-l-admitted | core |
| _ in t in context | CR-DEF-STRICT-IN-R | (closure law) | core |
| t = _ / _ = t in context | DEF-STRICT-EQ-L/-R | adm-def-strict-eq-l, adm-def-strict-eq-r | derived |
| t outside binders in a true IN / = / <= / < (and SEP conjuncts) | DEF-STRICT-HYP, STRICT-ATOM, TRUE-REACH | def-strict-hyp-derived, adm-strict-walk, adm-true-walk, adm-strict-atom | derived |
| structure hypothesis IS-X(t) / t in X | DEF-STRUCT-HYP | def-struct-hyp-derived | derived |
| predicate hypothesis, any arity, leading FORSOMEs, nested, parent chain | DEF-PRED-HYP-N, DEF-CERT-HYP, CERT-SET | def-pred-hyp-n-derived, def-cert-hyp-derived, adm-cert, adm-pred-unfold-n | derived |
| accessor ACC(s) under IS-X(s) | DEF-PRED-HYP-N | as above | derived |
| LIST of sets | CR-DEF-LIST | def-list-admitted | core (PAIR, SINGLETON: no head code) |
| total class constructor on certified arguments | CR-DEF-TOTAL | def-total-admitted | core, for the codes in TOTAL-HEAD |
| SEP / BIG-UNION / VNB-LAMBDA over a certified domain, predicative body | CR-DEF-BINDER | def-binder-admitted | core |
| COMP, predicative condition | CR-DEF-COMP | adm-def-comp-holds | core |
| NTH(k, LIST l), the list certified | DEF-NTH-LIST | def-nth-list-derived | derived |
| functoid with certified instance; NTH through a functoid; SEP through nested functoids | DEF-FUN-INST, DEF-FUN-NTH, DEF-FUN-SEP, DEF-FUN-STRICT | def-fun-inst-derived, def-fun-nth-derived, def-fun-sep-derived, def-fun-strict-derived | derived (rows of FUN-DEF are K3) |
| f(a), f in FUN(D, _), a in D | DEF-APP | adm-def-app | derived |
| LENGTH(t), t in TUPLES(A) in context (direct case of pi--typed-in-tuples?) | DEF-LEN-TUPLES (md 4a), over T holding AX-LEN-NN | adm-def-len-tuples (miL) | derived |
| LENGTH(t), t typed in a class of tuples through a SEP domain or a functoid body (MAT -> MATRIX -> TUPLES) | none | none | OPEN: needs pi--class-of-tuples? transcribed as a walk |
| ground arithmetic; arithmetic on number-typed arguments, nested | none | none | OPEN: head codes for the arithmetic heads and their closure axioms in T (K3) |
| applied structure operation ((ACC s) a1 .. an) on typed arguments | none | none | OPEN: encoding of a several-argument application (K3), the slot's domain term, fun-codomain-iff encoded |
| view clause ACC(V(r)) (the whole instantiated list certified) | none | none | not admissible as a row |
| COMP | CR-DEF-COMP, NBG-OK | (closure law) | that the kernel's test decides exactly NBG-OK is K3 |
| NTH of a literal list, pre-R4 clause (DEF-NTH-LIT) | -- | -- | retired in the kernel; not a row of DEF-RULE |
| a term mentioning a record variable under its binder | -- | -- | refused by the kernel since KREC (ae95997a) |

## 4. Changes since the ledger of 2026-10-22

| form | 10-22 | 11-20 | change |
|---|---|---|---|
| C | 20 | 19 | truth-intro retired (11-19) |
| C+ | 10 | 0 | bridges proven (METACORE, landed in 2e287dbb): 5 to B, 5 to B*; the -KD forms over DEF-DERIVABLE (BRIDGE, 11-19) |
| B | -- | 5 | rows 10, 11, 13, 14, 51 |
| B* | -- | 5 | rows 8, 15, 24, 26, 27 |
| S1 | 1 | 0 | row 52 to D (POSN, 11-19: every length n >= 1) |
| D | 15 | 19 | rows 28, 29 (METACORE), 49 (METACORE), 52 (POSN) |
| P1 | 7 | 0 | rows 36-38, 53-58 to PS (POSN, 11-19) |
| PS | -- | 9 | rows 36, 37, 38, 53, 54, 55, 56, 57, 58 |
| T | 5 | 0 | -- |
| all | 58 | 57 | |

Other changes in the relations:

* The three induction relations carry NBG-OK(P) (`REL-*-INDUCTION-NBG`, `REL-TFI-3CASES-NBG`); since W1 the
  kernel's induction checkers refuse an impredicative body (`chk-induction-body-impredicative`,
  `*nbg-induction-fatal?*`), so the transcription matches the kernel.
* Nine core schemas carry NBG-OK on their condition or body (meta-core.scm 4.3a): the core is NBG-strength,
  no longer Morse-Kelley.
* CR-TBIND-CR covers COMP (head 23) (W2B); CR-TUPLE-ETA is a new core schema (W2B).
* HYPS-IN states that the hypothesis list is a set (VIAGAP F1).
* REL-CONTRAPOSITION and adm-contraposition are removed (METACORE).
* The K1 repair (K1FIX, landed 11-20; DS-53): CR-TUPLES-MEM has the premise [g, A = A]; CR-UNION-MEM one premise
  [g, S_i = S_i] per entry (LENGTH hs = LENGTH l, the NTH-wise universal, as CR-DEF-TOTAL); CR-LAMBDA-TYPE a third
  premise [g, D = D]; CR-LAMBDA-BETA-EQ a second premise [g, b[x := t] in SET]. REL-UNION-INTRO is the owed form;
  REL-TUPLES-INTRO has n >= 1 and the empty tuple is REL-TUPLES-INTRO-0; REL-LAMBDA-TYPE-1 .. -4 and -N carry
  [g, D = D]; J-LB requires the value-in-SET sequent derivable; J-UDEC each entry's definedness derivable. New
  -K forms REL-TUPLES-INTRO-0K, REL-LAMBDA-TYPE-K. Added hypotheses (statement changes forced by the repair):
  derivable-union-mem-c and der-union-decompose (each entry's definedness derivable), der-union-binary
  ([g, a = a] and [g, b = b]).
* DS-52: CHOICE(A) denotes iff A is inhabited. pi--defined? never certifies a CHOICE term by its shape
  (primitive-inferences.scm, the total-head list); CHOICE has no head code in the encoding (K3).

## 5. Open rows

| item | rows | what it needs |
|---|---|---|
| certified omission, union-intro | 32 | a transcription of the kernel figure without the sequents of the k-th entry and of the entries the certificate accepts, and its admissibility (the k-th entry by def-strict-in-r; the others by lemma (*)) |
| certified omission, lambda-type at a binder list | 52 | a -K (and -KD) form of REL-LAMBDA-TYPE-N |
| certified omission through a composition of the rows | 30, 52 | -KD forms of REL-TUPLES-INTRO-0K and REL-LAMBDA-TYPE-K over DEF-DERIVABLE, as for the B* rows |
| the open rows of lemma (*) | 8, 15, 24, 26, 27 | section 3 |
| the PS exclusions | 36-38, 53-58 | binder-scope licence of lambda-beta; binder-domain reads; chain of conditions; numeral/succ bridge |
