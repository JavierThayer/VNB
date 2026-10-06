# Strand spaces in VNB, on the user's model (2026-10-06)

The strand-space line of the October roadmap (notes-57, line (c)) follows the user's paper with Herzog
and Guttman, *Strand Spaces: Proving Security Protocols Correct* (`~/docs/jcs_strand_spaces.pdf`,
sections 2-3). The DEFINITIONS, however, are the user's own, from `~/notes/notes-60.txt` (2026-10-06,
03:05Z) and his decisions of the same day; the paper supplies the theorems and the adversary's traces.
Built by batches S-2 and S-2b (2026-10-06; the agents' reports are `scratchpad/triage/WEEK3-REPORTS.md`),
on S-1 of 2026-10-04, whose message algebra was revised in place. Six files, 148 theorems, every one
`proven modulo 0`, oracles `arith` and `ineq` only:

    structure-library/strand-messages.scm      theorem-library/strand-messages-laws.scm   (57)
    structure-library/strand-spaces.scm        theorem-library/strand-space-laws.scm      (74)
    structure-library/strand-adversary.scm     theorem-library/strand-adversary-bound.scm (17)

The earlier versions are `archive/2026-10-06/` (S-1) and `archive/2026-10-06/s2b/` (S-2). The design
note of 2026-10-03 (`docs/strand-spaces-design-2026-10-03.md`) formalised the paper's objects and is
superseded.

## 1. The model

**Messages.** A set `T` of TOKENS and a set `K` of KEYS, `K` a subset of `T`. A message is a token, or a
list of messages, or an encryption of a message under a key:

    LST(l)     = [1, l]        l a list (TUPLES) of messages
    ENCR(m, k) = [2, m, k]     m a message, k in K

`MSG-SET(T, K)` is the union over `NN` of the stages `MSG-STAGE(T, K, n)`: `T` at stage 0, and at stage
`n+1` the stage `n` together with the tagged lists and encryptions over it. `MSG-RANK(T, K, m)` is the
least stage index holding `m`.

*Why the law and the tags.* The recursion (subterm, content, induction) needs the three cases
pairwise disjoint, and in VNB every list is a set. Tokens are separated from the two constructed shapes
by THE TOKEN LAW, `IS-TOKEN-SET(T)`: `T` is a set and no member of `T` is a list (`TUPLES(SET)`, the class
of all lists with set components, is the kernel-admissible spelling of "is a list"). It has to be a law:
the tree cannot prove of any particular set that it is not a list. Lists and encryptions are both lists
as sets, so a law on `T` cannot tell them apart; the tags 1 and 2 do, by arithmetic. This is the user's
"disjoint from both by the token law's device" (2026-10-06): the law one level up, tags one level down.

**The subterm relation** `IS-SUBTERM(T, K, a, b)` is the intersection closure (S-1's device): the least
relation containing `[a, a]` for every message, `[a, LST(l)]` whenever `a` is a subterm of a component
of `l`, and `[a, ENCR(g, k)]` whenever `a` is a subterm of `g`. THE KEY IS NOT A SUBTERM OF THE
ENCRYPTION (the paper's Definition 2.1). The bound of section 3 holds under either convention; what the
convention decides is whether its hypothesis can be met: under the other reading a regular strand that
encrypts under a key it never received would ORIGINATE that key, and "never originates on a regular
node" would fail for every key a participant uses.

**Directed messages, strands, spaces.** A directed message is `[dir, t]` with `dir` one of the
constants `SENT` (0) and `RECEIVED` (1); its content is `t`. A strand is a list of directed messages
(`STRANDS(T, K)`). A STRAND-SPACE is a `declare-structure` with carriers `TOKENS`, `KEYS`, `IDS` (the
STRAND IDENTIFIERS -- the user withdrew "agents"), the op `STRAND-MAP : IDS -> STRANDS(TOKENS, KEYS)`
(his Sigma; the name SIGMA is MEASURABLE-SPACE's slot) and the op `KINV : KEYS -> KEYS` (the paper's
`K^-1`; INV is GROUP's slot), with the laws `IS-TOKEN-SET(TOKENS)`, `KEYS` a subset of `TOKENS`, and
`KINV(KINV(k)) = k`. Symmetric keys are the fixpoints of `KINV`. The paper's non-injective `tr` is
several identifiers with equal strands.

**Nodes.** `NODES(sp)` is the SEP `{[k, a] in NN x IDS : 1 <= k <= LENGTH(STRAND-MAP(a))}`, so that
`NODE-CONTENT(sp, n)` and `NODE-DIR(sp, n)` are TOTAL on nodes (the user's "or undefined" was decided
away: a partial content owes `t = t` at every instantiation under the LUTINS rule). `IS-SENT`,
`IS-RECEIVED`.

**Two relations on nodes.** `SAME-STRAND-BEFORE(sp, n, n')`, the user's `==>`, is STRICT: same
identifier and index `<` (the reflexive reading made entry points contradictory; the user confirmed
strictness). `SAME-STRAND-UPTO` is its reflexive twin. `SENDS-TO(sp, n, n')`, the user's `-->`: `n`
sent, `n'` received, equal contents. `STRAND-NEXT(sp, n, n')`: `n'` immediately follows `n`.

**Occurrence and origination.** `OCCURS-IN-SPACE(sp, u)`: `u` is a subterm of some node's content.
`IS-ENTRY-POINT(sp, n, I)`: `n` is sent, its content is in `I`, and no `n' ==> n` has content in `I`.
`ORIGINATES(sp, u, n)`: `n` is an entry point into `{m : u subterm of m}`. `UNIQUELY-ORIGINATES(sp, u)`.

**Bundles.** `BUNDLE` is a `declare-structure` with the substructure `BSPACE` (a strand space), the
carrier `BNODES` (a subset of `NODES(BSPACE)`) and the relation slots `BSEND`, `BNEXT`; laws:
`CARD(BNODES) in NN`; every `BSEND` pair satisfies `SENDS-TO` and every `BNEXT` pair `STRAND-NEXT`;
every received node has EXACTLY ONE `BSEND`-predecessor; `BNODES` is closed under `==>` (ONE clause,
since `==>` is the whole same-strand order); the `BNEXT` edge is present for every `STRAND-NEXT` pair
inside; and ACYCLICITY: no `[n, n]` in `PRECEDES-STRICT(c)`, the least transitive relation on `BNODES`
containing `BSEND` and `==>` (defined on loose data as `PREC-STRICT`, because the acyclicity law names
it before the structure exists). `PRECEDES(c)` adds the identity.

**The adversary** (the paper's penetrator; the user: "adversary is a better term"). `INFILTRATED-SPACE`:
substructure `ISPACE`, carriers `ADV-IDS` (the adversary's strand identifiers) and `ADV-TOKENS` (what it
knows initially), with every adversary strand an adversary trace. The traces, over a strand space, are
the paper's Definition 3.1 with the K trace subsumed by M (keys are tokens):

    M  [sent a]                          a in ADV-TOKENS
    F  [received g]
    T  [received g, sent g, sent g]
    C  [received m1, ..., received mk, sent LST([m1, ..., mk])]     n-ary
    S  [received LST([m1, ..., mk]), sent m1, ..., sent mk]         n-ary
    E  [received k, received m, sent ENCR(m, k)]
    D  [received KINV(k), received ENCR(m, k), sent m]

`IS-ADVERSARY-NODE(isp, n)` (identifier in `ADV-IDS`); `IS-REGULAR-NODE` is its negation.

## 2. The theorems

All in `reference/THEOREMS.md` (and the web interface); the five numbered results of the paper are in
the MAJOR THEOREMS list (`docs/major-theorems-table.sexp`, document `strand-spaces`).

* Messages: freeness (`token-ne-list`, `encr-ne-token` by the token law; `encr-ne-list`, `lst-injective`,
  `encr-injective` by the tags), `msg-induction`, `msg-cases`, the subterm closure clauses, `subterm-least`,
  `subterm-cases` (inversion), `subterm-trans`, `subterm-of-token` (a token's only subterm is itself),
  `subterm-of-list`, `subterm-of-encr`, `token-subterm-of-list`, `token-subterm-of-encr`, `subterm-rank`,
  `subterm-antisym`, and the paper's Proposition 2.12 (`subterm-encr-other-key`).
* Spaces: node laws (one identifier, content a message, sent XOR received); `==>` irreflexive and
  transitive; `-->` only from a sent to a received node; `PRECEDES-STRICT` closure, minimality and the
  inversion lemma `ps-last-step`.
* LEMMA 2.7: `precedes-partial-order` (as `IS-PARTIAL-ORDER(BNODES, PRECEDES)`), `finite-strict-minimal`
  (a transitive irreflexive relation on a finite nonempty set has a minimal member), `bundle-minimal`
  (the minimal node of any nonempty subset of `BNODES`, witness explicit). The only finiteness used is
  `CARD(BNODES) in NN`. Ten minutes of agent time against the day the design note budgeted.
* LEMMA 2.8 `bundle-minimal-sent`, LEMMA 2.9 `bundle-minimal-originates`; origination facts
  (`originates-sent`, `originates-no-earlier`, `originates-unique`).
* THE ADVERSARY BOUND, Proposition 3.3 for any token: `adversary-bound` -- `c` a bundle with
  `BSPACE(c) = ISPACE(isp)`, `u` a token not in `ADV-TOKENS`, `u` originating on no regular node of `c`;
  then `u` is a subterm of no node's content. Corollary `adversary-bound-adversary-nodes`. The proof is
  the paper's method -- a minimal member of `{n in c : u subterm of content(n)}` by 2.7, originating by
  2.9, sent by 2.8, hence an adversary node, then the seven per-trace lemmas (`text-trace-origin`,
  `flush-trace-no-sent`, `tee-/concat-/separate-/encrypt-/decrypt-trace-no-origin`).

## 3. The paper's gaps under this model

Of the five gaps the integrator's reading of the paper had listed (2026-10-06 02:40Z), three DISSOLVE on
the user's definitions and two stand and are answered:

* (a), (e) Definition 2.3 clause 6 compares a SIGNED term with a set of UNSIGNED terms (vacuous as
  written) and the "abuse of language" on subterms of signed terms: DISSOLVED -- content is undirected
  by definition.
* (b) `=>+` is never defined and Lemma 2.9's proof iterates bundle clause 3 "as many times as
  necessary": DISSOLVED -- `==>` is the whole strict same-strand order, the bundle's closure is one law,
  and no proof steps along NEXT. Consequence: `BNEXT` and its two laws are used by NO theorem of
  2.7-2.9 or 3.3 (kept for fidelity to Definition 2.4; the user's call).
* (c) Lemma 2.7 is stated without proof: proved; finiteness of the edge sets is never used.
* (d) Definition 2.4 asks for a UNIQUE sender of each received node: uniqueness is used nowhere (2.8
  uses existence); carried as the paper has it.
* (f) NEW, the user's: the reflexive `==>` of notes-60 (g) made entry points contradictory; strict is the
  definition (`ssb-irreflexive`).
* (g) NEW: the n-ary C and S traces are characterised by LENGTH and entries with the component list
  quantified; `tuple-tabulation` sufficed to prove both exist for every list; no list law was missing.
* (h) NEW: Lemma 2.8 needs only ONE direction of its closure hypothesis (toward the sender); stated so.
* (i) NEW: the M and C cases of the bound rest on the TOKEN LAW, not on the freeness of a free algebra:
  the bound is a statement about TOKENS, and the paper's key case is its instance.
* (j) NEW (S-2b): the E case of the bound holds under either subterm convention; the convention governs
  the hypothesis, not the proof (section 1).

## 4. Open, for the user (2026-10-06 evening)

1. Confirm the vocabulary of section 1 (in particular `IS-TOKEN-SET` via `TUPLES(SET)`, `STRAND-MAP`,
   `KINV`, `BNODES` / `BSEND` / `BNEXT`, `ADV-IDS` / `ADV-TOKENS`, the trace predicates over the space).
2. Confirm the subterm convention: the key is not a subterm of the encryption.
3. `BNEXT`: keep (Definition 2.4 fidelity) or drop (unused). Recommendation: keep until S-3 (NSL) shows
   whether a protocol proof uses it.

## 5. What S-3 (Needham-Schroeder-Lowe) writes

`{N_a A}_KB` is `ENCR(LST([Na, A]), KB)`; B's private key is `KINV(KB)`; the secrecy hypothesis of the
bound is `KINV(KB) notin ADV-TOKENS`. The protocol's regular strands are concrete lists of directed
messages built by `directed-intro` and `node-intro`; the names S-3 cites are listed in the S-2b report.
One modelling choice is left to S-3: `{N_b}_KB` as `ENCR(Nb, KB)` (a token under a key) or over a
one-element list. Kit candidates named by the agents: a hypothesis-side rewrite (`dk-rewrite-h!`), a
`dk-cite!` that errors when its instantiation opens an owed `t = t` leaf, and a tactic inverting "token
`u` is a subterm of a LITERAL message" into the disjunction of equations.
