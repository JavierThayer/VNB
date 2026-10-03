# Strand spaces in VNB: a design note (2026-10-03)

The user's roadmap (notes-57, line (c)) asks for applications to network protocols after his paper
with Herzog and Guttman, *Strand Spaces: Proving Security Protocols Correct* (`~/docs/jcs_strand_spaces.pdf`),
and later Guttman's *Shapes* (`~/docs/shapes_surveying.pdf`). This note says how the paper's objects
become VNB objects, in the tree's own terms, what has to be decided, and the first theorems. The
user's decision 5 (2026-10-03) is already taken: the message algebra is BUILT, not axiomatised.

## 1. What the paper defines (sections 2, 3, 6)

* **Messages** (2.3): a set A, the free algebra over the atoms, texts T and keys K (disjoint), under
  two constructors, concatenation g h and encryption {g}_K, with an inverse map K -> K^{-1} on keys.
  Freeness: the two constructors are injective, their ranges disjoint from each other and from the
  atoms (Axioms 1, 2). The SUBTERM relation (Definition 2.11) is the least relation with a @ a,
  a @ {g}_K if a @ g, a @ g h if a @ g or a @ h; in particular K is NOT a subterm of {g}_K unless
  K @ g. Proposition 2.12 is the first consequence of freeness.
* **Signed terms and strands** (2.1, 2.2): a signed term is <sigma, a>, sigma one of +, -; a strand
  space over A is a set Sigma with a trace map tr : Sigma -> (+-A)*, finite sequences of signed terms.
* **Nodes and edges** (2.3): a node is <s, i> with 1 <= i <= length(tr(s)); term(n) is the i-th signed
  term; n1 -> n2 when term(n1) = +a and term(n2) = -a; <s, i> => <s, i+1>. Origination and unique
  origination (clauses 6 to 8): n is an entry point for a set I of terms when term(n) = +t with t in I
  and no earlier node of the strand has its term in I; t originates on n when n is an entry point for
  the set of terms having t as a subterm; t is uniquely originating when it originates on one node.
* **Bundles** (2.4): a FINITE subgraph C of the node graph such that every negative node of C has a
  unique incoming -> edge in C, every => predecessor of a node of C is in C with its edge, and C is
  ACYCLIC. Causal precedence (2.6) is the reflexive transitive closure of C's edges. Lemma 2.7: it is
  a partial order and every nonempty set of nodes of C has minimal members; Lemmas 2.8 and 2.9: a
  minimal member of a set closed under "same unsigned term" is positive, and a minimal node among
  those containing t is an originating occurrence of t. These three lemmas carry every later proof.
* **The penetrator** (3.1, 3.2): a set K_P of keys known initially and the eight penetrator traces
  (text, flush, tee, concatenation, separation, key, encryption, decryption); an infiltrated strand
  space is a strand space with a designated set P of penetrator strands; a bundle is "over" it.
* **Ideals and honesty** (6.1, 6.10, Theorem 6.11): a k-ideal is a set of terms closed under
  concatenation with anything and under encryption with the keys of k; Theorem 6.11 bounds what the
  penetrator can produce from a set S of atoms with no entry point on a penetrator strand. The protocol
  theorems (NSL 5.2, 5.8, 5.10, 5.13, 5.14; Otway-Rees 7.4 to 7.9) are proofs by minimal elements.

## 2. The objects in VNB

**2.1 Messages as an inductive set of tagged lists.** Atoms are the elements of two given sets T and K
(sets, as every list component must be: the list rule of 2026-10-01). A message is a VNB list with a
tag in its first slot:

    [0, a]        an atom a in T u K
    [1, g, h]     the concatenation g h
    [2, g, k]     the encryption {g}_k, k in K

The set A is the union of the stages A_0 = {[0, a] : a in T u K}, A_{n+1} = A_n u {[1, g, h] : g, h in A_n}
u {[2, g, k] : g in A_n, k in K}, the stages by `def-by-nn-recursion` and the union by `BIG-UNION`
over NN, exactly as NN is built from 0 and `succ`. What this buys, as theorems and not stamps:
* FREENESS: the constructors are injective and have disjoint ranges, by list extensionality on
  the tag and the components (`NTH`; the tuple tripwire guarantees every message is a set).
* STRUCTURAL INDUCTION: a property holding at the atoms and preserved by the two constructors holds
  on A, by `ni` on the stage index. This is the paper's "inductive definition" made available.
* The RANK (the least stage containing a message) and the WIDTH (2.10) as functoids by the stage
  recursion; the SUBTERM relation (2.11) as the least relation closed under the three clauses, which
  on an inductive set is the relation defined by recursion on the rank of the right-hand side.
  Proposition 2.12 is then a case analysis on the tag.
* The inverse map K -> K^{-1}: a function `INV in FUN(K, K)` with `INV(INV(k)) = k`, a parameter of
  the whole development (the paper fixes it; symmetric keys are the fixed points).
A `MESSAGE-ALGEBRA` structure (carriers T, K; op INV; derived A) packages the parameters so that
every later statement quantifies over one object; its default morphisms are irrelevant and the
category is not the point.

**2.2 Signed terms, traces, strands.** A signed term is [sigma, m] with sigma in {0, 1} (0 for +,
1 for -). A trace is a LIST of signed terms (the tree's finite sequences are lists, with `LENGTH` and
`NTH`). A strand space over the algebra is a structure `STRAND-SPACE` (carrier STRANDS; op TR from
STRANDS to the set of traces), the set of traces being the set of lists over the signed terms; the
paper allows tr not injective, which the op form respects. Nodes: the SEP of CARTESIAN(STRANDS, NN) by
1 <= i <= LENGTH(TR(s)); `TERM(n)`, `SIGN(n)`, `UNS-TERM(n)` as functoids by `NTH`. The two edge
relations are predicates `SENDS-TO(sp, n1, n2)` and `NEXT(sp, n1, n2)`.

**2.3 Bundles.** A bundle is a structure `BUNDLE` over a strand space: carrier NODES (a set of nodes
of the space), two relation slots `SEND` and `NEXT` (sets of pairs on NODES; the `relation` slot kind
of batch 40, two of them on one carrier) and the four laws of 2.4: NODES finite (`CARD` in NN, the
tree's finiteness), SEND a subrelation of the space's ->, NEXT a subrelation of =>, every negative node
has exactly one SEND predecessor, every => predecessor of a node is in NODES with its NEXT edge, and
ACYCLICITY, stated as: no node is related to itself by the transitive closure of SEND u NEXT. The
closure: the tree has no transitive-closure operator; define `PRECEDES(C)` as the INTERSECTION of all
reflexive transitive relations on NODES containing the edges (a SEP of POWER(NODES x NODES); relations
are sets of pairs, which the relation slot kind already assumes). That it is the least such relation
is one theorem; that it is a PARTIAL ORDER with minimal elements in every nonempty subset (Lemma 2.7)
is the engine: antisymmetry from acyclicity, minimal elements from finiteness (finite-set induction
over POWER(NODES), the pattern of `nn-finite-subset-bounded`). Lemmas 2.8 and 2.9 follow as stated.

**2.4 Origination.** `IS-ENTRY-POINT(sp, n, I)`, `ORIGINATES(sp, t, n)`, `UNIQUELY-ORIGINATES(sp, t)`
as predicates over the space, the last with `FORSOME` and uniqueness. Positive, negative nodes by the
sign.

**2.5 The penetrator.** `PENETRATOR-TRACE(alg, KP, tr)`: the disjunction of the eight shapes of 3.1
(each a list pattern over A with the keys of KP where the paper has them); an infiltrated space adds a
set P of strands whose traces are penetrator traces; regular = not in P. Proposition 3.3 (a key not in
KP never used in the clear...) is the first theorem about them.

**2.6 Ideals and honesty.** `IS-K-IDEAL(alg, k, I)`, `IDEAL-GENERATED(alg, k, S)` as the intersection
of the k-ideals containing S (the same intersection device as the closure), honesty (6.10) relative
to a bundle, Theorem 6.11 by minimal elements. Then NSL: the protocol's strands as the three shape
predicates of 5.1 (initiator, responder, penetrator), and Proposition 5.2, the responder's guarantee,
by Lemmas 5.3 to 5.7 as in the paper.

## 3. What the user decides

1. The tagged-list encoding of messages (2.1), against a `MESSAGE-ALGEBRA` structure with freeness
   laws as axioms. Decision 5 of the roadmap chose BUILT; this note fixes the encoding. The cost of the
   encoding is one layer of tags in every statement, hidden by the three constructor functoids
   `ATOM(a)`, `CAT(g, h)`, `ENC(g, k)` and their reading in `notation!`.
2. Traces as LISTs (NTH, LENGTH), against functions on an interval. Lists are what the tree already
   uses for finite sequences in this role and what the tuple rule now certifies.
3. The bundle as a STRUCTURE with two relation slots (2.3), against a predicate over a triple. A
   structure gives the accessors, the obligations audit, a place in the structure graph, and the
   generated morphism (bundle maps, which the Shapes paper needs as homomorphisms of skeletons).
4. Causal precedence as the intersection closure (2.3), against a recursive definition over NN of
   the n-step reachability. The intersection is shorter to define and its minimality is one theorem;
   the n-step form gives induction on the length of a chain for free. Recommendation: intersection,
   with the n-step characterisation proven when a proof needs it.
5. Which protocol first: NSL (section 5, the paper's worked example, three strand shapes) is the
   recommendation; Otway-Rees after.

## 4. The first batches

* **S-1, the algebra** (one agent, about a week): the stages, A, freeness, structural induction, rank,
  width, subterm with Proposition 2.12, INV. Vocabulary file in structure-library (no proof), theorems
  in theorem-library. Everything `modulo 0`; the only citations are the list laws, NN recursion,
  BIG-UNION and CARD.
* **S-2, spaces and bundles** (one agent, about a week, after S-1 is wired): STRAND-SPACE, nodes, edges,
  BUNDLE with its laws, PRECEDES, Lemma 2.7 (the engine), 2.8, 2.9, origination.
* **S-3, the penetrator and ideals** (one agent, a week): 3.1 to 3.3, 6.1 to 6.9, Theorem 6.11.
* **S-4, NSL** (one agent, a week or two): the shapes of 5.1, Proposition 5.2 with its lemmas, then 5.8.

Risks: finiteness arguments in the tree go through CARD and are verbose (the bundle's minimal elements
will cost a day of its own); the intersection closures want the sethood of POWER(NODES x NODES), which
the tree has (`power-set`, CARTESIAN sethood); the eight penetrator shapes are tedious but mechanical.
The Shapes paper (skeletons, homomorphisms, the search) is a second design note once S-2 is in.
