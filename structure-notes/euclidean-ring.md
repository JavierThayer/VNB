A **Euclidean ring** is an integral domain carrying a degree (or
size) function $\mathit{deg} : A \to \mathbb{N}$ that supports division
with remainder: for every $a$ and every nonzero $b$ there are $q, r$
with $a = qb + r$ and either $r = \mathit{zero}$ or $\mathit{deg}(r) < \mathit{deg}(b)$.
The two motivating instances are $\mathbb{Z}$ (degree = absolute value)
and $k[x]$ for a field $k$ (degree = polynomial degree). It is the
weakest setting in which the Euclidean algorithm — hence existence of
gcds and Bézout — goes through.

**The degree function is not structure data.** The defining predicate
asserts the degree function **exists** (`FORSOME deg`); it is not one of
the carried components $\langle a, \mathit{add}, \mathit{mul}, \mathit{neg}, \mathit{zero}, \mathit{one}\rangle$.
So a proof that wants to compute with "the" degree function cannot
simply project it out — it must **choose** one. The set of admissible
degree functions $\{\, f \in \mathrm{Fun}(A, \mathbb{N}) : f \text{ witnesses division with remainder} \,\}$
is nonempty exactly when $s$ is a Euclidean ring, so the standard
opening move is to take

$\mathit{deg} := \varepsilon(\{\, f \in \mathrm{Fun}(A,\mathbb{N}) : \cdots \,\})$

via the global choice operator. (Equivalently, eliminate the `FORSOME`
to introduce a fresh witness constant scoped to the proof; the
$\varepsilon$ form is preferable when you need $\mathit{deg}$ to denote
the **same** function across several lemmas, e.g. when developing gcd.)

**It is genuinely a choice.** The witnessing degree function is not
unique — a ring can be Euclidean with respect to many different degree
functions — so nothing canonical is being recovered. Proofs should rely
only on the division property, never on incidental features of whichever
$\mathit{deg}$ the choice happens to name.
