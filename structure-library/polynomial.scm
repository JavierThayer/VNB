;;; polynomial.scm -- the monoid-algebra construction A[M], and polynomials as
;;; its specialisation A[NN].
;;;
;;; Following Bourbaki (Algebra I, Ch. III, sec. 2): the algebra of a monoid M
;;; over a ring A is the free A-module on M with convolution multiplication.
;;; Concretely, its elements are the FINITELY-SUPPORTED functions M -> A, added
;;; pointwise and multiplied by convolution.  Polynomials in one variable are
;;; A[NN] (exponents are naturals); Laurent polynomials A[ZZ]; several variables
;;; A[NN^k]; the group algebra A[G].  ONE construction, one proof burden, the
;;; whole family -- which is the point of doing it this way rather than a bespoke
;;; POLYNOMIAL structure.
;;;
;;; The design decision that matters is the convolution's index set.  We take
;;;   (f * g)(m) = SUM over { (p,q) in supp(f) x supp(g) : p.q = m } of f(p).g(q)
;;; -- summing over supp(f) x supp(g), a product of two FINITE sets, filtered by
;;; p.q = m.  This is finite for EVERY monoid M, with no "M has finitely many
;;; factorisations" side condition; the alternative (sum over all factorisations
;;; of m in M) would need one.
;;;
;;; The parameter is a MONOID, not a semigroup: the identity of M is what gives
;;; the algebra its ONE (the indicator of IDEN(M) = the constant polynomial 1).
;;; A semigroup parameter would give a non-unital algebra (an rng), a separate
;;; variant not built here.
;;;
;;; Needs: monoid (CARR/OPR/IDEN, monoid.scm), ring (CARR/ADD/MUL/NEG/ZERO/ONE),
;;; RING-ADDITIVE-AG (views.scm) for FINSUM, FINSUM (finsum.scm), CARD
;;; (cardinality.scm), NN-ADD-MONOID (numeric-instances.scm).  Loaded after all.
;;; ====================================================================
;;; RETIRED 2026-09-14 (proven): monalg-is-ring -- theorem-library/monalg-is-ring.scm
;;; RETIRED 2026-09-14 (proven): monalg-mul-fun -- theorem-library/monalg-is-ring.scm
;;; RETIRED 2026-09-14 (proven): monalg-distrib-left -- theorem-library/monalg-is-ring.scm
;;; RETIRED 2026-09-14 (proven): monalg-one-left -- theorem-library/monalg-is-ring.scm

;;; ---- SUPP: the support of a function into a ring ----------------------
;;; SUPP(A, M, f) = { m in CARR(M) : f(m) /= ZERO(A) }.  A SEP over CARR(M),
;;; so it inherits sethood and the sep-membership characterisation.
(def-functoid 'SUPP '(A M f)
  '(SEP x_ (CARR M) (NOT (= (f x_) (ZERO A)))))
(notation! 'SUPP 'arity 3 'english "the support of $3")
(gloss! 'SUPP
  "SUPP(A,M,f) -- the support of f: the set of m in CARR(M) at which f(m) is not
   the zero of the ring A.  A finitely-supported function is one whose support
   is finite (CARD in NN).")

;;; ---- FINSUPP: the carrier of the monoid algebra ----------------------
;;; FINSUPP(A, M) = { f in FUN(CARR(M), CARR(A)) : SUPP(A,M,f) is finite }.
;;; Finiteness is `(IN (CARD ...) NN)', the house idiom (compactness.scm).
(def-functoid 'FINSUPP '(A M)
  '(SEP f (FUN (CARR M) (CARR A)) (IN (CARD (SUPP A M f)) NN)))
(notation! 'FINSUPP 'arity 2 'english "the finitely-supported functions $2 -> $1")
(gloss! 'FINSUPP
  "FINSUPP(A,M) -- the finitely-supported functions from CARR(M) to CARR(A);
   the carrier of the monoid algebra A[M].")

;;; ---- the operations, each a functoid (the MAT-RING factoring) --------

;;; The point at which these functions are evaluated is x_ (trailing underscore),
;;; NEVER m: `m' case-folds onto the monoid parameter M and would capture it
;;; inside the lambda, silently turning (OPR M) into OPR-of-the-point and
;;; (IDEN M) into IDEN-of-the-point.  The load does not complain -- a functoid
;;; body is not binder-audited -- so the wrong term just ships.  (Found by the
;;; OPERATORS.md unfold reading `opr(m)' on 2026-07-24.)

;;; pointwise sum: (f + g)(x) = f(x) + g(x) in A.
;;; M is a parameter because the pointwise sum's DOMAIN is M's carrier, and a
;;; lambda now carries its domain (2026-08-02).  Without M this functoid could
;;; not say what set its value is a function on.
(def-functoid 'MONALG-ADD '(A M f g)
  '(VNB-LAMBDA x_ (CARR M) ((ADD A) (f x_) (g x_))))

;;; pointwise negation.
(def-functoid 'MONALG-NEG '(A M f)
  '(VNB-LAMBDA x_ (CARR M) ((NEG A) (f x_))))

;;; the zero of A[M]: the constant zero function.
(def-functoid 'MONALG-ZERO '(A M)
  '(VNB-LAMBDA x_ (CARR M) (ZERO A)))

;;; the one of A[M]: the indicator of IDEN(M) (value ONE(A) there, ZERO else) --
;;; the constant polynomial 1.
(def-functoid 'MONALG-ONE '(A M)
  '(VNB-LAMBDA x_ (CARR M) (IF (= x_ (IDEN M)) (ONE A) (ZERO A))))

;;; convolution: (f * g)(x) = SUM_{ p.q = x, p in supp f, q in supp g } f(p).g(q).
;;; The index set is a SEP of pairs over supp(f) x supp(g) (the ringoid.scm
;;; CARTESIAN-SEP idiom); FINSUM sums the pair-summand over it in A's additive AG.
;;; Finite because supp(f) x supp(g) is a product of finite sets.
(def-functoid 'MONALG-MUL '(A M f g)
  '(VNB-LAMBDA x_ (CARR M)
     (FINSUM (RING-ADDITIVE-AG A)
             (VNB-LAMBDA p (SEP p (CARTESIAN (SUPP A M f) (SUPP A M g))
                  (= ((OPR M) (NTH 1 p) (NTH 2 p)) x_)) ((MUL A) (f (NTH 1 p)) (g (NTH 2 p))))
             (SEP p (CARTESIAN (SUPP A M f) (SUPP A M g))
                  (= ((OPR M) (NTH 1 p) (NTH 2 p)) x_)))))

;;; ---- MONALG: the monoid algebra as a RING 6-tuple --------------------
;;; [CARR ADD MUL NEG ZERO ONE], the ops curried to fit the RING shape, exactly
;;; as MAT-RING packages the matrix ring.
(def-functoid 'MONALG '(A M)
  '(LIST (FINSUPP A M)
         (VNB-LAMBDA (LIST f g) (CARTESIAN (FINSUPP A M) (FINSUPP A M)) (MONALG-ADD A M f g))
         (VNB-LAMBDA (LIST f g) (CARTESIAN (FINSUPP A M) (FINSUPP A M)) (MONALG-MUL A M f g))
         (VNB-LAMBDA f (FINSUPP A M) (MONALG-NEG A M f))
         (MONALG-ZERO A M)
         (MONALG-ONE A M)))
(notation! 'MONALG 'arity 2 'english "the monoid algebra $1[$2]")
(gloss! 'MONALG
  "MONALG(A,M) -- the monoid algebra A[M]: finitely-supported functions M -> A,
   added pointwise, multiplied by convolution, packaged as a RING 6-tuple.
   Polynomials are the case M = NN-ADD-MONOID; see POLY.")

;;; ---- POLY: one-variable polynomials A[NN] ----------------------------
;;; NN-ADD-MONOID = [NN, binplus, 0] is the exponent monoid; a polynomial is a
;;; finitely-supported NN -> CARR(A) (its coefficient sequence), and convolution
;;; over NN is the Cauchy product SUM_{i+j=n} a_i b_j.
(def-functoid 'POLY '(A)
  '(MONALG A NN-ADD-MONOID))
(notation! 'POLY 'arity 1 'english "$1[x]")
(gloss! 'POLY
  "POLY(A) = MONALG(A, NN-ADD-MONOID) -- the ring of polynomials in one variable
   over A.  A polynomial is its finitely-supported coefficient sequence
   NN -> CARR(A); multiplication is the Cauchy product.")

;;; =====================================================================
;;; Theorem seeds.  The ring laws of A[M] are ASSERTED with a Bourbaki
;;; citation; the convolution-associativity proof is the classic triple-sum
;;; reindexing, deferred.  poly-is-ring below is DERIVED (a real proof), not a
;;; seed -- it instantiates monalg-is-ring at NN-ADD-MONOID.
;;; =====================================================================

;;; A[M] is a ring when A is a ring and M a monoid.  The umbrella statement.
(gloss! 'monalg-is-ring
  "A[M] is a ring when A is a ring and M a monoid (Bourbaki, Algebra I, III.2).
   The hard part behind it is monalg-mul-assoc.")
(topic! 'monalg-is-ring 'algebra)

;;; The convolution is finitely supported -- supp(f*g) is contained in the finite
;;; set supp(f).supp(g), so the product lands back in the carrier.  This is the
;;; typing that makes MUL an operation on FINSUPP at all.
(gloss! 'monalg-mul-fun
  "The convolution of two finitely-supported functions is finitely supported:
   supp(f*g) is contained in supp(f).supp(g), a product of finite sets.")
(topic! 'monalg-mul-fun 'algebra)

;;; MOVED 2026-08-20 to theorem-library/monalg-laws.scm, where it is PROVEN:
;;; `monalg-add-fun' -- the pointwise sum stays finitely supported, because
;;; supp(f+g) is contained in supp(f) u supp(g).  It was asserted here with a
;;; Bourbaki reference warrant; it is now a theorem, billing
;;; {ring-add-closed, card-subset-nn}.  Nothing cited it at the time of the
;;; move, so no bill changed.  The file also proves the two bricks the argument
;;; needed and nothing in the tree had: `monoid-carrier-is-set' (the sethood
;;; conjunct of the IS-MONOID definition, which every `lam-t' over a structure
;;; carrier asks for) and `monalg-add-apply' (the pointwise value of the
;;; pointwise sum), and it surveys what the remaining five laws are missing.

;;; Associativity of convolution -- THE key obstacle.  (f*g)*h = f*(g*h) unfolds
;;; to a triple sum over { (p,q,r) : p.q.r = m } grouped two ways; equality is a
;;; reindexing that uses the associativity of M's OPR and the ring distributive
;;; law.  Stated so proofs can lean on it; the proof itself is deferred.
;;; monalg-mul-assoc RETIRED 2026-09-18 (rake batch 5c): proven in the block spliced into theorem-library/monalg-is-ring.scm

;;; Left distributivity of convolution over pointwise sum.  (Right is the mirror.)
(gloss! 'monalg-distrib-left
  "Convolution distributes over pointwise addition on the left; the right law is
   the mirror image.")
(topic! 'monalg-distrib-left 'algebra)

;;; The unit law: the indicator of IDEN(M) is a left identity for convolution.
;;; (Right identity is the mirror.)  This is where the MONOID identity is used.
;;; Stated POINTWISE -- ((ONE * f) m) = (f m) for every m -- NOT as the function
;;; equation (ONE * f) = f.  A support with a bare schema variable as one whole
;;; side registers a reverse rewrite whose pattern is that lone variable, which
;;; matches every term and loops any normalisation walk (it hung clear-first-col
;;; on 2026-07-24).  The pointwise form keeps both sides headed by an
;;; application, so no such wildcard macete is generated.  Function equality then
;;; follows by extensionality where a proof needs it.
;; The point is x_ (trailing underscore), NOT m: `m' case-folds onto the monoid
;; parameter M, collapsing the statement (case-fold-audit catches it).
(gloss! 'monalg-one-left
  "The indicator of IDEN(M) is a left identity for convolution -- the constant
   polynomial 1.  Stated pointwise: ((ONE * f) m) = (f m).  The monoid identity
   of M is exactly what makes this hold.")
(topic! 'monalg-one-left 'algebra)

;;; A[M] is commutative when both A and M are.  (Convolution is commutative iff
;;; M is; the coefficient products commute iff A is.)
;;; monalg-comm RETIRED 2026-09-18 (rake batch 5b): proven in theorem-library/rake-monalg-comm.scm
(gloss! 'monalg-comm
  "A[M] is a commutative ring when A is a commutative ring and M a commutative
   monoid.  In particular A[x] is commutative for commutative A.")
(topic! 'monalg-comm 'algebra)
