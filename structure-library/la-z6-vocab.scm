;;; la-z6-vocab.scm -- polynomials in n indeterminates and the permutation of the indeterminates
;;; (linear algebra, the paragraph before Proposition 3.15 and 3.15 itself) (LA-Z6, 2026-10-25).
;;; No proof in this file.
;;;
;;; THE SOURCE.  The user's linear-algebra notes, section "Determinants": "A permutation on a set X is a
;;; bijective mapping X -> X ... If p is a polynomial in the indeterminates x_1, ..., x_n, then by applying
;;; the permutation sigma to the indeterminates in p, we obtain a polynomial sigma . p."  Proposition 3.15:
;;; "p |-> sigma . p is an isomorphism of the ring R[x_1, x_2, ..., x_n]."
;;;
;;; THE CONSTRUCTION (standard; the brief of 2026-10-25).  R[x_1, ..., x_n] is the monoid algebra
;;; MONALG(R, M) (structure-library/polynomial) over the additive monoid M of MULTI-INDICES: the functions
;;; alpha : [1, n] -> NN, added pointwise, with the zero function as identity.  A polynomial is its
;;; finitely-supported coefficient function alpha |-> p_alpha, the coefficient of x_1^alpha_1 ... x_n^alpha_n.
;;; For a permutation sigma of [1, n], sigma . p has coefficient (sigma . p)_beta = p_(beta o sigma): the
;;; monomial x^alpha goes to prod_i x_(sigma i)^(alpha_i), whose exponent beta satisfies beta(sigma i) =
;;; alpha(i).  So sigma . p is p composed with the monoid map beta |-> beta o sigma, which is the special
;;; case of the PULLBACK of a coefficient function along a map of the monoid.
;;;
;;; THE DEFINITIONS.
;;;   IS-ISO-RING(A, B, f)           -- f is a ring isomorphism: IS-HOM-RING(A, B, f) and f a bijection of the
;;;                                     carriers (the shape of IS-ISO-MODULE).
;;;   MONALG-PULLBACK(A, M, ph, f)   -- the coefficient function f composed with the monoid map ph:
;;;                                     x |-> f(ph x) on CARR(M).
;;;   MI-ADD(X, u, v), MI-ZERO(X)    -- pointwise sum and zero of functions X -> NN.
;;;   MULTI-INDEX-MONOID(X)          -- [FUN(X, NN), pointwise +, the zero function]: the multi-indices on the
;;;                                     index set X, a commutative monoid (proven in la-z6-mpoly).
;;;   MI-REINDEX(X, s, b)            -- the multi-index b o s, i.e. j |-> b(s j) on X.
;;;   MPOLY(R, n)                    -- R[x_1, ..., x_n] = MONALG(R, MULTI-INDEX-MONOID([1, n])).
;;;   VAR-PERMUTE(R, n, s, p)        -- sigma . p = the pullback of p along beta |-> MI-REINDEX([1,n], s, beta).
;;;
;;; Binders: mpx_ mia_ miu_ miv_ mir_ mib_ -- names no predicate body, statement or driver uses elsewhere.
;;; Needs: structure-library/polynomial (MONALG, FINSUPP), monoid (MONOID), ring (IS-HOM-RING, generated),
;;; bijection (BIJECTION), matrix (INTERVAL).
;;; Destination structure-library/; LOAD WINDOW after "structure-library/polynomial" (load.scm:489), before
;;; theorem-library/la-z6-pullback.  Library: algebra (nothing in it is linear algebra).
;;; No axiom, support or stamp.

(def-predicate 'IS-ISO-RING '(A B f)
  '(AND (IS-HOM-RING A B f) (IN f (BIJECTION (CARR A) (CARR B)))))

(def-functoid 'MONALG-PULLBACK '(A M ph f)
  '(VNB-LAMBDA mpx_ (CARR M) (f (ph mpx_))))

(def-functoid 'MI-ADD '(X u v)
  '(VNB-LAMBDA mia_ X (+ (u mia_) (v mia_))))

(def-functoid 'MI-ZERO '(X)
  '(VNB-LAMBDA mia_ X 0))

(def-functoid 'MULTI-INDEX-MONOID '(X)
  '(LIST (FUN X NN)
         (VNB-LAMBDA (LIST miu_ miv_) (CARTESIAN (FUN X NN) (FUN X NN)) (MI-ADD X miu_ miv_))
         (MI-ZERO X)))

(def-functoid 'MI-REINDEX '(X s b)
  '(VNB-LAMBDA mir_ X (b (s mir_))))

(def-functoid 'MPOLY '(R n)
  '(MONALG R (MULTI-INDEX-MONOID (INTERVAL 1 n))))

(def-functoid 'VAR-PERMUTE '(R n s p)
  '(MONALG-PULLBACK R (MULTI-INDEX-MONOID (INTERVAL 1 n))
                    (VNB-LAMBDA mib_ (FUN (INTERVAL 1 n) NN) (MI-REINDEX (INTERVAL 1 n) s mib_))
                    p))

(notation! 'IS-ISO-RING 'kind 'predicate 'arity 3
           'english "$3 is a ring isomorphism from $1 to $2")
(notation! 'MONALG-PULLBACK 'kind 'functoid 'arity 4
           'english "the pullback of $4 along $3")
(notation! 'MI-ADD 'kind 'functoid 'arity 3
           'english "the pointwise sum of the multi-indices $2 and $3")
(notation! 'MI-ZERO 'kind 'functoid 'arity 1
           'english "the zero multi-index on $1")
(notation! 'MULTI-INDEX-MONOID 'kind 'functoid 'arity 1
           'english "the additive monoid of multi-indices on $1")
(notation! 'MI-REINDEX 'kind 'functoid 'arity 3
           'english "the multi-index $3 composed with $2")
(notation! 'MPOLY 'kind 'functoid 'arity 2
           'english "the polynomial ring $1[x_1, ..., x_$2]")
(notation! 'VAR-PERMUTE 'kind 'functoid 'arity 4
           'english "the polynomial $4 with its indeterminates permuted by $3")
