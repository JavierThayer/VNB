;;; la-z-vocab.scm -- subdeterminants, equivalence by elementary operations and the
;;; gcd of a set of integers (LA-Z, 2026-10-19).
;;;
;;; THE SOURCE.  The user's linear-algebra notes (linear-algebra.tex), section
;;; "Subdeterminants": "A submatrix of a matrix A is one obtained by deleting rows and
;;; columns of A.  A minor is a square submatrix ... The sigma-th order subdeterminants of
;;; A is the set of values sdet_sigma A = {det B : B in minor_sigma A}"; section "Normal
;;; Forms": "C is equivalent by integer elementary operations to D, denoted C ~ D, if and
;;; only if there is a sequence of integral row and column operations which transform C to
;;; D"; Corollary 3.31 ("gcd sdet_sigma A = +/- gcd sdet_sigma B").
;;;
;;; THE DEFINITIONS.
;;;   SUBMATRIX(A, s, p, q)      -- the s-by-s matrix whose (i, j) entry is A_{p(i), q(j)},
;;;                                 for index maps p : [1,s] -> rows, q : [1,s] -> columns.
;;;   SDET(R, m, n, A, s)        -- the s-th order subdeterminants of the m-by-n matrix A:
;;;                                 the values det(R, s, SUBMATRIX(A, s, p, q)) for p an
;;;                                 INJECTION [1,s] -> [1,m] and q an INJECTION [1,s] -> [1,n].
;;;                                 A minor obtained by deleting rows and columns keeps the
;;;                                 order of the rows and columns kept; an injection need
;;;                                 not.  So SDET is the notes' sdet_sigma A together with the
;;;                                 negatives of its elements (a minor with its rows or
;;;                                 columns rearranged has the same determinant up to sign),
;;;                                 and every statement about gcd sdet_sigma is unchanged.
;;;                                 The notes' "up to sign" in 3.29 is absorbed by this set.
;;;   ELEM-EQUIV(R, m, n, A, B)  -- B = P A Q with P in ELEM-GEN(R, m) (row operations: left
;;;                                 multiplication by elementary matrices) and Q in
;;;                                 ELEM-GEN(R, n) (column operations).  Over ZZ-RING this is
;;;                                 the notes' C ~ D: the integral elementary matrices are
;;;                                 F[k,l], G[r,k,l] with r in Z and H[r,k] with r = +/- 1,
;;;                                 the units of Z, which is IS-ELEMENTARY's H clause.  A
;;;                                 sequence of row and column operations is one left and
;;;                                 one right factor, by associativity.
;;;   ZZ-IS-GCD-SET(S, d)        -- d is a greatest common divisor of the set S of integers:
;;;                                 d divides every element of S, and every integer that
;;;                                 divides every element of S divides d (ZZ-IS-GCD for a
;;;                                 pair, structure-library/zz-divisibility, is the model).
;;;
;;; Binders: smi_ smj_ (SUBMATRIX), sdx_ sdp_ sdq_ (SDET), eqp_ eqq_ (ELEM-EQUIV), gse_
;;; gsx_ (ZZ-IS-GCD-SET): names no predicate body, statement or driver uses elsewhere.
;;; Needs: structure-library/matrix (MATOF, ENTRY, MATMUL), determinant (DET), injection
;;; (INJECTION), zz-divisibility (ZZ-DIVIDES), la-elem-vocab (ELEM-GEN; unwired).
;;; LOAD WINDOW: after "structure-library/la-elem-vocab" (itself after determinant,
;;; load.scm:479), before "theorem-library/la-z-sdet".  Library: linear-algebra.
;;; No axiom, support or stamp.

(def-functoid 'SUBMATRIX '(A s p q)
  '(MATOF s s (VNB-LAMBDA (LIST smi_ smj_) (CARTESIAN (INTERVAL 1 s) (INTERVAL 1 s))
     (ENTRY A (p smi_) (q smj_)))))

(def-functoid 'SDET '(R m n A s)
  '(SEP sdx_ (CARR R)
     (FORSOME sdp_ (FORSOME sdq_
       (AND (IN sdp_ (INJECTION (INTERVAL 1 s) (INTERVAL 1 m)))
            (AND (IN sdq_ (INJECTION (INTERVAL 1 s) (INTERVAL 1 n)))
                 (= sdx_ (DET R s (SUBMATRIX A s sdp_ sdq_)))))))))

(def-predicate 'ELEM-EQUIV '(R m n A B)
  '(FORSOME eqp_ (FORSOME eqq_
     (AND (IN eqp_ (ELEM-GEN R m))
          (AND (IN eqq_ (ELEM-GEN R n))
               (= B (MATMUL R (MATMUL R eqp_ A) eqq_)))))))

(def-predicate 'ZZ-IS-GCD-SET '(S d)
  '(AND (IN d ZZ)
        (AND (FORALL gsx_ (IMPLIES (IN gsx_ S) (ZZ-DIVIDES d gsx_)))
             (FORALL gse_ (IMPLIES (IN gse_ ZZ)
               (IMPLIES (FORALL gsx_ (IMPLIES (IN gsx_ S) (ZZ-DIVIDES gse_ gsx_)))
                        (ZZ-DIVIDES gse_ d)))))))

(notation! 'SUBMATRIX 'kind 'functoid 'arity 4
           'english "the $2-by-$2 submatrix of $1 on the rows $3 and the columns $4")
(notation! 'SDET 'kind 'functoid 'arity 5
           'english "the set of order-$5 subdeterminants of $4")
(notation! 'ELEM-EQUIV 'kind 'predicate 'arity 5
           'english "$5 is obtained from $4 by elementary row and column operations")
(notation! 'ZZ-IS-GCD-SET 'kind 'predicate 'arity 2
           'english "$2 is a greatest common divisor of the integers in $1")
