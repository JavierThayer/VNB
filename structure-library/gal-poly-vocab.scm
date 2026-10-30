;;; gal-poly-vocab.scm -- evaluation of a formal polynomial and the polynomial x - c
;;; (galois-theory notes, section 8: "the evaluation mapping F[x] x F -> F, (p(x), a) |-> p(a)";
;;; "a root of a polynomial is an element a in F such that p(a) = 0") (GALOIS B2, 2026-10-26).
;;; DEFINITIONS ONLY.  Destination: structure-library/gal-poly-vocab.scm, library algebra.
;;; Load window: after structure-library/poly-degree.scm (DEG, MONOMIAL) and sequences.scm (SUM-AG).
;;;
;;; POLY-EVAL(A, p, t) = sum_{k <= deg p} p(k) t^k, the sum taken in the additive group of A over
;;; {0, ..., deg p}; any larger bound gives the same value (poly-eval-bound, gal-poly.scm).
(def-functoid 'POLY-EVAL '(A p t)
  '(SUM-AG (RING-ADDITIVE-AG A) (VNB-LAMBDA gek_ NN ((MUL A) (p gek_) (RING-POWER A t gek_))) (succ (DEG A p))))
(notation! 'POLY-EVAL 'arity 3 'english "the value of $2 at $3")

;;; X-MINUS(A, c) = x - c, as an element of A[x].
(def-functoid 'X-MINUS '(A c)
  '((ADD (POLY A)) (MONOMIAL A (ONE A) 1) (MONOMIAL A ((NEG A) c) 0)))
(notation! 'X-MINUS 'arity 2 'english "the polynomial x - $2 over $1")

;;; POLY-LE(A, m) = F[x]_m, the polynomials of degree at most m (notes, section 9).
(def-functoid 'POLY-LE '(A m)
  '(SEP gpl_ (CARR (POLY A)) (DEG-BOUND A gpl_ m)))
(notation! 'POLY-LE 'arity 2 'english "the polynomials over $1 of degree at most $2")

;;; EVAL-AT-POINTS(A, th, m) = the map E : p |-> (p(th_1), ..., p(th_{m+1})) on F[x]_m, a value
;;; being a function on {1, ..., m+1} (notes, Proposition 1.47, with n = m + 1).
(def-functoid 'EVAL-AT-POINTS '(A th m)
  '(VNB-LAMBDA gep_ (POLY-LE A m)
     (VNB-LAMBDA gei_ (INTERVAL 1 (succ m)) (POLY-EVAL A gep_ (th gei_)))))
(notation! 'EVAL-AT-POINTS 'arity 3 'english "the evaluation at the points $2(1), ..., $2($3 + 1)")
