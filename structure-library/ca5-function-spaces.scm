;;; ca5-function-spaces.scm -- THE VOCABULARY OF CHAPTER 5 (FUNCTION SPACES) of the
;;; user's complex analysis notes (~/docs/complex-analysis.pdf, s.5.1), first part.
;;; DEFINITIONS ONLY; the laws are PROVEN in theorem-library/ca5-function-spaces.scm.
;;; Agent CA-5, 2026-10-14.  Every definition below is a decision for the user,
;;; confirmed after the fact.
;;;
;;; ---------------------------------------------------------------------
;;; CC-EXHAUST(u, n).  Lemma 5.1 of the notes: a separable locally compact metric
;;; space has an EXHAUSTIVE sequence of compact sets K_n -- every compact subset
;;; lies in some K_n.  Chapter 5 uses it for U an OPEN subset of CC only, and for
;;; that case the sequence is written down explicitly:
;;;
;;;     K_n = { z in CC : |z| <= n  and  B(z, 1/(n+1)) subset U },
;;;
;;; B the OPEN ball of CC-MS.  K_n is closed and bounded, hence compact; K_n lies
;;; in the interior of K_{n+1}; every point of U, and every compact subset of U,
;;; lies in some K_n (theorem-library/ca5-function-spaces.scm).  The definition
;;; makes sense for any class u; the laws carry the hypotheses they need.
;;; REJECTED ALTERNATIVE: { z : |z| <= n, dist(z, CC \ U) >= 1/(n+1) }, the
;;; textbook form (PT-SET-DIST exists in the tree): for an open U it is the same set
;;; (B(z, r) subset U iff dist(z, CC \ U) >= r), and the ball form needs no infimum.
;;; The general separable locally compact case of Lemma 5.1 is NOT stated.
;;;
;;; The binder `cxz_' is spelled like nothing else in the tree (CLAUDE.md: a term
;;; the driver rebuilds must use binders no predicate body binds).
(def-functoid 'CC-EXHAUST '(u n)
  '(SEP cxz_ CC
     (AND (<= (magnitude cxz_) n)
          (SUBSET (BALL CC-MS cxz_ (recip (+ n 1))) u))))

(notation! 'CC-EXHAUST 'kind 'functoid 'arity 2
           'english "the $2-th compact set of the exhaustion of $1")
(def-comments! 'CC-EXHAUST
  "$u$ is an open subset of $\\mathbb{C}$ and $n \\in \\mathbb{N}$;"
  "$K_n = \\{ z \\in \\mathbb{C} : |z| \\le n,\\ B(z, 1/(n+1)) \\subseteq u \\}$.")

;;; ---------------------------------------------------------------------
;;; C(U) and H(U) AS MODULES OVER CC (Proposition 5.2 / 5.3 setting).
;;;
;;; CC-CONT-FNS(u): the continuous functions on u -- f in FUN(u, CC), continuous at
;;; every point of u for the subspace metric (the continuity clause of morera and of
;;; holomorphic-on-continuous, verbatim).  CC-HOL-FNS(u): HOLOMORPHIC-ON(u, f).
;;; CC-FN-MODULE(u, v): the MODULE tuple on a class v of functions u -> CC with the
;;; POINTWISE operations; the scalars are NORMED-FIELD-AS-COMMUTATIVE-RING(CC-NORMED-FIELD),
;;; the six-slot ring view the Frechet vocabulary (IS-SEMINORM-FAMILY) pins SCAL to.
;;; It is a MODULE instance once v is closed under the operations (theorem-library);
;;; it is a functoid and not a declare-instance! because it is parametrised by u.
;;; CC-EXHAUST-SEMINORMS(u, v): k |-> (f |-> CC-SUP-NORM(f, K_k)), the seminorm family.
;;; Binders cf*_, ccf_, ccy_: used by no other body.
(def-functoid 'CC-CONT-FNS '(u)
  '(SEP ccf_ (FUN u CC)
     (FORALL ccy_ (IMPLIES (IN ccy_ u)
       (IS-CONTINUOUS-AT (SUBSPACE-MS (NF-METRIC-SPACE CC-NORMED-FIELD) u)
                         (NF-METRIC-SPACE CC-NORMED-FIELD) ccf_ ccy_)))))
(notation! 'CC-CONT-FNS 'kind 'functoid 'arity 1
           'english "the continuous complex functions on $1")

(def-functoid 'CC-HOL-FNS '(u)
  '(SEP ccf_ (FUN u CC) (HOLOMORPHIC-ON u ccf_)))
(notation! 'CC-HOL-FNS 'kind 'functoid 'arity 1
           'english "the holomorphic functions on $1")

(def-functoid 'CC-FN-MODULE '(u v)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD)
         v
         (VNB-LAMBDA (LIST cfa_ cfb_) (CARTESIAN v v) (VNB-LAMBDA cfz_ u (+ (cfa_ cfz_) (cfb_ cfz_))))
         (VNB-LAMBDA cfz_ u 0)
         (VNB-LAMBDA cfa_ v (VNB-LAMBDA cfz_ u (- (cfa_ cfz_))))
         (VNB-LAMBDA (LIST cfc_ cfa_) (CARTESIAN CC v) (VNB-LAMBDA cfz_ u (* cfc_ (cfa_ cfz_))))))
(notation! 'CC-FN-MODULE 'kind 'functoid 'arity 2
           'english "the module of the functions $2 on $1, with pointwise operations")

(def-functoid 'CC-EXHAUST-SEMINORMS '(u v)
  '(VNB-LAMBDA cfk_ NN (VNB-LAMBDA cfa_ v (CC-SUP-NORM cfa_ (CC-EXHAUST u cfk_)))))
(notation! 'CC-EXHAUST-SEMINORMS 'kind 'functoid 'arity 2
           'english "the sup seminorms on the exhaustion of $1, on $2")

;;; ---------------------------------------------------------------------
;;; CC-HOL-BOUNDED(u, a): a BOUNDED SUBSET OF H(u), the notes' 5.2: a is a class of holomorphic
;;; functions on u (a subset of CC-HOL-FNS(u)) bounded on every compact subset of u.  It is stated
;;; on the exhaustion -- for every n a bound M_n with |f(z)| <= M_n for all f in a and z in K_n --
;;; which is "bounded in every seminorm p_n" of the Frechet structure of ca5-frechet.scm, and is
;;; equivalent to the notes' "sup over every compact K of sup over a of |f| is finite" by
;;; cc-exhaust-exhaustive (every compact subset of u lies in some K_n).  Binders ch*_ are used by
;;; no other body.
(def-predicate 'CC-HOL-BOUNDED '(u a)
  '(AND (SUBSET a (CC-HOL-FNS u))
        (FORALL chn_ (IMPLIES (IN chn_ NN)
          (FORSOME chm_ (AND (IN chm_ RR)
            (FORALL chf_ (IMPLIES (IN chf_ a)
              (FORALL chz_ (IMPLIES (IN chz_ (CC-EXHAUST u chn_))
                (<= (magnitude (chf_ chz_)) chm_)))))))))))
(notation! 'CC-HOL-BOUNDED 'kind 'predicate 'arity 2
           'english "$2 is a bounded set of holomorphic functions on $1")
