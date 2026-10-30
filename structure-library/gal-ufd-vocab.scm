;;; gal-ufd-vocab.scm -- associates and unique factorization domains (galois-theory notes, section 1)
;;; (GALOIS, 2026-10-26).  DEFINITIONS ONLY.  Destination: structure-library/gal-ufd-vocab.scm,
;;; library algebra.  Load window: after scratchpad/catools/catools-gal-vocab (IS-UNIT,
;;; IS-PRIME-ELEMENT) and structure-library/finprod (PROD-RING).
;;;
;;; Finite products are the tree's PROD-RING(s, f, S) = FINPROD over the multiplicative commutative
;;; monoid of s (finprod.scm), taken over INTERVAL(1, n).
;;;
;;; IS-UFD follows the notes: every nonzero element is a unit times a product of primes, uniquely
;;; up to order and units.  The notes group equal primes into prime powers with pairwise
;;; inequivalent primes; here the product lists each prime with its multiplicity (p repeated a
;;; times), and "unique up to order and units" is a bijection of the index sets matching associated
;;; primes.  The two forms say the same thing (collect associated primes into powers).
(def-predicate 'ASSOCIATED '(gss_ gsa_ gsb_)
  '(AND (IN gsa_ (CARR gss_))
        (AND (IN gsb_ (CARR gss_))
             (FORSOME gsw_ (AND (IS-UNIT gss_ gsw_) (= gsb_ ((MUL gss_) gsw_ gsa_)))))))
(notation! 'ASSOCIATED 'kind 'predicate 'arity 3 'english "$2 and $3 are associated in $1")

(def-predicate 'IS-PRIME-SEQ '(gqs_ gqp_ gqn_)
  '(FORALL gqi_ (IMPLIES (IN gqi_ (INTERVAL 1 gqn_)) (IS-PRIME-ELEMENT gqs_ (gqp_ gqi_)))))
(notation! 'IS-PRIME-SEQ 'kind 'predicate 'arity 3 'english "$2(1), ..., $2($3) are primes of $1")

(def-predicate 'IS-UFD '(gus_)
  (conjuncts->and
    (list
      '(IS-INTEGRAL-DOMAIN gus_)
      '(FORALL gua_ (IMPLIES (IN gua_ (CARR gus_)) (IMPLIES (NOT (= gua_ (ZERO gus_)))
         (FORSOME guu_ (AND (IS-UNIT gus_ guu_)
           (FORSOME gun_ (AND (IN gun_ NN)
             (FORSOME gup_ (AND (IS-PRIME-SEQ gus_ gup_ gun_)
               (= gua_ ((MUL gus_) guu_ (PROD-RING gus_ gup_ (INTERVAL 1 gun_)))))))))))))
      '(FORALL gun_ (IMPLIES (IN gun_ NN) (FORALL gup_ (IMPLIES (IS-PRIME-SEQ gus_ gup_ gun_)
         (FORALL gum_ (IMPLIES (IN gum_ NN) (FORALL guq_ (IMPLIES (IS-PRIME-SEQ gus_ guq_ gum_)
           (FORALL guu_ (IMPLIES (IS-UNIT gus_ guu_) (FORALL guv_ (IMPLIES (IS-UNIT gus_ guv_)
             (IMPLIES (= ((MUL gus_) guu_ (PROD-RING gus_ gup_ (INTERVAL 1 gun_)))
                         ((MUL gus_) guv_ (PROD-RING gus_ guq_ (INTERVAL 1 gum_))))
               (AND (= gun_ gum_)
                    (FORSOME gus2_ (AND (IN gus2_ (BIJECTION (INTERVAL 1 gun_) (INTERVAL 1 gum_)))
                      (FORALL gui_ (IMPLIES (IN gui_ (INTERVAL 1 gun_))
                        (ASSOCIATED gus_ (gup_ gui_) (guq_ (gus2_ gui_))))))))))))))))))))))))
(notation! 'IS-UFD 'kind 'predicate 'arity 1 'english "$1 is a unique factorization domain")
