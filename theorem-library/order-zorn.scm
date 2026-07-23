;;; order-zorn.scm -- abstract partial orders and ZORN'S LEMMA (statement only).
;;; Seed for the functional-analysis build (Hahn-Banach for seminorms needs Zorn).
;;; Added 2026-07-22.  A partial order is a ground SET grd with an order relation
;;; carried as a set of 2-element lists: "x <= y" is (IN (LIST x y) porel).  This
;;; sidesteps any ordered-pair / CARTESIAN representation choice -- membership of
;;; (LIST x y) is all we ever ask.  (Binder is `porel', NOT `rel' -- `rel' is a
;;; registered accessor and the load-time constant-binder audit rejects it.)
;;; ====================================================================

(define (oz-all  v cond body) `(FORALL  ,v (IMPLIES ,cond ,body)))
(define (oz-some v cond body) `(FORSOME ,v (AND     ,cond ,body)))

;;; IS-PARTIAL-ORDER(grd, porel): porel is a reflexive, antisymmetric, transitive
;;; relation on the ground set grd.
(def-predicate 'IS-PARTIAL-ORDER '(grd porel)
  (conjuncts->and
    (list
      '(IN grd SET)
      '(IN porel SET)
      (oz-all 'x '(IN x grd) '(IN (LIST x x) porel))                       ; reflexive
      (oz-all 'x '(IN x grd)
        (oz-all 'y '(IN y grd)
          '(IMPLIES (AND (IN (LIST x y) porel) (IN (LIST y x) porel)) (= x y))))
      (oz-all 'x '(IN x grd)
        (oz-all 'y '(IN y grd)
          (oz-all 'z '(IN z grd)
            '(IMPLIES (AND (IN (LIST x y) porel) (IN (LIST y z) porel))
                      (IN (LIST x z) porel))))))))

;;; IS-CHAIN(grd, porel, ch): ch is a subset of grd totally ordered by porel.
(def-predicate 'IS-CHAIN '(grd porel ch)
  (conjuncts->and
    (list
      '(SUBSET ch grd)
      (oz-all 'x '(IN x ch)
        (oz-all 'y '(IN y ch)
          '(OR (IN (LIST x y) porel) (IN (LIST y x) porel)))))))

;;; IS-UPPER-BOUND(grd, porel, ch, b): b in grd dominates every element of ch.
(def-predicate 'IS-UPPER-BOUND '(grd porel ch b)
  (conjuncts->and
    (list
      '(IN b grd)
      (oz-all 'x '(IN x ch) '(IN (LIST x b) porel)))))

;;; IS-MAXIMAL(grd, porel, mx): nothing in grd lies strictly above mx.
(def-predicate 'IS-MAXIMAL '(grd porel mx)
  (conjuncts->and
    (list
      '(IN mx grd)
      (oz-all 'y '(IN y grd)
        '(IMPLIES (IN (LIST mx y) porel) (IN (LIST y mx) porel))))))

;;; ZORN'S LEMMA: a nonempty partial order in which every chain has an upper
;;; bound has a maximal element.
(support 'zorn-lemma
  (forall-guarded '(grd porel)
    (list
      '(IS-PARTIAL-ORDER grd porel)
      '(FORSOME w (IN w grd))
      '(FORALL ch (IMPLIES (IS-CHAIN grd porel ch)
         (FORSOME b (IS-UPPER-BOUND grd porel ch b)))))
    '(FORSOME mx (IS-MAXIMAL grd porel mx))))
(warrant! 'zorn-lemma 'reference '(yosida "Zorn's Lemma, Ch. 0.1" 20))
(gloss! 'zorn-lemma
  "Zorn's lemma: if (grd, porel) is a partially ordered set that is nonempty and in
   which every chain (totally ordered subset) has an upper bound in grd, then grd
   has a maximal element.  Equivalent to the axiom of choice; the intended proof
   here is from the already-installed well-ordering-principle (well-order grd,
   transfinite-recursively build a chain, its sup is maximal), hence the rests-on.")
(category! 'zorn-lemma 'set-quotient)
;; Intended proof: from well-ordering-principle (every set can be well-ordered).
(rests-on 'zorn-lemma '(well-ordering-principle))
