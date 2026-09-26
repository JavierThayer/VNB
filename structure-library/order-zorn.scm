;;; MOVED 2026-09-20 (batch 12-A) from theorem-library/: this file is VOCABULARY --
;;; definitions, notation and warranted supports, not one proof -- and every theorem
;;; stated with it had to load below it.  Its load.scm slot is unchanged.
;;; order-zorn.scm -- abstract partial orders and ZORN'S LEMMA (statement only).
;;; Seed for the functional-analysis build (Hahn-Banach for seminorms needs Zorn).
;;; Added 2026-07-22.  A partial order is a ground SET grd with an order relation
;;; carried as a set of 2-element lists: "x <= y" is (IN (LIST x y) porel).  This
;;; sidesteps any ordered-pair / CARTESIAN representation choice -- membership of
;;; (LIST x y) is all we ever ask.  (Binder is `porel', NOT `rel' -- `rel' is a
;;; registered accessor and the load-time constant-binder audit rejects it.)
;;; ====================================================================

;;; IS-PARTIAL-ORDER(grd, porel): porel is a reflexive, antisymmetric, transitive
;;; relation on the ground set grd.
(def-predicate 'IS-PARTIAL-ORDER '(grd porel)
  (conjuncts->and
    (list
      '(IN grd SET)
      '(IN porel SET)
      (forall-guarded 'x '(IN x grd) '(IN (LIST x x) porel))                       ; reflexive
      (forall-guarded 'x '(IN x grd)
        (forall-guarded 'y '(IN y grd)
          '(IMPLIES (AND (IN (LIST x y) porel) (IN (LIST y x) porel)) (= x y))))
      (forall-guarded 'x '(IN x grd)
        (forall-guarded 'y '(IN y grd)
          (forall-guarded 'z '(IN z grd)
            '(IMPLIES (AND (IN (LIST x y) porel) (IN (LIST y z) porel))
                      (IN (LIST x z) porel))))))))

;;; IS-CHAIN(grd, porel, ch): ch is a subset of grd totally ordered by porel.
(def-predicate 'IS-CHAIN '(grd porel ch)
  (conjuncts->and
    (list
      '(SUBSET ch grd)
      (forall-guarded 'x '(IN x ch)
        (forall-guarded 'y '(IN y ch)
          '(OR (IN (LIST x y) porel) (IN (LIST y x) porel)))))))

;;; IS-UPPER-BOUND(grd, porel, ch, b): b in grd dominates every element of ch.
(def-predicate 'IS-UPPER-BOUND '(grd porel ch b)
  (conjuncts->and
    (list
      '(IN b grd)
      (forall-guarded 'x '(IN x ch) '(IN (LIST x b) porel)))))

;;; IS-MAXIMAL(grd, porel, mx): nothing in grd lies strictly above mx.
(def-predicate 'IS-MAXIMAL '(grd porel mx)
  (conjuncts->and
    (list
      '(IN mx grd)
      (forall-guarded 'y '(IN y grd)
        '(IMPLIES (IN (LIST mx y) porel) (IN (LIST y mx) porel))))))

;;; ZORN'S LEMMA is no longer stated here.  It was an asserted support warranted
;;; to Yosida, with a `rests-on' naming well-ordering-principle as the intended
;;; route.  It is now PROVEN, in theorem-library/zorn-route-two.scm, and by a
;;; different route: a strictly increasing transfinite tower ORD -> grd, which
;;; contradicts Burali-Forti.  Nothing well-orders grd, so the old rests-on was
;;; wrong as well as unnecessary.  The statement is the same formula, with the
;;; binders spelled w_ / ch_ / u_ / mx_ there.

;;; English readings.  A def-predicate cannot derive one (noun vs adjective), so
;;; the load-time gate ("every predicate in the library has an English reading",
;;; test-suite.scm:3211) counts a predicate without `notation!' as vocabulary rot.
;;; These four were on that list.
(notation! 'IS-PARTIAL-ORDER 'kind 'predicate 'arity 2
           'english "$2 partially orders $1")
(notation! 'IS-CHAIN         'kind 'predicate 'arity 3
           'english "$3 is a chain in $1 under $2")
(notation! 'IS-UPPER-BOUND   'kind 'predicate 'arity 4
           'english "$4 is an upper bound of $3 in $1 under $2")
(notation! 'IS-MAXIMAL       'kind 'predicate 'arity 3
           'english "$3 is maximal in $1 under $2")
