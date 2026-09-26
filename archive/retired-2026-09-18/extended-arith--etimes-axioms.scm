(fluid-let ((*current-provenance* 'definitional))

  ;; Finite case: on the reals, etimes agrees with ordinary multiplication.
  ;; Guarded exactly as `eplus-real' is -- on membership in RR, which already
  ;; excludes POS-INF.
  (theory-add-axiom! *current-theory* 'etimes-real
    (forall-guarded '(x y) '((IN x RR) (IN y RR))
      '(= (etimes x y) (bintimes x y))))

  ;; The two 0 * inf cases.
  (theory-add-axiom! *current-theory* 'etimes-zero-pos-inf
    '(= (etimes 0 POS-INF) 0))

  (theory-add-axiom! *current-theory* 'etimes-pos-inf-zero
    '(= (etimes POS-INF 0) 0))

  ;; Left-absorbing on the nonzero part: POS-INF times anything but 0 is POS-INF.
  (theory-add-axiom! *current-theory* 'etimes-pos-inf-left
    (forall-guarded '(y) '((IN y RR-POS-STAR) (NOT (= y 0)))
      '(= (etimes POS-INF y) POS-INF)))

  ;; Right-absorbing on the nonzero part.
  (theory-add-axiom! *current-theory* 'etimes-pos-inf-right
    (forall-guarded '(x) '((IN x RR-POS-STAR) (NOT (= x 0)))
      '(= (etimes x POS-INF) POS-INF))))

;;; Closure / totality -- a sethood-and-totality claim, not a defining
;;; equation, so it sits outside the definitional block and is warranted on
;;; its own, as eplus-in-fun is in extended-reals-pos.scm.
(theory-add-axiom! *current-theory* 'etimes-in-fun
  '(IN etimes (FUN (CARTESIAN RR-POS-STAR RR-POS-STAR) RR-POS-STAR)))

(warrant! 'etimes-in-fun 'well-known
  "Extended multiplication is total on [0,+inf]: the five defining clauses
   above cover RR-POS-STAR x RR-POS-STAR exhaustively and land in RR-POS-STAR in every case (a
   product of nonnegative reals is a nonnegative real; the remaining values
   are 0 and POS-INF, both in RR-POS-STAR by zero-in-rr-pos-star and
   pos-inf-in-rr-pos-star).  Stated as a FUN membership, hence also asserting
   that the graph is a set -- exactly as eplus-in-fun does for extended
   addition in extended-reals-pos.scm, and accepted on the same grounds.")