;;; number-systems.scm -- number system constants and axioms
;;;
;;; NN : natural numbers (0, 1, 2, ...)
;;; ZZ : integers
;;; QQ : rationals
;;; RR : reals
;;; CC : complex numbers
;;;
;;; Inclusion chain: NN ⊆ ZZ ⊆ QQ ⊆ RR ⊆ CC
;;;
;;; Single arithmetic operators across all systems:
;;;   +  *  -  recip  abs  conjugate  succ  <=
;;; Numeric literals 0, 1, 2, ... and -1, -2, ... are constants in ZZ
;;; (non-negative literals also in NN via nn-subset-zz and closure axioms)

;;; -----------------------------------------------------------------------
;;; Sethood

(theory-add-axiom! *current-theory* 'nn-is-set      '(IN NN SET))
(theory-add-axiom! *current-theory* 'zz-is-set      '(IN ZZ SET))
(theory-add-axiom! *current-theory* 'qq-is-set      '(IN QQ SET))
(theory-add-axiom! *current-theory* 'rr-is-set      '(IN RR SET))
(theory-add-axiom! *current-theory* 'cc-is-set      '(IN CC SET))

;;; -----------------------------------------------------------------------
;;; Inclusion chain

(theory-add-axiom! *current-theory* 'nn-subset-zz
  '(FORALL n (IMPLIES (IN n NN) (IN n ZZ))))

(theory-add-axiom! *current-theory* 'zz-subset-qq
  '(FORALL n (IMPLIES (IN n ZZ) (IN n QQ))))

(theory-add-axiom! *current-theory* 'qq-subset-rr
  '(FORALL n (IMPLIES (IN n QQ) (IN n RR))))

(theory-add-axiom! *current-theory* 'rr-subset-cc
  '(FORALL n (IMPLIES (IN n RR) (IN n CC))))

;;; -----------------------------------------------------------------------
;;; NN — natural numbers (0, 1, 2, ...)

(theory-add-axiom! *current-theory* 'nn-zero-in '(IN 0 NN))

(theory-add-axiom! *current-theory* 'nn-succ-closed
  '(FORALL n (IMPLIES (IN n NN) (IN (succ n) NN))))

(theory-add-axiom! *current-theory* 'nn-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (IN (+ a b) NN)))))

(theory-add-axiom! *current-theory* 'nn-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (IN (* a b) NN)))))

(theory-add-axiom! *current-theory* 'nn-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'nn-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a NN) (IN b NN))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'nn-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a NN) (AND (IN b NN) (IN c NN)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'nn-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a NN) (AND (IN b NN) (IN c NN)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'nn-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a NN) (AND (IN b NN) (IN c NN)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'nn-one-mul
  '(FORALL a (IMPLIES (IN a NN) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'nn-add-zero
  '(FORALL a (IMPLIES (IN a NN) (= (+ a 0) a))))

;;; NN induction schema (class form).
;;; For any class C: if 0 ∈ C and (∀n∈NN. n∈C → succ(n)∈C) then ∀n∈NN. n∈C.
;;; Follows from transfinite-induction (ordinals.scm) + NN ⊆ ORD + 0 ∈ NN
;;; + nn-succ-closed; stated here as a named axiom for direct use.
(theory-add-axiom! *current-theory* 'nn-induction
  '(FORALL C
      (IMPLIES (AND (IN 0 C)
                    (FORALL n (IMPLIES (AND (IN n NN) (IN n C))
                                       (IN (succ n) C))))
               (FORALL n (IMPLIES (IN n NN) (IN n C))))))

;;; -----------------------------------------------------------------------
;;; ZZ — integers (ring)

(theory-add-axiom! *current-theory* 'zz-zero-in '(IN 0 ZZ))
(theory-add-axiom! *current-theory* 'zz-one-in  '(IN 1 ZZ))

(theory-add-axiom! *current-theory* 'zz-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (IN (+ a b) ZZ)))))

(theory-add-axiom! *current-theory* 'zz-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (IN (* a b) ZZ)))))

(theory-add-axiom! *current-theory* 'zz-neg-closed
  '(FORALL a (IMPLIES (IN a ZZ) (IN (- a) ZZ))))

(theory-add-axiom! *current-theory* 'zz-add-zero
  '(FORALL a (IMPLIES (IN a ZZ) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'zz-neg-inverse
  '(FORALL a (IMPLIES (IN a ZZ) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'zz-one-mul
  '(FORALL a (IMPLIES (IN a ZZ) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'zz-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'zz-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a ZZ) (IN b ZZ))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'zz-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a ZZ) (AND (IN b ZZ) (IN c ZZ)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'zz-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a ZZ) (AND (IN b ZZ) (IN c ZZ)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'zz-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a ZZ) (AND (IN b ZZ) (IN c ZZ)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

;;; -----------------------------------------------------------------------
;;; QQ — rationals (ordered field)

(theory-add-axiom! *current-theory* 'qq-zero-in '(IN 0 QQ))
(theory-add-axiom! *current-theory* 'qq-one-in  '(IN 1 QQ))

(theory-add-axiom! *current-theory* 'qq-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (IN (+ a b) QQ)))))

(theory-add-axiom! *current-theory* 'qq-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (IN (* a b) QQ)))))

(theory-add-axiom! *current-theory* 'qq-neg-closed
  '(FORALL a (IMPLIES (IN a QQ) (IN (- a) QQ))))

(theory-add-axiom! *current-theory* 'qq-add-zero
  '(FORALL a (IMPLIES (IN a QQ) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'qq-neg-inverse
  '(FORALL a (IMPLIES (IN a QQ) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'qq-one-mul
  '(FORALL a (IMPLIES (IN a QQ) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'qq-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'qq-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a QQ) (IN b QQ))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'qq-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a QQ) (AND (IN b QQ) (IN c QQ)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'qq-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a QQ) (AND (IN b QQ) (IN c QQ)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'qq-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a QQ) (AND (IN b QQ) (IN c QQ)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'qq-recip-closed
  '(FORALL a
      (IMPLIES (AND (IN a QQ) (NOT (= a 0)))
               (IN (recip a) QQ))))

(theory-add-axiom! *current-theory* 'qq-recip-inverse
  '(FORALL a
      (IMPLIES (AND (IN a QQ) (NOT (= a 0)))
               (= (* a (recip a)) 1))))

;;; -----------------------------------------------------------------------
;;; RR — reals (complete ordered field)

(theory-add-axiom! *current-theory* 'rr-zero-in '(IN 0 RR))
(theory-add-axiom! *current-theory* 'rr-one-in  '(IN 1 RR))

(theory-add-axiom! *current-theory* 'rr-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IN (+ a b) RR)))))

(theory-add-axiom! *current-theory* 'rr-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IN (* a b) RR)))))

(theory-add-axiom! *current-theory* 'rr-neg-closed
  '(FORALL a (IMPLIES (IN a RR) (IN (- a) RR))))

(theory-add-axiom! *current-theory* 'rr-add-zero
  '(FORALL a (IMPLIES (IN a RR) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'rr-neg-inverse
  '(FORALL a (IMPLIES (IN a RR) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'rr-one-mul
  '(FORALL a (IMPLIES (IN a RR) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'rr-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'rr-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'rr-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'rr-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'rr-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'rr-recip-closed
  '(FORALL a
      (IMPLIES (AND (IN a RR) (NOT (= a 0)))
               (IN (recip a) RR))))

(theory-add-axiom! *current-theory* 'rr-recip-inverse
  '(FORALL a
      (IMPLIES (AND (IN a RR) (NOT (= a 0)))
               (= (* a (recip a)) 1))))

;;; Order: <= is the numeric order on the real chain (NN/ZZ/QQ/RR/RR*).
;;; A total order compatible with the field operations.  Stated guarded by
;;; (IN _ RR); because the inclusions NN<=ZZ<=QQ<=RR are genuine set
;;; inclusions, these axioms also govern <= on the integers and rationals.
;;; The ordinal order is a separate relation <=_ORD (ordinals.scm), bridged
;;; to <= on NN, so nothing here leaks onto it; CC carries no <=.

(theory-add-axiom! *current-theory* 'rr-leq-reflexive
  '(FORALL a (IMPLIES (IN a RR) (<= a a))))

(theory-add-axiom! *current-theory* 'rr-leq-antisymmetric
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IMPLIES (AND (<= a b) (<= b a)) (= a b))))))

(theory-add-axiom! *current-theory* 'rr-leq-transitive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (IMPLIES (AND (<= a b) (<= b c)) (<= a c)))))))

(theory-add-axiom! *current-theory* 'rr-leq-total
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (OR (<= a b) (<= b a))))))

(theory-add-axiom! *current-theory* 'rr-leq-add-compat
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (IMPLIES (<= a b) (<= (+ a c) (+ b c))))))))

(theory-add-axiom! *current-theory* 'rr-leq-mul-nonneg
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IMPLIES (AND (<= 0 a) (<= 0 b)) (<= 0 (* a b)))))))

(theory-add-axiom! *current-theory* 'rr-abs-closed
  '(FORALL a (IMPLIES (IN a RR) (IN (abs a) RR))))

(theory-add-axiom! *current-theory* 'rr-abs-nonneg
  '(FORALL a (IMPLIES (IN a RR) (<= 0 (abs a)))))

(theory-add-axiom! *current-theory* 'rr-abs-zero
  '(FORALL a (IMPLIES (IN a RR) (IFF (= (abs a) 0) (= a 0)))))

(theory-add-axiom! *current-theory* 'rr-abs-triangle
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (<= (abs (+ a b))
                   (+ (abs a) (abs b)))))))

;;; Multiplicativity of abs -- the conjunct that `is-norm' (hence
;;; `rr-is-normed-field') needs for NRM = abs on RR-NORMED-FIELD.
(theory-add-axiom! *current-theory* 'rr-abs-mult
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (= (abs (* a b)) (* (abs a) (abs b)))))))

;;; -----------------------------------------------------------------------
;;; CC — complex numbers (field)

(theory-add-axiom! *current-theory* 'cc-zero-in '(IN 0 CC))
(theory-add-axiom! *current-theory* 'cc-one-in  '(IN 1 CC))

(theory-add-axiom! *current-theory* 'cc-add-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (IN (+ a b) CC)))))

(theory-add-axiom! *current-theory* 'cc-mul-closed
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (IN (* a b) CC)))))

(theory-add-axiom! *current-theory* 'cc-neg-closed
  '(FORALL a (IMPLIES (IN a CC) (IN (- a) CC))))

(theory-add-axiom! *current-theory* 'cc-add-zero
  '(FORALL a (IMPLIES (IN a CC) (= (+ a 0) a))))

(theory-add-axiom! *current-theory* 'cc-neg-inverse
  '(FORALL a (IMPLIES (IN a CC) (= (+ a (- a)) 0))))

(theory-add-axiom! *current-theory* 'cc-one-mul
  '(FORALL a (IMPLIES (IN a CC) (= (* 1 a) a))))

(theory-add-axiom! *current-theory* 'cc-add-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (+ a b) (+ b a))))))

(theory-add-axiom! *current-theory* 'cc-mul-comm
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (* a b) (* b a))))))

(theory-add-axiom! *current-theory* 'cc-add-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a CC) (AND (IN b CC) (IN c CC)))
               (= (+ (+ a b) c) (+ a (+ b c))))))))

(theory-add-axiom! *current-theory* 'cc-mul-assoc
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a CC) (AND (IN b CC) (IN c CC)))
               (= (* (* a b) c) (* a (* b c))))))))

(theory-add-axiom! *current-theory* 'cc-distributive
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a CC) (AND (IN b CC) (IN c CC)))
               (= (* a (+ b c))
                  (+ (* a b) (* a c))))))))

(theory-add-axiom! *current-theory* 'cc-recip-closed
  '(FORALL a
      (IMPLIES (AND (IN a CC) (NOT (= a 0)))
               (IN (recip a) CC))))

(theory-add-axiom! *current-theory* 'cc-recip-inverse
  '(FORALL a
      (IMPLIES (AND (IN a CC) (NOT (= a 0)))
               (= (* a (recip a)) 1))))

(theory-add-axiom! *current-theory* 'cc-conjugate-closed
  '(FORALL a (IMPLIES (IN a CC) (IN (conjugate a) CC))))

(theory-add-axiom! *current-theory* 'cc-conjugate-involution
  '(FORALL a (IMPLIES (IN a CC) (= (conjugate (conjugate a)) a))))

(theory-add-axiom! *current-theory* 'cc-conjugate-add
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (conjugate (+ a b))
                  (+ (conjugate a) (conjugate b)))))))

(theory-add-axiom! *current-theory* 'cc-conjugate-mul
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (conjugate (* a b))
                  (* (conjugate a) (conjugate b)))))))

(theory-add-axiom! *current-theory* 'cc-self-conj-real
  '(FORALL a (IMPLIES (IN a CC) (IN (* a (conjugate a)) RR))))

;; The product a * conjugate(a) is real (cc-self-conj-real); the inequality
;; lives in RR, where <= is the standard real order.
(theory-add-axiom! *current-theory* 'cc-self-conj-nonneg
  '(FORALL a (IMPLIES (IN a CC)
                      (AND (IN (* a (conjugate a)) RR)
                           (<= 0 (* a (conjugate a)))))))

;;; -----------------------------------------------------------------------
;;; magnitude : CC -> RR  (complex modulus)
;;;
;;; For reals, magnitude coincides with abs.
;;; These are the standard norm axioms for the complex absolute value.

(theory-add-axiom! *current-theory* 'cc-magnitude-closed
  '(FORALL z (IMPLIES (IN z CC) (IN (magnitude z) RR))))

(theory-add-axiom! *current-theory* 'cc-magnitude-nonneg
  '(FORALL z (IMPLIES (IN z CC) (<= 0 (magnitude z)))))

(theory-add-axiom! *current-theory* 'cc-magnitude-zero-iff
  '(FORALL z (IMPLIES (IN z CC)
               (IFF (= (magnitude z) 0) (= z 0)))))

(theory-add-axiom! *current-theory* 'cc-magnitude-neg
  '(FORALL z (IMPLIES (IN z CC)
               (= (magnitude (- z)) (magnitude z)))))

(theory-add-axiom! *current-theory* 'cc-magnitude-mul
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (= (magnitude (* a b))
                  (* (magnitude a) (magnitude b)))))))

(theory-add-axiom! *current-theory* 'cc-magnitude-triangle
  '(FORALL a (FORALL b
      (IMPLIES (AND (IN a CC) (IN b CC))
               (<= (magnitude (+ a b))
                   (+ (magnitude a) (magnitude b)))))))

(theory-add-axiom! *current-theory* 'rr-magnitude-is-abs
  '(FORALL a (IMPLIES (IN a RR) (= (magnitude a) (abs a)))))

;;; -----------------------------------------------------------------------
;;; Exponentiation
;;;
;;; power : (CARTESIAN CC NN) -> CC                    (total on NN)
;;; (power x 0)   = 1                                  (n = 0)
;;; (power x n+1) = (* x (power x n))                  (n ∈ NN)
;;; (power x -n)  = (recip (power x n))                (n ∈ NN, x ≠ 0; conditional, not a FUN typing)

;; Total typing on natural number exponents.  Stated as a closure axiom
;; in 2-argument-application form to match the recursion equations below
;; and the user-facing syntax `(power x n)`.  An earlier form
;;   (IN power (FUN (CARTESIAN CC NN) CC))
;; mismatched the application form: it suggested `power` applied to a
;; single CARTESIAN pair, while the system uses `(power x n)` directly.
(theory-add-axiom! *current-theory* 'power-typing-nonneg
  '(FORALL x (FORALL n
      (IMPLIES (AND (IN x CC) (IN n NN))
               (IN (power x n) CC)))))

(theory-add-axiom! *current-theory* 'power-zero
  '(FORALL x (IMPLIES (IN x CC) (= (power x 0) 1))))

(theory-add-axiom! *current-theory* 'power-succ
  '(FORALL x (FORALL n
      (IMPLIES (AND (IN x CC) (IN n NN))
               (= (power x (succ n))
                  (* x (power x n)))))))

(theory-add-axiom! *current-theory* 'power-neg
  '(FORALL x (FORALL n
      (IMPLIES (AND (IN x CC) (IN n NN) (NOT (= x 0)))
               (= (power x (- n))
                  (recip (power x n)))))))
