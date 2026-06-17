;;; ordinals.scm -- ordinal numbers: axioms, ordering, induction, recursion
;;;
;;; ORD is declared as a primitive class constant in theory.scm.
;;; IS-ORD predicate: (IS-ORD alpha) <-> (IN alpha ORD)
;;;
;;; New operators introduced here:
;;;   (<=_ORD alpha beta)      ordinal ≤ (total preorder on ORD)
;;;   (<_ORD  alpha beta)      ordinal < (strict)
;;;   (succ_ORD alpha)         ordinal successor of alpha
;;;   (LIMIT-ORD lambda)       predicate: limit ordinal
;;;   (ORD-SEGMENT alpha)      the set {beta : beta <_ORD alpha}
;;;   (SUP-ORD A)              least upper bound of a set A of ordinals

;;; -----------------------------------------------------------------------
;;; Burali-Forti: ORD is a proper class

(theory-add-axiom! *current-theory* 'burali-forti
  '(NOT (IN ORD SET)))

;;; -----------------------------------------------------------------------
;;; NN is a subset of ORD (finite ordinals are ordinals)

(theory-add-axiom! *current-theory* 'nn-subset-ord
  '(FORALL n (IMPLIES (IN n NN) (IN n ORD))))

;;; -----------------------------------------------------------------------
;;; Ordering: <=_ORD

;;; <=_ORD is only defined between ordinals
(theory-add-axiom! *current-theory* 'ord-le-closure
  '(FORALL alpha (FORALL beta
      (IMPLIES (<=_ORD alpha beta)
               (AND (IN alpha ORD) (IN beta ORD))))))

(theory-add-axiom! *current-theory* 'ord-le-refl
  '(FORALL alpha (IMPLIES (IN alpha ORD) (<=_ORD alpha alpha))))

(theory-add-axiom! *current-theory* 'ord-le-antisymm
  '(FORALL alpha (FORALL beta
      (IMPLIES (AND (<=_ORD alpha beta) (<=_ORD beta alpha))
               (= alpha beta)))))

(theory-add-axiom! *current-theory* 'ord-le-trans
  '(FORALL alpha (FORALL beta (FORALL gamma
      (IMPLIES (AND (<=_ORD alpha beta) (<=_ORD beta gamma))
               (<=_ORD alpha gamma))))))

(theory-add-axiom! *current-theory* 'ord-le-total
  '(FORALL alpha (FORALL beta
      (IMPLIES (AND (IN alpha ORD) (IN beta ORD))
               (OR (<=_ORD alpha beta) (<=_ORD beta alpha))))))

;;; 0 is the least ordinal (0 ∈ NN ⊆ ORD, so 0 ∈ ORD follows from nn-subset-ord + nn-zero-in)
(theory-add-axiom! *current-theory* 'ord-zero-least
  '(FORALL alpha (IMPLIES (IN alpha ORD) (<=_ORD 0 alpha))))

;;; -----------------------------------------------------------------------
;;; Strict ordering: <_ORD

(theory-add-axiom! *current-theory* 'ord-lt-iff
  '(FORALL alpha (FORALL beta
      (IFF (<_ORD alpha beta)
           (AND (<=_ORD alpha beta) (NOT (= alpha beta)))))))

;;; -----------------------------------------------------------------------
;;; Successor: succ_ORD

(theory-add-axiom! *current-theory* 'ord-succ-in
  '(FORALL alpha (IMPLIES (IN alpha ORD) (IN (succ_ORD alpha) ORD))))

;;; succ_ORD(alpha) is strictly above alpha
(theory-add-axiom! *current-theory* 'ord-succ-above
  '(FORALL alpha (IMPLIES (IN alpha ORD) (<_ORD alpha (succ_ORD alpha)))))

;;; succ_ORD(alpha) is the immediate successor: any ordinal > alpha is >= succ_ORD(alpha)
;;; Nested binary AND -- VNB's kernel uses binary-left/right (cadr/caddr) on
;;; AND, which silently drops the third conjunct on a flat (AND a b c).
(theory-add-axiom! *current-theory* 'ord-succ-immediate
  '(FORALL alpha (FORALL beta
      (IMPLIES (AND (IN alpha ORD) (AND (IN beta ORD) (<_ORD alpha beta)))
               (<=_ORD (succ_ORD alpha) beta)))))

;;; succ_ORD is injective
(theory-add-axiom! *current-theory* 'ord-succ-injective
  '(FORALL alpha (FORALL beta
      (IMPLIES (AND (IN alpha ORD) (AND (IN beta ORD)
                                         (= (succ_ORD alpha) (succ_ORD beta))))
               (= alpha beta)))))

;;; succ_ORD agrees with succ on NN
(theory-add-axiom! *current-theory* 'ord-succ-nn
  '(FORALL n (IMPLIES (IN n NN) (= (succ_ORD n) (succ n)))))

;;; <=_ORD restricted to NN matches numeric <=
(theory-add-axiom! *current-theory* 'ord-le-nn-compat
  '(FORALL m (FORALL n
      (IMPLIES (AND (IN m NN) (IN n NN))
               (IFF (<=_ORD m n) (<= m n))))))

;;; -----------------------------------------------------------------------
;;; Limit ordinals

;;; LIMIT-ORD(lambda): lambda is an ordinal that is neither 0 nor a successor
(theory-add-axiom! *current-theory* 'limit-ord-iff
  '(FORALL lambda
      (IFF (LIMIT-ORD lambda)
           (AND (IN lambda ORD)
                (AND (NOT (= lambda 0))
                     (NOT (FORSOME alpha
                             (AND (IN alpha ORD)
                                  (= lambda (succ_ORD alpha))))))))))

;;; -----------------------------------------------------------------------
;;; Initial segments: ORD-SEGMENT

;;; (ORD-SEGMENT alpha) is a set for every ordinal alpha
(theory-add-axiom! *current-theory* 'ord-segment-is-set
  '(FORALL alpha (IMPLIES (IN alpha ORD) (IN (ORD-SEGMENT alpha) SET))))

;;; Membership in ORD-SEGMENT: x ∈ ORD-SEGMENT(alpha) <-> x <_ORD alpha
(theory-add-axiom! *current-theory* 'ord-segment-membership
  '(FORALL alpha (FORALL x
      (IMPLIES (IN alpha ORD)
               (IFF (IN x (ORD-SEGMENT alpha))
                    (<_ORD x alpha))))))

;;; ORD-SEGMENT(0) = ∅
(theory-add-axiom! *current-theory* 'ord-segment-zero
  '(= (ORD-SEGMENT 0) EMPTY-SET))

;;; ORD-SEGMENT(succ_ORD(alpha)) = ORD-SEGMENT(alpha) ∪ {alpha}
(theory-add-axiom! *current-theory* 'ord-segment-succ
  '(FORALL alpha
      (IMPLIES (IN alpha ORD)
               (FORALL x
                 (IFF (IN x (ORD-SEGMENT (succ_ORD alpha)))
                      (OR (IN x (ORD-SEGMENT alpha))
                          (= x alpha)))))))

;;; For a limit ordinal, ORD-SEGMENT(lambda) = ∪ { ORD-SEGMENT(beta) : beta <_ORD lambda }
;;; (equivalently: x <_ORD lambda iff there exists beta <_ORD lambda with x <_ORD beta)
(theory-add-axiom! *current-theory* 'ord-segment-limit
  '(FORALL lambda
      (IMPLIES (LIMIT-ORD lambda)
               (FORALL x
                 (IMPLIES (<_ORD x lambda)
                          (FORSOME beta
                            (AND (<_ORD x beta) (<_ORD beta lambda))))))))

;;; -----------------------------------------------------------------------
;;; Supremum: SUP-ORD

;;; SUP-ORD(A) is an ordinal for any set of ordinals A
(theory-add-axiom! *current-theory* 'sup-ord-in
  '(FORALL A
      (IMPLIES (AND (IN A SET)
                    (FORALL x (IMPLIES (IN x A) (IN x ORD))))
               (IN (SUP-ORD A) ORD))))

;;; SUP-ORD(A) is an upper bound
(theory-add-axiom! *current-theory* 'sup-ord-upper
  '(FORALL A
      (IMPLIES (AND (IN A SET)
                    (FORALL x (IMPLIES (IN x A) (IN x ORD))))
               (FORALL alpha
                 (IMPLIES (IN alpha A)
                          (<=_ORD alpha (SUP-ORD A)))))))

;;; SUP-ORD(A) is the least upper bound
(theory-add-axiom! *current-theory* 'sup-ord-least
  '(FORALL A
      (IMPLIES (AND (IN A SET)
                    (FORALL x (IMPLIES (IN x A) (IN x ORD))))
               (FORALL beta
                 (IMPLIES (AND (IN beta ORD)
                               (FORALL alpha
                                 (IMPLIES (IN alpha A) (<=_ORD alpha beta))))
                          (<=_ORD (SUP-ORD A) beta))))))

;;; SUP-ORD(∅) = 0
(theory-add-axiom! *current-theory* 'sup-ord-empty
  '(= (SUP-ORD EMPTY-SET) 0))

;;; For a limit ordinal lambda, SUP-ORD(ORD-SEGMENT(lambda)) = lambda
(theory-add-axiom! *current-theory* 'limit-ord-is-sup
  '(FORALL lambda
      (IMPLIES (LIMIT-ORD lambda)
               (= (SUP-ORD (ORD-SEGMENT lambda)) lambda))))

;;; SUP-ORD(ORD-SEGMENT(succ_ORD(alpha))) = alpha  [the sup of {0..alpha} is alpha]
(theory-add-axiom! *current-theory* 'sup-ord-succ-segment
  '(FORALL alpha
      (IMPLIES (IN alpha ORD)
               (= (SUP-ORD (ORD-SEGMENT (succ_ORD alpha))) alpha))))

;;; -----------------------------------------------------------------------
;;; Transfinite induction schema
;;;
;;; Strong (complete) form: if P(alpha) holds whenever P(beta) holds for
;;; all beta <_ORD alpha, then P holds everywhere on ORD.
;;;
;;; In VNB (with class comprehension), this is a single axiom quantifying
;;; over classes C.  We state it in the class form.

(theory-add-axiom! *current-theory* 'transfinite-induction
  '(FORALL C
      (IMPLIES
        (FORALL alpha
          (IMPLIES
            (AND (IN alpha ORD)
                 (FORALL beta (IMPLIES (<_ORD beta alpha) (IN beta C))))
            (IN alpha C)))
        (FORALL alpha
          (IMPLIES (IN alpha ORD) (IN alpha C))))))

;;; -----------------------------------------------------------------------
;;; Well-ordering of ORD.  Every nonempty subclass A of ORD has a <=_ORD-
;;; least element.  This is the order-theoretic face of transfinite-induction
;;; above: instantiate that schema with C = { a : a not in A }; if A had no
;;; least element, totality (ord-le-total) makes every a with all smaller
;;; ordinals outside A itself outside A, so C = ORD and A is empty.  Asserted
;;; here as the canonical home of the well-ordering principle so downstream
;;; results (e.g. nn-least-element) DERIVE it rather than re-assert a bespoke
;;; copy.  [[feedback-library-axioms-fine]] [[feedback-warrants]]
;; Bound vars are case-fold-distinct (cl/w/x/m/k): the reader folds A and a
;; to one identifier, so an `A'/`a' pairing would capture.  [[feedback-no-case-variant-binders]]
(support 'ord-well-ordered
  '(FORALL cl
     (IMPLIES (AND (FORALL x (IMPLIES (IN x cl) (IN x ORD)))
                   (FORSOME w (IN w cl)))
       (FORSOME m (AND (IN m cl)
                       (FORALL k (IMPLIES (IN k cl) (<=_ORD m k))))))))
(warrant! 'ord-well-ordered 'proof
  "Classically equivalent to the transfinite-induction axiom already assumed: a nonempty subclass A of ORD with no <=_ORD-least element gives, via transfinite induction on P(a) = (a not in A) using totality of <=_ORD, that A is empty -- a contradiction.")

;;; -----------------------------------------------------------------------
;;; Transfinite recursion (axiom schema)
;;;
;;; The three-case form is most convenient for defining functions on ORD:
;;;
;;;   (1) F(0)             = z
;;;   (2) F(succ_ORD(a))   = G(a, F(a))         for all a ∈ ORD
;;;   (3) F(lim)           = H(lim, ORD-SEGMENT) for all limit lim
;;;
;;; Rather than axiomatising the abstract recursion theorem (which would
;;; require higher-order quantification), we provide a Scheme helper that
;;; installs the three defining equations as named axioms for any concrete
;;; function F.  Soundness rests on the transfinite recursion theorem of
;;; VNB set theory; we treat it as an admissible definition principle.

(define (symbol-append . syms)
  (string->symbol (apply string-append (map symbol->string syms))))

;;; (def-by-ord-recursion f-name params base-val succ-spec succ-expr lim-spec lim-expr)
;;;
;;; f-name     : symbol      -- the function constant being defined
;;; params     : (p1 p2 ...) -- extra parameters carried alongside the
;;;                             ordinal; '() for a plain ORD->A function.
;;;                             Mirrors def-by-nn-recursion.
;;; base-val   : S-expression -- value of (f-name p1 p2 ... 0)
;;; succ-spec  : (alpha val)  -- variables for successor step
;;; succ-expr  : S-expression -- value of (f-name p1 p2 ... (succ_ORD alpha)) in
;;;                              terms of p1..., alpha ∈ ORD, and
;;;                              val = (f-name p1... alpha)
;;; lim-spec   : (lambda) -- variable for limit step
;;; lim-expr   : S-expression -- value of (f-name p1 p2 ... lambda) in terms of
;;;                              p1..., lambda (a limit ordinal), and
;;;                              free uses of f-name (which must be written
;;;                              including the parameters, e.g. (f-name p1... beta))
;;;
;;; Installs three characterising axioms, each wrapped in FORALL over the
;;; parameters p1, p2, ...:
;;;   {f-name}-zero : forall p1.... (= (f-name p1... 0) base-val)
;;;   {f-name}-succ : forall p1.... FORALL alpha (IMPLIES (IN alpha ORD)
;;;                     (= (f-name p1... (succ_ORD alpha))
;;;                        succ-expr[val := (f-name p1... alpha)]))
;;;   {f-name}-limit: forall p1.... FORALL lambda (IMPLIES (LIMIT-ORD lambda)
;;;                     (= (f-name p1... lambda) lim-expr))

(define (def-by-ord-recursion f-name params base-val succ-spec succ-expr lim-spec lim-expr)
  (let* ((alpha     (car  succ-spec))
         (val       (cadr succ-spec))
         (lam       (car  lim-spec))
         (succ-body (subst-free val `(,f-name ,@params ,alpha) succ-expr))
         (zero-name (symbol-append f-name '-zero))
         (succ-name (symbol-append f-name '-succ))
         (lim-name  (symbol-append f-name '-limit))
         (zero-core `(= (,f-name ,@params 0) ,base-val))
         (succ-core `(FORALL ,alpha
                       (IMPLIES (IN ,alpha ORD)
                                (= (,f-name ,@params (succ_ORD ,alpha)) ,succ-body))))
         (lim-core  `(FORALL ,lam
                       (IMPLIES (LIMIT-ORD ,lam)
                                (= (,f-name ,@params ,lam) ,lim-expr))))
         (wrap      (lambda (f) (fold-right (lambda (p g) `(FORALL ,p ,g)) f params))))
    (theory-add-definition! *current-theory* f-name
      (list (cons zero-name (wrap zero-core))
            (cons succ-name (wrap succ-core))
            (cons lim-name  (wrap lim-core))))))

;;; -----------------------------------------------------------------------
;;; Primitive recursion on NN  (NN = {0, 1, 2, ...})
;;;
;;; (def-by-nn-recursion f-name params base-val succ-spec succ-expr)
;;;
;;; f-name    : symbol      -- the function constant being defined
;;; params    : (p1 p2 ...) -- extra parameters; '() for a plain NN→A function
;;; base-val  : S-expression -- value of (f-name p1 p2 ... 0)
;;; succ-spec : (n val)     -- variables for the step
;;; succ-expr : S-expression -- value of (f-name p1 p2 ... (succ n))
;;;                            in terms of p1..., n ∈ NN, val = (f-name p1... n)
;;;
;;; Installs two characterising axioms:
;;;   {f-name}-zero : forall p1....(= (f-name p1... 0) base-val)
;;;   {f-name}-succ : forall p1... n∈NN. (= (f-name p1... (succ n))
;;;                                          succ-expr[val := (f-name p1... n)])

(define (def-by-nn-recursion f-name params base-val succ-spec succ-expr)
  (let* ((n         (car  succ-spec))
         (val       (cadr succ-spec))
         (succ-body (subst-free val `(,f-name ,@params ,n) succ-expr))
         (zero-name (symbol-append f-name '-zero))
         (succ-name (symbol-append f-name '-succ))
         (zero-core `(= (,f-name ,@params 0) ,base-val))
         (succ-core `(FORALL ,n
                       (IMPLIES (IN ,n NN)
                                (= (,f-name ,@params (succ ,n)) ,succ-body))))
         (wrap      (lambda (f) (fold-right (lambda (p g) `(FORALL ,p ,g)) f params))))
    (theory-add-definition! *current-theory* f-name
      (list (cons zero-name (wrap zero-core))
            (cons succ-name (wrap succ-core))))))
