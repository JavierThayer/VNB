;;; card-defined.scm -- CARD, cardinality DEFINED rather than axiomatised.
;;;
;;;     CARD(A)  ==  IOTA alpha.  alpha in ORD
;;;                     and  forsome phi. phi in BIJECTION(A, S(alpha))
;;;                     and  forall beta with ORD-LT(beta, alpha).
;;;                            not forsome psi. psi in BIJECTION(A, S(beta))
;;;
;;; "the least ordinal whose segment A bijects onto" -- the meaning
;;; cardinality.scm's own header has always stated.  The definition itself is
;;; installed there; this file starts the proofs.
;;;
;;; HISTORY.  From 2026-08-05 to 2026-09-19 the defined constant was built here
;;; under the companion name CARD-STAR, because CARD cannot be both axiomatised
;;; and defined: the moment it has a definition, cardinality.scm's `primitive'
;;; axioms stop being a joint implicit definition and become claims that could
;;; be FALSE.  On 2026-09-20 the user made the swap -- the axioms were deleted,
;;; every one of them having been proven, and the companion took the name CARD
;;; (docs/card-defined-2026-09-20.md).
;;;
;;; THE DIRECTION OF THE BIJECTION IS A -> SEGMENT, and that is a decision, not
;;; a coin flip (user, 2026-08-05).  For A = S(n), killing a candidate beta < n
;;; then means refuting a bijection S(n) -> S(beta), which is IN PARTICULAR an
;;; injection S(n) -> S(beta) -- pigeonhole-segments-gen, applied directly.
;;; Segment-first would instead need the bijection INVERTED, and the library's
;;; only inverse, INVERSE-BIJ (bijection.scm), is defined via CHOICE, which this
;;; track is meant not to need.
;;;
;;; WHAT IS PROVEN HERE
;;;   cd-body-unique   the description pins at most one ordinal   (leastness
;;;                    both ways, then ordinal totality + antisymmetry)
;;;   cd-seg-body      n itself satisfies the description at A = S(n)
;;;                    (identity bijection for existence, pigeonhole for
;;;                    leastness) -- this is where the mathematics is
;;;   card-segment     CARD(S(n)) = n
;;;
;;; card-segment is the keystone: it is what used to be the axiom of that name,
;;; and proving it is what checks that the description says what it should.
;;;
;;; Needs pigeonhole-segments-gen, the segment/arithmetic bridges, bijection-
;;; derived (the three projections) and bijection-identity (now guarded on
;;; sethood, and this file is its first consumer).

;;; --------------------------------------------------------------------
;;; The definition is in structure-library/cardinality.scm (position 82), where
;;; CARD has always been introduced; it moved there on 2026-09-20 when the
;;; axioms it replaces were deleted.  This file proves the description's
;;; uniqueness and `card-segment'.
;;; --------------------------------------------------------------------

;;; the description's body, at an arbitrary class and ordinal -- written once,
;;; since three proofs below quantify over it.
(define (cd-body A al)
  (list 'AND (list 'IN al 'ORD)
    (list 'AND (list 'FORSOME 'phi (list 'IN 'phi (list 'BIJECTION A (list 'ORD-SEGMENT al))))
      (list 'FORALL 'beta
        (list 'IMPLIES (list 'ORD-LT 'beta al)
          (list 'NOT (list 'FORSOME 'psi
                       (list 'IN 'psi (list 'BIJECTION A (list 'ORD-SEGMENT 'beta))))))))))

(define (cd-first h)
  (let ((fs (filter (dk-head? h) (dk-asms))))
    (if (null? fs) (error "cd-first: nothing with head" h) (car fs))))
(define (cd-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop))))))

;;; --------------------------------------------------------------------
;;; cd-body-unique: the description pins AT MOST ONE ordinal.
;;;
;;; No composition of bijections is needed, which is the point of building
;;; leastness into the description: if be were BELOW al, al's own leastness
;;; clause would forbid the bijection be's existence clause supplies.  So
;;; neither is below the other, and ordinal totality closes it.
;;; --------------------------------------------------------------------

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'al (list 'FORALL 'be
      (list 'IMPLIES (cd-body 'a_ 'al)
        (list 'IMPLIES (cd-body 'a_ 'be) (list '= 'al 'be))))))))
(cd-peel!)
(define cd-u-al (dk-split! (cd-body 'a_ 'al)))
(define cd-u-be (dk-split! (cd-body 'a_ 'be)))
(define cd-al-least (car (filter (dk-head? 'FORALL)  cd-u-al)))
(define cd-be-least (car (filter (dk-head? 'FORALL)  cd-u-be)))
(define cd-al-ex    (car (filter (dk-head? 'FORSOME) cd-u-al)))
(define cd-be-ex    (car (filter (dk-head? 'FORSOME) cd-u-be)))

;;; neither is strictly below the other: HIGH's leastness clause, instantiated
;;; at LOW, is the negation of LOW's own existence clause.  The clauses are
;;; taken from what dk-split! returned, not searched for by shape.
(define (cd-not-below! low high least-of-high)
  (have! (list 'NOT (list 'ORD-LT low high))
         (lambda ()
           (di)
           (ai (dk-deepest (lambda () (inst+ least-of-high low)))))))
(cd-not-below! 'be 'al cd-al-least)
(cd-not-below! 'al 'be cd-be-least)

;;; ... so they are equal: totality gives one of the two <=, and each of them
;;; with the corresponding NOT (ORD-LT ...) forces equality through ord-lt-iff.
(have! '(AND (IN al ORD) (IN be ORD)))
(fact 'ord-le-total 'al 'be)
(use-cases (list '(ORD-LE al be) '(ORD-LE be al))
  (lambda ()
    (use-em '(= al be)
      (lambda () (ass))
      (lambda ()
        (have! '(ORD-LT al be) (lambda () (mac 'ord-lt-iff) (from-context!)))
        (ai '(NOT (ORD-LT al be))))))
  (lambda ()
    (use-em '(= al be)
      (lambda () (ass))
      (lambda ()
        (fact 'neq-sym 'al 'be)
        (have! '(ORD-LT be al) (lambda () (mac 'ord-lt-iff) (from-context!)))
        (ai '(NOT (ORD-LT be al)))))))
(qed 'cd-body-unique)
(topic! 'cd-body-unique 'set-theory)

;;; --------------------------------------------------------------------
;;; cd-seg-body: n satisfies the description at A = S(n).
;;;
;;; Existence is the identity bijection (bijection-identity, at the SET S(n)).
;;; Leastness is pigeonhole: a bijection S(n) -> S(beta) with beta < n is in
;;; particular an INJECTION, and pigeonhole-segments-gen forbids exactly that.
;;; --------------------------------------------------------------------

;;; The goal is a right-nested AND, and `di' splits ONE level per call, so the
;;; leaf walker recurses rather than assuming three leaves appear at once.
(define (cd-close-body!)
  (let ((g (dk-goal)))
    (cond
      ((eq? (car g) 'AND)
       (for-each (lambda (l) (dk-focus! l) (cd-close-body!))
                 (dk-opened (lambda () (di)))))
      ;; n in ORD
      ((eq? (car g) 'IN) (ass))
      ;; existence: the identity bijection on the SET S(n)
      ((eq? (car g) 'FORSOME)
       (fact 'bijection-identity '(ORD-SEGMENT n_))
       (ew '(VNB-LAMBDA x_ (ORD-SEGMENT n_) x_))
       (ass))
      ;; leastness: a bijection S(n) -> S(beta) with beta < n is an INJECTION,
      ;; and pigeonhole-segments-gen forbids exactly that
      (else
       (cd-peel!)                        ; beta, beta ORD-LT n_, and the FORSOME
       (ai (cd-first 'FORSOME))          ; ... opened: psi0 in BIJECTION(S n, S beta)
       (let* ((bij (car (filter (lambda (f)
                                  (and (pair? f) (eq? (car f) 'IN)
                                       (pair? (caddr f))
                                       (eq? (car (caddr f)) 'BIJECTION)))
                                (dk-asms))))
              (psi0 (cadr bij))
              (bet  (cadr (caddr (caddr bij)))))
         (have! (list 'IN bet '(ORD-SEGMENT n_))
                (lambda () (mac 'ord-segment-membership) (ass)))
         (fact 'ord-segment-nn-subset 'n_ bet)
         ;; seg-mem-lt rewrites membership -> inequality, so it goes on the
         ;; HYPOTHESIS: as a goal macete it would need the -rev companion.
         (mac-h 'seg-mem-lt (list 'IN bet '(ORD-SEGMENT n_)))
         (have! (list 'IN psi0 (list 'INJECTION '(ORD-SEGMENT n_) (list 'ORD-SEGMENT bet)))
                (lambda ()
                  (mac 'injection-membership-iff)
                  (fact 'bijection-in-fun '(ORD-SEGMENT n_) (list 'ORD-SEGMENT bet) psi0)
                  (fact 'bijection-injective '(ORD-SEGMENT n_) (list 'ORD-SEGMENT bet) psi0)
                  (from-context!)))
         (dk-fact! 'pigeonhole-segments-gen 'n_ bet psi0)
         (ai (list 'NOT (list 'IN psi0
                              (list 'INJECTION '(ORD-SEGMENT n_)
                                    (list 'ORD-SEGMENT bet))))))))))

(sp (make-wff (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                                      (cd-body '(ORD-SEGMENT n_) 'n_)))))
(di)
(fact 'nn-subset-ord 'n_)
(fact 'ord-segment-is-set 'n_)
(cd-close-body!)
(qed 'cd-seg-body)
(topic! 'cd-seg-body 'set-theory)

;;; --------------------------------------------------------------------
;;; card-segment:  CARD(S(n)) = n.
;;;
;;; `iota-d' posts existence-and-uniqueness (n is the witness, cd-body-unique
;;; the uniqueness) and hands back the defining property; cd-body-unique then
;;; identifies the described ordinal with n.
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
                 (= (CARD (ORD-SEGMENT n_)) n_)))))
(di)
(mac 'CARD)
(define cd-io (cadr (dk-goal)))          ; the IOTA term, as the engine built it
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'FORSOME)
       ;; existence and uniqueness
       (begin
         (ew 'n_)
         (fact 'cd-seg-body 'n_)
         (for-each
          (lambda (m)
            (dk-focus! m)
            (if (eq? (car (dk-goal)) 'FORALL)
                (begin
                  (cd-peel!)
                  (let ((y (caddr (dk-goal))))          ; goal (= n_ y)
                    (fact 'cd-body-unique '(ORD-SEGMENT n_) 'n_ y)
                    (ass)))
                (ass)))
          (dk-opened (lambda () (di)))))
       ;; the defining property, against cd-seg-body
       (begin
         ;; 2026-09-18 (LUTINS instantiation): cd-body-unique is cited at the
         ;; IOTA term, which is never certified defined by shape.  `iota-d' has
         ;; already granted the defining property, whose FIRST conjunct is
         ;; (IN <iota> ORD) -- split it out so the certificate reads it off an
         ;; atomic assumption.
         ;; `ai' REPLACES the conjunction it splits, and cd-body-unique
         ;; detaches against it, so read the conjunct out in a have! LANE.
         (have! (list 'IN cd-io 'ORD) (lambda () (prop)))
         (fact 'cd-seg-body 'n_)
         (fact 'cd-body-unique '(ORD-SEGMENT n_) cd-io 'n_)
         (ass))))
 (dk-opened (lambda () (iota-d cd-io))))
(qed 'card-segment)
(topic! 'card-segment 'set-theory)
