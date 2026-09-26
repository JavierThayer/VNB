;;; card-finite.scm -- the finite layer of the DEFINED cardinal, CARD-STAR.
;;;
;;; card-defined.scm builds CARD-STAR and proves card-star-segment (CARD-STAR(S(n)) = n).
;;; This file turns that keystone into the finite facts that cardinality.scm
;;; currently ASSERTS as `primitive' axioms about the axiomatised CARD.  Each
;;; theorem here is the CARD-STAR form of one of those axioms; the swap onto the
;;; name CARD is a separate step, made one name at a time as its theorem lands
;;; (see structure-notes/card-basics-worklist.md).
;;;
;;; WHAT IS PROVEN HERE
;;;   card-star-from-body   cd-body(A,al)  =>  CARD-STAR(A) = al          modulo 0
;;;   card-star-bij         bijections BOTH WAYS between A and S(n)
;;;                       =>  CARD-STAR(A) = n
;;;   seg0-empty        EMPTY-SET = ORD-SEGMENT(0)                modulo 0
;;;   card-star-empty       CARD-STAR(EMPTY-SET) = 0            [replaces card-empty]
;;;
;;; THE MECHANISM, AND WHY IT IS TWO-SIDED.  `card-star-from-body' is card-star-segment's
;;; `iota-d' script with the segment generalised to a class: it says that
;;; anything satisfying the description IS the cardinal, so every later fact
;;; reduces to exhibiting the description's body.  `card-star-bij' does that from
;;; bijections, and it takes BOTH directions as hypotheses on purpose:
;;;
;;;   * the EXISTENCE clause needs A -> S(n)   (supply it directly);
;;;   * the LEASTNESS clause needs S(n) -> A, to compose with a hypothetical
;;;     A -> S(beta) into S(n) -> S(beta), which pigeonhole-segments-gen kills.
;;;
;;; Either direction alone would need the other one INVERTED, and the tree's only
;;; inverse (INVERSE-BIJ, bijection.scm) is defined via CHOICE -- which this track
;;; exists not to need.  At the concrete sites both maps are explicit lambdas, so
;;; the two-sided hypothesis costs nothing there.  If the choice-free IOTA inverse
;;; for an injection is ever built ("the unique preimage"), one side becomes
;;; derivable and this statement can be weakened.

;;; --- file-local helpers (cf- prefix) ------------------------------------

;;; The description's body at an arbitrary class and ordinal.  A copy of
;;; card-defined.scm's `cd-body': load.scm loads each theorem-library file into
;;; its own environment, so that definition is not visible here.
(define (cf-body A al)
  (list 'AND (list 'IN al 'ORD)
    (list 'AND (list 'FORSOME 'phi (list 'IN 'phi (list 'BIJECTION A (list 'ORD-SEGMENT al))))
      (list 'FORALL 'beta
        (list 'IMPLIES (list 'ORD-LT 'beta al)
          (list 'NOT (list 'FORSOME 'psi
                       (list 'IN 'psi (list 'BIJECTION A (list 'ORD-SEGMENT 'beta))))))))))

;;; peel until the goal's head changes.  `di' is greedy but stops at an IMPLIES
;;; whose antecedent is an AND, so one call is not enough.
(define (cf-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop))))))

(define (cf-first h)
  (let ((fs (filter (dk-head? h) (dk-asms))))
    (if (null? fs) (error "cf-first: nothing with head" h) (car fs))))

;;; --------------------------------------------------------------------
;;; card-star-from-body:  anything satisfying the description IS the cardinal.
;;;
;;; `iota-d' posts existence-and-uniqueness (the hypothesis is the witness,
;;; cd-body-unique the uniqueness) and hands back the defining property;
;;; cd-body-unique then identifies the described ordinal with al.  This is
;;; card-star-segment's script with (ORD-SEGMENT n_) replaced by a variable.
;;; --------------------------------------------------------------------

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'al
      (list 'IMPLIES (cf-body 'a_ 'al) (list '= (list 'CARD-STAR 'a_) 'al))))))
(cf-peel!)
(mac 'card-star)
(define cf-io (cadr (dk-goal)))          ; the IOTA term, as the engine built it
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'FORSOME)
       ;; existence and uniqueness
       (begin
         (ew 'al)
         (for-each
          (lambda (m)
            (dk-focus! m)
            (if (eq? (car (dk-goal)) 'FORALL)
                (begin
                  (cf-peel!)
                  (let ((y (caddr (dk-goal))))          ; goal (= al y)
                    (fact 'cd-body-unique 'a_ 'al y)
                    (ass)))
                (ass)))
          (dk-opened (lambda () (di)))))
       ;; the defining property, against the hypothesis
       (begin
         ;; 2026-09-18 (LUTINS instantiation): cd-body-unique is cited at the
         ;; IOTA term, never certified defined by shape.  `iota-d' granted the
         ;; defining property, whose first conjunct is (IN <iota> ORD); read it
         ;; out in a have! LANE -- `ai' would REPLACE the conjunction that
         ;; cd-body-unique detaches against.
         (have! (list 'IN cf-io 'ORD) (lambda () (prop)))
         (fact 'cd-body-unique 'a_ cf-io 'al)
         (ass))))
 (dk-opened (lambda () (iota-d cf-io))))
(qed 'card-star-from-body)
(topic! 'card-star-from-body 'combinatorial)

;;; --------------------------------------------------------------------
;;; card-star-bij:  bijections both ways between A and S(n) compute CARD-STAR(A).
;;;
;;;   n in NN,  ph in BIJECTION(A, S(n)),  et in BIJECTION(S(n), A)
;;;     =>  CARD-STAR(A) = n
;;;
;;; Existence is `ph'.  Leastness composes `et' with a hypothetical
;;; A -> S(beta) (bijection-compose), reads the composite as an INJECTION
;;; S(n) -> S(beta) with beta < n, and cites pigeonhole-segments-gen.
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL a_ (FORALL ph (FORALL et
       (IMPLIES (AND (IN ph (BIJECTION a_ (ORD-SEGMENT n_)))
                     (IN et (BIJECTION (ORD-SEGMENT n_) a_)))
                (= (CARD-STAR a_) n_)))))))))
(cf-peel!)
(dk-split! '(AND (IN ph (BIJECTION a_ (ORD-SEGMENT n_)))
                 (IN et (BIJECTION (ORD-SEGMENT n_) a_))))
(fact 'nn-subset-ord 'n_)

;;; The body is a right-nested AND and `di' splits ONE level per call, so the
;;; walker recurses rather than assuming three leaves appear at once.
(define (cf-close-body!)
  (let ((g (dk-goal)))
    (cond
      ((eq? (car g) 'AND)
       (for-each (lambda (l) (dk-focus! l) (cf-close-body!))
                 (dk-opened (lambda () (di)))))
      ;; n_ in ORD
      ((eq? (car g) 'IN) (ass))
      ;; existence: the given bijection a_ -> S(n_)
      ((eq? (car g) 'FORSOME) (ew 'ph) (ass))
      ;; leastness: compose S(n_) -> a_ -> S(beta) and apply pigeonhole
      (else
       (cf-peel!)                        ; beta, beta ORD-LT n_, and the FORSOME
       (ai (cf-first 'FORSOME))          ; ... opened: chi in BIJECTION(a_, S beta)
       ;; the bijection OUT OF a_ that is not the hypothesis `ph'
       (let* ((bij (car (filter (lambda (f)
                                  (and (pair? f) (eq? (car f) 'IN)
                                       (pair? (caddr f))
                                       (eq? (car (caddr f)) 'BIJECTION)
                                       (equal? (cadr (caddr f)) 'a_)
                                       (not (equal? (cadr f) 'ph))))
                                (dk-asms))))
              (chi (cadr bij))
              (bet (cadr (caddr (caddr bij)))))
         (have! (list 'IN bet '(ORD-SEGMENT n_))
                (lambda () (mac 'ord-segment-membership) (ass)))
         (fact 'ord-segment-nn-subset 'n_ bet)
         ;; seg-mem-lt rewrites membership -> inequality, so it goes on the
         ;; HYPOTHESIS: as a goal macete it would need the -rev companion.
         (mac-h 'seg-mem-lt (list 'IN bet '(ORD-SEGMENT n_)))
         ;; bijection-compose has an AND antecedent, which `fact' will not
         ;; split -- land the conjunction first.
         (have! (list 'AND (list 'IN 'et '(BIJECTION (ORD-SEGMENT n_) a_))
                           (list 'IN chi (list 'BIJECTION 'a_ (list 'ORD-SEGMENT bet)))))
         (let* ((comp (dk-fact! 'bijection-compose '(ORD-SEGMENT n_) 'a_
                                (list 'ORD-SEGMENT bet) 'et chi))
                (lam  (cadr comp)))       ; the composite lambda, as installed
           (have! (list 'IN lam (list 'INJECTION '(ORD-SEGMENT n_) (list 'ORD-SEGMENT bet)))
                  (lambda ()
                    (mac 'injection-membership-iff)
                    (fact 'bijection-in-fun '(ORD-SEGMENT n_) (list 'ORD-SEGMENT bet) lam)
                    (fact 'bijection-injective '(ORD-SEGMENT n_) (list 'ORD-SEGMENT bet) lam)
                    (from-context!)))
           (dk-fact! 'pigeonhole-segments-gen 'n_ bet lam)
           (ai (list 'NOT (list 'IN lam (list 'INJECTION '(ORD-SEGMENT n_)
                                              (list 'ORD-SEGMENT bet)))))))))))

(have! (cf-body 'a_ 'n_) cf-close-body!)
(fact 'card-star-from-body 'a_ 'n_)
(ass)
(qed 'card-star-bij)
(topic! 'card-star-bij 'combinatorial)

;;; --------------------------------------------------------------------
;;; seg0-empty:  EMPTY-SET = ORD-SEGMENT(0).
;;;
;;; Both classes are empty, so class-extensionality (theory.scm, an NBG axiom
;;; with no set-of-both precondition) equates them.  Each direction of the IFF
;;; is ex falso: the hypothesis contradicts the emptiness fact for its own side,
;;; and `ai' on the negation closes the branch whatever the goal is.
;;;
;;; The direction is EMPTY-SET = ORD-SEGMENT(0), not the reverse, because
;;; `subst' rewrites left-to-right in the GOAL and the consumer below has
;;; EMPTY-SET in its goal.
;;; --------------------------------------------------------------------

(sp (make-wff '(= EMPTY-SET (ORD-SEGMENT 0))))

(have! '(FORALL x (IFF (IN x EMPTY-SET) (IN x (ORD-SEGMENT 0))))
  (lambda ()
    ;; one `di' peels the FORALL and splits the IFF into its two implications
    (di)
    (for-each
     (lambda (l)
       (dk-focus! l)
       (if (equal? (dk-goal) '(IN x EMPTY-SET))
           ;; assume x in S(0): ord-segment-zero-no-members refutes it
           (begin (fact 'ord-segment-zero-no-members 'x)
                  (ai '(NOT (IN x (ORD-SEGMENT 0)))))
           ;; assume x in EMPTY-SET: empty-set-has-no-members refutes it
           (begin (fact 'empty-set-has-no-members 'x)
                  (ai '(NOT (IN x EMPTY-SET))))))
     (dk-opened (lambda () (di))))))

(fact 'class-extensionality 'EMPTY-SET '(ORD-SEGMENT 0))
(ass)
(qed 'seg0-empty)
(topic! 'seg0-empty 'combinatorial)

;;; --------------------------------------------------------------------
;;; card-star-empty:  CARD-STAR(EMPTY-SET) = 0.   [the CARD-STAR form of card-empty]
;;;
;;; card-star-segment at n := 0, transported across seg0-empty.  This one needs
;;; neither card-star-bij nor any bijection: the two classes are literally equal.
;;; `subst' needs the equation in the CONTEXT, hence the `fact' above it.
;;; --------------------------------------------------------------------

(sp (make-wff '(= (CARD-STAR EMPTY-SET) 0)))
(fact 'nn-zero-in)
(fact 'card-star-segment 0)
(fact 'seg0-empty)
(subst '(= EMPTY-SET (ORD-SEGMENT 0)))
(ass)
(qed 'card-star-empty)
(topic! 'card-star-empty 'combinatorial)
