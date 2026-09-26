;;; rake-ord-pigeonhole.scm -- rake batch 5c, assignment 5c-U (2026-09-18).
;;;
;;; THE ASSIGNED TARGET (1) IS FALSE, AND THAT IS THE FINDING.
;;;
;;;   ord-segment-pigeonhole:  be, al in ORD,  ORD-LT be al
;;;                              =>  no injection ORD-SEGMENT(al) -> ORD-SEGMENT(be)
;;;
;;; is refuted by al = succ_ORD(omega), be = omega: ORD-SEGMENT(succ_ORD omega)
;;; is omega+1 = {0,1,2,...} u {omega}, ORD-SEGMENT(omega) is omega, and
;;;
;;;     omega |-> 0,      n |-> succ n   (n a natural)
;;;
;;; is an injection of the first into the second.  Pigeonhole for ordinal
;;; segments is FINITE pigeonhole: it holds for al in NN (that is
;;; `pigeonhole-segments-gen', theorem-library/pigeonhole-segments.scm) and for
;;; INITIAL ordinals (al = the least ordinal of its own cardinality), and for
;;; nothing else.  The initial-ordinal form is true but is Cantor-Schroeder-
;;; Bernstein in disguise and is not what this assignment needed; the NN form is
;;; proven below under the `-guarded' name the batch-5 rule asks for.
;;;
;;; VNB CANNOT ITSELF EXHIBIT THE COUNTEREXAMPLE, and that is worth stating:
;;; the refutation needs an infinite ordinal whose segment is exactly NN, i.e.
;;; "every ordinal below SUP-ORD(NN) is a natural number", and no axiom of
;;; structure-library/ordinals.scm says so (SUP-ORD is pinned only as a least
;;; upper bound).  So the statement is not refutable IN the theory; it is false
;;; in the intended model, which is the same verdict `matof-exists' got and the
;;; same reason to stop on it.
;;;
;;; WHAT REPLACES IT.  Target (2), `card-star-zermelo', was assigned as a
;;; CONSUMER of (1) -- leastness of the cardinal was to come from ordinal
;;; pigeonhole.  It does not need it.  The ordinal that CARD-STAR describes is
;;; obtained not by proving some particular ordinal least, but by WELL-ORDERING
;;; the ordinals that biject with S:
;;;
;;;     zermelo-bijection (rake-zermelo.scm) gives SOME al0 in ORD with a
;;;     bijection ORD-SEGMENT(al0) -> S;  inverse-bij-is-bijection flips it;
;;;     CL = { a in ORD-SEGMENT(succ_ORD al0) : S bijects with ORD-SEGMENT(a) }
;;;     is a SEP over a set, hence a set, and al0 is in it, so `ord-well-ordered'
;;;     returns its ORD-LE-least member m.  m satisfies the CARD-STAR
;;;     description outright: a smaller be that bijected with S would lie in CL
;;;     (it is below m <= al0 < succ al0), so m <= be, contradicting be < m.
;;;
;;; That is exactly the argument `zermelo-least-ordinal' runs one floor down,
;;; and it is the argument rake-zermelo.scm's closing note (3) attributes to a
;;; SEGMENT-FIRST cardinal.  The note's "(2) ... LEASTNESS, and this is the real
;;; gap" is therefore too pessimistic: bounding the candidates by
;;; ORD-SEGMENT(succ al0) makes the A-first CARD-STAR land with no pigeonhole
;;; anywhere.  Only the DIRECTION half of that note is needed, and it is the one
;;; citation the note names (inverse-bij-is-bijection, CHOICE-built; no cost
;;; here, ZEN is built on CHOICE from the start).
;;;
;;; WHAT IS PROVEN HERE (four theorems, all `modulo 0')
;;;
;;;   ord-segment-pigeonhole-guarded   the NN-guarded form of the false target:
;;;                                    al, be in NN, ORD-LT be al => no injection
;;;                                    ORD-SEGMENT(al) -> ORD-SEGMENT(be).
;;;   card-star-body-exists            S in SET => some ordinal satisfies the
;;;                                    CARD-STAR description at S.  The content.
;;;   card-star-zermelo                S in SET => CARD-STAR(S) is an ordinal and
;;;                                    S bijects with ORD-SEGMENT(CARD-STAR S).
;;;   card-star-well-ordering          S in SET => ORD-SEGMENT(CARD-STAR S)
;;;                                    bijects with S -- `well-ordering-principle'
;;;                                    (theorem-library/well-ordering.scm:10,
;;;                                    asserted `well-known') character for
;;;                                    character with CARD-STAR for CARD.
;;;
;;; NOTHING IS RETIRED BY THIS FILE.  well-ordering-principle is stated with the
;;; AXIOMATISED CARD, and CARD and CARD-STAR are two constants; retiring it is
;;; the identification decision, reported in the closing block.
;;;
;;; CITATIONS and their load positions (0-based over the quoted file names of
;;; *vnb-files*, load.scm:81):
;;;   structure-library/ordinals (77, primitive): ord-lt-iff, ord-le-closure,
;;;     ord-le-trans, ord-le-antisymm, ord-succ-in, ord-succ-above,
;;;     ord-segment-membership, ord-le-nn-compat
;;;   theorem-library/ord-well-ordered-proof (145): ord-well-ordered
;;;   theorem-library/equality-basics (146): eq-sym
;;;   theorem-library/nn-order-basics (166): nn-in-rr
;;;   theorem-library/rr-order-basics (173): rr-le-ne-lt
;;;   theorem-library/rake-inverse-bij (192): inverse-bij-is-bijection
;;;   theorem-library/pigeonhole-segments (219): pigeonhole-segments-gen
;;;   theorem-library/card-finite (274): card-star-from-body
;;;   theorem-library/zen-step (303): ord-lt-succ-iff-le
;;;   theorem-library/rake-zermelo (304): zermelo-bijection      -- the LATEST
;;;
;;; LOAD WINDOW [305, end).  lo is forced by theorem-library/rake-zermelo (304);
;;; nothing cites these four names, so no citer forces hi.
;;;
;;; Helper prefix: r7u-.

;;; ---- driver helpers ---------------------------------------------------

(define (r7u-find pred lst what)
  (or (any-pred pred lst) (error "rake-ord-pigeonhole: not found --" what)))
(define (r7u-asm pred what) (r7u-find pred (dk-asms) what))
(define (r7u-subject-of pred lst what) (cadr (r7u-find pred lst what)))
(define (r7u-in? cls) (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) cls))))

(define (r7u-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-ord-pigeonhole: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l)))
                    (newline))
                  (proof-leaves))
        (error "rake-ord-pigeonhole: unfinished" name))))

;; (ORD-LT v b) in context  ->  (IN v ORD), (IN b ORD), (ORD-LE v b), (NOT (= v b))
(define (r7u-ord-of-lt! v b)
  (fact 'ord-lt-iff v b)
  (ai (list 'IFF (list 'ORD-LT v b)
            (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b)))))
  (detach! (list 'IMPLIES (list 'ORD-LT v b)
                 (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b)))))
  (dk-split! (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b))))
  (fact 'ord-le-closure v b)
  (dk-split! (list 'AND (list 'IN v 'ORD) (list 'IN b 'ORD))))

;; segment membership, both ways.  (IN b ORD) must be in context.
(define (r7u-seg-iff! v b)
  (fact 'ord-segment-membership b v)
  (ai (list 'IFF (list 'IN v (list 'ORD-SEGMENT b)) (list 'ORD-LT v b))))
(define (r7u-seg->lt! v b)
  (r7u-seg-iff! v b)
  (detach! (list 'IMPLIES (list 'IN v (list 'ORD-SEGMENT b)) (list 'ORD-LT v b))))
(define (r7u-lt->seg! v b)
  (r7u-seg-iff! v b)
  (detach! (list 'IMPLIES (list 'ORD-LT v b) (list 'IN v (list 'ORD-SEGMENT b)))))

;; zen-step's proven bridge:  v ORD-LT succ_ORD(b)  <->  v ORD-LE b
(define (r7u-succ-bridge! v b)
  (fact 'ord-lt-succ-iff-le b v)
  (ai (list 'IFF (list 'ORD-LT v (list 'succ_ORD b)) (list 'ORD-LE v b))))

;;; =====================================================================
;;; ord-segment-pigeonhole-guarded -- the assigned statement, GUARDED to NN.
;;;
;;;   al, be in NN,  ORD-LT be al  =>  nothing injects S(al) into S(be)
;;;
;;; Everything here is the translation ORD-LT -> `<' on the naturals:
;;; ord-lt-iff opens ORD-LT into ORD-LE plus a disequality, ord-le-nn-compat
;;; takes ORD-LE to `<=' (its antecedent is an AND, so the conjunction is landed
;;; first -- `fact' will not split one), and rr-le-ne-lt makes it strict.
;;; `pigeonhole-segments-gen' is then cited verbatim.  The mathematics is all in
;;; that citation; what this theorem adds is the ORD-LT face, which is the face
;;; every ordinal-side consumer has.
;;; =====================================================================

(sp (make-wff
     '(FORALL al (IMPLIES (IN al NN)
        (FORALL be (IMPLIES (IN be NN)
          (IMPLIES (ORD-LT be al)
            (FORALL f_ (NOT (IN f_ (INJECTION (ORD-SEGMENT al)
                                              (ORD-SEGMENT be))))))))))))

(define r7u-t1-peel (dk-peel!))
(define r7u-t1-lt (r7u-find (dk-head? 'ORD-LT) r7u-t1-peel "the ORD-LT hypothesis"))
(define r7u-t1-be (cadr  r7u-t1-lt))
(define r7u-t1-al (caddr r7u-t1-lt))
(define r7u-t1-f
  (cadr (r7u-find (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                   (pair? (caddr f)) (eq? (car (caddr f)) 'INJECTION)))
                  (dk-landed (lambda () (di)))          ; the NOT goal: assume the positive
                  "the injection assumed for contradiction")))

(r7u-ord-of-lt! r7u-t1-be r7u-t1-al)                    ; ORD-LE and the disequality
(have! (list 'AND (list 'IN r7u-t1-be 'NN) (list 'IN r7u-t1-al 'NN)))
(fact 'ord-le-nn-compat r7u-t1-be r7u-t1-al)
(ai (list 'IFF (list 'ORD-LE r7u-t1-be r7u-t1-al) (list '<= r7u-t1-be r7u-t1-al)))
(detach! (list 'IMPLIES (list 'ORD-LE r7u-t1-be r7u-t1-al)
               (list '<= r7u-t1-be r7u-t1-al)))
(fact 'nn-in-rr r7u-t1-be)
(fact 'nn-in-rr r7u-t1-al)
(have! (list 'AND (list '<= r7u-t1-be r7u-t1-al)
             (list 'NOT (list '= r7u-t1-be r7u-t1-al))))
(fact 'rr-le-ne-lt r7u-t1-be r7u-t1-al)                 ; (< be al)
(dk-fact! 'pigeonhole-segments-gen r7u-t1-al r7u-t1-be r7u-t1-f)
(ai (list 'NOT (list 'IN r7u-t1-f
                     (list 'INJECTION (list 'ORD-SEGMENT r7u-t1-al)
                           (list 'ORD-SEGMENT r7u-t1-be)))))

(r7u-qed! 'ord-segment-pigeonhole-guarded)
(topic! 'ord-segment-pigeonhole-guarded 'combinatorial)

;;; =====================================================================
;;; card-star-body-exists -- the CARD-STAR description is satisfied.
;;;
;;;   S in SET  |-  forsome al.  al in ORD
;;;                   and  S bijects with ORD-SEGMENT(al)
;;;                   and  no ordinal below al bijects with S
;;;
;;; This is the content of the assignment, and it needs no pigeonhole.  The
;;; ordinals that biject with S and sit at or below the one zermelo-bijection
;;; produces form a SET -- a separation over ORD-SEGMENT(succ_ORD al0) -- so
;;; `ord-well-ordered' hands back the ORD-LE-least of them, and THAT ordinal
;;; satisfies the description outright.  The bound is what makes the class a
;;; set: the ordinals bijecting with S form a proper class as far as this tree
;;; is concerned (no COMP is installed in any formula here), and the least one
;;; is below al0 anyway.
;;;
;;; The description's existence clause is S -> SEGMENT (card-defined.scm's
;;; direction decision) while zermelo-bijection produces SEGMENT -> S, so the
;;; map is flipped once, by `inverse-bij-is-bijection'.
;;;
;;; The antecedent handed to `ord-well-ordered' is taken FROM THE PROVER rather
;;; than transcribed: its subset clause binds `x' and CL carries bound variables
;;; of its own, so a hand-written copy is one capture-rename away from matching
;;; nothing (zen-step.scm's class-extensionality note).
;;; =====================================================================

;; the description's body, at an arbitrary class and ordinal.  A copy of
;; card-defined.scm's `cd-body' / card-finite.scm's `cf-body': load.scm gives
;; each theorem-library file its own environment, so neither is visible here.
(define (r7u-body A al)
  (list 'AND (list 'IN al 'ORD)
    (list 'AND (list 'FORSOME 'phi (list 'IN 'phi (list 'BIJECTION A (list 'ORD-SEGMENT al))))
      (list 'FORALL 'beta
        (list 'IMPLIES (list 'ORD-LT 'beta al)
          (list 'NOT (list 'FORSOME 'psi
                       (list 'IN 'psi (list 'BIJECTION A (list 'ORD-SEGMENT 'beta))))))))))

;; "S bijects with ORD-SEGMENT(al)" -- the SEP body of CL, and the existence
;; clause of the description up to alpha-renaming of its witness binder.
(define (r7u-bijs A al)
  (list 'FORSOME 'ph_ (list 'IN 'ph_ (list 'BIJECTION A (list 'ORD-SEGMENT al)))))

(sp (make-wff (list 'FORALL 'S
                    (list 'IMPLIES '(IN S SET)
                          (list 'FORSOME 'al (r7u-body 'S 'al))))))

(define r7u-t2-peel (dk-peel!))
(define r7u-S (r7u-subject-of (r7u-in? 'SET) r7u-t2-peel "the set being counted"))

;;; ---- an ordinal that works at all: zermelo-bijection, flipped -----------
(fact 'zermelo-bijection r7u-S)
(define r7u-al0
  (dk-skolem! (list 'FORSOME 'al
                    (list 'AND '(IN al ORD)
                          (list 'FORSOME 'phi
                                (list 'IN 'phi (list 'BIJECTION '(ORD-SEGMENT al) r7u-S)))))))
(define r7u-seg0 (list 'ORD-SEGMENT r7u-al0))
(define r7u-phi0
  (dk-skolem! (list 'FORSOME 'phi (list 'IN 'phi (list 'BIJECTION r7u-seg0 r7u-S)))))
(dk-fact! 'inverse-bij-is-bijection r7u-seg0 r7u-S r7u-phi0)
(have! (r7u-bijs r7u-S r7u-al0)
       (lambda () (ew (list 'INVERSE-BIJ r7u-phi0 r7u-seg0 r7u-S)) (ass)))

;;; ---- the candidates, bounded so that they form a SET --------------------
(define R7U-SAL (list 'succ_ORD r7u-al0))
(fact 'ord-succ-in r7u-al0)                      ; (IN succ(al0) ORD)
(fact 'ord-succ-above r7u-al0)                   ; (ORD-LT al0 succ(al0))
(r7u-lt->seg! r7u-al0 R7U-SAL)                   ; (IN al0 (ORD-SEGMENT succ(al0)))

(define R7U-CL
  (list 'SEP 'a_ (list 'ORD-SEGMENT R7U-SAL) (r7u-bijs r7u-S 'a_)))

(define (r7u-cl-intro!)
  (for-each (lambda (l) (dk-focus! l) (ass))
            (dk-opened (lambda () (sep-mi)))))

(have! (list 'IN r7u-al0 R7U-CL) r7u-cl-intro!)

;;; ---- its least member ---------------------------------------------------
(fact 'ord-well-ordered R7U-CL)
(define r7u-owo
  (r7u-asm (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'FORSOME)
                            (dk-contains? f R7U-CL)))
           "ord-well-ordered at the class of candidate cardinals"))

(have! (cadr r7u-owo)
  (lambda ()
    (for-each
     (lambda (l)
       (dk-focus! l)
       (if (eq? (car (dk-goal)) 'FORSOME)
           (begin (ew r7u-al0) (ass))                 ; nonempty: al0 is a candidate
           (let* ((landed (dk-peel!))                 ; subset of ORD
                  (v (r7u-subject-of (r7u-in? R7U-CL) landed "the peeled candidate")))
             (sep-me (list 'IN v R7U-CL))
             (r7u-seg->lt! v R7U-SAL)
             (r7u-ord-of-lt! v R7U-SAL)
             (ass))))
     (dk-opened (lambda () (di))))))
(detach! r7u-owo)

(define r7u-m (dk-skolem! (caddr r7u-owo)))
(define r7u-least
  (r7u-asm (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                            (pair? (caddr (caddr f)))
                            (eq? (car (caddr (caddr f))) 'ORD-LE)))
           "the leastness of m"))

(sep-me (list 'IN r7u-m R7U-CL))                 ; segment membership + a bijection at m
(r7u-seg->lt! r7u-m R7U-SAL)
(r7u-ord-of-lt! r7u-m R7U-SAL)                   ; (IN m ORD)
(r7u-succ-bridge! r7u-m r7u-al0)
(detach! (list 'IMPLIES (list 'ORD-LT r7u-m R7U-SAL) (list 'ORD-LE r7u-m r7u-al0)))

;;; ---- nothing below m bijects with S -------------------------------------
;;; A candidate be below m is below al0 too, so it is IN CL, so m <= be -- and
;;; be < m gave be <= m, so antisymmetry makes them equal, against be /= m.
(define (r7u-least-branch!)
  (let* ((landed (dk-peel!))
         (bv (cadr (r7u-find (dk-head? 'ORD-LT) landed "the peeled candidate")))
         (ex (dk-landed-1 (lambda () (di))))       ; assume the bijection exists
         (psi0 (dk-skolem! ex)))
    (r7u-ord-of-lt! bv r7u-m)
    (have! (list 'AND (list 'ORD-LE bv r7u-m) (list 'ORD-LE r7u-m r7u-al0)))
    (fact 'ord-le-trans bv r7u-m r7u-al0)          ; (ORD-LE bv al0)
    (r7u-succ-bridge! bv r7u-al0)
    (detach! (list 'IMPLIES (list 'ORD-LE bv r7u-al0) (list 'ORD-LT bv R7U-SAL)))
    (r7u-lt->seg! bv R7U-SAL)
    (have! (r7u-bijs r7u-S bv) (lambda () (ew psi0) (ass)))
    (have! (list 'IN bv R7U-CL) r7u-cl-intro!)
    (dk-apply! r7u-least bv)                       ; (ORD-LE m bv)
    (have! (list 'AND (list 'ORD-LE r7u-m bv) (list 'ORD-LE bv r7u-m)))
    (fact 'ord-le-antisymm r7u-m bv)               ; (= m bv)
    (have! (list '= bv r7u-m) (lambda () (fact 'eq-sym r7u-m bv) (ass)))
    (ai (list 'NOT (list '= bv r7u-m)))))

(ew r7u-m)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORALL) (r7u-least-branch!) (ass))))

(r7u-qed! 'card-star-body-exists)
(topic! 'card-star-body-exists 'constructions)

;;; =====================================================================
;;; card-star-zermelo -- CARD-STAR is TOTAL on sets, and computes.
;;;
;;;   S in SET  |-  CARD-STAR(S) in ORD  and  S bijects with
;;;                 ORD-SEGMENT(CARD-STAR S)
;;;
;;; `card-star-from-body' (card-finite.scm) says anything satisfying the
;;; description IS the cardinal, so the theorem above turns into one `subst' of
;;; the equation it returns.  The first conjunct is what "CARD-STAR(S) denotes"
;;; amounts to in this logic: an IOTA whose description is satisfied by a unique
;;; object, and `iota-d' -- run inside card-star-from-body -- is what granted it.
;;;
;;; The body must be handed to card-star-from-body WHOLE: `fact' does not split
;;; a conjunctive antecedent, and dk-skolem! has already split this one to read
;;; the eigenvariable off, so it is reassembled in a `have!' lane.
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 'S
       (list 'IMPLIES '(IN S SET)
         (list 'AND (list 'IN '(CARD-STAR S) 'ORD)
               (list 'FORSOME 'phi
                     (list 'IN 'phi (list 'BIJECTION 'S
                                          (list 'ORD-SEGMENT '(CARD-STAR S))))))))))

(define r7u-t3-peel (dk-peel!))
(define r7u-t3-S (r7u-subject-of (r7u-in? 'SET) r7u-t3-peel "the set being counted"))

(fact 'card-star-body-exists r7u-t3-S)
(define r7u-t3-al
  (dk-skolem! (list 'FORSOME 'al (r7u-body r7u-t3-S 'al))))
(have! (r7u-body r7u-t3-S r7u-t3-al)
       (lambda () (dk-conj-close! (lambda () (ass)))))
(define r7u-t3-eq (dk-fact! 'card-star-from-body r7u-t3-S r7u-t3-al))  ; CARD-STAR(S) = al
(subst r7u-t3-eq)
(dk-conj-close! (lambda () (ass)))

(r7u-qed! 'card-star-zermelo)
(topic! 'card-star-zermelo 'constructions)

;;; =====================================================================
;;; card-star-well-ordering -- `well-ordering-principle' with CARD-STAR.
;;;
;;;   S in SET  |-  forsome phi.  phi in BIJECTION(ORD-SEGMENT(CARD-STAR S), S)
;;;
;;; The support at theorem-library/well-ordering.scm:10 is this statement with
;;; the AXIOMATISED CARD in place of CARD-STAR, and nothing else differs.  The
;;; proof is the previous theorem with the bijection flipped back the way
;;; zermelo-bijection produced it -- the round trip is not wasted work: what is
;;; gained in between is that the ordinal is the LEAST one, which is what makes
;;; it CARD-STAR(S) rather than some enumeration's accidental length.
;;;
;;; (IN (CARD-STAR S) ORD) is landed BEFORE the citation on purpose: since
;;; 2026-09-18 universal instantiation owes definedness, and an IOTA-bodied
;;; functoid is never certified by shape -- the typing in the context is what
;;; certifies ORD-SEGMENT(CARD-STAR S) as an instantiating term.
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 'S
       (list 'IMPLIES '(IN S SET)
         (list 'FORSOME 'phi
               (list 'IN 'phi (list 'BIJECTION (list 'ORD-SEGMENT '(CARD-STAR S)) 'S)))))))

(define r7u-t4-peel (dk-peel!))
(define r7u-t4-S (r7u-subject-of (r7u-in? 'SET) r7u-t4-peel "the set being counted"))
(define R7U-T4-SEG (list 'ORD-SEGMENT (list 'CARD-STAR r7u-t4-S)))

(fact 'card-star-zermelo r7u-t4-S)
(dk-split! (list 'AND (list 'IN (list 'CARD-STAR r7u-t4-S) 'ORD)
                 (list 'FORSOME 'phi
                       (list 'IN 'phi (list 'BIJECTION r7u-t4-S R7U-T4-SEG)))))
(define r7u-t4-phi
  (dk-skolem! (list 'FORSOME 'phi (list 'IN 'phi (list 'BIJECTION r7u-t4-S R7U-T4-SEG)))))
(dk-fact! 'inverse-bij-is-bijection r7u-t4-S R7U-T4-SEG r7u-t4-phi)
(ew (list 'INVERSE-BIJ r7u-t4-phi r7u-t4-S R7U-T4-SEG))
(ass)

(r7u-qed! 'card-star-well-ordering)
(topic! 'card-star-well-ordering 'constructions)

;;; =====================================================================
;;; REPORT (item 3 of the assignment): what the identification CARD =
;;; CARD-STAR would cost, and which card-* axioms become THEOREMS.
;;;
;;; THE IDENTIFICATION IS A RENAME, NOT A BRIDGING AXIOM.  `well-ordering-
;;; principle' (theorem-library/well-ordering.scm:10) is `card-star-well-
;;; ordering' above with CARD for CARD-STAR and nothing else changed, so it is
;;; retired the moment the two constants are one.  What it CANNOT be given is a
;;; bridge -- an axiom or theorem `forall A in SET. CARD(A) = CARD-STAR(A)'.
;;; Nothing in structure-library/cardinality.scm makes CARD least, or even makes
;;; CARD(A) biject with A when A is infinite (card-finite-bij is guarded on
;;; (IN (CARD A) NN)), so the bridge is not derivable, and asserting it would
;;; assert exactly the content of the support it is meant to discharge.  The
;;; honest move is the one card-defined.scm's header already names: prove the
;;; CARD-STAR form of each axiom, delete the axiom, rename -- one at a time.
;;;
;;; WHAT IS ALREADY DISCHARGED (the CARD-STAR form is PROVEN, modulo 0):
;;;   card-in-ord      first conjunct of card-star-zermelo (above)     NEW TODAY
;;;   card-finite-bij  card-star-well-ordering (above) with the        NEW TODAY
;;;                    finiteness guard DROPPED -- strictly stronger
;;;   card-empty       card-star-empty        (theorem-library/card-finite.scm)
;;;   card-segment     card-star-segment      (theorem-library/card-defined.scm)
;;;   well-ordering-principle                 card-star-well-ordering, verbatim
;;;
;;; WHAT IS NOT, and one of them is a STATEMENT DEFECT:
;;;   card-insert            FALSE of a defined CARD as it stands.  It is
;;;     unguarded: for infinite A it claims CARD(A u {x}) = succ_ORD(CARD A),
;;;     while the least ordinal bijecting with A u {x} is CARD(A) itself
;;;     (omega u {x} bijects with omega).  It needs the guard (IN (CARD A) NN) --
;;;     the guard its two neighbours card-union-disjoint and finite-set-induction
;;;     already carry -- and then it is the finite-surgery statement the
;;;     card*-insert note has been waiting on (EXTEND-BY; leastness at a finite
;;;     cardinal is pigeonhole-segments-gen, which exists).  This is the same
;;;     species as `interval-card-in-nn' in 2026-08: an axiom that is harmless
;;;     while CARD is implicit and false once it is defined, and it is the second
;;;     one found.  Worth a sweep of the remaining card-* statements for the
;;;     missing finiteness guard BEFORE any rename.
;;;   card-union-disjoint    guarded finite already; wants card-star-insert or a
;;;                          direct disjoint-union bijection.
;;;   finite-set-induction   guarded finite already; the header calls it derivable
;;;                          from nn-induction via card-finite-bij + card-insert,
;;;                          so it follows the two above.
;;;   card-image-injection   (structure-library/injection.scm, primitive) -- not
;;;                          examined here.
;;;
;;; SO THE REMAINING COST OF THE RENAME IS card-insert (guarded) AND ITS TWO
;;; DEPENDANTS, plus card-image-injection.  Everything else on the primitive
;;; card shelf is now a theorem of the DEFINED cardinal.
;;; =====================================================================
