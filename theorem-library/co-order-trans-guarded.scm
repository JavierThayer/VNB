;;; co-order-trans-guarded.scm -- the six `co-' order composition lemmas,
;;; PROVEN.  Four of them GUARDED on RR; two of them exactly as stated.
;;;
;;; structure-library/order-lemmas.scm:179-203 asserts, as `well-known' supports,
;;; the six order/equality compositions the `calc' order composer folds through
;;; (calc.scm:51-57).  All six are UNTYPED, and the comment above them says so
;;; deliberately: "so a forward `fact' discharges both order antecedents from
;;; context with no RR typing guard".
;;;
;;; The four genuine ORDER compositions
;;;
;;;     co-le-trans      a <= b  =>  b <= c  =>  a <= c   (REMOVED 2026-09-20:
;;;                      a duplicate of rr-le-trans-c, nn-order-basics.scm)
;;;     co-lt-trans      a <  b  =>  b <  c  =>  a <  c
;;;     co-le-lt-trans   a <= b  =>  b <  c  =>  a <  c
;;;     co-lt-le-trans   a <  b  =>  b <= c  =>  a <  c
;;;
;;; are NOT provable as stated.  Nothing in the theory constrains `<=' or `<'
;;; off the numeric chain, so the untyped form asserts transitivity of a GLOBAL
;;; relation -- the same defect nn-order-basics.scm records for the old
;;; unguarded `nn-le-trans' ("strictly stronger than anything the axioms
;;; license").  Guarded on RR each is one citation of the corresponding proven
;;; RR lemma, or equivalently one Farkas certificate from the `ineq' oracle,
;;; which is what is done below.  The antecedents stay CURRIED, as the supports
;;; have them, so a forward `fact' still auto-detaches both order premises; only
;;; the three typings are new.
;;;
;;; The two EQUALITY links
;;;
;;;     co-le-eq-trans   a <= b  =>  b =  c  =>  a <= c
;;;     co-eq-le-trans   a =  b  =>  b <= c  =>  a <= c
;;;
;;; are a different species and need NO guard: each is one Leibniz rewrite of
;;; the goal by the equation in context (`subst', pi-eq-subst! on the partial
;;; `='), after which the goal IS the other hypothesis.  No order axiom is used,
;;; so the statement is proven UNCHANGED, character for character.  This is
;;; exactly theorem-library/co-eq-lt-trans.scm's argument for the strict
;;; siblings co-eq-lt-trans / co-lt-eq-trans, and this file is its `<=' half.
;;;
;;; `subst' finds the equation in the context in EITHER orientation and rewrites
;;; left-to-right in the goal, so co-le-eq-trans names (= c b) against the
;;; hypothesis (= b c); no symmetry citation is needed.
;;;
;;; MEASURED ON THE BAND (2026-09-15, worker-01), which is the point of this
;;; file.  Every citation site of the six names in the tree, with the four
;;; citing files re-run against the guarded statements:
;;;
;;;   co-le-trans      4 sites   ord-segment-arith:73, pigeonhole-segments:170,
;;;                              poly-degree-laws:425, poly-degree-laws:625
;;;                              (all four now cite rr-le-trans-c)
;;;   co-le-lt-trans   5 sites   finite-surgery:123/170/201,
;;;                              pigeonhole-segments:301, poly-degree-laws:843+844
;;;   co-lt-trans / co-lt-le-trans / co-le-eq-trans / co-eq-le-trans
;;;                    0 sites   named only by calc.scm's composer table
;;;
;;; Unpatched, each of the four files dies at its FIRST citation: `fact' lands
;;; the implication instead of detaching, and the driver runs on.  Patched with
;;; the typing lines -- 30 `fact' calls on 10 lines, all of them nn-in-rr (22),
;;; nn-succ-closed (4), rr-zero-in (3), rr-one-in (1) -- all 30 theorems of the
;;; four files close, and the 14 that billed a co-* leaf bill `modulo 0'.  Every
;;; argument at every site is NN-typed in context already, or one nn-succ-closed
;;; away, or a numeric literal; no site needs a fact the file does not have.
;;; The patches are in scratchpad/co-guard-patches/.
;;;
;;; The three library files that USE `calc' (nn-mod3-proof, nn-integral,
;;; dyadic-weights) were re-run UNPATCHED against the guarded statements and are
;;; unaffected: their chains compose through co-eq-lt-trans / co-lt-eq-trans /
;;; eq-trans, the equality links, never through the four order ones.  But a calc
;;; order chain over NN-typed terms DOES break -- see the machinery note below.
;;;
;;; LOAD WINDOW, by FILE NAME.
;;;   after   theorem-library/rr-order-basics   (rr-lt-trans, rr-lt-le-trans,
;;;           rr-le-lt-trans) and theorem-library/nn-order-basics
;;;           (rr-le-trans-c) -- though in fact only the `ineq' oracle and
;;;           driver-kit are used, so structure-library/ineq-oracle suffices.
;;;   before  calc (the composer that names all six) and, among the proof
;;;           files, theorem-library/ord-segment-arith, the earliest citer.
;;;
;;; Helper prefix: cog-.

;;; ---- helpers -----------------------------------------------------------

;; The 1-based indices of the ORDER-shaped assumptions -- what `ineq' wants.
;; An `=' is deliberately NOT collected: an equation is arithmetic in SHAPE, so
;; it contributes atoms to the certificate, and here every proof that has one
;; closes by `subst' instead.
(define (cog-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <=)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (#t (loop (cdr l) (+ i 1) acc)))))

(define (cog-ineq!) (apply ineq (cog-idx)))

;; peel the whole FORALL/IMPLIES prefix, then decide by Farkas.
(define (cog-farkas!) (dk-peel!) (cog-ineq!))

;;; ---- the four order compositions, GUARDED on RR ------------------------

;; (The <= / <= composition stood here as `co-le-trans'; REMOVED 2026-09-20,
;; batch 11: it was alpha-equal to `rr-le-trans-c'
;; (theorem-library/nn-order-basics.scm:104), which loads before this file and
;; before all four of co-le-trans's call sites.  The other five compositions
;; below have no twin.)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
     (FORALL c (IMPLIES (IN c RR)
       (IMPLIES (< a b) (IMPLIES (< b c) (< a c)))))))))))
(cog-farkas!)
(qed 'co-lt-trans)
(topic! 'co-lt-trans 'inequalities)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
     (FORALL c (IMPLIES (IN c RR)
       (IMPLIES (<= a b) (IMPLIES (< b c) (< a c)))))))))))
(cog-farkas!)
(qed 'co-le-lt-trans)
(topic! 'co-le-lt-trans 'inequalities)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
     (FORALL c (IMPLIES (IN c RR)
       (IMPLIES (< a b) (IMPLIES (<= b c) (< a c)))))))))))
(cog-farkas!)
(qed 'co-lt-le-trans)
(topic! 'co-lt-le-trans 'inequalities)

;;; ---- the two equality links, UNCHANGED (no guard needed) ---------------

;; co-le-eq-trans: rewrite c -> b in the goal, then it is a <= b.
(sp (make-wff '(FORALL a (FORALL b (FORALL c
   (IMPLIES (<= a b) (IMPLIES (= b c) (<= a c))))))))
(dk-peel!)
(subst '(= c b))
(ass)
(qed 'co-le-eq-trans)
(topic! 'co-le-eq-trans 'inequalities)

;; co-eq-le-trans: rewrite a -> b in the goal, then it is b <= c.
(sp (make-wff '(FORALL a (FORALL b (FORALL c
   (IMPLIES (= a b) (IMPLIES (<= b c) (<= a c))))))))
(dk-peel!)
(subst '(= a b))
(ass)
(qed 'co-eq-le-trans)
(topic! 'co-eq-le-trans 'inequalities)

;;; MACHINERY NOTE (measured, same session).  `calc--compose-order' (calc.scm:186)
;;; calls (fact lemma L0 prev Li) with no typing step, so once these four are
;;; guarded an order chain closes only when its endpoints are already RR-typed in
;;; context.  Probed four ways: an RR-typed two-step `<=' chain closes before and
;;; after; an NN-typed one closes before and FAILS after.  The fix is one line at
;;; the fold -- calc already owns the bridge it needs, `calc--nn-rr-bridge!'
;;; (calc.scm:83), which today runs only inside the link LANE
;;; (`calc--order-close!'), not before the composer's citation; a chain with a
;;; numeric literal endpoint wants `rr-zero-in' / `rr-one-in' too.
