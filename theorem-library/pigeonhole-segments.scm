;;; pigeonhole-segments.scm -- Track A of the CARD plan: finite pigeonhole for
;;; ordinal segments, the one piece of real mathematics the plan needs.
;;;
;;; WHY.  CARD is axiomatised rather than defined (cardinality.scm's own header
;;; says so).  Defining it -- CARD(A) = the least ordinal in bijection with A --
;;; makes `card-segment' (CARD(ORD-SEGMENT n) = n) a THEOREM, and its proof is:
;;; the identity bijection witnesses existence at alpha = n, and PIGEONHOLE
;;; kills every beta < n.  With `ord-well-ordered' (PROVEN modulo 0) supplying
;;; leastness, pigeonhole is the whole remaining content of the finite layer --
;;; and the library does not have it.  The only pigeonhole fact installed is
;;; `pigeonhole-infinite', which is the infinite statement and no use here.
;;;
;;; WHERE THIS FILE STOPS, and why that is the honest place.  The base case is
;;; below and is proven.  The INDUCTION STEP -- from "no injection
;;; S(succ n) -> S(n)" to "no injection S(succ(succ n)) -> S(succ n)" -- needs a
;;; map this library does not have: the COLLAPSE of S(succ n) minus a point onto
;;; S(n) (identity below the removed point, predecessor above it).  `delete-at'
;;; (bijection.scm) is the closest thing and is the wrong surgery: it removes a
;;; point of the DOMAIN of a function, and is stated only for a PERMUTATION of
;;; S(succ n) that sends the removed index to n.  The collapse wants a point of
;;; the CODOMAIN removed, for an arbitrary injection.  Written as a
;;; `def-functoid' with an IF body it is definitional and costs no debt --
;;; that is the next rung, and it is a rung, not a step.

;;; --------------------------------------------------------------------
;;; ORD-SEGMENT(0) is empty.
;;;
;;; Was a warranted support (theorem-library/ord-segment-zero-no-members.scm,
;;; PSS-promoted 2026-05-27 with its machine proof archived).  It is the leaf
;;; both lemmas below would otherwise bill, and it is four citations deep:
;;; k in S(0) gives <_ORD k 0 -- ord-segment-membership, once 0 is typed in ORD
;;; -- which is <=_ORD k 0 plus k /= 0 (ord-lt-iff); ord-zero-least supplies
;;; <=_ORD 0 k; ord-le-antisymm closes it to k = 0, against k /= 0.
;;;
;;; It is proven HERE rather than in its own file because that file loads inside
;;; the block of pure `support' declarations, eighty entries before the tactic
;;; layer exists.
(sp (make-wff '(FORALL k (NOT (IN k (ORD-SEGMENT 0))))))
(di)                          ; the FORALL
(di)                          ; the NOT: assume k in S(0), prove FALSITY
(fact 'nn-zero-in)
(fact 'nn-subset-ord 0)       ; 0 in ORD, which ord-segment-membership wants
(mac-h 'ord-segment-membership '(IN k (ORD-SEGMENT 0)))
(mac-h 'ord-lt-iff '(<_ORD k 0))
(dk-split! '(AND (<=_ORD k 0) (NOT (= k 0))))
(fact 'ord-le-closure 'k 0)
(dk-split! '(AND (IN k ORD) (IN 0 ORD)))
(fact 'ord-zero-least 'k)
(have! '(AND (<=_ORD k 0) (<=_ORD 0 k)))
(fact 'ord-le-antisymm 'k 0)
(ai '(NOT (= k 0)))
(qed 'ord-segment-zero-no-members)
(category! 'ord-segment-zero-no-members 'set-theory)

;;; --------------------------------------------------------------------
;;; Nothing maps into the empty segment.
;;;
;;; ORD-SEGMENT(0) has no members, so a function into it cannot be applied at
;;; any point of an inhabited domain.  Stated as an absurdity rather than as
;;; "the domain is empty" because that is the shape every consumer wants: land
;;; the two typings, get FALSITY.
(sp (make-wff '(FORALL a (FORALL f (FORALL x
     (IMPLIES (IN f (FUN a (ORD-SEGMENT 0)))
       (IMPLIES (IN x a) FALSITY)))))))
(di) (di) (di)
(fact 'fun-apply-type-c 'f 'a '(ORD-SEGMENT 0) 'x)
(fact 'ord-segment-zero-no-members '(f x))
(ai '(NOT (IN (f x) (ORD-SEGMENT 0))))
(qed 'fun-into-seg-zero-absurd)
(category! 'fun-into-seg-zero-absurd 'set-theory)

;;; --------------------------------------------------------------------
;;; PIGEONHOLE, base case: no injection from S(1) into S(0).
;;;
;;; S(succ 0) contains 0 (the segment-successor iff, right disjunct), and an
;;; injection is in particular a function, so the lemma above applies.  The
;;; injectivity clause is never used -- at this rung a plain function already
;;; contradicts -- and that is worth noticing: the base case of pigeonhole is
;;; not about injectivity at all.
(sp (make-wff '(FORALL f
     (NOT (IN f (INJECTION (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0)))))))
(di)                       ; the FORALL
(di)                       ; a NOT goal: assume the positive, prove FALSITY
(mac-h 'injection-membership-iff
       '(IN f (INJECTION (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0))))
(dk-split! '(AND (IN f (FUN (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0)))
                 (FORALL a (IMPLIES (IN a (ORD-SEGMENT (succ 0)))
                   (FORALL b (IMPLIES (IN b (ORD-SEGMENT (succ 0)))
                     (IMPLIES (= (f a) (f b)) (= a b))))))))
(fact 'nn-zero-in)
(have! '(IN 0 (ORD-SEGMENT (succ 0)))
       (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
(fact 'fun-into-seg-zero-absurd '(ORD-SEGMENT (succ 0)) 'f 0)
(ass)
(qed 'no-injection-seg-1-into-seg-0)
(category! 'no-injection-seg-1-into-seg-0 'set-theory)
