;;; card-singleton-proof.scm -- the cardinality of a singleton is 1, proven.
;;;
;;;     forall x.  x in SET  =>  CARD(PAIR(x, x)) = succ 0
;;;
;;; In VNB the singleton {x} is (PAIR x x) -- the Kuratowski convention
;;; degenerates to {{x}} -- and 1 is succ 0.  The support of the same name
;;; lives in theorem-library/card-singleton.scm (a PSS-promoted stub whose
;;; archived script predates the E->IDEN rename); this file is named `-proof'
;;; only because that stub holds the name.
;;;
;;; PLAN.  card-insert (primitive, structure-library/cardinality.scm:53) at
;;; A := EMPTY-SET:
;;;     CARD(EMPTY-SET u {x}) = succ_ORD(CARD EMPTY-SET)
;;; needs EMPTY-SET in SET (empty-set-is-set) and x in SET, x not in EMPTY-SET
;;; (empty-set-has-no-members).  Then three rewrites of the goal:
;;;     {x}            -> EMPTY-SET u {x}    class-extensionality + union-membership
;;;                                          (the archive cited the `informal'
;;;                                          support union-empty-left; not here)
;;;     CARD(...)      -> succ_ORD(CARD EMPTY-SET)   card-insert
;;;     CARD EMPTY-SET -> 0                          card-empty (primitive)
;;; and the goal  succ_ORD 0 = succ 0  is ord-succ-nn (primitive) at 0.
;;;
;;; WINDOW.  Every citation is a base axiom (library.scm), a cardinality
;;; primitive (structure-library/cardinality) or an ordinal primitive
;;; (structure-library/ordinals), so lo = any theorem-library slot after
;;; driver-kit / proof-debt.  hi = theorem-library/makeset-basics, the earliest
;;; `fact' of card-singleton (founder-warrants only re-warrants it).
;;;
;;; Helper prefix: cs-.

;; Drop every assumption but the named ones (a lane-local `wk' sweep, as
;; fin-subsets' fs-only! does): `prop' has an atom cap and `fact' lands its
;; whole instantiation chain.
(define (cs-only! . keepers)
  (for-each (lambda (f) (if (not (member f keepers)) (wk f))) (dk-asms)))

(sp (make-wff '(FORALL x (IMPLIES (IN x SET)
     (= (CARD (PAIR x x)) (succ 0))))))
(di)                                          ; lands (IN x SET)

;; EMPTY-SET u {x} = {x}, by class-extensionality.  Done FIRST, while the
;; context is small.  The extensionality binder is renamed away from our x, so
;; the eigenvariable is read off the goal rather than guessed.
(have! '(= (UNION EMPTY-SET (PAIR x x)) (PAIR x x))
  (lambda ()
    (bc* 'class-extensionality)               ; goal: forall v. v in U iff v in {x}
    (di)
    (let* ((g (dk-goal))
           (v (cadr (cadr g))))               ; (IFF (IN v ...) (IN v ...))
      (fact 'union-membership 'EMPTY-SET '(PAIR x x) v)
      (fact 'empty-set-has-no-members v)
      (cs-only! (list 'IFF (list 'IN v '(UNION EMPTY-SET (PAIR x x)))
                      (list 'OR (list 'IN v 'EMPTY-SET) (list 'IN v '(PAIR x x))))
                (list 'NOT (list 'IN v 'EMPTY-SET)))
      (prop))))

;; card-insert at A := EMPTY-SET.  Since 2026-09-18 it also asks that A be
;; FINITE (structure-library/cardinality.scm: unguarded it is false of an
;; infinite A once CARD is the least ordinal in bijection); here CARD(EMPTY-SET)
;; is 0 by card-empty, so the guard is two lines.
(fact 'empty-set-is-set)                      ; (IN EMPTY-SET SET)
(fact 'empty-set-has-no-members 'x)           ; (NOT (IN x EMPTY-SET))
(fact 'card-empty)                            ; (= (CARD EMPTY-SET) 0)
(fact 'nn-zero-in)                            ; (IN 0 NN)
(have! '(IN (CARD EMPTY-SET) NN)
       (lambda () (subst '(= (CARD EMPTY-SET) 0)) (ass)))
(have! '(AND (IN x SET) (NOT (IN x EMPTY-SET))))
(fact 'card-insert 'EMPTY-SET 'x)             ; (= (CARD (UNION EMPTY-SET (PAIR x x))) (succ_ORD (CARD EMPTY-SET)))
(fact 'ord-succ-nn 0)                         ; (= (succ_ORD 0) (succ 0))

;; assemble
(subst '(= (PAIR x x) (UNION EMPTY-SET (PAIR x x))))          ; goal: CARD(EMPTY-SET u {x}) = succ 0
(subst '(= (CARD (UNION EMPTY-SET (PAIR x x))) (succ_ORD (CARD EMPTY-SET))))
(subst '(= (CARD EMPTY-SET) 0))                               ; goal: succ_ORD 0 = succ 0
(ass)
(qed 'card-singleton)
(topic! 'card-singleton 'plumbing)
