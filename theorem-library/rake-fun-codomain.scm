;;; theorem-library/rake-fun-codomain.scm -- codomain widening for FUN, PROVEN.
;;;
;;;   fun-codomain-superset   f in FUN(A,B), B subset C  =>  f in FUN(A,C)
;;;
;;; STATEMENT copied literally from its declaration site,
;;; theorem-library/noetherian-maximal-proof.scm:29 (add-to-pss).
;;; Sole leaf on the bill of `noetherian-set-has-maximal', and through it on the
;;; Hahn-Banach bills that consume hb-good-has-maximal.
;;;
;;; THE DOOR is `fun-codomain-iff' (library.scm:459, a base-library axiom):
;;;
;;;   f in FUN(A,B)  iff  f in FUN(A)  and  forall x in A. f(x) in B
;;;
;;; so the codomain is not part of the object -- it is a PREDICATE on the values.
;;; Widening is therefore not a FUN fact at all: it is the pointwise typing
;;; pushed along an inclusion, one `subset-mem-fwd' per value.  The proof:
;;; unfold the hypothesis with `mac-h' (the iff left-to-right), unfold the GOAL
;;; with `mac' (the iff right-to-left), close the FUN(A) conjunct by `ass', and
;;; on the pointwise conjunct peel one point and chase it B -> C.
;;;
;;; That is why CLAUDE.md's "no FUN codomain-widening lemma" was an item on the
;;; open-foundations list and not a gap in the foundations: the tree had every
;;; brick, and nobody had put the four of them together.  No new support, no
;;; stamp; `subset-mem-fwd' and `fun-codomain-iff' are both modulo 0.
;;;
;;; NOTE ON C.  No sethood guard is needed or wanted.  `IN f (FUN A C)' is
;;; characterised by the iff above, whose right-hand side is a membership
;;; statement about the VALUES; C may be a proper class and the statement stays
;;; true (and its citer in noetherian-maximal-proof instantiates C at
;;; POWER(VEC m), a set, so nothing downstream needs the general case either).
;;;
;;; LOAD WINDOW.  After theorem-library/subset-lemmas (subset-mem-fwd);
;;; fun-codomain-iff is a base-library axiom, so it imposes no floor.  Before
;;; theorem-library/noetherian-maximal-proof, the only citer.

;;; --------------------------------------------------------------------
;;; File-local helpers (the `rfc-' prefix; never named like a tactic).

;;; The unique context assumption that types f in a TWO-argument FUN.  Named on
;;; its shape rather than rebuilt, so the eigenvariables `di' actually minted
;;; are the ones we work with.
(define (rfc-fun2? fv)
  (lambda (fm)
    (and (pair? fm) (eq? (car fm) 'IN) (equal? (cadr fm) fv)
         (pair? (caddr fm)) (eq? (car (caddr fm)) 'FUN)
         (= (length (caddr fm)) 3))))

;;; --------------------------------------------------------------------
(sp (make-wff '(FORALL f (FORALL A (FORALL B (FORALL C
     (IMPLIES (IN f (FUN A B)) (IMPLIES (SUBSET B C) (IN f (FUN A C))))))))))
(dk-peel!)

;; Read every name off the peeled goal / context; never off the binder spelling.
(define rfc-goal (dk-goal))                      ; (IN f (FUN A C))
(define rfc-f (cadr rfc-goal))
(define rfc-a (cadr (caddr rfc-goal)))
(define rfc-c (caddr (caddr rfc-goal)))
(define rfc-sub (dk-pick (dk-head? 'SUBSET) "the SUBSET hypothesis"))
(define rfc-b (cadr rfc-sub))
(define rfc-hyp (dk-pick (rfc-fun2? rfc-f) "the FUN(A,B) hypothesis"))

;; fun-codomain-iff LEFT-TO-RIGHT on the hypothesis.  `mac-h' REPLACES it, by
;; design: nothing below needs (IN f (FUN A B)) itself, only its two conjuncts.
(define rfc-parts
  (dk-split! (dk-landed-1 (lambda () (mac-h 'fun-codomain-iff rfc-hyp)))))

;; Pick the pointwise universal out of what THIS split produced.
(define rfc-ptwise
  (let loop ((l rfc-parts))
    (cond ((null? l) (error "rfc: fun-codomain-iff landed no pointwise universal"))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL)) (car l))
          (#t (loop (cdr l))))))

;; fun-codomain-iff RIGHT-TO-LEFT on the goal: (IN f (FUN A C)) becomes the AND.
(mac 'fun-codomain-iff)

(for-each
 (lambda (rfc-leaf)
   (dk-focus! rfc-leaf)
   (let ((g (dk-goal)))
     (if (and (pair? g) (eq? (car g) 'FORALL))
         ;; the pointwise conjunct: peel one point and chase its value B -> C
         (let* ((rfc-landed (dk-peel!))
                (rfc-pt (cadr (dk-pick (lambda (fm)
                                         (and (member fm rfc-landed)
                                              (pair? fm) (eq? (car fm) 'IN)
                                              (equal? (caddr fm) rfc-a)))
                                       "the point typing (IN x A)"))))
           (dk-apply! rfc-ptwise rfc-pt)                     ; (IN (f x) B)
           (fact 'subset-mem-fwd rfc-b rfc-c (list rfc-f rfc-pt))
           (ass))
         ;; the (IN f (FUN A)) conjunct: already in context
         (ass))))
 (dk-opened (lambda () (di))))

(qed 'fun-codomain-superset)
(topic! 'fun-codomain-superset 'plumbing)
