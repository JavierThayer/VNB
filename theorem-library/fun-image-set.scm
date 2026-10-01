;;; fun-image-set.scm -- the image of ANY class under a function into a SET is a set,
;;; proven with no citation of `image-set' (replacement).
;;;
;;;   fun-image-set   f in FUN(A, B), B in SET  =>  IMAGE(f, S) in SET
;;;
;;; The user's item 3 of docs/decisions-pending-2026-10-01.md.  The form proposed
;;; there, `f in FUN(A, B), S in SET => IMAGE(f, S) in SET', is NOT provable in
;;; this tree without replacement: an ordered pair is the primitive constructor
;;; LIST, not a Kuratowski set, so "the union of the second components of f's
;;; pairs" is not a term the axioms reach.  What IS provable is the subclass
;;; argument: every member of IMAGE(f, S) is f(x) for some x with f(x) defined,
;;; hence (fun-domain-apply-def) x in A, hence (fun-apply-type-c) f(x) in B; so
;;; IMAGE(f, S) is a subclass of the set B (subclass-of-set-is-set, separation).
;;; No hypothesis on S at all: a point of S outside A contributes nothing, since
;;; `f(x) = w' is a strict atom.
;;;
;;; Citations: image-membership-iff (definitional), fun-domain-apply-def and
;;; fun-codomain-iff (base theory), fun-apply-type-c
;;; (theorem-library/fun-apply-type-proof.scm), subclass-of-set-is-set
;;; (theorem-library/subset-lemmas.scm).  Load after subset-lemmas.
;;; Helper prefix: fis-.

(sp (make-wff '(FORALL A (FORALL B (FORALL f (FORALL S
      (IMPLIES (IN f (FUN A B))
        (IMPLIES (IN B SET)
                 (IN (IMAGE f S) SET)))))))))
(dk-peel!)                              ; lands (IN f (FUN A B)) and (IN B SET)
(dk-have! '(SUBSET (IMAGE f S) B)
  (lambda ()
    (mac 'subset-def)
    (dk-peel!)                          ; lands (IN w (IMAGE f S)) for the minted w
    (let* ((fis-w  (cadr (dk-goal)))
           (fis-ex (dk-image-hyp! (list 'IN fis-w '(IMAGE f S))))
           (fis-x  (dk-skolem! fis-ex)))
      ;; context now: fis-x in S, f(fis-x) = w, w in SET.  First fis-x in A.
      ;; (IN f (FUN A)) on a lane: fun-apply-type-c below still wants (IN f (FUN A B))
      (dk-have! '(IN f (FUN A))
        (lambda ()
          (dk-split! (dk-landed-1 (lambda () (mac-h 'fun-codomain-iff '(IN f (FUN A B))))))
          (ass)))
      (dk-have! (list 'IN fis-x 'A)
        (lambda ()
          (fact 'fun-domain-apply-def 'A 'f fis-x)
          (dk-split! (list 'IFF (list '= (list 'f fis-x) (list 'f fis-x)) (list 'IN fis-x 'A)))
          (dk-have! (list '= (list 'f fis-x) (list 'f fis-x)) (lambda () (rfl)))
          (detach! (list 'IMPLIES (list '= (list 'f fis-x) (list 'f fis-x)) (list 'IN fis-x 'A)))
          (ass)))
      (fact 'fun-apply-type-c 'f 'A 'B fis-x)
      (subst (list '= fis-w (list 'f fis-x)))
      (ass))))
(fact 'subclass-of-set-is-set '(IMAGE f S) 'B)
(ass)
(qed 'fun-image-set)
(topic! 'fun-image-set 'plumbing)
