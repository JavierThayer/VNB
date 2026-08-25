;;; subsqn-basics.scm -- the SUBSQN relation and what is proven about it.
;;;
;;; SUBSQN(y, f) ("y is a subsequence of f") is defined in
;;; theorem-library/cauchy-subsequence.scm, which loads at load.scm:314 -- before
;;; `interactive', so it can carry the `def-predicate' but no proof.  This file
;;; carries the proofs.
;;;
;;; WHY THE RELATION IS SPACE-FREE, and why that is the point.  IS-SUBSEQUENCE(s,
;;; y, f) conflates a TYPING (f : NN -> PTS(s)) with a RELATION (y reindexes f).
;;; "y = f o phi for a strictly monotone phi" is a statement about two sequences
;;; and nothing else.  Measured before this file was written: IS-SUBSEQUENCE has
;;; ZERO citations in the tree, while five theorems in the same arc write its
;;; body out longhand with the typing dropped.  SUBSQN is that body, named.

;;; is-subsequence-iff-typed-subsqn: the two are the same thing, once the typing
;;; is written separately.  Both sides unfold by their defining IFFs and what is
;;; left is propositional.
(sp (make-wff
  '(FORALL s (FORALL y (FORALL f
     (IFF (IS-SUBSEQUENCE s y f)
          (AND (IN f (FUN NN (PTS s))) (SUBSQN y f))))))))
(di)
(mac 'is-subsequence)
(mac 'subsqn)
(prop)
(qed 'is-subsequence-iff-typed-subsqn)
(topic! 'is-subsequence-iff-typed-subsqn 'analysis)
(alias! 'is-subsequence-iff-typed-subsqn
        "IS-SUBSEQUENCE is a typing plus the space-free subsequence relation")

;;; -----------------------------------------------------------------------
;;; subsqn-preserves-sqn: a subsequence of a sequence in `a' is a sequence in
;;; `a'.  The CLOSURE property, and the reason it is worth proving rather than
;;; assuming: `subseq-is-fun' (cauchy-subsequence.scm) says exactly this and
;;; says it only for `PTS(s)' -- a metric space's carrier -- and says it as an
;;; ASSERTED support.  For a general class `a', which is what SQN(a) ranges
;;; over, the tree had nothing.
;;;
;;; It is NOT a consequence of the definition alone.  `SUBSEQ(f,phi)' is
;;; `VNB-LAMBDA k NN. f(phi k)', and a VNB-LAMBDA is a function only by `lam-t',
;;; which owes TWO leaves: the domain is a set, and the body is pointwise in the
;;; codomain.  So this proof is exactly those two obligations discharged --
;;; `nn-is-set' for the first, and `fun-apply-type-c' twice for the second
;;; (phi(k) in NN from phi : NN -> NN, then f(phi k) in a from f : NN -> a).
;;;
;;; Eigenvariables are READ OFF the context, never predicted: the fresh-variable
;;; counter depends on every proof that ran before this one.
(define (sub-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (sub-find pred)
  (let loop ((as (sub-asms)))
    (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))

(sp (make-wff-from-string
  "forall([a, f, y], f in sqn(a) implies subsqn(y, f) implies y in sqn(a))"))
(di)(di)(di)
(mac-h 'sqn-membership '(in f (sqn a)))
(mac-h 'subsqn '(subsqn y f))
(ai '(forsome phi (and (strictly-mono-nn phi) (= y (subseq f phi)))))
(ai 1)
(define sub-mono (sub-find (lambda (x) (and (pair? x) (eq? (car x) 'strictly-mono-nn)))))
(define sub-phi  (cadr sub-mono))
(subst (sub-find (lambda (x) (and (pair? x) (eq? (car x) '=)))))
(mac 'sqn-membership)
(mac 'subseq)
(lam-t)
;; leaf 1 -- the pointwise typing
(di)
(define sub-k
  (let loop ((as (sub-asms)))
    (cond ((null? as) #f)
          ((and (pair? (car as)) (eq? (car (car as)) 'in)
                (eq? (caddr (car as)) 'nn) (symbol? (cadr (car as))))
           (cadr (car as)))
          (else (loop (cdr as))))))
(mac-h 'strictly-mono-nn sub-mono)
(ai (sub-find (lambda (x) (and (pair? x) (eq? (car x) 'and)))))
(apply fact 'fun-apply-type-c (list sub-phi 'nn 'nn sub-k))
(apply fact 'fun-apply-type-c (list 'f 'nn 'a (list sub-phi sub-k)))
(ass)
;; leaf 2 -- the domain is a set
(ta 'nn-is-set)
(ass)
(qed 'subsqn-preserves-sqn)
(topic! 'subsqn-preserves-sqn 'analysis)
(alias! 'subsqn-preserves-sqn
        "a subsequence of a sequence in a is a sequence in a")

;;; -----------------------------------------------------------------------
;;; WHAT IS NOT HERE, and what each one costs.  Both are the facts that would
;;; make SUBSQN worth having as a named relation rather than an abbreviation,
;;; and neither is free:
;;;
;;; REFLEXIVITY, SUBSQN(f, f).  Needs a strictly monotone identity on NN, and
;;; the tree has no identity-function constructor at all (`bijection-compose'
;;; writes `vnb-lambda(x_, x, psi(phi(x_)))' inline rather than composing with
;;; one).  `VNB-LAMBDA k NN. k' is strictly monotone by `lam-t' plus beta, but
;;; then `f = SUBSEQ(f, id)' is an ETA law -- f versus `VNB-LAMBDA k NN. f(k)' --
;;; and that is function extensionality on FUN(NN, _), not a rewrite.
;;;
;;; TRANSITIVITY, SUBSQN(a,b) and SUBSQN(b,c) implies SUBSQN(a,c).  Needs
;;;   SUBSEQ(SUBSEQ(f, phi), psi) = SUBSEQ(f, COMPOSE(phi, psi))
;;; and the composition of two strictly monotone maps being strictly monotone.
;;; The first is a `lam-b' through nested VNB-LAMBDAs, which per CLAUDE.md needs
;;; the ARGUMENT TYPED first -- `(IN (psi k) NN)`, available from
;;; `psi in FUN(NN,NN)' -- so it is provable but it is a proof, not a rewrite.
;;; `COMPOSE' with `compose-apply' / `compose-type' (both PROVEN) is already
;;; there to state it with.
;;;
;;; Until those land, SUBSQN is a name for a formula rather than a relation with
;;; an algebra, and `subsequence-principle' keeps its nested-SUBSEQ statement.
