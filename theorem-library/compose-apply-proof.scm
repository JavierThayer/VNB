;;; compose-apply-proof.scm -- (COMPOSE f g)(x) = f(g(x)), PROVEN modulo 0.
;;;
;;; `compose-apply' was a `support' in structure-library/compose.scm carrying
;;; the TOP warrant tier, `proof', with the text
;;;
;;;   "Unfold COMPOSE to VNB-LAMBDA z. f(g(z)), then lambda-beta (lam-b):
;;;    ((VNB-LAMBDA z. f(g(z))) x) reduces to f(g(x)), and reflexivity closes
;;;    it.  The beta step needs no hypotheses; ..."
;;;
;;; -- a derivation written in prose and never run, the same species as
;;; `fun-apply-type-c' (theorem-library/fun-apply-type-proof.scm) and
;;; `integral-domain-nontrivial'.  It was, with `compose-type', the ENTIRE bill
;;; of `compose-continuous-at', `deriv-chain' and `deriv-inverse'.
;;;
;;; AND THE PROSE WAS WRONG on the one point that matters.  "The beta step needs
;;; no hypotheses" is false since the beta guard went in (2026-08-03):
;;; `pi-lambda-beta!' (primitive-inferences.scm:1404) licenses the redex only on
;;; the lambda's OWN domain, and COMPOSE's lambda is
;;;
;;;     VNB-LAMBDA z_ in DOM(g). f(g(z_))
;;;
;;; whose domain is DOM(g), NOT the A of the hypothesis (IN x A).  Worse, the
;;; obligation is POSTED against the outer context, so a `lam-b' fired without
;;; the typing still FIRES and silently owes (IN x (DOM g)) at a node that
;;; cannot discharge it; `qed' then reports an incomplete proof and names no
;;; step.  So the whole content of this file is the two lines that get
;;; (IN x (DOM g)) into the context BEFORE the beta.
;;;
;;; THE BRIDGE, and why the bill is still zero.  Two axioms of
;;; make-vnb-base-library, hence `primitive', hence contributing {} to the bill:
;;;
;;;   fun-codomain-iff    (library.scm:459)   f in FUN(A,B)  iff
;;;                                          f in FUN(A) and forall x in A. f(x) in B
;;;   dom-fun-membership  (library.scm:493)   f in FUN(A) => forall x. (x in DOM f iff x in A)
;;;
;;; The first, applied to the hypothesis, yields (IN g (FUN A)); the second then
;;; says DOM(g) and A have the same members, and (IN x A) is a hypothesis.
;;;
;;; WHICH EQUALITY.  The statement keeps the installed support's STRICT `=', not
;;; `=='.  Two reasons: the citing proofs (chain-rule, inverse-function,
;;; continuity-compose, sequential-continuity, product-weights,
;;; directional-derivative) all `fact' it and then `subst' with it, so weakening
;;; to `==' would move every one of them; and the strict form is what the typed
;;; hypotheses BUY -- `rfl' closes (f(g(x)) = f(g(x))) only against a definedness
;;; witness (asm-establishes-defined?, primitive-inferences.scm:594), which is
;;; exactly the (IN (f (g x)) C) landed by the second fun-apply-type-c citation.
;;; With `==' those two citations would be dead weight and `qrfl' would close
;;; unconditionally -- a weaker theorem for no gain.  The `==' form, guarded on
;;; (IN x (DOM g)) instead of typed, is the one test-suite.scm:3164 already runs.
;;;
;;; Needs: compose (COMPOSE, structure-library, far above), fun-apply-type-proof
;;; (fun-apply-type-c, just above), interactive/proof-debt (sp/qed) and
;;; driver-kit (dk-peel-to!, have!, dk-fact!).  Must precede every consumer of
;;; compose-apply -- the earliest is theorem-library/continuity-compose.

;; ---- file-local helpers (ca- prefix; never named like a tactic) -----------
;; Select assumptions by CONTENT, never by position: this file runs both from a
;; cold load and from a saved band, and landing ORDER is not stable across them.
(define (ca-asm what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ca-asm: no assumption is" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (ca-fun-asm fv arity)           ; (IN fv (FUN ...)) with `arity' args
  (ca-asm (list 'a 'FUN 'typing-of fv 'arity arity)
          (lambda (f)
            (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                 (equal? (cadr f) fv)
                 (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                 (= (length (caddr f)) (+ arity 1))))))

;;; compose-apply
(sp (make-wff
  '(FORALL A (FORALL B (FORALL C (FORALL f (FORALL g
     (IMPLIES (AND (IN g (FUN A B)) (IN f (FUN B C)))
       (FORALL x (IMPLIES (IN x A)
         (= ((COMPOSE f g) x) (f (g x)))))))))))))
(dk-peel-to! '=)
(ai '(AND (IN g (FUN a b)) (IN f (FUN b c))))
;; Both citations are load-bearing: the first supplies the antecedent of the
;; second, and the second is `rfl's definedness witness for f(g(x)).
(fact 'fun-apply-type-c 'g 'a 'b 'x)            ; (IN (g x) b)
(fact 'fun-apply-type-c 'f 'b 'c '(g x))        ; (IN (f (g x)) c)
(mac 'COMPOSE)                                  ; goal: ((VNB-LAMBDA z_ (DOM g) ...) x) = ...

;; The beta guard.  Read x and g off the GOAL rather than trusting the binder
;; names: (= ((VNB-LAMBDA z_ (DOM g) body) x) rhs).
(let* ((redex (cadr (dk-goal)))                 ; ((VNB-LAMBDA z_ (DOM g) body) x)
       (lam   (car redex))
       (arg   (cadr redex))
       (gv    (cadr (caddr lam))))              ; the g of DOM(g)
  (have! (list 'IN arg (list 'DOM gv))
    (lambda ()
      ;; fun-codomain-iff LEFT-TO-RIGHT on the FUN(A,B) hypothesis: the AND it
      ;; lands has (IN g (FUN A)) as its first conjunct.  `mac-h' REPLACES the
      ;; hypothesis, which is why this runs inside the have! lane -- the main
      ;; branch keeps (IN g (FUN a b)) intact.
      (dk-split! (dk-landed-1 (lambda () (mac-h 'fun-codomain-iff (ca-fun-asm gv 2)))))
      (let* ((fun1 (ca-fun-asm gv 1))           ; (IN g (FUN A))
             (dom  (cadr (caddr fun1))))        ; the A
        (inst+ (dk-fact! 'dom-fun-membership dom gv) arg)
        (ai (list 'IFF (list 'IN arg (list 'DOM gv)) (list 'IN arg dom)))
        (detach! (list 'IMPLIES (list 'IN arg dom) (list 'IN arg (list 'DOM gv))))
        (ass)))))

(lam-b)
(rfl)
(qed 'compose-apply)


;;; -----------------------------------------------------------------------
;;; compose-type -- g : A -> B and f : B -> C give f o g : A -> C, GUARDED on
;;; (IN A SET).  PROVEN modulo 0 (2026-08-23).  It was the LAST asserted leaf of
;;; fourteen bills and the sibling of compose-apply above; both were `support' +
;;; `warrant! proof' in structure-library/compose.scm, i.e. derivations written
;;; in prose and never run.
;;;
;;; WHY THE GUARD IS NOT OPTIONAL.  Unfolding COMPOSE gives the lambda
;;; VNB-LAMBDA z_ in DOM(g). f(g(z_)), so `lam-t' concludes membership in
;;; FUN(DOM(g), C).  Getting from there to FUN(A, C) is `dom-of-fun'
;;; (library.scm:500), whose second hypothesis is (IN A SET) -- and NOTHING IN
;;; THE TREE derives that from (IN g (FUN A B)).  Checked, not assumed:
;;;
;;;   * `fun-set-iff' (library.scm:412) is about FUN(A,B) BEING a set, not about
;;;     its having a member.
;;;   * `is-fun-def' (:479) quantifies its set domain EXISTENTIALLY, so it
;;;     delivers sethood of some witness, not of the A one already holds.
;;;   * `(IN (DOM f) SET)' occurs in exactly ONE place tree-wide -- inside
;;;     dom-of-fun itself, guarded on the very thing wanted.
;;;   * `lam-t' independently OPENS an (IN (DOM g) SET) leaf, so the sethood is
;;;     owed twice over.
;;;
;;; Mathematically the missing fact is REPLACEMENT (DOM(g) is the image of the
;;; set g under first-projection), and the step that is NOT available is naming
;;; that projection as a class function IMAGE can take.  Building it is set
;;; theory machinery; the guard is one hypothesis and it is true at every
;;; citation site.  "State the hypothesis, pay the migration" -- the citations
;;; are chain-rule.scm:245 and :248 (one rr-is-set serves both -- the context
;;; persists), inverse-function.scm:258, sequential-continuity.scm:189,
;;; product-weights.scm:223 and continuity-compose.scm:222.  Five sites, six
;;; citations, one line each.  Note product-weights: A there is NN, not the
;;; PTS(P1) the composite's OTHER arguments suggest -- the sequence is the
;;; second argument of COMPOSE, so the domain is the sequence's.
;;;
;;; The guard is the OUTERMOST antecedent, so `fact' detaches it first and the
;;; AND typing second -- both must be in context at the citation.

(sp (make-wff
  '(FORALL A (FORALL B (FORALL C (FORALL f (FORALL g
     (IMPLIES (IN A SET)
       (IMPLIES (AND (IN g (FUN A B)) (IN f (FUN B C)))
         (IN (COMPOSE f g) (FUN A C)))))))))))
(dk-peel-to! 'IN)

;;; Read A, C, f and g off the GOAL and B off g's typing -- never off the
;;; binder spellings, for the reason ca-asm above gives.
(let* ((g0    (dk-goal))                        ; (IN (COMPOSE f g) (FUN A C))
       (comp  (cadr g0))
       (fv    (cadr comp))
       (gv    (caddr comp))
       (funac (caddr g0))
       (av    (cadr funac))
       (cv    (caddr funac)))
  (dk-split! (ca-asm 'the-AND-antecedent (dk-head? 'AND)))
  (let ((bv (caddr (caddr (ca-fun-asm gv 2)))))  ; the B of (IN g (FUN A B))

    ;; (IN g (FUN A)) off fun-codomain-iff, in a have! LANE: `mac-h' REPLACES
    ;; the hypothesis and the main branch still needs (IN g (FUN A B)) intact.
    (have! (list 'IN gv (list 'FUN av))
      (lambda ()
        (dk-split! (dk-landed-1
                    (lambda () (mac-h 'fun-codomain-iff (ca-fun-asm gv 2)))))
        (ass)))

    ;; dom-of-fun has an AND antecedent, which `fact' will not split: assemble
    ;; the conjunction first (the ord-le-total rule).
    (have! (list 'AND (list 'IN gv (list 'FUN av)) (list 'IN av 'SET)))
    (dk-split! (dk-fact! 'dom-of-fun av gv))     ; (= (DOM g) A) and (IN (DOM g) SET)

    (mac 'COMPOSE)                               ; (IN (VNB-LAMBDA z_ (DOM g) ...) (FUN A C))
    ;; the DOM(g) here is a BINDER domain, which `subst's Leibniz walk does
    ;; reach -- it is not in operator position.
    (subst (list '= (list 'DOM gv) av))
    (dk-lam-t!)                                  ; closes the (IN A SET) leaf off the guard
    (di)
    (let* ((gz (cadr (cadr (dk-goal))))          ; (g z_)
           (z  (cadr gz)))
      (fact 'fun-apply-type-c gv av bv z)        ; (IN (g z_) B)
      (fact 'fun-apply-type-c fv bv cv gz)       ; (IN (f (g z_)) C)
      (ass))))

(qed 'compose-type)
