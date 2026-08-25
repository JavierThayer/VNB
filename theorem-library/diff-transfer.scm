;;; diff-transfer.scm -- differentiability reads only the VALUES: a map that
;;; agrees pointwise with a map differentiable at a is itself differentiable at
;;; a, with the same derivative.  PROVEN, `modulo 0'.
;;;
;;;   f in FUN(RR,RR),  IS-DIFF-AT(g,a,L),  f(x) = g(x) for every real x
;;;      =>  IS-DIFF-AT(f,a,L)
;;;
;;; It is the exact mirror of `cont-transfer-ptwise-eq'
;;; (theorem-library/continuity-transfer.scm) one storey up, and it exists for
;;; the same reason.  The differentiation rules conclude about SYNTAX:
;;; `deriv-product' concludes about the literal term
;;; (VNB-LAMBDA x RR (* (f x) (g x))), not about "any map that happens to be
;;; the product.  The function actually in hand -- in the power rule, the
;;; monomial (VNB-LAMBDA x RR (power x (succ (succ n)))) -- is some other term
;;; that agrees with it at every point.  Without a transfer the rules can only
;;; ever conclude about lambdas they built themselves, and an induction that
;;; feeds a rule's own conclusion back into the next rung is impossible.
;;;
;;; THE PROOF IS THE OBSERVATION THAT THE WITNESS DOES NOT MOVE.  Caratheodory
;;; differentiability at a is
;;;
;;;     forsome phi.  phi continuous at a,  phi(a) = L,
;;;                   f(x) - f(a) = phi(x) * (x - a)   for all real x
;;;
;;; and the whole of phi's job -- its FUN typing, its continuity, its value at
;;; a -- is about phi alone.  Only the last conjunct mentions the function, and
;;; there f(x) and f(a) are rewritten to g(x) and g(a) by two instances of the
;;; pointwise hypothesis.  So the same phi that witnesses g's differentiability
;;; witnesses f's, and the proof cites no continuity lemma, no arithmetic and
;;; no closure fact: `ew' the skolemized phi, discharge four conjuncts by `ass',
;;; and close the fifth with two `subst'.
;;;
;;; WHERE IT CAME FROM.  It was proved inside
;;; theorem-library/directional-derivative.scm (load.scm:1825+) and MOVED here
;;; 2026-08-23, because theorem-library/deriv-power.scm needs it and loads
;;; several hundred entries earlier.  One theorem, one proof: the alternative --
;;; a second `=' -shaped copy under another name -- is the duplication this tree
;;; keeps paying for elsewhere.  directional-derivative.scm keeps the
;;; `dd-consequent-head?' helper the block defined, which three of its later
;;; proofs use.
;;;
;;; WHY THE HYPOTHESIS (IN f (FUN RR RR)) IS NOT REDUNDANT.  IS-DIFF-AT's first
;;; conjunct is the FUN typing of its subject, and pointwise agreement with a
;;; function does NOT establish it: `f' is a function VARIABLE here, and
;;; (f x) = (g x) for x in RR says nothing about f off RR or about f being a
;;; set of pairs at all.  Every caller has the typing to hand anyway (in the
;;; power rule it is `pow-lam-in-fun'), so it costs nothing.
;;;
;;; Needs differentiation (IS-DIFF-AT) and the tactic surface; must precede
;;; deriv-power, its first consumer.

;;; ---- file-local driver helpers (the `dt-' prefix; never named like a
;;; tactic, and every assumption selected by CONTENT, not by position) ------

;; split every conjunctive / existential assumption, skolemizing the FORSOME
(define (dt-split!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME))))
                         (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))

;; the assumption (= (PHI pt) VAL) names the skolem factor PHI
(define (dt-phi-for pt val)
  (let ((h (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                      (equal? (caddr a) val)
                                      (pair? (cadr a)) (= (length (cadr a)) 2)
                                      (equal? (cadr (cadr a)) pt)))
                     (dk-asms))))
    (if h (car (cadr h)) (error "dt-phi-for: no factor assumption for" val))))

;; the Caratheodory factorization universal mentioning PHI
(define (dt-diffid phi)
  (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a phi)))
                (dk-asms))
      (error "dt-diffid: no factorization assumption for" phi)))

;;; ---- diff-transfer-ptwise-eq --------------------------------------------
;;; Argument order mirrors cont-transfer-ptwise-eq: f is the map CONCLUDED
;;; about, g the map already known differentiable.
;;; Statement reproduced VERBATIM from theorem-library/directional-derivative.scm,
;;; where it stood until 2026-08-23 -- the `==' (quasi-equality) hypothesis
;;; included.  `==' is the WEAKER hypothesis, hence the stronger theorem, and it
;;; is what a beta law hands you; the conclusion's own (IN f (FUN RR RR)) makes f
;;; total on RR, so on RR the two readings coincide.
(sp (make-wff
     '(FORALL f (FORALL g (FORALL a (FORALL dl
        (IMPLIES (IN f (FUN RR RR))
        (IMPLIES (IS-DIFF-AT g a dl)
        (IMPLIES (FORALL x_ (IMPLIES (IN x_ RR) (== (f x_) (g x_))))
                 (IS-DIFF-AT f a dl))))))))))
(dk-peel-to! 'IS-DIFF-AT)

;;; Read the three eigenvariables off the GOAL, not off the context.
(define dt-pt  (caddr (dk-goal)))                ; the point a
(define dt-val (cadddr (dk-goal)))               ; the derivative L
(define dt-f   (cadr (dk-goal)))                 ; the map concluded about

;;; The two universals in this context share the FORALL/IMPLIES shape, so they
;;; are told apart on the CONSEQUENT's head -- `==' for the pointwise
;;; hypothesis, `=' for g's Caratheodory identity.
(define (dt-consequent-head? h)
  (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                    (pair? (caddr fm)) (eq? (car (caddr fm)) 'IMPLIES)
                    (pair? (caddr (caddr fm)))
                    (eq? (car (caddr (caddr fm))) h))))
(define dt-pw
  (or (any-pred (dt-consequent-head? '==) (dk-asms))
      (error "diff-transfer: no pointwise hypothesis")))

(define dt-hyp
  (or (any-pred (dk-head? 'IS-DIFF-AT) (dk-asms))
      (error "diff-transfer: no IS-DIFF-AT hypothesis")))
(define dt-g (cadr dt-hyp))                      ; the map already known differentiable
(mac-h 'IS-DIFF-AT dt-hyp)
(dt-split!)
(define dt-phi (dt-phi-for dt-pt dt-val))

(mac 'IS-DIFF-AT)
(di) (ass)                                       ; (IN f (FUN RR RR))  -- hypothesis
(di) (ass)                                       ; (IN a RR)           -- from g's unfold
(di) (ass)                                       ; (IN L RR)           -- ditto
(ew dt-phi)                                      ; the SAME witness serves
(di) (ass)                                       ; phi in FUN(RR,RR)
(di) (ass)                                       ; phi continuous at a
(di) (ass)                                       ; phi(a) = L
;; the one conjunct that mentions the function: rewrite f to g at x and at a.
(let ((z (cadr (car (dk-landed* (lambda () (di)))))))
  (inst+ dt-pw z)                                ; f(z) = g(z)
  (inst+ dt-pw dt-pt)                            ; f(a) = g(a)
  (subst (list '== (list dt-f z) (list dt-g z)))
  (subst (list '== (list dt-f dt-pt) (list dt-g dt-pt)))
  (inst+ (dt-diffid dt-phi) z)
  (ass))
(qed 'diff-transfer-ptwise-eq)
(topic! 'diff-transfer-ptwise-eq 'analysis)
(alias! 'diff-transfer-ptwise-eq
        "a map agreeing pointwise with a differentiable map is differentiable, same derivative")
