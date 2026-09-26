;;; differentiation.scm -- Chapter 2 (Differentiation) of calculus.pdf, founded
;;; on the CARATHEODORY / o(h) ALGEBRAIC definition (user's choice 2026-06-27).
;;;
;;; f is differentiable at a with derivative L iff there is a function phi,
;;; continuous at a, with phi(a) = L and
;;;        f(x) - f(a) = phi(x) * (x - a)      for all x.
;;; This is equivalent to calculus.pdf Def 2.1 (the limit of the difference
;;; quotient): for x /= a the identity forces phi(x) = (f(x)-f(a))/(x-a), and
;;; continuity of phi at a is exactly existence of that limit, with the value
;;; phi(a) = f'(a).  But it is purely EQUATIONAL, so the differentiation rules
;;; become ring identities the macetes fire on directly (no eps-delta on the
;;; quotient): see the rule statements below and the notes' own Prop 2.4/2.5/2.6
;;; proofs, which already run through exactly this phi.
;;;
;;; Real functions f : RR -> RR; values use the +/-/*/abs surface (the same the
;;; RR-MS metric uses); point continuity is IS-CONTINUOUS-AT(RR-MS,RR-MS,phi,a)
;;; (structure-library/metric-continuity.scm).  The supporting "continuity
;;; algebra" lives in theorem-library/continuity-algebra.scm.
;;;
;;; STATUS (2026-08-23): deriv-const, deriv-identity, derivative-unique and
;;; diff-implies-continuous (Prop 2.4) are MACHINE-PROVEN here; deriv-sum (2.5)
;;; and deriv-product (2.6) are PROVEN in theorem-library/deriv-sum-product.scm,
;;; the chain rule in theorem-library/chain-rule.scm, and the power rule for the
;;; monomial in theorem-library/deriv-power.scm -- all `modulo 0' except the
;;; power rule, whose sole leaf is NN successor arithmetic (`nn-add-succ').
;;; What unlocked the sum/product pair was the continuity algebra coming down
;;; (continuity-basics/-sum/-product/-transfer), so that the witness's
;;; continuity is a citation rather than an eps-delta argument.  Still asserted
;;; here: `deriv-neg' (below), the scalar rule's c = -1 case.
;;; RETIRED 2026-09-14 (proven): deriv-neg -- theorem-library/mvt-cluster-readoffs.scm

;;; ===================================================================
;;; The Caratheodory derivative
;;; ===================================================================

;;; IS-DIFF-AT(f, a, L): f is differentiable at a with derivative L.
;;; IS-DIFF-AT MOVED 2026-09-20 (batch 12-A) to structure-library/derivative.scm:
;;; thirty-four other files state theorems with it, and the definition needs
;;; nothing this file proves.  The proofs below are unchanged.

;;; DERIV(f, a) = the unique L with IS-DIFF-AT(f,a,L) (well-defined by
;;; derivative-unique below); equals phi(a).  Written f'(a) in the notes.
;;; DERIV MOVED 2026-09-20 (batch 12-A) to structure-library/derivative.scm
;;; (with IS-DIFF-AT).  `derivative-unique' below is still what makes the IOTA
;;; a definition.

;;; ===================================================================
;;; First results (calculus.pdf Chapter 2.1) -- MACHINE-PROVEN from the
;;; Caratheodory definition + the continuity algebra (continuity-algebra.scm)
;;; and the RR equality/cancellation glue (order-lemmas.scm).
;;; ===================================================================

;;; Assembly helpers shared by the two proofs below.  The IS-DIFF-AT hypothesis
;;; unfolds to a big conjunction with an existential factor phi; these skolemize
;;; it and read the fresh eigenvar back out of the assumptions (its name is
;;; generated, so we capture it rather than write it).
(define (dfp--goalf) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (dfp--asms)  (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (dfp--occurs? sym e)
  (cond ((eq? sym e) #t)
        ((pair? e) (or (dfp--occurs? sym (car e)) (dfp--occurs? sym (cdr e))))
        (else #f)))
;; split every conjunctive / existential assumption (skolemizing FORSOME phi)
(define (dfp--split-asms!)
  (let loop ((budget 30))
    (when (> budget 0)
      (let ((tgt (let scan ((as (dfp--asms)))
                   (cond ((null? as) #f)
                         ((and (pair? (car as)) (memq (caar as) '(AND FORSOME))) (car as))
                         (else (scan (cdr as)))))))
        (when tgt (ai tgt) (loop (- budget 1)))))))
;; lambda-beta the goal to a fixpoint
(define (dfp--beta-goal!)
  (let loop ((prev #f) (n 8))
    (let ((g (dfp--goalf)))
      (when (and (> n 0) (not (equal? g prev)))
        (quietly (lambda () (vnb-guard (lambda () (lam-b)))))
        (loop g (- n 1))))))
(define (dfp--find-asm pred)
  (let scan ((as (dfp--asms)))
    (cond ((null? as) (error "dfp--find-asm: none matching"))
          ((pred (car as)) (car as))
          (else (scan (cdr as))))))
;; the skolem phi = f-slot of a continuity assumption (pick the one on `phi`)
(define (dfp--cont-skolem pred)
  (list-ref (dfp--find-asm (lambda (a) (and (pair? a) (eq? (car a) 'IS-CONTINUOUS-AT)
                                            (pred (list-ref a 3))))) 3))
;; the skolem whose phi(a)=VAL assumption is present
(define (dfp--phi-for val)
  (car (cadr (dfp--find-asm
    (lambda (a) (and (pair? a) (eq? (car a) '=) (equal? (caddr a) val)
                     (pair? (cadr a)) (equal? (cadr (cadr a)) 'a)))))))
;; the diff-identity forall assumption mentioning skolem PHI
(define (dfp--diffid phi)
  (dfp--find-asm (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dfp--occurs? phi a)))))
;; focus the open leaf whose goal head is HEAD
(define (dfp--focus-head! head)
  (let ((leaf (let scan ((ns (proof-open-goals *ps*)))
                (cond ((null? ns) #f)
                      ((and (null? (sequent-node-in-arrows (car ns)))
                            (let ((g (wff-formula (sequent-node-assertion (car ns)))))
                              (and (pair? g) (eq? (car g) head)))) (car ns))
                      (else (scan (cdr ns)))))))
    (if leaf (dk-focus! leaf) (error "dfp--focus-head!: no open leaf" head))))

;;; Prop 2.4: differentiable at a => continuous at a  (PROVEN).  f agrees pointwise
;;; with G(x) = f(a) + phi(x)*(x-a) [the Caratheodory identity], G is continuous at
;;; a by the continuity algebra (const + phi*(x-a)), so f is continuous at a
;;; (cont-transfer-ptwise-eq).  The continuity of G is assembled FORWARD (fact),
;;; supplying each block-lambda as an instantiation term -- sum/product-continuous-
;;; at cannot be backchained (their (g x)/(h x) are higher-order).
(sp '(FORALL f (FORALL a (FORALL L
       (IMPLIES (IS-DIFF-AT f a L) (IS-CONTINUOUS-AT RR-MS RR-MS f a))))))
(di)(di)(di)(di)
(mac-h 'IS-DIFF-AT '(IS-DIFF-AT f a L))
(dfp--split-asms!)
(let* ((PHI (dfp--cont-skolem (lambda (s) #t)))
       (DID (dfp--diffid PHI))
       (CFA '(VNB-LAMBDA x RR (f a)))
       (IDf '(VNB-LAMBDA x RR x))
       (CA  '(VNB-LAMBDA x RR a))
       (SUB `(VNB-LAMBDA x RR (- (,IDf x) (,CA x))))
       (PROD `(VNB-LAMBDA x RR (* (,PHI x) (,SUB x))))
       (G   `(VNB-LAMBDA x RR (+ (,CFA x) (,PROD x)))))
  (fact 'fun-apply-type-c 'f 'RR 'RR 'a)          ; IN (f a) RR
  (fact 'const-continuous-at '(f a) 'a)           ; cont const f(a)
  (fact 'identity-continuous-at 'a)               ; cont identity
  (fact 'const-continuous-at 'a 'a)               ; cont const a
  (fact 'sub-continuous-at IDf CA 'a)             ; cont (x-a)
  (fact 'product-continuous-at PHI SUB 'a)        ; cont phi*(x-a)
  (fact 'sum-continuous-at CFA PROD 'a)           ; cont G
  (cut `(FORALL x (IMPLIES (IN x RR) (= (f x) (,G x)))))   ; f = G pointwise
  (di)(di)
  (let* ((gl (dfp--goalf)) (X (cadr (cadr gl))))
    (dfp--beta-goal!)                             ; G(X) -> f(a)+phi(X)*(X-a)
    (inst+ DID X)                                 ; f(X)-f(a) = phi(X)*(X-a)
    (let ((DIFFt `(- (f ,X) (f a))) (PRODt `(* (,PHI ,X) (- ,X a))))
      (fact 'eq-sym DIFFt PRODt)                  ; phi(X)*(X-a) = f(X)-f(a)
      (subst `(= ,PRODt ,DIFFt))                 ; goal -> f(X) = f(a)+(f(X)-f(a))
      (fact 'fun-apply-type-c 'f 'RR 'RR X)       ; IN (f X) RR
      (crs)))
  (dfp--focus-head! 'IS-CONTINUOUS-AT)
  (fact 'cont-transfer-ptwise-eq 'f G 'a)         ; f continuous at a
  (ass))
(qed 'diff-implies-continuous)

;;; Uniqueness of the derivative  (PROVEN): makes DERIV's IOTA well-defined.
;;; f(x)-f(a) = phi(x)(x-a) = psi(x)(x-a), so for x/=a cancel (x-a)/=0 to get
;;; phi(x)=psi(x) off a; both continuous at a, so phi(a)=psi(a) (cont-agree-off-
;;; pt), i.e. L = phi(a) = psi(a) = M.
(sp '(FORALL f (FORALL a (FORALL L (FORALL M
       (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT f a M)) (= L M)))))))
(di)(di)(di)(di)(di)
(ai '(AND (IS-DIFF-AT f a L) (IS-DIFF-AT f a M)))
(mac-h 'IS-DIFF-AT '(IS-DIFF-AT f a L))
(mac-h 'IS-DIFF-AT '(IS-DIFF-AT f a M))
(dfp--split-asms!)
(let* ((PHIL (dfp--phi-for 'L)) (PHIM (dfp--phi-for 'M))
       (DIDL (dfp--diffid PHIL)) (DIDM (dfp--diffid PHIM)))
  (cut `(FORALL x (IMPLIES (IN x RR) (IMPLIES (NOT (= x a)) (= (,PHIL x) (,PHIM x))))))
  (di)(di)(di)
  (let* ((gl (dfp--goalf)) (X (cadr (cadr gl))))
    (inst+ DIDL X)                                ; f(X)-f(a) = phi_L(X)*(X-a)
    (inst+ DIDM X)                                ; f(X)-f(a) = phi_M(X)*(X-a)
    (let ((DIFFt `(- (f ,X) (f a)))
          (PRODL `(* (,PHIL ,X) (- ,X a)))
          (PRODM `(* (,PHIM ,X) (- ,X a))))
      (fact 'eq-sym DIFFt PRODL)                  ; phi_L(X)*(X-a) = f(X)-f(a)
      (fact 'eq-trans PRODL DIFFt PRODM)          ; phi_L(X)*(X-a) = phi_M(X)*(X-a)
      (fact 'fun-apply-type-c PHIL 'RR 'RR X)
      (fact 'fun-apply-type-c PHIM 'RR 'RR X)
      (fact 'rr-sub-in-rr X 'a)                   ; IN (X-a) RR
      (fact 'rr-sub-ne-zero X 'a)                 ; (X-a) /= 0
      (fact 'rr-cancel-mul-right (list PHIL X) (list PHIM X) `(- ,X a))  ; phi_L(X)=phi_M(X)
      (ass)))
  (dfp--focus-head! '=)                           ; back on main: goal L = M
  (fact 'cont-agree-off-pt PHIL PHIM 'a)          ; phi_L(a) = phi_M(a)
  (fact 'eq-sym (list PHIL 'a) 'L)                ; L = phi_L(a)
  (fact 'eq-trans 'L (list PHIL 'a) (list PHIM 'a))   ; L = phi_M(a)
  (fact 'eq-trans 'L (list PHIM 'a) 'M)           ; L = M
  (ass))
(qed 'derivative-unique)

;;; Derivative of a constant function is 0  (PROVEN).  Witness phi = const 0:
;;; c-c = 0 = 0*(x-a), and phi = const 0 is continuous at a with phi(a)=0.
(sp '(FORALL c (FORALL a
       (IMPLIES (AND (IN c RR) (IN a RR))
                (IS-DIFF-AT (VNB-LAMBDA x RR c) a 0)))))
(grind) (mac 'IS-DIFF-AT) (fact 'rr-zero-in)
(di) (dk-lam-t!) (grind) (ass)                       ; lambda(x,c) : RR -> RR
(di) (ass)                                       ; a in RR
(di) (ass)                                       ; 0 in RR
(ew '(VNB-LAMBDA x RR 0))                             ; phi := const 0
(di) (dk-lam-t!) (grind) (ass)                       ; lambda(x,0) : RR -> RR
(di) (bc* 'const-continuous-at () (ass) (ass))    ; phi continuous at a
(di) (lam-b) (rfl)                               ; phi(a) = 0
(grind) (lam-b) (crs)                            ; c-c = 0*(x-a)
(qed 'deriv-const)

;;; Derivative of the identity function is 1  (PROVEN).  Witness phi = const 1:
;;; x-a = 1*(x-a), and phi = const 1 is continuous at a with phi(a)=1.
(sp '(FORALL a
       (IMPLIES (IN a RR)
                (IS-DIFF-AT (VNB-LAMBDA x RR x) a 1))))
(grind) (mac 'IS-DIFF-AT) (fact 'rr-one-in)
(di) (dk-lam-t!) (grind) (ass)                       ; lambda(x,x) : RR -> RR
(di) (ass)                                       ; a in RR
(di) (ass)                                       ; 1 in RR
(ew '(VNB-LAMBDA x RR 1))                             ; phi := const 1
(di) (dk-lam-t!) (grind) (ass)                       ; lambda(x,1) : RR -> RR
(di) (bc* 'const-continuous-at () (ass) (ass))    ; phi continuous at a
(di) (lam-b) (rfl)                               ; phi(a) = 1
(grind) (lam-b) (crs)                            ; x-a = 1*(x-a)
(qed 'deriv-identity)

;;; Prop 2.5 (sum rule) and Prop 2.6 (product rule).  MOVED 2026-08-23 to
;;; theorem-library/deriv-sum-product.scm, where both are PROVEN `modulo 0'.
;;; They stood here as `reference' supports whose warrant texts WERE the proofs
;;; -- "the witness phi_f+phi_g is continuous at a (sum of continuous), value
;;; L+M", and for the product "by adding and subtracting f(a)g(x)" -- i.e. the
;;; derivation written in prose and then not run -- the same species as the
;;; chain rule (moved just below) and `compose-apply'.  Both statements are
;;; reproduced VERBATIM there.  What the warrants did NOT say, and what the
;;; product rule actually costs, is that its witness is continuous at a only
;;; because g is (Prop 2.4, `diff-implies-continuous'), which has to be cited
;;; BEFORE `mac-h' unfolds -- and destroys -- the IS-DIFF-AT hypothesis.
;;; Bills: both `modulo 0'.

;;; Prop 2.8: the CHAIN RULE.  MOVED 2026-08-23 to
;;; theorem-library/chain-rule.scm, where it is PROVEN, together with the DERIV
;;; form of equation (13) (`deriv-chain-value') and the reader
;;; `deriv-of-is-diff-at'.  It stood here as a `reference' support whose warrant
;;; text WAS the proof -- "the factor of g o f is (phi_g o f)*phi_f, continuous
;;; at a with value g'(f(a))*f'(a)" -- i.e. the derivation written in prose and
;;; then not run.  What made it reachable was `compose-continuous-at' coming
;;; down (theorem-library/continuity-compose.scm, 2026-08-23); the rest is two
;;; substitutions and one `crs'.  The statement is reproduced VERBATIM there.
;;; Bill: {compose-type, compose-apply}, inherited from compose-continuous-at.


;;; Negation rule: derivative of -f is -f'.  Special case of the scalar rule
;;; (c = -1); witness -phi (continuous at a, value -L).  Used by
;;; interior-min-deriv-zero (apply interior-max-deriv-zero to g = -f).

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
;;; (the IS-DIFF-AT notation! MOVED with the definition, 2026-09-20, to
;;; structure-library/derivative.scm)
