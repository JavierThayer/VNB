;;; rake-series.scm -- rake batch 5 T (2026-09-18): the little-o algebra, the
;;; power-series absolute-convergence bridge, and the Taylor clearing step.
;;;
;;;   little-o-scalar               c . o(x-a) is o(x-a)          little-o.scm:67
;;;   little-o-sum                  o(x-a) + o(x-a) is o(x-a)     little-o.scm:56
;;;   diff-iff-little-o             calculus.pdf eq (12)          little-o.scm:40
;;;   ps-absolute-implies-convergent  absolute => convergent,
;;;                                 for a power series            power-series.scm:157
;;;   vtaylor-clear-guarded         the Taylor clearing step, RE-STATED:
;;;                                 the support's own binder `rR' CASE-FOLDS onto
;;;                                 the class `RR' (vector-taylor-proof.scm:682)
;;;
;;; plus two new bricks the continuity algebra was missing:
;;;
;;;   shift-lam-in-fun              x |-> f(x) + k is a real function
;;;   shift-continuous-at           f continuous at a  =>  x |-> f(x) + k is
;;;
;;; ---------------------------------------------------------------------------
;;; vtaylor-clear IS DEGENERATE AS STATED, and the defect is the case fold.
;;;
;;; The support binds `rR' and types it `(IN rR RR)'.  Both the VNB reader and MIT
;;; Scheme fold to lower case, so `rR' and `RR' are ONE symbol: the quantifier
;;; captures the class name, the guard reads "rr in rr", and every later typing
;;; (`gv in rr', `nv in rr', `pw in rr') types its variable in the BOUND variable,
;;; not in the reals.  Measured on the band: `(eq? (quote rR) (quote RR))' is #t,
;;; and `free-vars' of the support's S-expression is `(nn)' -- the class RR does
;;; not occur in it at all.  So the installed fact is
;;;
;;;     forall X. X in X => forall gv in X, nv in X, pw in X, n in NN. ...
;;;
;;; which says nothing about real arithmetic and is vacuous wherever `X in X'
;;; fails.  It is cited by nothing (its own file cites `rr-mul-le-right' at
;;; :822, not this).  The statement below is the support's, character for
;;; character, with the binder renamed `rv'; it is proven `modulo 0'.  The
;;; integrator's call is whether to install it under the original name.
;;; This is the third species of case-fold accident CLAUDE.md records -- after a
;;; Scheme `define' clobbering a tactic and two binders held apart by case -- and
;;; the first where a BINDER swallows a registered CLASS.  A sweep of the PSS for
;;; a binder whose name folds onto a registered constant is worth one pass.
;;;
;;; ---------------------------------------------------------------------------
;;; THE SHIFT BRICKS.  Both o-algebra directions of eq (12) need "a continuous
;;; map plus a constant is continuous" -- forward the witness is phi - L,
;;; backward it is eps + L -- and the tree had `sum-continuous-at',
;;; `scale-continuous-at', `neg-continuous-at' and `const-continuous-at' but no
;;; combination of them stated at a TERM of that shape.  `sum-continuous-at'
;;; concludes about the literal lambda `x |-> g(x) + h(x)', so at h := the
;;; constant lambda it concludes about `x |-> f(x) + (y |-> k)(x)', a redex;
;;; `cont-transfer-ptwise-eq' moves it to `x |-> f(x) + k'.  That is the whole
;;; proof, and it is the same two-step continuity-scale.scm uses.
;;;
;;; ---------------------------------------------------------------------------
;;; ps-absolute-implies-convergent: THE BLOCKER IS GONE, and the header that
;;; recorded it is stale.  theorem-library/series-abs-converges.scm says (its
;;; lines 29-37) that deriving the power-series specialisation from the bare-series
;;; theorem "needs the PS/series bridges -- ps-partial-sum-as-series,
;;; ps-converges-as-series and ps-abs-term -- all THREE of which are themselves
;;; asserted supports".  All three have been PROVEN since 2026-09-04
;;; (theorem-library/ps-series-bridges.scm).  So the derivation trades nothing:
;;; type the three sequences, push both sides through `ps-converges-as-series',
;;; and hand `series-abs-converges' the termwise agreement, which IS `ps-abs-term'
;;; read backwards.
;;;
;;; ---------------------------------------------------------------------------
;;; CITATIONS, with the 0-based load position of the file that installs each:
;;;   primitive/base: rr-leq-mul-nonneg, rr-mul-closed, rr-neg-closed,
;;;     rr-abs-closed, rr-is-set, power-real-closed.
;;;   definitional unfolds: is-continuous-at (45), is-diff-at (335),
;;;     little-o-at (341), ps-absolutely-converges-at (127).
;;;   proven: eq-sym 148 (equality-basics); rr-add-in-rr / rr-sub-in-rr /
;;;     rr-mul-in-rr 161 (binary-minus-laws); fun-apply-type-c 162
;;;     (fun-apply-type-proof); const-continuous-at 323 (continuity-basics);
;;;     sum-lam-in-fun / sum-continuous-at 325 (continuity-sum);
;;;     cont-transfer-ptwise-eq 327 (continuity-transfer);
;;;     scale-lam-in-fun / scale-continuous-at 329 (continuity-scale);
;;;     series-abs-converges 403; ps-abs-term / ps-converges-as-series 498
;;;     (ps-series-bridges).
;;;   oracles: crs, ineq (both through `prop' / `crs' only -- no new trust).
;;;
;;; LOAD WINDOW [499, end).
;;;   lo = 499: theorem-library/ps-series-bridges (498) is the latest citation.
;;;   hi = end: not one of these five leaves is cited by anything proven, so no
;;;     citer forces a ceiling.  The natural slot is immediately after
;;;     ps-series-bridges, before "preamble".
;;;
;;; Helper prefix: r5t-.

;;; --- file-local helpers (r5t-) -------------------------------------------

(define (r5t-head? f h) (and (pair? f) (eq? (car f) h)))
(define (r5t-has? head) (not (null? (filter (lambda (p) (r5t-head? p head)) (dk-asms)))))
(define (r5t-pick head sym what)
  (dk-pick (lambda (f) (and (r5t-head? f head) (dk-contains? f sym))) what))

;; 1-based context index of FORM, for `ineq' (ineq-oracle.scm:206).  Named by
;; FORMULA, never by shape.
(define (r5t-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r5t-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r5t-ineq* . fs) (apply ineq (map r5t-idx fs)))

;; beta-reduce every redex the goal still carries.  PEEL AND TYPE FIRST: every
;; call below sits under a `di' that has already landed the argument's typing.
(define (r5t-beta!)
  (let loop ((fuel 8))
    (let ((before (dk-goal)))
      (quietly (lambda () (lam-b)))
      (if (or (= fuel 0) (equal? (dk-goal) before)) #t (loop (- fuel 1))))))

;; walk an AND tower, handing every leaf to CLOSE (which may itself open more)
(define (r5t-walk! close)
  (let ((gl (dk-goal)))
    (if (r5t-head? gl 'AND)
        (for-each (lambda (k) (dk-focus! k) (r5t-walk! close))
                  (dk-opened (lambda () (di))))
        (close gl))))

;;; =====================================================================
;;; vtaylor-clear  (the agent's `vtaylor-clear-guarded'; installed under the original
;;; name by the integrator 2026-09-18 -- the degenerate support is retired and nothing
;;; cites it, so the name is free; the binder is `rv', which folds onto no class)
;;;   (n+1)! rv = gv.pw,  gv <= nv,  0 <= pw   =>   (n+1)! rv <= nv.pw
;;; Pure real arithmetic: 0 <= nv - gv, multiply by pw, and rewrite.
;;; =====================================================================

(sp (make-wff
     '(FORALL rv (IMPLIES (IN rv RR)
        (FORALL gv (IMPLIES (IN gv RR)
        (FORALL nv (IMPLIES (IN nv RR)
        (FORALL pw (IMPLIES (IN pw RR)
        (FORALL n (IMPLIES (IN n NN)
          (IMPLIES (= (* (FACTORIAL (succ n)) rv) (* gv pw))
          (IMPLIES (<= gv nv)
          (IMPLIES (<= 0 pw)
            (<= (* (FACTORIAL (succ n)) rv) (* nv pw)))))))))))))))))
(dk-peel!)
(fact 'rr-mul-in-rr 'nv 'pw)
(fact 'rr-mul-in-rr 'gv 'pw)
(fact 'rr-sub-in-rr 'nv 'gv)
(have! '(<= 0 (- nv gv))
  (lambda () (r5t-ineq* '(<= gv nv) '(IN nv RR) '(IN gv RR) '(IN (- nv gv) RR))))
(have! '(AND (IN (- nv gv) RR) (IN pw RR)))
(have! '(AND (<= 0 (- nv gv)) (<= 0 pw)))
(fact 'rr-leq-mul-nonneg '(- nv gv) 'pw)
(have! '(= (- (* nv pw) (* gv pw)) (* (- nv gv) pw)) (lambda () (crs)))
(have! '(<= 0 (- (* nv pw) (* gv pw)))
  (lambda () (subst '(= (- (* nv pw) (* gv pw)) (* (- nv gv) pw))) (ass)))
(subst '(= (* (FACTORIAL (succ n)) rv) (* gv pw)))
(r5t-ineq* '(<= 0 (- (* nv pw) (* gv pw))) '(IN (* nv pw) RR) '(IN (* gv pw) RR))
(qed 'vtaylor-clear)
(topic! 'vtaylor-clear 'analysis)
(alias! 'vtaylor-clear
        "the Taylor clearing step: (n+1)! r = g.p, g <= N, 0 <= p give (n+1)! r <= N.p")

;;; =====================================================================
;;; little-o-scalar:  c . o(x-a) is o(x-a).  Witness c . eps_g.
;;; =====================================================================

(sp (make-wff
     '(FORALL c (FORALL g (FORALL a
        (IMPLIES (IN c RR)
        (IMPLIES (LITTLE-O-AT g a)
          (LITTLE-O-AT (VNB-LAMBDA x RR (* c (g x))) a))))))))
(dk-peel!)
(dk-split!
 (dk-landed-1
  (lambda () (mac-h 'little-o-at
                    (dk-pick (lambda (f) (r5t-head? f 'LITTLE-O-AT)) "the o-hypothesis")))))
(define r5t-se (dk-skolem! (dk-pick (lambda (p) (r5t-head? p 'FORSOME)) "eps_g")))
(define r5t-szero (r5t-pick '= r5t-se "eps_g(a) = 0"))
(define r5t-sptw (r5t-pick 'FORALL r5t-se "the pointwise equation"))
(define r5t-swit (list 'VNB-LAMBDA 'x_ 'RR (list '* 'c (list r5t-se 'x_))))
(define (r5t-sclose gl)
  (cond ((r5t-head? gl 'FORSOME) (ew r5t-swit) (r5t-walk! r5t-sclose))
        ;; the scaled map (body `(* c (g x))') and the scaled witness are both
        ;; `IN <lambda> (FUN RR RR)'; the function scaled is read off the body
        ((and (r5t-head? gl 'IN) (r5t-head? (cadr gl) 'VNB-LAMBDA))
         (fact 'scale-lam-in-fun 'c (car (caddr (list-ref (cadr gl) 3))))
         (ass))
        ((r5t-head? gl 'IS-CONTINUOUS-AT)
         (fact 'scale-continuous-at 'c r5t-se 'a) (ass))
        ((r5t-head? gl '=) (r5t-beta!) (subst r5t-szero) (crs))
        ((r5t-head? gl 'FORALL)
         (let ((z (dk-di-var!)))
           (r5t-beta!)
           (fact 'fun-apply-type-c r5t-se 'RR 'RR z)
           (fact 'rr-sub-in-rr z 'a)
           (subst (dk-apply! r5t-sptw z))
           (crs)))
        (#t (ass))))
(mac 'little-o-at)
(r5t-walk! r5t-sclose)
(qed 'little-o-scalar)
(topic! 'little-o-scalar 'analysis)

;;; =====================================================================
;;; little-o-sum:  o(x-a) + o(x-a) is o(x-a).  Witness eps_g + eps_h.
;;; =====================================================================

;; skolemize the ONE existential of LITTLE-O-AT(fn, a); return its witness
(define (r5t-open-o! fn)
  (let ((lo (dk-pick (lambda (f) (and (r5t-head? f 'LITTLE-O-AT) (equal? (cadr f) fn)))
                     "the o-hypothesis")))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'little-o-at lo))))
    (dk-skolem! (dk-pick (lambda (f) (r5t-head? f 'FORSOME)) "the eps existential"))))

(sp (make-wff
     '(FORALL g (FORALL h (FORALL a
        (IMPLIES (LITTLE-O-AT g a)
        (IMPLIES (LITTLE-O-AT h a)
          (LITTLE-O-AT (VNB-LAMBDA x RR (+ (g x) (h x))) a))))))))
(dk-peel!)
(define r5t-eg (r5t-open-o! 'g))
(define r5t-eh (r5t-open-o! 'h))
(define r5t-zg (r5t-pick '= r5t-eg "eps_g(a) = 0"))
(define r5t-zh (r5t-pick '= r5t-eh "eps_h(a) = 0"))
(define r5t-pg (r5t-pick 'FORALL r5t-eg "the pointwise equation for g"))
(define r5t-ph (r5t-pick 'FORALL r5t-eh "the pointwise equation for h"))
(define r5t-mwit (list 'VNB-LAMBDA 'x_ 'RR
                       (list '+ (list r5t-eg 'x_) (list r5t-eh 'x_))))
(define (r5t-mclose gl)
  (cond ((r5t-head? gl 'FORSOME) (ew r5t-mwit) (r5t-walk! r5t-mclose))
        ((and (r5t-head? gl 'IN) (r5t-head? (cadr gl) 'VNB-LAMBDA))
         (let ((body (list-ref (cadr gl) 3)))
           (fact 'sum-lam-in-fun (car (cadr body)) (car (caddr body))))
         (ass))
        ((r5t-head? gl 'IS-CONTINUOUS-AT)
         (fact 'sum-continuous-at r5t-eg r5t-eh 'a) (ass))
        ((r5t-head? gl '=) (r5t-beta!) (subst r5t-zg) (subst r5t-zh) (crs))
        ((r5t-head? gl 'FORALL)
         (let ((z (dk-di-var!)))
           (r5t-beta!)
           (fact 'fun-apply-type-c r5t-eg 'RR 'RR z)
           (fact 'fun-apply-type-c r5t-eh 'RR 'RR z)
           (fact 'rr-sub-in-rr z 'a)
           (subst (dk-apply! r5t-pg z))
           (subst (dk-apply! r5t-ph z))
           (crs)))
        (#t (ass))))
(mac 'little-o-at)
(r5t-walk! r5t-mclose)
(qed 'little-o-sum)
(topic! 'little-o-sum 'analysis)

;;; =====================================================================
;;; shift-lam-in-fun / shift-continuous-at -- a continuous map plus a constant
;;; =====================================================================

(define r5t-shift-lam '(VNB-LAMBDA x RR (+ (f x) k)))

(sp (make-wff '(FORALL k (IMPLIES (IN k RR)
                 (FORALL f (IMPLIES (IN f (FUN RR RR))
                   (IN (VNB-LAMBDA x RR (+ (f x) k)) (FUN RR RR))))))))
(dk-peel!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (r5t-head? (dk-goal) 'FORALL)
       (let ((z (dk-di-var!)))
         (fact 'fun-apply-type-c 'f 'RR 'RR z)
         (fact 'rr-add-in-rr (list 'f z) 'k)
         (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'shift-lam-in-fun)
(topic! 'shift-lam-in-fun 'analysis)
(alias! 'shift-lam-in-fun "a real function plus a constant is a real function")

(sp (make-wff '(FORALL k (IMPLIES (IN k RR)
                 (FORALL f (FORALL a (IMPLIES
                   (IS-CONTINUOUS-AT RR-MS RR-MS f a)
                   (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (+ (f x) k)) a))))))))
(dk-peel!)
;; the FUN typing of f and the typing of a, read off IS-CONTINUOUS-AT in a `have!'
;; LANE: `mac-h' is destructive and the citations below need the folded predicate.
(dk-split!
 (dk-landed-1
  (lambda ()
    (have! '(AND (IN f (FUN RR RR)) (IN a RR))
      (lambda ()
        (dk-split! (dk-landed-1
                    (lambda () (mac-h 'is-continuous-at
                                      '(IS-CONTINUOUS-AT RR-MS RR-MS f a)))))
        (slot-h 'PTS '(IN f (FUN (PTS RR-MS) (PTS RR-MS))))
        (slot-h 'PTS '(IN a (PTS RR-MS)))
        (dk-conj-close! (lambda () (ass))))))))
(define r5t-cst '(VNB-LAMBDA x_ RR k))
(define r5t-sum (list 'VNB-LAMBDA 'x_ 'RR (list '+ '(f x_) (list r5t-cst 'x_))))
(fact 'const-continuous-at 'k 'a)
(fact 'sum-continuous-at 'f r5t-cst 'a)
(fact 'shift-lam-in-fun 'k 'f)
(have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ RR)
              (list '= (list r5t-shift-lam 'w_) (list r5t-sum 'w_))))
  (lambda ()
    (let ((w (dk-di-var!)))
      (r5t-beta!)
      (fact 'fun-apply-type-c 'f 'RR 'RR w)
      (fact 'rr-add-in-rr (list 'f w) 'k)
      (rfl))))
(fact 'cont-transfer-ptwise-eq r5t-shift-lam r5t-sum 'a)
(ass)
(qed 'shift-continuous-at)
(topic! 'shift-continuous-at 'analysis)
(alias! 'shift-continuous-at
        "a continuous map plus a constant is continuous")

;;; =====================================================================
;;; diff-iff-little-o -- calculus.pdf eq (12)
;;;   IS-DIFF-AT(f,a,L)  iff  the increment x |-> f(x)-f(a)-L(x-a) is o(x-a)
;;; Forward the o-witness is phi - L, backward the Caratheodory factor is eps + L.
;;; =====================================================================

(define r5t-inc '(VNB-LAMBDA x RR (- (- (f x) (f a)) (* L (- x a)))))

(define r5t-phi #f) (define r5t-fzero #f) (define r5t-fptw #f) (define r5t-fwit #f)
(define r5t-e #f)   (define r5t-bzero #f) (define r5t-bptw #f) (define r5t-bwit #f)

;; `lam-t' on the increment lambda: the pointwise typing, then RR in SET
(define (r5t-inc-type!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (r5t-head? (dk-goal) 'FORALL)
         (let ((z (dk-di-var!)))
           (fact 'fun-apply-type-c 'f 'RR 'RR z)
           (fact 'fun-apply-type-c 'f 'RR 'RR 'a)
           (fact 'rr-sub-in-rr (list 'f z) '(f a))
           (fact 'rr-sub-in-rr z 'a)
           (fact 'rr-mul-in-rr 'L (list '- z 'a))
           (fact 'rr-sub-in-rr (list '- (list 'f z) '(f a)) (list '* 'L (list '- z 'a)))
           (ass))
         (begin (fact 'rr-is-set) (ass))))
   (dk-opened (lambda () (lam-t)))))

(define (r5t-fclose gl)
  (cond ((r5t-head? gl 'LITTLE-O-AT) (mac 'little-o-at) (r5t-walk! r5t-fclose))
        ((r5t-head? gl 'FORSOME) (ew r5t-fwit) (r5t-walk! r5t-fclose))
        ;; the increment lambda (body head `-') vs the o-witness (body head `+')
        ((and (r5t-head? gl 'IN) (r5t-head? (cadr gl) 'VNB-LAMBDA))
         (if (eq? (car (list-ref (cadr gl) 3)) '-)
             (r5t-inc-type!)
             (begin (fact 'shift-lam-in-fun '(- L) r5t-phi) (ass))))
        ((r5t-head? gl 'IS-CONTINUOUS-AT)
         (fact 'shift-continuous-at '(- L) r5t-phi 'a) (ass))
        ((r5t-head? gl '=) (r5t-beta!) (subst r5t-fzero) (crs))
        ((r5t-head? gl 'FORALL)
         (let ((z (dk-di-var!)))
           (r5t-beta!)
           (fact 'fun-apply-type-c r5t-phi 'RR 'RR z)
           (fact 'rr-sub-in-rr z 'a)
           (subst (dk-apply! r5t-fptw z))
           (crs)))
        (#t (ass))))

(define (r5t-bclose gl)
  (cond ((r5t-head? gl 'FORSOME) (ew r5t-bwit) (r5t-walk! r5t-bclose))
        ((and (r5t-head? gl 'IN) (r5t-head? (cadr gl) 'VNB-LAMBDA))
         (fact 'shift-lam-in-fun 'L r5t-e) (ass))
        ((r5t-head? gl 'IS-CONTINUOUS-AT)
         (fact 'shift-continuous-at 'L r5t-e 'a) (ass))
        ((r5t-head? gl '=) (r5t-beta!) (subst r5t-bzero) (crs))
        ((r5t-head? gl 'FORALL)
         (let ((z (dk-di-var!)))
           (r5t-beta!)
           (fact 'fun-apply-type-c r5t-e 'RR 'RR z)
           (fact 'fun-apply-type-c 'f 'RR 'RR z)
           (fact 'fun-apply-type-c 'f 'RR 'RR 'a)
           (fact 'rr-sub-in-rr z 'a)
           ;; the o-equation still carries the increment lambda as a redex; the
           ;; beta has to happen in the HYPOTHESIS (`lam-b-h'), and the argument
           ;; is typed one line above it.
           (let* ((inst (dk-apply! r5t-bptw z))
                  (h    (dk-landed-1 (lambda () (lam-b-h inst))))
                  (lhs  (cadr h)) (rhs (caddr h))
                  (za   (list '- z 'a))
                  (dist (list '= (list '* (list '+ (list r5t-e z) 'L) za)
                              (list '+ (list '* (list r5t-e z) za)
                                    (list '* 'L za)))))
             (have! dist (lambda () (crs)))
             (subst dist)
             (fact 'eq-sym lhs rhs)
             (subst (list '= rhs lhs))
             (crs))))
        (#t (ass))))

(sp (make-wff
     '(FORALL f (FORALL a (FORALL L
        (IFF (IS-DIFF-AT f a L)
             (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN L RR)
                  (LITTLE-O-AT (VNB-LAMBDA x RR (- (- (f x) (f a)) (* L (- x a)))) a))))))))))
(dk-peel!)
;; `di' on an IFF goal is iff-intro: one leaf per direction, each with its own
;; antecedent assumed.  Discriminate on the CONTEXT, never on the goal shape.
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (r5t-has? 'IS-DIFF-AT)
       (begin                                             ; ---- forward ----
         (dk-split! (dk-landed-1 (lambda () (mac-h 'is-diff-at '(IS-DIFF-AT f a L)))))
         (set! r5t-phi (dk-skolem! (dk-pick (lambda (p) (r5t-head? p 'FORSOME))
                                            "the Caratheodory factor")))
         (set! r5t-fzero (r5t-pick '= r5t-phi "phi(a) = L"))
         (set! r5t-fptw (r5t-pick 'FORALL r5t-phi "the Caratheodory equation"))
         (set! r5t-fwit (list 'VNB-LAMBDA 'x_ 'RR (list '+ (list r5t-phi 'x_) '(- L))))
         (fact 'rr-neg-closed 'L)
         (r5t-walk! r5t-fclose))
       (begin                                             ; ---- backward ----
         (dk-split! (dk-pick (lambda (p) (r5t-head? p 'AND)) "the o-form conjunction"))
         (dk-split! (dk-landed-1
                     (lambda () (mac-h 'little-o-at (list 'LITTLE-O-AT r5t-inc 'a)))))
         (set! r5t-e (dk-skolem! (dk-pick (lambda (p) (r5t-head? p 'FORSOME)) "eps")))
         (set! r5t-bzero (r5t-pick '= r5t-e "eps(a) = 0"))
         (set! r5t-bptw (r5t-pick 'FORALL r5t-e "the o-equation"))
         (set! r5t-bwit (list 'VNB-LAMBDA 'x_ 'RR (list '+ (list r5t-e 'x_) 'L)))
         (mac 'is-diff-at)
         (r5t-walk! r5t-bclose))))
 (dk-opened (lambda () (di))))
(qed 'diff-iff-little-o)
(topic! 'diff-iff-little-o 'analysis)

;;; =====================================================================
;;; ps-absolute-implies-convergent
;;; =====================================================================

(define r5t-tmpl '(VNB-LAMBDA n NN (* (coef n) (power x n))))

;; (IN LAM (FUN NN RR)) by lam-t, the pointwise body closed by CLOSE
(define (r5t-seq-type! lam close)
  (have! (list 'IN lam '(FUN NN RR))
    (lambda () (dk-lam-t!) (di)
               (let ((v (cadr (cadr (cadr (dk-goal))))))
                 (r5t-beta!)
                 (close v))
               (ass))))

(sp (make-wff
     '(FORALL coef
        (IMPLIES (IN coef (FUN NN RR))
          (FORALL x
            (IMPLIES (AND (IN x RR) (PS-ABSOLUTELY-CONVERGES-AT coef x))
              (PS-CONVERGES-AT coef x)))))))
(dk-peel!)
(dk-split-all!)
(fact 'rr-abs-closed 'x)
;; unfold the absolute-convergence hypothesis and READ the abs'd coefficient
;; sequence off what landed -- never rebuild it, the definition's binder is its own
(define r5t-l1
  (dk-landed-1 (lambda () (mac-h 'ps-absolutely-converges-at
                                 '(PS-ABSOLUTELY-CONVERGES-AT coef x)))))
(define r5t-absc (cadr r5t-l1))
(define r5t-f (subst-free* (list (cons 'coef 'coef) (cons 'x 'x)) r5t-tmpl))
(define r5t-g (subst-free* (list (cons 'coef r5t-absc) (cons 'x '(abs x))) r5t-tmpl))

(r5t-seq-type! r5t-f
  (lambda (v)
    (fact 'fun-apply-type-c 'coef 'NN 'RR v)
    (fact 'power-real-closed 'x v)
    (have! (list 'AND (list 'IN (list 'coef v) 'RR) (list 'IN (list 'power 'x v) 'RR)))
    (fact 'rr-mul-closed (list 'coef v) (list 'power 'x v))))
(r5t-seq-type! r5t-absc
  (lambda (v)
    (fact 'fun-apply-type-c 'coef 'NN 'RR v)
    (fact 'rr-abs-closed (list 'coef v))))
(r5t-seq-type! r5t-g
  (lambda (v)
    (fact 'fun-apply-type-c 'coef 'NN 'RR v)
    (fact 'rr-abs-closed (list 'coef v))
    (fact 'power-real-closed '(abs x) v)
    (have! (list 'AND (list 'IN (list 'abs (list 'coef v)) 'RR)
                 (list 'IN (list 'power '(abs x) v) 'RR)))
    (fact 'rr-mul-closed (list 'abs (list 'coef v)) (list 'power '(abs x) v))))

;; the abs'd power series, as a bare series
(define r5t-iff1 (dk-fact! 'ps-converges-as-series r5t-absc '(abs x)))
(have! (list 'SERIES-CONVERGES r5t-g)
  (lambda () (dk-only! r5t-iff1 r5t-l1) (prop)))
;; the termwise agreement -- `ps-abs-term' read backwards
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
             (list '= (list r5t-g 'j_) (list 'abs (list r5t-f 'j_)))))
  (lambda ()
    (let ((j (dk-di-var!)))
      (r5t-beta!)
      (let ((t (dk-fact! 'ps-abs-term 'coef 'x j)))
        (fact 'eq-sym (cadr t) (caddr t))
        (ass)))))
(dk-fact! 'series-abs-converges r5t-f r5t-g)
(define r5t-iff2 (dk-fact! 'ps-converges-as-series 'coef 'x))
(dk-only! r5t-iff2 (list 'SERIES-CONVERGES r5t-f))
(prop)
(qed 'ps-absolute-implies-convergent)
(topic! 'ps-absolute-implies-convergent 'analysis)

;;; =====================================================================
;;; esum-finite-implies-bounded -- the HALF of `esum-finite-iff-bounded'
;;; (theorem-library/extended-sum.scm:79) that the theory supports.
;;;
;;; The other half is NOT DERIVABLE from the extended-real axioms as they
;;; stand, and the reason is a missing order fact, not a missing driver.
;;; The (<=) direction has to rule out ESUM(f) = POS-INF from "ESUM(f) <= M
;;; for a real M".  Every order axiom about POS-INF is an UPPER bound --
;;; `pos-inf-upper-bound' (extended-reals.scm:73) and
;;; `rr-pos-star-below-pos-inf' (extended-reals-pos.scm:68) -- and the three
;;; laws that would close the gap are all guarded on RR:
;;; `rr-leq-antisymmetric', `rr-leq-total', `rr-leq-transitive'
;;; (number-systems.scm:410-423).  Nothing says POS-INF is ABOVE the reals.
;;;
;;; A countermodel to the derivation (not to the statement -- the statement is
;;; true of the intended structure): interpret `<=' so that POS-INF <= y for
;;; EVERY y as well as y <= POS-INF, and let ESUM(f) = POS-INF for every f.
;;; Then esum-in, esum-upper, esum-least, pos-inf-upper-bound,
;;; rr-pos-star-below-pos-inf and rr-pos-star-membership all hold, every real
;;; M bounds every partial sum vacuously, and ESUM(f) is not in RR.
;;;
;;; The one line that fixes it is a foundational decision about the extended
;;; reals, so it is the user's, not an agent's:
;;;     pos-inf-above-reals:  forall x. x in RR => not (POS-INF <= x)
;;; (equivalently, antisymmetry of <= on RR-STAR).  With it the (<=) direction
;;; is four citations: esum-in, esum-least at b := max(M,0), the membership
;;; disjunction, and the contradiction.
;;; =====================================================================

(sp (make-wff
     '(FORALL f (IMPLIES (IN f (FUN (DOM f) RR-POS-STAR))
        (IMPLIES (IN (ESUM f) RR)
          (FORSOME M (AND (IN M RR)
            (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
              (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) M))))))))))
(dk-peel!)
(fact 'esum-upper 'f)
(ew '(ESUM f))
(dk-conj-close! (lambda () (ass)))
(qed 'esum-finite-implies-bounded)
(topic! 'esum-finite-implies-bounded 'analysis)
(alias! 'esum-finite-implies-bounded
        "a finite unordered sum bounds its finite partial sums")
