;;; theorem-library/taylor-clear-guarded.scm -- the two RR-algebra leaves of
;;; Taylor's theorem, and the two micro-lemmas beside them, PROVEN:
;;;
;;;   rr-power-pos         0 < d  =>  0 < d^n            (d in RR, n in NN)
;;;   rr-cancel-mul-left   c*u = c*v, c /= 0  =>  u = v  (c, u, v in RR)
;;;   rr-recip-factorial   n! * recip(n!) = 1            (n in NN)
;;;   taylor-clear         the clearing identity of taylor-lagrange's endgame:
;;;                        from  (0 - (recip(n!)*fn1)*pw)*(hx-ha)
;;;                                = (0 - succ(n)*pw)*(gx-ga)
;;;                        with gx = hx = 0, ha = d, ga = r, 0 < pw,
;;;                        conclude  succ(n)! * r = fn1 * d.
;;;
;;; All four stood in taylor-proof.scm as `add-to-pss' + `warrant! 'well-known'
;;; (rr-power-pos at ~399, the other three at ~407-463).  Tonight (2026-09-15)
;;; `taylor-lagrange' bills EXACTLY these two leaves, rr-power-pos and
;;; taylor-clear; the neighbours are what taylor-clear's own warrant chains
;;; through ("cancel pw /= 0", "multiply by n!"), so they are proven here too
;;; and taylor-clear cites them.  STATEMENTS ARE BYTE-IDENTICAL to the supports'
;;; (copied from the definition sites; nothing is unguarded -- gx, ga, hx, ha
;;; are untyped in taylor-clear but each is EQUATED to a real or to 0 by an
;;; antecedent, which is all the proof needs).
;;;
;;; SPLICE POINT.  This block goes into theorem-library/taylor-proof.scm right
;;; after the marker  `;;; ===== END second spliced block ====='  (line ~2089),
;;; i.e. immediately BEFORE the `taylor-lagrange (cleared form)' section that
;;; cites rr-power-pos and taylor-clear.  It cannot be a separate load.scm
;;; entry: the window is INSIDE taylor-proof.scm (the lemma block above --
;;; factorial-real-pos, recip-factorial-in-rr -- is cited, and taylor-lagrange
;;; below is the citer), and load.scm gives each theorem-library file its own
;;; environment.  Window, as a file: [taylor-proof's own position, itself).
;;;
;;; CITATIONS (all loaded before taylor-proof, load.scm line in parentheses,
;;; or in taylor-proof.scm's own lemma block above the splice point):
;;;   primitive (number-systems.scm / injection.scm def-constant):
;;;     rr-subset-cc, power-zero, power-succ, rr-mul-closed, rr-recip-closed,
;;;     rr-recip-inverse, nn-succ-closed, factorial-succ, rr-zero-in
;;;   equality-basics (589):   eq-sym, eq-trans
;;;   nn-order-basics (675):   nn-in-rr
;;;   rr-order-basics (688):   rr-pos-ne-zero
;;;   rr-recip-order (735):    rr-zero-lt-one, rr-mul-pos
;;;   inverse-function (1510): rr-recip-solve
;;;   dyadic-weights (1962):   power-real-closed
;;;   taylor-proof.scm above:  factorial-real-pos, recip-factorial-in-rr
;;;
;;; MECHANICS.
;;;   rr-power-pos binds d OUTERMOST, so `ni' cannot fire on the statement (it
;;;   wants the NN binder on top).  `dk-peel!' takes the whole prefix, then the
;;;   n-outermost form is `cut' and proved by `use-induction' (the induction
;;;   lane's recipe, CLAUDE.md), and the main branch closes by instantiating
;;;   the cut at n.  The cut binds `n_', not `n': `n' is already an
;;;   eigenvariable of the context.  Base: power-zero (guarded on CC, hence
;;;   rr-subset-cc first) + rr-zero-lt-one.  Step: power-succ, then the
;;;   product of positives (rr-mul-pos) with power-real-closed for the typing.
;;;   This is dyadic-weights' `power-two-pos' with d for 2.
;;;
;;;   taylor-clear is goal-directed and never rewrites a hypothesis.  The four
;;;   equations are pushed into the gMVT equation by REVERSE substitution
;;;   inside `have!' lanes (the lane's goal carries d, r, 0; the context's
;;;   equation carries ha, ga, hx, gx; the lane substitutes hx:=0 etc. INTO ITS
;;;   OWN GOAL and closes by `crs' or `ass').  Then both sides are normalised
;;;   by `crs' (generators: recip(n!), fn1, pw, d, r, succ(n) -- each typed in
;;;   RR beforehand, since crs certifies its generators), chained by eq-trans,
;;;   pw is cancelled by rr-cancel-mul-left, and n! is cleared by
;;;   factorial-succ + rr-recip-factorial.
;;;
;;; Helper prefix: `tcl-' (never a tactic name; case folding).

;;; ---- rr-power-pos: a positive real to a natural power is positive ----------
(sp (make-wff '(FORALL d (IMPLIES (IN d RR) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (< 0 d) (< 0 (power d n)))))))))
(dk-peel!)                                   ; d in RR, n in NN, 0 < d
(fact 'rr-subset-cc 'd)                      ; d in CC (power-zero/succ are on CC)
(define tcl-pp-cut '(FORALL n_ (IMPLIES (IN n_ NN) (< 0 (power d n_)))))
(define tcl-pp-leaves (dk-opened (lambda () (cut tcl-pp-cut))))
(define tcl-pp-side
  (let ((l (filter (lambda (s) (alpha-equiv? (dk-goal-of s) tcl-pp-cut)) tcl-pp-leaves)))
    (if (= (length l) 1) (car l) (error "tcl: cut side goal not found" (length l)))))
(define tcl-pp-main
  (let ((l (filter (lambda (s) (not (eq? s tcl-pp-side))) tcl-pp-leaves)))
    (if (= (length l) 1) (car l) (error "tcl: cut main branch not found" (length l)))))
(dk-focus! tcl-pp-side)
(define tcl-pp-br (use-induction))
(dk-focus! (cdr (assq 'base tcl-pp-br)))
(mac 'power-zero)                            ; 0 < 1
(fact 'rr-zero-lt-one)
(ass)
(dk-focus! (cdr (assq 'step tcl-pp-br)))
(define tcl-pp-k (cdr (assq 'var tcl-pp-br)))
(have! (list 'AND '(IN d CC) (list 'IN tcl-pp-k 'NN)))
(fact 'power-succ 'd tcl-pp-k)               ; d^(succ k) = d * d^k
(subst (list '= (list 'power 'd (list 'succ tcl-pp-k))
                (list '* 'd (list 'power 'd tcl-pp-k))))
(fact 'power-real-closed 'd tcl-pp-k)        ; d^k in RR
(fact 'rr-mul-pos 'd (list 'power 'd tcl-pp-k))   ; 0 < d * d^k
(ass)
(dk-focus! tcl-pp-main)
(inst+ tcl-pp-cut 'n)                        ; 0 < d^n
(ass)
(qed 'rr-power-pos)
(topic! 'rr-power-pos 'analysis)

;;; ---- rr-cancel-mul-left: c*u = c*v, c /= 0  =>  u = v ----------------------
;;; Through rr-recip-solve (u' = c*v' => v' = recip(c)*u') at u' := c*u,
;;; v' := v, then recip(c)*(c*u) = (c*recip(c))*u = 1*u = u.  The right-factor
;;; twin (rr-cancel-mul-right, rr-order-basics.scm) goes through
;;; rr-no-zero-divisors instead; either works, this one is four rewrites.
(sp (make-wff '(FORALL c (IMPLIES (IN c RR) (FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (NOT (= c 0)) (IMPLIES (= (* c u) (* c v)) (= u v)))))))))))
(dk-peel!)                                   ; c,u,v in RR; c /= 0; c*u = c*v
(have! '(AND (IN c RR) (IN u RR)))
(fact 'rr-mul-closed 'c 'u)                  ; c*u in RR
(have! '(AND (IN c RR) (NOT (= c 0))))
(fact 'rr-recip-closed 'c)                   ; recip c in RR
(fact 'rr-recip-inverse 'c)                  ; c * recip c = 1
(fact 'rr-recip-solve 'c '(* c u) 'v)        ; v = recip(c) * (c*u)
(subst '(= v (* (recip c) (* c u))))         ; goal: u = recip(c) * (c*u)
(have! '(= (* (recip c) (* c u)) (* (* c (recip c)) u)) (lambda () (crs)))
(subst '(= (* (recip c) (* c u)) (* (* c (recip c)) u)))
(subst '(= (* c (recip c)) 1))               ; goal: u = 1 * u
(crs)
(qed 'rr-cancel-mul-left)
(topic! 'rr-cancel-mul-left 'analysis)

;;; ---- rr-recip-factorial: n! * recip(n!) = 1 --------------------------------
;;; recip-factorial-in-rr's proof with rr-recip-inverse in place of
;;; rr-recip-closed at the last line.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (* (FACTORIAL n) (recip (FACTORIAL n))) 1)))))
(dk-peel!)
(fact 'factorial-real-pos 'n)
(dk-split! '(AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n))))
(fact 'rr-pos-ne-zero '(FACTORIAL n))
(have! '(AND (IN (FACTORIAL n) RR) (NOT (= (FACTORIAL n) 0))))
(fact 'rr-recip-inverse '(FACTORIAL n))
(ass)
(qed 'rr-recip-factorial)
(topic! 'rr-recip-factorial 'analysis)

;;; ---- taylor-clear: the clearing identity ------------------------------------
(sp (make-wff
  '(FORALL fn1 (IMPLIES (IN fn1 RR)
   (FORALL pw (IMPLIES (IN pw RR)
   (FORALL d (IMPLIES (IN d RR)
   (FORALL r (IMPLIES (IN r RR)
   (FORALL gx (FORALL ga (FORALL hx (FORALL ha
   (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (< 0 pw)
     (IMPLIES (= gx 0)
     (IMPLIES (= hx 0)
     (IMPLIES (= ha d)
     (IMPLIES (= ga r)
     (IMPLIES (= (* (- 0 (* (* (recip (FACTORIAL n)) fn1) pw)) (- hx ha))
                 (* (- 0 (* (succ n) pw)) (- gx ga)))
       (= (* (FACTORIAL (succ n)) r) (* fn1 d))))))))))))))))))))))))
(dk-peel!)   ; fn1 pw d r in RR; n in NN; 0<pw; gx=0; hx=0; ha=d; ga=r; the equation
;; typings of every generator crs will see, and the two clearing facts
(fact 'recip-factorial-in-rr 'n)             ; recip(n!) in RR
(fact 'factorial-real-pos 'n)
(dk-split! '(AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n))))
(fact 'nn-succ-closed 'n)
(fact 'nn-in-rr '(succ n))                   ; succ n in RR
(fact 'rr-pos-ne-zero 'pw)                   ; pw /= 0
(fact 'rr-recip-factorial 'n)                ; n! * recip(n!) = 1
(fact 'factorial-succ 'n)                    ; succ(n)! = succ(n) * n!
(define tcl-rf '(recip (FACTORIAL n)))
(define tcl-A  (list '- 0 (list '* (list '* tcl-rf 'fn1) 'pw)))   ; the G' factor
(define tcl-B  '(- 0 (* (succ n) pw)))                            ; the H' factor
;; the gMVT equation with the four endpoint equations substituted in:
;;   A * (0 - d) = B * (0 - r)
(have! '(= (- 0 d) (- hx ha)) (lambda () (subst '(= hx 0)) (subst '(= ha d)) (crs)))
(have! '(= (- 0 r) (- gx ga)) (lambda () (subst '(= gx 0)) (subst '(= ga r)) (crs)))
(define tcl-E1 (list '= (list '* tcl-A '(- 0 d)) (list '* tcl-B '(- 0 r))))
(have! tcl-E1 (lambda () (subst '(= (- 0 d) (- hx ha)))
                         (subst '(= (- 0 r) (- gx ga)))
                         (ass)))
;; normalise both sides:  pw * ((rf*fn1)*d)  =  pw * (succ(n)*r)
(define tcl-U  (list '* (list '* tcl-rf 'fn1) 'd))
(define tcl-V  '(* (succ n) r))
(define tcl-LN (list '* 'pw tcl-U))
(define tcl-RN (list '* 'pw tcl-V))
(have! (list '= tcl-LN (cadr tcl-E1)) (lambda () (crs)))
(have! (list '= (caddr tcl-E1) tcl-RN) (lambda () (crs)))
(fact 'eq-trans tcl-LN (cadr tcl-E1) (caddr tcl-E1))   ; LN = B*(0-r)
(fact 'eq-trans tcl-LN (caddr tcl-E1) tcl-RN)          ; LN = RN
;; cancel pw:  (rf*fn1)*d = succ(n)*r
(have! (list 'AND (list 'IN tcl-rf 'RR) '(IN fn1 RR)))
(fact 'rr-mul-closed tcl-rf 'fn1)
(have! (list 'AND (list 'IN (list '* tcl-rf 'fn1) 'RR) '(IN d RR)))
(fact 'rr-mul-closed (list '* tcl-rf 'fn1) 'd)          ; U in RR
(have! '(AND (IN (succ n) RR) (IN r RR)))
(fact 'rr-mul-closed '(succ n) 'r)                      ; V in RR
(fact 'rr-cancel-mul-left 'pw tcl-U tcl-V)              ; U = V
(fact 'eq-sym tcl-U tcl-V)                              ; V = U
;; clear n!:  goal  succ(n)! * r = fn1 * d
(subst '(= (FACTORIAL (succ n)) (* (succ n) (FACTORIAL n))))   ; (succ n * n!) * r = fn1*d
(have! (list '= '(* (* (succ n) (FACTORIAL n)) r) (list '* '(FACTORIAL n) tcl-V))
       (lambda () (crs)))
(subst (list '= '(* (* (succ n) (FACTORIAL n)) r) (list '* '(FACTORIAL n) tcl-V)))
(subst (list '= tcl-V tcl-U))                           ; n! * ((rf*fn1)*d) = fn1*d
(have! (list '= (list '* '(FACTORIAL n) tcl-U)
                (list '* (list '* '(FACTORIAL n) tcl-rf) '(* fn1 d)))
       (lambda () (crs)))
(subst (list '= (list '* '(FACTORIAL n) tcl-U)
                (list '* (list '* '(FACTORIAL n) tcl-rf) '(* fn1 d))))
(subst (list '= (list '* '(FACTORIAL n) tcl-rf) 1))    ; 1 * (fn1*d) = fn1*d
(crs)
(qed 'taylor-clear)
(topic! 'taylor-clear 'analysis)
