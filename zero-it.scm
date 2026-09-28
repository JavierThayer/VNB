;;; zero-it.scm -- (zero-it): move an equation goal P = Q to its normal form R = 0.
;;;
;;; The user's notes-42 (2026-09-26): "my biggest gripe is the inability to simplify
;;; algebraic expressions in formulas".  On the focus goal
;;;
;;;     x in rr  ==>  P(x) = Q(x)
;;;
;;; (zero-it) computes the normal form R of P - Q with crs's own calculator and leaves
;;;
;;;     x in rr, [the eliminated terms all defined]  ==>  R = 0
;;;
;;; The design is docs/zero-it-design-2026-09-26.md; its "Built" section is the walkthrough.
;;;
;;; WHAT IT DOES, by the value of R (always printed first: ";; zero-it: P - Q  normalises
;;; to  R"):
;;;   R = 0          the goal is a commutative-ring identity.  Closed by `crs'.  When `crs'
;;;                  can close the goal as it stands, the recorded step IS `(crs)'; when it
;;;                  cannot (an atom still to be typed, a guard it does not peel, a `=='),
;;;                  the step is `(zero-it)' and does the preparation first.
;;;   R a non-zero   the goal is FALSE: it reduces to R = 0.  Printed, NO inference, nothing
;;;   numeral        recorded -- the dead-path signal the notes ask for.
;;;   otherwise      ONE recorded step `(zero-it)': the atoms are typed (or their typings
;;;                  are cut as OWED side leaves, listed), `R = 0' is cut, the branch
;;;                  `R = 0 |- P = Q' is closed, and the focus is left on `|- R = 0'.
;;; The value is R (DATA), or #f when zero-it declines (the reason is printed; nothing
;;; changes).
;;;
;;; THE RING.  The concrete number surface (+ - * ^ and numerals; atoms typed in NN ZZ QQ RR
;;; CC -- the ring is the largest class an atom is typed in, NN lifting like `contra') or an
;;; abstract ring `a' ((ADD a) (MUL a) (NEG a) (ZERO a) (ONE a)) with IS-COMMUTATIVE-RING(a)
;;; in context.  NN alone is refused for the rewrite (NN has no subtraction, so `R = 0' would
;;; not be a statement about NN); an identity or a FALSE verdict over NN is still reported.
;;;
;;; THE CLOSING BRANCH needs no sub-zero law and no typing of P or Q (a deviation from the
;;; design note, recorded there): from `R = 0' in context,
;;;     P = Q + R          by crs on a lane           (skipped when P is literally Q + R)
;;;     rewrite P -> Q + R  by subst                   goal  Q + R = Q
;;;     rewrite R -> 0      by subst                   goal  Q' + 0 = Q'
;;;     crs.
;;; (Q' is Q with R replaced by 0 wherever R occurs; the last goal is an identity for every
;;; Q'.)  The rewrite of P needs P not to occur inside Q, and the rewrite of R needs R not
;;; to occur inside an ATOM of Q (f(R) would become the untyped f(0)); when either fails the
;;; mirror orientation is used (Q -> P - R, then R -> 0), and when both fail zero-it declines.
;;;
;;; RECORDING.  One step, `(zero-it)' with no arguments: the normal form is recomputed at
;;; replay from the same goal.  The inner steps run with recording suppressed on the path the
;;; bc* handlers use (`*replaying?*' and `*in-bc*-handler?*' bound, interactive.scm:128-146),
;;; so their citations reach the ledger through `*proof-hidden-citations*'; `apply-recorded-
;;; cmd!' has a `zero-it' case that calls the surface command.  The inner steps run inside
;;; `dk--transaction' (driver-kit.scm): any failure puts the graph, focus, script, mints,
;;; trace, undo stack and hidden citations back, prints the reason and returns #f.
;;;
;;; TRUST.  No kernel rule, no support, no stamp.  The steps are cut / crs / subst / di /
;;; fact / ass / qrfl through the surface, each checked by its rule checker; the only oracle
;;; is crs, and the printed R comes from the calculator crs itself uses.
;;;
;;; Loaded at the root right after counterexample (before suggest.scm, which calls the
;;; what-now lane defined at the end of this file).  Prefix `zi-'.

;;; -----------------------------------------------------------------------
;;; Small helpers

(define (zi--say . strs)
  (vnb-report! (apply string-append strs))       ; the report channel (interactive.scm)
  (unless *vnb-quiet*
    (for-each display strs)
    (newline)))

;;; A decline is part of the report too: under a quiet surface the reason must
;;; still reach the user.
(define (zi--warn msg)
  (vnb-report! (string-append ";VNB warning: " msg))
  (vnb--print-warning msg))

;;; The warning OBJECT vnb--run! prints for a step that did not go through: on the
;;; channel as well.
(define (zi--warning msg)
  (vnb-report! (string-append ";VNB warning: " msg))
  (make-vnb-warning msg))

(define (zi--get a key) (let ((p (assq key a))) (and p (cdr p))))

(define (zi--occurs? x e)
  (or (equal? x e)
      (and (pair? e) (any (lambda (s) (zi--occurs? x s)) e))))

;;; NN ZZ QQ RR CC ranked; #f for anything else (compared by name, both cases, as
;;; ring-domain? does).
(define (zi--rank C)
  (and (symbol? C)
       (let ((s (string-downcase (symbol->string C))))
         (cond ((string=? s "nn") 0) ((string=? s "zz") 1) ((string=? s "qq") 2)
               ((string=? s "rr") 3) ((string=? s "cc") 4) (#t #f)))))

;;; A goal P = Q or P == Q under a chain of TYPED universals
;;; (FORALL v (IMPLIES (IN v C) ...)).  -> (binders . core), binders ((v . C) ...).
(define (zi--peel g)
  (let loop ((g g) (bs '()))
    (if (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3) (symbol? (cadr g))
             (let ((b (caddr g)))
               (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
                    (let ((h (cadr b)))
                      (and (pair? h) (eq? (car h) 'IN) (= (length h) 3)
                           (eq? (cadr h) (cadr g)))))))
        (loop (caddr (caddr g))
              (cons (cons (cadr g) (caddr (cadr (caddr g)))) bs))
        (cons (reverse bs) g))))

(define (zi--rel? f)
  (and (pair? f) (memq (car f) '(= ==)) (= (length f) 3)))

;;; The classes C with (IN t C) among the binders and the context.
(define (zi--typings t asms binders)
  (append (filter-map (lambda (b) (and (equal? (car b) t) (cdr b))) binders)
          (filter-map (lambda (f) (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                                       (equal? (cadr f) t) (caddr f)))
                      asms)))

;;; The normal form as a FLAT surface term, highest degree first (expand's order), for a
;;; poly whose coefficients may be complex (1i): a coefficient is "negative" only when it is
;;; a negative real, and printed by its magnitude then.
(define (zi--neg-coef? c) (and (real? c) (negative? c)))
(define (zi--mag c) (if (real? c) (abs c) c))

;;; A coefficient as a TERM.  A mixed complex c = a + b i is written a + b * 1i (the printer
;;; renders a pure imaginary as `3i' but a mixed number as Scheme's `-1+i'); crs reads the sum
;;; back to the same number.
(define (zi--coef-term c)
  (if (or (real? c) (zero? (real-part c)))
      c
      (list '+ (real-part c) (make-rectangular 0 (imag-part c)))))

;;; c * g1^e1 * g2^e2 ..., flat (expand's monomial, with a term coefficient allowed).
(define (zi--mono c w)
  (let ((ct (zi--coef-term c)))
    (if (number? ct)
        (expand--flat-mono ct w)
        (let ((m (expand--flat-mono 1 w)))
          (cond ((eqv? m 1) ct)
                ((and (pair? m) (eq? (car m) '*)) (cons '* (cons ct (cdr m))))
                (#t (list '* ct m)))))))

(define (zi--poly->term p)
  (if (null? p)
      0
      (let* ((ts  (sort p (lambda (a b) (> (length (car a)) (length (car b))))))
             (pos (filter (lambda (tm) (not (zi--neg-coef? (cdr tm)))) ts))
             (neg (filter (lambda (tm) (zi--neg-coef? (cdr tm))) ts))
             (->t (lambda (tm) (zi--mono (zi--mag (cdr tm)) (car tm))))
             (sum (lambda (xs) (if (null? (cdr xs)) (->t (car xs)) (cons '+ (map ->t xs))))))
        (cond ((null? neg) (sum pos))
              ((null? pos) (list '- (sum neg)))
              (#t (cons '- (cons (sum pos) (map ->t neg))))))))

;;; The constant of a poly that has no generator: 0 for '(), c for ((() . c)); else #f.
(define (zi--poly-const p)
  (cond ((null? p) 0)
        ((and (null? (cdr p)) (null? (caar p))) (cdar p))
        (#t #f)))

;;; The ring operations on each surface.
(define (zi--add s a x y) (if (eq? s 'generic) (list (list 'ADD a) x y) (list '+ x y)))
(define (zi--sub s a x y)
  (if (eq? s 'generic) (list (list 'ADD a) x (list (list 'NEG a) y)) (list '- x y)))
(define (zi--zero s a) (if (eq? s 'generic) (list 'ZERO a) 0))

;;; The arguments of a ring-operation node, or #f when T is an ATOM (a generator) of the
;;; surface.  A power is an operation only with a literal exponent (crs expands exactly those).
(define (zi--op-args s a t)
  (cond
    ((not (pair? t)) #f)
    ((eq? s 'generic)
     (let ((h (car t)))
       (cond ((and (pair? h) (memq (car h) '(ADD MUL NEG)) (= (length h) 2) (equal? (cadr h) a))
              (cdr t))
             ((and (memq h '(ZERO ONE)) (= (length t) 2) (equal? (cadr t) a)) '())
             (#t #f))))
    ((memq (car t) '(+ - * binplus bintimes binneg)) (cdr t))
    ((and (memq (car t) '(power ^ expt)) (= (length t) 3)
          (exact-nonnegative-integer? (caddr t)))
     (list (cadr t)))
    (#t #f)))

;;; Does R occur INSIDE an atom of T (so that rewriting R -> 0 would change the atom)?
;;; An occurrence as a whole ring-position subterm is fine.
(define (zi--inside-atom? s a r t)
  (cond ((equal? r t) #f)
        ((not (pair? t)) #f)
        ((zi--op-args s a t) => (lambda (xs) (any (lambda (x) (zi--inside-atom? s a r x)) xs)))
        (#t (zi--occurs? r t))))

;;; -----------------------------------------------------------------------
;;; Typing an atom (concrete surface): type-term's plan (driver-kit.scm), or, for recip(t),
;;; D-recip-closed with t typed and not(t = 0) in context.

(define (zi--recip-plan g D asms)
  (and (pair? g) (eq? (car g) 'recip) (= (length g) 2)
       (let* ((t   (cadr g))
              (thm (string->symbol (string-append (string-downcase (symbol->string D))
                                                  "-recip-closed")))
              (tp  (type-term--plan t D)))
         (and (hash-table-ref/default *theorem-table* thm #f)
              tp
              (member (list 'NOT (list '= t 0)) asms)
              (list 'zi-recip (list 'IN g D) tp thm t D)))))

(define (zi--type-plan g D asms)
  (or (zi--recip-plan g D asms)
      (type-term--plan g D)))

(define (zi--exec-plan! p)
  (if (eq? (car p) 'zi-recip)
      (let ((typ (list-ref p 1)) (tp (list-ref p 2)) (thm (list-ref p 3))
            (t (list-ref p 4)) (D (list-ref p 5)))
        (type-term--exec! tp)
        (dk-have! typ (lambda ()
                        (dk-have! (list 'AND (list 'IN t D) (list 'NOT (list '= t 0))))
                        (fact thm t)
                        (ass))))
      (type-term--exec! p)))

;;; -----------------------------------------------------------------------
;;; THE ANALYSIS.  PURE: reads the goal G and the raw context ASMS, returns an alist.
;;;   status   decline | false | zero | rewrite
;;;   reason   (decline) the string printed
;;;   rel P Q binders surface ring R const untyped plans owed orient

(define (zi--decline reason . more)
  (append (list (cons 'status 'decline) (cons 'reason reason)) more))

(define (zi--analyse g asms)
  (let* ((pk      (zi--peel g))
         (binders (car pk))
         (core    (cdr pk)))
    (cond
      ((not (zi--rel? core))
       (zi--decline "the goal is not an equation P = Q (or P == Q), bare or under typed universals"))
      (#t
       (let* ((rel (car core)) (P (cadr core)) (Q (caddr core))
              (a   (or (find-cring P) (find-cring Q))))
         (if a
             (zi--analyse-generic rel P Q a asms binders)
             (zi--analyse-concrete rel P Q asms binders)))))))

;;; The common tail: numeral verdicts, the rewrite plan.
(define (zi--finish rel P Q binders surface ring poly untyped plans owed)
  (let* ((R     (if (eq? surface 'generic) (cpoly->cring-term poly ring) (zi--poly->term poly)))
         (const (zi--poly-const poly))
         (Z     (zi--zero surface ring))
         (base  (list (cons 'rel rel) (cons 'P P) (cons 'Q Q) (cons 'binders binders)
                      (cons 'surface surface) (cons 'ring ring) (cons 'R R)
                      (cons 'const const) (cons 'untyped untyped)
                      (cons 'plans plans) (cons 'owed owed))))
    (cond
      ((and const (zero? const)) (cons (cons 'status 'zero) base))
      (const (cons (cons 'status 'false) base))
      ((and (eq? surface 'concrete) (eqv? (zi--rank ring) 0))
       (append (zi--decline
                (string-append "NN is not a ring: no subtraction, so "
                               (expression->string (list '= R 0))
                               " is not a statement about NN.  Type an atom in ZZ or RR"
                               " to work in a ring"))
               base))
      ((and (null? binders) (alpha-equiv? (list '= R Z) (list rel P Q)))
       (append (zi--decline "the goal already reads R = 0: there is nothing to simplify")
               base))
      (#t
       (let ((orient
              (cond ((and (not (zi--occurs? P Q)) (not (zi--inside-atom? surface ring R Q))) 'left)
                    ((and (not (zi--occurs? Q P)) (not (zi--inside-atom? surface ring R P))) 'right)
                    (#t #f))))
         (if orient
             (append (list (cons 'status 'rewrite) (cons 'orient orient)) base)
             (append (zi--decline
                      (string-append (expression->string R)
                                     " occurs inside an atom of both sides, so the goal cannot"
                                     " be rewritten to R = 0 by substitution"))
                     base)))))))

(define (zi--analyse-concrete rel P Q asms binders)
  (let* ((e1 (cvnb-expand-pow P)) (e2 (cvnb-expand-pow Q))
         (p1 (cvnb->poly e1))     (p2 (cvnb->poly e2)))
    (if (not (and p1 p2))
        (zi--decline "a side of the equation is not a ring term")
        (let* ((gens    (cvnb-eq-source-generators e1 e2))
               (ranked  (filter-map
                         (lambda (g)
                           (let ((rs (filter-map zi--rank (zi--typings g asms binders))))
                             (and (pair? rs) (apply max rs))))
                         gens))
               (untyped (filter (lambda (g)
                                  (not (any zi--rank (zi--typings g asms binders))))
                                gens))
               ;; the ring: the largest class an atom is typed in; failing that, the
               ;; smallest class type-term can type an untyped atom in (f(x) with f in
               ;; FUN(RR, RR) gives RR) -- read off the CONTEXT, so under universals it is
               ;; decided after the `di' the step begins with
               (D       (cond ((pair? ranked)
                               (list-ref '(NN ZZ QQ RR CC) (apply max ranked)))
                              ((and (pair? untyped) (null? binders))
                               (let ((cs (filter-map
                                          (lambda (g)
                                            (find (lambda (C) (type-term--plan g C))
                                                  '(NN ZZ QQ RR CC)))
                                          untyped)))
                                 (and (pair? cs)
                                      (list-ref '(NN ZZ QQ RR CC)
                                                (apply max (map zi--rank cs))))))
                              (#t #f))))
          (cond
            ((and (pair? gens) (not D) (pair? binders)
                  (any (lambda (b) (not (zi--rank (cdr b)))) binders))
             ;; an atom typed through a binder that is not a number class (f in FUN(RR, RR)):
             ;; decide after the peel
             (let ((poly (poly-add p1 (poly-neg p2))))
               (zi--finish rel P Q binders 'concrete #f poly untyped '() '())))
            ((and (pair? gens) (not D))
             (zi--decline
              (string-append "no atom of the equation is typed in a number class"
                             " (NN ZZ QQ RR CC): "
                             (zi--list-string gens))))
            ((and (null? gens)
                  (not (or (number? P) (number? Q)
                           (concrete-ring-head? P) (concrete-ring-head? Q))))
             (zi--decline "the equation is not between ring terms"))
            (#t
             (let* ((poly  (poly-add p1 (poly-neg p2)))
                    (plans (if (null? binders)
                               (filter-map (lambda (g) (and D (zi--type-plan g D asms))) untyped)
                               '()))
                    (owed  (if (null? binders)
                               (filter-map (lambda (g)
                                             (and (not (and D (zi--type-plan g D asms)))
                                                  (list 'IN g D)))
                                           untyped)
                               (map (lambda (g) (list 'IN g D)) untyped))))
               (zi--finish rel P Q binders 'concrete D poly untyped plans owed))))))))

(define (zi--analyse-generic rel P Q a asms binders)
  (let ((p1 (cring->poly P a)) (p2 (cring->poly Q a)))
    (cond
      ((not (and p1 p2)) (zi--decline "a side of the equation is not a ring term"))
      ((not (member (list 'IS-COMMUTATIVE-RING a) asms))
       (zi--decline (string-append (expression->string (list 'IS-COMMUTATIVE-RING a))
                                   " is not in the context: the ring laws crs uses are not"
                                   " available for " (expression->string a))))
      (#t
       (let* ((carrier (list 'CARR a))
              (gens    (cring-eq-source-generators P Q a))
              (untyped (filter (lambda (g) (not (member carrier (zi--typings g asms binders))))
                               gens)))
         (zi--finish rel P Q binders 'generic a (poly-add p1 (poly-neg p2)) untyped '()
                     (map (lambda (g) (list 'IN g carrier)) untyped)))))))

(define (zi--list-string ts)
  (let loop ((ts ts) (acc ""))
    (if (null? ts)
        acc
        (loop (cdr ts) (string-append acc (if (string=? acc "") "" ", ")
                                      (expression->string (car ts)))))))

;;; Can `crs' close the goal exactly as it stands?  (Its concrete path peels ring-typed
;;; universals itself; its generic path wants the equation at sequent level; both want every
;;; atom typed, and a `==' is not its shape.)
(define (zi--crs-direct? a)
  (and (eq? (zi--get a 'rel) '=)
       (null? (zi--get a 'untyped))
       (if (eq? (zi--get a 'surface) 'generic)
           (null? (zi--get a 'binders))
           (every (lambda (b) (ring-domain? (cdr b))) (zi--get a 'binders)))))

;;; -----------------------------------------------------------------------
;;; THE STEPS (run with recording suppressed, inside a transaction; focus = the leaf).

;;; cut F; -> (side . main), focus on main.  side is #f when hash-consing grounded it.
(define (zi--cut! f)
  (let* ((new  (dk-opened (lambda () (cut f))))
         (side (any-pred (lambda (s) (alpha-equiv? (dk-goal-of s) f)) new))
         (main (any-pred (lambda (s) (not (eq? s side))) new)))
    (if (not main) (error "zero-it: cut left no main branch for" f))
    (dk-focus! main)
    (cons side main)))

;;; Close (rel P Q) on the focus leaf when P - Q normalises to 0.
(define (zi--close-identity!)
  (let* ((leaf (proof-state-focus *ps*)) (g (dk-goal)) (P (cadr g)) (Q (caddr g)))
    (cond
      ((eq? (car g) '=) (crs))
      ((equal? P Q) (qrfl))
      (#t (let ((e (if (zi--occurs? P Q) (list '= Q P) (list '= P Q))))
            (dk-have! (list '= P Q) (lambda () (crs)))
            (subst e)
            (qrfl))))
    (sequent-node-grounded? leaf)))

;;; The branch R = 0 |- (rel P Q), on the focus leaf.
(define (zi--close-branch! a)
  (let* ((leaf (proof-state-focus *ps*))
         ;; NB case folding: `rng', never `r' beside `R' (they are ONE symbol)
         (s (zi--get a 'surface)) (rng (zi--get a 'ring))
         (P (zi--get a 'P)) (Q (zi--get a 'Q)) (R (zi--get a 'R))
         (Z (zi--zero s rng))
         (left? (eq? (zi--get a 'orient) 'left))
         (from (if left? P Q))
         (to   (if left? (zi--add s rng Q R) (zi--sub s rng P R))))
    (unless (equal? from to)
      (let ((e1 (list '= from to)))
        (dk-have! e1 (lambda () (crs)))
        (subst e1)))
    (subst (list '= R Z))
    (zi--close-identity!)
    (sequent-node-grounded? leaf)))

;;; Land the typings that can be landed; cut the rest as owed side leaves.  Focus ends on
;;; the main branch.  -> the list of owed side leaves (nodes, or #f when already grounded).
(define (zi--land-typings! a)
  (for-each zi--exec-plan! (zi--get a 'plans))
  (map (lambda (f) (car (zi--cut! f))) (zi--get a 'owed)))

;;; The whole drive.  -> #t on success (the transaction keeps it), #f otherwise.
;;; The analysis the drive actually used (re-made after `di' when the goal had universals,
;;; whose eigenvariables may have been renamed) is kept for the printout.
(define *zi-last-analysis* #f)

(define (zi--drive! a0)
  (let ((a (if (pair? (zi--get a0 'binders))
               (begin (di) (zi--analyse (dk-goal) (dk-asms)))
               a0)))
    (set! *zi-last-analysis* a)
    (and (memq (zi--get a 'status) '(zero rewrite))
         (null? (zi--get a 'binders))
         (begin
           (zi--land-typings! a)
           (if (eq? (zi--get a 'status) 'zero)
               (zi--close-identity!)
               (let ((eqn (list '= (zi--get a 'R) (zi--zero (zi--get a 'surface) (zi--get a 'ring)))))
                 (if (dk-asm? eqn)
                     (zi--close-branch! a)
                     (let* ((sm (zi--cut! eqn)) (side (car sm)) (main (cdr sm)))
                       (and (zi--close-branch! a)
                            (sequent-node-grounded? main)
                            (begin
                              (if (and side (not (sequent-node-grounded? side)))
                                  (dk-focus! side))
                              #t))))))))))

;;; -----------------------------------------------------------------------
;;; Printing

(define (zi--difference-string a)
  (let ((s (zi--get a 'surface)) (rng (zi--get a 'ring)))
    (expression->string (zi--sub s rng (zi--get a 'P) (zi--get a 'Q)))))

(define (zi--say-normal-form a)
  (zi--say ";; zero-it: " (zi--difference-string a) "  normalises to  "
           (expression->string (zi--get a 'R))))

(define (zi--false-message a)
  (let ((c (zi--get a 'const)))
    (string-append
     (cond ((and (eq? (zi--get a 'surface) 'generic) (not (= (zi--mag c) 1)))
            (string-append ";; zero-it: the goal reduces to " (number->string c)
                           " * 1 = 0 in " (expression->string (zi--get a 'ring))
                           ": FALSE unless the characteristic of the ring divides "
                           (number->string (zi--mag c))))
           (#t (string-append ";; zero-it: the goal is FALSE in every ring where 1 /= 0: it reduces to "
                              (expression->string (list '= (zi--get a 'R) (zi--zero (zi--get a 'surface) (zi--get a 'ring)))))))
     (if (and (eq? (zi--get a 'rel) '==) (pair? (zi--get a 'untyped)))
         (string-append " (unless an untyped atom is undefined: "
                        (zi--list-string (zi--get a 'untyped)) ")")
         "")
     ".  This path is dead; no inference was made.")))

(define (zi--say-owed owed)
  (for-each (lambda (f) (zi--say ";;   owed: " (expression->string f))) owed))

;;; -----------------------------------------------------------------------
;;; (zero-it) -- the surface command.

(define (zero-it)
  (cond
    ((not (and (proof-state? *ps*) (not (proof-done? *ps*))))
     (zi--warn "zero-it: no open goal; nothing changed")
     #f)
    (#t
     (let ((a (zi--analyse (dk-goal) (dk-asms))))
       (case (zi--get a 'status)
         ((decline)
          (if (zi--get a 'R) (zi--say-normal-form a))
          (zi--warn (string-append "zero-it: " (zi--get a 'reason) "; nothing changed"))
          #f)
         ((false)
          (zi--say-normal-form a)
          (zi--say (zi--false-message a))
          (zi--get a 'R))
         ((zero)
          (zi--say-normal-form a)
          (if (zi--crs-direct? a)
              (let ((leaf (proof-state-focus *ps*)))
                (crs)                                  ; recorded as itself: the oracle
                (if (sequent-node-grounded? leaf)
                    (begin (zi--say ";; zero-it: an identity of commutative rings; closed by crs") 0)
                    #f))
              (zi--run-step! a)))
         ((rewrite)
          (zi--say-normal-form a)
          (zi--run-step! a))
         (else #f))))))

;;; The one recorded step.  The inner steps run with recording suppressed (bc*-handler path)
;;; inside a transaction; a failure rolls back and is reported as a warning (not recorded).
(define (zi--run-step! a)
  (let* ((ok   #f)
         (leaf (proof-state-focus *ps*)))
    (set! *zi-last-analysis* a)
    (vnb--run! 'zero-it '()
               (lambda ()
                 (set! ok (fluid-let ((*in-bc*-handler?* (or *in-bc*-handler?* (not *replaying?*)))
                                      (*replaying?* #t))
                            (dk--transaction (lambda () (zi--drive! a)))))
                 (if ok
                     *ps*
                     (zi--warning
                      (string-append "zero-it: " (zi--difference-string a) " normalises to "
                                     (expression->string (zi--get a 'R))
                                     ", but the rewriting steps did not go through"
                                     (let ((why (and *zi-last-analysis*
                                                     (zi--get *zi-last-analysis* 'reason))))
                                       (if why (string-append " (" why ")") ""))
                                     "; nothing changed")))))
    (cond
      ((not ok) #f)
      ((sequent-node-grounded? leaf)
       (zi--say ";; zero-it: closed") (zi--get a 'R))
      ((eq? (zi--get a 'status) 'zero)
       (zi--say ";; zero-it: the identity is closed by crs, given the typings owed below")
       (zi--say-owed (zi--get *zi-last-analysis* 'owed))
       (zi--get a 'R))
      (#t
       (zi--say ";; zero-it: the goal is now  "
                (expression->string (dk-goal)))
       (zi--say-owed (zi--get *zi-last-analysis* 'owed))
       (zi--get *zi-last-analysis* 'R)))))

;;; -----------------------------------------------------------------------
;;; The what-now lane (suggest.scm).  Returns the move forms it offers; prints only when it
;;; has something to say.  Never raises.

(define (what-now--show-zero-it goal)
  (let ((a (and *ps* (not (proof-done? *ps*))
                (dk--silently (lambda () (zi--analyse (dk-goal) (dk-asms)))))))
    (if (not a)
        '()
        (case (zi--get a 'status)
          ((false)
           (display ";; ZERO-IT -- ") (display (zi--difference-string a))
           (display " normalises to ") (display (expression->string (zi--get a 'R))) (newline)
           (display (zi--false-message a)) (newline)
           '())
          ((zero rewrite)
           (display ";; ZERO-IT -- ") (display (zi--difference-string a))
           (display " normalises to ") (display (expression->string (zi--get a 'R))) (newline)
           (if (eq? (zi--get a 'status) 'zero)
               (begin (display ";;   an identity of commutative rings: (zero-it) closes it by crs") (newline))
               (begin
                 (display ";;   (zero-it) leaves the goal  ")
                 (display (expression->string (list '= (zi--get a 'R)
                                                    (zi--zero (zi--get a 'surface) (zi--get a 'ring)))))
                 (newline)
                 (for-each (lambda (f) (display ";;   owed: ") (display (expression->string f)) (newline))
                           (zi--get a 'owed))))
           (display ";;   (zero-it)") (newline)
           (list '(zero-it)))
          (else '())))))
