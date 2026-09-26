;;; zz-division.scm -- DIVISION WITH REMAINDER, and ZZ as a Euclidean ring.
;;;
;;;   nn-division           a, b in NN, b /= 0  =>  forsome q, r in NN.
;;;                           a = q*b + r  and  succ r <= b
;;;   zz-division           the same on ZZ, with the Euclidean size bound
;;;                           succ(|r|) <= |b| (a NEGATIVE remainder is legal)
;;;   zz-is-euclidean-ring  IS-EUCLIDEAN-RING(ZZ-RING)
;;;
;;; The plan is the one written out at theorem-library/zz-order.scm:224-340.
;;; Only the first has content: an induction on a with b fixed.  Everything
;;; after it is sign bookkeeping (STEP 1-3) and an unfold (STEP 4).
;;;
;;; RETIRES the asserted axiom `zz-is-euclidean-ring'
;;; (structure-library/numeric-instances.scm:317), the library's last
;;; `trust: none' bill -- it enters through zz-bezout.
;;;
;;; LOAD WINDOW [219, 301), by NAME: after theorem-library/zz-order, before
;;; theorem-library/zz-bezout-proof.
;;;   lo  theorem-library/zz-order (218) -- zz-abs-in-nn, zz-abs-cases,
;;;       zz-lt-succ-le.  The deepest citation; nothing else is later.
;;;   hi  theorem-library/zz-bezout-proof (301) cites zz-is-euclidean-ring.
;;; Also cited: nn-parity-proof (210: nn-nonzero-is-succ, nn-one-is-succ-zero,
;;; nn-succ-plus-one, nn-mul-succ), zz-integral-domain (205:
;;; zz-is-integral-domain), lambda-slot-apply (201, through
;;; dk-saturate-slot-ops!), transport (189, surface-goal!), rr-recip-order
;;; (181: rr-mul-zero), rr-abs-basics (177: rr-abs-zero, rr-abs-neg,
;;; rr-abs-of-nonneg), rr-order-basics (174: rr-le-cases), nn-order-basics
;;; (167: nn-in-rr, zz-in-rr), nn-order-ord (165: nn-zero-le, nn-one-le-succ),
;;; equality-basics (148: eq-sym), prop (143), driver-kit (140),
;;; numeric-instances (68: the ZZ-RING instance), euclidean-ring (56:
;;; is-euclidean-ring-def), nn-arith (35: nn-add-succ) and the primitives of
;;; number-systems (34).  (Positions are 0-based indices over the quoted file
;;; names in load.scm, read 2026-09-17; load.scm moved under this file while it
;;; was written, so wire it BY NAME.)
;;;
;;; ---- file-local driver helpers (zd- prefix; never named like a tactic) ----

(define (zd-head g) (and (pair? g) (car g)))

;;; have!, but a no-op when the claim is already in context up to alpha.  `have!'
;;; ERRORS on that (the cut is a self-loop -- CLAUDE.md), and the typing
;;; conjunctions below are cited from several branches.
(define (zd-have! form . opt)
  (if (not (any-pred (lambda (f) (alpha-equiv? f form)) (dk-asms)))
      (apply have! form opt)))

;;; Peel (FORALL b (IMPLIES (IN b NN) (IMPLIES (NOT (= b 0)) ...))) and return
;;; the eigenvariable, read off the landed typing -- never guessed from the
;;; binder, which `di' renames when the name is taken.
(define (zd-mul-in! x y)
  (zd-have! (list 'AND (list 'IN x 'NN) (list 'IN y 'NN)))
  (fact 'nn-mul-closed x y))

(define (zd-add-in! x y)
  (zd-have! (list 'AND (list 'IN x 'NN) (list 'IN y 'NN)))
  (fact 'nn-add-closed x y))

(define (zd-peel-b!)
  (let* ((landed (dk-peel!))
         (typing (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                (eq? (caddr f) 'NN)
                                                (symbol? (cadr f))))
                               landed)
                     (error "zd-peel-b!: di landed no (IN b NN)"))))
    (cadr typing)))

;;; Close the goal tower (AND (IN w NN) (AND EQ LE)) left by an `ew': typings
;;; from the context, the equation by EQ!, the size bound by LE!.
(define (zd-close! eq! le!)
  (let ((g (dk-goal)))
    (cond ((eq? (zd-head g) 'AND)
           (for-each (lambda (k) (dk-focus! k) (zd-close! eq! le!))
                     (dk-opened (lambda () (di)))))
          ((eq? (zd-head g) 'IN) (from-context!))
          ((eq? (zd-head g) '=)  (eq!))
          ((eq? (zd-head g) '<=) (le!))
          (#t (error "zd-close!: unexpected goal" (expression->string g))))))

;;; Exhibit both witnesses of
;;;   (FORSOME q (AND (IN q NN) (FORSOME r (AND (IN r NN) (AND EQ LE)))))
;;; and close every leaf.
(define (zd-ew2! wq wr eq! le!)
  (ew wq)
  (for-each (lambda (k)
              (dk-focus! k)
              (if (eq? (zd-head (dk-goal)) 'FORSOME)
                  (begin (ew wr) (zd-close! eq! le!))
                  (from-context!)))
            (dk-opened (lambda () (di)))))

;;; Goal (<= (succ 0) B), context (IN B NN) and (NOT (= B 0)).  B = succ m
;;; (nn-nonzero-is-succ), 1 <= succ m (nn-one-le-succ), 1 = succ 0.
(define (zd-one-le! b)
  (let* ((ex (dk-fact! 'nn-nonzero-is-succ b))
         (m  (dk-skolem! ex)))
    (fact 'nn-one-le-succ m)
    (fact 'nn-one-is-succ-zero)                   ; 1 = succ 0
    (fact 'eq-sym 1 '(succ 0))                    ; succ 0 = 1
    (subst '(= (succ 0) 1))
    (subst (list '= b (list 'succ m)))
    (ass)))

(define (zd-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** zz-division: ") (display name)
        (display " did NOT close.  Open leaves:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (sequent-node-assertion l)))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (list-head (sequent-node-assumptions l)
                                         (min 8 (length (sequent-node-assumptions l))))))
                  (proof-leaves))
        (error "zz-division: unfinished" name))))

;;; =======================================================================
;;; nn-division:  a, b in NN, b /= 0  =>  a = q*b + r with succ r <= b.
;;;
;;; Induction on a, b quantified INSIDE (so the induction hypothesis is
;;; available at the same b).
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ NN)
                 (FORALL b_ (IMPLIES (IN b_ NN)
                   (IMPLIES (NOT (= b_ 0))
                     (FORSOME q_ (AND (IN q_ NN)
                       (FORSOME r_ (AND (IN r_ NN)
                         (AND (= a_ (+ (* q_ b_) r_))
                              (<= (succ r_) b_)))))))))))))

(define zd-IND  (use-induction))
(define zd-base (cdr (assq 'base zd-IND)))
(define zd-step (cdr (assq 'step zd-IND)))
(define zd-ih   (cdr (assq 'ih   zd-IND)))

;;; ---- BASE a = 0:  q := 0, r := 0.  0 = 0*b + 0, and succ 0 <= b. ----
(dk-focus! zd-base)
(define zd-bb (zd-peel-b!))
(zd-ew2! 0 0
  (lambda ()                                     ; (= 0 (+ (* 0 b) 0))
    (zd-mul-in! 0 zd-bb)                         ; IN (* 0 b) NN
    (fact 'nn-add-zero (list '* 0 zd-bb))        ; (* 0 b) + 0 = (* 0 b)
    (subst (list '= (list '+ (list '* 0 zd-bb) 0) (list '* 0 zd-bb)))
    (fact 'nn-mul-comm 0 zd-bb)                  ; 0*b = b*0
    (subst (list '= (list '* 0 zd-bb) (list '* zd-bb 0)))
    (fact 'nn-in-rr zd-bb)
    (fact 'rr-mul-zero zd-bb)                    ; b*0 = 0   (RR: NN has no such axiom)
    (fact 'eq-sym (list '* zd-bb 0) 0)           ; 0 = b*0
    (ass))
  (lambda () (zd-one-le! zd-bb)))

;;; ---- STEP a -> succ a. ----
(dk-focus! zd-step)
(define zd-b (zd-peel-b!))
(define zd-exq (dk-apply! zd-ih zd-b))           ; IH at b, guards detached
(define zd-q   (dk-skolem! zd-exq))
(define zd-exr (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                              (not (equal? f zd-exq))))
                             (dk-asms))
                   (error "nn-division: no inner existential after skolemizing q")))
(define zd-r   (dk-skolem! zd-exr))
(define zd-eq  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) '=)
                                              (equal? (caddr f)
                                                      (list '+ (list '* zd-q zd-b) zd-r))))
                             (dk-asms))
                   (error "nn-division: no IH equation a = q*b + r")))

;;; succ a = q*b + succ r -- true in BOTH branches, and case (ii) reduces to it.
(define (zd-succ-eq!)
  (zd-mul-in! zd-q zd-b)
  (fact 'nn-add-succ (list '* zd-q zd-b) zd-r)   ; q*b + succ r = succ(q*b + r)
  (subst (list '= (list '+ (list '* zd-q zd-b) (list 'succ zd-r))
               (list 'succ (list '+ (list '* zd-q zd-b) zd-r))))
  (subst zd-eq)                                   ; a -> q*b + r
  (zd-add-in! (list '* zd-q zd-b) zd-r)
  (fact 'nn-succ-closed (list '+ (list '* zd-q zd-b) zd-r))
  (rfl))

(fact 'nn-succ-closed zd-r)
(fact 'nn-in-rr (list 'succ zd-r))
(fact 'nn-in-rr zd-b)
(fact 'rr-le-cases (list 'succ zd-r) zd-b)       ; succ r < b  or  succ r = b

(use-cases (list (list '< (list 'succ zd-r) zd-b)
                 (list '= (list 'succ zd-r) zd-b))
  ;; (i) succ r < b:  q' := q, r' := succ r.
  (lambda ()
    (zd-ew2! zd-q (list 'succ zd-r)
      zd-succ-eq!
      (lambda ()                                 ; (<= (succ (succ r)) b)
        (fact 'nn-subset-zz (list 'succ zd-r))
        (fact 'nn-subset-zz zd-b)
        (fact 'zz-lt-succ-le (list 'succ zd-r) zd-b)   ; succ r + 1 <= b
        (fact 'nn-succ-plus-one (list 'succ zd-r))     ; succ(succ r) = succ r + 1
        (subst (list '= (list 'succ (list 'succ zd-r))
                     (list '+ (list 'succ zd-r) 1)))
        (ass))))
  ;; (ii) succ r = b:  q' := succ q, r' := 0.
  (lambda ()
    (fact 'nn-succ-closed zd-q)
    (zd-ew2! (list 'succ zd-q) 0
      (lambda ()                                 ; (= (succ a) (+ (* (succ q) b) 0))
        (let ((H (list '= (list '+ (list '* (list 'succ zd-q) zd-b) 0)
                       (list '+ (list '* zd-q zd-b) (list 'succ zd-r)))))
          (have! H
            (lambda ()
              (subst (list '= (list 'succ zd-r) zd-b))   ; RHS: succ r -> b
              (zd-mul-in! (list 'succ zd-q) zd-b)
              (fact 'nn-add-zero (list '* (list 'succ zd-q) zd-b))
              (subst (list '= (list '+ (list '* (list 'succ zd-q) zd-b) 0)
                           (list '* (list 'succ zd-q) zd-b)))
              (fact 'nn-mul-comm (list 'succ zd-q) zd-b)
              (subst (list '= (list '* (list 'succ zd-q) zd-b)
                           (list '* zd-b (list 'succ zd-q))))
              (fact 'nn-mul-succ zd-b zd-q)              ; b * succ q = b*q + b
              (subst (list '= (list '* zd-b (list 'succ zd-q))
                           (list '+ (list '* zd-b zd-q) zd-b)))
              (zd-have! (list 'AND (list 'IN zd-b 'NN) (list 'IN zd-q 'NN)))
              (fact 'nn-mul-comm zd-b zd-q)
              (subst (list '= (list '* zd-b zd-q) (list '* zd-q zd-b)))
              (zd-mul-in! zd-q zd-b)
              (zd-add-in! (list '* zd-q zd-b) zd-b)
              (rfl)))
          (subst H)
          (zd-succ-eq!)))
      (lambda () (zd-one-le! zd-b)))))

(zd-qed! 'nn-division)
(topic! 'nn-division 'inequalities)

;;; =======================================================================
;;; zz-division:  the division algorithm on ZZ, in the shape the EUCLIDEAN-RING
;;; law asks for.  The remainder condition is the SIZE bound succ(|r|) <= |b|,
;;; not 0 <= r < |b|, so a NEGATIVE remainder is legal -- which is what makes
;;; the four sign cases one line each instead of four cases plus a correction.
;;;
;;; STEP 1  nn-division at (|a|, |b|) gives Q, R in NN with |a| = Q|b| + R and
;;;         succ R <= |b|.  |b| /= 0 is rr-abs-zero read against b /= 0.
;;; STEP 2  zz-abs-cases at a and at b gives four branches; in each the
;;;         witnesses are read straight off, and the equation is a ZZ ring
;;;         identity once the two sign equations are substituted (`crs').
;;; STEP 3  |r| = R in every branch (rr-abs-of-nonneg, and rr-abs-neg where
;;;         r = -R), so the size bound IS the one nn-division handed over.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ ZZ)
                 (FORALL b_ (IMPLIES (IN b_ ZZ)
                   (IMPLIES (NOT (= b_ 0))
                     (FORSOME q_ (AND (IN q_ ZZ)
                       (FORSOME r_ (AND (IN r_ ZZ)
                         (AND (= a_ (+ (* q_ b_) r_))
                              (OR (= r_ 0)
                                  (<= (succ (abs r_)) (abs b_)))))))))))))))
(dk-peel!)
(fact 'zz-in-rr 'a_)
(fact 'zz-in-rr 'b_)
(fact 'zz-abs-in-nn 'a_)
(fact 'zz-abs-in-nn 'b_)
;; |b| /= 0, from b /= 0.  The lane is weakened to the two formulas that decide
;; it: `prop' searches 2^atoms and the context here is twenty deep.
(have! '(NOT (= (abs b_) 0))
  (lambda ()
    (fact 'rr-abs-zero 'b_)
    (let ((zdz-iff (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IFF)))
                            "the |b| = 0 iff b = 0 biconditional")))
      (dk-only! zdz-iff '(NOT (= b_ 0)))
      (prop))))

(define zdz-ex  (dk-fact! 'nn-division '(abs a_) '(abs b_)))
(define zdz-Q   (dk-skolem! zdz-ex))
(define zdz-exr (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                               (not (equal? f zdz-ex))))
                              (dk-asms))
                    (error "zz-division: no inner existential after skolemizing Q")))
(define zdz-R   (dk-skolem! zdz-exr))
(define zdz-eq  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) '=)
                                               (equal? (caddr f)
                                                       (list '+ (list '* zdz-Q '(abs b_)) zdz-R))))
                              (dk-asms))
                    (error "zz-division: no nn-division equation |a| = Q|b| + R")))

;; Q, R and the two absolute values, in ZZ -- what `crs' needs as generators.
(fact 'nn-subset-zz zdz-Q)
(fact 'nn-subset-zz zdz-R)
(fact 'nn-subset-zz '(abs a_))
(fact 'nn-subset-zz '(abs b_))
(fact 'zz-neg-closed zdz-Q)
(fact 'zz-neg-closed zdz-R)
;; |R| = R  and  |-R| = |R|.
(fact 'nn-in-rr zdz-R)
(fact 'nn-zero-le zdz-R)
(fact 'rr-abs-of-nonneg zdz-R)
(fact 'rr-abs-neg zdz-R)

(define (zdz-rabs+)                                   ; r := R
  (subst (list '= (list 'abs zdz-R) zdz-R)))
(define (zdz-rabs-)                                   ; r := -R
  (subst (list '= (list 'abs (list '- zdz-R)) (list 'abs zdz-R)))
  (subst (list '= (list 'abs zdz-R) zdz-R)))

(define (zdz-close! aeq beq rabs)
  (let ((g (dk-goal)))
    (cond ((eq? (zd-head g) 'AND)
           (for-each (lambda (k) (dk-focus! k) (zdz-close! aeq beq rabs))
                     (dk-opened (lambda () (di)))))
          ((eq? (zd-head g) 'IN) (ass))
          ((eq? (zd-head g) '=)
           (subst aeq) (subst beq) (subst zdz-eq) (crs))
          ((eq? (zd-head g) 'OR) (oi-r) (rabs) (ass))
          (#t (error "zdz-close!: unexpected goal" (expression->string g))))))

(define (zdz-case! aeq beq q r rabs)
  (ew q)
  (for-each (lambda (k)
              (dk-focus! k)
              (if (eq? (zd-head (dk-goal)) 'FORSOME)
                  (begin (ew r) (zdz-close! aeq beq rabs))
                  (ass)))
            (dk-opened (lambda () (di)))))

(fact 'zz-abs-cases 'a_)
(fact 'zz-abs-cases 'b_)

(use-cases (list '(= a_ (abs a_)) '(= a_ (- (abs a_))))
  (lambda ()
    (use-cases (list '(= b_ (abs b_)) '(= b_ (- (abs b_))))
      (lambda ()                                      ; a = A, b = B:  q = Q, r = R
        (zdz-case! '(= a_ (abs a_)) '(= b_ (abs b_)) zdz-Q zdz-R zdz-rabs+))
      (lambda ()                                      ; a = A, b = -B: q = -Q, r = R
        (zdz-case! '(= a_ (abs a_)) '(= b_ (- (abs b_)))
                   (list '- zdz-Q) zdz-R zdz-rabs+))))
  (lambda ()
    (use-cases (list '(= b_ (abs b_)) '(= b_ (- (abs b_))))
      (lambda ()                                      ; a = -A, b = B:  q = -Q, r = -R
        (zdz-case! '(= a_ (- (abs a_))) '(= b_ (abs b_))
                   (list '- zdz-Q) (list '- zdz-R) zdz-rabs-))
      (lambda ()                                      ; a = -A, b = -B: q = Q, r = -R
        (zdz-case! '(= a_ (- (abs a_))) '(= b_ (- (abs b_)))
                   zdz-Q (list '- zdz-R) zdz-rabs-)))))

(zd-qed! 'zz-division)
(topic! 'zz-division 'inequalities)

;;; =======================================================================
;;; zz-is-euclidean-ring:  IS-EUCLIDEAN-RING(ZZ-RING).
;;;
;;; It was an asserted axiom (structure-library/numeric-instances.scm:317) and
;;; the library's last `trust: none' bill, entering through zz-bezout.
;;;
;;; is-euclidean-ring-def is IS-INTEGRAL-DOMAIN plus the Euclidean law.  The
;;; first is the theorem in theorem-library/zz-integral-domain.scm.  For the
;;; second the degree function must be a genuine SET function ZZ -> NN, so
;;; exhibit  z |-> |z|  and type it with `lam-t' (pointwise: zz-abs-in-nn;
;;; sethood: zz-is-set).  Then the law IS zz-division, once the slot operation
;;; (ADD ZZ-RING) -- which surface-goal! leaves as an applied tupled lambda --
;;; is read off with `dk-saturate-slot-ops!', and the two applications of the
;;; degree function are beta-reduced with their arguments ALREADY typed
;;; (CLAUDE.md: peel and type, then beta -- a `lam-b' fired before the typing
;;; owes an unprovable leaf).

;;; The degree function.  Binder `z_', NOT `a_': the law's own outer variable is
;;; `a_', and a lambda binder spelled the same would shadow it in the printout
;;; for no reason.
(define zde-dg      '(VNB-LAMBDA z_ ZZ (abs z_)))
(define zde-closure '((+ . zz-add-closed) (* . zz-mul-closed) (- . zz-neg-closed)))

;;; Reduce every degree-function redex in the goal.  `lam-b' is a no-op once
;;; there is none left, so loop on the goal CHANGING, never on a count.
(define (zde-beta!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (> n 8)
          (error "zde-beta!: lam-b did not reach a fixpoint")
          (begin (quietly (lambda () (lam-b)))
                 (if (equal? (dk-goal) g) 'done (loop (+ n 1))))))))

(define (zde-close!)
  (let ((g (dk-goal)))
    (cond ((eq? (zd-head g) 'AND)
           (for-each (lambda (k) (dk-focus! k) (zde-close!))
                     (dk-opened (lambda () (di)))))
          ((eq? (zd-head g) 'IN) (ass))
          ((eq? (zd-head g) '=)
           (dk-saturate-slot-ops! 'ZZ zde-closure)     ; (ADD ZZ-RING)(u,v) -> u + v
           (ass))
          ((eq? (zd-head g) 'OR) (zde-beta!) (ass))
          (#t (error "zde-close!: unexpected goal" (expression->string g))))))

;;; The division clause, at the exhibited degree function.
(define (zde-body!)
  (let* ((landed (dk-peel!))
         (ins    (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'ZZ)))
                         landed))
         (va     (cadr (car ins)))
         (vb     (cadr (cadr ins)))
         (ex     (dk-fact! 'zz-division va vb))
         (qq     (dk-skolem! ex))
         (exr    (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                                (not (equal? f ex))))
                               (dk-asms))
                     (error "zz-is-euclidean-ring: no inner existential")))
         (rr_    (dk-skolem! exr)))
    (ew qq)
    (for-each (lambda (k)
                (dk-focus! k)
                (if (eq? (zd-head (dk-goal)) 'FORSOME)
                    (begin (ew rr_) (zde-close!))
                    (ass)))
              (dk-opened (lambda () (di))))))

(sp (make-wff '(IS-EUCLIDEAN-RING ZZ-RING)))
(mac 'is-euclidean-ring-def)
(quietly (lambda () (surface-goal! 'ZZ-RING)))
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (equal? (dk-goal) '(IS-INTEGRAL-DOMAIN ZZ-RING))
       (begin (fact 'zz-is-integral-domain) (ass))
       (begin
         (ew zde-dg)
         (for-each
          (lambda (j)
            (dk-focus! j)
            (if (eq? (zd-head (dk-goal)) 'IN)
                ;; (IN (VNB-LAMBDA z_ ZZ (abs z_)) (FUN ZZ NN)) -- lam-t's two
                ;; leaves: pointwise typing and sethood of ZZ (dk-lam-t! closes
                ;; the second and leaves focus on the first).
                (begin (dk-lam-t!)
                       (let ((lv (dk-peel!)))
                         (fact 'zz-abs-in-nn (cadr (car lv)))
                         (ass)))
                (zde-body!)))
          (dk-opened (lambda () (di)))))))
 (dk-opened (lambda () (di))))

(zd-qed! 'zz-is-euclidean-ring)
(topic! 'zz-is-euclidean-ring 'algebra)
