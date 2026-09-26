;;; rake-dc-on-nn.scm -- dependent choice on NN, PROVEN.
;;;
;;; Replaces the two asserted supports of theorem-library/dc-on-nn.scm:
;;;
;;;   dc-on-nn-pred   set-valued step:  nxt(k,u) is the set of allowed
;;;                   successors of u at stage k.
;;;   dc-on-nn        relation form: R a set of encoded triples (LIST k u y).
;;;
;;; THE CONSTRUCTION is the one both warrants describe, made concrete by a
;;; single parametric NN recursion (def-by-nn-recursion, ordinals.scm):
;;;
;;;   DC-ITER(S,a,nxt,0)        == a
;;;   DC-ITER(S,a,nxt,succ n)   == CHOICE { y in S : y in nxt(n, DC-ITER(S,a,nxt,n)) }
;;;
;;; No triple is ever collected into a set on this route, so the tree's
;;; missing SEP-over-triples is never wanted: the separation is over y alone.
;;;
;;; Three theorems, in dependency order:
;;;
;;;   dc-iter-in     n in NN |- DC-ITER(S,a,nxt,n) in S      [ni, induction on n]
;;;   dc-iter-step   n in NN |- DC-ITER(S,a,nxt,succ n) in nxt(n, DC-ITER(...,n))
;;;   dc-on-nn-pred  the support, at f := (VNB-LAMBDA k_ in NN. DC-ITER(X,a,nxt,k_))
;;;
;;; THE INDUCTION VARIABLE IS OUTERMOST in both lemmas.  `ni' tests the literal
;;; shape (FORALL n (IMPLIES (IN n NN) body)) and `di' is greedy -- it would
;;; take the whole FORALL/IMPLIES prefix in one step -- so S, a and nxt are
;;; quantified INSIDE the induction, not fixed before it.  The induction
;;; hypothesis is then the full universal at n, which is what the step needs.
;;;
;;; DEFINEDNESS (the LUTINS rule).  pi--defined? certifies neither a CHOICE term
;;; nor an untyped application, so the successor lane types before it
;;; instantiates: dc-iter-in at n lands (IN DC-ITER(..,n) S) FIRST, and only
;;; then is the totality hypothesis instantiated at u := DC-ITER(..,n).  The
;;; recursion equations are `==' (def-by-nn-recursion's quasi-equalities, since
;;; the parameters are unguarded); they are used through `subst', which takes
;;; `==' as `=', never through a reconstructed right-hand side -- the SEP is
;;; read OFF the landed instance, so this file cannot drift from what
;;; def-by-nn-recursion installed.
;;;
;;; THE SET IS BOUND AS `s_', NEVER `X'.  The reader case-folds, so a binder
;;; spelled X is the eigenvariable x of `choice-axiom' (theory.scm:312); a
;;; separation over it makes capture-avoidance rename choice-axiom's own binder
;;; and the auto-detach then misses.  zen-step.scm records the two runs that
;;; cost.  dc-on-nn-pred's own statement DOES bind X -- it is copied literally
;;; -- which is exactly why all the choice work happens in the two lemmas and
;;; the support's proof only cites them.
;;;
;;; Needs: structure-library/ordinals (def-by-nn-recursion), number-systems
;;; (NN, succ, nn-zero-in, nn-succ-closed, nn-is-set), theory.scm
;;; (choice-axiom, primitive), interactive + proof-debt + driver-kit
;;; (dk-peel!, dk-apply!, dk-skolem!, dk-fact!, choose!, in-sep!, dk-lam-t!).
;;;
;;; LOAD WINDOW [161, 293).  lo is forced by theorem-library/fun-apply-type-proof
;;; (position 160), cited once, in dc-on-nn's last step, for f(k) in X; every
;;; other citation is far below (ordinals 77 for def-by-nn-recursion,
;;; number-systems 34, theory.scm 11) and the machinery floor is proof-debt at
;;; 139.  hi = 293, theorem-library/diagonalization, the earliest file that
;;; cites dc-on-nn-pred in a proof.  Drop the fun-apply-type-c citation --
;;; fun-codomain-iff (theory.scm, primitive) is three lines more -- and lo
;;; falls back to 140.
;;;
;;; NOTE for the integrator: dc-on-nn.scm itself sits at 86, BELOW interactive
;;; (134), so the supports cannot be replaced in place; the support file keeps
;;; its header and loses the two `support' + `warrant!' forms.  ALSO
;;; theorem-library/founder-warrants (131) carries a second
;;; `(warrant! 'dc-on-nn 'informal ...)' -- founder-warrants.scm:109 -- which
;;; loads BELOW this file and must go with them.
;;;
;;; Helper prefix: rdc-.

;;; ---- file-local driver helpers ----------------------------------------

(define (rdc-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-dc-on-nn: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (sequent-node-assumptions l)))
                  (proof-open-goals *ps*))
        (error "rake-dc-on-nn: unfinished" name))))

(define (rdc-split-landed! fs)
  (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) fs)
  fs)

;;; ---- the recursion ----------------------------------------------------
;;; DC-ITER(S,a,nxt,-) : the generic dependent iterate.  `def-by-nn-recursion'
;;; installs dc-iter-zero and dc-iter-succ as DEFINITIONAL quasi-equalities,
;;; the parameters universally quantified and unguarded.

(register-constant! 'DC-ITER 'defined-fn)

(def-by-nn-recursion 'DC-ITER '(S a nxt) 'a '(n val)
  '(CHOICE (SEP y_ S (IN y_ (nxt n val)))))

;;; ---- the shapes, built by CONSTRUCTOR ---------------------------------

;; totality of the step over the carrier S:
;;   forall k in NN. forall u in S. forsome y. y in S and y in nxt(k,u)
;; Binders k, u, y are SPELLED AS IN THE SUPPORT, so the instance of this
;; formula IS the support's own hypothesis and detaches against it.
(define (rdc-tot s nx)
  (list 'FORALL 'k
    (list 'IMPLIES '(IN k NN)
      (list 'FORALL 'u
        (list 'IMPLIES (list 'IN 'u s)
          (list 'FORSOME 'y
            (list 'AND (list 'IN 'y s) (list 'IN 'y (list nx 'k 'u)))))))))

;; (FORALL n_ in NN. FORALL s_. FORALL a_ in s_. FORALL nx_ with totality. CONCL)
(define (rdc-stmt concl)
  (list 'FORALL 'n_
    (list 'IMPLIES '(IN n_ NN)
      (list 'FORALL 's_
        (list 'FORALL 'a_
          (list 'IMPLIES '(IN a_ s_)
            (list 'FORALL 'nx_
              (list 'IMPLIES (rdc-tot 's_ 'nx_) (concl 's_ 'a_ 'nx_ 'n_)))))))))

(define (rdc-concl-in s a nx n) (list 'IN (list 'DC-ITER s a nx n) s))
(define (rdc-concl-step s a nx n)
  (list 'IN (list 'DC-ITER s a nx (list 'succ n))
            (list nx n (list 'DC-ITER s a nx n))))

;; After a dk-peel! of one of the two statements, read the four eigenvariables
;; off the GOAL -- never off the context order.  Both conclusions carry a
;; DC-ITER term whose four arguments are exactly s, a, nx and the stage.
(define (rdc-params-of-goal)
  (let* ((g (dk-goal))
         (t (cadr g)))                        ; (DC-ITER s a nx <stage>)
    (if (not (and (pair? t) (eq? (car t) 'DC-ITER) (= (length t) 5)))
        (error "rdc-params-of-goal: goal is not a DC-ITER membership"
               (expression->string g)))
    (list (cadr t) (caddr t) (cadddr t))))

;;; The successor lane, shared by the two lemmas.  Requires, in context:
;;;   (IN n NN), the totality hypothesis TOT, and (IN (DC-ITER s a nx n) s).
;;; Lands (IN (CHOICE sep) s) and (IN (CHOICE sep) (nx n (DC-ITER s a nx n))),
;;; rewrites the goal's DC-ITER(..,succ n) to that CHOICE, and closes by `ass'.
(define (rdc-succ-close! s a nx n tot)
  (let* ((dcn (list 'DC-ITER s a nx n))
         (ex  (dk-apply! tot n dcn))          ; forsome y. y in s and y in nx(n,dcn)
         (w   (dk-skolem! ex))
         (eq  (dk-fact! 'DC-ITER-succ s a nx n))   ; (== DC-ITER(..,succ n) (CHOICE sep))
         (sep (cadr (caddr eq))))             ; the SEP, READ OFF the instance
    (rdc-split-landed!
      (choose! sep w (lambda () (in-sep! (lambda () (ass)) (lambda () (ass))))))
    (subst eq)                                ; `subst' takes == as =
    (ass)))

;;; =====================================================================
;;; dc-iter-in -- the iterate stays in the carrier.  Induction on n.
;;; =====================================================================

(sp (make-wff (rdc-stmt rdc-concl-in)))
(define rdc-a-cases (dk-opened (lambda () (ni))))

;; The STEP case is the one `ni' re-quantified over the induction variable:
;; its body is an IMPLIES guarded on (IN _ NN).  The BASE case's body is the
;; next FORALL of the statement.  Discriminate on THAT, never on leaf order.
(define (rdc-step-case? g)
  (and (pair? g) (eq? (car g) 'FORALL)
       (pair? (caddr g)) (eq? (car (caddr g)) 'IMPLIES)
       (pair? (cadr (caddr g))) (eq? (car (cadr (caddr g))) 'IN)
       (eq? (caddr (cadr (caddr g))) 'NN)))

(define (rdc-case what pred)
  (dk-focus! (or (any-pred (lambda (l) (pred (dk-goal-of l))) rdc-a-cases)
                 (error "dc-iter-in: no case" what))))

;; BASE: DC-ITER(s,a,nx,0) == a, and a is in s.
(rdc-case "base" (lambda (g) (not (rdc-step-case? g))))
(dk-peel!)
(let* ((p  (rdc-params-of-goal))
       (eq (dk-fact! 'DC-ITER-zero (car p) (cadr p) (caddr p))))
  (subst eq)
  (ass))

;; STEP: the induction hypothesis is the WHOLE universal at n.
(rdc-case "step" rdc-step-case?)
(let* ((landed (dk-peel!))
       (t      (cadr (dk-goal)))              ; (DC-ITER s a nx (succ n))
       (s      (cadr t)) (a (caddr t)) (nx (cadddr t))
       (n      (cadr (car (cddddr t))))       ; the succ's argument
       (tot    (rdc-tot s nx))
       (ih     (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                              (not (equal? f tot))))
                             landed)
                   (error "dc-iter-in: no induction hypothesis"))))
  (dk-apply! ih s a nx)                       ; (IN (DC-ITER s a nx n) s)
  (rdc-succ-close! s a nx n tot))

(rdc-qed! 'dc-iter-in)
(topic! 'dc-iter-in 'combinatorial)

;;; =====================================================================
;;; dc-iter-step -- the successor really is an allowed successor.
;;; =====================================================================

(sp (make-wff (rdc-stmt rdc-concl-step)))
(dk-peel!)
(let* ((g  (dk-goal))
       (t  (cadr g))                          ; (DC-ITER s a nx (succ n))
       (s  (cadr t)) (a (caddr t)) (nx (cadddr t))
       (n  (cadr (car (cddddr t))))            ; the succ's argument
       (tot (rdc-tot s nx)))
  (fact 'dc-iter-in n s a nx)                 ; (IN (DC-ITER s a nx n) s)
  (rdc-succ-close! s a nx n tot))

(rdc-qed! 'dc-iter-step)
(topic! 'dc-iter-step 'combinatorial)

;;; =====================================================================
;;; dc-on-nn-pred -- THE SUPPORT, stated literally (dc-on-nn.scm:83).
;;; =====================================================================

(sp (make-wff
  '(FORALL X
     (IMPLIES (IN X SET)
       (FORALL a
         (IMPLIES (IN a X)
           (FORALL nxt
             (IMPLIES
               (FORALL k
                 (IMPLIES (IN k NN)
                   (FORALL u
                     (IMPLIES (IN u X)
                       (FORSOME y
                         (AND (IN y X)
                              (IN y (nxt k u))))))))
               (FORSOME f
                 (AND (IN f (FUN NN X))
                      (AND (= (f 0) a)
                           (FORALL k
                             (IMPLIES (IN k NN)
                               (IN (f (succ k)) (nxt k (f k))))))))))))))))

(define rdc-p-landed (dk-peel!))

(define rdc-p-X
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                 "the carrier")))
(define rdc-p-a
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) rdc-p-X)))
                 "the base point")))
(define rdc-p-tot
  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) rdc-p-landed)
      (error "dc-on-nn-pred: no totality hypothesis")))
;; The step variable is the one free variable of the totality hypothesis that
;; occurs in HEAD position -- `nxt' is applied, (nxt k u); the carrier and NN
;; occur only as arguments.  (free-vars reports class constants such as NN, and
;; NN is not in *constant-registry*, so constant-head? does not filter it.)
(define (rdc-heads f)
  (let loop ((e f) (acc '()))
    (if (pair? e)
        (let loop2 ((l (cdr e)) (a (if (symbol? (car e)) (cons (car e) acc) acc)))
          (if (null? l) a (loop2 (cdr l) (loop (car l) a))))
        acc)))
(define rdc-p-nxt
  (let* ((heads (rdc-heads rdc-p-tot))
         (vs (filter (lambda (v) (and (not (eq? v rdc-p-X)) (memq v heads)))
                     (delete-duplicates (free-vars rdc-p-tot)))))
    (if (= (length vs) 1) (car vs)
        (error "dc-on-nn-pred: cannot name the step variable" vs))))

(define rdc-p-lam
  (list 'VNB-LAMBDA 'k_ 'NN (list 'DC-ITER rdc-p-X rdc-p-a rdc-p-nxt 'k_)))

(ew rdc-p-lam)

(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ;; (IN LAM (FUN NN X)) -- lam-t, pointwise typing from dc-iter-in
       ((and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
        (dk-lam-t!)
        (let ((kv (dk-di-var!)))
          (fact 'dc-iter-in kv rdc-p-X rdc-p-a rdc-p-nxt)
          (ass)))
       ;; (= (LAM 0) a) -- type 0, beta, then the zero equation
       ((eq? (car g) '=)
        (fact 'nn-zero-in)
        (lam-b)
        (subst (dk-fact! 'DC-ITER-zero rdc-p-X rdc-p-a rdc-p-nxt))
        (rfl))
       ;; forall k in NN. LAM(succ k) in nxt(k, LAM k)
       (#t
        (let ((kv (dk-di-var!)))
          (fact 'nn-succ-closed kv)           ; TYPE BEFORE YOU BETA
          (lam-b)
          (fact 'dc-iter-step kv rdc-p-X rdc-p-a rdc-p-nxt)
          (ass)))))))

(rdc-qed! 'dc-on-nn-pred)

;;; =====================================================================
;;; dc-on-nn -- THE SUPPORT, stated literally (dc-on-nn.scm:35), FROM
;;; dc-on-nn-pred at the set-valued step
;;;
;;;     nxt := (VNB-LAMBDA (k_,u_) in NN x X. { y in X : (k_,u_,y) in R })
;;;
;;; The triple is a TERM in the separation's condition and nothing collects
;;; triples into a set, so the tree's missing SEP-over-triples is not wanted
;;; here either.  The destructuring lambda reduces in its DIRECT two-argument
;;; application -- the shape (nxt k u) becomes after substitution -- because
;;; reduce-lambda-in-expr/scope's multi-binder arm takes
;;; ((VNB-LAMBDA (LIST x1..xn) A body) a1..an) and pi--beta-licensed? licenses
;;; it componentwise against CARTESIAN(NN,X).  So both `lam-b' (in the totality
;;; lane's goal) and `lam-b-h' (on the conclusion's per-stage hypothesis) fire
;;; once the two arguments are typed; f(k) in X is fun-apply-type-c.
;;; =====================================================================

(define (rdc-r-nxt x r)
  (list 'VNB-LAMBDA '(LIST k_ u_) (list 'CARTESIAN 'NN x)
        (list 'SEP 'y_ x (list 'IN (list 'LIST 'k_ 'u_ 'y_) r))))

(define (rdc-find-sub pred e)
  (cond ((pred e) e)
        ((pair? e) (let loop ((l e))
                     (cond ((null? l) #f)
                           ((pair? l) (or (rdc-find-sub pred (car l)) (loop (cdr l))))
                           (#t #f))))
        (#t #f)))

(sp (make-wff
  '(FORALL X
     (IMPLIES (IN X SET)
       (FORALL a
         (IMPLIES (IN a X)
           (FORALL R
             (IMPLIES (IN R SET)
               (IMPLIES
                 (FORALL k
                   (IMPLIES (IN k NN)
                     (FORALL u
                       (IMPLIES (IN u X)
                         (FORSOME y
                           (AND (IN y X)
                                (IN (LIST k u y) R)))))))
                 (FORSOME f
                   (AND (IN f (FUN NN X))
                        (AND (= (f 0) a)
                             (FORALL k
                               (IMPLIES (IN k NN)
                                 (IN (LIST k (f k) (f (succ k))) R)))))))))))))))

(define rdc-r-landed (dk-peel!))

;; The carrier is the codomain of the FUN in the goal -- there are TWO
;; (IN _ SET) hypotheses here (X and R), so the SET typing cannot name it.
(define rdc-r-X
  (caddr (or (rdc-find-sub (lambda (e) (and (pair? e) (eq? (car e) 'FUN)
                                            (= (length e) 3) (eq? (cadr e) 'NN)))
                           (dk-goal))
             (error "dc-on-nn: no (FUN NN X) in the goal"))))
(define rdc-r-a
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) rdc-r-X)))
                 "the base point")))
(define rdc-r-R
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)
                                  (not (eq? (cadr f) rdc-r-X))))
                 "the relation")))
(define rdc-r-TOT
  (or (any-pred (dk-head? 'FORALL) rdc-r-landed)
      (error "dc-on-nn: no totality hypothesis")))
(define rdc-r-nxt-term (rdc-r-nxt rdc-r-X rdc-r-R))

;; the set-valued totality dc-on-nn-pred asks for
(have! (rdc-tot rdc-r-X rdc-r-nxt-term)
  (lambda ()
    (let* ((landed (dk-peel!))
           (kv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (eq? (caddr f) 'NN)))
                              "the stage")))
           (uv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (eq? (caddr f) rdc-r-X)
                                               (not (eq? (cadr f) rdc-r-a))))
                              "the current point"))))
      (lam-b)                                   ; kv and uv are typed: the redex fires
      (let* ((ex (dk-apply! rdc-r-TOT kv uv))
             (w  (dk-skolem! ex)))
        (witness! w
          (lambda ()
            (dk-conj-close!
             (lambda ()
               ;; NOT `in-sep!': the domain half (IN w X) is in the context, so
               ;; sep-mi grounds it on the spot and leaves ONE open leaf --
               ;; in-sep! demands both and errors.  Close whatever is open.
               (let ((g (dk-goal)))
                 (if (and (pair? (caddr g)) (eq? (car (caddr g)) 'SEP))
                     (for-each (lambda (l) (dk-focus! l) (ass))
                               (dk-opened (lambda () (sep-mi))))
                     (ass)))))))))))

(define rdc-r-EX (dk-fact! 'dc-on-nn-pred rdc-r-X rdc-r-a rdc-r-nxt-term))
(define rdc-r-f  (dk-skolem! rdc-r-EX))
(define rdc-r-fall
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f rdc-r-f)))
           "the per-stage step property"))

(witness! rdc-r-f
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (if (and (pair? g) (eq? (car g) 'FORALL))
             (let* ((kv (dk-di-var!))
                    (h  (dk-apply! rdc-r-fall kv)))
               (fact 'fun-apply-type-c rdc-r-f 'NN rdc-r-X kv)   ; f(k) in X
               (sep-me (car (dk-landed (lambda () (lam-b-h h)))))
               (ass))
             (ass)))))))

(rdc-qed! 'dc-on-nn)
