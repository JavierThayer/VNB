;;; rr-is-normed-field.scm -- IS-NORMED-FIELD(RR-NORMED-FIELD), PROVED.
;;;
;;; The reals are a normed field under abs.  Until now this was the asserted
;;; axiom `rr-is-normed-field' (structure-library/numeric-instances.scm), warranted
;;; `well-known' on 2026-08-24 and the SOLE door from RR to the ring world
;;; (NORMED-FIELD-AS-COMMUTATIVE-RING), so it sat in 73 bills.
;;;
;;; The plan is theorem-library/zz-ring-is-ring.scm's, one slot wider: unfold the
;;; defining IFF, `surface-goal!' the accessors down to the lambda slots and the
;;; surface operators, split the conjunction, and close each conjunct by its
;;; shape.  Seventeen leaves:
;;;
;;;   length(rr-normed-field) = 7            rr-normed-field-def, len-r, arith
;;;   rr in set                              rr-is-set
;;;   0 in rr, 1 in rr                       arith
;;;   four op-slot typings (lambda in FUN)   lam-t + the closure axiom
;;;                                          (rr-add/mul/neg-closed, rr-abs-closed)
;;;                                          + rr-is-set / cartesian-set-iff
;;;   eight ring laws                        unfold, surface, peel, crs
;;;   is-norm(abs-lambda, ...)               lam-t as above for the FUN clause;
;;;                                          peel, lam-b, then rr-abs-nonneg,
;;;                                          rr-abs-zero, rr-abs-mult, rr-abs-triangle
;;;
;;; The warrant's two blockers are both gone: the norm slot has held
;;; `(VNB-LAMBDA x_ RR (abs x_))' since 2026-08-31, so its FUN(RR,RR) typing is a
;;; `lam-t' and not a sethood claim about the primitive `abs'; and the four
;;; abs laws (theorem-library/rr-abs-basics.scm) load well before the first
;;; theorem that bills this one (rr-nvs-is-normed-vector-space).
;;;
;;; LOAD WINDOW.  Lower bound: theorem-library/lambda-slot-apply (surface-goal!'s
;;; lam-slot-*-apply bridges, in *surface-bridge-theorems*) and
;;; theorem-library/rr-abs-basics (the abs laws) -- both must precede this file.
;;; Upper bound: theorem-library/rr-nvs-exemplification, the first proof whose
;;; bill carries rr-is-normed-field.  The natural slot is immediately after
;;; zz-ring-is-ring, i.e. immediately before rr-nvs-exemplification.
;;;
;;; The name is the AXIOM's name, so every existing citation keeps working; the
;;; band prints "re-installing the same statement" at the qed.

(define (rnf-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (rnf-head g) (and (pair? g) (car g)))
;;; A genuine open LEAF: ungrounded and no rule has fired on it (zz-ring-is-ring's
;;; zr-open, for the same reason: proof-open-goals also lists ancestors).
(define (rnf-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))

(define rnf-carrier 'RR)
(define rnf-closure '((+ . rr-add-closed) (* . rr-mul-closed)
                      (- . rr-neg-closed) (abs . rr-abs-closed)))

;;; peel every leading FORALL/IMPLIES, guarding on PROGRESS (di only warns when
;;; it cannot decompose).
(define (rnf-peel!)
  (let lp ((n 20))
    (let ((before (rnf-goal)))
      (when (and (> n 0) (memq (rnf-head before) '(FORALL IMPLIES)))
        (di)
        (if (not (equal? (rnf-goal) before)) (lp (- n 1)))))))

;;; beta-reduce every slot application left standing (the abs lambda has no
;;; surface bridge); the arguments are typed by the peel above, so lam-b owes
;;; nothing.
(define (rnf-beta!)
  (let lp ((n 12))
    (let ((before (rnf-goal)))
      (quietly (lambda () (lam-b)))
      (when (and (> n 0) (not (equal? (rnf-goal) before))) (lp (- n 1))))))

;;; The op-slot typing  IN (VNB-LAMBDA ...) (FUN dom rng).  lam-t opens the
;;; pointwise typing and (unless a sibling already posted it) the sethood of the
;;; domain.  TAKE THE LEAVES lam-t OPENED; never search open leaves by shape.
(define (rnf-close-lambda-typing! g)
  (let* ((lam     (cadr g))
         (binder  (cadr lam))
         (body    (cadddr lam))
         (thm     (cdr (assq (car body) rnf-closure)))
         (tupled? (and (pair? binder) (eq? (car binder) 'LIST)))
         (opened  (dk-opened (lambda () (lam-t)))))
    (define (pick head)
      (let ((hit (filter (lambda (n)
                           (let ((gg (wff-formula (sequent-node-assertion n))))
                             (and (pair? gg) (eq? (car gg) head))))
                         opened)))
        (and (pair? hit) (dk-focus! (car hit)))))
    (if (null? opened)
        (error "rr-is-normed-field: lam-t opened nothing on" g))
    (when (pick 'FORALL)
      (di)
      (let* ((g2 (rnf-goal)) (term (cadr g2)) (args (cdr term)))
        (if (pair? (cdr args))
            (begin (dk-have! (list 'AND (list 'IN (car args)  rnf-carrier)
                                        (list 'IN (cadr args) rnf-carrier)))
                   (fact thm (car args) (cadr args)))
            (fact thm (car args))))
      (ass))
    (when (pick 'IN)
      (fact 'rr-is-set)
      (when tupled?
        (dk-have! '(AND (IN RR SET) (IN RR SET)))
        (mac 'cartesian-set-iff))
      (ass))))

;;; Close an ATOM of a law or of is-norm, after peel + beta, by its shape.
(define (rnf-close-atom!)
  (let ((g (rnf-goal)))
    (cond
      ;; a pair in a product -- lam-b's owed obligation on a tupled lambda
      ((and (eq? (rnf-head g) 'IN)
            (pair? (caddr g)) (eq? (car (caddr g)) 'CARTESIAN))
       (for-each (lambda (n) (dk-focus! n) (rnf-close-atom!))
                 (dk-opened (lambda () (ci)))))
      ((and (eq? (rnf-head g) 'IN) (eq? (caddr g) 'RR))
       (if (dk-asm? g) (ass) (in-rr)))
      ;; the norm laws
      ((and (eq? (rnf-head g) '<=) (eqv? (cadr g) 0))
       (fact 'rr-abs-nonneg (cadr (caddr g))) (ass))
      ((eq? (rnf-head g) 'IFF)
       (fact 'rr-abs-zero (cadr (cadr (cadr g)))) (ass))
      ;; rr-abs-triangle / rr-abs-mult have AND antecedents, which `fact' will
      ;; not split: build the conjunction first.
      ((and (eq? (rnf-head g) '<=) (dk-contains? g 'abs))
       (let* ((arg (cadr (cadr g))) (a (cadr arg)) (b (caddr arg)))
         (dk-have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
         (fact 'rr-abs-triangle a b))
       (ass))
      ((and (eq? (rnf-head g) '=) (dk-contains? g 'abs))
       (let* ((arg (cadr (cadr g))) (a (cadr arg)) (b (caddr arg)))
         (dk-have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
         (fact 'rr-abs-mult a b))
       (ass))
      ;; a ring identity over typed generators
      ((memq (rnf-head g) '(= <=))
       (dk-saturate-slot-ops! rnf-carrier rnf-closure)
       (crs))
      (else (error "rr-is-normed-field: unexpected atom" g)))))

;;; peel, saturate, split ANDs recursively; beta and close only at the ATOMS.
;;;
;;; SATURATE BEFORE BETA, AND BETA ONLY WHEN NO BINDER IS LEFT.  Two traps, both
;;; measured on this proof:
;;;   * the lam-slot bridges are guarded on their arguments being in the
;;;     carrier, and a nested application's argument (u + v) is typed by nothing
;;;     until saturation lands it; a lam-b fired first owes
;;;     `[u + v, w] in cartesian(rr, rr)' as an extra leaf per redex (two per
;;;     associativity conjunct).
;;;   * a lam-b fired on `forall b in rr. ... abs-lam(a * b) ...' licenses the
;;;     redex against the binder's guard but posts the owed `(a * b) in rr' at
;;;     the OUTER context, where b is free -- an UNPROVABLE leaf (CLAUDE.md,
;;;     "peel and type first, then beta").  So the abs lambda, which has no
;;;     bridge, is reduced only once every binder above it has been peeled and
;;;     dk-saturate-slot-ops! has typed its argument.
(define (rnf-close-body! fuel)
  (if (<= fuel 0) (error "rr-is-normed-field: body split did not terminate"))
  (rnf-peel!)
  (dk-saturate-slot-ops! rnf-carrier rnf-closure)
  (let ((g (rnf-goal)))
    (cond
      ((eq? (rnf-head g) 'AND)
       (for-each (lambda (k) (dk-focus! k) (rnf-close-body! (- fuel 1)))
                 (dk-opened (lambda () (di)))))
      ((memq (rnf-head g) '(FORALL IMPLIES))
       (error "rr-is-normed-field: peel stalled on" g))
      (else
       (rnf-beta!)
       (dk-saturate-slot-ops! rnf-carrier rnf-closure)
       (rnf-close-atom!)))))

;;; Discharge the FOCUSED conjunct by its shape.
(define (rnf-close-leaf!)
  (let ((g (rnf-goal)))
    (cond
      ((and (eq? (rnf-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac 'rr-normed-field-def) (len-r) (arith))
      ((and (eq? (rnf-head g) 'IN) (number? (cadr g)))
       (arith))
      ((equal? g '(IN RR SET))
       (fact 'rr-is-set) (ass))
      ((and (eq? (rnf-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
       (rnf-close-lambda-typing! g))
      ((memq (rnf-head g) '(is-associative is-commutative is-identity
                            has-inverses is-distributive))
       (mac (rnf-head g))
       (quietly (lambda () (surface-goal! 'RR-NORMED-FIELD)))
       (rnf-close-body! 20))
      ((eq? (rnf-head g) 'is-norm)
       (mac 'is-norm)
       (quietly (lambda () (surface-goal! 'RR-NORMED-FIELD)))
       ;; AND(FUN typing, forall a ...): split, then the typing by lam-t and
       ;; the value clauses by peel/beta/shape.
       (for-each (lambda (k)
                   (dk-focus! k)
                   (let ((gk (rnf-goal)))
                     (if (and (eq? (rnf-head gk) 'IN)
                              (pair? (cadr gk)) (eq? (car (cadr gk)) 'VNB-LAMBDA))
                         (rnf-close-lambda-typing! gk)
                         (rnf-close-body! 20))))
                 (dk-opened (lambda () (di)))))
      (else (error "rr-is-normed-field: unexpected conjunct" g)))))

(sp (make-wff '(IS-NORMED-FIELD RR-NORMED-FIELD)))
(mac 'IS-NORMED-FIELD)
(quietly (lambda () (surface-goal! 'RR-NORMED-FIELD)))
;; split the top conjunction to leaves
(let split ((fuel 40))
  (let ((andl (find-first (lambda (s)
                            (eq? (rnf-head (wff-formula (sequent-node-assertion s))) 'AND))
                          (rnf-open))))
    (when andl
      (if (= fuel 0) (error "rr-is-normed-field: AND split did not terminate"))
      (dk-focus! andl) (di) (split (- fuel 1)))))
;; close each conjunct, insisting on progress
(let sweep ((fuel 40))
  (let* ((open (rnf-open)) (n (length open)))
    (when (pair? open)
      (if (= fuel 0) (error "rr-is-normed-field: sweep out of fuel"))
      (dk-focus! (car open))
      (let ((g (rnf-goal)))
        (rnf-close-leaf!)
        (if (>= (length (rnf-open)) n)
            (error "rr-is-normed-field: this conjunct did not close" g)))
      (sweep (- fuel 1)))))
(if (not (proof-done? *ps*))
    (begin
      (for-each (lambda (l)
                  (display "   OPEN: ")
                  (display (expression->string (wff-formula (sequent-node-assertion l))))
                  (newline))
                (proof-open-goals *ps*))
      (error "rr-is-normed-field: proof did not close")))
(qed 'rr-is-normed-field)
(topic! 'rr-is-normed-field 'algebra)
(alias! 'rr-is-normed-field "the reals are a normed field under abs")
