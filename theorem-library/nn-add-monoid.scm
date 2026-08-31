;;; nn-add-monoid.scm -- IS-COMM-MONOID(NN-ADD-MONOID), PROVED.
;;;
;;; The last of the numeric-instance assertions with a dependent, and the one
;;; that had to wait for a partner: it and `comm-monoid-is-monoid' were BOTH
;;; unwarranted leaves of the same single bill (poly-is-ring), so each shadowed
;;; the other and neither was worth anything alone.  With comm-monoid-is-monoid
;;; proved (subtype-laws.scm) this one finally moves a bill.
;;;
;;; Shape: zz-ring-is-ring.scm's, with one deliberate difference.  Unfold the
;;; IS-COMM-MONOID definition, `surface-goal!' the accessors down to NN
;;; arithmetic, split, and close each conjunct.  But the three LAW conjuncts are
;;; closed by CITING the NN axioms (nn-add-assoc, nn-add-comm, nn-add-zero,
;;; primitive in number-systems.scm) and NOT by `crs'.
;;;
;;; That is the point worth recording.  `crs' decides commutative-RING
;;; identities, and NN is not a ring -- it has no negation.  The three
;;; identities here are true of NN, so `crs' would have closed the goals and
;;; nothing would have looked wrong; but the justification would have been "this
;;; holds in any commutative ring", which is not a statement about NN.  The
;;; oracle is sound where it applies and the burden is on the caller to know
;;; that it applies.  Citing the axioms costs three extra lines and says
;;; something true.
;;;
;;; Needs: interactive + qed/proof-debt, driver-kit (have!, dk-focus!,
;;; dk-opened), transport (surface-goal!).  Must precede
;;; theorem-library/poly-is-ring-proof, which cites it by name.

;;; ---- file-local driver helpers (nm- prefix; never named like a tactic) ----
(define (nm-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (nm-head g) (and (pair? g) (car g)))
(define (nm-open) (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))

(define (nm-peel!)
  (let pl ((fuel 20))
    (let ((before (nm-goal)))
      (when (and (> fuel 0) (memq (nm-head before) '(FORALL IMPLIES)))
        (di)
        (if (equal? (nm-goal) before)
            (error "nn-add-monoid: di made no progress on" before)
            (pl (- fuel 1)))))))

;;; Read the eigenvariables off the GOAL, never off the context.  `dk-asms''
;;; order is not the peel order -- taking the NN-typed hypotheses in context
;;; order yields (w v u) where the goal wants (u v w), and `fact' then builds an
;;; instance that does not match the goal, which `ass' quietly refuses.  The
;;; goal's own shape is unambiguous.
(define (nm-assoc-vars g)        ; (= (+ (+ a b) c) (+ a (+ b c)))
  (let ((lhs (cadr g))) (list (cadr (cadr lhs)) (caddr (cadr lhs)) (caddr lhs))))
(define (nm-comm-vars g)         ; (= (+ a b) (+ b a))
  (let ((lhs (cadr g))) (list (cadr lhs) (caddr lhs))))
(define (nm-ident-var g)         ; (AND (= (+ 0 u) u) (= (+ u 0) u))
  (caddr (cadr g)))

(define (nm-and* xs)
  (fold-right (lambda (x acc) (if acc (list 'AND x acc) x)) #f xs))

;;; Focus the open leaf whose goal satisfies PRED.  Errors on a miss -- a focus
;;; helper that returns #f and leaves focus put hides every later failure.
(define (nm-focus-leaf! pred)
  (let ((ls (filter (lambda (n) (pred (wff-formula (sequent-node-assertion n))))
                    (filter (lambda (s) (null? (sequent-node-in-arrows s)))
                            (proof-open-goals *ps*)))))
    (if (null? ls) (error "nn-add-monoid: no open leaf matches"))
    (dk-focus! (car ls))))

(define (nm-close-leaf!)
  (let ((g (nm-goal)))
    (cond
      ;; length(nn-add-monoid) = 3
      ((and (eq? (nm-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac 'nn-add-monoid-def) (len-r) (arith))
      ((equal? g '(IN NN SET)) (fact 'nn-is-set) (ass))
      ;; the op-slot typing.  Until 2026-08-29 the slot held the shared constant
      ;; `binplus' and this cited binplus-in-fun-nn -- one of the fourteen
      ;; axioms that jointly proved NN = ZZ = QQ = RR = CC and hence FALSITY.
      ;; The slot now holds a tupled VNB-LAMBDA, so the typing is PROVED: lam-t
      ;; leaves the pointwise closure fact (nn-add-closed) and the sethood of
      ;; CARTESIAN(NN,NN).  Nothing is asserted that was not already there.
      ((and (eq? (nm-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
       ;; Take the leaves lam-t OPENED; a shape search over all open leaves
       ;; picks up a sibling conjunct's IN goal (see zz-ring-is-ring.scm).
       (let* ((opened (dk-opened (lambda () (lam-t))))
              (pick (lambda (head)
                      (let ((hit (filter (lambda (n)
                                           (let ((gg (wff-formula
                                                      (sequent-node-assertion n))))
                                             (and (pair? gg) (eq? (car gg) head))))
                                         opened)))
                        (and (pair? hit) (dk-focus! (car hit)))))))
         (when (pick 'FORALL)
           (di)
           (let* ((g2 (nm-goal)) (sum (cadr g2)) (a (cadr sum)) (b (caddr sum)))
             (dk-have! (list 'AND (list 'IN a 'NN) (list 'IN b 'NN)))
             (fact 'nn-add-closed a b))
           (ass))
         ;; sethood is conditional: hash-consing means a sibling conjunct may
         ;; already have posted the identical node, so lam-t opens one leaf.
         (when (pick 'IN)
           (fact 'nn-is-set)
           (dk-have! '(AND (IN NN SET) (IN NN SET)))
           (mac 'cartesian-set-iff)
           (ass))))
      ((and (eq? (nm-head g) 'IN) (number? (cadr g))) (arith))
      ;; a law: unfold, drop to the surface, peel, then CITE.
      ((memq (nm-head g) '(is-associative is-commutative is-identity))
       (let ((law (nm-head g)))
         (mac law)
         (quietly (lambda () (surface-goal! 'NN-ADD-MONOID)))
         (nm-peel!)
         ;; NN-ADD-MONOID's ADD slot holds a tupled VNB-LAMBDA now, not the
         ;; shared constant `binplus', so the law goals arrive as lambda
         ;; APPLICATIONS.  Take them down to `+' before citing the NN axioms.
         (dk-saturate-slot-ops! 'NN '((+ . nn-add-closed)))
         (let ((gg (nm-goal)))
           (case law
             ((is-associative)
              (let ((vs (nm-assoc-vars gg)))
                (dk-have! (nm-and* (map (lambda (v) (list 'IN v 'NN)) vs)))
                (apply fact 'nn-add-assoc vs)
                (ass)))
             ((is-commutative)
              (let ((vs (nm-comm-vars gg)))
                (dk-have! (nm-and* (map (lambda (v) (list 'IN v 'NN)) vs)))
                (apply fact 'nn-add-comm vs)
                (ass)))
             ((is-identity)
              ;; two-sided: u + 0 = u is the axiom; 0 + u = u is that plus
              ;; commutativity.  Establish both, THEN split the conjunction.
              (let ((u (nm-ident-var gg)))
                (fact 'nn-add-zero u)                            ; u + 0 = u
                (dk-have! (list 'AND '(IN 0 NN) (list 'IN u 'NN)))  ; from-context!
                (fact 'nn-add-comm 0 u)                          ; 0 + u = u + 0
                (dk-have! (list '= (list '+ 0 u) u)
                       (lambda ()
                         (subst (list '= (list '+ 0 u) (list '+ u 0)))
                         (ass)))
                (for-each (lambda (k) (dk-focus! k) (ass))
                          (dk-opened (lambda () (di))))))))))
      (else (error "nn-add-monoid: unexpected conjunct" g)))))

(sp (make-wff '(IS-COMM-MONOID NN-ADD-MONOID)))
(mac 'IS-COMM-MONOID)
(quietly (lambda () (surface-goal! 'NN-ADD-MONOID)))

;;; Split the conjunction to leaves.  Filtering on in-arrows is what stops the
;;; split from re-finding the conjunction it just split (see zz-ring-is-ring).
(let split ((fuel 40))
  (let ((andl (find-first
               (lambda (s) (eq? (nm-head (wff-formula (sequent-node-assertion s))) 'AND))
               (nm-open))))
    (when andl
      (if (= fuel 0) (error "nn-add-monoid: AND split did not terminate"))
      (dk-focus! andl) (di) (split (- fuel 1)))))

;;; Close each conjunct, insisting on PROGRESS: a pass that leaves the open-leaf
;;; count unchanged names the conjunct that failed instead of looping on it.
(let sweep ((fuel 40))
  (let* ((open (nm-open)) (n (length open)))
    (when (pair? open)
      (if (= fuel 0) (error "nn-add-monoid: sweep out of fuel"))
      (dk-focus! (car open))
      (let ((g (nm-goal)))
        (nm-close-leaf!)
        (if (>= (length (nm-open)) n)
            (error "nn-add-monoid: this conjunct did not close" g)))
      (sweep (- fuel 1)))))

(if (proof-done? *ps*)
    (qed 'nn-add-monoid-is-comm-monoid)
    (begin
      (display "\n*** nn-add-monoid did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (sequent-node-assertion l)))
                  (newline))
                (nm-open))
      (error "nn-add-monoid: unfinished")))
