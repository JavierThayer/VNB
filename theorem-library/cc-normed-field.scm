;;; cc-normed-field.scm -- IS-NORMED-FIELD(CC-NORMED-FIELD), PROVED.
;;;
;;; The complex numbers are a normed field under `magnitude'.  Until now this
;;; was the asserted axiom `cc-is-normed-field'
;;; (structure-library/numeric-instances.scm:324) -- the last unwarranted
;;; assertion of that file's IS-X witnesses, and the one that stood between the
;;; complex plane and every `modulo 0' statement about CC as a normed field
;;; (the complex half of IS-DIFF-ON / HOLOMORPHIC-ON reaches CC only through
;;; IS-NORMED-FIELD(CC-NORMED-FIELD)).
;;;
;;; THE PROOF IS theorem-library/rr-is-normed-field.scm's, verbatim in shape,
;;; with the complex data substituted: unfold the defining IFF, `surface-goal!'
;;; the accessors down to the lambda slots and the numeric operators, split the
;;; conjunction, and close each conjunct by its shape.  Seventeen leaves:
;;;
;;;   length(cc-normed-field) = 7        cc-normed-field-def, len-r, arith
;;;   CC in SET                          cc-is-set
;;;   0 in CC, 1 in CC                   cc-zero-in, cc-one-in
;;;   four op-slot typings (lambda in FUN)
;;;                                      lam-t + the closure axioms
;;;                                      (cc-add/mul/neg-closed,
;;;                                      cc-magnitude-closed)
;;;                                      + cc-is-set / cartesian-set-iff
;;;   eight ring laws                    unfold, surface, peel, crs
;;;                                      ("cc" is a ring domain of
;;;                                      comm-ring-simplify, so `crs' decides
;;;                                      these over CC-typed generators exactly
;;;                                      as it does over RR-typed ones)
;;;   is-norm(magnitude-lambda, ...)     lam-t as above for the FUN clause;
;;;                                      peel, lam-b, then cc-magnitude-nonneg,
;;;                                      cc-magnitude-zero-iff,
;;;                                      cc-magnitude-mul,
;;;                                      cc-magnitude-triangle
;;;
;;; WHAT IS *NOT* PROVED HERE, because IS-NORMED-FIELD does not say it: that
;;; every nonzero element has a multiplicative inverse, and that 0 /= 1.  Those
;;; are the separate axioms `normed-field-mul-inverses' and
;;; `normed-field-zero-not-one' (structure-library/normed-field.scm), asserted
;;; of EVERY normed field; they are no part of this predicate and no part of
;;; this bill.  (Inverses are true of CC and `cc-recip-inverse' says so; there
;;; is no `cc-zero-not-one' in the tree at all.  Proving either here would
;;; prove something other than the statement being retired.)
;;;
;;; The four magnitude laws are theorems since 2026-08-17
;;; (theorem-library/cc-magnitude.scm), which is what made this reachable: the
;;; norm slot holds `(VNB-LAMBDA x_ CC (magnitude x_))' -- a genuine set of
;;; pairs, so its FUN(CC,RR) typing is a `lam-t' -- and every clause of
;;; `is-norm' is one of those four theorems.
;;;
;;; LOAD WINDOW.  Lower bound: theorem-library/cc-magnitude (position 455; the
;;; four modulus laws), theorem-library/lambda-slot-apply (244; the
;;; lam-slot-*-apply bridges `surface-goal!' reads), theorem-library/
;;; rr-abs-basics (189) is NOT needed.  Upper bound: none at present -- nothing
;;; in the tree cites `cc-is-normed-field' (it appears in DEBT-BUNDLE s.4, the
;;; asserted names on NO bill), so the file may sit anywhere after 455.  The
;;; natural slot is IMMEDIATELY AFTER theorem-library/cc-magnitude, i.e. before
;;; cc-metric-space-proof.
;;;
;;; The name is the AXIOM's name, so any future citation keeps working; the
;;; band prints "re-installing the same statement" at the qed.
;;;
;;; Helper prefix: ccn-.

(define (ccn-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ccn-head g) (and (pair? g) (car g)))
;;; A genuine open LEAF: ungrounded and no rule has fired on it
;;; (proof-open-goals also lists ancestors).
(define (ccn-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))

(define ccn-carrier 'CC)
;;; The CLOSURE alist used for saturation: only the operations whose value lands
;;; back in the carrier.  `magnitude' maps CC into RR, so it must not be here --
;;; dk-saturate-slot-ops! types every hit's value in `carrier'.
(define ccn-closure '((+ . cc-add-closed) (* . cc-mul-closed) (- . cc-neg-closed)))
;;; The lookup used for a LAMBDA SLOT's typing, where the conclusion's class is
;;; the lambda's own range: here `magnitude' belongs.
(define ccn-lam-closure
  (cons '(magnitude . cc-magnitude-closed) ccn-closure))

;;; peel every leading FORALL/IMPLIES, guarding on PROGRESS (di only warns when
;;; it cannot decompose).
(define (ccn-peel!)
  (let lp ((n 20))
    (let ((before (ccn-goal)))
      (when (and (> n 0) (memq (ccn-head before) '(FORALL IMPLIES)))
        (di)
        (if (not (equal? (ccn-goal) before)) (lp (- n 1)))))))

;;; beta-reduce every slot application left standing (the magnitude lambda has
;;; no surface bridge); the arguments are typed by the peel above, so lam-b owes
;;; nothing.
(define (ccn-beta!)
  (let lp ((n 12))
    (let ((before (ccn-goal)))
      (quietly (lambda () (lam-b)))
      (when (and (> n 0) (not (equal? (ccn-goal) before))) (lp (- n 1))))))

;;; The op-slot typing  IN (VNB-LAMBDA ...) (FUN dom rng).  lam-t opens the
;;; pointwise typing and (unless a sibling already posted it) the sethood of the
;;; domain.  TAKE THE LEAVES lam-t OPENED; never search open leaves by shape.
(define (ccn-close-lambda-typing! g)
  (let* ((lam     (cadr g))
         (binder  (cadr lam))
         (body    (cadddr lam))
         (thm     (cdr (assq (car body) ccn-lam-closure)))
         (tupled? (and (pair? binder) (eq? (car binder) 'LIST)))
         (opened  (dk-opened (lambda () (lam-t)))))
    (define (pick head)
      (let ((hit (filter (lambda (n)
                           (let ((gg (wff-formula (sequent-node-assertion n))))
                             (and (pair? gg) (eq? (car gg) head))))
                         opened)))
        (and (pair? hit) (dk-focus! (car hit)))))
    (if (null? opened)
        (error "cc-is-normed-field: lam-t opened nothing on" g))
    (when (pick 'FORALL)
      (di)
      (let* ((g2 (ccn-goal)) (term (cadr g2)) (args (cdr term)))
        (if (pair? (cdr args))
            (begin (dk-have! (list 'AND (list 'IN (car args)  ccn-carrier)
                                        (list 'IN (cadr args) ccn-carrier)))
                   (fact thm (car args) (cadr args)))
            (fact thm (car args))))
      (ass))
    (when (pick 'IN)
      (fact 'cc-is-set)
      (when tupled?
        (dk-have! '(AND (IN CC SET) (IN CC SET)))
        (mac 'cartesian-set-iff))
      (ass))))

;;; Close an ATOM of a law or of is-norm, after peel + beta, by its shape.
(define (ccn-close-atom!)
  (let ((g (ccn-goal)))
    (cond
      ;; a pair in a product -- lam-b's owed obligation on a tupled lambda
      ((and (eq? (ccn-head g) 'IN)
            (pair? (caddr g)) (eq? (car (caddr g)) 'CARTESIAN))
       (for-each (lambda (n) (dk-focus! n) (ccn-close-atom!))
                 (dk-opened (lambda () (ci)))))
      ((and (eq? (ccn-head g) 'IN) (eq? (caddr g) 'CC))
       (cond ((dk-asm? g) (ass))
             ((eqv? (cadr g) 0) (fact 'cc-zero-in) (ass))
             ((eqv? (cadr g) 1) (fact 'cc-one-in) (ass))
             ((and (pair? (cadr g)) (assq (car (cadr g)) ccn-closure))
              (let* ((t (cadr g)) (args (cdr t))
                     (thm (cdr (assq (car t) ccn-closure))))
                (if (pair? (cdr args))
                    (begin (dk-have! (list 'AND (list 'IN (car args)  'CC)
                                                (list 'IN (cadr args) 'CC)))
                           (fact thm (car args) (cadr args)))
                    (fact thm (car args))))
              (ass))
             (#t (error "cc-is-normed-field: no route to" g))))
      ((and (eq? (ccn-head g) 'IN) (eq? (caddr g) 'RR))
       (if (dk-asm? g) (ass) (in-rr)))
      ;; the norm laws
      ((and (eq? (ccn-head g) '<=) (eqv? (cadr g) 0))
       (fact 'cc-magnitude-nonneg (cadr (caddr g))) (ass))
      ((eq? (ccn-head g) 'IFF)
       (fact 'cc-magnitude-zero-iff (cadr (cadr (cadr g)))) (ass))
      ;; cc-magnitude-triangle / cc-magnitude-mul have AND antecedents, which
      ;; `fact' will not split: build the conjunction first.
      ((and (eq? (ccn-head g) '<=) (dk-contains? g 'magnitude))
       (let* ((arg (cadr (cadr g))) (a (cadr arg)) (b (caddr arg)))
         (dk-have! (list 'AND (list 'IN a 'CC) (list 'IN b 'CC)))
         (fact 'cc-magnitude-triangle a b))
       (ass))
      ((and (eq? (ccn-head g) '=) (dk-contains? g 'magnitude))
       (let* ((arg (cadr (cadr g))) (a (cadr arg)) (b (caddr arg)))
         (dk-have! (list 'AND (list 'IN a 'CC) (list 'IN b 'CC)))
         (fact 'cc-magnitude-mul a b))
       (ass))
      ;; a ring identity over typed generators
      ((memq (ccn-head g) '(= <=))
       (dk-saturate-slot-ops! ccn-carrier ccn-closure)
       (crs))
      (#t (error "cc-is-normed-field: unexpected atom" g)))))

;;; peel, saturate, split ANDs recursively; beta and close only at the ATOMS.
;;;
;;; SATURATE BEFORE BETA, AND BETA ONLY WHEN NO BINDER IS LEFT -- the two traps
;;; measured on rr-is-normed-field.scm (its comment records both): the lam-slot
;;; bridges are guarded on their arguments being in the carrier, and a lam-b
;;; fired under a still-unpeeled binder posts its owed typing in the OUTER
;;; context, where the binder is free -- an unprovable leaf.
(define (ccn-close-body! fuel)
  (if (<= fuel 0) (error "cc-is-normed-field: body split did not terminate"))
  (ccn-peel!)
  (dk-saturate-slot-ops! ccn-carrier ccn-closure)
  (let ((g (ccn-goal)))
    (cond
      ((eq? (ccn-head g) 'AND)
       (for-each (lambda (k) (dk-focus! k) (ccn-close-body! (- fuel 1)))
                 (dk-opened (lambda () (di)))))
      ((memq (ccn-head g) '(FORALL IMPLIES))
       (error "cc-is-normed-field: peel stalled on" g))
      (#t
       (ccn-beta!)
       (dk-saturate-slot-ops! ccn-carrier ccn-closure)
       (ccn-close-atom!)))))

;;; Discharge the FOCUSED conjunct by its shape.
(define (ccn-close-leaf!)
  (let ((g (ccn-goal)))
    (cond
      ((and (eq? (ccn-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac 'cc-normed-field-def) (len-r) (arith))
      ((equal? g '(IN 0 CC)) (fact 'cc-zero-in) (ass))
      ((equal? g '(IN 1 CC)) (fact 'cc-one-in)  (ass))
      ((equal? g '(IN CC SET)) (fact 'cc-is-set) (ass))
      ((and (eq? (ccn-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
       (ccn-close-lambda-typing! g))
      ((memq (ccn-head g) '(is-associative is-commutative is-identity
                            has-inverses is-distributive))
       (mac (ccn-head g))
       (quietly (lambda () (surface-goal! 'CC-NORMED-FIELD)))
       (ccn-close-body! 20))
      ((eq? (ccn-head g) 'is-norm)
       (mac 'is-norm)
       (quietly (lambda () (surface-goal! 'CC-NORMED-FIELD)))
       ;; AND(FUN typing, forall a ...): split, then the typing by lam-t and
       ;; the value clauses by peel/beta/shape.
       (for-each (lambda (k)
                   (dk-focus! k)
                   (let ((gk (ccn-goal)))
                     (if (and (eq? (ccn-head gk) 'IN)
                              (pair? (cadr gk)) (eq? (car (cadr gk)) 'VNB-LAMBDA))
                         (ccn-close-lambda-typing! gk)
                         (ccn-close-body! 20))))
                 (dk-opened (lambda () (di)))))
      (#t (error "cc-is-normed-field: unexpected conjunct" g)))))

(sp (make-wff '(IS-NORMED-FIELD CC-NORMED-FIELD)))
(mac 'IS-NORMED-FIELD)
(quietly (lambda () (surface-goal! 'CC-NORMED-FIELD)))
;; split the top conjunction to leaves
(let split ((fuel 40))
  (let ((andl (find-first (lambda (s)
                            (eq? (ccn-head (wff-formula (sequent-node-assertion s))) 'AND))
                          (ccn-open))))
    (when andl
      (if (= fuel 0) (error "cc-is-normed-field: AND split did not terminate"))
      (dk-focus! andl) (di) (split (- fuel 1)))))
;; close each conjunct, insisting on progress
(let sweep ((fuel 40))
  (let* ((open (ccn-open)) (n (length open)))
    (when (pair? open)
      (if (= fuel 0) (error "cc-is-normed-field: sweep out of fuel"))
      (dk-focus! (car open))
      (let ((g (ccn-goal)))
        (ccn-close-leaf!)
        (if (>= (length (ccn-open)) n)
            (error "cc-is-normed-field: this conjunct did not close" g)))
      (sweep (- fuel 1)))))
(if (not (proof-done? *ps*))
    (begin
      (for-each (lambda (l)
                  (display "   OPEN: ")
                  (display (expression->string (wff-formula (sequent-node-assertion l))))
                  (newline))
                (proof-open-goals *ps*))
      (error "cc-is-normed-field: proof did not close")))
(qed 'cc-is-normed-field)
(topic! 'cc-is-normed-field 'algebra)
(alias! 'cc-is-normed-field "the complex numbers are a normed field under the modulus")
