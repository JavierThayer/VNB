;;; rr-nvs-exemplification.scm -- THE FIRST WITNESS OF A NORMED VECTOR SPACE.
;;;
;;;     RR-NVS = [ normed-field-as-commutative-ring(rr-normed-field),   SCAL
;;;                RR,                                                 VEC
;;;                lambda([x,y] in RRxRR, x + y),                       VADD
;;;                0,                                                  VZERO
;;;                lambda(x in RR, -x),                                 VNEG
;;;                lambda([r,x] in RRxRR, r * x),                        ACT
;;;                lambda(x in RR, abs x) ]                             VNRM
;;;
;;; the reals as a ONE-DIMENSIONAL real normed vector space.  n = 1 is the whole
;;; point: no finite products, no bases, no linear algebra, and every obligation
;;; it raises is an ordinary fact about RR and abs.
;;;
;;; WHY IT MATTERS.  `IS-NORMED-VECTOR-SPACE' pinned length(scal(s)) to 6 and to
;;; 7 at once until 2026-08-23, so hahn-banach, norm-as-sup, vector-taylor and
;;; two more were VACUOUS.  That repair made the predicate SATISFIABLE.  It
;;; exhibited nothing satisfying it: `structure-exemplification-audit' still put
;;; NORMED-VECTOR-SPACE in its UNWITNESSED list, and a repaired-but-unwitnessed
;;; predicate is an ordinary missing construction -- but it is also why no proof
;;; in the library had ever had to MEET the hypothesis, which is how the defect
;;; sat for months.  This is the model.
;;;
;;; The plan is the one prove-scripts/drives/rr-nvs-exemplification-drive.scm
;;; laid out on 2026-08-23 and left for the user to drive.  Two things changed
;;; under it since:
;;;
;;;   * THE SLOTS HOLD LAMBDAS, not `binplus'/`bintimes'/`binneg'.  One object
;;;     cannot be a set function with five different domains; asserting so
;;;     proved NN = ZZ = QQ = RR = CC and thence FALSITY (numeric-instances.scm,
;;;     repaired 2026-08-29).  So the op-slot typings are PROVED by `lam-t' plus
;;;     the carrier's closure axioms, where the drive's notes cited
;;;     binplus-in-fun-rr and its siblings.
;;;
;;;   * THE SCALAR PINNING LAW needed a kernel addition to close.  `scal(s) =
;;;     normed-field-as-commutative-ring(rr-normed-field)' reduces to X = X, and
;;;     `=' is PARTIAL, so that is a DEFINEDNESS claim.  With `binplus' in the
;;;     slots the tuple was atoms all the way down and closed syntactically;
;;;     with lambdas it did not, because nothing in the theory said a lambda is
;;;     an object -- VNB-LAMBDA had NO characterisation at all, and definedness
;;;     was obtainable only as a by-product of typing it into a FUN, i.e. of
;;;     TOTALITY.  `term-self-defined?' (primitive-inferences.scm) now says a
;;;     lambda denotes whenever its DOMAIN does, which is the user's reading and
;;;     the right one: the lambda is its graph, so an undefined body merely
;;;     leaves the graph empty.  Definedness is not sethood -- `ORD = ORD'
;;;     closes and `ORD in SET' does not -- so a proper-class domain gives a
;;;     defined proper CLASS, still in no FUN.
;;;
;;; So the witness is a citation exercise, as the drive promised, plus one
;;; foundational sentence about what a lambda is.  The next rung -- RR^n, with
;;; FINSUM for the sum norm -- is where the real work starts.

(declare-instance! 'RR-NVS 'NORMED-VECTOR-SPACE 'rr-nvs-def
  '((NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) RR
    (VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (+ x_ y_)) 0
    (VNB-LAMBDA x_ RR (- x_))
    (VNB-LAMBDA (LIST r_ x_) (CARTESIAN RR RR) (* r_ x_))
    (VNB-LAMBDA x_ RR (abs x_))))

(define (rn-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (rn-head) (let ((g (rn-goal))) (and (pair? g) (car g))))

;;; peel every leading FORALL/IMPLIES, guarding on progress
(define (rn-peel!)
  (let lp ((n 12))
    (let ((before (rn-goal)))
      (when (and (> n 0) (memq (rn-head) '(FORALL IMPLIES)))
        (di)
        (if (not (equal? (rn-goal) before)) (lp (- n 1)))))))

;;; beta-reduce every slot application; the arguments are typed by the peel above
(define (rn-beta!)
  (let lp ((n 12))
    (let ((before (rn-goal)))
      (quietly (lambda () (lam-b)))
      (when (and (> n 0) (not (equal? (rn-goal) before))) (lp (- n 1))))))

(sp (make-wff '(IS-NORMED-VECTOR-SPACE RR-NVS)))
(mac 'IS-NORMED-VECTOR-SPACE)
(let loop ((n 0))
  (let ((any #f))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (and (pair? (rn-goal)) (eq? (car (rn-goal)) 'AND))
                    (begin (set! any #t) (vnb-guard (lambda () (di))))))
              (proof-leaves))
    (if (and any (< n 40)) (loop (+ n 1)))))
(for-each (lambda (l)
            (dk-focus! l)
            (vnb-guard (lambda () (surface-goal! 'RR-NVS)))
            (for-each (lambda (m) (vnb-guard (lambda () (mac m))))
                      '(rr-scalar-ring-carr rr-scalar-ring-add
                        rr-scalar-ring-mul  rr-scalar-ring-one
                        rr-scalar-ring-zero rr-scalar-ring-neg)))
          (proof-leaves))


;;; ONE closer, applied to whatever a leaf turns out to be, and iterated to a
;;; fixpoint.  Facts are PER-NODE: landing rr-is-set once before the loop puts it
;;; in one leaf's context and nobody else's, which is why the first draft left
;;; `rr in set' open three leaves later.
(define (rn-close-leaf!)
  (let ((g (rn-goal)))
    (cond
      ;; a pair in a product -- lam-b's owed obligation on a tupled lambda
      ((and (pair? g) (eq? (car g) 'IN)
            (pair? (caddr g)) (eq? (car (caddr g)) 'CARTESIAN))
       (ci)
       (for-each (lambda (n) (dk-focus! n) (rn-close-leaf!))
                 (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                         (proof-open-goals *ps*))))
      ;; a real
      ((and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'RR))
       (quietly (lambda () (fact 'rr-is-set) (fact 'rr-zero-in) (fact 'rr-one-in)))
       (in-rr))
      ((equal? g '(IN RR SET)) (fact 'rr-is-set) (ass))
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (n) (dk-focus! n) (rn-close-leaf!))
                 (dk-opened (lambda () (di)))))
      ;; the norm laws
      ((and (pair? g) (eq? (car g) '<=) (eqv? (cadr g) 0))
       (fact 'rr-abs-nonneg (cadr (caddr g))) (ass))
      ((and (pair? g) (eq? (car g) 'IFF))
       (fact 'rr-abs-zero (cadr (cadr (cadr g)))) (ass))
      ;; rr-abs-triangle and rr-abs-mult have AND antecedents, which `fact' will
      ;; not split -- build the conjunction first or the citation lands the
      ;; IMPLICATION and `ass' finds nothing (CLAUDE.md).
      ((and (pair? g) (eq? (car g) '<=) (dk-contains? g 'abs))
       (let* ((arg (cadr (cadr g))) (a (cadr arg)) (b (caddr arg)))
         (dk-have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
         (fact 'rr-abs-triangle a b)) (ass))
      ((and (pair? g) (eq? (car g) '=) (dk-contains? g 'abs))
       (let* ((arg (cadr (cadr g))) (a (cadr arg)) (b (caddr arg)))
         (dk-have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
         (fact 'rr-abs-mult a b)) (ass))
      ;; the scalar law: both sides are the same closed term
      ((and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))
       (mac 'NORMED-FIELD-AS-COMMUTATIVE-RING)
       (quietly (lambda () (surface-goal! 'RR-NORMED-FIELD)))
       (rfl))
      ((and (pair? g) (eq? (car g) 'IS-RING))
       (fact 'rr-is-normed-field)
       (fact 'normed-field-as-commutative-ring-is-commutative-ring 'RR-NORMED-FIELD)
       (fact 'commutative-ring-is-ring
             '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))
       (ass))
      (else (quietly (lambda () (crs)))))))



;;; the op-slot typing: lam-t, then the carrier's closure axiom and sethood.
;;; Exactly the route ZZ-RING's slots take (theorem-library/zz-ring-is-ring.scm).
(define (rn-close-typing! g)
  (let* ((lam  (cadr g))
         (bind (cadr lam))
         (body (cadddr lam))
         (thm  (case (car body)
                 ((+)   'rr-add-closed) ((*) 'rr-mul-closed)
                 ((-)   'rr-neg-closed) ((abs) 'rr-abs-closed)
                 (else (error "rn: unknown slot body" body))))
         (tup? (and (pair? bind) (eq? (car bind) 'LIST)))
         (opened (dk-opened (lambda () (lam-t)))))
    (define (pick h)
      (let ((hit (filter (lambda (n)
                           (let ((gg (wff-formula (sequent-node-assertion n))))
                             (and (pair? gg) (eq? (car gg) h))))
                         opened)))
        (and (pair? hit) (dk-focus! (car hit)))))
    (when (pick 'FORALL)
      (di)
      (let* ((g2 (rn-goal)) (t (cadr g2)) (args (cdr t)))
        (if (pair? (cdr args))
            (begin (dk-have! (list 'AND (list 'IN (car args) 'RR)
                                        (list 'IN (cadr args) 'RR)))
                   (fact thm (car args) (cadr args)))
            (fact thm (car args))))
      (ass))
    (when (pick 'IN)
      (fact 'rr-is-set)
      (when tup?
        (dk-have! '(AND (IN RR SET) (IN RR SET)))
        (mac 'cartesian-set-iff))
      (ass))))

(define rn-left '())
(for-each
 (lambda (l)
   (dk-focus! l)
   (let ((g (rn-goal)))
     (cond
       ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
        (mac 'rr-nvs-def) (len-r) (arith))
       ((equal? g '(IN RR SET)) (rn-close-leaf!))
       ((and (eq? (car g) 'IN) (number? (cadr g))) (arith))
       ((eq? (car g) 'IS-RING) (rn-close-leaf!))
       ((and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
        (rn-close-typing! g))
       ((memq (car g) '(is-associative is-commutative is-identity has-inverses))
        (mac (car g)) (rn-peel!) (rn-beta!) (rn-close-leaf!))
       ((eq? (car g) '=) (rn-close-leaf!))
       (else
        (rn-peel!) (rn-beta!)
        (rn-close-leaf!)))))
 (proof-leaves))

;;; THE REAL LEAF SET.  `proof-leaves' counts nodes with no in-arrow; a node a
;;; rule fired on, whose children are still open, is NOT in it -- so "0 leaves"
;;; can coexist with (proof-done? #f).  zz-ring-is-ring.scm's `zr-open' is the
;;; same filter and the same reason.
(define (rn-open)
  (filter (lambda (n) (null? (sequent-node-in-arrows n))) (proof-open-goals *ps*)))

;;; iterate to a fixpoint: closing one leaf can leave another open (lam-b's
;;; owed pair-memberships arrive only when the beta actually fires).
(let sweep ((n 0))
  (let ((before (length (rn-open))))
    (for-each (lambda (l) (dk-focus! l) (vnb-guard (lambda () (rn-close-leaf!))))
              (rn-open))
    (if (and (< n 8) (< (length (rn-open)) before)) (sweep (+ n 1)))))
(if (not (proof-done? *ps*))
    (error "rr-nvs-exemplification: proof did not close"))
(qed 'rr-nvs-is-normed-vector-space)
(topic! 'rr-nvs-is-normed-vector-space 'algebra)
(alias! 'rr-nvs-is-normed-vector-space
        "the reals are a one-dimensional real normed vector space")
