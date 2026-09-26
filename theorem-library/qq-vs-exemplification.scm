;;; qq-vs-exemplification.scm -- THE FIRST WITNESS OF A VECTOR SPACE.
;;;
;;;     QQ-LINE = [ field-as-integral-domain(qq-field),   SCAL -- a 6-slot ring
;;;                 QQ,                                   VEC
;;;                 lambda([x,y] in QQxQQ, x + y),         VADD
;;;                 0,                                    VZERO
;;;                 lambda(x in QQ, -x),                   VNEG
;;;                 lambda([r,x] in QQxQQ, r * x) ]         ACT
;;;
;;; the rationals as a one-dimensional vector space over themselves.
;;;
;;; WHY QQ AND NOT RR.  `VECTOR-SPACE' is `same-shape-as MODULE' plus the single
;;; law `is-field-ring(scal(s))', so its scalar slot must be a SIX-slot ring that
;;; is a field.  `field-is-field-ring' (theorem-library/field-ring-view.scm)
;;; delivers exactly that -- for FIELD-AS-INTEGRAL-DOMAIN(s) given IS-FIELD(s) --
;;; and QQ-FIELD is the only FIELD instance in the tree.  RR reaches rings only
;;; through NORMED-FIELD-AS-COMMUTATIVE-RING, the ring view of a normed field,
;;; which no theorem yet shows to be a field-ring; that is why RR-NVS witnesses
;;; NORMED-VECTOR-SPACE but leaves VECTOR-SPACE unwitnessed.
;;;
;;; IS-VECTOR-SPACE unfolds to just TWO conjuncts -- `same-shape-as' keeps the
;;; parent predicate whole rather than re-expanding it:
;;;     is-module(qq-line)
;;;     is-field-ring(field-as-integral-domain(qq-field))
;;; The second is one citation.  The first is the work, and proving it witnesses
;;; MODULE directly -- seeded, not merely reachable through a view.
;;;
;;; The op-slot typings are PROVED by `lam-t' plus the carrier's closure axioms
;;; (qq-add-closed and siblings), never by a FUN-membership axiom about a shared
;;; constant: one object cannot be a set function with five domains, and
;;; asserting so proved NN = ZZ = QQ = RR = CC (numeric-instances.scm, repaired
;;; 2026-08-29).  The scalar law needs the accessors taken down TWICE -- once
;;; through the FIELD-AS-INTEGRAL-DOMAIN view (field-id-carr and siblings), then
;;; through QQ-FIELD's own slot equations.

(declare-instance! 'QQ-LINE 'VECTOR-SPACE 'qq-line-def
  '((FIELD-AS-INTEGRAL-DOMAIN QQ-FIELD) QQ
    (VNB-LAMBDA (LIST x_ y_) (CARTESIAN QQ QQ) (+ x_ y_)) 0
    (VNB-LAMBDA x_ QQ (- x_))
    (VNB-LAMBDA (LIST r_ x_) (CARTESIAN QQ QQ) (* r_ x_))))

(define (qv-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (qv-head) (let ((g (qv-goal))) (and (pair? g) (car g))))
(define (qv-peel!)
  (let lp ((n 12))
    (let ((before (qv-goal)))
      (when (and (> n 0) (memq (qv-head) '(FORALL IMPLIES)))
        (di) (if (not (equal? (qv-goal) before)) (lp (- n 1)))))))
(define (qv-beta!)
  (let lp ((n 12))
    (let ((before (qv-goal)))
      (quietly (lambda () (lam-b)))
      (when (and (> n 0) (not (equal? (qv-goal) before))) (lp (- n 1))))))

;;; An open LEAF right now: ungrounded, and no rule has fired on it.  Every loop
;;; below walks a SNAPSHOT of the leaf list, and `in-rr' ends with an `ass-all'
;;; that grounds every assumption-closable node anywhere in the graph -- so a
;;; later element of the snapshot can already be closed when the loop reaches
;;; it.  `dk-focus!' on such a node moves the focus and records NOTHING (it is
;;; not in proof-open-leaves, driver-kit.scm:164), and the closer's steps then
;;; go onto the page against whatever leaf the engine had chosen: the page-audit
;;; gate found this proof typing back in with its typing leaves open, diverging
;;; exactly at a `fact'/`in-rr' run on a leaf the previous `ass-all' had just
;;; closed (2026-09-15).  Skip what is no longer a leaf; nothing is lost, the
;;; work on a closed node was wasted anyway.
(define (qv-live-leaf? n)
  (and (not (sequent-node-grounded? n)) (null? (sequent-node-in-arrows n))))

;;; the real leaf set: ungrounded AND no rule fired.  `proof-leaves' misses a
;;; node a REWRITE fired on, so it can read 0 while the proof is not done.
(define (qv-open)
  (filter (lambda (n) (null? (sequent-node-in-arrows n))) (proof-open-goals *ps*)))

;;; op-slot typing: lam-t, then the carrier's closure axiom and sethood.
(define (qv-close-typing! g)
  (let* ((lam (cadr g)) (bind (cadr lam)) (body (cadddr lam))
         (thm (case (car body)
                ((+) 'qq-add-closed) ((*) 'qq-mul-closed) ((-) 'qq-neg-closed)
                (else (error "qq-vs: unknown slot body" body))))
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
      (let* ((g2 (qv-goal)) (t (cadr g2)) (args (cdr t)))
        (if (pair? (cdr args))
            (begin (dk-have! (list 'AND (list 'IN (car args) 'QQ)
                                        (list 'IN (cadr args) 'QQ)))
                   (fact thm (car args) (cadr args)))
            (fact thm (car args))))
      (ass))
    (when (pick 'IN)
      (fact 'qq-is-set)
      (when tup?
        (dk-have! '(AND (IN QQ SET) (IN QQ SET)))
        (mac 'cartesian-set-iff))
      (ass))))

(define (qv-close-leaf!)
  (let ((g (qv-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'IN)
            (pair? (caddr g)) (eq? (car (caddr g)) 'CARTESIAN))
       (ci)
       (for-each (lambda (n) (when (qv-live-leaf? n) (dk-focus! n) (qv-close-leaf!)))
                 (qv-open)))
      ((and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'QQ))
       (quietly (lambda () (fact 'qq-is-set) (fact 'qq-zero-in) (fact 'qq-one-in)))
       (in-rr))
      ((equal? g '(IN QQ SET)) (fact 'qq-is-set) (ass))
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (n) (dk-focus! n) (qv-close-leaf!))
                 (dk-opened (lambda () (di)))))
      ;; the scalars are a RING: the field view's typing axiom, then the ladder
      ((and (pair? g) (eq? (car g) 'IS-RING))
       (fact 'qq-field-is-field)
       (fact 'field-as-integral-domain-is-integral-domain 'QQ-FIELD)
       (fact 'integral-domain-is-commutative-ring '(FIELD-AS-INTEGRAL-DOMAIN QQ-FIELD))
       (fact 'commutative-ring-is-ring '(FIELD-AS-INTEGRAL-DOMAIN QQ-FIELD))
       (ass))
      (else (quietly (lambda () (crs)))))))

;;; ---- IS-MODULE(QQ-LINE) -------------------------------------------------
(sp (make-wff '(IS-MODULE QQ-LINE)))
(mac 'IS-MODULE)
(let loop ((n 0))
  (let ((any #f))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (and (pair? (qv-goal)) (eq? (car (qv-goal)) 'AND))
                    (begin (set! any #t) (vnb-guard (lambda () (di))))))
              (proof-leaves))
    (if (and any (< n 40)) (loop (+ n 1)))))
(for-each (lambda (l)
            (dk-focus! l)
            (vnb-guard (lambda () (surface-goal! 'QQ-LINE)))
            (for-each (lambda (m) (vnb-guard (lambda () (mac m))))
                      '(field-id-carr field-id-add field-id-mul
                        field-id-neg  field-id-one field-id-zero))
            (vnb-guard (lambda () (surface-goal! 'QQ-FIELD))))
          (proof-leaves))
(for-each
 (lambda (l)
  (when (qv-live-leaf? l)
   (dk-focus! l)
   (let ((g (qv-goal)))
     (cond
       ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
        (mac 'qq-line-def) (len-r) (arith))
       ((and (eq? (car g) 'IN) (number? (cadr g))) (arith))
       ((and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
        (qv-close-typing! g))
       ((memq (car g) '(is-associative is-commutative is-identity has-inverses))
        (mac (car g)) (qv-peel!) (qv-beta!) (qv-close-leaf!))
       (else (qv-peel!) (qv-beta!) (qv-close-leaf!))))))
 (proof-leaves))
(let sweep ((n 0))
  (let ((before (length (qv-open))))
    (for-each (lambda (l) (when (qv-live-leaf? l)
                            (dk-focus! l) (vnb-guard (lambda () (qv-close-leaf!)))))
              (qv-open))
    (if (and (< n 8) (< (length (qv-open)) before)) (sweep (+ n 1)))))
(if (not (proof-done? *ps*))
    (error "qq-vs-exemplification: IS-MODULE(QQ-LINE) did not close"))
(qed 'qq-line-is-module)
(topic! 'qq-line-is-module 'algebra)
(alias! 'qq-line-is-module "the rationals are a module over themselves")

;;; ---- IS-VECTOR-SPACE(QQ-LINE) -------------------------------------------
;;; `same-shape-as' keeps the parent predicate whole, so this is exactly
;;;     is-module(qq-line)  and  is-field-ring(scal(qq-line))
;;; -- the module above, and `field-is-field-ring' at the one FIELD instance the
;;; tree has.  That theorem (field-ring-view.scm) was proved for this.
(sp (make-wff '(IS-VECTOR-SPACE QQ-LINE)))
(mac 'IS-VECTOR-SPACE)
(vnb-guard (lambda () (surface-goal! 'QQ-LINE)))
(fact 'qq-line-is-module)
(fact 'qq-field-is-field)
(fact 'field-is-field-ring 'QQ-FIELD)
(for-each (lambda (n) (dk-focus! n) (vnb-guard (lambda () (ass))))
          (dk-opened (lambda () (di))))
(if (not (proof-done? *ps*))
    (error "qq-vs-exemplification: IS-VECTOR-SPACE(QQ-LINE) did not close"))
(qed 'qq-line-is-vector-space)
(topic! 'qq-line-is-vector-space 'algebra)
(alias! 'qq-line-is-vector-space
        "the rationals are a one-dimensional vector space over themselves")
