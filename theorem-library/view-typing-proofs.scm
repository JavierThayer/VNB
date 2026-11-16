;;; theorem-library/view-typing-proofs.scm -- THE DEFERRED FIELD VIEW TYPINGS, PROVEN
;;; (D8, 2026-11-15; the user's decision "Prove views + fix F1/F2").
;;;
;;; Three views of structure-library/views.scm post a DEFERRED typing obligation
;;; (def-functor ... 'deferred): the generic read-off driver (dk-view-typing!,
;;; driver-kit.scm) closes every conjunct of the target but one, and that one is a
;;; theorem with content.  Each is proven here; until 2026-11-15 each was a
;;; `definitional' typing AXIOM, unproven, and the third was FALSE.
;;;
;;;   normed-field-as-integral-domain-is-integral-domain
;;;       a normed field has no zero divisors: its ring view is a field-ring
;;;       (normed-field-is-field-ring, below), and field-ring-is-integral-domain;
;;;   field-as-euclidean-ring-is-euclidean-ring
;;;       the Euclidean law with the trivial degree deg = 0: a = (a * b^-1) * b + 0;
;;;   field-multiplicative-group-is-group
;;;       DEFSTAMP F1.  The group's operation was MUL(r) itself, typed by the axiom
;;;       on NON-ZERO x NON-ZERO; a member of FUN(A, B) is defined EXACTLY on A and
;;;       IS-FIELD types MUL(r) on CARR x CARR, so the axiom made 0 a non-zero
;;;       element and 0 = 1 followed modulo 0.  The view's operation is now the
;;;       RESTRICTION of MUL(r) to NON-ZERO(r) x NON-ZERO(r) (views.scm), and the
;;;       group laws are proven: NON-ZERO(r) is closed under MUL because a field has
;;;       no zero divisors (the typing of FIELD-AS-INTEGRAL-DOMAIN, field-ring-view.scm),
;;;       and the restricted product reduces by beta to MUL(r) on typed arguments.
;;;
;;; Each proof is followed by view-typing-installed!, which hands the new theorem to
;;; the views declared after its own (structures.scm).
;;;
;;; Window: after field-ring-view (field-ring-is-integral-domain, the typing of
;;; FIELD-AS-INTEGRAL-DOMAIN), view-typing-laws (the typing of
;;; NORMED-FIELD-AS-COMMUTATIVE-RING), singleton-membership, difference-laws.

;;; ---- file-local helpers (prefix vtp-), r the field ----------------------
(define vtp-nzd '(DIFFERENCE (CARR r) (SINGLETON (ZERO r))))
;; x in carr(r), not(x = zero(r)) in context  ==>  x in non-zero(r)
(define (vtp-nz! x)
  (dk-have! (list 'NOT (list 'IN x (list 'SINGLETON '(ZERO r))))
    (lambda () (fact 'singleton-membership '(ZERO r) x) (prop)))
  (dk-have! (list 'IN x vtp-nzd)
    (lambda () (fact 'difference-membership '(CARR r) (list 'SINGLETON '(ZERO r)) x) (prop)))
  (dk-have! (list 'IN x '(NON-ZERO r))
    (lambda () (subst (list '= '(NON-ZERO r) vtp-nzd)) (ass))))
;; x in non-zero(r)  ==>  x in carr(r)
(define (vtp-carr! x)
  (if (not (dk-asm? (list 'IN x '(CARR r))))
      (dk-have! (list 'IN x '(CARR r))
        (lambda ()
          (dk-have! (list 'IN x vtp-nzd) (lambda () (subst (list '= vtp-nzd '(NON-ZERO r))) (ass)))
          (fact 'difference-membership '(CARR r) (list 'SINGLETON '(ZERO r)) x)
          (prop)))))
;; x in non-zero(r)  ==>  not(x = zero(r))
(define (vtp-nonzero! x)
  (let ((ne (list 'NOT (list '= x '(ZERO r)))))
    (if (not (dk-asm? ne))
        (dk-have! ne
          (lambda ()
            (dk-have! (list 'IN x vtp-nzd) (lambda () (subst (list '= vtp-nzd '(NON-ZERO r))) (ass)))
            (let* ((dm (dk-cite! 'difference-membership '(CARR r) (list 'SINGLETON '(ZERO r)) x))
                   (nsing (list 'NOT (list 'IN x (list 'SINGLETON '(ZERO r))))))
              (dk-have! nsing (lambda () (dk-only! dm (list 'IN x vtp-nzd)) (prop)))
              (if (not (dk-asm? (list 'IN x '(CARR r))))
                  (dk-have! (list 'IN x '(CARR r)) (lambda () (dk-only! dm (list 'IN x vtp-nzd)) (prop))))
              (dk-cite! 'membership-implies-sethood x '(CARR r))
              (let ((sm (dk-cite! 'singleton-membership '(ZERO r) x)))
                (dk-only! sm nsing (list 'IN x 'SET))
                (prop))))))))
;; (IN ((op r) a b) (CARR r)) for a binary operation slot typed on CARR x CARR
(define (vtp-bin-type! op a b)
  (dk-have! (list 'IN (list (list op 'r) a b) '(CARR r))
    (lambda ()
      (fact 'apply-tupling-2 (list op 'r) a b)
      (subst (list '== (list (list op 'r) a b) (list (list op 'r) (list 'LIST a b))))
      (fact 'pair-in-cartesian '(CARR r) '(CARR r) a b)
      (fact 'fun-apply-type-c (list op 'r) '(CARTESIAN (CARR r) (CARR r)) '(CARR r) (list 'LIST a b))
      (ass))))
(define (vtp-left-check! who left)
  (if (not (null? left))
      (error (string-append "view-typing-proofs: " who ": the generic driver left more than expected")
             (map (lambda (l) (expression->string (dk-goal-of l))) left))))

;;; =====================================================================
;;; (1) A NORMED FIELD's ring view is a field-ring; its integral-domain view is
;;;     an integral domain.
;;; =====================================================================
(sp (make-wff '(FORALL f (IMPLIES (IS-NORMED-FIELD f) (IS-FIELD-RING (NORMED-FIELD-AS-COMMUTATIVE-RING f))))))
(dk-peel!)
(let ((left (dk-view-close! 'NORMED-FIELD-AS-COMMUTATIVE-RING 'FIELD-RING)))
  (if (not (= (length left) 1)) (vtp-left-check! "normed-field-is-field-ring" left))
  (dk-focus! (car left)))
;; the one leaf: forsome b in carr(f). mul(f)(a, b) = one(f), for the eigenvariable a /= 0;
;; the normed field's law gives such a b (with b /= 0 besides)
(let* ((a   (cadr (cadr (caddr (caddr (dk-goal))))))
       (inv (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'FORSOME) (dk-contains? h '(ONE f))))
                     "the normed field's inverse law"))
       (b   (dk-skolem! (dk-apply! inv a))))
  (dk-split-all!)
  (ew b)
  (from-context!))
(qed 'normed-field-is-field-ring)
(topic! 'normed-field-is-field-ring 'algebra)

(sp (make-wff '(FORALL r (IMPLIES (IS-NORMED-FIELD r) (IS-INTEGRAL-DOMAIN (NORMED-FIELD-AS-INTEGRAL-DOMAIN r))))))
(dk-peel!)
(fact 'normed-field-is-field-ring 'r)
(fact 'field-ring-is-integral-domain '(NORMED-FIELD-AS-COMMUTATIVE-RING r))
(vtp-left-check! "normed-field-as-integral-domain" (dk-view-close! 'NORMED-FIELD-AS-INTEGRAL-DOMAIN))
(qed 'normed-field-as-integral-domain-is-integral-domain)
(view-typing-installed! 'NORMED-FIELD-AS-INTEGRAL-DOMAIN)

;;; =====================================================================
;;; (2) A FIELD is a Euclidean ring, with the degree identically 0.
;;; =====================================================================
(sp (make-wff '(FORALL r (IMPLIES (IS-FIELD r) (IS-EUCLIDEAN-RING (FIELD-AS-EUCLIDEAN-RING r))))))
(dk-peel!)
(fact 'field-as-integral-domain-is-integral-domain 'r)
(let ((left (dk-view-close! 'FIELD-AS-EUCLIDEAN-RING)))
  (if (not (= (length left) 1)) (vtp-left-check! "field-as-euclidean-ring" left))
  (dk-focus! (car left)))
;; forsome dg in fun(carr(r), nn). forall a, b in carr(r). b /= 0 =>
;;   forsome q, r_ in carr(r). a = q*b + r_ and (r_ = 0 or succ(dg(r_)) <= dg(b))
(ew '(VNB-LAMBDA egx_ (CARR r) 0))
(let ((ls (dk-opened (lambda () (di)))))
  (dk-focus! (car ls))
  (dk-lam-type! (lambda () (dk-peel!) (arith)))
  (dk-focus! (cadr ls)))
(dk-peel!)
(let* ((ib (list '(MUL-INV r) 'b))
       (q  (list '(MUL r) 'a ib))
       (fd '(FIELD-AS-INTEGRAL-DOMAIN r)))
  (vtp-nz! 'b)
  (fact 'fun-apply-type-c '(MUL-INV r) '(NON-ZERO r) '(NON-ZERO r) 'b)
  (vtp-carr! ib)
  (vtp-bin-type! 'MUL 'a ib)
  (ew q)
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (car ls)) (ass)
    (dk-focus! (cadr ls)))
  (ew '(ZERO r))
  (let ((ls (dk-vt--goal-leaves!)))
    ;; zero(r) in carr(r)
    (dk-focus! (car ls)) (ass)
    ;; zero(r) = zero(r) or ...
    (dk-focus! (caddr ls))
    (dk-have! '(= (ZERO r) (ZERO r)) (lambda () (rfl)))
    (prop)
    ;; a = add(mul(mul(a, b^-1), b), zero): a commutative-ring identity at the integral-
    ;; domain view, carried to r's own spelling by the view read-off, then b * b^-1 = 1, a * 1 = a
    (dk-focus! (cadr ls))
    (fact 'integral-domain-is-commutative-ring fd)
    (for-each (lambda (x) (dk-have! (list 'IN x (list 'CARR fd)) (lambda () (dk-vt--match!)))) (list 'a 'b ib))
    (dk-have! (list '= (list (list 'ADD fd) (list (list 'MUL fd) (list (list 'MUL fd) 'a ib) 'b) (list 'ZERO fd))
                       (list (list 'MUL fd) 'a (list (list 'MUL fd) 'b ib)))
              (lambda () (crs)))
    (let ((er (list '= (list '(ADD r) (list '(MUL r) q 'b) '(ZERO r)) (list '(MUL r) 'a (list '(MUL r) 'b ib)))))
      (dk-have! er (lambda () (dk-vt--match!)))
      (subst er))
    (subst (dk-apply! (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h '(MUL-INV r))
                                                (dk-contains? h '(NON-ZERO r)) (dk-contains? h '(ONE r))))
                               "the field's inverse law")
                      'b))
    (dk-split! (dk-apply! (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h '(ONE r)) (dk-contains? h 'AND)
                                                    (dk-contains? h '(MUL r)) (not (dk-contains? h 'MUL-INV))))
                                   "the multiplicative identity law")
                          'a))
    (subst (list '= (list '(MUL r) 'a '(ONE r)) 'a))
    (rfl)))
(qed 'field-as-euclidean-ring-is-euclidean-ring)
(view-typing-installed! 'FIELD-AS-EUCLIDEAN-RING)

;;; =====================================================================
;;; (3) THE MULTIPLICATIVE GROUP OF A FIELD (F1).
;;; =====================================================================
(define vtp-op '(VNB-LAMBDA (LIST fmgu_ fmgv_) (CARTESIAN (NON-ZERO r) (NON-ZERO r)) ((MUL r) fmgu_ fmgv_)))
(define vtp-zd
  '(FORALL a (IMPLIES (IN a (CARR r)) (FORALL b (IMPLIES (IN b (CARR r))
     (IMPLIES (= ((MUL r) a b) (ZERO r)) (OR (= a (ZERO r)) (= b (ZERO r)))))))))
;; the absence of zero divisors in r's own spelling, read off IS-INTEGRAL-DOMAIN(FIELD-AS-INTEGRAL-DOMAIN r)
;; (D8b) read off on a LANE, so that only the law reaches the branch, and once, on the
;; main branch before the goal is split, so that every branch inherits it: the first
;; version expanded IS-INTEGRAL-DOMAIN on every branch that needed the law (V1).
(define (vtp-zd!)
  (if (not (dk-asm? vtp-zd))
      (dk-have! vtp-zd
        (lambda ()
          (fact 'field-as-integral-domain-is-integral-domain 'r)
          (dk-vt--expand! 'INTEGRAL-DOMAIN '(FIELD-AS-INTEGRAL-DOMAIN r) 0)
          (if (not (dk-vt--match!)) (error "view-typing-proofs: no zero divisors: no read-off"))))))
;; x, y in non-zero(r)  ==>  mul(r)(x, y) in non-zero(r)
(define (vtp-closure! x y)
  (let ((m (list '(MUL r) x y)))
    (if (not (dk-asm? (list 'IN m '(NON-ZERO r))))
        (begin
          (vtp-zd!)
          (vtp-carr! x) (vtp-carr! y)
          (vtp-nonzero! x) (vtp-nonzero! y)
          (if (not (dk-asm? (list 'IN m '(CARR r)))) (vtp-bin-type! 'MUL x y))
          (dk-have! (list 'NOT (list '= m '(ZERO r)))
            (lambda ()
              (di)
              (let ((o (dk-apply! vtp-zd x y)))
                (dk-only! o (list 'NOT (list '= x '(ZERO r))) (list 'NOT (list '= y '(ZERO r))))
                (prop))))
          (vtp-nz! m)))))
;;; THE CLOSURE OF NON-ZERO(r) UNDER MUL(r), a lemma of its own (D8b, finding V1).
;;; Every posted sequent is compared with every node of the proof's graph
;;; (deduction-graphs.scm, dg-find-sequent-node: a linear scan, by design), so a
;;; proof's cost grows with the SQUARE of its size.  The first version re-derived the
;;; closure on every branch that needed it -- some twenty lanes each time -- and the
;;; group typing posted 2,400 sequents (in a load: 400 s, against 8 s for the probe of
;;; an earlier, smaller version).  Proven once here, it is one citation on each branch.
(sp (make-wff '(FORALL r (IMPLIES (IS-FIELD r)
                 (FORALL fnzu_ (IMPLIES (IN fnzu_ (NON-ZERO r))
                   (FORALL fnzv_ (IMPLIES (IN fnzv_ (NON-ZERO r)) (IN ((MUL r) fnzu_ fnzv_) (NON-ZERO r))))))))))
(dk-peel!)
(dk-vt--expand! 'FIELD 'r 0)          ; NON-ZERO(r)'s definition and MUL(r)'s typing
(let ((lane (proof-state-focus *ps*)) (m (cadr (dk-goal))))
  (vtp-closure! (cadr m) (caddr m))
  (if (not (sequent-node-grounded? lane)) (ass)))
(qed 'field-non-zero-mul-closed)
(topic! 'field-non-zero-mul-closed 'algebra)
;; the closure by citation: x, y in non-zero(r) in context
(define (vtp-closed! x y)
  (if (not (dk-asm? (list 'IN (list '(MUL r) x y) '(NON-ZERO r))))
      (dk-cite! 'field-non-zero-mul-closed 'r x y)))
(define (vtp-op-app? e) (and (pair? e) (= (length e) 3) (equal? (car e) vtp-op)))
;; type the restricted product's applications in E bottom-up, left to right; E reduced
(define (vtp-prep! e)
  (cond ((vtp-op-app? e)
         (let* ((a (vtp-prep! (cadr e))) (b (vtp-prep! (caddr e))))
           (if (and (pair? a) (equal? (car a) '(MUL r))) (vtp-closed! (cadr a) (caddr a)))
           (if (and (pair? b) (equal? (car b) '(MUL r))) (vtp-closed! (cadr b) (caddr b)))
           (list '(MUL r) a b)))
        ((pair? e) (let loop ((xs e) (acc '()))
                     (if (null? xs) (reverse acc) (loop (cdr xs) (cons (vtp-prep! (car xs)) acc)))))
        (#t e)))
(define (vtp-find pat vars what)
  (or (any-pred (lambda (h) (and (dk-head-is? h 'FORALL)
                                 (dk-vt--pmatch pat (cdr (dk-vt--univ-parts h)) vars '())))
                (dk-asms))
      (error "view-typing-proofs: no hypothesis for" what)))
(define (vtp-one-nz!)
  (if (not (dk-asm? '(IN (ONE r) (NON-ZERO r))))
      (begin
        (if (not (dk-asm? '(NOT (= (ONE r) (ZERO r))))) (fact 'neq-sym '(ZERO r) '(ONE r)))
        (vtp-nz! '(ONE r)))))
;; an equation of the group laws, its products reduced: assoc, identity, inverse
(define (vtp-close-eq!)
  (let ((g (dk-goal)))
    (for-each (lambda (h) (if (and (dk-head-is? h 'IN) (equal? (caddr h) '(NON-ZERO r)) (dk-contains? g (cadr h)))
                              (vtp-carr! (cadr h))))
              (dk-asms))
    (cond
      ((dk-contains? g '(MUL-INV r))
       (let* ((iu (let find ((e g)) (cond ((and (pair? e) (equal? (car e) '(MUL-INV r))) e)
                                          ((pair? e) (or (find (car e)) (find (cdr e))))
                                          (#t #f))))
              (x  (cadr iu)))
         (if (equal? (cadr (cadr g)) iu)
             (subst (dk-apply! (vtp-find '(= ((MUL r) x1 x2) ((MUL r) x2 x1)) '(x1 x2) "commutativity") iu x)))
         (dk-apply! (vtp-find '(= ((MUL r) x1 ((MUL-INV r) x1)) (ONE r)) '(x1) "the inverse law") x)
         (ass)))
      ((dk-contains? g '(ONE r))
       (let ((x (if (equal? (cadr (cadr g)) '(ONE r)) (caddr (cadr g)) (cadr (cadr g)))))
         (dk-split! (dk-apply! (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h '(ONE r)) (dk-contains? h 'AND)
                                                         (not (dk-contains? h 'MUL-INV)) (dk-contains? h '(MUL r))))
                                        "the identity law")
                               x))
         (ass)))
      (#t
       (let ((m1 (cadr g)))
         (dk-apply! (vtp-find '(= ((MUL r) ((MUL r) x1 x2) x3) ((MUL r) x1 ((MUL r) x2 x3))) '(x1 x2 x3) "associativity")
                    (cadr (cadr m1)) (caddr (cadr m1)) (caddr m1))
         (ass))))))
(sp (make-wff '(FORALL r (IMPLIES (IS-FIELD r) (IS-GROUP (FIELD-MULTIPLICATIVE-GROUP r))))))
(dk-peel!)
(for-each
  (lambda (l)
    (if (not (sequent-node-grounded? l))
        (begin
          (dk-focus! l)
          (let ((g (dk-goal)))
            (cond
              ;; the restricted product lands in NON-ZERO(r)
              ((and (dk-head-is? g 'IN) (equal? (cadr g) vtp-op))
               ;; (D8b) the citation may close this lane's goal outright: the closing `ass'
               ;; only when the lane is still open (a drift otherwise)
               (dk-lam-type! (lambda ()
                               (dk-peel!)
                               (let ((lane (proof-state-focus *ps*)) (m (cadr (dk-goal))))
                                 (vtp-closed! (cadr m) (caddr m))
                                 (if (not (sequent-node-grounded? lane)) (ass))))))
              ;; one(r) is not zero(r)
              ;; (vtp-nz!'s last claim is the focus goal: dk-have! proves it in place)
              ((equal? g '(IN (ONE r) (NON-ZERO r)))
               (vtp-one-nz!)
               (if (not (sequent-node-grounded? l))
                   (error "view-typing-proofs: one(r) in non-zero(r) is still open")))
              ;; a law: type the products, reduce them, close by the field's law
              (#t
               (for-each (lambda (h) (if (and (dk-head-is? h 'IN) (equal? (caddr h) '(NON-ZERO r)) (symbol? (cadr h))
                                              (dk-contains? g (list '(MUL-INV r) (cadr h))))
                                         (fact 'fun-apply-type-c '(MUL-INV r) '(NON-ZERO r) '(NON-ZERO r) (cadr h))))
                         (dk-asms))
               (if (dk-contains? g '(ONE r)) (vtp-one-nz!))
               (vtp-prep! g)
               (dk-lam-b!)
               (vtp-close-eq!)))))))
  (dk-view-close! 'FIELD-MULTIPLICATIVE-GROUP))
(qed 'field-multiplicative-group-is-group)
(view-typing-installed! 'FIELD-MULTIPLICATIVE-GROUP)
