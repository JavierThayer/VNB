;;; rabasics-open.scm -- calculus.pdf 3.3, complex-analysis.pdf 1.5: the intersection of FINITELY
;;; many open sets is open (the union half is union-of-opens-open, already proven).
;;;
;;;   intersection-of-insert        t inhabited, x0 a set:
;;;                                   INTERSECTION-OF(t u {x0}) = INTERSECTION-OF(t) n x0
;;;   intersection-of-insert-empty  t with no member, x0 a set:  INTERSECTION-OF(t u {x0}) = x0
;;;   inter-of-finite-opens-open    in a metric space, a non-empty FINITE family c (c a set,
;;;                                 CARD(c) in NN) of open sets has an open intersection
;;;                                 INTERSECTION-OF(c).
;;;
;;; The notes' "finitely many" is a non-empty finite family (the empty intersection is not open-set
;;; vocabulary: INTERSECTION-OF of the empty family is EMPTY-SET, intersection-of-empty-family).
;;; The proof is finite-set-induction (class form) on the property
;;;     P(t) := t inhabited => every member of t open => INTERSECTION-OF(t) open,
;;; the step adding one set x: if t is inhabited, the two set equations above reduce to
;;; inter-of-opens-open; if t is empty, INTERSECTION-OF(t u {x}) = x.
;;;
;;; Library: analysis (IS-OPEN).  The two set equations are core vocabulary (INTERSECTION-OF,
;;; UNION, PAIR) and may move to a core file.  Load window: after theorem-library/rake-open-sets
;;; (inter-of-opens-open), theorem-library/intersection-of-laws (intersection-of-is-set,
;;; intersection-of-membership) and theorem-library/rake-card-star-laws (finite-set-induction);
;;; no citer yet.  Helper prefix: rbx-.

(define (rbx-find what pred)
  (let ((l (filter pred (dk-asms))))
    (if (null? l) (error "rbx-find: nothing matching" what) (car l))))

;;; (IN x0 (UNION tf (PAIR x0 x0))), with (IN x0 SET) in context.
(define (rbx-in-pair! x0 p)
  (dk-have! (list 'IN x0 p)
    (lambda ()
      (dk-have! (list 'AND (list 'IN x0 'SET) (list 'IN x0 'SET)))
      (let ((pm (dk-fact! 'pairing-membership x0 x0 x0)))
        (dk-have! (list '= x0 x0) (lambda () (rfl)))
        (dk-only! pm (list '= x0 x0))
        (prop)))))
(define (rbx-in-union-right! x0 u)
  (rbx-in-pair! x0 (caddr u))
  (dk-have! (list 'IN x0 u)
    (lambda () (mac 'union-membership) (oi-r) (ass))))
;;; with (IN v (PAIR x0 x0)) in context, land (= v x0)
(define (rbx-pair-eq! v x0)
  (let ((p (list 'PAIR x0 x0)))
    (dk-have! (list 'AND (list 'IN x0 'SET) (list 'IN x0 'SET)))
    (let ((pm (dk-fact! 'pairing-membership x0 x0 v)))
      (dk-have! (list '= v x0)
        (lambda () (dk-only! pm (list 'IN v p)) (prop))))))

;;; the universal (FORALL i (IMPLIES (IN i SET) (IN z i))) landed by opening (IN z (INTERSECTION-OF SET))
(define (rbx-all-of set)
  (rbx-find 'intersection-universal
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (let ((b (caddr a)))
                       (and (pair? b) (eq? (car b) 'IMPLIES)
                            (equal? (caddr (cadr b)) set)))))))

;;; open (IN z (INTERSECTION-OF set)) in context: land its two conjuncts
(define (rbx-open-io! z set)
  (let ((h (list 'IN z (list 'INTERSECTION-OF set))))
    (mac-h 'intersection-of-membership h)
    (dk-split-all!)))

;;; z in INTERSECTION-OF(U) => z in INTERSECTION(It, x0)   [U = tv u {x0}, u1 in tv]
(define (rbx-ins-fwd! z U tv xv It B u1)
  (rbx-open-io! z U)
  (let ((hu (rbx-all-of U)))
    (mac 'intersection-membership)
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (equal? (dk-goal) (list 'IN z xv))
           (begin (inst+ hu xv) (ass))
           (begin
             (mac 'intersection-of-membership)
             (for-each (lambda (lf) (dk-focus! lf) (rbx-ins-fwd-leaf! z U hu u1))
                       (dk-opened (lambda () (di)))))))
     (dk-opened (lambda () (di))))))
(define (rbx-ins-fwd-leaf! z U hu u1)
  (if (eq? (car (dk-goal)) 'FORSOME)
      (begin (ew u1) (ass))
      (let* ((pl (dk-peel!))
             (iv (caddr (dk-goal))))
        (dk-have! (list 'IN iv U)
          (lambda () (mac 'union-membership) (oi-l) (ass)))
        (inst+ hu iv)
        (ass))))

;;; goal (IN z (INTERSECTION-OF U)), with the members of tv containing z given by HT-CASE:
;;; a thunk run on the branch (IN iv tv) that closes (IN z iv).
(define (rbx-into-io! z U tv xv tv-case!)
  (mac 'intersection-of-membership)
  (for-each
   (lambda (lf)
     (dk-focus! lf)
     (if (eq? (car (dk-goal)) 'FORSOME)
         (begin (ew xv) (ass))
         (let* ((pl (dk-peel!))
                (iv (caddr (dk-goal))))
           (mac-h 'union-membership (list 'IN iv U))
           (use-cases (list (list 'IN iv tv) (list 'IN iv (caddr U)))
             (lambda () (tv-case! iv))
             (lambda ()
               (rbx-pair-eq! iv xv)
               (subst (list '= iv xv))
               (ass))))))
   (dk-opened (lambda () (di)))))

;;; ---------------------------------------------------------------------------
(sp (make-wff
  '(FORALL tf (FORALL x0 (IMPLIES (IN x0 SET) (IMPLIES (FORSOME w (IN w tf))
     (= (INTERSECTION-OF (UNION tf (PAIR x0 x0))) (INTERSECTION (INTERSECTION-OF tf) x0))))))))
(define rbx1-landed (dk-peel!))
(define rbx1-A  (cadr (dk-goal)))
(define rbx1-B  (caddr (dk-goal)))
(define rbx1-U  (cadr rbx1-A))
(define rbx1-tv (cadr rbx1-U))
(define rbx1-xv (cadr (caddr rbx1-U)))
(define rbx1-It (cadr rbx1-B))
(define rbx1-u1 (dk-skolem! (car (filter (lambda (a) (eq? (car a) 'FORSOME)) rbx1-landed))))
(fact 'intersection-of-is-set rbx1-U)
(fact 'intersection-of-is-set rbx1-tv)
(dk-have! (list 'OR (list 'IN rbx1-It 'SET) (list 'IN rbx1-xv 'SET)) (lambda () (oi-r) (ass)))
(fact 'intersection-set-closure rbx1-It rbx1-xv)
(dk-have! (list 'AND (list 'IN rbx1-A 'SET) (list 'IN rbx1-B 'SET)))
(rbx-in-union-right! rbx1-xv rbx1-U)
(define rbx1-ext (dk-fact! 'extensionality rbx1-A rbx1-B))
(define rbx1-claim (caddr rbx1-ext))
(dk-have! rbx1-claim
  (lambda ()
    (di)
    (let ((z (cadr (cadr (dk-goal)))))
      (dk-iff! (lambda (g) (equal? g (list 'IN z rbx1-B)))
        (lambda () (rbx-ins-fwd! z rbx1-U rbx1-tv rbx1-xv rbx1-It rbx1-B rbx1-u1))
        (lambda ()
          (mac-h 'intersection-membership (list 'IN z rbx1-B))
          (dk-split-all!)
          (rbx-open-io! z rbx1-tv)
          (let ((ht (rbx-all-of rbx1-tv)))
            (rbx-into-io! z rbx1-U rbx1-tv rbx1-xv
              (lambda (iv) (inst+ ht iv) (ass)))))))))
(dk-only! rbx1-ext rbx1-claim)
(prop)
(qed 'intersection-of-insert)

;;; ---------------------------------------------------------------------------
(sp (make-wff
  '(FORALL tf (FORALL x0 (IMPLIES (IN x0 SET) (IMPLIES (NOT (FORSOME w (IN w tf)))
     (= (INTERSECTION-OF (UNION tf (PAIR x0 x0))) x0)))))))
(define rbx2-landed (dk-peel!))
(define rbx2-A  (cadr (dk-goal)))
(define rbx2-U  (cadr rbx2-A))
(define rbx2-tv (cadr rbx2-U))
(define rbx2-xv (cadr (caddr rbx2-U)))
(define rbx2-nf (car (filter (lambda (a) (eq? (car a) 'NOT)) rbx2-landed)))
(fact 'intersection-of-is-set rbx2-U)
(dk-have! (list 'AND (list 'IN rbx2-A 'SET) (list 'IN rbx2-xv 'SET)))
(rbx-in-union-right! rbx2-xv rbx2-U)
(define rbx2-ext (dk-fact! 'extensionality rbx2-A rbx2-xv))
(define rbx2-claim (caddr rbx2-ext))
(dk-have! rbx2-claim
  (lambda ()
    (di)
    (let ((z (cadr (cadr (dk-goal)))))
      (dk-iff! (lambda (g) (equal? g (list 'IN z rbx2-xv)))
        (lambda ()
          (rbx-open-io! z rbx2-U)
          (inst+ (rbx-all-of rbx2-U) rbx2-xv)
          (ass))
        (lambda ()
          (rbx-into-io! z rbx2-U rbx2-tv rbx2-xv
            (lambda (iv)
              (dk-have! (cadr rbx2-nf) (lambda () (ew iv) (ass)))
              (dk-only! rbx2-nf (cadr rbx2-nf))
              (prop))))))))
(dk-only! rbx2-ext rbx2-claim)
(prop)
(qed 'intersection-of-insert-empty)

;;; ---------------------------------------------------------------------------
;;; inter-of-finite-opens-open, by finite-set-induction on P(t) (the induction pattern of
;;; integral-convergence.scm's icv-induct!).
(define (rbx-prop-of s v)
  (list 'IMPLIES (list 'FORSOME 'w (list 'IN 'w v))
        (list 'IMPLIES (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u v) (list 'IS-OPEN s 'u)))
              (list 'IS-OPEN s (list 'INTERSECTION-OF v)))))

;;; the step: P(sv) given as IH, show P(union(sv, pair(xv, xv))) on the focus goal
(define (rbx-step! s sv xv uu ih)
  (let* ((pl (dk-peel!))
         (hu (car (filter (lambda (a) (eq? (car a) 'FORALL)) pl))))
    (rbx-in-union-right! xv uu)
    (inst+ hu xv)                                          ; (IS-OPEN s xv)
    (use-em (cadr ih)
      (lambda ()
        (let ((ht (cadr (caddr ih))))
          (dk-have! ht
            (lambda ()
              (let* ((pl2 (dk-peel!))
                     (iv  (cadr (car (filter (lambda (a) (eq? (car a) 'IN)) pl2)))))
                (dk-have! (list 'IN iv uu)
                  (lambda () (mac 'union-membership) (oi-l) (ass)))
                (inst+ hu iv)
                (ass))))
          (detach! ih)
          (detach! (caddr ih))
          (let ((it (list 'INTERSECTION-OF sv)))
            (dk-have! (list 'AND (list 'IS-OPEN s it) (list 'IS-OPEN s xv)))
            (fact 'inter-of-opens-open s it xv)
            (fact 'intersection-of-insert sv xv)
            (subst (list '= (list 'INTERSECTION-OF uu) (list 'INTERSECTION it xv)))
            (ass))))
      (lambda ()
        (fact 'intersection-of-insert-empty sv xv)
        (subst (list '= (list 'INTERSECTION-OF uu) xv))
        (ass)))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL c (IMPLIES (IN c SET) (IMPLIES (IN (CARD c) NN)
       (IMPLIES (FORSOME w (IN w c))
         (IMPLIES (FORALL u (IMPLIES (IN u c) (IS-OPEN s u)))
           (IS-OPEN s (INTERSECTION-OF c)))))))))))
(define rbx3-landed (dk-peel!))
(define rbx3-s  (cadr (car (filter (lambda (a) (eq? (car a) 'IS-METRIC-SPACE)) rbx3-landed))))
(define rbx3-c  (cadr (caddr (dk-goal))))
(define rbx3-cls  (list 'COMP 'iu_ (rbx-prop-of rbx3-s 'iu_)))
(define rbx3-stepf
  (list 'FORALL 'is_
    (list 'IMPLIES (list 'AND '(IN is_ SET) (list 'AND '(IN (CARD is_) NN) (list 'IN 'is_ rbx3-cls)))
      (list 'FORALL 'ix_
        (list 'IMPLIES '(AND (IN ix_ SET) (NOT (IN ix_ is_)))
          (list 'IN '(UNION is_ (PAIR ix_ ix_)) rbx3-cls))))))
;; base: P(EMPTY-SET) holds vacuously
(dk-have! (list 'IN 'EMPTY-SET rbx3-cls)
  (lambda ()
    (for-each
      (lambda (leaf)
        (dk-focus! leaf)
        (if (equal? (dk-goal) '(IN EMPTY-SET SET))
            (begin (fact 'empty-set-is-set) (ass))
            (let* ((pl (dk-peel!))
                   (w0 (dk-skolem! (car (filter (lambda (a) (eq? (car a) 'FORSOME)) pl))))
                   (no (dk-fact! 'empty-set-has-no-members w0)))
              (dk-only! no (list 'IN w0 'EMPTY-SET))
              (prop))))
      (dk-opened (lambda () (comp-mi))))))
;; step
(dk-have! rbx3-stepf
  (lambda ()
    (let* ((landed (dk-peel!))
           (g      (dk-goal))
           (uu     (cadr g))
           (sv     (cadr uu))
           (xv     (cadr (caddr uu))))
      (dk-split-all! landed)
      (dk-have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
      (fact 'pairing xv xv)
      (dk-have! (list 'AND (list 'IN sv 'SET) (list 'IN (list 'PAIR xv xv) 'SET)))
      (fact 'union-set-closure sv (list 'PAIR xv xv))
      (let* ((ls (dk-landed (lambda () (comp-me (list 'IN sv rbx3-cls)))))
             (ih (car (filter (lambda (f) (eq? (car f) 'IMPLIES)) ls))))
        (for-each
          (lambda (leaf)
            (dk-focus! leaf)
            (if (equal? (dk-goal) (list 'IN uu 'SET))
                (ass)
                (rbx-step! rbx3-s sv xv uu ih)))
          (dk-opened (lambda () (comp-mi))))))))
(dk-have! (list 'AND (list 'IN 'EMPTY-SET rbx3-cls) rbx3-stepf))
(define rbx3-ind (dk-fact! 'finite-set-induction rbx3-cls))
(dk-have! (list 'AND (list 'IN rbx3-c 'SET) (list 'IN (list 'CARD rbx3-c) 'NN)))
(define rbx3-inc (dk-apply! rbx3-ind rbx3-c))
(define rbx3-pc
  (car (filter (lambda (f) (eq? (car f) 'IMPLIES))
               (dk-landed (lambda () (comp-me rbx3-inc))))))
(detach! rbx3-pc)
(detach! (caddr rbx3-pc))
(ass)
(qed 'inter-of-finite-opens-open)

(display ";; RBX qed failures: ") (display *vnb-qed-failures*) (newline)
;; (probe trailer removed at integration 2026-10-27) (page-audit!)
;; (probe trailer removed at integration 2026-10-27) (report-page-audit)
