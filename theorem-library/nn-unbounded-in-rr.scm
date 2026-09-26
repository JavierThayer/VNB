;;; nn-unbounded-in-rr.scm -- the ARCHIMEDEAN PROPERTY, PROVEN.
;;;
;;;   forall x in RR.  forsome n_ in NN.  x < n_
;;;
;;; "No real number is an upper bound for the naturals."  Statement byte-for-
;;; byte the support of the same name in structure-library/order-predicates.scm
;;; (line 126), whose `informal' warrant IS this proof, written in prose.
;;;
;;; THE PROOF.  Classical, through order completeness.  Excluded middle on the
;;; conclusion.  If no natural exceeds x, then every natural is <= x
;;; (rr-lt-trichotomy: the three cases are the excluded one, an equation and a
;;; strict inequality, and `ineq' decides the last two), so x is an upper bound
;;; of NN, so NN is bounded above.  NN is a subset of RR (nn-in-rr) and is
;;; inhabited (0), so s = SUP(NN) exists (rr-sup-in) and rr-sup-approx at d = 1
;;; hands back a natural w with s - 1 < w.  Then w + 1 is a natural, so
;;; w + 1 <= s by rr-sup-upper -- against s < w + 1.  From the contradiction
;;; `ineq' proves x < w + 1, so w + 1 is the witness the negated conclusion
;;; denies.
;;;
;;; WHAT IT COSTS.  `modulo 0'.  rr-sup-in / rr-sup-upper are primitive
;;; (number-systems.scm is in *primitive-files*); nn-zero-in / nn-add-closed /
;;; rr-zero-in / rr-one-in are primitive; nn-one-in, nn-in-rr, rr-zero-lt-one,
;;; rr-lt-trichotomy and rr-sup-approx are theorems; `ineq' adds no debt.
;;;
;;; LOAD WINDOW.  [289, 326) in the leaf-triage table's coordinates (library
;;; files, 0-based): lo is forced by rr-sup-approx (theorem-library/
;;; rr-sup-approx.scm, position 288) -- every other citation is at or below
;;; rr-order-basics (137); hi is the earliest citer, bernstein-density (326).
;;; The window is empty for nn-recip-succ-small's citer (compact-separable-
;;; proof, 180) unless rr-sup-approx moves up -- see that file's header.

;;; ---- file-local driver helpers (the `nu-' prefix) --------------------

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (nu-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "nu-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `ineq' wants 1-based assumption indices, named ONE BY ONE: a membership
;;; premise whose atoms cannot be certified in RR poisons the whole call.
(define (nu-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "nu-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (nu-ineq . forms) (apply ineq (map nu-idx forms)))

;;; ---- the statement ---------------------------------------------------

(define nu-concl '(FORSOME n_ (AND (IN n_ NN) (< x n_))))

(define nu-stmt
  (forall-guarded 'x '(IN x RR)
    (forsome-guarded 'n_ '(IN n_ NN)
      '(< x n_))))

;;; ---- the branch that has to die: no natural exceeds x -----------------

;;; Goal (<= z x) for the eigenvariable z, with (IN z NN) in context.  Read z
;;; off the GOAL, never off the context.
(define (nu-bound!)
  (let ((z (cadr (dk-goal)))
        (no (nu-find 'no-witness
              (lambda (a) (and (pair? a) (eq? (car a) 'NOT)
                               (pair? (cadr a)) (eq? (car (cadr a)) 'FORSOME))))))
    (fact 'nn-in-rr z)
    (fact 'rr-lt-trichotomy 'x z)
    (use-cases (list (list '< 'x z) (list '= 'x z) (list '< z 'x))
      ;; x < z: then z IS the witness, against the negated conclusion.
      (lambda ()
        (have! nu-concl (lambda () (ew z) (from-context!)))
        (ai no))
      (lambda () (nu-ineq (list '= 'x z)))
      (lambda () (nu-ineq (list '< z 'x))))))

(define (nu-no-witness!)
  (begin
    ;; the three hypotheses of order completeness, for S = NN
    (have! '(SUBSET NN RR)
      (lambda ()
        (let ((z (subset-by-element!)))
          (fact 'nn-in-rr z)
          (ass))))
    (have! '(FORSOME x_ (IN x_ NN))
      (lambda () (ew 0) (ass)))
    (have! '(RR-BOUNDED-ABOVE NN)
      (lambda ()
        (mac 'rr-bounded-above)
        (ew 'x)
        (mac 'rr-upper-bound)
        (for-each (lambda (k)
                    (dk-focus! k)
                    (if (eq? (car (dk-goal)) 'IN) (ass) (begin (di) (nu-bound!))))
                  (dk-opened (lambda () (di))))))
    (fact 'rr-sup-in 'NN)                            ; SUP(NN) in RR
    ;; a natural within 1 of the supremum
    (let* ((ex    (dk-fact! 'rr-sup-approx 'NN 1))
           (parts (dk-split! ex))
           (w     (cadr (or (find-first (dk-head? 'IN) parts)
                            (error "nu: no landed membership" parts)))))
      (fact 'nn-in-rr w)
      (have! (list 'AND (list 'IN w 'NN) '(IN 1 NN)))
      (fact 'nn-add-closed w 1)                       ; w + 1 in NN
      ;; w + 1 <= SUP(NN), from rr-sup-upper
      (let* ((ub  (dk-fact! 'rr-sup-upper 'NN))
             (ubp (dk-split! (dk-landed-1 (lambda () (mac-h 'rr-upper-bound ub)))))
             (all (or (find-first (dk-head? 'FORALL) ubp)
                      (error "nu: no landed universal" ubp))))
        (inst*! all (list '+ w 1)))
      ;; SUP - 1 < w and w + 1 <= SUP are inconsistent, so x < w + 1
      (have! (list '< 'x (list '+ w 1))
        (lambda () (nu-ineq (list '< '(- (SUP NN) 1) w)
                            (list '<= (list '+ w 1) '(SUP NN)))))
      ;; the goal IS the conclusion here (the NOT-branch of use-em keeps it), so
      ;; exhibit the witness directly -- a `have!' of the goal cuts a self-loop.
      (ew (list '+ w 1))
      (from-context!))))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff nu-stmt))
(di)                                              ; x in RR

(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'nn-zero-in)
(fact 'nn-one-in)
(fact 'rr-zero-lt-one)

(use-em nu-concl
  (lambda () (ass))
  nu-no-witness!)

(qed 'nn-unbounded-in-rr)
(topic! 'nn-unbounded-in-rr 'inequalities)
(alias! 'nn-unbounded-in-rr "archimedean property" "the naturals are unbounded in the reals")
