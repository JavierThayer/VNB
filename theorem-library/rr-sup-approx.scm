;;; rr-sup-approx.scm -- the SUP APPROXIMATION lemma, PROVEN.
;;;
;;;   S subset RR, S inhabited, S bounded above, d in RR, 0 < d
;;;     =>  forsome w.  w in S  and  SUP(S) - d < w
;;;
;;; "Nothing below SUP(S) is an upper bound."  It is the one half of order
;;; completeness that `rr-sup-in' / `rr-sup-upper' / `rr-sup-least' do not hand
;;; you directly: those three are all statements ABOUT SUP(S), and every
;;; creeping argument needs the converse move -- from "s is the LEAST upper
;;; bound" to an actual MEMBER of S near s.
;;;
;;; WHY IT IS ITS OWN FILE.  Every sup argument that has to look BACKWARD from
;;; the supremum needs it, and it is the step that cannot be done by `ineq': it
;;; is a classical existence step (excluded middle on the conclusion, then
;;; De Morgan through a universal), not a linear-arithmetic one.  IVT did not
;;; need it -- Bolzano's argument only ever shows that a candidate IS an upper
;;; bound -- which is exactly why it did not appear until the EVT work.  It is
;;; the workhorse of theorem-library/ccint-creep.scm and of both halves of EVT.
;;;
;;; THE PROOF.  Excluded middle on the conclusion.  If no member of S exceeds
;;; SUP(S) - d, then every member is <= SUP(S) - d (trichotomy: the three cases
;;; are the excluded one, an equation and a strict inequality, and `ineq'
;;; decides the last two), so SUP(S) - d is an upper bound, so rr-sup-least
;;; gives SUP(S) <= SUP(S) - d, hence d <= 0 against 0 < d.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.  rr-sup-in / rr-sup-least are
;;; primitive (number-systems.scm is in *primitive-files*), subset-mem-fwd,
;;; rr-sub-in-rr and rr-lt-trichotomy are theorems, and `ineq' adds no debt.
;;;
;;; Loads with the calculus arc, after ivt-proof; its own needs are subset-lemmas
;;; (subset-mem-fwd), rr-order-basics
;;; (rr-lt-trichotomy), binary-minus-laws (rr-sub-in-rr) and driver-kit.

;;; ---- file-local driver helpers (the `sa-' prefix) --------------------

;;; Peel the whole guarded FORALL/IMPLIES prefix.  `di' is greedy WITHIN one
;;; binder level and stops at the next, so this takes several calls; guarded on
;;; fuel as well as on the head, because `di' only WARNS when it cannot
;;; decompose and a head test alone would spin on the no-op.
(define (sa-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; Select a hypothesis by CONTENT and ERROR on a miss -- a driver that
;;; reconstructs a formula to cite it addresses the wrong assumption silently.
(define (sa-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "sa-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `ineq' wants 1-based assumption indices, and the premises are named ONE BY
;;; ONE rather than swept up: the context carries membership formulas whose
;;; atoms can never be certified in RR, and a single such premise poisons the
;;; whole call.
(define (sa-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "sa-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (sa-ineq . forms) (apply ineq (map sa-idx forms)))

;;; ---- the statement ---------------------------------------------------

(define sa-sup '(SUP s_))
(define sa-lo (list '- sa-sup 'd_))
(define sa-concl (list 'FORSOME 'w_ (list 'AND '(IN w_ s_) (list '< sa-lo 'w_))))

(define sa-stmt
  (forall-guarded '(s_ d_)
    (list '(SUBSET s_ RR) '(FORSOME x_ (IN x_ s_)) '(RR-BOUNDED-ABOVE s_)
          '(IN d_ RR) '(< 0 d_))
    sa-concl))

;;; ---- the branch that has to die: no member exceeds SUP(S) - d --------

;;; Goal (<= z (- (SUP s_) d_)) for the eigenvariable z, with (IN z s_) in
;;; context.  Read z off the GOAL, never off the context: `dk-asms' order is
;;; not the peel order.
(define (sa-bound!)
  (let ((z (cadr (dk-goal)))
        (no (sa-find 'no-witness
              (lambda (a) (and (pair? a) (eq? (car a) 'NOT)
                               (pair? (cadr a)) (eq? (car (cadr a)) 'FORSOME))))))
    (fact 'subset-mem-fwd 's_ 'RR z)
    (fact 'rr-lt-trichotomy sa-lo z)
    (use-cases (list (list '< sa-lo z) (list '= sa-lo z) (list '< z sa-lo))
      ;; SUP(S) - d < z: then z IS the witness, against the negated conclusion.
      (lambda ()
        (have! sa-concl (lambda () (ew z) (from-context!)))
        (ai no))
      ;; the equation and the strict inequality are linear consequences
      (lambda () (sa-ineq (list '= sa-lo z)))
      (lambda () (sa-ineq (list '< z sa-lo))))))

(define (sa-no-witness!)
  (have! (list 'RR-UPPER-BOUND 's_ sa-lo)
    (lambda ()
      (mac 'rr-upper-bound)
      (for-each (lambda (k)
                  (dk-focus! k)
                  (if (eq? (car (dk-goal)) 'IN) (ass) (begin (di) (sa-bound!))))
                (dk-opened (lambda () (di))))))
  (fact 'rr-sup-least 's_ sa-lo)                 ; SUP(S) <= SUP(S) - d
  (have! '(= 0 d_)
    (lambda () (sa-ineq (list '<= sa-sup sa-lo) '(<= 0 d_))))
  (ai '(NOT (= 0 d_))))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff sa-stmt))
(sa-peel!)

(mac-h '< '(< 0 d_))
(dk-split! '(AND (<= 0 d_) (NOT (= 0 d_))))
(fact 'rr-sup-in 's_)                            ; SUP(S) in RR
(fact 'rr-sub-in-rr sa-sup 'd_)                  ; SUP(S) - d in RR

(use-em sa-concl
  (lambda () (ass))
  sa-no-witness!)

(qed 'rr-sup-approx)
(topic! 'rr-sup-approx 'analysis)
(alias! 'rr-sup-approx "supremum approximation" "approximation property of the supremum")
