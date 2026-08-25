;;; evt-min-proof.scm -- the EXTREME VALUE THEOREM (min form), PROVEN.
;;;
;;;   f in FUN(RR,RR), a <= b, f continuous at every point of [a,b]
;;;     =>  forsome c in [a,b].  forall x in [a,b].  f(c) <= f(x)
;;;
;;; It is `extreme-value-max' (theorem-library/evt-proof.scm) at the map
;;; z |-> -f(z), and NOT a second copy of that file's two creeps.  What made
;;; the reduction available is the pair of theorems in
;;; theorem-library/neg-continuous.scm: -f is a function RR -> RR
;;; (`neg-fun-in-fun'), and it is continuous wherever f is
;;; (`neg-continuous-at').  Both are `modulo 0', so the min form costs exactly
;;; what the max form costs.
;;;
;;; The warrant this file retires said the same thing -- "apply
;;; extreme-value-max to -f; the argmax of -f is the argmin of f" -- and was a
;;; proof written in prose and then not run.  Running it is four steps: cite
;;; extreme-value-max at the lambda, skolemize its argmax c, beta-reduce the
;;; two applications of the lambda in the resulting inequality (`lam-b-h', the
;;; hypothesis-side twin of `lam-b' -- a `fact' that instantiates a function
;;; VARIABLE at a lambda lands the APPLIED lambda in the CONTEXT, where the
;;; goal-side beta cannot reach it), and hand -f(x) <= -f(c) to `ineq'.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after evt-proof and neg-continuous.

;;; ---- file-local driver helpers (the `em-' prefix) --------------------

(define (em-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (em-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "em-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (em-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "em-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (em-ineq . forms) (apply ineq (map em-idx forms)))

(define (em-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (em-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (em-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (em-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "em-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (em-fvs forms) (apply append (map free-vars forms)))

(define (em-skolem! ex)
  (let* ((fv0 (em-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (em-fvs (dk-asms)))))
      (if (null? fresh)
          (error "em-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

;;; ---- the map, the statement, and the finders -------------------------

(define em-neg '(VNB-LAMBDA z_ RR (- (f z_))))

(define em-stmt
  '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (<= a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
       (FORSOME c (AND (IN c (CCINT a b))
                  (FORALL x (IMPLIES (IN x (CCINT a b))
                    (<= (f c) (f x))))))))))))

(define em-neg-cont
  (list 'FORALL 'x_
    (list 'IMPLIES '(IN x_ (CCINT a b))
          (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS em-neg 'x_))))

;;; Discriminate the continuity hypothesis on its CONSEQUENT: extreme-value-max
;;; carries the very same universal in its ANTECEDENT, and once cited its
;;; instantiation chain sits nearer the top of the context.
(define (em-forall-cont-of g)
  (em-find 'cont
    (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                     (let ((body (caddr h)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body))
                            (eq? (car (caddr body)) 'IS-CONTINUOUS-AT)
                            (equal? (list-ref (caddr body) 3) g)))))))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff em-stmt))
(em-peel!)
(em-split!)

(have! '(SUBSET (CCINT a b) RR)
  (lambda ()
    (mac 'subset-def)
    (let ((mem (car (em-di-landed!))))
      (mac-h 'ccint-membership mem)
      (em-split!)
      (ass))))

;;; -f is a function RR -> RR, and is continuous at every point of [a,b]
(fact 'neg-fun-in-fun 'f)
(have! em-neg-cont
  (lambda ()
    (let* ((mem (car (em-di-landed!)))
           (x (cadr mem)))
      (fact 'subset-mem-fwd '(CCINT a b) 'RR x)
      (inst+ (em-forall-cont-of 'f) x)
      (fact 'neg-continuous-at 'f x)
      (ass))))

;;; EVT (max) at -f
(have! (list 'AND (list 'IN em-neg '(FUN RR RR))
                  '(AND (IN a RR) (AND (IN b RR) (<= a b)))))
(define em-argmax
  (em-skolem! (dk-fact! 'extreme-value-max em-neg 'a 'b)))

;;; the argmax of -f is the argmin of f
(ew em-argmax)
(em-goal-and!
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORALL)
       (let* ((mem (car (em-di-landed!)))
              (x (cadr mem)))
         (fact 'subset-mem-fwd '(CCINT a b) 'RR x)
         (fact 'subset-mem-fwd '(CCINT a b) 'RR em-argmax)
         (fact 'fun-apply-type-c 'f 'RR 'RR x)
         (fact 'fun-apply-type-c 'f 'RR 'RR em-argmax)
         (let ((le (dk-deepest
                    (lambda ()
                      (inst+ (em-find 'negmax
                               (lambda (h)
                                 (and (pair? h) (eq? (car h) 'FORALL)
                                      (dk-contains? h em-neg)
                                      (dk-contains? h em-argmax))))
                             x)))))
           ;; The applied lambda landed in the CONTEXT, so the beta is
           ;; hypothesis-side.  Loop rather than count: one `lam-b-h' takes
           ;; both applications here, and a second call would then find nothing
           ;; and error.
           (lam-b-h le)
           (let loop ((n 0))
             (let ((h (find-first (lambda (a) (and (pair? a) (eq? (car a) '<=)
                                                   (dk-contains? a 'VNB-LAMBDA)))
                                  (dk-asms))))
               (if (and h (< n 4)) (begin (lam-b-h h) (loop (+ n 1))))))
           (em-ineq (list '<= (list '- (list 'f x))
                              (list '- (list 'f em-argmax))))))
       (ass))))

(qed 'extreme-value-min)
(topic! 'extreme-value-min 'analysis)
(alias! 'extreme-value-min "Extreme Value Theorem" "EVT")
