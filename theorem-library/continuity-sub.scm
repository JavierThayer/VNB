;;; continuity-sub.scm -- the pointwise DIFFERENCE of two maps continuous at a
;;; point is continuous there, PROVEN, with its FUN typing.
;;;
;;;   g, h continuous at a  =>  (VNB-LAMBDA x RR (- (g x) (h x))) continuous at a
;;;
;;; This was the last of the seven `support' + `warrant! 'well-known' facts in
;;; theorem-library/continuity-algebra.scm to carry content, and after
;;; continuity-transfer.scm it was the SOLE unwarranted leaf of
;;; `diff-implies-continuous'.  The statement is reproduced VERBATIM from
;;; continuity-algebra.scm, so differentiation.scm's citation reads exactly as
;;; before.
;;;
;;; NO EPS/DELTA IS DONE HERE, and that is the point of the file.  The retired
;;; warrant proposed the obvious route -- "the eps/2 split for sum-continuous-at,
;;; negation being an isometry of RR" -- i.e. a second copy of continuity-sum's
;;; driver with `-' throughout.  It is not needed.  Three theorems already in the
;;; library compose:
;;;
;;;   neg-continuous-at   (neg-continuous.scm)      -h is continuous at a
;;;   sum-continuous-at   (continuity-sum.scm)      g + (-h) is continuous at a
;;;   cont-transfer-ptwise-eq (continuity-transfer) ... and so is anything
;;;                                                 agreeing with it pointwise
;;;
;;; and the difference lambda agrees with the sum lambda pointwise by one `crs'.
;;; The whole proof is four `fact's and a bridge.
;;;
;;; THE BRIDGE IS THE WHOLE STORY, and it is worth stating why it is needed at
;;; all.  `sum-continuous-at' concludes about the LITERAL term it builds,
;;;
;;;     (VNB-LAMBDA x RR (+ (g x) ((VNB-LAMBDA z_ RR (- (h z_))) x)))
;;;
;;; which is not the term this theorem is about.  The two denote the same
;;; function and are different S-expressions, and no amount of continuity
;;; reasoning closes that gap -- it is a gap about SYNTAX.  Closing it is
;;; exactly what `cont-transfer-ptwise-eq' is for: beta-reduce both sides at a
;;; real point, and what is left is
;;;
;;;     (- (g w) (h w))  =  (+ (g w) (- (h w)))
;;;
;;; which `crs' decides once (g w) and (h w) are typed in RR.  (`crs' handles
;;; the binary minus directly; no `binary-minus-def' unfold is needed.)
;;;
;;; THE ONE TRAP, and it is `mac-h' being destructive.  `neg-continuous-at' and
;;; `neg-fun-in-fun' both want (IN h (FUN RR RR)), and `neg-continuous-at' wants
;;; (IN a RR) as well -- none of which this theorem assumes.  All three are
;;; conjuncts of the continuity hypotheses, but unfolding a hypothesis to read
;;; them off DELETES the hypothesis that the very next `fact' needs.  So each
;;; typing is extracted inside a `have!' LANE (`cu-typing!' / `cu-point!'
;;; below): the unfold happens on the side branch, the main branch keeps
;;; IS-CONTINUOUS-AT intact and gains the typing.  Doing it in the main branch
;;; instead loses the hypothesis and the following `fact' silently lands an
;;; implication rather than its conclusion.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after neg-continuous (neg-fun-in-fun, neg-continuous-at),
;;; continuity-sum (sum-continuous-at), continuity-transfer
;;; (cont-transfer-ptwise-eq), binary-minus-laws (rr-sub-in-rr),
;;; fun-apply-type-proof (fun-apply-type-c) -- and BEFORE continuity-algebra,
;;; whose `sub-continuous-at' support it retires, and differentiation.

;;; ---- file-local driver helpers (the `cu-' prefix) --------------------

(define (cu-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (cu-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 18)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (cu-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cu-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (cu-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (cu-has-lambda-app? (car g)) (cu-has-lambda-app? (cdr g))))
        (else #f)))

;;; `lam-b' to exhaustion.  Safe here because the argument is already typed in
;;; RR when this runs -- see the `lam-b' note in CLAUDE.md: firing it before the
;;; typing is evident still reduces, but OWES (IN arg RR) at a node whose
;;; context predates the binder, and that leaf can never be closed.
(define (cu-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (cu-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; =====================================================================
;;; (1) x |-> g(x) - h(x) is a function RR -> RR.
;;;
;;; `lam-t' opens TWO leaves, not one: the pointwise typing of the body and the
;;; SETHOOD of the domain -- a VNB-LAMBDA is a set of pairs, so RR must be a set
;;; before the lambda is a function at all.
;;; =====================================================================

(define cu-sub-lam '(VNB-LAMBDA x RR (- (g x) (h x))))

(sp (make-wff (forall-guarded '(g h) (list '(IN g (FUN RR RR)) '(IN h (FUN RR RR)))
                (list 'IN cu-sub-lam '(FUN RR RR)))))
(cu-peel!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (let ((z (cadr (car (cu-di-landed!)))))
         (fact 'fun-apply-type-c 'g 'RR 'RR z)
         (fact 'fun-apply-type-c 'h 'RR 'RR z)
         (fact 'rr-sub-in-rr (list 'g z) (list 'h z))
         (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))
(qed 'sub-lam-in-fun)
(topic! 'sub-lam-in-fun 'analysis)
(alias! 'sub-lam-in-fun
        "the pointwise difference of two real functions is a function")

;;; =====================================================================
;;; (2) sub-continuous-at.
;;; =====================================================================

;;; eigenvariables, set as the proof runs
(define cu-g #f)          ; the minuend
(define cu-h #f)          ; the subtrahend
(define cu-a #f)          ; the point

;;; (IN FN (FUN RR RR)) read off FN's continuity WITHOUT destroying it: the
;;; unfold runs inside the have! lane, so it replaces the hypothesis only on
;;; that side branch.  The main branch keeps IS-CONTINUOUS-AT and gains the
;;; typing.
(define (cu-typing! fn)
  (have! (list 'IN fn '(FUN RR RR))
    (lambda ()
      (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS fn cu-a))
      (cu-split!)
      (slot-h 'PTS (list 'IN fn '(FUN (PTS RR-MS) (PTS RR-MS))))
      (ass))))

;;; ... and (IN a RR), the same way, off g's continuity.
(define (cu-point!)
  (have! (list 'IN cu-a 'RR)
    (lambda ()
      (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS cu-g cu-a))
      (cu-split!)
      (slot-h 'PTS (list 'IN cu-a '(PTS RR-MS)))
      (ass))))

;;; Statement reproduced VERBATIM from theorem-library/continuity-algebra.scm,
;;; where it stood as a `well-known' support until 2026-08-18.
(define cu-stmt
  '(FORALL g (FORALL h (FORALL a (IMPLIES
     (IS-CONTINUOUS-AT RR-MS RR-MS g a)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS h a)
     (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (- (g x) (h x))) a)))))))

(sp (make-wff cu-stmt))
(cu-peel!)

;;; The three eigenvariables off the GOAL, which names all three in their roles.
;;; Never off the context here: the two continuity hypotheses are the same shape
;;; and the context order is not the peel order.
(let* ((g0 (dk-goal)) (lam (list-ref g0 3)) (body (list-ref lam 3)))
  (set! cu-a (list-ref g0 4))
  (set! cu-g (car (list-ref body 1)))
  (set! cu-h (car (list-ref body 2))))

;;; the three lambdas: the one this theorem is about, the negation
;;; `neg-continuous-at' builds, and the sum `sum-continuous-at' builds out of it
(define cu-sub (list-ref (dk-goal) 3))
(define cu-neg (list 'VNB-LAMBDA 'z_ 'RR (list '- (list cu-h 'z_))))
(define cu-sum (list 'VNB-LAMBDA 'x 'RR (list '+ (list cu-g 'x) (list cu-neg 'x))))

;;; the typings, each in its own lane (see the header's trap note)
(cu-typing! cu-g)
(cu-typing! cu-h)
(cu-point!)

;;; the continuity algebra, forward
(fact 'neg-fun-in-fun cu-h)                    ; -h is a function
(fact 'neg-continuous-at cu-h cu-a)            ; ... and continuous at a
(fact 'sum-continuous-at cu-g cu-neg cu-a)     ; g + (-h) is continuous at a
(fact 'sub-lam-in-fun cu-g cu-h)               ; g - h is a function

;;; the bridge: g - h and g + (-h) agree at every real point
(have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ RR)
                               (list '= (list cu-sub 'w_) (list cu-sum 'w_))))
  (lambda ()
    (let ((v (cadr (car (cu-di-landed!)))))       ; (IN w RR) -- BEFORE any beta
      (cu-beta!)
      (fact 'fun-apply-type-c cu-g 'RR 'RR v)
      (fact 'fun-apply-type-c cu-h 'RR 'RR v)
      (crs))))

(fact 'cont-transfer-ptwise-eq cu-sub cu-sum cu-a)
(ass)

(qed 'sub-continuous-at)
(topic! 'sub-continuous-at 'analysis)
(alias! 'sub-continuous-at
        "the difference of two continuous maps is continuous")
