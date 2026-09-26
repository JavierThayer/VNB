;;; recip-succ-null.scm -- 1/(n+1) -> 0, PROVEN.
;;;
;;;     rr-recip-succ-converges-to-zero:
;;;       CONVERGES-TO(RR-MS, (vnb-lambda k in NN. recip(k + 1)), 0)
;;;
;;; The null sequence every eps/N argument reaches for, and the tree did not
;;; have it: `nn-recip-succ-small' says a scale below eps EXISTS, which is the
;;; combinatorial half, and nothing said the scales CONVERGE.  A ratio test, a
;;; comparison test, or the exponential series each want the second form.
;;;
;;; WHY `+ 1' AND NOT `succ'.  The three facts this rests on --
;;; nn-recip-succ-small, nn-recip-succ-antitone, nn-recip-succ-pos -- are all
;;; stated with `recip(n + 1)', so the statement is written that way to match
;;; them without a rewrite at every citation.  `succ n = n + 1' is
;;; `nn-succ-plus-one' (proven) for a citer that wants the other spelling.
;;;
;;; WHAT IT COSTS: `modulo {nn-recip-succ-small}', trust `informal'.  That leaf
;;; is the Archimedean property in its NN reading and is the only thing between
;;; this result and `modulo 0'; `nn-recip-succ-pos' was the other one until
;;; theorem-library/pos-rr-of-lt.scm proved it.
;;;
;;; THE SHAPE OF THE PROOF, because a CONVERGES-TO goal is four obligations and
;;; only the last is analysis:
;;;
;;;   1. IS-METRIC-SPACE(RR-MS)                     rr-is-metric-space
;;;   2. the lambda is in FUN(NN, RR)               `lam-t', which opens TWO
;;;      leaves -- the pointwise typing AND the SETHOOD of the domain, since a
;;;      VNB-LAMBDA is a set of pairs and is a function only when its domain is
;;;      a set.  A driver expecting one leaf leaves the other open until `qed'.
;;;   3. 0 in RR                                    rr-zero-in
;;;   4. the eps/N estimate.
;;;
;;; `rr-ms@pts' is fired on the goal BEFORE the conjunction is split, so that
;;; PTS(RR-MS) reads RR in obligations 2 and 3 at once.
;;;
;;; TWO TRAPS MET HERE, both of them CLAUDE.md entries:
;;;
;;;  * TYPE THE ARGUMENT BEFORE THE BETA.  `lam-b' on
;;;    (vnb-lambda k NN (recip (k+1)))(n_) is licensed only because `n_ in NN'
;;;    is already in the context; fired earlier it would still reduce and would
;;;    OWE `(IN n_ NN)' at a node where n_ does not yet exist -- an unprovable
;;;    leaf that says nothing until `qed'.
;;;  * `mac' on a GUARDED macete does not apply unless the arguments are typed:
;;;    `rr-ms-dist' is guarded on both of its, so `recip(n_+1) in RR' and
;;;    `0 in RR' are landed before it, or the rewrite silently does not happen
;;;    and the driver sails on rewriting a goal that never changed.
;;;
;;; AND ONE THAT COST A RUN, worth recording because the file that warns about
;;; it was open at the time.  The threshold eigenvariable and the running index
;;; were held apart as `rn-N' and `rn-n' -- and MIT Scheme folds case, so they
;;; are ONE variable.  The threshold silently became the running index, the
;;; antitonicity citation instantiated both slots with it, and the failure
;;; surfaced several steps later as an `ineq' whose premise was not in context.
;;; They are `rn-bnd' and `rn-run' below.  Never distinguish two names by case.
;;;
;;; Loads after pos-rr-of-lt (nn-recip-succ-pos), rr-abs-basics (rr-abs-bound),
;;; order-predicates (nn-recip-succ-small/-antitone), numeric-instances
;;; (RR-MS, rr-ms@pts, rr-ms-dist) and metric-completeness (CONVERGES-TO).

(define (rn-fvs fs) (apply append (map free-vars fs)))

;;; Skolemize a FORSOME already in the CONTEXT: `obtain' diffs its own lane and
;;; cannot see one, and it swallows the error if the lane raises.
(define (rn-skolem! ex)
  (let* ((fv0 (rn-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (rn-fvs (dk-asms)))))
      (if (null? fresh) (error "rn-skolem!: nothing fresh appeared for" ex)
          (car fresh)))))

(define (rn-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rn-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (rn-ineq . fs) (apply ineq (map rn-idx fs)))

;;; POS-RR(t) -> the three conjuncts, on the assumption side.
(define (rn-open-pos! t)
  (mac-h 'pos-rr (list 'POS-RR t))
  (dk-split! (list 'AND (list 'IN t 'RR)
                   (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t))))))

(define rn-lam '(VNB-LAMBDA k NN (recip (+ k 1))))

(sp (make-wff (list 'CONVERGES-TO 'RR-MS rn-lam 0)))
(mac 'converges-to)
;; PTS(RR-MS) reads RR in every conjunct at once.  `slot' and NOT
;; `(mac 'rr-ms@pts)': an accessor's reduction is global and unconditional, a
;; deliberate but PROVISIONAL choice, and `slot' is the single procedure allowed
;; to depend on it -- the suite fails any other file that fires an accessor
;; macete by name (accessor-callsite-audit).  Caught exactly that way here.
(slot 'PTS)

;;; Split the four obligations.
(define rn-leaves '())
(let loop ()
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (l) (dk-focus! l) (loop)) (dk-opened (lambda () (di))))
        (set! rn-leaves (cons (proof-state-focus *ps*) rn-leaves)))))

(define (rn-leaf-headed head)
  (let loop ((l rn-leaves))
    (cond ((null? l) (error "rn-leaf-headed: none" head))
          ((eq? (car (dk-goal-of (car l))) head) (car l))
          (else (loop (cdr l))))))

;;; 1.  RR-MS is a metric space.
(dk-focus! (rn-leaf-headed 'IS-METRIC-SPACE))
(fact 'rr-is-metric-space)
(ass)

;;; 3.  0 is real.  Same head as obligation 2, so choose by the SUBJECT.
(define rn-in-leaves (filter (lambda (l) (eq? (car (dk-goal-of l)) 'IN)) rn-leaves))
(define (rn-in-leaf want)
  (let loop ((l rn-in-leaves))
    (cond ((null? l) (error "rn-in-leaf: none"))
          ((eq? (equal? (dk-goal-of (car l)) '(IN 0 RR)) want) (car l))
          (else (loop (cdr l))))))
(dk-focus! (rn-in-leaf #t))
(fact 'rr-zero-in)
(ass)

;;; 2.  The lambda is a member of FUN(NN, RR) -- TWO leaves.
(dk-focus! (rn-in-leaf #f))
(define rn-lam-branches (dk-opened (lambda () (lam-t))))
(define (rn-branch-headed head)
  (let loop ((l rn-lam-branches))
    (cond ((null? l) (error "rn-branch-headed: none" head))
          ((eq? (car (dk-goal-of (car l))) head) (car l))
          (else (loop (cdr l))))))

(dk-focus! (rn-branch-headed 'IN))            ; NN in SET -- the sethood half
(fact 'nn-is-set)
(ass)

(dk-focus! (rn-branch-headed 'FORALL))        ; the pointwise typing
(di)
(let ((kk (cadr (cadr (cadr (dk-goal))))))    ; goal (IN (recip (+ k 1)) RR)
  (fact 'nn-recip-succ-pos kk)
  (rn-open-pos! (list 'recip (list '+ kk 1)))
  (ass))

;;; 4.  The estimate.
(dk-focus! (car (proof-leaves)))
(di) (di)                                     ; unguarded FORALL eps, then POS-RR eps
(define rn-bnd (rn-skolem! (dk-fact! 'nn-recip-succ-small 'eps)))
(ew rn-bnd)

;;; `ew' leaves the witness's own typing beside the estimate; the typing is
;;; already in context from the skolemization.
(define rn-ew (dk-opened (lambda () (di))))
(for-each (lambda (l) (dk-focus! l) (if (eq? (car (dk-goal)) 'IN) (ass))) rn-ew)

(dk-focus! (car (filter (lambda (l) (eq? (car (dk-goal-of l)) 'FORALL)) rn-ew)))
(di)                                          ; the running index
(define rn-run
  (cadr (car (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN) (eq? (caddr a) 'NN)
                                      (not (eq? (cadr a) rn-bnd))))
                     (dk-asms)))))
(di)                                          ; and the threshold hypothesis

(define rn-recip-run (list 'recip (list '+ rn-run 1)))
(define rn-recip-bnd (list 'recip (list '+ rn-bnd 1)))

(lam-b)                                       ; argument typed above; see the header
(fact 'nn-recip-succ-pos rn-run)
(rn-open-pos! rn-recip-run)
(fact 'rr-zero-in)
(mac 'rr-ms-dist)                             ; both arguments now typed

;;; |1/(n+1) - 0| <= eps, as a pair of linear bounds the oracle can take.
(rn-open-pos! 'eps)
(fact 'rr-sub-in-rr rn-recip-run 0)
(mac 'rr-abs-bound)

;;; The threshold's reciprocal needs an `IN _ RR' certificate too, or `ineq'
;;; cannot certify the atom and reports that the GOAL does not follow.
(fact 'nn-recip-succ-pos rn-bnd)
(rn-open-pos! rn-recip-bnd)
(fact 'nn-recip-succ-antitone rn-bnd rn-run)

(for-each
 (lambda (l)
   (dk-focus! l)
   (rn-ineq (list '<= rn-recip-run rn-recip-bnd)
            (list '< rn-recip-bnd 'eps)
            (list '<= 0 rn-recip-run)
            '(<= 0 eps)))
 (dk-opened (lambda () (di))))

(qed 'rr-recip-succ-converges-to-zero)
(topic! 'rr-recip-succ-converges-to-zero 'analysis)
(alias! 'rr-recip-succ-converges-to-zero "the sequence 1/(n+1) converges to 0")
