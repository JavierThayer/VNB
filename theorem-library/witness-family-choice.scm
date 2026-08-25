;;; witness-family-choice.scm -- TWO FAMILIES BUILT BY CHOICE, and nothing else.
;;;
;;;   antiderivable-family-choice   forall k. IS-ANTIDERIVABLE(phifam(k),a,b)
;;;                                 =>  forsome fam in FUN(NN,FUN(RR,RR)).
;;;                                     forall k. IS-ANTIDERIVATIVE(fam(k), phifam(k), a, b)
;;;
;;;   diff-at-witness-family        forall k. IS-DIFF-AT(fam(k), t, lfam(k))
;;;                                 =>  forsome wfam in FUN(NN,FUN(RR,RR)).
;;;                                     forall k. wfam(k) is a Caratheodory
;;;                                     witness for fam(k) at t
;;;
;;; WHY.  Both hypotheses are a universally quantified EXISTENTIAL -- "for each
;;; k there is such a function" -- and every theorem that consumes such a family
;;; wants it as a FUNCTION on NN: `uniform-limit-continuous-at' and
;;; `diff-at-ptwise-limit' both take `fam in FUN(NN, FUN(RR,RR))' and apply it,
;;; and neither can be cited about a k-indexed existential.  Turning the one
;;; into the other is global CHOICE plus the separation schema, and it is the
;;; same three lines both times:
;;;
;;;   * the SEP of the functions with the wanted property, at index k;
;;;   * `choose!' (driver-kit), which lands (IN (CHOICE S) S) against the
;;;     existential witness the hypothesis supplies, and splits the SEP
;;;     membership into its domain and property halves;
;;;   * the VNB-LAMBDA k |-> CHOICE(...), typed by `lam-t' and reduced by
;;;     `lam-b' -- k is typed by the enclosing guard before the beta, which is
;;;     what keeps `lam-b' from owing an (IN k NN) at a node where k does not
;;;     occur.
;;;
;;; THE CHOICE TERM DOES NOT ESCAPE.  Both statements conclude with a FORSOME,
;;; so a consumer skolemizes and never sees a CHOICE at all.  That is
;;; deliberate: the family is not canonical (a different SEP, or a different
;;; global choice, gives a different one) and nothing downstream should be able
;;; to depend on which one it got.
;;;
;;; TWO MECHANICAL POINTS.
;;;
;;; * `choose!' returns what `sep-me' landed, and when the SEP's property is
;;;   itself a CONJUNCTION that lands as ONE formula.  The `ass' that wants a
;;;   single conjunct then fails with "goal not in context" and the enclosing
;;;   `have!' reports its side goal left open -- three steps away from the cause.
;;;   Split the landed conjunctions before closing anything.
;;; * The second statement is a four-deep alternation of quantifiers, and it was
;;;   written first as a hand-nested paren pyramid, which cost a run to a
;;;   miscount that MIT reported as "Premature EOF" at the END of the file.
;;;   `forall-guarded' / `forsome-guarded' / `conjuncts->and' (structures.scm)
;;;   take FLAT lists and have no last close to lose.
;;;
;;; Both `modulo 0'.  The property of the second is written to be LITERALLY the
;;; tail of IS-DIFF-AT's defining body, so the skolemized witness closes each
;;; conjunct by `ass' with no reshaping.
;;;
;;; Loads after antiderivative (IS-ANTIDERIVABLE, antiderivative-map-in-fun),
;;; differentiation (IS-DIFF-AT), metric-continuity (IS-CONTINUOUS-AT) and
;;; driver-kit (choose!, in-sep!, dk-lam-t!).
;;; =====================================================================

;;; ---- file-local driver helpers (the `wf-' prefix) --------------------

(define (wf-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (begin (di) (loop (+ n 1))) #t))))

(define (wf-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "wf-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; skolemize a FORSOME already in the CONTEXT (`obtain' sees only its own lane);
;;; the eigenvariable is read off by free-variable set difference.
(define (wf-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

(define (wf-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (wf-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (wf-split-landed! fs)
  (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) fs))

;;; The common tail: exhibit the lambda, type it by `lam-t', and close the
;;; pointwise claim by `lam-b' against the per-index fact PT.
(define (wf-exhibit! lam pt)
  (ew lam)
  (wf-and!
   (lambda ()
     (let ((g (dk-goal)))
       (if (and (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
           (begin
             (dk-lam-t!)
             (let ((z (cadr (car (dk-landed (lambda () (di)))))))
               (dk-split! (dk-deepest (lambda () (inst+ pt z))))
               (ass)))
           (let ((z (cadr (car (dk-landed (lambda () (di)))))))
             (lam-b)
             (dk-split! (dk-deepest (lambda () (inst+ pt z))))
             (wf-and! (lambda () (ass)))))))))

;;; =====================================================================
;;; 1.  THE ANTIDERIVATIVE FAMILY.
;;; =====================================================================

(define (wf-a-sep k) (list 'SEP 'f_ '(FUN RR RR)
                           (list 'IS-ANTIDERIVATIVE 'f_ (list 'phifam k) 'a 'b)))
(define wf-a-lam (list 'VNB-LAMBDA 'k_ 'NN (list 'CHOICE (wf-a-sep 'k_))))

(sp (make-wff "forall([phifam in fun(nn, fun(rr,rr)), a in rr, b in rr],
   forall([k_ in nn], is-antiderivable(phifam(k_), a, b)) implies
   forsome([fam in fun(nn, fun(rr,rr))],
      forall([k_ in nn], is-antiderivative(fam(k_), phifam(k_), a, b))))"))
(quietly (lambda () (wf-peel!)))
(define WF-AH (car (dk-asms)))

(have! (forall-guarded 'k_ '(IN k_ NN)
         (list 'AND (list 'IN (list 'CHOICE (wf-a-sep 'k_)) '(FUN RR RR))
                    (list 'IS-ANTIDERIVATIVE (list 'CHOICE (wf-a-sep 'k_))
                          '(phifam k_) 'a 'b)))
  (lambda ()
    (quietly (lambda ()
      (di)
      (dk-deepest (lambda () (inst+ WF-AH 'k_)))
      (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE '(phifam k_) 'a 'b))
      (let* ((ex (wf-find 'ex (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)))))
             (sk (wf-skolem! ex))
             (w  (car (cadr sk))))
        (fact 'antiderivative-map-in-fun w '(phifam k_) 'a 'b)
        (wf-split-landed!
          (choose! (wf-a-sep 'k_) w
                   (lambda () (in-sep! (lambda () (ass)) (lambda () (ass))))))
        (wf-and! (lambda () (ass))))))))

(quietly (lambda () (wf-exhibit! wf-a-lam (car (dk-asms)))))
(qed 'antiderivable-family-choice)
(topic! 'antiderivable-family-choice 'analysis)
(alias! 'antiderivable-family-choice
        "a sequence of antiderivable functions has a sequence of antiderivatives")

;;; =====================================================================
;;; 2.  THE CARATHEODORY WITNESS FAMILY AT A FIXED POINT.
;;; =====================================================================

;;; literally the tail of IS-DIFF-AT's defining body (differentiation.scm)
(define (wf-w-prop w k)
  (conjuncts->and
    (list (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS w 't_)
          (list '= (list w 't_) (list 'lfam k))
          (forall-guarded 'x_ '(IN x_ RR)
            (list '= (list '- (list (list 'fam k) 'x_) (list (list 'fam k) 't_))
                     (list '* (list w 'x_) '(- x_ t_)))))))
(define (wf-w-sep k) (list 'SEP 'w_ '(FUN RR RR) (wf-w-prop 'w_ k)))
(define wf-w-lam (list 'VNB-LAMBDA 'k_ 'NN (list 'CHOICE (wf-w-sep 'k_))))

(sp (make-wff
  (forall-guarded '(fam lfam t_)
    (list '(IN fam (FUN NN (FUN RR RR)))
          '(IN lfam (FUN NN RR))
          '(IN t_ RR)
          (forall-guarded 'k_ '(IN k_ NN) '(IS-DIFF-AT (fam k_) t_ (lfam k_))))
    (forsome-guarded 'wfam '(IN wfam (FUN NN (FUN RR RR)))
      (forall-guarded 'k_ '(IN k_ NN) (wf-w-prop '(wfam k_) 'k_))))))
(quietly (lambda () (wf-peel!)))
(define WF-WH (car (dk-asms)))

(have! (forall-guarded 'k_ '(IN k_ NN)
         (list 'AND (list 'IN (list 'CHOICE (wf-w-sep 'k_)) '(FUN RR RR))
                    (wf-w-prop (list 'CHOICE (wf-w-sep 'k_)) 'k_)))
  (lambda ()
    (quietly (lambda ()
      (di)
      (dk-deepest (lambda () (inst+ WF-WH 'k_)))
      (dk-split! (dk-landed-1 (lambda ()
         (mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT '(fam k_) 't_ '(lfam k_))))))
      (let* ((ex (wf-find 'ex (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)))))
             (sk (wf-skolem! ex))
             (w  (car (cadr sk))))
        (dk-split! (car sk))
        (wf-split-landed!
          (choose! (wf-w-sep 'k_) w
                   (lambda () (in-sep! (lambda () (ass))
                                       (lambda () (wf-and! (lambda () (ass))))))))
        (wf-and! (lambda () (ass))))))))

(quietly (lambda () (wf-exhibit! wf-w-lam (car (dk-asms)))))
(qed 'diff-at-witness-family)
(topic! 'diff-at-witness-family 'analysis)
(alias! 'diff-at-witness-family
        "a sequence of differentiable maps has a sequence of Caratheodory witnesses")
