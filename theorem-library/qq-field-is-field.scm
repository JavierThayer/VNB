;;; qq-field-is-field.scm -- IS-FIELD(QQ-FIELD), PROVED.
;;;
;;; It was an asserted axiom with no warrant (numeric-instances.scm), i.e.
;;; `trust: none' -- and it was the SOLE unwarranted leaf of `qq-line-is-module'
;;; and `qq-line-is-vector-space', so those two read `trust: none' for it alone.
;;; QQ-FIELD is also the tree's only FIELD instance, so it is what witnesses
;;; FIELD-RING through `field-is-field-ring', and (once `field-is-pid' exists)
;;; what will witness PID.
;;;
;;; THE SLOT-8 STORY, which is why this needed an amendment and not just a proof.
;;; IS-FIELD carries `(op MUL-INV NON-ZERO NON-ZERO)', hence the conjunct
;;;
;;;     MUL-INV(QQ-FIELD)  in  FUN(QQ \ {0}, QQ \ {0}).
;;;
;;; With the bare constant `recip' in slot 8 -- as the instance had it -- nothing
;;; in the tree discharges that: there is no `recip in FUN(...)' statement for
;;; ANY carrier.  Nor may one be added.  `recip' is a single shared constant
;;; (qq-recip-closed, rr-recip-closed, binary-divide-def all name it), so
;;; `recip in FUN(QQ\{0},.)' beside `recip in FUN(RR\{0},.)' proves
;;; QQ\{0} = RR\{0} by `dom-of-fun' -- the one-object-two-domains inconsistency
;;; the 2026-08-29 bridge repair took 14 axioms out for.  The instance now holds
;;; a LAMBDA in slot 8, exactly as slots 2-4 hold lambdas for the same reason,
;;; and the conjunct is PROVED by `lam-t'.
;;;
;;; THE BILL.  This lands at `well-known', not `modulo 0', and the whole of the
;;; residue is `difference-membership' / `difference-set' (prod-of-sums.scm) --
;;; asserted supports whose own warrants say DIFFERENCE has no definition.  They
;;; restate, verbatim, `complement-in-membership' and `complement-in-set-closure'
;;; (theory.scm:731,726): DIFFERENCE *is* COMPLEMENT-IN under a second name.
;;; Defining it as such turns both into one-line theorems and takes this proof
;;; to `modulo 0' -- deliberately NOT done here, because DIFFERENCE sits inside
;;; IS-FIELD's own defining IFF and unfolding it perturbs field-is-field-ring,
;;; prod-of-sums and measure.  That is a separate, measured change.
;;;
;;; Technique: zz-ring-is-ring.scm's.  Unfold the definitional IFF, push the
;;; accessors to the surface language with `surface-goal!', split, and close each
;;; conjunct by its own shape.  Thirteen of the seventeen conjuncts are RING's
;;; and go exactly as they do there; the four new ones are the length (8, not 6),
;;; the derived NON-ZERO pair, and the MUL-INV typing above.

;;; --- file-local helpers (qf- prefix) ------------------------------------
;;;
;;; NEVER name one of these like a tactic.  A first cut called the state-dumping
;;; helper `show', which is the display tactic: `have!' then called (show) with
;;; no arguments and the file died with "compound-procedure show has been called
;;; with 0 arguments".  CLAUDE.md's rule, met head-on.

(define (qf-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (qf-head g) (and (pair? g) (car g)))

;;; QQ \ {0}: the NON-ZERO slot, the MUL-INV lambda's domain AND its codomain, so
;;; a typo in any one of the three would be a long hunt.  Written once.
(define qf-nz '(DIFFERENCE QQ (SINGLETON 0)))

;;; The QQ closure axioms, keyed by the surface operation the lambda body applies.
(define qf-closure '((+ . qq-add-closed) (* . qq-mul-closed) (- . qq-neg-closed)))

;;; A genuine open LEAF: ungrounded AND no rule has fired on it.  `proof-open-goals'
;;; also lists ANCESTORS (a node stays ungrounded while any descendant is open), so
;;; searching it for an AND keeps re-splitting the same conjunction forever --
;;; zz-ring-is-ring.scm records that hanging its proof twice, and a probe of this
;;; file reported the ROOT goal as an unrecognised conjunct for the same reason.
(define (qf-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))

;;; Peel a FORALL/IMPLIES prefix, GUARDING ON PROGRESS: `di' only warns when it
;;; cannot decompose, so "loop while the head is FORALL" spins on a no-op.
(define (qf-peel!)
  (let loop ((fuel 20))
    (let ((before (qf-goal)))
      (when (and (> fuel 0) (memq (qf-head before) '(FORALL IMPLIES)))
        (di)
        (if (equal? (qf-goal) before)
            (error "qq-field-is-field: di made no progress on" before)
            (loop (- fuel 1)))))))

;;; -----------------------------------------------------------------------
;;; qq-recip-nonzero -- the half of the MUL-INV typing that QQ does not state.
;;;
;;; `qq-recip-closed' gives recip(a) in QQ.  The codomain is QQ \ {0}, so the
;;; NON-VANISHING is owed too, and nothing in number-systems.scm says it.  It is
;;; one step from `qq-recip-inverse': if recip(a) were 0 then a * 0 = 1, and
;;; a * 0 = 0, so 0 = 1.
;;;
;;; TWO MECHANICS, both of which cost a run.  (1) `qq-recip-inverse' has a
;;; CONJUNCTIVE antecedent, so `fact' lands the IMPLICATION rather than detaching
;;; it -- hence the `have!' of the AND immediately before (CLAUDE.md's rule; the
;;; probe showed the undetached implication sitting in the context).  (2) The
;;; contradiction is NOT reached by rewriting: after `di' on the NOT the goal is
;;; FALSITY, and `subst' is a GOAL-side Leibniz rewrite, so it has nothing to
;;; rewrite and merely warns.  The move is to `have!' the NEGATION of a formula
;;; already in the context and then `ai' it -- NOT-elim -- which is exactly the
;;; shape CLAUDE.md prescribes for every contradiction.  Inside that lane the
;;; goal DOES contain the terms, so `subst' works twice.
;;; -----------------------------------------------------------------------

(sp (make-wff (forall-guarded '(a_) '((IN a_ QQ) (NOT (= a_ 0)))
                '(NOT (= (recip a_) 0)))))
(qf-peel!)                                    ; a_ in QQ, a_ /= 0 assumed
(have! '(AND (IN a_ QQ) (NOT (= a_ 0))) (lambda () (prop)))
(fact 'qq-recip-inverse 'a_)                  ; a_ * recip(a_) = 1
(di)                                          ; assume recip(a_) = 0; goal FALSITY
(have! '(= (* a_ 0) 0)                        ; ring arithmetic, via QQ <= RR
       (lambda () (fact 'qq-subset-rr) (fact 'subset-mem-fwd 'QQ 'RR 'a_) (crs)))
(have! '(NOT (= (* a_ (recip a_)) 1))
       (lambda () (subst '(= (recip a_) 0))   ; goal: not(a_ * 0 = 1)
                  (subst '(= (* a_ 0) 0))     ; goal: not(0 = 1)
                  (arith)))
(ai '(NOT (= (* a_ (recip a_)) 1)))           ; NOT-elim against the positive
(qed 'qq-recip-nonzero)
(topic! 'qq-recip-nonzero 'algebra)

;;; -----------------------------------------------------------------------
;;; qq-field-mul-inv-type -- the MUL-INV slot typing, the one genuinely new
;;; obligation, stated separately because a failure inside the eighteen-conjunct
;;; sweep is far harder to read than a failure here.
;;;
;;; `singleton-membership' reads  x in {y} iff x in SET and x = y  -- a
;;; CONJUNCTION, so its negation does not hand back `x /= 0' directly; the
;;; sethood half has to be supplied (from x in QQ) before `prop' can peel it.
;;; -----------------------------------------------------------------------

(sp (make-wff (list 'IN (list 'VNB-LAMBDA 'x_ qf-nz '(recip x_))
                    (list 'FUN qf-nz qf-nz))))
(let ((opened (dk-opened (lambda () (lam-t)))))
  (if (null? opened) (error "qq-field-is-field: lam-t opened nothing"))
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (let ((g (qf-goal)))
       (cond
         ;; SETHOOD of the domain: QQ \ {0} is a set because QQ is.
         ((equal? g (list 'IN qf-nz 'SET))
          (fact 'qq-is-set) (fact 'difference-set 'QQ '(SINGLETON 0)) (ass))
         ;; POINTWISE: x in QQ\{0}  =>  recip(x) in QQ\{0}.
         ((eq? (qf-head g) 'FORALL)
          (di)
          (let ((x (cadr (cadr (qf-goal)))))   ; eigenvariable, read off the GOAL
            (dk-split! (dk-landed-1 (lambda ()
               (mac-h 'difference-membership (list 'IN x qf-nz)))))
            (mac-h 'singleton-membership (list 'NOT (list 'IN x '(SINGLETON 0))))
            (fact 'membership-implies-sethood x 'QQ)
            (have! (list 'NOT (list '= x 0)) (lambda () (prop)))
            (have! (list 'AND (list 'IN x 'QQ) (list 'NOT (list '= x 0)))
                   (lambda () (prop)))
            (fact 'qq-recip-closed x)                     ; recip(x) in QQ
            (fact 'qq-recip-nonzero x)                    ; recip(x) /= 0
            (fact 'membership-implies-sethood (list 'recip x) 'QQ)
            (mac 'difference-membership)
            (mac 'singleton-membership)
            (prop)))
         (else (error "qq-field-is-field: unexpected lam-t leaf" g)))))
   opened))
(qed 'qq-field-mul-inv-type)
(topic! 'qq-field-mul-inv-type 'plumbing)

;;; -----------------------------------------------------------------------
;;; IS-FIELD(QQ-FIELD) -- eighteen conjuncts.
;;; -----------------------------------------------------------------------

;;; ADD/MUL/NEG typing.  TAKE THE LEAVES `lam-t' OPENED -- never search the open
;;; leaves by shape: the other seventeen conjuncts are still open and several are
;;; `IN' goals (zz-ring-is-ring.scm records a shape search picking up MUL's
;;; typing while closing ADD's, then failing several steps later).
(define (qf-close-op-typing! g)
  (let* ((lam    (cadr g))
         (binder (cadr lam))
         (body   (cadddr lam))
         (thm    (cdr (assq (car body) qf-closure)))
         (tupled? (and (pair? binder) (eq? (car binder) 'LIST)))
         (opened  (dk-opened (lambda () (lam-t)))))
    (define (pick head)
      (let ((hit (filter (lambda (n)
                           (let ((gg (wff-formula (sequent-node-assertion n))))
                             (and (pair? gg) (eq? (car gg) head))))
                         opened)))
        (and (pair? hit) (dk-focus! (car hit)))))
    (if (null? opened) (error "qq-field-is-field: lam-t opened nothing on" g))
    (when (pick 'FORALL)
      (di)
      (let* ((g2 (qf-goal)) (term (cadr g2)) (args (cdr term)))
        (if (pair? (cdr args))
            (begin (dk-have! (list 'AND (list 'IN (car args) 'QQ)
                                     (list 'IN (cadr args) 'QQ)))
                   (fact thm (car args) (cadr args)))
            (fact thm (car args))))
      (ass))
    ;; sethood of the domain -- CONDITIONAL: sequent nodes are hash-consed, so a
    ;; sibling that already posted the identical `CARTESIAN(QQ,QQ) in SET' under
    ;; the identical context leaves lam-t nothing new to open here.  Never assume
    ;; an arity of leaves.
    (when (pick 'IN)
      (fact 'qq-is-set)
      (when tupled?
        (dk-have! '(AND (IN QQ SET) (IN QQ SET)))
        (mac 'cartesian-set-iff))
      (ass))))

;;; Discharge the FOCUSED conjunct.  Every branch is decided by the goal's own
;;; shape; there is no search, and no leaf is left to luck.
(define (qf-close-leaf!)
  (let ((g (qf-goal)))
    (cond
      ;; length(QQ-FIELD) = 8
      ((and (eq? (qf-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac 'qq-field-def) (len-r) (arith))
      ;; (IN 0 QQ) / (IN 1 QQ) -- ground, so `arith' decides them
      ((and (eq? (qf-head g) 'IN) (number? (cadr g)))
       (arith))
      ;; (IN QQ SET)
      ((equal? g '(IN QQ SET))
       (fact 'qq-is-set) (ass))
      ;; the DERIVED carrier's sethood
      ((equal? g (list 'IN qf-nz 'SET))
       (fact 'qq-is-set) (fact 'difference-set 'QQ '(SINGLETON 0)) (ass))
      ;; the DERIVED carrier's defining equation.  `surface-goal!' has already
      ;; reduced both sides to QQ \ {0}, but `=' is PARTIAL, so this is a
      ;; DEFINEDNESS claim and not a syntactic triviality: the sethood facts are
      ;; landed first and then `rfl' fires.
      ((and (eq? (qf-head g) '=) (equal? (cadr g) qf-nz))
       (fact 'qq-is-set) (fact 'difference-set 'QQ '(SINGLETON 0)) (rfl))
      ;; the MUL-INV slot typing -- the lemma above.  Matched on the lambda's
      ;; DOMAIN, which is what distinguishes it from ADD/MUL/NEG.
      ((and (eq? (qf-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA)
            (equal? (caddr (cadr g)) qf-nz))
       (fact 'qq-field-mul-inv-type) (ass))
      ;; the ADD / MUL / NEG slot typings
      ((and (eq? (qf-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
       (qf-close-op-typing! g))
      ;; a law: unfold it, drop to the surface, peel, and let `crs' decide the
      ;; ring identity.  (`di' splits the AND goals of is-identity /
      ;; has-inverses / is-distributive; each half is again a ring identity.)
      ((memq (qf-head g) '(is-associative is-commutative is-identity
                           has-inverses is-distributive))
       (mac (qf-head g))
       (quietly (lambda () (surface-goal! 'QQ-FIELD)))
       (qf-peel!)
       (let close ((fuel 20))
         (let ((g2 (qf-goal)))
           (cond
             ((<= fuel 0) (error "qq-field-is-field: AND split did not terminate"))
             ((eq? (qf-head g2) 'AND)
              (for-each (lambda (k) (dk-focus! k) (close (- fuel 1)))
                        (dk-opened (lambda () (di)))))
             (else (dk-saturate-slot-ops! 'QQ qf-closure) (crs))))))
      (else (error "qq-field-is-field: unexpected conjunct" g)))))

(sp (make-wff '(IS-FIELD QQ-FIELD)))
(mac 'IS-FIELD)                                    ; the definitional IFF
(quietly (lambda () (surface-goal! 'QQ-FIELD)))    ; carr(s) -> QQ, add(s) -> the lambda, ...
;; split the conjunction to leaves
(let split ((fuel 40))
  (let ((andl (find-first (lambda (s)
                            (eq? (qf-head (wff-formula (sequent-node-assertion s))) 'AND))
                          (qf-open))))
    (when andl
      (if (= fuel 0) (error "qq-field-is-field: AND split did not terminate"))
      (dk-focus! andl) (di) (split (- fuel 1)))))
;; close each conjunct.  The sweep INSISTS ON PROGRESS: a leaf that does not
;; close is NAMED, rather than re-focused forever.
(let sweep ((fuel 40))
  (let* ((open (qf-open)) (n (length open)))
    (when (pair? open)
      (if (= fuel 0) (error "qq-field-is-field: sweep out of fuel"))
      (dk-focus! (car open))
      (let ((g (qf-goal)))
        (qf-close-leaf!)
        (if (>= (length (qf-open)) n)
            (error "qq-field-is-field: this conjunct did not close" g)))
      (sweep (- fuel 1)))))

(if (proof-done? *ps*)
    (qed 'qq-field-is-field)                 ; the name the AXIOM had: citations keep working
    (begin
      (display "\n*** qq-field-is-field did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (wff-formula (sequent-node-assertion l))))
                  (newline))
                (qf-open))
      (error "qq-field-is-field: unfinished")))
(topic! 'qq-field-is-field 'algebra)
