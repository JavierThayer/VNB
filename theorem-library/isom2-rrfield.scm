;;; isom2-rrfield.scm -- IS-FIELD(RR-FIELD) and the field ring of the reals: the
;;; scalars of the real vector spaces of isom2-rrvs.scm.  Agent ISOM, 2026-10-26.
;;; The proof is theorem-library/qq-field-is-field.scm (QQ-FIELD) with QQ replaced by RR
;;; and the qq- closure laws by their rr- twins; nothing else changes.
;;;
;;;   rr-recip-nonzero, rr-field-mul-inv-type, rr-field-is-field, rr-field-is-field-ring
;;;
;;; WINDOW.  As qq-field-is-field (after interactive and field-ring-view; difference-laws),
;;; after isom2-rrvs-vocab.scm.  Library: analysis (algebra would do; the vocabulary file
;;; carries RR-FN-SPACE, used only by the calculus statement).
;;;
;;; Helper prefix: rfd-.

;;; FIELD declaration (field.scm).  They were separate ASSERTED axioms with no
;;; warrant -- `field-zero-not-one' and `field-mul-inverse', two of the three
;;; remaining `trust: none' bills -- i.e. supports finishing a definition,
;;; exactly as `field-non-zero-carrier' was until 2026-07-12.  The slot
;;; `(op MUL-INV NON-ZERO NON-ZERO)' TYPED the inverse and never said it
;;; inverted anything.  So this proof has two more conjuncts to discharge, and
;;; both are new content rather than plumbing: nontriviality is `not(0 = 1)' in
;;; RR, and invertibility is `rr-recip-inverse' reached through two betas.
;;;
;;; Technique: zz-ring-is-ring.scm's.  Unfold the definitional IFF, push the
;;; accessors to the surface language with `surface-goal!', split, and close each
;;; conjunct by its own shape.  Thirteen of the nineteen conjuncts are RING's
;;; and go exactly as they do there; the six others are the length (8, not 6),
;;; the derived NON-ZERO pair, the MUL-INV typing above, and the two laws.

;;; --- file-local helpers (rfd- prefix) ------------------------------------
;;;
;;; NEVER name one of these like a tactic.  A first cut called the state-dumping
;;; helper `show', which is the display tactic: `have!' then called (show) with
;;; no arguments and the file died with "compound-procedure show has been called
;;; with 0 arguments".  CLAUDE.md's rule, met head-on.

(define (rfd-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (rfd-head g) (and (pair? g) (car g)))

;;; RR \ {0}: the NON-ZERO slot, the MUL-INV lambda's domain AND its codomain, so
;;; a typo in any one of the three would be a long hunt.  Written once.
(define rfd-nz '(DIFFERENCE RR (SINGLETON 0)))

;;; The RR closure axioms, keyed by the surface operation the lambda body applies.
(define rfd-closure '((+ . rr-add-closed) (* . rr-mul-closed) (- . rr-neg-closed)))

;;; A genuine open LEAF: ungrounded AND no rule has fired on it.  `proof-open-goals'
;;; also lists ANCESTORS (a node stays ungrounded while any descendant is open), so
;;; searching it for an AND keeps re-splitting the same conjunction forever --
;;; zz-ring-is-ring.scm records that hanging its proof twice, and a probe of this
;;; file reported the ROOT goal as an unrecognised conjunct for the same reason.
(define (rfd-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))

;;; Peel a FORALL/IMPLIES prefix, GUARDING ON PROGRESS: `di' only warns when it
;;; cannot decompose, so "loop while the head is FORALL" spins on a no-op.
(define (rfd-peel!)
  (let loop ((fuel 20))
    (let ((before (rfd-goal)))
      (when (and (> fuel 0) (memq (rfd-head before) '(FORALL IMPLIES)))
        (di)
        (if (equal? (rfd-goal) before)
            (error "rr-field-is-field: di made no progress on" before)
            (loop (- fuel 1)))))))

;;; -----------------------------------------------------------------------
;;; rr-recip-nonzero -- the half of the MUL-INV typing that RR does not state.
;;;
;;; `rr-recip-closed' gives recip(a) in RR.  The codomain is RR \ {0}, so the
;;; NON-VANISHING is owed too, and nothing in number-systems.scm says it.  It is
;;; one step from `rr-recip-inverse': if recip(a) were 0 then a * 0 = 1, and
;;; a * 0 = 0, so 0 = 1.
;;;
;;; TWO MECHANICS, both of which cost a run.  (1) `rr-recip-inverse' has a
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

(sp (make-wff (forall-guarded '(a_) '((IN a_ RR) (NOT (= a_ 0)))
                '(NOT (= (recip a_) 0)))))
(rfd-peel!)                                    ; a_ in RR, a_ /= 0 assumed
(have! '(AND (IN a_ RR) (NOT (= a_ 0))) (lambda () (prop)))
(fact 'rr-recip-inverse 'a_)                  ; a_ * recip(a_) = 1
(di)                                          ; assume recip(a_) = 0; goal FALSITY
(have! '(= (* a_ 0) 0)                        ; ring arithmetic, via RR <= RR
       (lambda () (crs)))
(have! '(NOT (= (* a_ (recip a_)) 1))
       (lambda () (subst '(= (recip a_) 0))   ; goal: not(a_ * 0 = 1)
                  (subst '(= (* a_ 0) 0))     ; goal: not(0 = 1)
                  (arith)))
(ai '(NOT (= (* a_ (recip a_)) 1)))           ; NOT-elim against the positive
(qed 'rr-recip-nonzero)
(topic! 'rr-recip-nonzero 'algebra)

;;; -----------------------------------------------------------------------
;;; rr-field-mul-inv-type -- the MUL-INV slot typing, the one genuinely new
;;; obligation, stated separately because a failure inside the twenty-conjunct
;;; sweep is far harder to read than a failure here.
;;;
;;; `singleton-membership' reads  x in {y} iff x in SET and x = y  -- a
;;; CONJUNCTION, so its negation does not hand back `x /= 0' directly; the
;;; sethood half has to be supplied (from x in RR) before `prop' can peel it.
;;; -----------------------------------------------------------------------

(sp (make-wff (list 'IN (list 'VNB-LAMBDA 'x_ rfd-nz '(recip x_))
                    (list 'FUN rfd-nz rfd-nz))))
(let ((opened (dk-opened (lambda () (lam-t)))))
  (if (null? opened) (error "rr-field-is-field: lam-t opened nothing"))
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (let ((g (rfd-goal)))
       (cond
         ;; SETHOOD of the domain: RR \ {0} is a set because RR is.
         ((equal? g (list 'IN rfd-nz 'SET))
          (fact 'rr-is-set) (fact 'difference-set 'RR '(SINGLETON 0)) (ass))
         ;; POINTWISE: x in RR\{0}  =>  recip(x) in RR\{0}.
         ((eq? (rfd-head g) 'FORALL)
          (di)
          (let ((x (cadr (cadr (rfd-goal)))))   ; eigenvariable, read off the GOAL
            (dk-split! (dk-landed-1 (lambda ()
               (mac-h 'difference-membership (list 'IN x rfd-nz)))))
            (mac-h 'singleton-membership (list 'NOT (list 'IN x '(SINGLETON 0))))
            (fact 'membership-implies-sethood x 'RR)
            (have! (list 'NOT (list '= x 0)) (lambda () (prop)))
            (have! (list 'AND (list 'IN x 'RR) (list 'NOT (list '= x 0)))
                   (lambda () (prop)))
            (fact 'rr-recip-closed x)                     ; recip(x) in RR
            (fact 'rr-recip-nonzero x)                    ; recip(x) /= 0
            (fact 'membership-implies-sethood (list 'recip x) 'RR)
            (mac 'difference-membership)
            (mac 'singleton-membership)
            (prop)))
         (else (error "rr-field-is-field: unexpected lam-t leaf" g)))))
   opened))
(qed 'rr-field-mul-inv-type)
(topic! 'rr-field-mul-inv-type 'plumbing)

;;; -----------------------------------------------------------------------
;;; IS-FIELD(RR-FIELD) -- twenty conjuncts.
;;; -----------------------------------------------------------------------

;;; ADD/MUL/NEG typing.  TAKE THE LEAVES `lam-t' OPENED -- never search the open
;;; leaves by shape: the other seventeen conjuncts are still open and several are
;;; `IN' goals (zz-ring-is-ring.scm records a shape search picking up MUL's
;;; typing while closing ADD's, then failing several steps later).
(define (rfd-close-op-typing! g)
  (let* ((lam    (cadr g))
         (binder (cadr lam))
         (body   (cadddr lam))
         (thm    (cdr (assq (car body) rfd-closure)))
         (tupled? (and (pair? binder) (eq? (car binder) 'LIST)))
         (opened  (dk-opened (lambda () (lam-t)))))
    (define (pick head)
      (let ((hit (filter (lambda (n)
                           (let ((gg (wff-formula (sequent-node-assertion n))))
                             (and (pair? gg) (eq? (car gg) head))))
                         opened)))
        (and (pair? hit) (dk-focus! (car hit)))))
    (if (null? opened) (error "rr-field-is-field: lam-t opened nothing on" g))
    (when (pick 'FORALL)
      (di)
      (let* ((g2 (rfd-goal)) (term (cadr g2)) (args (cdr term)))
        (if (pair? (cdr args))
            (begin (dk-have! (list 'AND (list 'IN (car args) 'RR)
                                     (list 'IN (cadr args) 'RR)))
                   (fact thm (car args) (cadr args)))
            (fact thm (car args))))
      (ass))
    ;; sethood of the domain -- CONDITIONAL: sequent nodes are hash-consed, so a
    ;; sibling that already posted the identical `CARTESIAN(RR,RR) in SET' under
    ;; the identical context leaves lam-t nothing new to open here.  Never assume
    ;; an arity of leaves.
    (when (pick 'IN)
      (fact 'rr-is-set)
      (when tupled?
        (dk-have! '(AND (IN RR SET) (IN RR SET)))
        (mac 'cartesian-set-iff))
      (ass))))

;;; The INVERTIBILITY law conjunct (field.scm's second (law ...) clause).  Surfaced
;;; at RR-FIELD it reads
;;;
;;;   forall([a_ in difference(qq, singleton(0))],
;;;     (vnb-lambda([x_,y_], cartesian(qq,qq), x_ * y_))(
;;;        a_, (vnb-lambda(x_, difference(qq, singleton(0)), recip(x_)))(a_)) = 1)
;;;
;;; -- TWO redexes, the MUL slot's tupled lambda and the MUL-INV slot's unary one.
;;; ONE `lam-b' reduces both and owes NOTHING, but only because every typing it
;;; needs is landed first.  Two traps, each measured on the band:
;;;
;;;   * `mac-h difference-membership' REPLACES the hypothesis `a_ in RR \ {0}',
;;;     and that membership is exactly what licenses the INNER beta.  Unfolded,
;;;     the reduction owes `a_ in difference(qq, singleton(0))' back at a node
;;;     whose context no longer holds it -- an open leaf `ass' cannot close, and
;;;     nothing says so until qed.  Read the two pieces FORWARD with `fact' and
;;;     leave the membership standing.  (The MUL-INV typing lemma above CAN use
;;;     `mac-h': it betas nothing.)
;;;   * PEEL AND TYPE FIRST, THEN BETA (CLAUDE.md).  With `recip(a_) in RR'
;;;     missing, the OUTER tupled redex owes `[a_, recip(a_)] in cartesian(RR,RR)'
;;;     as a second leaf.  With it in context the walker discharges that itself.
(define (rfd-close-inverse-law!)
  (di)                                          ; assume a_ in RR \ {0}
  (let ((a (cadr (cadr (rfd-goal)))))            ; eigenvariable, read off the GOAL
    (fact 'difference-membership 'RR '(SINGLETON 0) a)
    (have! (list 'IN a 'RR) (lambda () (prop)))
    (fact 'membership-implies-sethood a 'RR)    ; the sethood half of singleton
    (fact 'singleton-membership 0 a)
    (have! (list 'NOT (list '= a 0)) (lambda () (prop)))
    (have! (list 'AND (list 'IN a 'RR) (list 'NOT (list '= a 0)))
           (lambda () (prop)))
    (fact 'rr-recip-closed a)                   ; recip(a_) in RR
    (fact 'rr-recip-inverse a)                  ; a_ * recip(a_) = 1
    ;; whatever lam-b opens: the reduced equation closes by `ass', and a domain
    ;; obligation (if the walker ever posts one) is in context by construction.
    (for-each (lambda (n) (dk-focus! n) (ass))
              (dk-opened (lambda () (lam-b))))))

;;; Discharge the FOCUSED conjunct.  Every branch is decided by the goal's own
;;; shape; there is no search, and no leaf is left to luck.
(define (rfd-close-leaf!)
  (let ((g (rfd-goal)))
    (cond
      ;; length(RR-FIELD) = 8
      ((and (eq? (rfd-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
       (mac 'rr-field-def) (len-r) (arith))
      ;; (IN 0 RR) / (IN 1 RR) -- ground, so `arith' decides them
      ((and (eq? (rfd-head g) 'IN) (number? (cadr g)))
       (arith))
      ;; (IN RR SET)
      ((equal? g '(IN RR SET))
       (fact 'rr-is-set) (ass))
      ;; the DERIVED carrier's sethood
      ((equal? g (list 'IN rfd-nz 'SET))
       (fact 'rr-is-set) (fact 'difference-set 'RR '(SINGLETON 0)) (ass))
      ;; the DERIVED carrier's defining equation.  `surface-goal!' has already
      ;; reduced both sides to RR \ {0}, but `=' is PARTIAL, so this is a
      ;; DEFINEDNESS claim and not a syntactic triviality: the sethood facts are
      ;; landed first and then `rfl' fires.
      ((and (eq? (rfd-head g) '=) (equal? (cadr g) rfd-nz))
       (fact 'rr-is-set) (fact 'difference-set 'RR '(SINGLETON 0)) (rfl))
      ;; the MUL-INV slot typing -- the lemma above.  Matched on the lambda's
      ;; DOMAIN, which is what distinguishes it from ADD/MUL/NEG.
      ((and (eq? (rfd-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA)
            (equal? (caddr (cadr g)) rfd-nz))
       (fact 'rr-field-mul-inv-type) (ass))
      ;; the ADD / MUL / NEG slot typings
      ((and (eq? (rfd-head g) 'IN)
            (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA))
       (rfd-close-op-typing! g))
      ;; NONTRIVIALITY, the first of the two (law ...) conjuncts: surfaced it is
      ;; the ground `not(0 = 1)', which `arith' decides.
      ((equal? g '(NOT (= 0 1)))
       (arith))
      ;; INVERTIBILITY, the second.  It is the only FORALL conjunct: the
      ;; operation-property conjuncts are still folded (is-associative(...) and
      ;; friends are ATOMS until `mac' opens them) and every other conjunct is an
      ;; IN, an = or a NOT.
      ((eq? (rfd-head g) 'FORALL)
       (rfd-close-inverse-law!))
      ;; a law: unfold it, drop to the surface, peel, and let `crs' decide the
      ;; ring identity.  (`di' splits the AND goals of is-identity /
      ;; has-inverses / is-distributive; each half is again a ring identity.)
      ((memq (rfd-head g) '(is-associative is-commutative is-identity
                           has-inverses is-distributive))
       (mac (rfd-head g))
       (quietly (lambda () (surface-goal! 'RR-FIELD)))
       (rfd-peel!)
       (let close ((fuel 20))
         (let ((g2 (rfd-goal)))
           (cond
             ((<= fuel 0) (error "rr-field-is-field: AND split did not terminate"))
             ((eq? (rfd-head g2) 'AND)
              (for-each (lambda (k) (dk-focus! k) (close (- fuel 1)))
                        (dk-opened (lambda () (di)))))
             (else (dk-saturate-slot-ops! 'RR rfd-closure) (crs))))))
      (else (error "rr-field-is-field: unexpected conjunct" g)))))

(sp (make-wff '(IS-FIELD RR-FIELD)))
(mac 'IS-FIELD)                                    ; the definitional IFF
(quietly (lambda () (surface-goal! 'RR-FIELD)))    ; carr(s) -> RR, add(s) -> the lambda, ...
;; split the conjunction to leaves
(let split ((fuel 40))
  (let ((andl (find-first (lambda (s)
                            (eq? (rfd-head (wff-formula (sequent-node-assertion s))) 'AND))
                          (rfd-open))))
    (when andl
      (if (= fuel 0) (error "rr-field-is-field: AND split did not terminate"))
      (dk-focus! andl) (di) (split (- fuel 1)))))
;; close each conjunct.  The sweep INSISTS ON PROGRESS: a leaf that does not
;; close is NAMED, rather than re-focused forever.
(let sweep ((fuel 40))
  (let* ((open (rfd-open)) (n (length open)))
    (when (pair? open)
      (if (= fuel 0) (error "rr-field-is-field: sweep out of fuel"))
      (dk-focus! (car open))
      (let ((g (rfd-goal)))
        (rfd-close-leaf!)
        (if (>= (length (rfd-open)) n)
            (error "rr-field-is-field: this conjunct did not close" g)))
      (sweep (- fuel 1)))))

(if (proof-done? *ps*)
    (qed 'rr-field-is-field)                 ; the name the AXIOM had: citations keep working
    (begin
      (display "\n*** rr-field-is-field did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (wff-formula (sequent-node-assertion l))))
                  (newline))
                (rfd-open))
      (error "rr-field-is-field: unfinished")))
(topic! 'rr-field-is-field 'algebra)


(sp (make-wff '(IS-FIELD-RING (FIELD-AS-INTEGRAL-DOMAIN RR-FIELD))))
(fact 'rr-field-is-field)
(dk-close-if! (lambda () (fact 'field-is-field-ring 'RR-FIELD)) ass)
(qed 'rr-field-is-field-ring)
(topic! 'rr-field-is-field-ring 'algebra)
