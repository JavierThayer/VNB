;;; zz-integral-domain.scm -- IS-COMMUTATIVE-RING(ZZ-RING) and
;;; IS-INTEGRAL-DOMAIN(ZZ-RING), PROVED.
;;;
;;; Both were asserted axioms in numeric-instances.scm, and neither carried a
;;; `warrant!', so both entered every citing bill at `trust: none' -- the
;;; weakest report there is.  `zz-is-integral-domain' was the largest single
;;; remaining source of that tier: seven bills, and it SHADOWED the rest, so
;;; discharging anything else those seven cite moved nothing (proving
;;; integral-domain-cancel-zero the same day left the count unchanged at 19).
;;;
;;; The pattern is zz-ring-is-ring.scm's, one storey up: the IS-X predicate is
;;; an IFF, so unfold it, push the accessors down to the surface language with
;;; `surface-goal!' -- (MUL ZZ-RING) == bintimes, bintimes(x,y) == x * y, both
;;; THEOREMS -- and the conjuncts become ordinary integer arithmetic.  Two of
;;; the four then fall to a decision procedure and one to a citation.
;;;
;;; The fourth is the only real content: ZZ has NO ZERO DIVISORS.  Nothing in
;;; number-systems.scm says so -- there is no ZZ zero-divisor axiom and no sign
;;; or trichotomy machinery for the integers -- so it is proved where the fact
;;; actually comes from, one system up.  QQ is a FIELD: `qq-recip-closed' and
;;; `qq-recip-inverse' give b a multiplicative inverse as soon as b /= 0, and
;;; `zz-subset-qq' (primitive) carries the integers into it.  Then
;;;
;;;     a = a . 1 = a . (b . b^-1) = (a . b) . b^-1 = 0 . b^-1 = 0,
;;;
;;; which is four rewrites.  No induction, no order, no descent: the integers
;;; have no zero divisors because the rationals have inverses.
;;;
;;; Needs: interactive + qed/proof-debt, driver-kit (have!, use-em, dk-focus!),
;;; transport (surface-goal!), crs, and theorem-library/zz-ring-is-ring for
;;; IS-RING(ZZ-RING).  Must precede theorem-library/nn-integral, which
;;; transports integral-domain-cancel-zero through zz-is-integral-domain.

;;; ---- file-local driver helpers (zid- prefix; never named like a tactic) ----
(define (zid-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (zid-head g) (and (pair? g) (car g)))

;;; A genuine open LEAF: ungrounded AND no rule has fired on it.  proof-open-goals
;;; also lists ANCESTORS, so filtering on in-arrows is what stops an AND split
;;; from re-finding the conjunction it just split (the bug that hung
;;; zz-ring-is-ring twice; see its comment).
(define (zid-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))

;;; Split every AND goal down to leaves.  Fuel-bounded: a split that stops
;;; making progress is a bug, not a fixpoint.
(define (zid-split!)
  (let split ((fuel 20))
    (let ((andl (find-first
                 (lambda (s) (eq? (zid-head (wff-formula (sequent-node-assertion s))) 'AND))
                 (zid-open))))
      (when andl
        (if (= fuel 0) (error "zz-integral-domain: AND split did not terminate"))
        (dk-focus! andl) (di) (split (- fuel 1))))))

;;; Peel the leading FORALL/IMPLIES prefix.  GUARDED ON PROGRESS -- `di' only
;;; WARNS when it cannot decompose, so "loop while the head is FORALL/IMPLIES"
;;; spins forever the moment it no-ops.
(define (zid-peel!)
  (let peel ((fuel 12))
    (let ((before (zid-goal)))
      (when (and (> fuel 0) (memq (zid-head before) '(FORALL IMPLIES)))
        (di)
        (if (equal? (zid-goal) before)
            (error "zz-integral-domain: di made no progress on" before)
            (peel (- fuel 1)))))))

(define (zid-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** zz-integral-domain: ") (display name)
        (display " did NOT close.  Open leaves:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (sequent-node-assertion l)))
                    (newline))
                  (proof-leaves))
        (error "zz-integral-domain: unfinished" name))))

;;; =======================================================================
;;; zz-is-commutative-ring : IS-COMMUTATIVE-RING(ZZ-RING).
;;;
;;; is-commutative-ring-def is IS-RING plus commutativity of MUL.  The first is
;;; the theorem next door; the second, at the surface, is a . b = b . a on the
;;; integers, which is a commutative-ring identity over typed generators and so
;;; is exactly what `crs' decides.
(sp (make-wff '(IS-COMMUTATIVE-RING ZZ-RING)))
(mac 'is-commutative-ring-def)
(quietly (lambda () (surface-goal! 'ZZ-RING)))
(zid-split!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (equal? (zid-goal) '(IS-RING ZZ-RING))
       (begin (fact 'zz-is-ring) (ass))
       (begin (zid-peel!) (crs))))
 (zid-open))
(zid-qed! 'zz-is-commutative-ring)

;;; =======================================================================
;;; zz-no-zero-divisors : the content, stated at the surface.
;;;
;;;   forall a, b in ZZ.  a . b = 0  =>  a = 0 or b = 0
;;;
;;; Proved through QQ, as the header explains.  Split on b = 0 by `use-em'
;;; (classical, debt-free: the exhaustiveness obligation is closed by driver-kit
;;; itself).  On b /= 0 the inverse exists and four rewrites finish it.
(sp (make-wff '(FORALL a (IMPLIES (IN a ZZ)
                 (FORALL b (IMPLIES (IN b ZZ)
                   (IMPLIES (= (* a b) 0)
                     (OR (= a 0) (= b 0)))))))))
(zid-peel!)
(fact 'zz-subset-qq 'a)                       ; a in QQ
(fact 'zz-subset-qq 'b)                       ; b in QQ
(use-em '(= b 0)
  ;; b = 0: the right disjunct is the hypothesis.
  (lambda () (oi-r) (ass))
  ;; b /= 0: b is invertible in QQ, so a is 0.
  (lambda ()
    (oi-l)
    ;; qq-recip-closed / -inverse / -mul-assoc all guard on a CONJUNCTION, which
    ;; `fact' will not split -- hence the have! before each (CLAUDE.md).
    (have! '(AND (IN b QQ) (NOT (= b 0))))
    (fact 'qq-recip-closed 'b)                ; recip(b) in QQ
    (fact 'qq-recip-inverse 'b)               ; b . recip(b) = 1
    (have! '(AND (IN a QQ) (AND (IN b QQ) (IN (recip b) QQ))))
    (fact 'qq-mul-assoc 'a 'b '(recip b))     ; (a.b).recip(b) = a.(b.recip(b))
    ;; (a.b).recip(b) = a  -- reassociate, cancel, drop the unit.
    (have! '(= (* (* a b) (recip b)) a)
           (lambda ()
             (subst '(= (* (* a b) (recip b)) (* a (* b (recip b)))))
             (subst '(= (* b (recip b)) 1))
             (crs)))                          ; a . 1 = a
    ;; ... so the goal a = 0 becomes (a.b).recip(b) = 0, and a.b IS 0.
    (subst '(= a (* (* a b) (recip b))))
    (subst '(= (* a b) 0))
    (crs)))                                   ; 0 . recip(b) = 0
(zid-qed! 'zz-no-zero-divisors)
(topic! 'zz-no-zero-divisors 'algebra)

;;; =======================================================================
;;; zz-is-integral-domain : IS-INTEGRAL-DOMAIN(ZZ-RING).
;;;
;;; Three conjuncts, one line each: the commutative ring above, 1 /= 0 (ground,
;;; so `arith' decides it), and no zero divisors, which after surface-goal! is
;;; literally zz-no-zero-divisors.
(sp (make-wff '(IS-INTEGRAL-DOMAIN ZZ-RING)))
(mac 'is-integral-domain-def)
(quietly (lambda () (surface-goal! 'ZZ-RING)))
(zid-split!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (let ((g (zid-goal)))
     (cond ((equal? g '(IS-COMMUTATIVE-RING ZZ-RING))
            (fact 'zz-is-commutative-ring) (ass))
           ((eq? (zid-head g) 'NOT) (arith))
           (else (fact 'zz-no-zero-divisors) (ass)))))
 (zid-open))
(zid-qed! 'zz-is-integral-domain)
