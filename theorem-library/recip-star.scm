;;; recip-star.scm -- THE TOTALISED RECIPROCAL, and the reason it exists.
;;;
;;;     RECIP-STAR(u_)  ==  IF u_ = 0 THEN 0 ELSE recip(u_)
;;;
;;; WHY.  `recip' is PARTIAL: rr-recip-closed and rr-recip-inverse
;;; (number-systems.scm) are both guarded on `a /= 0', and there is no
;;; `recip 0' convention.  So (VNB-LAMBDA z_ RR (recip z_)) is NOT a member of
;;; FUN(RR,RR) -- `lam-t' would owe (IN (recip 0) RR), which is false -- and the
;;; INTEGRAND of the logarithm,
;;;
;;;     log(x)  =  C-INT(recip, 1, x),
;;;
;;; is therefore not a term this vocabulary can write down at all:
;;; IS-ANTIDERIVATIVE(f, phi, a, b) (theorem-library/antiderivative.scm)
;;; demands phi in FUN(RR,RR), a GLOBAL function.  continuity-recip.scm's own
;;; header names the fix -- "a conditional total extension
;;; (VNB-LAMBDA x RR (IF (= x 0) 0 (recip x))) ... would give the bare-map
;;; reading, at the cost of a case split at every use" -- and this file is that
;;; extension, with the case split paid ONCE, here.
;;;
;;; THE PRECEDENT is SEQ-LIMIT (theorem-library/seq-limit.scm), totalised by an
;;; IF for exactly this reason: a `lam-t' body obligation ranges over the WHOLE
;;; domain, so the typing lemma has to be UNCONDITIONAL, and a partial
;;; description cannot make it so.  Its packaging discipline is copied too.
;;; The five read-offs below are the entire interface:
;;;
;;;   recip-star-in-rr        u_ in RR  =>  RECIP-STAR(u_) in RR
;;;   recip-star-lam-in-fun   z_ |-> RECIP-STAR(z_)  in FUN(RR,RR)   [no hypothesis]
;;;   recip-star-value        u_ /= 0   =>  RECIP-STAR(u_) = recip(u_)
;;;   recip-star-zero         RECIP-STAR(0) = 0
;;;   recip-star-inverse      u_ /= 0   =>  u_ * RECIP-STAR(u_) = 1
;;;
;;; with two more once continuity is in hand:
;;;
;;;   recip-star-continuous-at         c /= 0 => the map is continuous at c
;;;   recip-star-continuous-on-ccint   0 < a, x_ in [a,b] => continuous at x_
;;;
;;; and NOTHING downstream should ever unfold the functoid.  `recip-star-value'
;;; is the citation an `rr-recip-closed' site wants; `recip-star-inverse' is the
;;; one an `rr-recip-inverse' site wants.  `mac recip-star' occurs THREE times
;;; in this file (recip-star-in-rr, recip-star-value, recip-star-zero) and
;;; should occur nowhere else in the tree; every later proof here, including
;;; both continuity theorems, goes through the read-offs like any other citer.
;;;
;;; THE CONVENTION AT 0 is 0.  It is the one that makes `recip-star-zero' a
;;; one-liner and it is what continuity-recip.scm's header proposed; nothing
;;; below depends on the choice except that lemma.  It also makes the identity
;;; recip-star(recip-star(u)) = u hold at 0, which the alternative 1 would not.
;;;
;;; CONTINUITY AWAY FROM ZERO, and the two transfers it costs.  The tree's
;;; reciprocal-continuity theorem, `recip-continuous-at'
;;; (theorem-library/continuity-recip.scm, `modulo 0'), concludes about the
;;; COMPOSITE x |-> recip(h(x)) for a NOWHERE-ZERO h -- deliberately, because
;;; the bare map was not statable.  The totalised map cannot be reached from it
;;; by the GLOBAL transfer `cont-transfer-ptwise-eq': no nowhere-zero h has
;;; recip(h(0)) = 0, since h(0)*recip(h(0)) = 1 while h(0)*0 = 0.  The
;;; agreement is only LOCAL, so the tool is `continuous-at-local'
;;; (theorem-library/continuity-local.scm, `modulo 0'), and it is used TWICE:
;;;
;;;   NZ-IDENT  =  w_ |-> IF w_ = 0 THEN 1 ELSE w_
;;;
;;; is the identity made nowhere zero.  It agrees with the identity on the ball
;;; of radius m about c whenever m + m = |c| (that is `rr-half-ball-nonzero'
;;; below), so it is continuous at every c /= 0 -- transfer ONE, off
;;; `identity-continuous-at'.  Then `recip-continuous-at' at h := NZ-IDENT makes
;;; x |-> recip(NZ-IDENT(x)) continuous at c, and THAT map agrees with the
;;; totalised reciprocal on the same ball -- transfer TWO.  Both transfers use
;;; the same radius and the same nonvanishing lemma, which is why the lemma is
;;; stated separately.
;;;
;;; `rr-half-ball-nonzero' is the only arithmetic in the file: |c| - |y| <=
;;; ||c|-|y|| <= |c-y| = |y-c| <= m and |c| = m+m give m <= |y|, so |y| > 0 and
;;; y /= 0.  One `ineq' over abs-atoms, then the modus tollens through
;;; `rr-abs-zero' done by hand -- `prop' sees 32 atoms in that context and
;;; declines, which is the correct answer from a tactic whose atoms are opaque.
;;;
;;; WHAT IT COSTS: every theorem here is `modulo 0'.
;;;
;;; AND THE POINT OF IT ALL.  Def 4.6 (IS-ANTIDERIVATIVE, antiderivative.scm)
;;; demands `phi in FUN(RR,RR)' of the INTEGRAND.  With recip-star-lam-in-fun
;;; and recip-star-continuous-on-ccint that conjunct and the continuity of the
;;; integrand on [a,b] (0 < a) are one citation each, so
;;;
;;;     log(x)  =  C-INT(z_ |-> RECIP-STAR(z_), 1, x)
;;;
;;; is a statement the vocabulary can now make.  Nothing here proves anything
;;; about log; it makes writing it down legal.
;;;
;;; Loads after continuity-local (continuous-at-local), continuity-recip
;;; (recip-continuous-at, recip-lam-in-fun), continuity-basics
;;; (identity-continuous-at, ident-lam-in-fun), rr-abs-basics, rr-order-basics,
;;; rr-halving (rr-pos-halvable) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `rs-' prefix) ---------------------

(define (rs-check name)
  (if (not (proof-done? *ps*))
      (error "recip-star: proof did not close" name
             (expression->string (dk-goal)))))

;;; `di' until the goal's head is HEAD.  `di' is greedy and would swallow a
;;; NOT goal (assuming it, goal FALSITY), so peeling is never by a count.
(define (rs-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 20) (error "rs-peel-to!: never reached" head
                           (expression->string (dk-goal))))
          (else (di) (loop (+ n 1))))))

;;; Name an `ineq' premise by its FORMULA, never by a position: a miss ERRORS.
;;; (`contra--usable-indices' would do the selecting, but contra.scm loads long
;;; after theorem-library/ and is not in scope here.)
(define (rs-idx f)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rs-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (else (lp (cdr l) (+ i 1))))))
(define (rs-ineq . fs) (apply ineq (map rs-idx fs)))

;;; `ai' every conjunction in the context to exhaustion.  Tolerant where
;;; `dk-split!' is not: `obtain' may or may not have split what it landed, and
;;; `dk-split!' on an already-split conjunction errors rather than no-opping.
(define (rs-split!)
  (let loop ((b 40))
    (if (> b 0)
        (let ((t (let scan ((as (dk-asms)))
                   (cond ((null? as) #f)
                         ((and (pair? (car as)) (eq? (caar as) 'AND)) (car as))
                         (else (scan (cdr as)))))))
          (if t (begin (ai t) (loop (- b 1))))))))

;;; Reduce every VNB-LAMBDA redex in the goal.  Every argument below is typed
;;; in RR before this runs, which is what `lam-b' needs; without the typing it
;;; fires anyway and owes a leaf nothing can close.
(define (rs-redex? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (rs-redex? (car g)) (rs-redex? (cdr g))))
        (else #f)))
(define (rs-beta!)
  (let loop ((n 8))
    (if (and (> n 0) (rs-redex? (dk-goal)))
        (let ((b (dk-goal))) (lam-b) (if (equal? (dk-goal) b) #t (loop (- n 1))))
        #t)))

;;; The two terms.
(define RS-LAM '(VNB-LAMBDA z_ RR (RECIP-STAR z_)))
(define RS-NZI '(VNB-LAMBDA w_ RR (IF (= w_ 0) 1 w_)))
(define RS-GLAM (list 'VNB-LAMBDA 'x 'RR (list 'recip (list RS-NZI 'x))))
(define (rs-if v)  (list 'IF (list '= v 0) 0 (list 'recip v)))
(define (rs-nzif v) (list 'IF (list '= v 0) 1 v))

;;; =====================================================================
;;; 0.  THE DEFINITION.
;;; =====================================================================

(def-functoid 'RECIP-STAR '(u_) '(IF (= u_ 0) 0 (recip u_)))
(notation! 'RECIP-STAR 'kind 'functoid 'arity 1
           'english "the totalised reciprocal of $1"
           'noun "totalised reciprocal of $1"
           'tex "{$1}^{\\ast\\!-1}")

;;; =====================================================================
;;; 1.  recip-star-in-rr -- the value is always real.  Guarded on (IN u_ RR)
;;; only because recip of a non-real is not claimed to be real; the LAMBDA
;;; typing below, which is what matters, has no hypothesis at all.
;;; =====================================================================

(sp (make-wff '(FORALL u_ (IMPLIES (IN u_ RR) (IN (RECIP-STAR u_) RR)))))
(quietly (lambda ()
  (di)
  (mac 'recip-star)
  (use-em '(= u_ 0)
    (lambda ()
      (for-each (lambda (l)
                  (dk-focus! l)
                  (if (eq? (car (dk-goal)) '=)
                      (ass)
                      (begin (subst (list '= (rs-if 'u_) 0)) (fact 'rr-zero-in) (ass))))
                (dk-opened (lambda () (if-true (rs-if 'u_))))))
    (lambda ()
      (for-each (lambda (l)
                  (dk-focus! l)
                  (if (eq? (car (dk-goal)) 'NOT)
                      (ass)
                      (begin (subst (list '= (rs-if 'u_) '(recip u_)))
                             (have! '(AND (IN u_ RR) (NOT (= u_ 0))))
                             (fact 'rr-recip-closed 'u_)
                             (ass))))
                (dk-opened (lambda () (if-false (rs-if 'u_)))))))))
(rs-check 'recip-star-in-rr)
(qed 'recip-star-in-rr)
(topic! 'recip-star-in-rr 'analysis)
(alias! 'recip-star-in-rr "the totalised reciprocal of a real is a real")

;;; =====================================================================
;;; 2.  recip-star-lam-in-fun -- UNCONDITIONAL.  This is the whole point of
;;; the file: the bare map z_ |-> recip(z_) is not a member of FUN(RR,RR),
;;; and the totalised one is, with no hypothesis to discharge at a use site.
;;; =====================================================================

(sp (make-wff (list 'IN RS-LAM '(FUN RR RR))))
(quietly (lambda ()
  (for-each (lambda (leaf)
              (dk-focus! leaf)
              (if (eq? (car (dk-goal)) 'FORALL)
                  (let ((v (cadr (car (dk-landed (lambda () (di)))))))
                    (fact 'recip-star-in-rr v)
                    (ass))
                  (begin (fact 'rr-is-set) (ass))))
            (dk-opened (lambda () (lam-t))))))
(rs-check 'recip-star-lam-in-fun)
(qed 'recip-star-lam-in-fun)
(topic! 'recip-star-lam-in-fun 'analysis)
(alias! 'recip-star-lam-in-fun
        "the totalised reciprocal is a function from the reals to the reals")

;;; =====================================================================
;;; 3.  recip-star-value -- away from 0 it IS the reciprocal.  The goal after
;;; the unfold IS the equation `if-false' hands over, so there is no rewrite.
;;; =====================================================================

(sp (make-wff '(FORALL u_ (IMPLIES (IN u_ RR)
                  (IMPLIES (NOT (= u_ 0)) (= (RECIP-STAR u_) (recip u_)))))))
(quietly (lambda ()
  (di) (di)
  (mac 'recip-star)
  (for-each (lambda (l) (dk-focus! l) (ass))
            (dk-opened (lambda () (if-false (rs-if 'u_)))))))
(rs-check 'recip-star-value)
(qed 'recip-star-value)
(topic! 'recip-star-value 'analysis)
(alias! 'recip-star-value "away from zero the totalised reciprocal is the reciprocal")

;;; =====================================================================
;;; 4.  recip-star-zero -- the convention, stated so that no citer has to look
;;; at the IF to find out what it is.
;;; =====================================================================

(sp (make-wff '(= (RECIP-STAR 0) 0)))
(quietly (lambda ()
  (mac 'recip-star)
  (for-each (lambda (l)
              (dk-focus! l)
              (if (equal? (dk-goal) '(= 0 0)) (rfl) (ass)))
            (dk-opened (lambda () (if-true (rs-if 0)))))))
(rs-check 'recip-star-zero)
(qed 'recip-star-zero)
(topic! 'recip-star-zero 'analysis)
(alias! 'recip-star-zero "the totalised reciprocal of zero is zero")

;;; =====================================================================
;;; 5.  recip-star-inverse -- the form an `rr-recip-inverse' citer wants.
;;; =====================================================================

(sp (make-wff '(FORALL u_ (IMPLIES (IN u_ RR)
                  (IMPLIES (NOT (= u_ 0)) (= (* u_ (RECIP-STAR u_)) 1))))))
(quietly (lambda ()
  (di) (di)
  (fact 'recip-star-value 'u_)
  (subst '(= (RECIP-STAR u_) (recip u_)))
  (have! '(AND (IN u_ RR) (NOT (= u_ 0))))
  (fact 'rr-recip-inverse 'u_)
  (ass)))
(rs-check 'recip-star-inverse)
(qed 'recip-star-inverse)
(topic! 'recip-star-inverse 'analysis)
(alias! 'recip-star-inverse
        "a nonzero real times its totalised reciprocal is one")

;;; =====================================================================
;;; 6.  rr-half-ball-nonzero -- the ball of radius m about c misses 0 when
;;; m + m = |c|.  The one piece of arithmetic in the file, and the hypothesis
;;; both local transfers below need.
;;; =====================================================================

(sp (make-wff "forall([c in rr, m in rr, y_ in rr],
   0 < m implies m + m = abs(c) implies abs(y_ - c) <= m implies not(y_ = 0))"))
(quietly (lambda ()
  (rs-peel-to! 'NOT)
  (fact 'rr-abs-closed 'c)
  (fact 'rr-abs-closed 'y_)
  (fact 'rr-sub-in-rr 'c 'y_)
  (fact 'rr-sub-in-rr 'y_ 'c)
  (fact 'rr-abs-closed '(- c y_))
  (fact 'rr-abs-closed '(- y_ c))
  (fact 'rr-sub-in-rr '(abs c) '(abs y_))
  (fact 'rr-abs-closed '(- (abs c) (abs y_)))
  (fact 'rr-abs-reverse-triangle 'c 'y_)
  (fact 'rr-abs-sub-sym 'c 'y_)
  (fact 'rr-le-abs '(- (abs c) (abs y_)))
  (have! '(< 0 (abs y_))
    (lambda ()
      (rs-ineq '(< 0 m)
               '(= (+ m m) (abs c))
               '(<= (abs (- y_ c)) m)
               '(<= (abs (- (abs c) (abs y_))) (abs (- c y_)))
               '(= (abs (- c y_)) (abs (- y_ c)))
               '(<= (- (abs c) (abs y_)) (abs (- (abs c) (abs y_)))))))
  (fact 'rr-pos-ne-zero '(abs y_))
  (fact 'rr-abs-zero 'y_)
  ;; modus tollens through the iff, by hand: `prop' sees 32 atoms here.
  (di)                                          ; assume y_ = 0, goal FALSITY
  (ai '(IFF (= (abs y_) 0) (= y_ 0)))
  (detach! '(IMPLIES (= y_ 0) (= (abs y_) 0)))
  (ai '(NOT (= (abs y_) 0)))))
(rs-check 'rr-half-ball-nonzero)
(qed 'rr-half-ball-nonzero)
(topic! 'rr-half-ball-nonzero 'inequalities)
(alias! 'rr-half-ball-nonzero
        "a point within half of |c| of c is not zero")

;;; =====================================================================
;;; 7.  NZ-IDENT = w_ |-> IF w_ = 0 THEN 1 ELSE w_ -- the identity made
;;; nowhere zero, which is what `recip-continuous-at' takes as its h.
;;; =====================================================================

(sp (make-wff (list 'IN RS-NZI '(FUN RR RR))))
(quietly (lambda ()
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'FORALL)
         (let ((v (cadr (car (dk-landed (lambda () (di)))))))
           (use-em (list '= v 0)
             (lambda ()
               (for-each (lambda (l)
                           (dk-focus! l)
                           (if (eq? (car (dk-goal)) '=)
                               (ass)
                               (begin (subst (list '= (rs-nzif v) 1))
                                      (fact 'rr-one-in) (ass))))
                         (dk-opened (lambda () (if-true (rs-nzif v))))))
             (lambda ()
               (for-each (lambda (l)
                           (dk-focus! l)
                           (if (eq? (car (dk-goal)) 'NOT)
                               (ass)
                               (begin (subst (list '= (rs-nzif v) v)) (ass))))
                         (dk-opened (lambda () (if-false (rs-nzif v))))))))
         (begin (fact 'rr-is-set) (ass))))
   (dk-opened (lambda () (lam-t))))))
(rs-check 'nonzero-ident-lam-in-fun)
(qed 'nonzero-ident-lam-in-fun)
(topic! 'nonzero-ident-lam-in-fun 'analysis)
(alias! 'nonzero-ident-lam-in-fun
        "the identity made nowhere zero is a function from the reals to the reals")

;;; The binder here is `x' and not `x_' because this formula is cited AS the
;;; second antecedent of `recip-continuous-at', which spells it that way.
(sp (make-wff (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
                     (list 'NOT (list '= (list RS-NZI 'x) 0))))))
(quietly (lambda ()
  (di)
  (rs-beta!)
  (use-em '(= x 0)
    (lambda ()
      (for-each (lambda (l)
                  (dk-focus! l)
                  (if (eq? (car (dk-goal)) '=)
                      (ass)
                      (begin (subst (list '= (rs-nzif 'x) 1))
                             (fact 'rr-one-in)
                             (fact 'rr-zero-lt-one)
                             (fact 'rr-pos-ne-zero 1)
                             (ass))))
                (dk-opened (lambda () (if-true (rs-nzif 'x))))))
    (lambda ()
      (for-each (lambda (l)
                  (dk-focus! l)
                  (if (and (eq? (car (dk-goal)) 'NOT) (dk-contains? (dk-goal) 'IF))
                      (begin (subst (list '= (rs-nzif 'x) 'x)) (ass))
                      (ass)))
                (dk-opened (lambda () (if-false (rs-nzif 'x)))))))))
(rs-check 'nonzero-ident-nowhere-zero)
(qed 'nonzero-ident-nowhere-zero)
(topic! 'nonzero-ident-nowhere-zero 'analysis)
(alias! 'nonzero-ident-nowhere-zero "the identity made nowhere zero never vanishes")

;;; =====================================================================
;;; 8.  The radius.  |c| = m + m with 0 < m, for c /= 0 -- the common opening
;;; of the two local transfers.  Returns the half.
;;; =====================================================================

(define (rs-radius! c)
  (fact 'rr-abs-closed c)
  (fact 'rr-abs-nonneg c)
  (fact 'rr-abs-zero c)
  (have! (list 'NOT (list '= (list 'abs c) 0))
    (lambda ()
      (di)
      (ai (list 'IFF (list '= (list 'abs c) 0) (list '= c 0)))
      (detach! (list 'IMPLIES (list '= (list 'abs c) 0) (list '= c 0)))
      (ai (list 'NOT (list '= c 0)))))
  (fact 'neq-sym (list 'abs c) 0)
  (have! (list 'POS-RR (list 'abs c)) (lambda () (mac 'pos-rr) (from-context!)))
  (let ((d (obtain (lambda () (fact 'rr-pos-halvable (list 'abs c))))))
    (if (not d) (error "rs-radius!: no half obtained" c))
    (rs-split!)
    (mac-h 'pos-rr (list 'POS-RR d))
    (rs-split!)
    (have! (list '< 0 d) (lambda () (mac '<) (from-context!)))
    d))

;;; =====================================================================
;;; 9.  TRANSFER ONE: NZ-IDENT is continuous at every c /= 0, because it
;;; agrees with the identity on the ball of radius m about c.
;;; =====================================================================

(sp (make-wff (list 'FORALL 'c (list 'IMPLIES '(IN c RR)
       (list 'IMPLIES '(NOT (= c 0))
             (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS RS-NZI 'c))))))
(quietly (lambda ()
  (rs-peel-to! 'IS-CONTINUOUS-AT)
  (let ((d (rs-radius! 'c)))
    (fact 'nonzero-ident-lam-in-fun)
    (fact 'ident-lam-in-fun)
    (fact 'identity-continuous-at 'c)
    (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
             (list 'IMPLIES (list '<= '(abs (- x_ c)) d)
                   (list '= (list RS-NZI 'x_) (list '(VNB-LAMBDA x RR x) 'x_)))))
      (lambda ()
        (di) (di)
        (fact 'rr-half-ball-nonzero 'c d 'x_)
        (rs-beta!)
        (for-each (lambda (l) (dk-focus! l) (ass))
                  (dk-opened (lambda () (if-false (rs-nzif 'x_)))))))
    (fact 'continuous-at-local RS-NZI '(VNB-LAMBDA x RR x) 'c d)
    (ass))))
(rs-check 'nonzero-ident-continuous-at)
(qed 'nonzero-ident-continuous-at)
(topic! 'nonzero-ident-continuous-at 'analysis)
(alias! 'nonzero-ident-continuous-at
        "the identity made nowhere zero is continuous away from zero")

;;; =====================================================================
;;; 10.  TRANSFER TWO: the totalised reciprocal is continuous at every c /= 0.
;;; =====================================================================

(sp (make-wff (list 'FORALL 'c (list 'IMPLIES '(IN c RR)
       (list 'IMPLIES '(NOT (= c 0))
             (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS RS-LAM 'c))))))
(quietly (lambda ()
  (rs-peel-to! 'IS-CONTINUOUS-AT)
  (let ((d (rs-radius! 'c)))
    (fact 'nonzero-ident-lam-in-fun)
    (fact 'nonzero-ident-nowhere-zero)
    (fact 'nonzero-ident-continuous-at 'c)
    (fact 'recip-lam-in-fun RS-NZI)
    (fact 'recip-continuous-at RS-NZI 'c)
    (fact 'recip-star-lam-in-fun)
    (have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
             (list 'IMPLIES (list '<= '(abs (- x_ c)) d)
                   (list '= (list RS-LAM 'x_) (list RS-GLAM 'x_)))))
      (lambda ()
        (di) (di)
        (fact 'rr-half-ball-nonzero 'c d 'x_)
        (rs-beta!)
        (for-each (lambda (l)
                    (dk-focus! l)
                    (if (eq? (car (dk-goal)) 'NOT)
                        (ass)
                        (begin (subst (list '= (rs-nzif 'x_) 'x_))
                               (fact 'recip-star-value 'x_)
                               (ass))))
                  (dk-opened (lambda () (if-false (rs-nzif 'x_)))))))
    (fact 'continuous-at-local RS-LAM RS-GLAM 'c d)
    (ass))))
(rs-check 'recip-star-continuous-at)
(qed 'recip-star-continuous-at)
(topic! 'recip-star-continuous-at 'analysis)
(alias! 'recip-star-continuous-at
        "the totalised reciprocal is continuous away from zero")

;;; =====================================================================
;;; 11.  What the logarithm actually needs: the integrand is continuous at
;;; every point of a closed interval that stays to the right of 0.  With
;;; recip-star-lam-in-fun (the FUN(RR,RR) membership Def 4.6 demands of its
;;; phi) this is the whole of the integrand side of
;;;
;;;     log(x)  =  C-INT(z_ |-> RECIP-STAR(z_), 1, x).
;;; =====================================================================

(sp (make-wff (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
       (list 'FORALL 'b (list 'IMPLIES '(IN b RR)
         (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
           (list 'IMPLIES '(< 0 a)
             (list 'IMPLIES '(IN x_ (CCINT a b))
                   (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS RS-LAM 'x_)))))))))))
(quietly (lambda ()
  (rs-peel-to! 'IS-CONTINUOUS-AT)
  (fact 'ccint-membership 'a 'b 'x_)
  (ai '(IFF (IN x_ (CCINT a b)) (AND (IN x_ RR) (AND (<= a x_) (<= x_ b)))))
  (detach! '(IMPLIES (IN x_ (CCINT a b))
                     (AND (IN x_ RR) (AND (<= a x_) (<= x_ b)))))
  (rs-split!)
  (have! '(< 0 x_) (lambda () (rs-ineq '(< 0 a) '(<= a x_))))
  (fact 'rr-pos-ne-zero 'x_)
  (fact 'recip-star-continuous-at 'x_)
  (ass)))
(rs-check 'recip-star-continuous-on-ccint)
(qed 'recip-star-continuous-on-ccint)
(topic! 'recip-star-continuous-on-ccint 'analysis)
(alias! 'recip-star-continuous-on-ccint
        "the totalised reciprocal is continuous on a closed interval to the right of zero")
