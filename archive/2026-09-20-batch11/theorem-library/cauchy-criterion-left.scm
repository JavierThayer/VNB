;;; cauchy-criterion-left.scm -- docs/calculus.pdf Ch 4 Sec 1.
;;;
;;; A CAUCHY CRITERION FOR ONE-SIDED LIMITS.  The notes end the sufficiency
;;; half of Proposition 4.5 with "since epsilon is arbitrary, this proves the
;;; left hand limits for g exist at x" -- that sentence IS this lemma, and
;;; nothing in the tree had it.  With it, sufficiency is assembly.
;;;
;;;   forall f in FUN(RR,RR), x in RR.
;;;     (forall eps > 0. exists delta > 0. forall s,t in [x-delta, x).
;;;                                          |f(s) - f(t)| <= eps)
;;;     implies  exists l.  IS-LEFT-LIMIT(f, x, l)
;;;
;;; Bills `modulo {nn-recip-succ-small}': the Archimedean assertion, inherited
;;; through `recip-succ-small'.  Nothing else is assumed.
;;;
;;; NO CHOICE FAMILY IS NEEDED, which is where this came in cheaper than
;;; estimated.  The textbook proof reads as though the sample points must be
;;; CHOSEN per epsilon; fixing them in closed form as x - recip(k+1) removes the
;;; per-index choice and the whole lam-t-over-a-chosen-family apparatus with it.
;;; When a proof says "choose", ask first whether a canonical sequence will do.
;;;
;;; `seq-limit' names the limit as a TERM (seq-limit-converges-to), so the
;;; existential witness is an expression and is never skolemized.
;;;
;;; FOUR CERTIFICATION TRAPS, none of them mathematics, all of them cost a run:
;;;
;;;   * `ineq' LINEARISES over `+', so it certifies the SUMMANDS: `K in rr' is
;;;     useless where K is n1 + n2, and `n1 in rr', `n2 in rr' are wanted.
;;;   * `pos-rr(d)' is NOT a membership the oracle can see.  `d in rr' has to be
;;;     landed, and in a `have!' LANE -- `mac-h' is destructive and the main
;;;     branch still wants the pos-rr.
;;;   * `rr-abs-triangle-c' detaches only with BOTH summands typed, and they are
;;;     differences of reals: rr-sub-in-rr twice.
;;;   * it is stated |a+b| <= |a|+|b|, so `f(t) - l' must be bridged into a
;;;     genuine SUM (crs, then subst) before it applies.

;;; cauchy-criterion-left-drive.scm
;;;
;;; docs/calculus.pdf Chapter 4, the mechanism Proposition 4.5 is really about:
;;; a CAUCHY CRITERION FOR ONE-SIDED LIMITS.  The notes end the sufficiency
;;; half with "since epsilon is arbitrary, this proves the left hand limits
;;; for g exist at x" -- that sentence IS this lemma, and nothing in the tree
;;; had it.  With it, sufficiency becomes assembly.
;;;
;;;   forall f in FUN(RR,RR), x in RR.
;;;     (forall eps > 0. exists delta > 0. forall s,t in [x-delta, x).
;;;                                          |f(s) - f(t)| <= eps)
;;;     implies  exists l.  IS-LEFT-LIMIT(f, x, l)
;;;
;;; The construction takes the sample sequence  SQ(k) = f(x - recip(k+1)) --
;;; NO choice family is needed, which is the one place this came in cheaper
;;; than estimated: fixing the sample points in closed form removes the
;;; per-index choice the textbook proof appears to want.
;;;
;;; Done and checked below: SQ is typed into FUN(NN,RR) (lam-t, both leaves),
;;; SQ is Cauchy, rr-cauchy-converges gives convergence, and
;;; seq-limit-converges-to names the limit as a TERM -- so the existential
;;; witness is `seq-limit(SQ)' and never has to be skolemized.
;;;
;;;   ./prover -i prove-scripts/drives/cauchy-criterion-left-drive.scm
;;;
(define SQ '(VNB-LAMBDA k_ NN (f (- x (RECIP (+ k_ 1))))))
(define (sqapp i) (list SQ i))
(define cauchy-cond
  (list 'FORALL 'ep2
    (list 'IMPLIES '(POS-RR ep2)
      (list 'FORSOME 'nq
        (list 'AND '(IN nq NN)
          (list 'FORALL 'mq (list 'IMPLIES '(IN mq NN)
            (list 'FORALL 'pq (list 'IMPLIES '(IN pq NN)
              (list 'IMPLIES '(<= nq mq)
                (list 'IMPLIES '(<= nq pq)
                  (list '<= (list 'ABS (list '- (sqapp 'mq) (sqapp 'pq))) 'ep2))))))))))))
(define cc-left "forall([f, x], f in fun(rr, rr) implies x in rr implies (forall([eps_], pos-rr(eps_) implies forsome([delta_], pos-rr(delta_) and forall([s_, t_], (s_ in rr and x - delta_ <= s_ and s_ < x) implies (t_ in rr and x - delta_ <= t_ and t_ < x) implies abs(f(s_) - f(t_)) <= eps_)))) implies forsome([l_], is-left-limit(f, x, l_)))")

;;; (theorem-library/regulated, onesided-limits, recip-succ-small; load.scm
;;; ~2185).  This script therefore proves nothing before it starts -- it opens
;;; a proof and peels.  Re-proving a prelude on every load is what made the
;;; earlier version of this file fragile: any step failing anywhere in that
;;; chain left the prover on an unexplained leaf, and under `quietly' it did so
;;; silently.  If the vocabulary is absent you are on a band older than the
;;; library, and that is worth saying HERE rather than failing at the first
;;; `mac' three steps later.

;;; File-local, with this file's prefix, per the brief: a driver helper lives in
;;; driver-kit.scm or in the file that uses it, and there is no third place.
;;; `theorem-library/recip-succ-small' has a twin, but library files load into
;;; contained environments, so it is not visible from here -- which is the
;;; containment doing its job.
;;; Context and leaf finders, file-local with this file's prefix.  Nothing here
;;; is positional: an assumption is located by a PREDICATE on its formula and a
;;; leaf by its goal, both resolved at call time.  That is the same discipline
;;; `ineq!' enforces for the oracle's premises, and for the same reason -- an
;;; index is right only for the context its author happened to have.
;;; cauchy-criterion-left-drive.scm
;;;
;;; docs/calculus.pdf Chapter 4, the mechanism Proposition 4.5 is really about:
;;; a CAUCHY CRITERION FOR ONE-SIDED LIMITS.  The notes end the sufficiency
;;; half with "since epsilon is arbitrary, this proves the left hand limits
;;; for g exist at x" -- that sentence IS this lemma, and nothing in the tree
;;; had it.  With it, sufficiency becomes assembly.
;;;
;;;   forall f in FUN(RR,RR), x in RR.
;;;     (forall eps > 0. exists delta > 0. forall s,t in [x-delta, x).
;;;                                          |f(s) - f(t)| <= eps)
;;;     implies  exists l.  IS-LEFT-LIMIT(f, x, l)
;;;
;;; The construction takes the sample sequence  SQ(k) = f(x - recip(k+1)) --
;;; NO choice family is needed, which is the one place this came in cheaper
;;; than estimated: fixing the sample points in closed form removes the
;;; per-index choice the textbook proof appears to want.
;;;
;;; Done and checked below: SQ is typed into FUN(NN,RR) (lam-t, both leaves),
;;; SQ is Cauchy, rr-cauchy-converges gives convergence, and
;;; seq-limit-converges-to names the limit as a TERM -- so the existential
;;; witness is `seq-limit(SQ)' and never has to be skolemized.
;;;
;;;   ./prover -i prove-scripts/drives/cauchy-criterion-left-drive.scm
;;;
(define (astr a) (expression->string (if (wff? a) (wff-formula a) a)))
(define (dump tag . n) tag n)          ; silent; flip to print while driving
(define (show-leaf)
  (display "  GOAL: ")
  (display (expression->string (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))) (newline)
  (let loop ((as (dk-asms)) (i 1))
    (if (and (pair? as) (<= i 6))
        (begin (display "  A") (display i) (display ": ") (display (astr (car as))) (newline)
               (loop (cdr as) (+ i 1))))))
(define SQ '(VNB-LAMBDA k_ NN (f (- x (RECIP (+ k_ 1))))))
(define (sqapp i) (list SQ i))
(define cauchy-cond
  (list 'FORALL 'ep2
    (list 'IMPLIES '(POS-RR ep2)
      (list 'FORSOME 'nq
        (list 'AND '(IN nq NN)
          (list 'FORALL 'mq (list 'IMPLIES '(IN mq NN)
            (list 'FORALL 'pq (list 'IMPLIES '(IN pq NN)
              (list 'IMPLIES '(<= nq mq)
                (list 'IMPLIES '(<= nq pq)
                  (list '<= (list 'ABS (list '- (sqapp 'mq) (sqapp 'pq))) 'ep2))))))))))))
(define cc-left "forall([f, x], f in fun(rr, rr) implies x in rr implies (forall([eps_], pos-rr(eps_) implies forsome([delta_], pos-rr(delta_) and forall([s_, t_], (s_ in rr and x - delta_ <= s_ and s_ < x) implies (t_ in rr and x - delta_ <= t_ and t_ < x) implies abs(f(s_) - f(t_)) <= eps_)))) implies forsome([l_], is-left-limit(f, x, l_)))")

;;; The vocabulary and the one-sided lemmas are LIBRARY results now
;;; (theorem-library/regulated, onesided-limits, recip-succ-small; load.scm
;;; ~2185).  This script therefore proves nothing before it starts -- it opens
;;; a proof and peels.  Re-proving a prelude on every load is what made the
;;; earlier version of this file fragile: any step failing anywhere in that
;;; chain left the prover on an unexplained leaf, and under `quietly' it did so
;;; silently.  If the vocabulary is absent you are on a band older than the
;;; library, and that is worth saying HERE rather than failing at the first
;;; `mac' three steps later.

;;; File-local, with this file's prefix, per the brief: a driver helper lives in
;;; driver-kit.scm or in the file that uses it, and there is no third place.
;;; `theorem-library/recip-succ-small' has a twin, but library files load into
;;; contained environments, so it is not visible from here -- which is the
;;; containment doing its job.
;;; Context and leaf finders, file-local with this file's prefix.  Nothing here
;;; is positional: an assumption is located by a PREDICATE on its formula and a
;;; leaf by its goal, both resolved at call time.  That is the same discipline
;;; `ineq!' enforces for the oracle's premises, and for the same reason -- an
;;; index is right only for the context its author happened to have.
(define (cc-asm-index pred)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "cc-asm-index: no assumption matches"))
          ((pred (car as)) i)
          (else (loop (cdr as) (+ i 1))))))

(define (cc-mentions? f sub)
  (cond ((equal? f sub) #t)
        ((pair? f) (or (cc-mentions? (car f) sub) (cc-mentions? (cdr f) sub)))
        (else #f)))

(define (cc-focus-goal! g)
  (dk-focus! (or (find-first (lambda (n) (equal? (wff-formula (sequent-node-assertion n)) g))
                             (proof-leaves))
                 (error "cc-focus-goal!: no open leaf with that goal" g))))

(define (cc-focus-head! h)
  (dk-focus! (or (find-first (lambda (n) (let ((g (wff-formula (sequent-node-assertion n))))
                                           (and (pair? g) (eq? (car g) h))))
                             (proof-leaves))
                 (error "cc-focus-head!: no open leaf with head" h))))

;;; `ai' the context existential at index K and return the ONE eigenvariable it
;;; minted, read off by free-variable difference.  Never hard-code a minted
;;; name: the counter is global and monotonic, so `delta_4526' is a fact about
;;; the session, not about the proof.
(define (cc-skolem-of! k)
  (let ((before (free-vars (car (dk-asms)))))
    (ai k)
    (let* ((after (free-vars (car (dk-asms))))
           (new   (filter (lambda (v) (not (memq v before))) after)))
      (if (not (= 1 (length new)))
          (error "cc-skolem-of!: expected exactly one new eigenvariable" new))
      (car new))))

(define (cc-type-recip! n)
  (fact 'rr-one-in)
  (fact 'rr-zero-in)
  (fact 'nn-in-rr n)
  (fact 'nn-zero-le n)
  (have! (list 'IN (list '+ n 1) 'RR) (lambda () (in-rr)))
  ;; name the two premises: `ineq!' vets by RR-certifiability and this
  ;; context has order facts it cannot certify, which poison the call.
  (have! (list '< 0 (list '+ n 1))
         (lambda () (ineq-on! (list '<= 0 n) (list 'IN n 'RR))))
  (fact 'rr-pos-ne-zero (list '+ n 1))
  (have! (list 'AND (list 'IN (list '+ n 1) 'RR)
                    (list 'NOT (list '= (list '+ n 1) 0)))
         (lambda () (di) (ass-all)))
  (fact 'rr-recip-closed (list '+ n 1))
  (fact 'rr-recip-pos (list '+ n 1)))

(sp (make-wff cc-left))
(quietly (lambda ()
  (di) (di) (di) (di)))
(have! (list 'IN SQ '(FUN NN RR))
       (lambda ()
         (lam-t)
         (let ((kk (cadr (dk-goal))))
           (di) (cc-type-recip! kk)
           (in-rr))
         (cc-focus-goal! '(IN NN SET)) (fact 'nn-is-set) (ass)))
(display ";; sequence typed\n")
(have! cauchy-cond
       (lambda ()
         (di) (di)
         ;; delta from the hypothesis at ep2
         (inst+ (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                            (cc-mentions? g 'delta_)))) 'ep2)
         (let ((dl (cc-skolem-of! 1)))
           (dk-split! (car (dk-asms)))
           ;; delta in rr, for the oracle's typing certificates
           (have! (list 'IN dl 'RR)
                  (lambda () (mac-h 'pos-rr (list 'POS-RR dl))
                             (dk-split! (car (dk-asms))) (ass)))
           ;; the Archimedean threshold for that delta
           (fact 'recip-succ-small dl)
           (let ((nn0 (cc-skolem-of! 1)))
             (dk-split! (car (dk-asms)))
             (ew nn0)
             (di) (ass-all) (cc-focus-head! 'FORALL)
             (di) (di) (di)
             (lam-b)
             (inst+ (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                                (cc-mentions? g (list 'RECIP (list '+ 'm_ 1)))))) 'mq)
             (inst+ (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                                (cc-mentions? g (list 'RECIP (list '+ 'm_ 1)))))) 'pq)
             (cc-type-recip! 'mq) (cc-type-recip! 'pq)
             ;; both sample points lie in [x - delta, x)
             (define (guard-for! i)
               (let ((pt (list '- 'x (list 'RECIP (list '+ i 1)))))
                 (have! (list 'IN pt 'RR) (lambda () (in-rr)))
                 (have! (list '<= (list '- 'x dl) pt)
                        (lambda () (ineq (cc-asm-index (lambda (g) (equal? g (list '<= (list 'RECIP (list '+ i 1)) dl)))))))
                 (have! (list '< pt 'x)
                        (lambda () (ineq (cc-asm-index (lambda (g) (equal? g (list '< 0 (list 'RECIP (list '+ i 1))))))
                                         (cc-asm-index (lambda (g) (equal? g (list 'IN 'x 'RR)))))))
                 (have! (list 'AND (list 'IN pt 'RR)
                                   (list 'AND (list '<= (list '- 'x dl) pt) (list '< pt 'x)))
                        (lambda () (di) (ass-all) (cc-focus-head! 'AND) (di) (ass-all)))))
             (guard-for! 'mq) (guard-for! 'pq)
             (let ((find-st (lambda ()
                              (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                                          (cc-mentions? g 'ep2)
                                                          (cc-mentions? g 'ABS)))))))
               (inst+ (find-st) (list '- 'x (list 'RECIP (list '+ 'mq 1))))
               (inst+ (find-st) (list '- 'x (list 'RECIP (list '+ 'pq 1)))))
             (dump "after instantiating the hypothesis" 3)
             (ass)))))
(display ";; Cauchy condition for the sequence: established\n")
(quietly (lambda ()
  (fact 'rr-cauchy-converges SQ)
  (fact 'seq-limit-converges-to SQ)))
(dump "limit in hand" 3)
(quietly (lambda ()
  (ew (list 'SEQ-LIMIT SQ))
  (mac 'IS-LEFT-LIMIT)))
(quietly (lambda ()
  (mac-h 'converges-to (list 'CONVERGES-TO 'RR-MS SQ (list 'SEQ-LIMIT SQ)))
  (dk-split! (car (dk-asms)))
  (slot-h 'PTS (list 'IN (list 'SEQ-LIMIT SQ) '(PTS RR-MS)))
  (di) (focus 2) (di) (focus 3) (di) (focus 4)
  (ass-all) (focus 1) (di) (di)))

;; --- step 1: halve eps, and get delta1 from the ORIGINAL Cauchy hypothesis ---
(quietly (lambda () (fact 'rr-pos-halvable 'eps_)))
(define hh (cc-skolem-of! 1))
(quietly (lambda () (dk-split! (car (dk-asms)))))
(display "\n;; h = ") (display hh) (newline)
;; the original hypothesis: forall eps_. pos-rr(eps_) implies forsome delta_. ... s_,t_ ...
(quietly (lambda ()
  (inst+ (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                        (cc-mentions? g 's_) (cc-mentions? g 't_))))
         hh)))
(define dl (cc-skolem-of! 1))
(quietly (lambda () (dk-split! (car (dk-asms)))))

;; --- step 2: the two thresholds, at h and at delta1 ---
(quietly (lambda ()
  (inst+ (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                        (cc-mentions? g '(DIST RR-MS))
                                        (cc-mentions? g 'SEQ-LIMIT))))
         hh)))
(define n1 (cc-skolem-of! 1))
(quietly (lambda () (dk-split! (car (dk-asms)))))
(quietly (lambda () (fact 'recip-succ-small dl)))
(define n2 (cc-skolem-of! 1))
(quietly (lambda () (dk-split! (car (dk-asms)))))

;; --- step 3: K = N1 + N2 dominates both thresholds ---
(define kk (list '+ n1 n2))
(quietly (lambda ()
  (have! (list 'AND (list 'IN n1 'NN) (list 'IN n2 'NN)) (lambda () (di) (ass-all)))
  (fact 'nn-add-closed n1 n2)          ; K in nn
  (fact 'nn-le-add n2 n1)              ; n1 <= n1 + n2
  (fact 'nn-le-add-left n1 n2)))       ; n2 <= n1 + n2

;; --- step 4: supply delta1 as the witness and peel t_ ---
(quietly (lambda ()
  (ew dl)
  (di) (ass-all)
  (cc-focus-head! 'FORALL)
  (di) (di)
  (dk-split! (car (dk-asms)))))

;; --- step 5: the two summands ---
(quietly (lambda ()
  (fact 'rr-one-in) (fact 'rr-zero-in)
  (fact 'nn-in-rr kk) (fact 'nn-zero-le kk)
  ;; `ineq' LINEARISES over `+', so it certifies the SUMMANDS, not the sum:
  ;; `K in rr' alone leaves n1 and n2 uncertified and the call is refused.
  (fact 'nn-in-rr n1) (fact 'nn-in-rr n2)
  (have! (list 'IN (list '+ kk 1) 'RR) (lambda () (in-rr)))))
(have! (list '< 0 (list '+ kk 1))
       (lambda () (ineq-on! (list '<= 0 kk) (list 'IN kk 'RR))))
(quietly (lambda ()
  ;; recip(K+1) <= delta1
  (inst+ (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                        (cc-mentions? g dl)
                                        (cc-mentions? g 'RECIP)))) kk)
  ;; dist(rr-ms)(SQ(K), l) <= h
  (inst+ (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                        (cc-mentions? g '(DIST RR-MS))
                                        (cc-mentions? g 'SEQ-LIMIT)
                                        (cc-mentions? g hh)))) kk)
  (lam-b-h 1)))

;; --- step 6: finish the typing of recip(K+1), place tau_K in the interval ---
(quietly (lambda ()
  (fact 'rr-pos-ne-zero (list '+ kk 1))
  (have! (list 'AND (list 'IN (list '+ kk 1) 'RR)
                    (list 'NOT (list '= (list '+ kk 1) 0)))
         (lambda () (di) (ass-all)))
  (fact 'rr-recip-closed (list '+ kk 1))
  (fact 'rr-recip-pos (list '+ kk 1))
  ;; tau_K = x - recip(K+1) lies in [x - delta1, x)
  (have! (list 'IN (list '- 'x (list 'RECIP (list '+ kk 1))) 'RR) (lambda () (in-rr)))
  ;; delta1 in rr, for the oracle's certificates.  Taken in a `have!' LANE so
  ;; the destructive `mac-h' does not remove pos-rr(delta1) from the main branch.
  (have! (list 'IN dl 'RR)
         (lambda () (mac-h 'pos-rr (list 'POS-RR dl))
                    (dk-split! (car (dk-asms))) (ass)))
  (have! (list '<= (list '- 'x dl) (list '- 'x (list 'RECIP (list '+ kk 1))))
         (lambda () (ineq-on! (list '<= (list 'RECIP (list '+ kk 1)) dl))))
  (have! (list '< (list '- 'x (list 'RECIP (list '+ kk 1))) 'x)
         (lambda () (ineq-on! (list '< 0 (list 'RECIP (list '+ kk 1)))
                              (list 'IN 'x 'RR))))))

;; --- step 7: the first summand, |f(t_) - f(tau_K)| <= h ---
(define tau (list '- 'x (list 'RECIP (list '+ kk 1))))
(define (guard-of pt)
  (list 'AND (list 'IN pt 'RR)
             (list 'AND (list '<= (list '- 'x dl) pt) (list '< pt 'x))))
(quietly (lambda ()
  (have! (guard-of 't_)  (lambda () (di) (ass-all) (cc-focus-head! 'AND) (di) (ass-all)))
  (have! (guard-of tau)  (lambda () (di) (ass-all) (cc-focus-head! 'AND) (di) (ass-all)))
  (let ((st (lambda () (cc-asm-index (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                                      (cc-mentions? g hh)
                                                      (cc-mentions? g 'ABS)))))))
    (inst+ (st) 't_)
    (inst+ (st) tau))))
;; --- step 8: the second summand, |f(tau_K) - l| <= h ---
(quietly (lambda ()
  (fact 'fun-apply-type-c 'f 'RR 'RR tau)
  (mac-h 'rr-ms-dist
         (list '<= (list (list 'DIST 'RR-MS) (list 'f tau)
                         (list 'SEQ-LIMIT '(VNB-LAMBDA k_ NN (f (- x (RECIP (+ k_ 1)))))))
               hh))))

;; --- step 9: the triangle ---
;; rr-abs-triangle-c is |a+b| <= |a|+|b|, so bridge  f(t_) - l  into a SUM first.
(define lim (list 'SEQ-LIMIT '(VNB-LAMBDA k_ NN (f (- x (RECIP (+ k_ 1)))))))
(define A (list '- (list 'f 't_) (list 'f tau)))
(define B (list '- (list 'f tau) lim))
(quietly (lambda ()
  (fact 'fun-apply-type-c 'f 'RR 'RR 't_)
  (have! (list '= (list '- (list 'f 't_) lim) (list '+ A B)) (lambda () (crs)))
  (subst (list '= (list '- (list 'f 't_) lim) (list '+ A B)))
  ;; the triangle detaches only with BOTH summands typed; they are differences
  ;; of reals, so rr-sub-in-rr supplies them.
  (fact 'rr-sub-in-rr (list 'f 't_) (list 'f tau))
  (fact 'rr-sub-in-rr (list 'f tau) lim)
  (fact 'rr-abs-triangle-c A B)
  ;; h and eps_ in RR, for the oracle's certificates -- `pos-rr' alone is not
  ;; a membership the oracle can see.  Both in `have!' lanes: `mac-h' is
  ;; destructive and pos-rr(eps_) is still wanted in the main branch.
  (have! (list 'IN hh 'RR)
         (lambda () (mac-h 'pos-rr (list 'POS-RR hh))
                    (dk-split! (car (dk-asms))) (ass)))
  (have! '(IN eps_ RR)
         (lambda () (mac-h 'pos-rr '(POS-RR eps_))
                    (dk-split! (car (dk-asms))) (ass)))))
(ineq-on! (list '<= (list 'ABS A) hh)
          (list '<= (list 'ABS B) hh)
          (list '= (list '+ hh hh) 'eps_)
          (list '<= (list 'ABS (list '+ A B)) (list '+ (list 'ABS A) (list 'ABS B))))
(qed 'cauchy-criterion-left)
(display "  GOAL: ") (display (expression->string (dk-goal))) (newline)
