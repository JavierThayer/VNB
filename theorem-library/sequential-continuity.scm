;;; sequential-continuity.scm -- THE SEQUENTIAL CHARACTERIZATION OF
;;; CONTINUITY, both directions PROVEN:
;;;
;;;   IS-CONTINUOUS-AT(s, t, f, a)
;;;     iff  every sequence sq -> a in s has COMPOSE(f, sq) -> f(a) in t.
;;;
;;; The tree had the eps/delta side only (structure-library/metric-continuity.scm,
;;; whose head comment lists "the sequential characterization" as deliberately
;;; deferred) and the convergence side only (metric-completeness.scm); nothing
;;; joined them.  That is the gap under `product-weights-equivalent'
;;; (structure-library/product-metric.scm), which is stated as BICONTINUITY of the
;;; identity while everything the product lane proves --
;;; `product-convergence-coordinatewise', `dominated-null-series' -- is about
;;; CONVERGENCE.
;;;
;;; TWO SPACES, not one: IS-CONTINUOUS-AT is (s t f a), with (DIST s) on the
;;; hypothesis side and (DIST t) on the conclusion side.  The image sequence is
;;; COMPOSE(f, sq) -- in COMPOSE(f, g) the map g runs FIRST (compose.scm).
;;;
;;; WHAT IS IN THE FILE, in order:
;;;
;;;   L1  continuous-at-implies-sequential   (=>)   modulo {compose-type, compose-apply}
;;;   L2  not-continuous-witness             logic  modulo 0
;;;   L3  rr-recip-antitone                  scalar modulo 0
;;;   L4  nn-recip-succ-antitone             scalar modulo {nn-zero-le}
;;;   L5  sequential-implies-continuous-at   (<=)
;;;   L6  continuous-at-iff-sequential       the two, by `prop'
;;;
;;; THE TWO DIRECTIONS ARE NOT THE SAME SIZE.
;;;
;;; (=>) is a direct chase and needs nothing new: take eps, get delta from
;;; continuity, get N from the convergence of sq at delta, and the same N serves.
;;; The only two mechanical points are that CONVERGES-TO's estimate is
;;; d(s)(sq(n), a) while IS-CONTINUOUS-AT's is d(s)(a, b) -- one `metric-sym' on
;;; each side -- and that the goal's term is (COMPOSE(f,sq))(n), which
;;; `compose-apply' turns into f(sq(n)).
;;;
;;; (<=) carries the content and needs a CONSTRUCTION.  Contrapositive: if some
;;; eps has no delta, then at each scale 1/(k+1) there is a point x_k with
;;; d(s)(a, x_k) <= 1/(k+1) and NOT d(t)(f(a), f(x_k)) <= eps; that sequence
;;; converges to a while its image does not converge to f(a).  Three things had
;;; to be settled, and each is worth stating on its own:
;;;
;;; * THE CHOICE.  x_k is CHOICE of a SEP -- the CENTRES idiom of
;;;   compactness.scm and the fibre of ord-no-injection.scm -- and the sequence
;;;   is the VNB-LAMBDA k. CHOICE(W_k), typed by `lam-t'.  `choice-axiom'
;;;   (library.scm) is PRIMITIVE, so this construction adds NOTHING to the bill:
;;;   no countable-choice or dependent-choice support is needed, and `dc-on-nn'
;;;   (asserted, `reference') is NOT cited -- the choices here are independent,
;;;   so the plain Hilbert epsilon at each k suffices.
;;;
;;; * THE NEGATION, which `push-not-h' (push-not.scm) now does -- but only in a
;;;   SMALL context.  It discharges its FORALL case through `prop', and `prop'
;;;   counts the atoms of the WHOLE context; at the point the driver needs the
;;;   push there are sixteen, over *prop-atom-cap* (12), and the push fails.  So
;;;   the step is L2, a standalone THEOREM of pure logic -- no typing hypothesis,
;;;   no metric fact -- proved where the context is the single NOT, and cited by
;;;   `fact' at each radius.  The same cap bites at L6 and is dodged the same
;;;   way: each citation goes inside its own `have!' lane, so the instantiation
;;;   chains `fact' lands stay out of the context `prop' has to read.
;;;
;;; * THE MISSING SCALAR FACT (L3).  1/(n+1) <= 1/(N+1) for n >= N is what turns
;;;   the ladder of radii into convergence, and the tree had no recip
;;;   monotonicity at all: `rr-recip-pos' (rr-recip-order.scm) is the whole of
;;;   it, and the warrants of `nn-recip-succ-pos' and `nn-recip-succ-small'
;;;   (order-predicates.scm) both say so in as many words -- "it needs the
;;;   recip-monotonicity lemmas (0 < a => 0 < recip a; 0 < a < b => recip b <
;;;   recip a), which the tree does not have yet".  The second of those is L3,
;;;   proved here `modulo 0' by the cross-multiplication that `bdd-fn-reflect'
;;;   uses: 1/u - 1/v = (1/u)(1/v)(v - u) is a `crs' identity with recip(u),
;;;   recip(v) as opaque generators, the two inverse equations collapse
;;;   u*recip(u) and v*recip(v) to 1, and `ineq' reads the order off the sign of
;;;   the difference.  L4 is its NN reading.
;;;
;;; Dependencies: metric-continuity (IS-CONTINUOUS-AT), metric-completeness
;;; (CONVERGES-TO), compose (COMPOSE, compose-type, compose-apply), sqn
;;; (sqn-membership), metric-laws (metric-sym), metric-space (metric-dist-real),
;;; fun-apply-type-proof (fun-apply-type-c), order-predicates
;;; (nn-recip-succ-pos/-small), order-lemmas (nn-zero-le), rr-recip-order
;;; (rr-recip-pos, rr-mul-pos), rr-order-basics, nn-order-basics (nn-in-rr,
;;; nn-le-refl), push-not (push-not-h), prop, driver-kit.

;;; ---- file-local driver helpers (the `sc-' prefix) --------------------

;;; Peel the FORALL/IMPLIES prefix until the goal's head is `head'.  `di' is
;;; greedy within one binder level and stops at the next, so this loops.
(define (sc-peel-to! head)
  (let lp ((k 0))
    (if (and (< k 24) (pair? (dk-goal)) (not (eq? (car (dk-goal)) head)))
        (begin (di) (lp (+ k 1))))))

(define (sc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "sc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; Close a right-nested AND goal, conjunct by conjunct, with `closer'.
(define (sc-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (sc-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (sc-and2! a b) (have! (list 'AND a b) (lambda () (sc-and! (lambda () (ass))))))

;;; Skolemize a FORSOME that this call lands itself (`obtain' cannot see one
;;; that is already in the context): `ai' it, split whatever conjunction lands,
;;; and read the eigenvariable off by free-variable set difference.
(define (sc-fvs forms) (apply append (map free-vars forms)))
(define (sc-skolem! ex)
  (let* ((fv0 (sc-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (sc-fvs (dk-asms)))))
      (if (null? fresh) (error "sc-skolem!: nothing appeared" ex) (car fresh)))))

;;; Loop on the LANDING, not on a `di' count: a guarded universal lands its
;;; guard in one call, an implication with an AND antecedent lands nothing.
(define (sc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "sc-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (sc-di-landed-1!)
  (let ((new (sc-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "sc-di-landed-1!: expected 1" (map expression->string new)))))

(define (sc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "sc-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (sc-ineq . forms) (apply ineq (map sc-idx forms)))
;; the reverse of a context equation, by rewriting the goal with it
(define (sc-rev! e)
  (let ((r (list '= (caddr e) (cadr e))))
    (have! r (lambda () (subst e) (rfl)))
    r))

;;; =====================================================================
;;; continuous-at-implies-sequential -- the (=>) half.
;;; =====================================================================

(sp "forall([s, t, f, a], is-metric-space(s) implies is-metric-space(t) implies f in fun(pts(s), pts(t)) implies a in pts(s) implies (is-continuous-at(s, t, f, a) implies forall([sq in sqn(pts(s))], converges-to(s, sq, a) implies converges-to(t, compose(f, sq), f(a)))))")

(sc-peel-to! 'CONVERGES-TO)

;;; Read the eigenvariables off the GOAL, never off the context.
(define sc-g0 (dk-goal))                       ; (CONVERGES-TO t (COMPOSE f sq) (f a))
(define sc-t  (cadr sc-g0))
(define sc-f  (cadr (caddr sc-g0)))
(define sc-sq (caddr (caddr sc-g0)))
(define sc-a  (cadr (cadddr sc-g0)))
(define sc-s  (cadr (caddr (sc-find 'a-typing
   (lambda (x) (and (pair? x) (eq? (car x) 'IN) (equal? (cadr x) sc-a)
                    (pair? (caddr x)) (eq? (car (caddr x)) 'PTS)))))))
(define sc-Ps (list 'PTS sc-s))
(define sc-Pt (list 'PTS sc-t))
(define sc-Ds (list 'DIST sc-s))
(define sc-Dt (list 'DIST sc-t))
(define sc-sq-fun (list 'IN sc-sq (list 'FUN 'NN sc-Ps)))
(define sc-f-fun  (list 'IN sc-f  (list 'FUN sc-Ps sc-Pt)))

;;; SQN(X) is a functoid: `mac' unfolds it in a goal, `mac-h' cannot unfold it
;;; in an assumption -- the membership IFF is what does that (sqn.scm).
(mac-h 'sqn-membership (list 'IN sc-sq (list 'SQN sc-Ps)))

(dk-split! (dk-landed-find
            (lambda () (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT sc-s sc-t sc-f sc-a)))
            (lambda (x) (eq? (car x) 'AND))))
(dk-split! (dk-landed-find
            (lambda () (mac-h 'converges-to (list 'CONVERGES-TO sc-s sc-sq sc-a)))
            (lambda (x) (eq? (car x) 'AND))))

;;; Discriminate the two eps-universals on the metric they mention, not on their
;;; shape: both are FORALL eps guarded by POS-RR.
(define sc-cont-tail
  (sc-find 'cont-tail (lambda (x) (and (eq? (car x) 'FORALL) (dk-contains? x sc-Dt)))))
(define sc-conv-tail
  (sc-find 'conv-tail (lambda (x) (and (eq? (car x) 'FORALL) (dk-contains? x sc-Ds)
                                       (not (dk-contains? x sc-Dt))))))

;;; The two typing conjuncts of the unfolded goal.
(fact 'fun-apply-type-c sc-f sc-Ps sc-Pt sc-a)          ; f(a) in PTS(t)
(sc-and2! sc-sq-fun sc-f-fun)
(fact 'nn-is-set)                                       ; compose-type's (IN A SET) guard
(fact 'compose-type 'NN sc-Ps sc-Pt sc-f sc-sq)         ; f o sq : NN -> PTS(t)

(mac 'converges-to)
(sc-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((memq (car g) '(IS-METRIC-SPACE IN)) (ass))
           (else
            ;; the eps/N clause: eps -> delta (continuity) -> N (convergence).
            (let* ((eps (cadr (sc-di-landed-1!)))
                   (dex (dk-deepest (lambda () (inst+ sc-cont-tail eps))))
                   (dlt (sc-skolem! dex))
                   (cont-inner (sc-find 'cont-inner
                                (lambda (x) (and (eq? (car x) 'FORALL) (dk-contains? x dlt)
                                                 (dk-contains? x sc-Dt)))))
                   (nex (dk-deepest (lambda () (inst+ sc-conv-tail dlt))))
                   (bigN (sc-skolem! nex))
                   (conv-inner (sc-find 'conv-inner
                                (lambda (x) (and (eq? (car x) 'FORALL) (dk-contains? x bigN))))))
              (ew bigN)
              (sc-and!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (let* ((n_   (cadr (sc-di-landed-1!)))
                            (sqn_ (list sc-sq n_))
                            (fsqn (list sc-f sqn_))
                            (fa   (list sc-f sc-a)))
                       (sc-di-landed!)                        ; N <= n_
                       (inst+ conv-inner n_)                  ; d(s)(sq(n_), a) <= delta
                       (fact 'fun-apply-type-c sc-sq 'NN sc-Ps n_)
                       (fact 'metric-sym sc-s sc-a sqn_)
                       (have! (list '<= (list sc-Ds sc-a sqn_) dlt)
                              (lambda ()
                                (subst (list '= (list sc-Ds sc-a sqn_) (list sc-Ds sqn_ sc-a)))
                                (ass)))
                       (inst+ cont-inner sqn_)                ; d(t)(f(a), f(sq(n_))) <= eps
                       (fact 'fun-apply-type-c sc-f sc-Ps sc-Pt sqn_)
                       (fact 'compose-apply 'NN sc-Ps sc-Pt sc-f sc-sq n_)
                       (subst (list '= (list (list 'COMPOSE sc-f sc-sq) n_) fsqn))
                       (fact 'metric-sym sc-t fsqn fa)
                       (subst (list '= (list sc-Dt fsqn fa) (list sc-Dt fa fsqn)))
                       (ass)))))))))))
(qed 'continuous-at-implies-sequential)

(topic! 'continuous-at-implies-sequential 'analysis)
(alias! 'continuous-at-implies-sequential
        "a continuous map carries a convergent sequence to a convergent sequence")

;;; =====================================================================
;;; L2.  not-continuous-witness -- the negation step, as a THEOREM.
;;;
;;; PURE LOGIC: no typing hypothesis, no metric fact.  It is here as a named
;;; lemma and not as three inline `push-not-h' calls for a mechanical reason
;;; worth recording: `push-not-h' discharges its FORALL case through `prop',
;;; and `prop' counts the atoms of the WHOLE context.  Inside the (<=) driver
;;; the context at that moment holds sixteen -- over `*prop-atom-cap*' (12) --
;;; so the push failed there and succeeds here, where the context is the single
;;; NOT.  Proved once, cited with `fact', at any delta.
;;; =====================================================================

(sp "forall([s, t, f, a, eps, dl], not(forall([b_ in pts(s)], (dist(s))(a, b_) <= dl implies (dist(t))(f(a), f(b_)) <= eps)) implies forsome([b_ in pts(s)], (dist(s))(a, b_) <= dl and not((dist(t))(f(a), f(b_)) <= eps)))")
(sc-peel-to! 'FORSOME)
(push-not-h (car (dk-asms)))
(define sc-w-b0 (sc-skolem! (car (dk-asms))))
(push-not-h (sc-find 'not-implies
             (lambda (x) (and (eq? (car x) 'NOT) (pair? (cadr x)) (eq? (car (cadr x)) 'IMPLIES)))))
(dk-split! (car (dk-asms)))
(ew sc-w-b0)
(sc-and! (lambda () (ass)))
(qed 'not-continuous-witness)
(topic! 'not-continuous-witness 'analysis)
(alias! 'not-continuous-witness "a point where continuity fails at a given scale")

;;; =====================================================================
;;; L3.  rr-recip-antitone -- 0 < u <= v gives 1/v <= 1/u.
;;;
;;; The recip-monotonicity lemma the tree did not have, and whose absence is
;;; named in the warrants of `nn-recip-succ-pos' and `nn-recip-succ-small'
;;; (order-predicates.scm: "it needs the recip-monotonicity lemmas ... which the
;;; tree does not have").  Cross-multiplication, in the shape of
;;; `bdd-fn-reflect': 1/u - 1/v = (1/u)(1/v)(v - u), a product of three
;;; nonnegatives.  `crs' does the ring identity with recip(u), recip(v) as
;;; opaque generators; the two inverse equations turn u*recip(u) and v*recip(v)
;;; into 1; `ineq' reads off the order from the sign of the difference.
;;; =====================================================================

(sp "forall([u in rr, v in rr], 0 < u implies u <= v implies recip(v) <= recip(u))")
(sc-peel-to! '<=)
(define sc-ru '(recip u))
(define sc-rv '(recip v))
(fact 'rr-zero-in)
(sc-and2! '(< 0 u) '(<= u v))
(fact 'rr-lt-le-trans 0 'u 'v)                          ; 0 < v
(fact 'rr-pos-ne-zero 'u)
(fact 'rr-pos-ne-zero 'v)
(sc-and2! '(IN u RR) '(NOT (= u 0)))
(sc-and2! '(IN v RR) '(NOT (= v 0)))
(fact 'rr-recip-closed 'u)
(fact 'rr-recip-closed 'v)
(fact 'rr-recip-inverse 'u)
(fact 'rr-recip-inverse 'v)
(fact 'rr-recip-pos 'u)
(fact 'rr-recip-pos 'v)
(fact 'rr-lt-implies-le 0 sc-ru)
(fact 'rr-lt-implies-le 0 sc-rv)
(define sc-rprod (list '* sc-ru sc-rv))
(define sc-vmu '(- v u))
(sc-and2! (list 'IN sc-ru 'RR) (list 'IN sc-rv 'RR))
(fact 'rr-mul-closed sc-ru sc-rv)
(sc-and2! (list '<= 0 sc-ru) (list '<= 0 sc-rv))
(fact 'rr-leq-mul-nonneg sc-ru sc-rv)
(fact 'rr-sub-in-rr 'v 'u)
(have! (list '<= 0 sc-vmu) (lambda () (sc-ineq '(<= u v))))
(sc-and2! (list 'IN sc-rprod 'RR) (list 'IN sc-vmu 'RR))
(sc-and2! (list '<= 0 sc-rprod) (list '<= 0 sc-vmu))
(fact 'rr-leq-mul-nonneg sc-rprod sc-vmu)               ; 0 <= (1/u)(1/v)(v-u)
;; (1/u)(1/v)(v-u) = (1/u)(v(1/v)) - (1/v)(u(1/u)) = 1/u - 1/v
(define sc-Ha (list '= (list '* sc-rprod sc-vmu)
                    (list '- (list '* sc-ru (list '* 'v sc-rv))
                             (list '* sc-rv (list '* 'u sc-ru)))))
(have! sc-Ha (lambda () (crs)))
(have! (list '= (caddr sc-Ha) (list '- sc-ru sc-rv))
       (lambda () (subst '(= (* v (recip v)) 1)) (subst '(= (* u (recip u)) 1)) (crs)))
(define sc-H4 (list '= (list '* sc-rprod sc-vmu) (list '- sc-ru sc-rv)))
(have! sc-H4 (lambda () (subst sc-Ha) (ass)))
(have! (list '<= 0 (list '- sc-ru sc-rv))
       (lambda () (subst (sc-rev! sc-H4)) (ass)))
(sc-ineq (list '<= 0 (list '- sc-ru sc-rv)))
(qed 'rr-recip-antitone)
(topic! 'rr-recip-antitone 'inequalities)
(alias! 'rr-recip-antitone "the reciprocal reverses the order on the positives")

;;; =====================================================================
;;; L4.  nn-recip-succ-antitone -- m <= n gives 1/(n+1) <= 1/(m+1).
;;; The form the ladder of radii is consumed in.
;;; =====================================================================

(sp "forall([m in nn, n_ in nn], m <= n_ implies recip(n_ + 1) <= recip(m + 1))")
(sc-peel-to! '<=)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'nn-in-rr 'm)
(fact 'nn-in-rr 'n_)
(fact 'nn-zero-le 'm)
(sc-and2! '(IN m RR) '(IN 1 RR))
(fact 'rr-add-closed 'm 1)
(sc-and2! '(IN n_ RR) '(IN 1 RR))
(fact 'rr-add-closed 'n_ 1)
(have! '(< 0 (+ m 1)) (lambda () (sc-ineq '(<= 0 m))))
(have! '(<= (+ m 1) (+ n_ 1)) (lambda () (sc-ineq '(<= m n_))))
(fact 'rr-recip-antitone '(+ m 1) '(+ n_ 1))
(ass)
(qed 'nn-recip-succ-antitone)
(topic! 'nn-recip-succ-antitone 'inequalities)
(alias! 'nn-recip-succ-antitone "1/(n+1) decreases")

;;; =====================================================================
;;; L5.  sequential-implies-continuous-at -- the (<=) half.
;;; =====================================================================

;;; from POS-RR x in the context: (IN x RR) and (<= 0 x), which `ineq' wants
(define (sb-rr-parts! x)
  (for-each
   (lambda (part)
     (have! part (lambda ()
                   (mac-h 'pos-rr (list 'POS-RR x))
                   (dk-split! (list 'AND (list 'IN x 'RR)
                                    (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
                   (ass))))
   (list (list 'IN x 'RR) (list '<= 0 x))))

(sp "forall([s, t, f, a], is-metric-space(s) implies is-metric-space(t) implies f in fun(pts(s), pts(t)) implies a in pts(s) implies ((forall([sq in sqn(pts(s))], converges-to(s, sq, a) implies converges-to(t, compose(f, sq), f(a)))) implies is-continuous-at(s, t, f, a)))")
(sc-peel-to! 'IS-CONTINUOUS-AT)

(define sb-g0 (dk-goal))
(define sb-s (cadr sb-g0))
(define sb-t (caddr sb-g0))
(define sb-f (cadddr sb-g0))
(define sb-a (car (cddddr sb-g0)))
(define sb-Ps (list 'PTS sb-s))
(define sb-Pt (list 'PTS sb-t))
(define sb-Ds (list 'DIST sb-s))
(define sb-Dt (list 'DIST sb-t))
(define sb-H (sc-find 'seq-hyp
              (lambda (x) (and (eq? (car x) 'FORALL) (dk-contains? x 'COMPOSE)))))

;;; the ladder of radii, the witness set at scale k, and the chosen point
(define (sb-r k) (list 'recip (list '+ k 1)))
(define (sb-W eps k)
  (list 'SEP 'b_ sb-Ps
        (list 'AND (list '<= (list sb-Ds sb-a 'b_) (sb-r k))
                   (list 'NOT (list '<= (list sb-Dt (list sb-f sb-a) (list sb-f 'b_)) eps)))))
(define (sb-c eps k) (list 'CHOICE (sb-W eps k)))
(define (sb-body eps k)
  (list 'AND (list 'IN (sb-c eps k) sb-Ps)
        (list 'AND (list '<= (list sb-Ds sb-a (sb-c eps k)) (sb-r k))
                   (list 'NOT (list '<= (list sb-Dt (list sb-f sb-a)
                                              (list sb-f (sb-c eps k))) eps)))))

(mac 'is-continuous-at)
(sc-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((memq (car g) '(IS-METRIC-SPACE IN)) (ass))
      (else
       (let ((eps (cadr (sc-di-landed-1!))))
         ;; Suppose no delta works at this eps.
         (pbc)
         (push-not-h (car (dk-asms)))
         (let* ((negK (car (dk-asms)))
                (P  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (sb-body eps 'k_))))
                (XS (list 'VNB-LAMBDA 'k_ 'NN (sb-c eps 'k_))))
           ;; (1) at every scale 1/(k+1) the witness set is inhabited, so the
           ;; chosen point has both properties.  GLOBAL CHOICE (choice-axiom,
           ;; primitive) -- the same idiom as CENTRES (compactness.scm) and the
           ;; fibre of ord-no-injection.
           (have! P
             (lambda ()
               (let ((kk (cadr (sc-di-landed-1!))))
                 (fact 'nn-recip-succ-pos kk)
                 ;; LUTINS instantiation (2026-09-18): both citations below are
                 ;; AT the radius recip(kk+1), which owes (= t t) unless the
                 ;; context types it -- the owed-leaf hook runs `in-rr', and
                 ;; `in-rr' cannot type a reciprocal.  POS-RR of it is the line
                 ;; above, and sb-rr-parts! reads (IN _ RR) off that.
                 (sb-rr-parts! (sb-r kk))
                 (dk-deepest (lambda () (inst+ negK (sb-r kk))))
                 (let* ((exb (dk-deepest
                              (lambda () (fact 'not-continuous-witness
                                               sb-s sb-t sb-f sb-a eps (sb-r kk)))))
                        (b0 (sc-skolem! exb)))
                   (for-each (lambda (x) (if (and (pair? x) (eq? (car x) 'AND)) (dk-split! x)))
                             (choose! (sb-W eps kk) b0
                                      (lambda () (in-sep! (lambda () (ass))
                                                          (lambda () (sc-and! (lambda () (ass))))))))
                   (sc-and! (lambda () (ass)))))))
           ;; (2) the chosen points form a sequence
           (have! (list 'IN XS (list 'FUN 'NN sb-Ps))
             (lambda ()
               (dk-lam-t!)
               (let ((kk (cadr (sc-di-landed-1!))))
                 (dk-split! (inst*! P kk))
                 (ass))))
           ;; (3) ... which converges to a: 1/(n+1) <= 1/(N+1) < eps'
           (have! (list 'CONVERGES-TO sb-s XS sb-a)
             (lambda ()
               (mac 'converges-to)
               (sc-and!
                (lambda ()
                  (let ((g2 (dk-goal)))
                    (cond
                     ((memq (car g2) '(IS-METRIC-SPACE IN)) (ass))
                     (else
                      (let* ((ep2 (cadr (sc-di-landed-1!)))
                             (nx (dk-deepest (lambda () (fact 'nn-recip-succ-small ep2))))
                             (bigN (sc-skolem! nx)))
                        (ew bigN)
                        (sc-and!
                         (lambda ()
                           (if (eq? (car (dk-goal)) 'IN) (ass)
                               (let ((n_ (cadr (sc-di-landed-1!))))
                                 (sc-di-landed!)                    ; N <= n_
                                 (lam-b)                            ; XS(n_) = the chosen point
                                 (dk-split! (inst*! P n_))
                                 (let ((cc (sb-c eps n_)))
                                   (fact 'metric-sym sb-s cc sb-a)
                                   (have! (list '<= (list sb-Ds cc sb-a) (sb-r n_))
                                          (lambda ()
                                            (subst (list '= (list sb-Ds cc sb-a)
                                                            (list sb-Ds sb-a cc)))
                                            (ass)))
                                   (fact 'nn-recip-succ-antitone bigN n_)
                                   (fact 'metric-dist-real sb-s cc sb-a)
                                   (fact 'nn-recip-succ-pos n_)
                                   (fact 'nn-recip-succ-pos bigN)
                                   (sb-rr-parts! (sb-r n_))
                                   (sb-rr-parts! (sb-r bigN))
                                   (sb-rr-parts! ep2)
                                   (sc-ineq (list '<= (list sb-Ds cc sb-a) (sb-r n_))
                                            (list '<= (sb-r n_) (sb-r bigN))
                                            (list '< (sb-r bigN) ep2)))))))))))))))
           ;; (4) so the hypothesis applies to it, and the image converges to f(a)
           (have! (list 'IN XS (list 'SQN sb-Ps)) (lambda () (mac 'sqn-membership) (ass)))
           (let* ((conv2 (dk-deepest (lambda () (inst+ sb-H XS)))))
             (dk-split! (dk-landed-find (lambda () (mac-h 'converges-to conv2))
                                        (lambda (x) (eq? (car x) 'AND))))
             (let* ((tail2 (sc-find 'tail2
                            (lambda (x) (and (eq? (car x) 'FORALL) (dk-contains? x 'COMPOSE)))))
                    (nx2 (dk-deepest (lambda () (inst+ tail2 eps))))
                    (bigN2 (sc-skolem! nx2))
                    (inner2 (sc-find 'inner2
                             (lambda (x) (and (eq? (car x) 'FORALL) (dk-contains? x bigN2)))))
                    (xn (list XS bigN2)))
               (fact 'nn-le-refl bigN2)
               (inst+ inner2 bigN2)              ; d(t)((f o XS)(N2), f(a)) <= eps
               (sc-and2! (list 'IN XS (list 'FUN 'NN sb-Ps))
                         (list 'IN sb-f (list 'FUN sb-Ps sb-Pt)))
               (fact 'compose-apply 'NN sb-Ps sb-Pt sb-f XS bigN2)
               (fact 'fun-apply-type-c XS 'NN sb-Ps bigN2)
               (fact 'fun-apply-type-c sb-f sb-Ps sb-Pt xn)
               (fact 'fun-apply-type-c sb-f sb-Ps sb-Pt sb-a)
               ;; the estimate, at the point the sequence was built to refute it
               (have! (list '<= (list sb-Dt (list sb-f sb-a) (list sb-f xn)) eps)
                 (lambda ()
                   (fact 'metric-sym sb-t (list sb-f sb-a) (list sb-f xn))
                   (subst (list '= (list sb-Dt (list sb-f sb-a) (list sb-f xn))
                                   (list sb-Dt (list sb-f xn) (list sb-f sb-a))))
                   (subst (sc-rev! (list '= (list (list 'COMPOSE sb-f XS) bigN2)
                                            (list sb-f xn))))
                   (ass)))
               (lam-b-h (list '<= (list sb-Dt (list sb-f sb-a) (list sb-f xn)) eps))
               (dk-split! (inst*! P bigN2))
               (ai (list 'NOT (list '<= (list sb-Dt (list sb-f sb-a)
                                             (list sb-f (sb-c eps bigN2))) eps))))))))))))
(qed 'sequential-implies-continuous-at)
(topic! 'sequential-implies-continuous-at 'analysis)
(alias! 'sequential-implies-continuous-at
        "sequential continuity at a point implies continuity there")

;;; =====================================================================
;;; L6.  continuous-at-iff-sequential -- the two halves, assembled by `prop'.
;;; `prop' treats both sides as opaque atoms, which is all the assembly needs,
;;; and discharges through the kernel rules, so it costs no trust.
;;; =====================================================================

(sp "forall([s, t, f, a], is-metric-space(s) implies is-metric-space(t) implies f in fun(pts(s), pts(t)) implies a in pts(s) implies (is-continuous-at(s, t, f, a) iff forall([sq in sqn(pts(s))], converges-to(s, sq, a) implies converges-to(t, compose(f, sq), f(a)))))")
(sc-peel-to! 'IFF)
(define sb2-g (dk-goal))
(define sb2-s (cadr (cadr sb2-g)))
(define sb2-t (caddr (cadr sb2-g)))
(define sb2-f (cadddr (cadr sb2-g)))
(define sb2-a (car (cddddr (cadr sb2-g))))
;; each citation inside its own `have!' lane: `fact' lands its whole
;; instantiation chain, and `prop' counts the atoms of the WHOLE context --
;; cited in the main branch the two chains put it over *prop-atom-cap*.
(have! (list 'IMPLIES (cadr sb2-g) (caddr sb2-g))
       (lambda () (fact 'continuous-at-implies-sequential sb2-s sb2-t sb2-f sb2-a) (ass)))
(have! (list 'IMPLIES (caddr sb2-g) (cadr sb2-g))
       (lambda () (fact 'sequential-implies-continuous-at sb2-s sb2-t sb2-f sb2-a) (ass)))
(prop)
(qed 'continuous-at-iff-sequential)
(topic! 'continuous-at-iff-sequential 'analysis)
(alias! 'continuous-at-iff-sequential
        "continuity at a point is sequential continuity there")
