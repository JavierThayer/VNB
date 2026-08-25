;;; product-weights.scm -- ANY TWO SUMMABLE WEIGHT SEQUENCES GIVE THE SAME
;;; TOPOLOGY ON THE COUNTABLE PRODUCT, proven -- retiring the asserted
;;; `product-weights-equivalent' of structure-library/product-metric.scm, the
;;; last statement of that file about the product's topology.
;;;
;;;   the identity  PRODUCT-METRIC-W(ms,w) -> PRODUCT-METRIC-W(ms,w2)
;;;   is continuous, in both directions.
;;;
;;; IT IS `product-convergence-coordinatewise' TWICE AND NOTHING ELSE, which is
;;; what the retired warrant said -- but the statement is about CONTINUITY and
;;; everything provable about the product metric is about CONVERGENCE, and until
;;; 2026-08-23 nothing crossed between them.  `continuous-at-iff-sequential'
;;; (theorem-library/sequential-continuity.scm) is that crossing; this file is
;;; its first customer.  The route, at a point a of the common carrier:
;;;
;;;   sq -> a in w   =>  coordinatewise         (rung 4, forward, at w)
;;;                  =>  sq -> a in w2          (rung 4, backward, at w2)
;;;                  =>  COMPOSE(id, sq) -> a   (converges-to-transfer)
;;;
;;; and `sequential-implies-continuous-at' turns that into IS-CONTINUOUS-AT.
;;;
;;; THE TWO CARRIERS ARE ONE SET, AND THAT IS THE WHOLE REASON THE IDENTITY IS
;;; EVEN TYPED.  PTS(PRODUCT-METRIC-W(ms,w)) == PRODUCT-CARRIER(ms) for EVERY w
;;; (`product-metric-carrier', product-summable.scm) -- the weights change the
;;; distance, never the points.  So `(VNB-LAMBDA x PTS(P_w). x)' is a member of
;;; FUN(PTS(P_w), PTS(P_w2)), and the proof of that is one `mac' in each
;;; direction.  The equation is used four more times below, to move a sequence
;;; and a limit between the two PTS spellings and the PRODUCT-CARRIER spelling
;;; that rung 4 is stated in.  Note the DIRECTION: the macete rewrites
;;; PTS(...) -> PRODUCT-CARRIER(...), so it fires with `mac' on a goal that
;;; mentions PTS and with `mac-h' on a hypothesis that does -- never the
;;; reverse, and a `mac' aimed the wrong way is a silent no-op.
;;;
;;; THE SETHOOD LEAF.  `lam-t' on the identity owes (IN PTS(P_w) SET), and
;;; `dk-set-close!' (driver-kit.scm) knows NN, RR, ZZ, QQ, CC, intervals and
;;; cartesian products -- not the carrier of an arbitrary metric space.  It
;;; falls through to `ass', so the obligation is met by having the fact IN THE
;;; CONTEXT first: it is a typing conjunct of IS-METRIC-SPACE, landed here on a
;;; `have!' lane because `mac-h' on IS-METRIC-SPACE(P_w) would DELETE the
;;; predicate the sibling conjuncts of IS-CONTINUOUS still cite.
;;;
;;; WHAT IT COSTS.  The bill is rung 4's, plus `compose-type' and
;;; `compose-apply' (structure-library/compose.scm, both warranted `proof') and
;;; `nn-recip-succ-pos' / `nn-recip-succ-small' inherited through
;;; `sequential-implies-continuous-at'.  Nothing new is asserted here.
;;;
;;; Loads after theorem-library/product-convergence (rungs 4 and the
;;; converges-to-transfer it carries), sequential-continuity
;;; (sequential-implies-continuous-at), product-summable
;;; (product-metric-carrier), structure-library/compose and sqn.

;;; ---- file-local driver helpers (the `pw-' prefix) ---------------------
;;; shared file-local driver helpers for the product-convergence work (pw-)
(define (pw-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (pw-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (pw-and2! a b) (have! (list 'AND a b) (lambda () (pw-and! (lambda () (ass))))))
(define (pw-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "pw-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (pw-ineq . forms) (apply ineq (map pw-idx forms)))
(define (pw-eq! e) (have! e (lambda () (crs))) (subst e))
(define (pw-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "pw-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))
(define (pw-fvs forms) (apply append (map free-vars forms)))
(define (pw-skolem! ex)
  (let* ((fv0 (pw-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (pw-fvs (dk-asms)))))
      (if (null? fresh) (error "pw-skolem!: nothing appeared" ex) (car fresh)))))
(define (pw-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "pw-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (pw-di-landed-1!)
  (let ((new (pw-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "pw-di-landed-1!: expected 1" (map expression->string new)))))
(define (pw-peel-to! head)
  (let lp ((k 0))
    (if (and (< k 16) (not (eq? (car (dk-goal)) head)))
        (begin (di) (lp (+ k 1))))))
(define (pw-split-h! name form)
  (dk-split! (dk-landed-find (lambda () (mac-h name form))
                             (lambda (f) (eq? (car f) 'AND)))))
(define (pw-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))
(define (pw-has-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA)) #t)
        (else (any-pred pw-has-redex? e))))
(define (pw-beta!)
  (let lp ((n 0))
    (if (and (< n 8) (pw-has-redex? (dk-goal)))
        (begin (lam-b) (lp (+ n 1))))))
(define (pw-converges-to! eps-branch)
  (mac 'converges-to)
  (pw-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
             ((eq? (car gl) 'IN) (slot 'PTS) (ass))
             (else (eps-branch)))))))
;;; (IN x TY) where TY mentions PTS(RR-MS): prove it from the RR form by `slot'.
(define (pw-pts-rr! ty x) (have! (list 'IN x ty) (lambda () (slot 'PTS) (ass))))
(define pw-fun-pts-rr '(FUN NN (PTS RR-MS)))
;; the two conjuncts of a context (< a b), landed WITHOUT destroying it
(define (pw-from-lt! a b)
  (let ((lt (list '< a b)))
    (for-each
     (lambda (part)
       (have! part (lambda ()
                     (dk-split! (dk-landed-find (lambda () (mac-h '< lt))
                                                (lambda (f) (eq? (car f) 'AND))))
                     (ass))))
     (list (list '<= a b) (list 'NOT (list '= a b))))))

;;; The two universals inside IS-MS-SEQUENCE and SUMMABLE-WEIGHT, landed
;;; WITHOUT destroying either predicate: `mac-h' REPLACES the assumption it
;;; unfolds, and both are antecedents that later citations still detach on.
(define pw-msu #f) (define pw-wpos #f)
(define (pw-setup! wv msv)
  (set! pw-msu (list 'FORALL 'nx_ (list 'IMPLIES '(IN nx_ NN)
                                        (list 'IS-METRIC-SPACE (list msv 'nx_)))))
  (set! pw-wpos (list 'FORALL 'nx_ (list 'IMPLIES '(IN nx_ NN)
                                         (list '< 0 (list wv 'nx_)))))
  (have! pw-msu (lambda () (mac-h 'is-ms-sequence (list 'IS-MS-SEQUENCE msv)) (ass)))
  (for-each
   (lambda (claim)
     (have! claim (lambda ()
                    (pw-split-h! 'summable-weight (list 'SUMMABLE-WEIGHT wv))
                    (ass))))
   (list pw-wpos (list 'IN wv '(FUN NN RR)) (list 'SERIES-CONVERGES wv))))

;;; =====================================================================
;;; L8.  product-identity-continuous -- the identity P_w -> P_w2 is continuous.
;;; The whole content; L9 is this twice.
;;; =====================================================================
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
   (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
     (FORALL w2 (IMPLIES (SUMMABLE-WEIGHT w2)
       (IS-CONTINUOUS (PRODUCT-METRIC-W ms w) (PRODUCT-METRIC-W ms w2)
                      (VNB-LAMBDA x (PTS (PRODUCT-METRIC-W ms w)) x))))))))))
(pw-peel-to! 'IS-CONTINUOUS)
(define pw-g   (dk-goal))
(define pw-p1  (cadr pw-g))
(define pw-p2  (caddr pw-g))
(define pw-id  (cadddr pw-g))
(define pw-ms  (cadr pw-p1))
(define pw-w   (caddr pw-p1))
(define pw-w2  (caddr pw-p2))
(define pw-pc  (list 'PRODUCT-CARRIER pw-ms))
(define pw-c1  (list 'PTS pw-p1))
(define pw-c2  (list 'PTS pw-p2))

(fact 'product-is-metric-space pw-ms pw-w)
(fact 'product-is-metric-space pw-ms pw-w2)
;; (IN (PTS P1) SET) -- a typing conjunct of IS-METRIC-SPACE, on a side lane
;; because `mac-h' would delete the predicate the branches still cite.
(have! (list 'IN pw-c1 'SET)
  (lambda () (pw-split-h! 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE pw-p1)) (ass)))
;; the identity IS a map P1 -> P2: both carriers ARE PRODUCT-CARRIER(ms).
(have! (list 'IN pw-id (list 'FUN pw-c1 pw-c2))
  (lambda ()
    (dk-lam-t!)
    (let ((x (cadr (pw-di-landed-1!))))
      (mac-h 'product-metric-carrier (list 'IN x pw-c1))
      (mac 'product-metric-carrier)
      (ass))))

(mac 'is-continuous)
(pw-and!
 (lambda ()
   (let ((g (dk-goal)))
     (if (memq (car g) '(IS-METRIC-SPACE IN)) (ass)
      (let ((a (cadr (pw-di-landed-1!))))
        (have! (list 'IN a pw-pc)
          (lambda () (mac-h 'product-metric-carrier (list 'IN a pw-c1)) (ass)))
        (have! (list 'IN a pw-c2)
          (lambda () (mac 'product-metric-carrier) (ass)))
        (have!
         (list 'FORALL 'sq_ (list 'IMPLIES (list 'IN 'sq_ (list 'SQN pw-c1))
           (list 'IMPLIES (list 'CONVERGES-TO pw-p1 'sq_ a)
             (list 'CONVERGES-TO pw-p2 (list 'COMPOSE pw-id 'sq_) (list pw-id a)))))
         (lambda ()
           (let* ((land (pw-peel-to! 'CONVERGES-TO))
                  (sqv  (cadr (pw-find 'sqtyping
                          (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                           (pair? (caddr f))
                                           (eq? (car (caddr f)) 'SQN)))))))
             (have! (list 'IN sqv (list 'FUN 'NN pw-c1))
               (lambda () (mac-h 'sqn-membership (list 'IN sqv (list 'SQN pw-c1)))
                       (ass)))
             (have! (list 'IN sqv (list 'FUN 'NN pw-pc))
               (lambda () (mac-h 'sqn-membership (list 'IN sqv (list 'SQN pw-c1)))
                       (mac-h 'product-metric-carrier (list 'IN sqv (list 'FUN 'NN pw-c1)))
                       (ass)))
             (have! (list 'IN sqv (list 'FUN 'NN pw-c2))
               (lambda () (mac 'product-metric-carrier) (ass)))
             ;; the two rungs: out of the w-product, into the w2-product
             (fact 'product-convergence-coordinatewise-fwd pw-ms pw-w sqv a)
             (fact 'product-convergence-coordinatewise-bwd pw-ms pw-w2 sqv a)
             ;; the image sequence is the sequence
             (pw-and2! (list 'IN sqv (list 'FUN 'NN pw-c1))
                       (list 'IN pw-id (list 'FUN pw-c1 pw-c2)))
             ;; compose-type's (IN A SET) guard, A = NN here
             (fact 'nn-is-set)
             (fact 'compose-type 'NN pw-c1 pw-c2 pw-id sqv)
             (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
                       (list '= (list (list 'COMPOSE pw-id sqv) 'j_) (list sqv 'j_))))
               (lambda ()
                 (let ((j (cadr (pw-di-landed-1!))))
                   (fact 'fun-apply-type-c sqv 'NN pw-c1 j)
                   (fact 'compose-apply 'NN pw-c1 pw-c2 pw-id sqv j)
                   (subst (list '= (list (list 'COMPOSE pw-id sqv) j)
                                   (list pw-id (list sqv j))))
                   (pw-beta!)
                   (rfl))))
             (fact 'converges-to-transfer pw-p2 sqv (list 'COMPOSE pw-id sqv) a)
             (pw-beta!)
             (ass))))
        (fact 'sequential-implies-continuous-at pw-p1 pw-p2 pw-id a)
        (ass))))))
(qed 'product-identity-continuous)

;;; =====================================================================
;;; L9.  product-weights-equivalent -- THE HEADLINE.  Statement VERBATIM from
;;; the support this file retires (structure-library/product-metric.scm).  It
;;; is L8 twice, at (w, w2) and at (w2, w), and nothing else.
;;; =====================================================================
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
       (FORALL w2 (IMPLIES (SUMMABLE-WEIGHT w2)
         (AND (IS-CONTINUOUS (PRODUCT-METRIC-W ms w) (PRODUCT-METRIC-W ms w2)
                             (VNB-LAMBDA x (PTS (PRODUCT-METRIC-W ms w)) x))
              (IS-CONTINUOUS (PRODUCT-METRIC-W ms w2) (PRODUCT-METRIC-W ms w)
                             (VNB-LAMBDA x (PTS (PRODUCT-METRIC-W ms w2)) x)))))))))))
(pw-peel-to! 'AND)
(pw-and!
 (lambda ()
   (let* ((g (dk-goal)) (src (cadr g)) (tgt (caddr g)))
     (fact 'product-identity-continuous (cadr src) (caddr src) (caddr tgt))
     (ass))))
(qed 'product-weights-equivalent)

;;; -----------------------------------------------------------------------
(topic! 'product-identity-continuous 'constructions)
(alias! 'product-identity-continuous
        "the identity between two weightings of a product is continuous")
(topic! 'product-weights-equivalent 'constructions)
(alias! 'product-weights-equivalent
        "the product topology does not depend on the weights"
        "any two summable positive weight sequences give topologically equivalent product metrics")
