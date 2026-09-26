;;; cc-reciprocal.scm -- z |-> 1/z: the punctured plane, the continuity of the
;;; reciprocal, its derivative, and the reciprocal and quotient rules for
;;; HOLOMORPHIC-ON.
;;;
;;; THE NOTES.  Section 2.1 of ~/docs/complex-analysis.pdf states the algebra of
;;; the complex derivative as Proposition 2.2 (differentiable implies
;;; continuous), Proposition 2.3 (sum and product) and Proposition 2.4 (the
;;; chain rule), prefaced by "The complex derivative satisfies the same
;;; algebraic rules as the ordinary derivative of calculus".  The quotient rule
;;; is NOT stated there -- it is used later, at (74), as "the quotient rule for
;;; derivatives" -- so the statement below is the one Proposition 2.3's shape
;;; dictates, with the hypothesis the notes always attach to a quotient: the
;;; denominator does not vanish.  The chain rule is the notes' 2.4, already in
;;; the tree as `diff-on-chain'.
;;;
;;; THE SET.  The library writes a relative complement as DIFFERENCE(A, B)
;;; (structure-library/set-vocabulary.scm), and a punctured carrier as
;;; DIFFERENCE(CARR, SINGLETON(ZERO)) -- exactly as IS-FIELD's NON-ZERO slot
;;; does (structure-library/field.scm) and as QQ-FIELD instantiates it.  So the
;;; domain of the reciprocal is
;;;
;;;     CCNZ  =  DIFFERENCE(CC, SINGLETON(0)),
;;;
;;; and `cc-nonzero-membership' below is the one read-off everything else uses:
;;; z in CCNZ iff z in CC and z /= 0.  NO STRICT EQUATION ANYWHERE MENTIONS
;;; recip(0): `recip' is partial (cc-recip-closed and cc-recip-inverse,
;;; number-systems.scm, are both guarded on a /= 0), so the reciprocal map is
;;; built as a lambda over CCNZ and never over CC.
;;;
;;; THE TWO SPACES.  IS-DIFF-ON(K, U, f, a, L) asks for U open in
;;; NF-METRIC-SPACE(K) and for the Caratheodory factor to be continuous as a map
;;; SUBSPACE-MS(NF-METRIC-SPACE(K), U) -> NF-METRIC-SPACE(K).  Every other
;;; complex statement in the library says CC-MS.  `cc-ms-open-iff'
;;; (theorem-library/holomorphic-basics.scm) is the single citation between the
;;; two readings of openness (`cc-nonzero-open-nf' is that citation), and
;;; `nf-cc-agree-dist' together with `cc-ms-dist' the bridge between the two
;;; distances -- the pair used, in `ccr-dist-facts!', wherever an estimate has to
;;; be read as a MODULUS.
;;;
;;; THE ESTIMATE, and what makes it short.  It is the complex mirror of
;;; `recip-continuous-at' (theorem-library/continuity-recip.scm), whose trick is
;;; to bound NO reciprocal at all.  With c the centre, z the varying point,
;;; D = |1/c - 1/z| and M = |c| > 0:
;;;
;;;     (1/c - 1/z) . (c.z)  =  z - c
;;;
;;; is a commutative-ring identity of CC in the opaque generators recip(c),
;;; recip(z) once c.recip(c) = 1 and z.recip(z) = 1 collapse (`crs' certifies
;;; each generator from its (IN . CC) typing).  `cc-magnitude-mul' twice gives
;;; D . (M . |z|) = |z - c|.  Halving M = m + m, the reverse triangle inequality
;;; in the form `cc-magnitude-le-add' (|c| <= |c - z| + |z|) forces |z| >= m
;;; inside the ball of radius w <= m, so with also w <= eps.(M.m),
;;;
;;;     D . K  <=  D . (M.|z|)  =  |z - c|  <=  w  <=  eps . K,     K = M.m > 0,
;;;
;;; and `rr-nonneg-cancel-pos' strips K.  No modulus of a reciprocal is ever
;;; needed, and no new lemma is minted: |recip u| = recip |u| does not exist in
;;; the tree and is not wanted.
;;;
;;; NOT HERE: the quotient rule WITH the derivative, (f'g - fg')/g^2.  The two
;;; ingredients are in place (`diff-on-recip-cc' gives (1/g)' = -g'/g^2 and
;;; `diff-on-product' the Leibniz rule), and what is left is the CC ring
;;; identity that collects the two terms over the common denominator; the
;;; HOLOMORPHIC-ON form, which is what batch 15 asked for, does not need it.
;;;
;;; WHAT IT COSTS.  Every theorem here is `modulo 0'.  In particular NOTHING
;;; goes through `normed-field-mul-inverses' or `normed-field-zero-not-one'
;;; (both asserted): the inverse facts used are `cc-recip-closed' and
;;; `cc-recip-inverse', which are in the PRIMITIVE arithmetic base
;;; (number-systems.scm:684, :689) and contribute {} to every bill.
;;;
;;; Helper prefix: `ccr-'.
;;;
;;; LOAD WINDOW.  lo = theorem-library/holomorphic-basics-2 (load.scm line 2874:
;;; holomorphic-transfer-ptwise-eq, holomorphic-const, holomorphic-product),
;;; which itself sits after diff-on-laws-2 (diff-on-chain, nf-mul-cancel,
;;; ms-cont-transfer-on, nf-product-continuous-on, nf-open-is-set) and
;;; holomorphic-basics (cc-ms-open-iff, cc-nf-add-apply/-mul-apply/-neg-apply,
;;; nf-cc-agree-pts/-dist).  Everything else is far below: cc-magnitude (2121),
;;; difference-laws (951), metric-subspace-laws (1395), number-systems,
;;; rr-order-basics, rr-halving.  hi: none -- nothing cites these names yet.
;;; Proposed slot: the line immediately after "theorem-library/holomorphic-basics-2".

;;; =====================================================================
;;; File-local driver helpers.
;;; =====================================================================

(define (ccr-head e) (and (pair? e) (car e)))

(define ccr-nz '(DIFFERENCE CC (SINGLETON 0)))
(define ccr-k  'CC-NORMED-FIELD)
(define ccr-m  '(NF-METRIC-SPACE CC-NORMED-FIELD))
(define ccr-w  '(SUBSPACE-MS (NF-METRIC-SPACE CC-NORMED-FIELD)
                             (DIFFERENCE CC (SINGLETON 0))))
(define ccr-rl '(VNB-LAMBDA crz_ (DIFFERENCE CC (SINGLETON 0)) (recip crz_)))

(define (ccr-find what p)
  (let lp ((l (dk-asms)))
    (cond ((null? l) (error "ccr-find: no context formula" what))
          ((p (car l)) (car l))
          (#t (lp (cdr l))))))

(define (ccr-idx f)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ccr-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (#t (lp (cdr l) (+ i 1))))))
(define (ccr-ineq . fs) (apply ineq (map ccr-idx fs)))

(define (ccr-check name)
  (if (not (proof-done? *ps*))
      (error "cc-reciprocal: proof did not close" name
             (expression->string (dk-goal)))))

;;; t in RR and 0 < t  ==>  POS-RR(t) in context.
(define (ccr-pos! t)
  (fact 'rr-lt-implies-le 0 t)
  (fact 'rr-pos-ne-zero t)
  (fact 'neq-sym t 0)
  (dk-have! (list 'POS-RR t) (lambda () (mac 'pos-rr) (from-context!))))

;;; POS-RR(t) in context ==> (IN t RR) and (< 0 t), BY CITATION (`mac-h' would
;;; consume the POS-RR, which the eps-universals still detach against).
(define (ccr-open-pos! t)
  (fact 'rr-pos-rr-in-rr t)
  (fact 'rr-lt-of-pos-rr t))

;;; z in CCNZ  ==>  (IN z CC) and (NOT (= z 0)) in context.
(define (ccr-nonzero-parts! z)
  (fact 'cc-nonzero-membership z)
  (dk-have! (list 'IN z 'CC) (lambda () (prop)))
  (dk-have! (list 'NOT (list '= z 0)) (lambda () (prop))))

;;; 0 < magnitude(z), from z in CC and z /= 0 (both already in context).
(define (ccr-mag-pos! z)
  (let ((mg (list 'magnitude z)))
    (fact 'cc-magnitude-closed z)
    (fact 'cc-magnitude-nonneg z)
    (fact 'cc-magnitude-zero-iff z)
    (dk-have! (list 'NOT (list '= mg 0)) (lambda () (prop)))
    (fact 'neq-sym mg 0)
    (dk-have! (list 'AND (list '<= 0 mg) (list 'NOT (list '= 0 mg))))
    (fact 'rr-le-ne-lt 0 mg)
    mg))

;;; =====================================================================
;;; (1) THE PUNCTURED PLANE.
;;; =====================================================================

;;; z in CC \ {0}  iff  z in CC and z /= 0.  `singleton-membership' reads
;;; x in {y} iff x in SET and x = y -- a CONJUNCTION -- so the sethood half has
;;; to be supplied from (IN z CC) before `prop' can peel it.
(sp (make-wff (list 'FORALL 'crw_
      (list 'IFF (list 'IN 'crw_ ccr-nz)
                 '(AND (IN crw_ CC) (NOT (= crw_ 0)))))))
(di)
(fact 'difference-membership 'CC '(SINGLETON 0) 'crw_)
(fact 'singleton-membership 0 'crw_)
(fact 'membership-implies-sethood 'crw_ 'CC)
(prop)
(ccr-check 'cc-nonzero-membership)
(qed 'cc-nonzero-membership)
(topic! 'cc-nonzero-membership 'analysis)
(alias! 'cc-nonzero-membership
        "a complex number is in the punctured plane iff it is nonzero")

(sp (make-wff (list 'SUBSET ccr-nz 'CC)))
(mac 'subset-def)
(let ((z (dk-di-var!)))
  (fact 'cc-nonzero-membership z)
  (prop))
(ccr-check 'cc-nonzero-subset)
(qed 'cc-nonzero-subset)
(topic! 'cc-nonzero-subset 'analysis)
(alias! 'cc-nonzero-subset "the punctured plane is a subset of the complex numbers")

(sp (make-wff (list 'IN ccr-nz 'SET)))
(fact 'cc-is-set)
(fact 'difference-set 'CC '(SINGLETON 0))
(ass)
(ccr-check 'cc-nonzero-is-set)
(qed 'cc-nonzero-is-set)
(topic! 'cc-nonzero-is-set 'analysis)
(alias! 'cc-nonzero-is-set "the punctured plane is a set")

;;; =====================================================================
;;; (2) THE PUNCTURED PLANE IS OPEN.
;;;
;;; At y /= 0 take the radius m with m + m = |y|.  For z in the ball,
;;; |y| <= |y - z| + |z| <= m + |z| (cc-magnitude-le-add), so |z| >= m > 0 and
;;; z /= 0 by cc-magnitude-zero-iff.
;;; =====================================================================

(sp (make-wff (list 'IS-OPEN 'CC-MS ccr-nz)))
(fact 'cc-is-metric-space)
(dk-have! '(== (PTS CC-MS) CC) (lambda () (slot 'PTS) (qrfl)))
(fact 'cc-nonzero-subset)
(dk-have! (list 'SUBSET ccr-nz '(PTS CC-MS))
          (lambda () (subst '(== (PTS CC-MS) CC)) (ass)))
(mac 'IS-OPEN)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (ccr-head (dk-goal)) 'FORALL))
       (ass)
       (let* ((y  (dk-di-var!))
              (my (begin (ccr-nonzero-parts! y) (ccr-mag-pos! y))))
         (ccr-pos! my)
         (let ((m (dk-skolem! (dk-fact! 'rr-pos-halvable my))))
           (dk-split-all!)
           (ccr-open-pos! m)
           (ew m)
           (dk-conj-close!
            (lambda ()
              (if (not (eq? (ccr-head (dk-goal)) 'SUBSET))
                  (ass)
                  (begin
                    (mac 'subset-def)
                    (let ((z (dk-di-var!)))
                      (fact 'ball-membership 'CC-MS y m z)
                      (dk-have! (list 'IN z '(PTS CC-MS)) (lambda () (prop)))
                      (dk-have! (list 'IN z 'CC)
                                (lambda () (subst '(== CC (PTS CC-MS))) (ass)))
                      (fact 'cc-ms-dist y z)
                      (dk-have! (list '<= (list '(DIST CC-MS) y z) m)
                                (lambda () (prop)))
                      (dk-have! (list '<= (list 'magnitude (list '- y z)) m)
                        (lambda ()
                          (subst (list '== (list 'magnitude (list '- y z))
                                            (list '(DIST CC-MS) y z)))
                          (ass)))
                      (fact 'cc-sub-in-cc y z)
                      (fact 'cc-magnitude-closed (list '- y z))
                      (fact 'cc-magnitude-closed z)
                      (fact 'cc-magnitude-nonneg z)
                      (fact 'cc-magnitude-le-add y z)
                      (dk-have! (list '< 0 (list 'magnitude z))
                        (lambda ()
                          (ccr-ineq
                           (list '<= (list 'magnitude y)
                                 (list '+ (list 'magnitude (list '- y z))
                                          (list 'magnitude z)))
                           (list '<= (list 'magnitude (list '- y z)) m)
                           (list '= (list '+ m m) my)
                           (list '< 0 m))))
                      (fact 'rr-pos-ne-zero (list 'magnitude z))
                      (fact 'cc-magnitude-zero-iff z)
                      (dk-have! (list 'NOT (list '= z 0)) (lambda () (prop)))
                      (fact 'cc-nonzero-membership z)
                      (prop)))))))))))
(ccr-check 'cc-nonzero-open)
(qed 'cc-nonzero-open)
(topic! 'cc-nonzero-open 'topology)
(alias! 'cc-nonzero-open "the punctured complex plane is open")

(sp (make-wff (list 'IS-OPEN ccr-m ccr-nz)))
(fact 'cc-nonzero-open)
(fact 'cc-ms-open-iff ccr-nz)
(prop)
(ccr-check 'cc-nonzero-open-nf)
(qed 'cc-nonzero-open-nf)
(topic! 'cc-nonzero-open-nf 'topology)
(alias! 'cc-nonzero-open-nf
        "the punctured complex plane is open in the normed field's metric")

;;; =====================================================================
;;; (3) THE RECIPROCAL IS A FUNCTION CCNZ -> CC.
;;; =====================================================================

;;; `lam-t' opens TWO leaves -- the pointwise typing of the body and the
;;; SETHOOD of the domain.  They are taken as `dk-opened' hands them over
;;; (`dk-lam-t!' would send the sethood leaf to `dk-set-close!', which knows
;;; nothing about DIFFERENCE).
(sp (make-wff (list 'IN ccr-rl (list 'FUN ccr-nz 'CC))))
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (let ((g (dk-goal)))
     (cond ((equal? g (list 'IN ccr-nz 'SET))
            (fact 'cc-nonzero-is-set) (ass))
           ((eq? (ccr-head g) 'FORALL)
            (let ((z (dk-di-var!)))
              (ccr-nonzero-parts! z)
              (dk-have! (list 'AND (list 'IN z 'CC) (list 'NOT (list '= z 0))))
              (fact 'cc-recip-closed z)
              (ass)))
           (#t (error "cc-reciprocal: unexpected lam-t leaf"
                      (expression->string g))))))
 (dk-opened (lambda () (lam-t))))
(ccr-check 'cc-recip-lam-in-fun)
(qed 'cc-recip-lam-in-fun)
(topic! 'cc-recip-lam-in-fun 'analysis)
(alias! 'cc-recip-lam-in-fun
        "the reciprocal is a function from the punctured plane to the complex numbers")

;;; =====================================================================
;;; (4) THE RECIPROCAL IS CONTINUOUS AT EVERY NONZERO POINT.
;;;
;;; As a map SUBSPACE-MS(NF-METRIC-SPACE(CC-NORMED-FIELD), CCNZ) ->
;;; NF-METRIC-SPACE(CC-NORMED-FIELD) -- the exact shape IS-DIFF-ON's
;;; Caratheodory factor is asked for, so the derivative below cites this once
;;; and rewrites nothing.
;;; =====================================================================

;;; `di' until something lands: a universal guarded by a PREDICATE (POS-RR)
;;; lands nothing on the call that peels it.
(define (ccr-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "ccr-di-landed!: nothing landed"))
            (#t (loop (+ n 1)))))))

(define (ccr-pts-cc-ms!)
  (dk-have! '(== (PTS CC-MS) CC) (lambda () (slot 'PTS) (qrfl))))

;;; ((DIST (NF-METRIC-SPACE CC-NORMED-FIELD)) u v) == magnitude(u - v), for u, v
;;; typed in CC: the two agreement citations, landed for later `subst'.
(define (ccr-dist-facts! u v)
  (dk-have! (list 'IN u '(PTS CC-MS)) (lambda () (subst '(== (PTS CC-MS) CC)) (ass)))
  (dk-have! (list 'IN v '(PTS CC-MS)) (lambda () (subst '(== (PTS CC-MS) CC)) (ass)))
  (fact 'nf-cc-agree-dist u v)
  (fact 'cc-ms-dist u v))

(define ccr-mm #f) (define ccr-half #f) (define ccr-kk #f)

;;; ---- the inner estimate ---------------------------------------------

(define (ccr-inner! eps wv)
  (let* ((landed (ccr-di-landed!))
         (mem    (or (find-first (lambda (u) (and (pair? u) (eq? (car u) 'IN))) landed)
                     (error "ccr-inner!: no membership landed")))
         (b      (cadr mem)))
    (if (not (find-first (lambda (u) (and (pair? u) (eq? (car u) '<=))) landed))
        (ccr-di-landed!))
    (let* ((a    'cra_)
           (ra   (list 'recip a))
           (rb   (list 'recip b))
           (dif  (list '- ra rb))
           (dd   (list 'magnitude dif))
           (cz   (list '* a b))
           (mb   (list 'magnitude b))
           (mz   (list '* ccr-mm mb))
           (cctt (list '* eps ccr-kk)))
      (dk-have! (list 'IN b ccr-nz)
                (lambda () (subst (list '== ccr-nz (list 'PTS ccr-w))) (ass)))
      (ccr-nonzero-parts! b)
      ;; the hypothesis, read as a modulus
      (fact 'subspace-dist ccr-m ccr-nz a b)
      (ccr-dist-facts! a b)
      (fact 'cc-sub-in-cc a b)
      (fact 'cc-magnitude-closed (list '- a b))
      (dk-have! (list '<= (list 'magnitude (list '- a b)) wv)
        (lambda ()
          (subst (list '== (list 'magnitude (list '- a b))
                            (list (list 'DIST 'CC-MS) a b)))
          (subst (list '== (list (list 'DIST 'CC-MS) a b)
                            (list (list 'DIST ccr-m) a b)))
          (subst (list '== (list (list 'DIST ccr-m) a b)
                            (list (list 'DIST ccr-w) a b)))
          (ass)))
      ;; the goal, read as a modulus
      (dk-have! (list 'AND (list 'IN a 'CC) (list 'NOT (list '= a 0))))
      (fact 'cc-recip-closed a)
      (fact 'cc-recip-inverse a)
      (dk-have! (list 'AND (list 'IN b 'CC) (list 'NOT (list '= b 0))))
      (fact 'cc-recip-closed b)
      (fact 'cc-recip-inverse b)
      (dk-lam-b!)
      (ccr-dist-facts! ra rb)
      (subst (list '== (list (list 'DIST ccr-m) ra rb)
                        (list (list 'DIST 'CC-MS) ra rb)))
      (subst (list '== (list (list 'DIST 'CC-MS) ra rb) dd))
      ;; |b| >= m
      (fact 'cc-magnitude-closed b)
      (fact 'cc-magnitude-nonneg b)
      (fact 'cc-magnitude-le-add a b)
      (dk-have! (list '<= ccr-half mb)
        (lambda ()
          (ccr-ineq (list '<= ccr-mm (list '+ (list 'magnitude (list '- a b)) mb))
                    (list '<= (list 'magnitude (list '- a b)) wv)
                    (list '<= wv ccr-half)
                    (list '= (list '+ ccr-half ccr-half) ccr-mm))))
      ;; (1/a - 1/b) . (a.b) = b - a
      (fact 'cc-sub-in-cc ra rb)
      (dk-have! (list 'AND (list 'IN a 'CC) (list 'IN b 'CC)))
      (fact 'cc-mul-closed a b)
      (fact 'cc-sub-in-cc b a)
      (let ((expand (list '- (list '* (list '* a ra) b) (list '* (list '* b rb) a))))
        (dk-have! (list '= (list '* dif cz) (list '- b a))
          (lambda ()
            (dk-have! (list '= (list '* dif cz) expand) (lambda () (crs)))
            (subst (list '= (list '* dif cz) expand))
            (subst (list '= (list '* a ra) 1))
            (subst (list '= (list '* b rb) 1))
            (crs))))
      ;; D . (M . |b|) = |b - a|
      (dk-have! (list 'AND (list 'IN dif 'CC) (list 'IN cz 'CC)))
      (fact 'cc-magnitude-mul dif cz)
      (fact 'cc-magnitude-mul a b)
      (fact 'cc-magnitude-closed dif)
      (fact 'cc-magnitude-nonneg dif)
      (fact 'cc-magnitude-closed (list '- b a))
      (dk-have! (list '= (list '* dd mz) (list 'magnitude (list '- b a)))
        (lambda ()
          (fact 'eq-sym (list 'magnitude cz) mz)
          (subst (list '= mz (list 'magnitude cz)))
          (fact 'eq-sym (list 'magnitude (list '* dif cz)) (list '* dd (list 'magnitude cz)))
          (subst (list '= (list '* dd (list 'magnitude cz)) (list 'magnitude (list '* dif cz))))
          (subst (list '= (list '* dif cz) (list '- b a)))
          (rfl)))
      (fact 'cc-magnitude-sub-sym b a)
      (dk-have! (list '<= (list 'magnitude (list '- b a)) wv)
        (lambda ()
          (subst (list '= (list 'magnitude (list '- b a))
                          (list 'magnitude (list '- a b))))
          (ass)))
      ;; D . K <= D . (M . |b|) = |b - a| <= w <= eps . K
      (dk-have! (list 'AND (list 'IN ccr-mm 'RR) (list 'IN mb 'RR)))
      (fact 'rr-mul-closed ccr-mm mb)
      (dk-have! (list 'AND (list '<= 0 ccr-mm) (list '<= ccr-half mb)))
      (fact 'rr-le-scale-nonneg ccr-mm ccr-half mb)
      (dk-have! (list 'AND (list 'IN dd 'RR) (list 'IN ccr-kk 'RR)))
      (fact 'rr-mul-closed dd ccr-kk)
      (dk-have! (list 'AND (list 'IN dd 'RR) (list 'IN mz 'RR)))
      (fact 'rr-mul-closed dd mz)
      (dk-have! (list 'AND (list '<= 0 dd) (list '<= ccr-kk mz)))
      (fact 'rr-le-scale-nonneg dd ccr-kk mz)
      (dk-have! (list '<= (list '* dd ccr-kk) cctt)
        (lambda ()
          (ccr-ineq (list '<= (list '* dd ccr-kk) (list '* dd mz))
                    (list '= (list '* dd mz) (list 'magnitude (list '- b a)))
                    (list '<= (list 'magnitude (list '- b a)) wv)
                    (list '<= wv cctt))))
      ;; strip K
      (fact 'rr-sub-in-rr eps dd)
      (dk-have! (list 'AND (list 'IN ccr-kk 'RR) (list 'IN (list '- eps dd) 'RR)))
      (fact 'rr-mul-closed ccr-kk (list '- eps dd))
      (dk-have! (list '<= 0 (list '* ccr-kk (list '- eps dd)))
        (lambda ()
          (dk-have! (list '= (list '* ccr-kk (list '- eps dd))
                             (list '- cctt (list '* dd ccr-kk)))
                    (lambda () (crs)))
          (subst (list '= (list '* ccr-kk (list '- eps dd))
                           (list '- cctt (list '* dd ccr-kk))))
          (ccr-ineq (list '<= (list '* dd ccr-kk) cctt))))
      (fact 'rr-nonneg-cancel-pos ccr-kk (list '- eps dd))
      (ccr-ineq (list '<= 0 (list '- eps dd))))))

;;; ---- the eps lane ----------------------------------------------------

(define (ccr-eps!)
  (let* ((pos (car (ccr-di-landed!)))
         (eps (cadr pos))
         (cctt (list '* eps ccr-kk)))
    (ccr-open-pos! eps)
    (dk-have! (list 'AND (list 'IN eps 'RR) (list 'IN ccr-kk 'RR)))
    (fact 'rr-mul-closed eps ccr-kk)
    (fact 'rr-mul-pos eps ccr-kk)
    (let ((wv (dk-skolem! (dk-fact! 'rr-min-pos ccr-half cctt))))
      (dk-split-all!)
      (ccr-pos! wv)
      (ew wv)
      (dk-conj-close!
       (lambda ()
         (if (eq? (ccr-head (dk-goal)) 'FORALL)
             (ccr-inner! eps wv)
             (ass)))))))

(sp (make-wff (list 'FORALL 'cra_ (list 'IMPLIES (list 'IN 'cra_ ccr-nz)
      (list 'IS-CONTINUOUS-AT ccr-w ccr-m ccr-rl 'cra_)))))
(dk-peel!)
(fact 'cc-is-normed-field)
(fact 'nf-cc-is-metric-space)
(fact 'nf-metric-carrier ccr-k)
(fact 'cc-nf-carr)
(ccr-pts-cc-ms!)
(dk-have! (list '== (list 'PTS ccr-m) 'CC)
  (lambda () (subst (list '== (list 'PTS ccr-m) '(CARR CC-NORMED-FIELD))) (ass)))
(fact 'cc-nonzero-subset)
(dk-have! (list 'SUBSET ccr-nz (list 'PTS ccr-m))
  (lambda () (subst (list '== (list 'PTS ccr-m) 'CC)) (ass)))
(fact 'subspace-is-metric-space ccr-m ccr-nz)
(fact 'subspace-pts ccr-m ccr-nz)
(dk-have! (list 'IN 'cra_ (list 'PTS ccr-w))
  (lambda () (subst (list '== (list 'PTS ccr-w) ccr-nz)) (ass)))
(fact 'cc-recip-lam-in-fun)
(dk-have! (list 'IN ccr-rl (list 'FUN (list 'PTS ccr-w) (list 'PTS ccr-m)))
  (lambda () (subst (list '== (list 'PTS ccr-w) ccr-nz))
             (subst (list '== (list 'PTS ccr-m) 'CC))
             (ass)))
(ccr-nonzero-parts! 'cra_)
(set! ccr-mm (ccr-mag-pos! 'cra_))
(ccr-pos! ccr-mm)
(set! ccr-half (dk-skolem! (dk-fact! 'rr-pos-halvable ccr-mm)))
(dk-split-all!)
(ccr-open-pos! ccr-half)
(dk-have! (list 'AND (list 'IN ccr-mm 'RR) (list 'IN ccr-half 'RR)))
(fact 'rr-mul-closed ccr-mm ccr-half)
(fact 'rr-mul-pos ccr-mm ccr-half)
(set! ccr-kk (list '* ccr-mm ccr-half))
(mac 'is-continuous-at)
(dk-conj-close!
 (lambda ()
   (if (eq? (ccr-head (dk-goal)) 'FORALL) (ccr-eps!) (ass))))
(ccr-check 'cc-recip-continuous-at)
(qed 'cc-recip-continuous-at)
(topic! 'cc-recip-continuous-at 'analysis)
(alias! 'cc-recip-continuous-at
        "the reciprocal is continuous at every nonzero complex number")

;;; =====================================================================
;;; (5) TWO ARITHMETIC FACTS ABOUT THE RECIPROCAL IN CC.
;;;
;;; The complex numbers have no zero divisors, and the reciprocal is
;;; multiplicative.  Both go through `cc-recip-inverse' (PRIMITIVE) and `crs';
;;; neither touches a normed-field axiom.
;;; =====================================================================

(sp (make-wff
     '(FORALL ccu_ (IMPLIES (IN ccu_ CC)
        (FORALL ccv_ (IMPLIES (IN ccv_ CC)
          (IMPLIES (NOT (= ccu_ 0))
          (IMPLIES (NOT (= ccv_ 0))
                   (NOT (= (* ccu_ ccv_) 0))))))))))
(dk-peel!)
(dk-have! '(AND (IN ccu_ CC) (NOT (= ccu_ 0))))
(fact 'cc-recip-closed 'ccu_)
(fact 'cc-recip-inverse 'ccu_)
(dk-have! '(AND (IN ccv_ CC) (NOT (= ccv_ 0))))
(fact 'cc-recip-closed 'ccv_)
(fact 'cc-recip-inverse 'ccv_)
(dk-have! '(AND (IN ccu_ CC) (IN ccv_ CC)))
(fact 'cc-mul-closed 'ccu_ 'ccv_)
(dk-have! '(AND (IN (recip ccu_) CC) (IN (recip ccv_) CC)))
(fact 'cc-mul-closed '(recip ccu_) '(recip ccv_))
(dk-have! '(= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))) 1)
  (lambda ()
    (dk-have! '(= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_)))
                  (* (* ccu_ (recip ccu_)) (* ccv_ (recip ccv_))))
              (lambda () (crs)))
    (subst '(= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_)))
               (* (* ccu_ (recip ccu_)) (* ccv_ (recip ccv_)))))
    (subst '(= (* ccu_ (recip ccu_)) 1))
    (subst '(= (* ccv_ (recip ccv_)) 1))
    (crs)))
(di)                                    ; assume (* ccu_ ccv_) = 0; goal FALSITY
(dk-have! '(= (* 0 (* (recip ccu_) (recip ccv_))) 0) (lambda () (crs)))
(dk-have! '(NOT (= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))) 1))
  (lambda ()
    (subst '(= (* ccu_ ccv_) 0))
    (subst '(= (* 0 (* (recip ccu_) (recip ccv_))) 0))
    (arith)))
(ai '(NOT (= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))) 1)))
(ccr-check 'cc-mul-nonzero)
(qed 'cc-mul-nonzero)
(topic! 'cc-mul-nonzero 'algebra)
(alias! 'cc-mul-nonzero "a product of nonzero complex numbers is nonzero")

;;; recip(u.v) = recip(u).recip(v): the uniqueness of the inverse, written out
;;; as P = P.(W.Q) = (W.P).Q = Q with W = u.v.
(sp (make-wff
     '(FORALL ccu_ (IMPLIES (IN ccu_ CC)
        (FORALL ccv_ (IMPLIES (IN ccv_ CC)
          (IMPLIES (NOT (= ccu_ 0))
          (IMPLIES (NOT (= ccv_ 0))
                   (= (recip (* ccu_ ccv_))
                      (* (recip ccu_) (recip ccv_)))))))))))
(dk-peel!)
(dk-have! '(AND (IN ccu_ CC) (NOT (= ccu_ 0))))
(fact 'cc-recip-closed 'ccu_)
(fact 'cc-recip-inverse 'ccu_)
(dk-have! '(AND (IN ccv_ CC) (NOT (= ccv_ 0))))
(fact 'cc-recip-closed 'ccv_)
(fact 'cc-recip-inverse 'ccv_)
(dk-have! '(AND (IN ccu_ CC) (IN ccv_ CC)))
(fact 'cc-mul-closed 'ccu_ 'ccv_)
(dk-have! '(AND (IN (recip ccu_) CC) (IN (recip ccv_) CC)))
(fact 'cc-mul-closed '(recip ccu_) '(recip ccv_))
(fact 'cc-mul-nonzero 'ccu_ 'ccv_)
(dk-have! '(AND (IN (* ccu_ ccv_) CC) (NOT (= (* ccu_ ccv_) 0))))
(fact 'cc-recip-closed '(* ccu_ ccv_))
(fact 'cc-recip-inverse '(* ccu_ ccv_))
(dk-have! '(= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))) 1)
  (lambda ()
    (dk-have! '(= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_)))
                  (* (* ccu_ (recip ccu_)) (* ccv_ (recip ccv_))))
              (lambda () (crs)))
    (subst '(= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_)))
               (* (* ccu_ (recip ccu_)) (* ccv_ (recip ccv_)))))
    (subst '(= (* ccu_ (recip ccu_)) 1))
    (subst '(= (* ccv_ (recip ccv_)) 1))
    (crs)))
(dk-have! '(= (recip (* ccu_ ccv_))
              (* (recip (* ccu_ ccv_))
                 (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_)))))
  (lambda ()
    (subst '(= (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))) 1))
    (crs)))
(dk-have! '(= (* (recip (* ccu_ ccv_))
                 (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))))
              (* (* (* ccu_ ccv_) (recip (* ccu_ ccv_)))
                 (* (recip ccu_) (recip ccv_))))
          (lambda () (crs)))
(dk-have! '(= (* (* (* ccu_ ccv_) (recip (* ccu_ ccv_)))
                 (* (recip ccu_) (recip ccv_)))
              (* (recip ccu_) (recip ccv_)))
  (lambda ()
    (subst '(= (* (* ccu_ ccv_) (recip (* ccu_ ccv_))) 1))
    (crs)))
(subst '(= (recip (* ccu_ ccv_))
           (* (recip (* ccu_ ccv_))
              (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))))))
(subst '(= (* (recip (* ccu_ ccv_))
              (* (* ccu_ ccv_) (* (recip ccu_) (recip ccv_))))
           (* (* (* ccu_ ccv_) (recip (* ccu_ ccv_)))
              (* (recip ccu_) (recip ccv_)))))
(ass)
(ccr-check 'cc-recip-mul)
(qed 'cc-recip-mul)
(topic! 'cc-recip-mul 'algebra)
(alias! 'cc-recip-mul "the reciprocal of a product is the product of the reciprocals")

;;; =====================================================================
;;; (6) THE DERIVATIVE OF 1/z.
;;;
;;;     IS-DIFF-ON(CC-NORMED-FIELD, CCNZ, z |-> recip(z), a, -recip(a.a))
;;;
;;; The Caratheodory factor is  phi(z) = -(recip(z).recip(a)), which IS the
;;; difference quotient in closed form:
;;;     1/z - 1/a  =  -(1/z)(1/a) . (z - a).
;;; Its continuity at a is the product of `cc-recip-continuous-at' with the
;;; CONSTANT map -recip(a) (nf-product-continuous-on), transported onto the
;;; numeric shape by `ms-cont-transfer-on'; phi(a) = -(recip(a).recip(a)) is
;;; -recip(a.a) by `cc-recip-mul'.
;;; =====================================================================

(define ccr-phi
  (list 'VNB-LAMBDA 'crz_ ccr-nz '(- (* (recip crz_) (recip cra_)))))
(define ccr-deriv '(- (recip (* cra_ cra_))))

(sp (make-wff (list 'FORALL 'cra_ (list 'IMPLIES (list 'IN 'cra_ ccr-nz)
      (list 'IS-DIFF-ON ccr-k ccr-nz ccr-rl 'cra_ ccr-deriv)))))
(dk-peel!)
(fact 'cc-is-normed-field)
(fact 'nf-cc-is-metric-space)
(fact 'nf-metric-carrier ccr-k)
(fact 'cc-nf-carr)
(dk-have! (list '== (list 'PTS ccr-m) 'CC)
  (lambda () (subst (list '== (list 'PTS ccr-m) '(CARR CC-NORMED-FIELD))) (ass)))
(fact 'cc-nonzero-open-nf)
(fact 'cc-nonzero-subset)
(fact 'cc-nonzero-is-set)
(dk-have! (list 'SUBSET ccr-nz (list 'PTS ccr-m))
  (lambda () (subst (list '== (list 'PTS ccr-m) 'CC)) (ass)))
(fact 'subspace-is-metric-space ccr-m ccr-nz)
(fact 'subspace-pts ccr-m ccr-nz)
;; the point and its reciprocal
(ccr-nonzero-parts! 'cra_)
(dk-have! '(AND (IN cra_ CC) (NOT (= cra_ 0))))
(fact 'cc-recip-closed 'cra_)
(fact 'cc-recip-inverse 'cra_)
(fact 'cc-neg-closed '(recip cra_))
(dk-have! '(AND (IN cra_ CC) (IN cra_ CC)))
(fact 'cc-mul-closed 'cra_ 'cra_)
(fact 'cc-mul-nonzero 'cra_ 'cra_)
(dk-have! '(AND (IN (* cra_ cra_) CC) (NOT (= (* cra_ cra_) 0))))
(fact 'cc-recip-closed '(* cra_ cra_))
(fact 'cc-neg-closed '(recip (* cra_ cra_)))
(fact 'cc-recip-mul 'cra_ 'cra_)
;; phi(a) itself: `rfl' will not close an equation whose term is not certified
;; DEFINED, so the value of the factor at a is typed before the definition is
;; unfolded.
(dk-have! '(AND (IN (recip cra_) CC) (IN (recip cra_) CC)))
(fact 'cc-mul-closed '(recip cra_) '(recip cra_))
(fact 'cc-neg-closed '(* (recip cra_) (recip cra_)))
;; the two FUN typings, in the normed field's own reading of the codomain
(fact 'cc-recip-lam-in-fun)
(dk-have! (list 'IN ccr-rl (list 'FUN ccr-nz '(CARR CC-NORMED-FIELD)))
  (lambda () (subst '(== (CARR CC-NORMED-FIELD) CC)) (ass)))
(dk-have! (list 'IN ccr-deriv '(CARR CC-NORMED-FIELD))
  (lambda () (subst '(== (CARR CC-NORMED-FIELD) CC)) (ass)))
(dk-have! (list 'IN ccr-phi (list 'FUN ccr-nz 'CC))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (let ((g (dk-goal)))
         (cond ((equal? g (list 'IN ccr-nz 'SET)) (ass))
               ((eq? (ccr-head g) 'FORALL)
                (let ((z (dk-di-var!)))
                  (ccr-nonzero-parts! z)
                  (dk-have! (list 'AND (list 'IN z 'CC) (list 'NOT (list '= z 0))))
                  (fact 'cc-recip-closed z)
                  (dk-have! (list 'AND (list 'IN (list 'recip z) 'CC)
                                       '(IN (recip cra_) CC)))
                  (fact 'cc-mul-closed (list 'recip z) '(recip cra_))
                  (fact 'cc-neg-closed (list '* (list 'recip z) '(recip cra_)))
                  (ass)))
               (#t (error "cc-reciprocal: unexpected lam-t leaf"
                          (expression->string g))))))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'IN ccr-phi (list 'FUN ccr-nz '(CARR CC-NORMED-FIELD)))
  (lambda () (subst '(== (CARR CC-NORMED-FIELD) CC)) (ass)))
;; the continuity of the factor
(dk-have! '(IN cra_ (PTS (SUBSPACE-MS (NF-METRIC-SPACE CC-NORMED-FIELD)
                                      (DIFFERENCE CC (SINGLETON 0)))))
  (lambda () (subst (list '== (list 'PTS ccr-w) ccr-nz)) (ass)))
(dk-have! '(IN (- (recip cra_)) (PTS (NF-METRIC-SPACE CC-NORMED-FIELD)))
  (lambda () (subst (list '== (list 'PTS ccr-m) 'CC)) (ass)))
(fact 'cc-recip-continuous-at 'cra_)
(define ccr-const-lam
  (list-ref (dk-fact! 'ms-const-continuous-on ccr-w ccr-nz ccr-m
                      '(- (recip cra_)) 'cra_) 3))
(define ccr-prod-lam
  (list-ref (dk-fact! 'nf-product-continuous-on ccr-k ccr-w ccr-nz
                      ccr-rl ccr-const-lam 'cra_) 3))
(dk-have! (list 'FORALL 'crv_ (list 'IMPLIES (list 'IN 'crv_ ccr-nz)
            (list '= (list ccr-phi 'crv_) (list ccr-prod-lam 'crv_))))
  (lambda ()
    (di)
    (ccr-nonzero-parts! 'crv_)
    (dk-have! '(AND (IN crv_ CC) (NOT (= crv_ 0))))
    (fact 'cc-recip-closed 'crv_)
    (dk-lam-b!)
    (dk-have! '(AND (IN (recip crv_) CC) (IN (- (recip cra_)) CC)))
    (fact 'cc-nf-mul-apply '(recip crv_) '(- (recip cra_)))
    (subst '(== ((MUL CC-NORMED-FIELD) (recip crv_) (- (recip cra_)))
                (* (recip crv_) (- (recip cra_)))))
    (crs)))
(fact 'ms-cont-transfer-on ccr-w ccr-m ccr-nz 'CC ccr-prod-lam ccr-phi 'cra_)
;; the definition
(mac 'IS-DIFF-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (ccr-head (dk-goal)) 'FORSOME))
       (ass)
       (begin
         (ew ccr-phi)
         (dk-conj-close!
          (lambda ()
            (let ((g (dk-goal)))
              (cond
                ((eq? (ccr-head g) '=)
                 (dk-lam-b!)
                 (subst '(= (recip (* cra_ cra_)) (* (recip cra_) (recip cra_))))
                 (rfl))
                ((eq? (ccr-head g) 'FORALL)
                 (let* ((x  (dk-di-var!))
                        (rx (list 'recip x))
                        (ra '(recip cra_)))
                   (ccr-nonzero-parts! x)
                   (dk-have! (list 'AND (list 'IN x 'CC) (list 'NOT (list '= x 0))))
                   (fact 'cc-recip-closed x)
                   (fact 'cc-recip-inverse x)
                   (dk-lam-b!)
                   (fact 'cc-nf-sub rx ra)
                   (fact 'cc-nf-sub x 'cra_)
                   (subst (list '== (list '(ADD CC-NORMED-FIELD) rx
                                          (list '(NEG CC-NORMED-FIELD) ra))
                                    (list '- rx ra)))
                   (subst (list '== (list '(ADD CC-NORMED-FIELD) x
                                          '((NEG CC-NORMED-FIELD) cra_))
                                    (list '- x 'cra_)))
                   (dk-have! (list 'AND (list 'IN rx 'CC) (list 'IN ra 'CC)))
                   (fact 'cc-mul-closed rx ra)
                   (fact 'cc-neg-closed (list '* rx ra))
                   (fact 'cc-sub-in-cc x 'cra_)
                   (dk-have! (list 'AND (list 'IN (list '- (list '* rx ra)) 'CC)
                                        (list 'IN (list '- x 'cra_) 'CC)))
                   (fact 'cc-nf-mul-apply (list '- (list '* rx ra)) (list '- x 'cra_))
                   (subst (list '== (list '(MUL CC-NORMED-FIELD)
                                          (list '- (list '* rx ra))
                                          (list '- x 'cra_))
                                    (list '* (list '- (list '* rx ra))
                                             (list '- x 'cra_))))
                   (let ((expand (list '- (list '* rx (list '* 'cra_ ra))
                                          (list '* ra (list '* x rx)))))
                     (dk-have! (list '= (list '* (list '- (list '* rx ra))
                                                 (list '- x 'cra_))
                                        expand)
                               (lambda () (crs)))
                     (subst (list '= (list '* (list '- (list '* rx ra))
                                              (list '- x 'cra_))
                                     expand))
                     (subst (list '= (list '* 'cra_ ra) 1))
                     (subst (list '= (list '* x rx) 1))
                     (crs))))
                (#t (ass))))))))))
(ccr-check 'cc-recip-diff-on)
(qed 'cc-recip-diff-on)
(topic! 'cc-recip-diff-on 'analysis)
(alias! 'cc-recip-diff-on
        "the reciprocal is differentiable on the punctured plane with derivative -1/z^2")

;;; =====================================================================
;;; (7) 1/z IS HOLOMORPHIC ON THE PUNCTURED PLANE.
;;; =====================================================================

(sp (make-wff (list 'HOLOMORPHIC-ON ccr-nz ccr-rl)))
(fact 'cc-nonzero-open-nf)
(fact 'cc-recip-lam-in-fun)
(mac 'HOLOMORPHIC-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (ccr-head (dk-goal)) 'FORALL))
       (ass)
       (let* ((a   (dk-di-var!))
              (res (dk-fact! 'cc-recip-diff-on a)))
         (fact 'diff-on-deriv-in-carr ccr-k ccr-nz ccr-rl a (list-ref res 5))
         (ew (list-ref res 5))
         (ass)))))
(ccr-check 'holomorphic-recip)
(qed 'holomorphic-recip)
(topic! 'holomorphic-recip 'analysis)
(alias! 'holomorphic-recip "the reciprocal is holomorphic on the punctured plane")

;;; =====================================================================
;;; (8) THE RECIPROCAL RULE, WITH THE DERIVATIVE.
;;;
;;;   f differentiable at a on U, f NOWHERE ZERO on U, q = 1/f pointwise
;;;      =>  q is differentiable at a with q'(a) = -f'(a)/f(a)^2.
;;;
;;; The nowhere-zero hypothesis is on the MAP and not on the point, for the
;;; reason continuity-recip.scm records: `recip' is partial, so 1/f is a
;;; function on U only when f omits 0 on all of U.  This is the notes' chain
;;; rule (Proposition 2.4) at the outer map z |-> 1/z, and it is `diff-on-chain'
;;; here, at s := CCNZ.
;;; =====================================================================

(sp (make-wff
     '(FORALL cru_ (FORALL crf_ (FORALL cra_ (FORALL crl_ (FORALL crq_
        (IMPLIES (IS-DIFF-ON CC-NORMED-FIELD cru_ crf_ cra_ crl_)
        (IMPLIES (FORALL cry_ (IMPLIES (IN cry_ cru_) (NOT (= (crf_ cry_) 0))))
        (IMPLIES (IN crq_ (FUN cru_ CC))
        (IMPLIES (FORALL cry_ (IMPLIES (IN cry_ cru_)
                   (== (crq_ cry_) (recip (crf_ cry_)))))
                 (IS-DIFF-ON CC-NORMED-FIELD cru_ crq_ cra_
                    (- (* crl_ (recip (* (crf_ cra_) (crf_ cra_)))))))))))))))))
(dk-peel!)
(define ccr-nzu
  (ccr-find 'nowhere-zero
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x 'NOT)))))
(define ccr-ptw
  (ccr-find 'pointwise
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x 'recip)))))
(fact 'cc-is-normed-field)
(fact 'cc-nf-carr)
(fact 'diff-on-pt-in ccr-k 'cru_ 'crf_ 'cra_ 'crl_)
(fact 'diff-on-in-fun ccr-k 'cru_ 'crf_ 'cra_ 'crl_)
(fact 'diff-on-deriv-in-carr ccr-k 'cru_ 'crf_ 'cra_ 'crl_)
(dk-have! '(IN crf_ (FUN cru_ CC))
  (lambda () (subst '(== CC (CARR CC-NORMED-FIELD))) (ass)))
(dk-have! '(IN crl_ CC)
  (lambda () (subst '(== CC (CARR CC-NORMED-FIELD))) (ass)))
(dk-have! '(IN crq_ (FUN cru_ (CARR CC-NORMED-FIELD)))
  (lambda () (subst '(== (CARR CC-NORMED-FIELD) CC)) (ass)))
(fact 'fun-apply-type-c 'crf_ 'cru_ 'CC 'cra_)
(dk-apply! ccr-nzu 'cra_)
(fact 'cc-nonzero-membership '(crf_ cra_))
(dk-have! (list 'IN '(crf_ cra_) ccr-nz) (lambda () (prop)))
;; f maps U into the punctured plane
(define ccr-into
  (list 'FORALL 'crv_ (list 'IMPLIES '(IN crv_ cru_) (list 'IN '(crf_ crv_) ccr-nz))))
(dk-have! ccr-into
  (lambda ()
    (di)
    (fact 'fun-apply-type-c 'crf_ 'cru_ 'CC 'crv_)
    (dk-apply! ccr-nzu 'crv_)
    (fact 'cc-nonzero-membership '(crf_ crv_))
    (prop)))
;; -1/f(a)^2 is TYPED BEFORE the chain rule is instantiated at it (the LUTINS
;; rule: forall-elim owes `t = t' for a term the certificate does not accept,
;; and the failure surfaces as a `detach' miss several steps later).
(dk-have! '(AND (IN (crf_ cra_) CC) (IN (crf_ cra_) CC)))
(fact 'cc-mul-closed '(crf_ cra_) '(crf_ cra_))
(fact 'cc-mul-nonzero '(crf_ cra_) '(crf_ cra_))
(dk-have! '(AND (IN (* (crf_ cra_) (crf_ cra_)) CC)
                (NOT (= (* (crf_ cra_) (crf_ cra_)) 0))))
(fact 'cc-recip-closed '(* (crf_ cra_) (crf_ cra_)))
(fact 'cc-neg-closed '(recip (* (crf_ cra_) (crf_ cra_))))
;; the outer map at f(a), then the chain rule
(define ccr-outer (dk-fact! 'cc-recip-diff-on '(crf_ cra_)))
(define ccr-mterm (list-ref ccr-outer 5))
(define ccr-chain
  (dk-fact! 'diff-on-chain ccr-k 'cru_ ccr-nz 'crf_ ccr-rl 'cra_ 'crl_ ccr-mterm))
(define ccr-chain-lam (list-ref ccr-chain 3))
(define ccr-chain-der (list-ref ccr-chain 5))
;; the derivative, in the numeric shape the statement uses
(dk-have! (list 'AND (list 'IN ccr-mterm 'CC) '(IN crl_ CC)))
(fact 'cc-nf-mul-apply ccr-mterm 'crl_)
(dk-have! (list '= ccr-chain-der
                   '(- (* crl_ (recip (* (crf_ cra_) (crf_ cra_))))))
  (lambda ()
    (subst (list '== ccr-chain-der (list '* ccr-mterm 'crl_)))
    (crs)))
;; the transfer onto q
(dk-have! (list 'FORALL 'crv_ (list 'IMPLIES '(IN crv_ cru_)
            (list '== '(crq_ crv_) (list ccr-chain-lam 'crv_))))
  (lambda ()
    (di)
    ;; the universal CAPTURED WHEN IT WAS BUILT: `fact' lands every link of the
    ;; instantiation chain, and a shape-based finder picks one of those.
    (dk-apply! ccr-into 'crv_)
    (dk-lam-b!)
    (dk-apply! ccr-ptw 'crv_)
    (ass)))
(subst (list '= '(- (* crl_ (recip (* (crf_ cra_) (crf_ cra_))))) ccr-chain-der))
(fact 'diff-on-transfer-ptwise-eq ccr-k 'cru_ 'crq_ ccr-chain-lam 'cra_ ccr-chain-der)
(ass)
(ccr-check 'diff-on-recip-cc)
(qed 'diff-on-recip-cc)
(topic! 'diff-on-recip-cc 'analysis)
(alias! 'diff-on-recip-cc
        "the derivative of 1/f is -f'/f^2, where f does not vanish")

;;; =====================================================================
;;; (9) THE RECIPROCAL RULE FOR HOLOMORPHIC-ON.
;;; =====================================================================

(sp (make-wff
     '(FORALL cru_ (FORALL crf_ (FORALL crq_
        (IMPLIES (HOLOMORPHIC-ON cru_ crf_)
        (IMPLIES (FORALL cry_ (IMPLIES (IN cry_ cru_) (NOT (= (crf_ cry_) 0))))
        (IMPLIES (IN crq_ (FUN cru_ CC))
        (IMPLIES (FORALL cry_ (IMPLIES (IN cry_ cru_)
                   (== (crq_ cry_) (recip (crf_ cry_)))))
                 (HOLOMORPHIC-ON cru_ crq_))))))))))
(dk-peel!)
(fact 'holomorphic-on-open 'cru_ 'crf_)
(fact 'holomorphic-on-diff 'cru_ 'crf_)
(define ccr-hdiff
  (ccr-find 'diff-universal
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x 'IS-DIFF-ON)))))
(mac 'HOLOMORPHIC-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (ccr-head (dk-goal)) 'FORALL))
       (ass)
       (let* ((a   (dk-di-var!))
              (lw  (dk-skolem! (dk-apply! ccr-hdiff a)))
              (res (dk-fact! 'diff-on-recip-cc 'cru_ 'crf_ a lw 'crq_)))
         (fact 'diff-on-deriv-in-carr ccr-k 'cru_ 'crq_ a (list-ref res 5))
         (ew (list-ref res 5))
         (ass)))))
(ccr-check 'holomorphic-recip-of)
(qed 'holomorphic-recip-of)
(topic! 'holomorphic-recip-of 'analysis)
(alias! 'holomorphic-recip-of
        "the reciprocal of a nowhere-zero holomorphic function is holomorphic")

;;; =====================================================================
;;; (10) THE QUOTIENT RULE FOR HOLOMORPHIC-ON.
;;;
;;; The notes' section 2.1 gives sums and products (Proposition 2.3) and the
;;; chain rule (Proposition 2.4) and says "the complex derivative satisfies the
;;; same algebraic rules as the ordinary derivative of calculus"; the quotient
;;; rule is used later, at (74).  The hypothesis is the one a quotient always
;;; carries: the denominator does not vanish on U.  `/' is DEFINED
;;; (binary-divide-def: a / b == a . recip(b)), so the statement may be written
;;; with the quotient sign and unfolded in one macete.
;;; =====================================================================

(sp (make-wff
     '(FORALL cru_ (FORALL crf_ (FORALL crg_ (FORALL crq_
        (IMPLIES (HOLOMORPHIC-ON cru_ crf_)
        (IMPLIES (HOLOMORPHIC-ON cru_ crg_)
        (IMPLIES (FORALL cry_ (IMPLIES (IN cry_ cru_) (NOT (= (crg_ cry_) 0))))
        (IMPLIES (IN crq_ (FUN cru_ CC))
        (IMPLIES (FORALL cry_ (IMPLIES (IN cry_ cru_)
                   (== (crq_ cry_) (/ (crf_ cry_) (crg_ cry_)))))
                 (HOLOMORPHIC-ON cru_ crq_))))))))))))
(dk-peel!)
(define ccr-qnz
  (ccr-find 'nowhere-zero
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x 'NOT)))))
(define ccr-qptw
  (ccr-find 'pointwise
    (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x '/)))))
(fact 'cc-is-normed-field)
(fact 'holomorphic-on-open 'cru_ 'crg_)
(fact 'nf-open-is-set ccr-k 'cru_)
(fact 'holomorphic-on-in-fun 'cru_ 'crf_)
(fact 'holomorphic-on-in-fun 'cru_ 'crg_)
(define ccr-rg (list 'VNB-LAMBDA 'crz_ 'cru_ '(recip (crg_ crz_))))
(define (ccr-recip-typed! v)
  (fact 'fun-apply-type-c 'crg_ 'cru_ 'CC v)
  (dk-apply! ccr-qnz v)
  (dk-have! (list 'AND (list 'IN (list 'crg_ v) 'CC)
                       (list 'NOT (list '= (list 'crg_ v) 0))))
  (fact 'cc-recip-closed (list 'crg_ v)))
(dk-have! (list 'IN ccr-rg '(FUN cru_ CC))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (let ((g (dk-goal)))
         (cond ((equal? g '(IN cru_ SET)) (ass))
               ((eq? (ccr-head g) 'FORALL)
                (let ((z (dk-di-var!)))
                  (ccr-recip-typed! z)
                  (ass)))
               (#t (error "cc-reciprocal: unexpected lam-t leaf"
                          (expression->string g))))))
     (dk-opened (lambda () (lam-t))))))
(define ccr-rgptw
  (list 'FORALL 'crv_ (list 'IMPLIES '(IN crv_ cru_)
    (list '== (list ccr-rg 'crv_) '(recip (crg_ crv_))))))
(dk-have! ccr-rgptw
  (lambda ()
    (di)
    (ccr-recip-typed! 'crv_)
    (dk-lam-b!)
    (qrfl)))
(fact 'holomorphic-recip-of 'cru_ 'crg_ ccr-rg)
(dk-have! (list 'FORALL 'crv_ (list 'IMPLIES '(IN crv_ cru_)
            (list '== '(crq_ crv_) (list '* '(crf_ crv_) (list ccr-rg 'crv_)))))
  (lambda ()
    (di)
    (ccr-recip-typed! 'crv_)
    (dk-lam-b!)
    (dk-apply! ccr-qptw 'crv_)
    (subst '(== (crq_ crv_) (/ (crf_ crv_) (crg_ crv_))))
    (mac 'binary-divide-def)
    (qrfl)))
(fact 'holomorphic-product 'cru_ 'crf_ ccr-rg 'crq_)
(ass)
(ccr-check 'holomorphic-quotient)
(qed 'holomorphic-quotient)
(topic! 'holomorphic-quotient 'analysis)
(alias! 'holomorphic-quotient
        "a quotient of holomorphic functions with nonvanishing denominator is holomorphic")
