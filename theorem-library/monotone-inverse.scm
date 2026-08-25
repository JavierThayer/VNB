;;; monotone-inverse.scm -- MONOTONICITY VOCABULARY FOR REAL FUNCTIONS, and
;;; the EXISTENCE HALF of the inverse function theorem on a closed interval.
;;; Everything here is `modulo 0'.
;;;
;;; The tree had NO monotonicity predicate for real functions at all.  The only
;;; IS-STRICTLY-* anywhere was IS-STRICTLY-BELOW, a poset relation in
;;; zorn-route-two.scm and unrelated; `deriv-monotone-proof.scm:34-36' writes
;;; "f is strictly increasing on [a,b]" out longhand, as a nested FORALL, and so
;;; does every other site that needs it.  `IS-STRICTLY-INCREASING-ON' below is
;;; that formula, named.  It is a `def-predicate', hence `definitional', hence
;;; free: unfolding it puts nothing in any bill.
;;;
;;; WHAT IS PROVED, and it is the honest core of "a continuous strictly
;;; increasing f on [a,b] has an inverse on [f(a),f(b)]":
;;;
;;;   ccint-subset-rr                  [a,b] is a subclass of RR
;;;   strict-increase-injective        strictly increasing on s => injective on s
;;;   monotone-ccint-inverse-exists    for every y in [f(a),f(b)] there is a
;;;                                    UNIQUE x in [a,b] with f(x) = y
;;;   monotone-ccint-inverse-order     f(u) < f(v) => u < v, for u,v in [a,b]
;;;                                    -- the inverse is order-preserving
;;;
;;; The first is separation; the second is the trichotomy plus one instance of
;;; the monotonicity universal on each side; the third is `ivt' (ivt-proof.scm,
;;; PROVEN, Bolzano route) for existence and the second for uniqueness; the
;;; fourth is the trichotomy again, run backwards.  No new analysis: the whole
;;; content is the intermediate value theorem, which the tree already had.
;;;
;;; WHAT IS **NOT** PROVED, AND WHY -- the obstacle, stated once and precisely.
;;; The classical statement packages the above as a FUNCTION: "f has a
;;; continuous, strictly increasing inverse g on [f(a),f(b)]".  Neither half of
;;; that phrase is expressible here, and both failures are the SAME missing
;;; piece -- a metric SUBSPACE structure, which the tree has deliberately
;;; deferred (it is also what blocks Heine-Borel).
;;;
;;; * CONTINUITY OF THE INVERSE cannot even be STATED.  `IS-CONTINUOUS-AT(RR-MS,
;;;   RR-MS, g, y)' is continuity of a map TOTAL on RR.  Any total extension of
;;;   the inverse past [f(a),f(b)] -- say by the `IF' idiom of finsum.scm's
;;;   ENUM-FAM, (VNB-LAMBDA y RR (IF (IN y (CCINT (f a) (f b))) ... a)) -- is
;;;   DISCONTINUOUS at the two endpoints of the image interval, so the
;;;   statement one can write down is false, and the statement one means needs
;;;   continuity RELATIVE to [f(a),f(b)].  That is a new predicate
;;;   (IS-CONTINUOUS-ON-AT, or a subspace metric), and it is a design decision
;;;   about the metric vocabulary, not a lemma.  It is left to the user.
;;; * STRICT INCREASE OF THE INVERSE cannot be stated with the predicate below
;;;   either, for the mirror-image reason: `IS-STRICTLY-INCREASING-ON' hoists
;;;   `(IN f (FUN RR RR))', following the house style of IS-CONTINUOUS-AT,
;;;   IS-LINEAR-FUNCTIONAL-ON and IS-DIFF-AT, and the inverse is a map
;;;   [f(a),f(b)] -> [a,b], not a map RR -> RR.  `monotone-ccint-inverse-order'
;;;   is that fact in the only form the vocabulary allows -- pointwise, about f,
;;;   with no g mentioned.
;;;
;;; So the two questions are one question: whether the tree grows relativised
;;; predicates (a `-ON' family carrying its own domain) or a subspace
;;; structure.  Until that is settled, "the inverse is a continuous increasing
;;; function on the image interval" is not a theorem this vocabulary has a
;;; statement for, and asserting it as a support would be asserting a sentence
;;; whose closest writable form is false.
;;;
;;; DRIVER NOTES.
;;;
;;; * `mac-h ccint-membership' REPLACES the assumption it unfolds, and the
;;;   monotonicity universal is GUARDED on that same membership -- so in
;;;   monotone-ccint-inverse-order the typings are read off inside `have!'
;;;   lanes and the main branch keeps (IN u_ (CCINT a b)) intact.  Done in the
;;;   main branch, the later `inst+' lands an undetached implication and the
;;;   `dk-deepest' around it errors several steps from the cause.
;;; * The monotonicity universal is captured BEFORE `rr-lt-trichotomy' is
;;;   cited.  The trichotomy's instantiation chain contains a FORALL of exactly
;;;   the same FORALL/`<' shape and lands NEARER the top of the context, so a
;;;   finder written after the citation picks the wrong one -- the
;;;   discriminate-on-the-consequent rule, met from the other side.
;;; * The contradictory branches close by `ineq' on two named premises, not by
;;;   `contra'.  `contra' does close them -- it is exactly its job -- but it
;;;   probes on a scratch state over the whole context, and two such calls cost
;;;   more than the rest of the file put together.  Name the premises when you
;;;   know them.
;;;
;;; Loads after ivt-proof and ccint-basics.  Needs ivt (ivt-proof),
;;; ccint-membership (ccint-basics), CCINT (extreme-value), rr-order-basics
;;; (rr-lt-trichotomy), fun-apply-type-proof (fun-apply-type-c),
;;; metric-continuity (IS-CONTINUOUS-AT), driver-kit.

;;; ---- file-local driver helpers (the `mi-' prefix) --------------------

(define (mi-peel-forall!)
  (let loop ((n 0))
    (if (and (pair? (dk-goal)) (eq? (car (dk-goal)) 'FORALL) (< n 8))
        (begin (di) (loop (+ n 1))) #t)))

(define (mi-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1))) #t))))
(define (mi-split!)
  (let loop ((b 40))
    (when (> b 0)
      (let ((t (let scan ((as (dk-asms)))
                 (cond ((null? as) #f)
                       ((and (pair? (car as)) (memq (caar as) '(AND FORSOME))) (car as))
                       (else (scan (cdr as)))))))
        (when t (ai t) (loop (- b 1)))))))
(define (mi-idx f)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "mi-idx: not in context" f))
          ((equal? (car l) f) i) (else (lp (cdr l) (+ i 1))))))
(define (mi-ineq . fs) (apply ineq (map mi-idx fs)))
(define (mi-find what p)
  (let lp ((l (dk-asms)))
    (cond ((null? l) (error "mi-find" what)) ((p (car l)) (car l)) (else (lp (cdr l))))))


;;; =====================================================================
;;; The vocabulary.
;;;
;;; Argument order and the hoisted typing follow the house style of
;;; IS-CONTINUOUS-AT (metric-continuity.scm:33) and IS-LINEAR-FUNCTIONAL-ON
;;; (linear-functional.scm:60): the function leads when RR is fixed -- as in
;;; IS-DIFF-AT -- the SET follows, the typing conjuncts are inside the body,
;;; and the domain is constrained by `SUBSET s RR' rather than by sethood.
;;; `-ON' is the tree's established marker for "restricted to a subset".
;;; =====================================================================

(def-predicate 'IS-STRICTLY-INCREASING-ON '(f s)
  '(AND (IN f (FUN RR RR))
   (AND (SUBSET s RR)
        (FORALL u (IMPLIES (IN u s)
          (FORALL v (IMPLIES (IN v s)
            (IMPLIES (< u v) (< (f u) (f v))))))))))
(notation! 'IS-STRICTLY-INCREASING-ON 'kind 'predicate 'arity 2
           'english "$1 is strictly increasing on $2")


;;; =====================================================================
;;; (1) A closed interval is a subclass of RR.  Separation, nothing else --
;;; but a caller has to supply it to establish IS-STRICTLY-INCREASING-ON at
;;; a CCINT, so it is worth a name.
;;; =====================================================================

(sp (make-wff '(FORALL a (FORALL b (SUBSET (CCINT a b) RR)))))
(mi-peel-forall!)
(mac 'subset-def)
(let* ((landed (dk-landed (lambda () (di)))) (z (cadr (car landed))))
  (mac-h 'ccint-membership (list 'IN z '(CCINT a b)))
  (mi-split!)
  (ass))
(qed 'ccint-subset-rr)
(topic! 'ccint-subset-rr 'topology)
(alias! 'ccint-subset-rr "a closed interval is a subclass of the reals")

;;; =====================================================================
;;; (2) Strictly increasing implies injective.
;;; =====================================================================

(sp (make-wff '(FORALL f (FORALL s (IMPLIES (IS-STRICTLY-INCREASING-ON f s)
   (FORALL u (IMPLIES (IN u s) (FORALL v (IMPLIES (IN v s)
     (IMPLIES (= (f u) (f v)) (= u v)))))))))))
(mi-peel!)
(mac-h 'IS-STRICTLY-INCREASING-ON '(IS-STRICTLY-INCREASING-ON f s))
(mi-split!)
(mac-h 'subset-def '(SUBSET s RR))
(mi-split!)
(let ((sub (mi-find 'sub (lambda (x) (and (pair? x) (eq? (car x) 'FORALL) (dk-contains? x 'RR)
                                          (not (dk-contains? x '<)))))))
  (inst+ sub 'u) (inst+ sub 'v))
;; the monotonicity universal, captured BEFORE rr-lt-trichotomy lands a
;; universal of the very same FORALL/`<' shape
(define mi-mono
  (mi-find 'mono (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                  (dk-contains? x '<) (dk-contains? x 's)))))
(fact 'rr-lt-trichotomy 'u 'v)
(fact 'fun-apply-type-c 'f 'RR 'RR 'u)
(fact 'fun-apply-type-c 'f 'RR 'RR 'v)
(let ((mono mi-mono))
  (use-cases '((< u v) (= u v) (< v u))
    (lambda ()
      (let ((mu (dk-deepest (lambda () (inst+ mono 'u)))))
        (dk-deepest (lambda () (inst+ mu 'v))))
      (mi-ineq '(< (f u) (f v)) '(= (f u) (f v))))
    (lambda () (ass))
    (lambda ()
      (let ((mv (dk-deepest (lambda () (inst+ mono 'v)))))
        (dk-deepest (lambda () (inst+ mv 'u))))
      (mi-ineq '(< (f v) (f u)) '(= (f u) (f v))))))
(qed 'strict-increase-injective)
(topic! 'strict-increase-injective 'analysis)
(alias! 'strict-increase-injective "a strictly increasing function is injective")

;;; =====================================================================
;;; (3) EXISTENCE AND UNIQUENESS OF THE INVERSE VALUE.
;;;
;;; For f continuous on [a,b] and strictly increasing there, every y between
;;; f(a) and f(b) is f(x) for exactly one x in [a,b].  Existence is `ivt';
;;; uniqueness is (2).  This is the inverse function, stated pointwise --
;;; see the head comment for why it is not stated as a function.
;;; =====================================================================

(sp (make-wff
  (forall-guarded '(f a b)
    (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR) '(<= a b)
          '(FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
          '(IS-STRICTLY-INCREASING-ON f (CCINT a b)))
    '(FORALL y (IMPLIES (IN y (CCINT (f a) (f b)))
        (FORSOME p_ (AND (IN p_ (CCINT a b))
                    (AND (= (f p_) y)
                         (FORALL q_ (IMPLIES (IN q_ (CCINT a b))
                            (IMPLIES (= (f q_) y) (= p_ q_))))))))))))
(mi-peel!)
(mac-h 'ccint-membership '(IN y (CCINT (f a) (f b))))
(mi-split!)
(have! '(AND (<= (f a) y) (<= y (f b))))
(define mi-ex (dk-deepest (lambda () (fact 'ivt 'f 'a 'b 'y))))

(define mi-w
  (let* ((fv0 (apply append (map free-vars (dk-asms))))
         (landed (dk-landed (lambda () (ai mi-ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                         (apply append (map free-vars (dk-asms))))))
      (if (null? fresh) (error "no witness") (car fresh)))))
(ew mi-w)
(for-each
 (lambda (k)
   (dk-focus! k)
   (let ((g (dk-goal)))
     (if (eq? (car g) 'AND)
         (for-each
          (lambda (k2)
            (dk-focus! k2)
            (let ((g2 (dk-goal)))
              (if (eq? (car g2) 'FORALL)
                  (begin
                    (di) (di)
                    (let* ((gq (dk-goal)) (q (caddr gq)))
                      (have! (list '= (list 'f mi-w) (list 'f q))
                        (lambda ()
                          (subst (list '= (list 'f mi-w) 'y))
                          (fact 'eq-sym (list 'f q) 'y)
                          (ass)))
                      (fact 'strict-increase-injective 'f '(CCINT a b) mi-w q)
                      (ass)))
                  (ass))))
          (dk-opened (lambda () (di))))
         (ass))))
 (dk-opened (lambda () (di))))
(qed 'monotone-ccint-inverse-exists)
(topic! 'monotone-ccint-inverse-exists 'analysis)
(alias! 'monotone-ccint-inverse-exists
        "a continuous strictly increasing function is invertible on a closed interval")

;;; =====================================================================
;;; (4) THE INVERSE IS ORDER-PRESERVING, pointwise.
;;; =====================================================================

(sp (make-wff
  (forall-guarded '(f a b)
    (list '(IS-STRICTLY-INCREASING-ON f (CCINT a b)))
    '(FORALL u_ (IMPLIES (IN u_ (CCINT a b))
       (FORALL v_ (IMPLIES (IN v_ (CCINT a b))
         (IMPLIES (< (f u_) (f v_)) (< u_ v_)))))))))
(mi-peel!)
(mac-h 'IS-STRICTLY-INCREASING-ON '(IS-STRICTLY-INCREASING-ON f (CCINT a b)))
(mi-split!)
(define mi-mono2
  (mi-find 'mono2 (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                   (dk-contains? x '<) (dk-contains? x 'CCINT)))))
;; `mac-h' REPLACES the assumption it unfolds, and the monotonicity universal
;; is guarded on the CCINT membership -- so the typing is read off inside a
;; `have!' lane and the main branch keeps (IN u_ (CCINT a b)) intact.
(have! '(IN u_ RR)
  (lambda () (mac-h 'ccint-membership '(IN u_ (CCINT a b))) (mi-split!) (ass)))
(have! '(IN v_ RR)
  (lambda () (mac-h 'ccint-membership '(IN v_ (CCINT a b))) (mi-split!) (ass)))
(fact 'fun-apply-type-c 'f 'RR 'RR 'u_)
(fact 'fun-apply-type-c 'f 'RR 'RR 'v_)
(fact 'rr-lt-trichotomy 'u_ 'v_)
(use-cases '((< u_ v_) (= u_ v_) (< v_ u_))
  (lambda () (ass))
  (lambda ()
    (have! '(= (f u_) (f v_)) (lambda () (subst '(= u_ v_)) (rfl)))
    (mi-ineq '(< (f u_) (f v_)) '(= (f u_) (f v_))))
  (lambda ()
    (let ((mv (dk-deepest (lambda () (inst+ mi-mono2 'v_)))))
      (dk-deepest (lambda () (inst+ mv 'u_))))
    (mi-ineq '(< (f u_) (f v_)) '(< (f v_) (f u_)))))
(qed 'monotone-ccint-inverse-order)
(topic! 'monotone-ccint-inverse-order 'analysis)
(alias! 'monotone-ccint-inverse-order "the inverse of an increasing function is increasing")
