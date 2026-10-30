;;; rr-star-order-minimal.scm -- THE MINIMAL PRIMITIVE SET of the extended line, run.
;;; Agent EXT-ORDER, 2026-10-26.  Wired 2026-10-27 (batch 0): the two stamps retired from
;;; structure-library/extended-reals.scm, the three order laws below never stamped.
;;; Library: analysis (extended-reals.scm's library).
;;;
;;; From  rr-star-membership (definitional), rr-star-leq-antisymmetric (primitive, new),
;;;       pos-inf-upper-bound, neg-inf-lower-bound (primitive, 2026-09-18),
;;;       and the RR field and order axioms of number-systems.scm,
;;; this file proves, modulo 0:
;;;
;;;   pos-inf-above-reals      x in RR => NOT (POS-INF <= x)      (stamp RETIRED 2026-10-27)
;;;   neg-inf-not-in-rr        NOT (NEG-INF in RR)                (stamp RETIRED 2026-10-27)
;;;   neg-inf-below-reals      x in RR => NOT (x <= NEG-INF)      (EXT-INF's proposed primitive)
;;;   rr-star-le-pos-inf-eq    x in RR-STAR, POS-INF <= x => x = POS-INF
;;;   rr-star-le-neg-inf-eq    x in RR-STAR, x <= NEG-INF => x = NEG-INF
;;;   rr-star-leq-reflexive    (EXT-ORDER's proposed primitive; NOT stamped)
;;;   rr-star-leq-transitive   (EXT-ORDER's proposed primitive; NOT stamped)
;;;   rr-star-leq-total        (EXT-ORDER's proposed primitive; NOT stamped)
;;;
;;; So the integrator can RETIRE the stamps pos-inf-above-reals and neg-inf-not-in-rr, never
;;; wire neg-inf-below-reals as an axiom, and -- the user's decision -- retire the primitives
;;; rr-star-leq-reflexive / -transitive / -total, leaving antisymmetry, the two bounds and
;;; rr-star-leq-domain as the whole primitive order theory of RR-STAR.  If the three are
;;; kept primitive, DELETE their three proofs below (install-duplicate audit).
;;;
;;; NOTHING HERE CITES pos-inf-above-reals, neg-inf-not-in-rr, pos-inf-not-in-rr,
;;; neg-inf-below-reals or any rr-star-leq-* axiom other than rr-star-leq-antisymmetric
;;; before proving it; rr-star-leq-domain is not cited at all.  The minimality probe
;;; (p-min.scm) loads ONLY the antisymmetry axiom (p-min-ax.scm) before this file.
;;;
;;; THE ROUTES.  An infinity that were real would have a real beyond it: POS-INF in RR
;;; gives POS-INF + 1 in RR <= POS-INF (upper bound), and NEG-INF in RR gives NEG-INF <=
;;; NEG-INF + (-1) (lower bound); `ineq' refutes either.  pos-inf-above-reals: POS-INF <= x
;;; and x <= POS-INF give x = POS-INF by antisymmetry, so POS-INF would be real.
;;; neg-inf-below-reals likewise from neg-inf-not-in-rr.  The order laws by cases on
;;; rr-star-membership, every infinite case pushed onto a bound by the two -eq lemmas.
;;;
;;; LOAD WINDOW: after theorem-library/rr-order-basics (rr-lt-irrefl, through dk-absurd!),
;;; `prop' and structure-library/extended-reals; BEFORE theorem-library/rake-infinity-points
;;; (load.scm 1043), whose pos-inf-not-in-rr proof cites pos-inf-above-reals.  Slot: right
;;; after theorem-library/rake-rr-order-leaves (1038).
;;; Helper prefix: rsm-.

;;; (IN TM RR-STAR), from the disjunct KEEPER of rr-star-membership (in context)
(define (rsm-star! tm keeper)
  (let ((g (list 'IN tm 'RR-STAR)))
    (if (not (dk-asm? g))
        (dk-have! g
          (lambda ()
            (let ((inst (dk-cite! 'rr-star-membership tm)))
              (if (dk-only! inst keeper) (prop))))))))

(define (rsm-star-const! c)
  (let ((e (list '= c c)))
    (if (not (dk-asm? e)) (dk-have! e (lambda () (rfl))))
    (rsm-star! c e)))

(define (rsm-vars landed)
  (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)))) landed)))

(define (rsm-and! . fs)
  (let ((c (let loop ((l fs)) (if (null? (cdr l)) (car l) (list 'AND (car l) (loop (cdr l)))))))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (ass))))))))

;;; use-cases that skips a branch hash-consing already grounded (copy of eio-use-cases!)
(define (rsm-use-cases! disjuncts . bodies)
  (let* ((result (use-cases disjuncts))
         (ob     (cases-obligation result))
         (cs     (cdr (assq 'cases result))))
    (if ob (error "rsm-use-cases!: the disjunction is not in context" disjuncts))
    (if (not (= (length cs) (length bodies)))
        (error "rsm-use-cases!: branch count" (length cs) (length bodies)))
    (for-each (lambda (mc body)
                (if (not (sequent-node-grounded? (cdr mc)))
                    (begin (dk-focus! (cdr mc)) (body))))
              cs bodies)))

;;; TM in RR-STAR in context: three cases, real / POS-INF / NEG-INF
(define (rsm-cases! tm real! pinf! ninf!)
  (let ((d (list 'OR (list 'IN tm 'RR) (list 'OR (list '= tm 'POS-INF) (list '= tm 'NEG-INF)))))
    (if (not (dk-asm? d))
        (dk-have! d
          (lambda ()
            (let ((i (dk-cite! 'rr-star-membership tm)))
              (if (dk-only! i (list 'IN tm 'RR-STAR)) (prop))))))
    (rsm-use-cases! (list (list 'IN tm 'RR) (list '= tm 'POS-INF) (list '= tm 'NEG-INF))
                    real! pinf! ninf!)))

;;; land the atom ATOM from a context atom by putting the case equations EQS back
;;; (each (= var const)): every const of EQS in the goal is rewritten to its var
(define (rsm-lift! atom eqs)
  (if (not (dk-asm? atom))
      (dk-have! atom
        (lambda ()
          (for-each (lambda (e) (if (dk-contains? (dk-goal) (caddr e)) (subst (list '= (caddr e) (cadr e)))))
                    eqs)
          (ass)))))

;;; the converse: land ATOM (mentioning the case variables) from the context atom it
;;; becomes when every var of EQS is rewritten to its const
(define (rsm-drop! atom eqs)
  (if (not (dk-asm? atom))
      (dk-have! atom
        (lambda ()
          (for-each (lambda (e) (if (dk-contains? (dk-goal) (cadr e)) (subst e))) eqs)
          (ass)))))

;;; ---------------------------------------------------------------------------
;;; pos-inf-above-reals -- statement copied literally from extended-reals.scm
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (NOT (<= POS-INF x))))))
(let ((x (car (rsm-vars (dk-peel!)))))
  (di)                                          ; (<= POS-INF x) assumed; FALSITY
  (rsm-star! x (list 'IN x 'RR))
  (rsm-star-const! 'POS-INF)
  (dk-cite! 'pos-inf-upper-bound x)             ; x <= POS-INF
  (rsm-and! '(IN POS-INF RR-STAR) (list 'IN x 'RR-STAR))
  (rsm-and! (list '<= 'POS-INF x) (list '<= x 'POS-INF))
  (dk-cite! 'rr-star-leq-antisymmetric 'POS-INF x)          ; POS-INF = x
  (dk-have! '(IN POS-INF RR) (lambda () (subst (list '= 'POS-INF x)) (ass)))
  (dk-cite! 'rr-one-in)
  (rsm-and! '(IN POS-INF RR) '(IN 1 RR))
  (dk-cite! 'rr-add-closed 'POS-INF 1)          ; POS-INF + 1 in RR
  (rsm-star! '(+ POS-INF 1) '(IN (+ POS-INF 1) RR))
  (dk-cite! 'pos-inf-upper-bound '(+ POS-INF 1))
  (dk-absurd! '(IN POS-INF RR) '(<= (+ POS-INF 1) POS-INF)))
(qed 'pos-inf-above-reals)
(topic! 'pos-inf-above-reals 'analysis)

;;; ---------------------------------------------------------------------------
;;; neg-inf-not-in-rr -- statement copied literally from extended-reals.scm
(sp (make-wff '(NOT (IN NEG-INF RR))))
(di)                                            ; (IN NEG-INF RR) assumed; FALSITY
(dk-cite! 'rr-one-in)
(dk-cite! 'rr-neg-closed 1)                     ; (- 1) in RR
(rsm-and! '(IN NEG-INF RR) '(IN (- 1) RR))
(dk-cite! 'rr-add-closed 'NEG-INF '(- 1))
(rsm-star! '(+ NEG-INF (- 1)) '(IN (+ NEG-INF (- 1)) RR))
(dk-cite! 'neg-inf-lower-bound '(+ NEG-INF (- 1)))
(dk-absurd! '(IN NEG-INF RR) '(<= NEG-INF (+ NEG-INF (- 1))))
(qed 'neg-inf-not-in-rr)
(topic! 'neg-inf-not-in-rr 'analysis)

;;; ---------------------------------------------------------------------------
;;; neg-inf-below-reals -- statement copied literally from scratchpad/extinf/neg-inf-below-reals.scm
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (NOT (<= x NEG-INF))))))
(let ((x (car (rsm-vars (dk-peel!)))))
  (di)                                          ; (<= x NEG-INF) assumed; FALSITY
  (rsm-star! x (list 'IN x 'RR))
  (rsm-star-const! 'NEG-INF)
  (dk-cite! 'neg-inf-lower-bound x)             ; NEG-INF <= x
  (rsm-and! (list 'IN x 'RR-STAR) '(IN NEG-INF RR-STAR))
  (rsm-and! (list '<= x 'NEG-INF) (list '<= 'NEG-INF x))
  (dk-cite! 'rr-star-leq-antisymmetric x 'NEG-INF)          ; x = NEG-INF
  (dk-have! '(IN NEG-INF RR) (lambda () (subst (list '= 'NEG-INF x)) (ass)))
  (fact 'neg-inf-not-in-rr)
  (ai '(NOT (IN NEG-INF RR))))
(qed 'neg-inf-below-reals)
(topic! 'neg-inf-below-reals 'analysis)

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL x (IMPLIES (IN x RR-STAR) (IMPLIES (<= POS-INF x) (= x POS-INF))))))
(let ((x (car (rsm-vars (dk-peel!)))))
  (rsm-star-const! 'POS-INF)
  (dk-cite! 'pos-inf-upper-bound x)
  (rsm-and! (list 'IN x 'RR-STAR) '(IN POS-INF RR-STAR))
  (rsm-and! (list '<= x 'POS-INF) (list '<= 'POS-INF x))
  (dk-cite! 'rr-star-leq-antisymmetric x 'POS-INF)
  (ass))
(qed 'rr-star-le-pos-inf-eq)
(topic! 'rr-star-le-pos-inf-eq 'analysis)

(sp (make-wff '(FORALL x (IMPLIES (IN x RR-STAR) (IMPLIES (<= x NEG-INF) (= x NEG-INF))))))
(let ((x (car (rsm-vars (dk-peel!)))))
  (rsm-star-const! 'NEG-INF)
  (dk-cite! 'neg-inf-lower-bound x)
  (rsm-and! (list 'IN x 'RR-STAR) '(IN NEG-INF RR-STAR))
  (rsm-and! (list '<= x 'NEG-INF) (list '<= 'NEG-INF x))
  (dk-cite! 'rr-star-leq-antisymmetric x 'NEG-INF)
  (ass))
(qed 'rr-star-le-neg-inf-eq)
(topic! 'rr-star-le-neg-inf-eq 'analysis)

;;; ---------------------------------------------------------------------------
;;; rr-star-leq-reflexive -- statement copied literally from rr-star-order.scm
(sp (make-wff '(FORALL a (IMPLIES (IN a RR-STAR) (<= a a)))))
(let ((x (car (rsm-vars (dk-peel!)))))
  (rsm-cases! x
    (lambda () (dk-cite! 'rr-leq-reflexive x) (ass))
    (lambda ()
      (subst (list '= x 'POS-INF))
      (rsm-star-const! 'POS-INF)
      (dk-cite! 'pos-inf-upper-bound 'POS-INF)
      (ass))
    (lambda ()
      (subst (list '= x 'NEG-INF))
      (rsm-star-const! 'NEG-INF)
      (dk-cite! 'neg-inf-lower-bound 'NEG-INF)
      (ass))))
(qed 'rr-star-leq-reflexive)
(topic! 'rr-star-leq-reflexive 'analysis)

;;; ---------------------------------------------------------------------------
;;; rr-star-leq-transitive -- statement copied literally from rr-star-order.scm
(sp (make-wff '(FORALL a (FORALL b (FORALL c
        (IMPLIES (AND (IN a RR-STAR) (AND (IN b RR-STAR) (IN c RR-STAR)))
                 (IMPLIES (AND (<= a b) (<= b c)) (<= a c))))))))
(dk-peel!)
(dk-split-all!)
(let* ((g (dk-goal)) (a (cadr g)) (c (caddr g))
       (ab (car (filter (lambda (f) (and (dk-head-is? f '<=) (eq? (cadr f) a) (not (eq? (caddr f) c))))
                        (dk-asms))))
       (b (caddr ab))
       (ea+ (list '= a 'POS-INF)) (ea- (list '= a 'NEG-INF))
       (eb+ (list '= b 'POS-INF)) (eb- (list '= b 'NEG-INF))
       (ec+ (list '= c 'POS-INF)) (ec- (list '= c 'NEG-INF))
       (to-lb! (lambda (ea)              ; a = NEG-INF in context: the goal is the lower bound at c
                 (subst ea) (dk-cite! 'neg-inf-lower-bound c) (ass)))
       (to-ub! (lambda (ec)              ; c = POS-INF in context: the goal is the upper bound at a
                 (subst ec) (dk-cite! 'pos-inf-upper-bound a) (ass))))
  (rsm-cases! a
    (lambda ()
      (rsm-cases! c
        (lambda ()
          (rsm-cases! b
            (lambda () (dk-ineq! (list 'IN a 'RR) (list 'IN b 'RR) (list 'IN c 'RR)
                                 (list '<= a b) (list '<= b c)))
            (lambda ()                   ; b = POS-INF: then c = POS-INF
              (rsm-lift! (list '<= 'POS-INF c) (list eb+))
              (dk-cite! 'rr-star-le-pos-inf-eq c)
              (to-ub! ec+))
            (lambda ()                   ; b = NEG-INF: then a = NEG-INF
              (rsm-lift! (list '<= a 'NEG-INF) (list eb-))
              (dk-cite! 'rr-star-le-neg-inf-eq a)
              (to-lb! ea-))))
        (lambda () (to-ub! ec+))
        (lambda ()                       ; c = NEG-INF: then b = NEG-INF, then a = NEG-INF
          (rsm-lift! (list '<= b 'NEG-INF) (list ec-))
          (dk-cite! 'rr-star-le-neg-inf-eq b)
          (rsm-lift! (list '<= a 'NEG-INF) (list eb-))
          (dk-cite! 'rr-star-le-neg-inf-eq a)
          (to-lb! ea-))))
    (lambda ()                           ; a = POS-INF: then b = POS-INF, then c = POS-INF
      (rsm-lift! (list '<= 'POS-INF b) (list ea+))
      (dk-cite! 'rr-star-le-pos-inf-eq b)
      (rsm-lift! (list '<= 'POS-INF c) (list eb+))
      (dk-cite! 'rr-star-le-pos-inf-eq c)
      (to-ub! ec+))
    (lambda () (to-lb! ea-))))
(qed 'rr-star-leq-transitive)
(topic! 'rr-star-leq-transitive 'analysis)

;;; ---------------------------------------------------------------------------
;;; rr-star-leq-total -- statement copied literally from rr-star-order.scm
(sp (make-wff '(FORALL a (FORALL b
        (IMPLIES (AND (IN a RR-STAR) (IN b RR-STAR))
                 (OR (<= a b) (<= b a)))))))
(dk-peel!)
(dk-split-all!)
(let* ((g (dk-goal)) (a (cadr (cadr g))) (b (caddr (cadr g)))
       (close! (lambda (atom) (if (dk-only! atom) (prop)))))
  (rsm-cases! a
    (lambda ()
      (rsm-cases! b
        (lambda ()
          (rsm-and! (list 'IN a 'RR) (list 'IN b 'RR))
          (dk-cite! 'rr-leq-total a b)
          (ass))
        (lambda ()
          (dk-cite! 'pos-inf-upper-bound a)
          (rsm-drop! (list '<= a b) (list (list '= b 'POS-INF)))
          (close! (list '<= a b)))
        (lambda ()
          (dk-cite! 'neg-inf-lower-bound a)
          (rsm-drop! (list '<= b a) (list (list '= b 'NEG-INF)))
          (close! (list '<= b a)))))
    (lambda ()
      (dk-cite! 'pos-inf-upper-bound b)
      (rsm-drop! (list '<= b a) (list (list '= a 'POS-INF)))
      (close! (list '<= b a)))
    (lambda ()
      (dk-cite! 'neg-inf-lower-bound b)
      (rsm-drop! (list '<= a b) (list (list '= a 'NEG-INF)))
      (close! (list '<= a b)))))
(qed 'rr-star-leq-total)
(topic! 'rr-star-leq-total 'analysis)
