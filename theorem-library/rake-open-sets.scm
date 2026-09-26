;;; rake-open-sets.scm -- the metric topology axioms, PROVEN.
;;;
;;; Eight supports of structure-library/metric-open-sets.scm, every one of them
;;; warranted `proof' -- "a machine-checked proof exists" -- with no proof in the
;;; tree.  The warrants are the proof plans and are followed here.
;;;
;;;   empty-is-open                      {} is open
;;;   carrier-is-open                    PTS(s) is open
;;;   union-of-opens-open                an indexed union of opens is open
;;;   inter-of-opens-open                a binary intersection of opens is open
;;;   preimage-complement                f^-1(PTS(t)\U) = PTS(s)\f^-1(U)
;;;   open-preimage-implies-continuous   opens pull back open  =>  f continuous
;;;   continuous-implies-closed-preimage f continuous  =>  closeds pull back closed
;;;   closed-preimage-implies-continuous closeds pull back closed  =>  f continuous
;;;
;;; Every statement is copied LITERALLY from its support site
;;; (structure-library/metric-open-sets.scm:64, :72, :84, :94, :165, :135, :177, :186).
;;;
;;; THE ARGUMENTS.
;;;   empty / carrier    IS-OPEN unfolds to three conjuncts; for {} the
;;;     point-quantifier is vacuous (empty-set-has-no-members) and the inclusion
;;;     vacuous too.  For PTS(s) the inclusion is reflexivity and radius 1 serves
;;;     at every point, BALL(s,y,1) being a SEP over PTS(s) -- (mac 'BALL) plus
;;;     the kernel sep rules, no ball support cited.
;;;   union              A point of the union lies in some g(i) (bu-me); that
;;;     term's own witnessing ball is inside g(i), hence inside the union (bu-mi
;;;     at the same index).
;;;   intersection       rr-min-pos supplies a positive lower bound m of the two
;;;     radii -- no MIN operator -- and the BALL(s,y,m) subset BALL(s,y,r) step is
;;;     done inline: open the SEP (ball-sep-unfold), one `ineq' over
;;;     d <= m, m <= r, and close the SEP again (sep-mi).
;;;   preimage-complement  class-extensionality (no sethood obligation), then the
;;;     two directions off preimage-membership and complement-in-membership.
;;;   open-preimage      At a in PTS(s) with eps > 0, V = BALL(t, f(a), eps) is
;;;     open (ball-is-open) and contains f(a) (metric-self-zero), so a is in the
;;;     open set f^-1(V), which therefore holds a ball of radius r about a.  The
;;;     definition of IS-CONTINUOUS-AT gives a NON-STRICT bound d(a,b) <= delta
;;;     while ball membership is STRICT, so delta is r/2 (dk-halve!), not r.
;;;   closed-preimage    The complement flip.  It needs PTS \ (PTS \ X) = X for
;;;     X subset PTS, which the tree does not have; rko-dbl-comp! proves it in
;;;     place (unfold both complement memberships, then `prop').
;;;
;;; CITATIONS, with 0-based load positions over the quoted names in load.scm:
;;;   primitive (theory.scm): empty-set-has-no-members, subset-def,
;;;     class-extensionality, complement-in-membership, intersection-membership.
;;;   definitional: preimage-membership (metric-open-sets, stamped at
;;;     structure-library/definitional-reclass 106); the is-open / is-closed /
;;;     is-continuous / is-continuous-at / pos-rr / < unfolds; the BALL and
;;;     PREIMAGE functoid unfolds.
;;;   proven: eq-sym 148, fun-apply-type-c 163, rr-min-pos 175,
;;;     rr-pos-rr-in-rr + rr-lt-of-pos-rr 177, rr-pos-rr-of-lt 183,
;;;     rr-pos-halvable 184 (through dk-halve!), subset-mem-fwd 192,
;;;     metric-dist-real 198, complement-in-subset 242, ball-sep-unfold 246,
;;;     metric-self-zero 255, ball-is-open 271.
;;;   ASSERTED, and deliberately: continuous-implies-open-preimage
;;;     (metric-open-sets.scm:112, `informal').  It is the ONE leaf of
;;;     continuous-implies-closed-preimage's bill; the warrant of that support
;;;     names it, and it is not in this batch.
;;;
;;; LOAD WINDOW [272, 464).  lo is forced by ball-is-open (271), the latest
;;; citation; hi by theorem-library/metric-top-proof (464), the only proven citer
;;; of the first four (pss-topics, 483, merely files them by topic).  The last
;;; four are cited by nothing proven.
;;;
;;; Helper prefix: rko-.

;;; -----------------------------------------------------------------------
;;; Shared helpers.

(define (rko-head? f h) (and (pair? f) (eq? (car f) h)))
(define (rko-in? f set) (and (rko-head? f 'IN) (equal? (caddr f) set)))

;; run THUNK (a branching tactic) and visit each opened leaf with VISIT.
(define (rko-each-leaf! thunk visit)
  (for-each (lambda (leaf) (dk-focus! leaf) (visit)) (dk-opened thunk)))

;; goal (SUBSET A B): unfold and introduce the element; return the landed (IN z A).
(define (rko-subset-elt!)
  (mac 'subset-def)
  (dk-landed-1 (lambda () (di))))

;; (IN z EMPTY-SET) in context: close anything.
(define (rko-absurd! z)
  (fact 'empty-set-has-no-members z)
  (ai `(NOT (IN ,z EMPTY-SET))))

;; (IS-OPEN s U) in context -> its conjuncts, split, returned.  DESTRUCTIVE
;; (mac-h replaces the hypothesis), so call it in a have! lane when IS-OPEN
;; itself is still wanted.
(define (rko-open-h! op) (dk-split! (dk-landed-1 (lambda () (mac-h 'is-open op)))))

;; the interior universal of an unfolded IS-OPEN, picked by the SET its guard
;; ranges over -- never by head alone (two of them are in context at once).
(define (rko-interior-univ set)
  (dk-pick (lambda (f)
             (and (rko-head? f 'FORALL) (rko-head? (caddr f) 'IMPLIES)
                  (let ((ante (cadr (caddr f))))
                    (and (rko-head? ante 'IN) (equal? (caddr ante) set)))))
           "the interior universal"))

;; 1-based context index of FORM, for `ineq' (ineq-oracle.scm:206).
(define (rko-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rko-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))

;; goal (IN z (BALL sp c r)): the SEP intro, both leaves from context.
(define (rko-ball-goal!)
  (mac 'BALL)
  (rko-each-leaf! (lambda () (sep-mi)) (lambda () (dk-conj-close!))))

;; (IN z (BALL sp c r)) in context -> (IN z (PTS sp)), (<= d r), (NOT (= d r)).
;; mac-h cannot unfold the BALL functoid by its own name; ball-sep-unfold is the
;; PROVEN unfold equation and rebuilds the rule from the theorem table.
(define (rko-ball-h! mem)
  (dk-split-all!
   (dk-landed (lambda () (sep-me (dk-landed-1 (lambda () (mac-h 'ball-sep-unfold mem))))))))

;; (POS-RR e) in context -> (IN e RR), (<= 0 e), (NOT (= 0 e)), and the AND of
;; the three, which is ball-is-open's antecedent (`fact' will not split one).
(define (rko-pos-parts! e)
  (fact 'rr-pos-rr-in-rr e)
  (let ((lt (dk-fact! 'rr-lt-of-pos-rr e)))
    (dk-split! (dk-landed-1 (lambda () (mac-h '< lt)))))
  (have! `(AND (IN ,e RR) (AND (<= 0 ,e) (NOT (= 0 ,e))))))

;;; -----------------------------------------------------------------------
;;; empty-is-open

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-OPEN s EMPTY-SET)))))
(dk-peel!)
(mac 'is-open)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((rko-head? g 'IS-METRIC-SPACE) (ass))
           ((rko-head? g 'SUBSET) (rko-absurd! (cadr (rko-subset-elt!))))
           ((rko-head? g 'FORALL) (rko-absurd! (cadr (car (dk-peel!)))))
           (#t (error "empty-is-open: unexpected conjunct" (expression->string g)))))))
(qed 'empty-is-open)
(topic! 'empty-is-open 'topology)

;;; -----------------------------------------------------------------------
;;; carrier-is-open

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IS-OPEN s (PTS s))))))
(dk-peel!)
(mac 'is-open)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((rko-head? g 'IS-METRIC-SPACE) (ass))
           ((rko-head? g 'SUBSET) (rko-subset-elt!) (ass))
           ((rko-head? g 'FORALL)
            (dk-peel!)
            (have! '(POS-RR 1) (lambda () (mac 'pos-rr) (arith)))
            (ew 1)
            (dk-conj-close!
             (lambda ()
               (if (rko-head? (dk-goal) 'POS-RR)
                   (ass)
                   ;; BALL(s,y,1) subset PTS(s): a SEP over PTS(s), no support
                   (begin (mac 'BALL)
                          (let ((m (rko-subset-elt!)))
                            (dk-split-all! (dk-landed (lambda () (sep-me m))))
                            (ass)))))))
           (#t (error "carrier-is-open: unexpected conjunct" (expression->string g)))))))
(qed 'carrier-is-open)
(topic! 'carrier-is-open 'topology)

;;; -----------------------------------------------------------------------
;;; union-of-opens-open

;; (IN z (BIG-UNION i A (g i))) in context: eliminate; return the index
;; eigenvariable, read off the landed (IN z (g e)).
(define (rko-bu-elim! mem)
  (let* ((z (cadr mem))
         (landed (dk-landed (lambda () (bu-me mem))))
         (hit (find-first (lambda (f) (and (rko-head? f 'IN) (equal? (cadr f) z)
                                           (pair? (caddr f))))
                          landed)))
    (if (not hit)
        (error "rko-bu-elim!: no (IN z (g e)) landed" (map expression->string landed)))
    (cadr (caddr hit))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (FORALL g
       (IMPLIES (FORALL i (IMPLIES (IN i A) (IS-OPEN s (g i))))
         (IS-OPEN s (BIG-UNION i A (g i))))))))))
(define rko-u-hyp
  (let ((landed (dk-peel!)))
    (or (find-first (lambda (f) (rko-head? f 'FORALL)) landed)
        (error "union-of-opens-open: no openness hypothesis landed"
               (map expression->string landed)))))

(mac 'is-open)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((rko-head? g 'IS-METRIC-SPACE) (ass))
      ((rko-head? g 'SUBSET)
       (let* ((mem (rko-subset-elt!))            ; (IN z (BIG-UNION i a (g i)))
              (z   (cadr mem))
              (e   (rko-bu-elim! mem)))
         (rko-open-h! (dk-apply! rko-u-hyp e))
         (fact 'subset-mem-fwd `(g ,e) (caddr g) z)
         (ass)))
      ((rko-head? g 'FORALL)
       (let* ((mem (car (dk-peel!)))             ; (IN y (BIG-UNION i a (g i)))
              (y   (cadr mem))
              (e   (rko-bu-elim! mem)))
         (rko-open-h! (dk-apply! rko-u-hyp e))
         (let* ((ex (dk-apply! (rko-interior-univ `(g ,e)) y))
                (r0 (dk-skolem! ex)))
           (ew r0)
           (dk-conj-close!
            (lambda ()
              (if (rko-head? (dk-goal) 'POS-RR)
                  (ass)
                  (let* ((m2 (rko-subset-elt!))  ; (IN w (BALL s y r0))
                         (w  (cadr m2)))
                    (fact 'subset-mem-fwd `(BALL s ,y ,r0) `(g ,e) w)
                    (rko-each-leaf! (lambda () (bu-mi e)) (lambda () (ass))))))))))
      (#t (error "union-of-opens-open: unexpected conjunct" (expression->string g)))))))
(qed 'union-of-opens-open)
(topic! 'union-of-opens-open 'topology)

;;; -----------------------------------------------------------------------
;;; inter-of-opens-open

;; DESTRUCTIVE in (IS-OPEN s U): split it, instantiate its interior universal
;; at Y, skolemize; return the radius.
(define (rko-radius! op y)
  (rko-open-h! op)
  (dk-skolem! (dk-apply! (rko-interior-univ (caddr op)) y)))

;; goal (SUBSET (BALL s y m) (INTERSECTION u w)), with m <= ru, m <= rw and
;; (SUBSET (BALL s y ru) u), (SUBSET (BALL s y rw) w) in context.
(define (rko-inter-ball! y m ru rw)
  (let* ((mem (rko-subset-elt!))                 ; (IN z (BALL s y m))
         (z   (cadr mem))
         (d   `((DIST s) ,y ,z)))
    (rko-ball-h! mem)
    (fact 'subset-mem-fwd 'u '(PTS s) y)
    (fact 'metric-dist-real 's y z)
    (have! `(< ,d ,m) (lambda () (mac '<) (from-context!)))
    (for-each
     (lambda (r)
       (have! `(< ,d ,r) (lambda () (ineq (rko-idx `(< ,d ,m)) (rko-idx `(<= ,m ,r)))))
       (dk-split! (dk-landed-1 (lambda () (mac-h '< `(< ,d ,r)))))
       (have! `(IN ,z (BALL s ,y ,r)) (lambda () (rko-ball-goal!))))
     (list ru rw))
    (fact 'subset-mem-fwd `(BALL s ,y ,ru) 'u z)
    (fact 'subset-mem-fwd `(BALL s ,y ,rw) 'w z)
    (mac 'intersection-membership)
    (dk-conj-close!)))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL U (FORALL W
       (IMPLIES (AND (IS-OPEN s U) (IS-OPEN s W))
         (IS-OPEN s (INTERSECTION U W)))))))))
(dk-split-all! (dk-peel!))
(mac 'is-open)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((rko-head? g 'IS-METRIC-SPACE) (ass))
      ((rko-head? g 'SUBSET)
       (let* ((mem (rko-subset-elt!))            ; (IN z (INTERSECTION u w))
              (z   (cadr mem)))
         (dk-split-all! (dk-landed (lambda () (mac-h 'intersection-membership mem))))
         (rko-open-h! '(IS-OPEN s u))
         (fact 'subset-mem-fwd 'u '(PTS s) z)
         (ass)))
      ((rko-head? g 'FORALL)
       (let* ((mem (car (dk-peel!)))             ; (IN y (INTERSECTION u w))
              (y   (cadr mem)))
         (dk-split-all! (dk-landed (lambda () (mac-h 'intersection-membership mem))))
         (let* ((ru (rko-radius! '(IS-OPEN s u) y))
                (rw (rko-radius! '(IS-OPEN s w) y)))
           (fact 'rr-pos-rr-in-rr ru) (fact 'rr-lt-of-pos-rr ru)
           (fact 'rr-pos-rr-in-rr rw) (fact 'rr-lt-of-pos-rr rw)
           (let ((mm (dk-skolem! (dk-fact! 'rr-min-pos ru rw))))
             (fact 'rr-pos-rr-of-lt mm)
             (ew mm)
             (dk-conj-close!
              (lambda ()
                (if (rko-head? (dk-goal) 'POS-RR)
                    (ass)
                    (rko-inter-ball! y mm ru rw))))))))
      (#t (error "inter-of-opens-open: unexpected conjunct" (expression->string g)))))))
(qed 'inter-of-opens-open)
(topic! 'inter-of-opens-open 'topology)

;;; -----------------------------------------------------------------------
;;; preimage-complement

(define rko-pc-lhs '(PREIMAGE s f (COMPLEMENT-IN (PTS t) u)))
(define rko-pc-rhs '(COMPLEMENT-IN (PTS s) (PREIMAGE s f u)))

(define (rko-pc-fwd! x)                          ; ctx (IN x LHS), goal (IN x RHS)
  (dk-split! (dk-landed-1 (lambda () (mac-h 'preimage-membership `(IN ,x ,rko-pc-lhs)))))
  (let ((cm (dk-pick (lambda (a) (and (rko-head? a 'IN) (rko-head? (caddr a) 'COMPLEMENT-IN)))
                     "f(x) in the complement")))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'complement-in-membership cm)))))
  (let ((neg (dk-pick (lambda (a) (rko-head? a 'NOT)) "not f(x) in u")))
    (mac 'complement-in-membership)
    (dk-conj-close!
     (lambda ()
       (if (rko-head? (dk-goal) 'NOT)
           (begin (di)                           ; assume (IN x (PREIMAGE s f u))
                  (dk-split! (dk-landed-1
                              (lambda () (mac-h 'preimage-membership `(IN ,x (PREIMAGE s f u))))))
                  (ai neg))
           (ass))))))

(define (rko-pc-bwd! x)                          ; ctx (IN x RHS), goal (IN x LHS)
  (dk-split! (dk-landed-1 (lambda () (mac-h 'complement-in-membership `(IN ,x ,rko-pc-rhs)))))
  (let ((neg (dk-pick (lambda (a) (rko-head? a 'NOT)) "not x in the preimage")))
    (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) x)
    (mac 'preimage-membership)
    (dk-conj-close!
     (lambda ()
       (if (rko-in? (dk-goal) '(PTS s))
           (ass)
           (begin
             (mac 'complement-in-membership)
             (dk-conj-close!
              (lambda ()
                (if (rko-head? (dk-goal) 'NOT)
                    (begin (di)                  ; assume (IN (f x) u)
                           (have! `(IN ,x (PREIMAGE s f u))
                                  (lambda () (mac 'preimage-membership) (dk-conj-close!)))
                           (ai neg))
                    (ass))))))))))

(define (rko-pc-branch!)
  (let ((g (dk-goal)))
    (if (rko-in? g rko-pc-rhs) (rko-pc-fwd! (cadr g)) (rko-pc-bwd! (cadr g)))))

(sp (make-wff '(FORALL s (FORALL t (FORALL f (FORALL U
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IS-METRIC-SPACE t)
                   (IN f (FUN (PTS s) (PTS t)))))
       (= (PREIMAGE s f (COMPLEMENT-IN (PTS t) U))
          (COMPLEMENT-IN (PTS s) (PREIMAGE s f U))))))))))
(dk-split-all! (dk-peel!))
(have! `(FORALL x_ (IFF (IN x_ ,rko-pc-lhs) (IN x_ ,rko-pc-rhs)))
  (lambda ()
    (for-each
     (lambda (l)
       (dk-focus! l)
       (if (rko-head? (dk-goal) 'IFF)
           (rko-each-leaf! (lambda () (di)) rko-pc-branch!)
           (rko-pc-branch!)))
     (dk-opened (lambda () (di))))))
(fact 'class-extensionality rko-pc-lhs rko-pc-rhs)
(ass)
(qed 'preimage-complement)
(topic! 'preimage-complement 'topology)

;;; -----------------------------------------------------------------------
;;; open-preimage-implies-continuous

(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IS-METRIC-SPACE t)
                   (IN f (FUN (PTS s) (PTS t)))))
       (IMPLIES (FORALL V (IMPLIES (IS-OPEN t V)
                  (IS-OPEN s (PREIMAGE s f V))))
         (IS-CONTINUOUS s t f))))))))
(dk-split-all! (dk-peel!))
(define rko-opc-h
  (dk-pick (lambda (a) (and (rko-head? a 'FORALL) (rko-head? (caddr a) 'IMPLIES)
                            (rko-head? (cadr (caddr a)) 'IS-OPEN)))
           "the open-preimage hypothesis"))

;; the eps/delta conjunct of IS-CONTINUOUS-AT at the point A, radius EPS.
(define (rko-opc-delta! a eps)
  (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) a)
  (rko-pos-parts! eps)
  (let ((V `(BALL t (f ,a) ,eps)))
    (fact 'metric-self-zero 't `(f ,a))
    (have! `(IN ,a (PREIMAGE s f ,V))       ; f(a) is at distance 0 < eps from itself
      (lambda ()
        (mac 'preimage-membership)
        (dk-conj-close!
         (lambda ()
           (if (rko-in? (dk-goal) '(PTS s))
               (ass)
               (begin (mac 'BALL)
                      (rko-each-leaf!
                       (lambda () (sep-mi))
                       (lambda ()
                         (if (rko-head? (dk-goal) 'AND)
                             (begin (subst `(= ((DIST t) (f ,a) (f ,a)) 0))
                                    (dk-conj-close!))
                             (ass))))))))))
    (fact 'ball-is-open 't `(f ,a) eps)
    (rko-open-h! (dk-apply! rko-opc-h V))
    (let* ((ex (dk-apply! (rko-interior-univ `(PREIMAGE s f ,V)) a))
           (r0 (dk-skolem! ex)))
      (fact 'rr-pos-rr-in-rr r0)
      ;; ball membership is STRICT, the definition's bound is NOT: halve.
      (let ((h (dk-halve! r0)))
        (have! `(< ,h ,r0)
          (lambda () (ineq (rko-idx `(= (+ ,h ,h) ,r0)) (rko-idx `(< 0 ,h)))))
        (ew h)
        (dk-conj-close!
         (lambda ()
           (if (rko-head? (dk-goal) 'POS-RR)
               (ass)
               (let* ((landed (dk-peel!))
                      (b (cadr (or (find-first (lambda (q) (rko-in? q '(PTS s))) landed)
                                   (error "open-preimage: no (IN b (PTS s)) landed"
                                          (map expression->string landed)))))
                      (d `((DIST s) ,a ,b)))
                 (fact 'metric-dist-real 's a b)
                 (have! `(< ,d ,r0)
                   (lambda () (ineq (rko-idx `(<= ,d ,h)) (rko-idx `(< ,h ,r0)))))
                 (dk-split! (dk-landed-1 (lambda () (mac-h '< `(< ,d ,r0)))))
                 (have! `(IN ,b (BALL s ,a ,r0)) (lambda () (rko-ball-goal!)))
                 (fact 'subset-mem-fwd `(BALL s ,a ,r0) `(PREIMAGE s f ,V) b)
                 (dk-split! (dk-landed-1
                             (lambda () (mac-h 'preimage-membership `(IN ,b (PREIMAGE s f ,V))))))
                 (rko-ball-h! `(IN (f ,b) ,V))
                 (ass)))))))))

(mac 'is-continuous)
(dk-conj-close!
 (lambda ()
   (if (rko-head? (dk-goal) 'FORALL)
       (let ((a (cadr (car (dk-peel!)))))
         (mac 'is-continuous-at)
         (dk-conj-close!
          (lambda ()
            (if (rko-head? (dk-goal) 'FORALL)
                (rko-opc-delta! a (cadr (car (dk-peel!))))
                (ass)))))
       (ass))))
(qed 'open-preimage-implies-continuous)
(topic! 'open-preimage-implies-continuous 'topology)

;;; -----------------------------------------------------------------------
;;; continuous-implies-closed-preimage
;;;
;;; The ONE asserted leaf of this file's bills enters here:
;;; continuous-implies-open-preimage (metric-open-sets.scm:112, `informal').

(define rko-typings
  '(AND (IS-METRIC-SPACE s) (AND (IS-METRIC-SPACE t) (IN f (FUN (PTS s) (PTS t))))))

;; the three typing conjuncts of (IS-CONTINUOUS s t f), read off in a have! lane
;; so the hypothesis itself survives (mac-h is destructive).
(define (rko-cont-typings!)
  (have! rko-typings
    (lambda ()
      (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous '(IS-CONTINUOUS s t f)))))
      (dk-conj-close!))))

(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-CONTINUOUS s t f)
       (FORALL A (IMPLIES (IS-CLOSED t A)
         (IS-CLOSED s (PREIMAGE s f A))))))))))
(dk-peel!)
(mac 'is-closed)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((rko-head? g 'IS-METRIC-SPACE)
       (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous '(IS-CONTINUOUS s t f)))))
       (ass))
      ((rko-head? g 'SUBSET)                     ; the preimage is a SEP over PTS(s)
       (let ((mem (rko-subset-elt!)))
         (dk-split! (dk-landed-1 (lambda () (mac-h 'preimage-membership mem))))
         (ass)))
      ((rko-head? g 'IS-OPEN)
       (dk-split! (dk-landed-1 (lambda () (mac-h 'is-closed '(IS-CLOSED t a)))))
       (rko-cont-typings!)
       (let ((eqn (dk-fact! 'preimage-complement 's 't 'f 'a)))
         (fact 'eq-sym (cadr eqn) (caddr eqn))
         (subst `(= ,(caddr eqn) ,(cadr eqn)))   ; PTS(s)\f^-1(a) -> f^-1(PTS(t)\a)
         (dk-apply! (dk-fact! 'continuous-implies-open-preimage 's 't 'f)
                    '(COMPLEMENT-IN (PTS t) a))
         (ass)))
      (#t (error "continuous-implies-closed-preimage: unexpected conjunct"
                 (expression->string g)))))))
(qed 'continuous-implies-closed-preimage)
(topic! 'continuous-implies-closed-preimage 'topology)

;;; -----------------------------------------------------------------------
;;; closed-preimage-implies-continuous

;; does F contain a membership in a relative complement?
(define (rko-comp-mem? f)
  (cond ((not (pair? f)) #f)
        ((and (eq? (car f) 'IN) (pair? (caddr f)) (eq? (car (caddr f)) 'COMPLEMENT-IN)) #t)
        (#t (and (any-pred rko-comp-mem? (cdr f)) #t))))

(define (rko-unfold-comp-h! form)
  (let loop ((f form))
    (if (rko-comp-mem? f)
        (loop (dk-landed-1 (lambda () (mac-h 'complement-in-membership f))))
        f)))

(define (rko-unfold-comp-goal!)
  (let loop ()
    (if (rko-comp-mem? (dk-goal))
        (let ((g (dk-goal)))
          (mac 'complement-in-membership)
          (if (equal? (dk-goal) g)
              (error "rko-unfold-comp-goal!: mac made no progress" (expression->string g)))
          (loop)))))

;; PTS \ (PTS \ X) = X for X subset PTS.  The tree has no double-complement
;; lemma; with both memberships unfolded the identity is PROPOSITIONAL, so
;; `prop' closes each direction once dk-only! has trimmed the context under its
;; atom cap.  Requires (SUBSET sub base) in context; returns the equation.
(define (rko-dbl-comp! base sub)
  (let ((big `(COMPLEMENT-IN ,base (COMPLEMENT-IN ,base ,sub))))
    (have! `(FORALL x_ (IFF (IN x_ ,big) (IN x_ ,sub)))
      (lambda ()
        (di)
        (rko-each-leaf!
         (lambda () (di))
         (lambda ()
           (let* ((g (dk-goal)) (x (cadr g)))
             (if (equal? (caddr g) sub)
                 (begin (dk-only! (rko-unfold-comp-h! `(IN ,x ,big))) (prop))
                 (begin (fact 'subset-mem-fwd sub base x)
                        (dk-only! `(IN ,x ,sub) `(IN ,x ,base))
                        (rko-unfold-comp-goal!)
                        (prop)))))))) 
    (dk-fact! 'class-extensionality big sub)))

;; goal mentions TO where an equation (= FROM TO) is in context: rewrite TO back
;; to FROM (subst replaces its equation's LEFT side, so flip first).
(define (rko-rewrite-goal! from to)
  (fact 'eq-sym from to)
  (subst `(= ,to ,from)))

(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (AND (IS-METRIC-SPACE s)
              (AND (IS-METRIC-SPACE t)
                   (IN f (FUN (PTS s) (PTS t)))))
       (IMPLIES (FORALL A (IMPLIES (IS-CLOSED t A)
                  (IS-CLOSED s (PREIMAGE s f A))))
         (IS-CONTINUOUS s t f))))))))
(dk-split-all! (dk-peel!))
(define rko-cpc-h
  (dk-pick (lambda (a) (and (rko-head? a 'FORALL) (rko-head? (caddr a) 'IMPLIES)
                            (rko-head? (cadr (caddr a)) 'IS-CLOSED)))
           "the closed-preimage hypothesis"))

(have! '(FORALL V (IMPLIES (IS-OPEN t V) (IS-OPEN s (PREIMAGE s f V))))
  (lambda ()
    (let* ((op (car (dk-peel!)))                 ; (IS-OPEN t v)
           (v  (caddr op))
           (pv `(PREIMAGE s f ,v))
           (cv `(COMPLEMENT-IN (PTS t) ,v)))
      (have! `(SUBSET ,v (PTS t)) (lambda () (rko-open-h! op) (ass)))
      (let ((e1 (rko-dbl-comp! '(PTS t) v)))
        (have! `(IS-CLOSED t ,cv)                ; the complement of an open is closed
          (lambda ()
            (mac 'is-closed)
            (dk-conj-close!
             (lambda ()
               (let ((g (dk-goal)))
                 (cond ((rko-head? g 'IS-METRIC-SPACE) (ass))
                       ((rko-head? g 'SUBSET) (fact 'complement-in-subset v '(PTS t)) (ass))
                       (#t (subst e1) (ass)))))))))
      (let ((cl (dk-apply! rko-cpc-h cv)))       ; IS-CLOSED s (PREIMAGE s f (PTS(t)\v))
        (dk-split! (dk-landed-1 (lambda () (mac-h 'is-closed cl)))))
      (have! rko-typings)
      (let ((e2 (dk-fact! 'preimage-complement 's 't 'f v)))
        (have! `(SUBSET ,pv (PTS s))
          (lambda ()
            (let ((mem (rko-subset-elt!)))
              (dk-split! (dk-landed-1 (lambda () (mac-h 'preimage-membership mem))))
              (ass))))
        (let ((e3 (rko-dbl-comp! '(PTS s) pv)))
          (rko-rewrite-goal! (cadr e3) (caddr e3))   ; f^-1(v) -> PTS(s)\(PTS(s)\f^-1(v))
          (rko-rewrite-goal! (cadr e2) (caddr e2))   ; PTS(s)\f^-1(v) -> f^-1(PTS(t)\v)
          (ass))))))
(have! rko-typings)
(fact 'open-preimage-implies-continuous 's 't 'f)
(ass)
(qed 'closed-preimage-implies-continuous)
(topic! 'closed-preimage-implies-continuous 'topology)
