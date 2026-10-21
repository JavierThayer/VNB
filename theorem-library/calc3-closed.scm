;;; calc3-closed.scm -- calculus.pdf Prop 3.10: A SET IS CLOSED IFF IT CONTAINS ALL
;;; ITS ACCUMULATION POINTS.  Agent CALC-3, 2026-10-19.
;;;
;;; THE NOTES.  "A necessary and sufficient condition that A subset X be closed is
;;; that it contain all its accumulation points", x being an accumulation point of A
;;; when every ball B(x, r) contains an element of A distinct from x
;;; (IS-ACCUMULATION-POINT, structure-library/calc3-vocab.scm).
;;;
;;;   closed-iff-contains-accumulation-points
;;;     forall s. is-metric-space(s) => forall A. A subset pts(s) =>
;;;       (is-closed(s, A) <=> forall x. is-accumulation-point(s, A, x) => x in A)
;;;
;;; THE PROOF.  Necessity is the notes' argument: if x is an accumulation point not
;;; in A, x lies in the open complement, so a ball B(x, r) misses A, and the
;;; accumulation point property puts a point of A in that ball.  Sufficiency goes
;;; through the closure (closure-subset-closed: closure(A) subset A makes A closed):
;;; a point z of the closure that is not in A is an accumulation point, since every
;;; ball around z is an open set containing z and so meets A (closure-membership), in
;;; a point that differs from z because z is not in A.  The notes argue by
;;; contraposition on "X \ A is not open"; the closure route is the same argument
;;; with the negations already pushed through by closure-membership.
;;;
;;; WINDOW.  Cited: complement-in-membership (set kernel), closure-membership /
;;; closure-in-carrier / closure-subset-closed (theorem-library/metric-closure-laws; the
;;; last moved there from hilbert-projection on 2026-10-20), ball-is-open / ball-center-in
;;; (rake-balls), subset-mem-fwd, metric-dist-real.  lo = metric-closure-laws; hi = none.  structure-library/calc3-vocab must load first.
;;; Library: analysis.
;;;
;;; Helper prefix: c3c-.

(define (c3c-head g) (and (pair? g) (car g)))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (SUBSET A (PTS s))
       (IFF (IS-CLOSED s A)
            (FORALL x (IMPLIES (IS-ACCUMULATION-POINT s A x) (IN x A))))))))))
(dk-peel!)
(dk-iff!
 (lambda (g) (eq? (c3c-head g) 'FORALL))
 ;; ---- necessity: IS-CLOSED s A in context
 (lambda ()
   (let* ((landed (dk-peel!))
          (hacc (car (filter (lambda (f) (eq? (c3c-head f) 'IS-ACCUMULATION-POINT)) landed)))
          (x (cadddr hacc)))
     (mac-h 'IS-ACCUMULATION-POINT hacc)
     (dk-split-all!)
     (use-em (list 'IN x 'A)
       (lambda () (ass))
       (lambda ()
         (let ((comp '(COMPLEMENT-IN (PTS s) A)))
           (dk-have! (list 'IN x comp)
             (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass)))))
           (mac-h 'IS-CLOSED '(IS-CLOSED s A))
           (dk-split-all!)
           (mac-h 'IS-OPEN (list 'IS-OPEN 's comp))
           (dk-split-all!)
           (let* ((uo (dk-pick (lambda (h) (and (eq? (c3c-head h) 'FORALL)
                                                (dk-contains? h 'COMPLEMENT-IN)
                                                (dk-contains? h 'FORSOME)))
                               "the openness universal of the complement"))
                  (r (dk-skolem! (dk-apply! uo x)))   ; POS-RR r, BALL(s,x,r) subset comp
                  (ua (dk-pick (lambda (h) (and (eq? (c3c-head h) 'FORALL)
                                                (dk-contains? h 'POS-RR)
                                                (dk-contains? h 'NOT)))
                               "the accumulation universal"))
                  (y (dk-skolem! (dk-apply! ua r))))  ; y in A, y in BALL(s,x,r), y /= x
             (fact 'subset-mem-fwd (list 'BALL 's x r) comp y)
             (mac-h 'complement-in-membership (list 'IN y comp))
             (dk-split-all!)
             (ai (list 'NOT (list 'IN y 'A)))))))))
 ;; ---- sufficiency: the accumulation-point universal in context
 (lambda ()
   (let ((hall (dk-pick (lambda (h) (and (eq? (c3c-head h) 'FORALL)
                                         (dk-contains? h 'IS-ACCUMULATION-POINT)))
                        "every accumulation point is in A")))
     (dk-have! '(SUBSET (CLOSURE s A) A)
       (lambda ()
         (mac 'subset-def)
         (let ((z (dk-di-var!)))                     ; z in CLOSURE(s, A)
           (fact 'closure-in-carrier 's 'A)
           (fact 'subset-mem-fwd '(CLOSURE s A) '(PTS s) z)
           (use-em (list 'IN z 'A)
             (lambda () (ass))
             (lambda ()
               (dk-have! (list 'IS-ACCUMULATION-POINT 's 'A z)
                 (lambda ()
                   (mac 'IS-ACCUMULATION-POINT)
                   (dk-conj-close!
                    (lambda ()
                      (if (eq? (c3c-head (dk-goal)) 'FORALL)
                          (let* ((pr (dk-peel!))
                                 (r (cadr (car pr))))     ; POS-RR r
                            (dk-pos-parts! r)
                            (fact 'ball-is-open 's z r)
                            (fact 'ball-center-in 's z r)
                            (mac-h 'closure-membership (list 'IN z '(CLOSURE s A)))
                            (dk-split-all!)
                            (let* ((uc (dk-pick (lambda (h) (and (eq? (c3c-head h) 'FORALL)
                                                                 (dk-contains? h 'IS-OPEN) (dk-contains? h 'FORSOME)))
                                                "the closure universal"))
                                   (bl (list 'BALL 's z r))
                                   (hb (dk-have! (list 'AND (list 'IS-OPEN 's bl) (list 'IN z bl))
                                         (lambda () (dk-conj-close! (lambda () (ass))))))
                                   (ex (dk-apply! uc bl))
                                   (y (dk-skolem! ex)))   ; y in BALL(s,z,r), y in A
                              (ew y)
                              (dk-conj-close!
                               (lambda ()
                                 (if (eq? (c3c-head (dk-goal)) 'NOT)
                                     (begin
                                       (di)               ; y = z
                                       (dk-have! (list 'IN z 'A)
                                         (lambda () (subst (list '= z y)) (ass)))
                                       (ai (list 'NOT (list 'IN z 'A))))
                                     (ass))))))
                          (ass))))))
               (dk-apply! hall z)
               (ai (list 'NOT (list 'IN z 'A))))))))
     (fact 'closure-subset-closed 's 'A)            ; detaches to IS-CLOSED(s, A)
     (ass))))
(qed 'closed-iff-contains-accumulation-points)
(topic! 'closed-iff-contains-accumulation-points 'analysis)
(alias! 'closed-iff-contains-accumulation-points
        "a set is closed iff it contains all its accumulation points")
