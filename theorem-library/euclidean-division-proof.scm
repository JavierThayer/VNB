;;; euclidean-division-proof.scm -- Brick B2 (LA Phase B, algebraic-numbers.pdf
;;; ch.3): division-with-remainder in usable form over any euclidean ring.  For
;;; a euclidean ring s, a in CARR, b in CARR, b/=0, there are q,r with a = q.b + r
;;; and (r = 0 or deg(r) < deg(b)), where deg = GAUGE(s) (the named degree).  This
;;; is the ring-theoretic core of the Smith/normal-form reduction (Prop 3.36): it
;;; is what shrinks a pivot below the running minimum.  Proof = gauge-is-degree
;;; (GAUGE has division-with-remainder) + unfold HAS-DIV-REMAINDER + instantiate.
(define (ed-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ed-di*) (let lp () (let* ((g (ed-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(sp (make-wff '(FORALL s (IMPLIES (IS-EUCLIDEAN-RING s) (FORALL a (IMPLIES (IN a (CARR s)) (FORALL b (IMPLIES (IN b (CARR s)) (IMPLIES (NOT (= b (ZERO s))) (FORSOME q (AND (IN q (CARR s)) (FORSOME r (AND (IN r (CARR s)) (AND (= a ((ADD s) ((MUL s) q b) r)) (OR (= r (ZERO s)) (<= (succ ((GAUGE s) r)) ((GAUGE s) b)))))))))))))))))
(ed-di*)
(fact 'gauge-is-degree 's)
(ai 1)
(mac-h 'HAS-DIV-REMAINDER '(HAS-DIV-REMAINDER s (GAUGE s)))
(inst+ '(FORALL a_ (IMPLIES (IN a_ (CARR s)) (FORALL b (IMPLIES (IN b (CARR s)) (IMPLIES (NOT (= b (ZERO s))) (FORSOME q (AND (IN q (CARR s)) (FORSOME r (AND (IN r (CARR s)) (AND (= a_ ((ADD s) ((MUL s) q b) r)) (OR (= r (ZERO s)) (<= (succ ((GAUGE s) r)) ((GAUGE s) b))))))))))))) 'a)
(inst+ '(FORALL b (IMPLIES (IN b (CARR s)) (IMPLIES (NOT (= b (ZERO s))) (FORSOME q (AND (IN q (CARR s)) (FORSOME r (AND (IN r (CARR s)) (AND (= a ((ADD s) ((MUL s) q b) r)) (OR (= r (ZERO s)) (<= (succ ((GAUGE s) r)) ((GAUGE s) b))))))))))) 'b)
(ass)
(qed 'euclidean-division)
(topic! 'euclidean-division 'algebra)
