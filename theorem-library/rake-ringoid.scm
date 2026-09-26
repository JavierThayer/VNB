;;; rake-ringoid.scm -- rq-add-computes: addition on R/I computes on classes.
;;;
;;; THE STATEMENT (structure-library/ringoid.scm:139, copied unchanged):
;;;
;;;     r a ringoid, a, b in CARR(r)
;;;       =>  (ADD RINGOID-QUOTIENT-RING(r))([a], [b])  =  [ (ADD r)(a, b) ]
;;;
;;; THE ROUTE, which is rake-algebra3.scm's closing block run.  Three pieces,
;;; and only the third has content:
;;;
;;;  (i) `rq-add' (definitional, ringoid.scm) rewrites ADD(RINGOID-QUOTIENT-RING r)
;;;      to DESCEND2(RINGOID-SETOID r, f) with f the class-of-sum map
;;;      [a,b] |-> [a+b].  That is one `subst': the term sits in OPERATOR
;;;      position and `subst' has reached operator position since 2026-09-16.
;;; (ii) f is a FUNCTION CARTESIAN(PTS s, PTS s) -> QUOTIENT(s): `lam-t', whose
;;;      SETHOOD leaf is cartesian-set-iff off ringoid-carr-in-set and whose
;;;      pointwise leaf is class-in-quotient.  `PTS(RINGOID-SETOID r)' is
;;;      `CARR(r)' by the definitional `ringoid-setoid-pts', so the statement is
;;;      written in PTS form (which is what descend2-computes asks for) and the
;;;      driver `mac's it down to CARR inside.
;;;(iii) f RESPECTS2 the congruence.  By class-eq-iff this is
;;;      (a+b) - (a'+b') in IDL(r) from (a - a') and (b - b') in IDL(r), i.e.
;;;      ringoid-ideal-add plus the regrouping (a+b) - (a'+b') = (a-a') + (b-b')
;;;      -- `r6b-rdiff-add', proven in theorem-library/rake-ringoid-additive.scm.
;;;
;;; Then `descend2-computes' (rake-setoid2.scm) IS the conclusion, and `lam-b-h'
;;; on the landed equation reduces its right side to the class of the sum.  The
;;; beta is done in the HYPOTHESIS rather than the goal on purpose: the goal
;;; route ends at `t = t' and owes `rfl' a definedness witness that the forward
;;; route never needs (elem-entry-readoffs.scm's two-routes note).
;;;
;;; THE CONGRUENCE, read out of and into RELATED.  `mac-h' cannot unfold the
;;; RELATED or RINGOID-REL functoids in an assumption, and `slot-h' has no
;;; accessor fallback, so the bridge is two small theorems: `r6b-setoid-rel'
;;; (REL(RINGOID-SETOID r) == RINGOID-REL r, proved (slot)(mac)(nth-r)(qrfl)) and
;;; the pair r6b-related-out / r6b-related-in.
;;;
;;; LOAD WINDOW [496, end).
;;;   lo = 496: the latest citation is `ringoid-setoid-is-setoid'
;;;             (theorem-library/ringoid-setoid-proof, 495).  Then
;;;             class-eq-iff / class-in-quotient / descend2-computes /
;;;             rko2-related-unfold (theorem-library/rake-setoid2, 427),
;;;             respects2-unfold (theorem-library/rake-setoid, 165),
;;;             pair-in-cartesian (164), the additive lemmas
;;;             (theorem-library/rake-ringoid-additive, wherever it is placed in
;;;             [165, 495)), and ringoid.scm's own read-offs (26).
;;;   hi = end: NOTHING loaded cites rq-add-computes.  The only citer in the tree
;;;             is theorem-library/ringoid-quotient-ring-proof.scm, which is NOT
;;;             in load.scm and has not been for as long as it has existed (it
;;;             also cites `ring-add-closed-ringoid-as-ring', a view companion
;;;             that does not exist -- the view specializer ran before
;;;             ring-add-closed was proven).
;;;
;;; Helper prefix: r6b-.

(define (r6b-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'set-quotient))
      (begin
        (display "\n*** rake-ringoid: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-ringoid: unfinished" name))))

;;; ---- the two terms the whole file is about ----------------------------
(define r6b-set '(RINGOID-SETOID r))
(define r6b-lam                                  ; rq-add's right-hand map
  '(VNB-LAMBDA (LIST a b) (CARTESIAN (CARR r) (CARR r))
     (CLASS (RINGOID-SETOID r) ((ADD r) a b))))
(define r6b-d2 (list 'DESCEND2 r6b-set r6b-lam))

;;; ---- REL(RINGOID-SETOID r) == RINGOID-REL r ---------------------------
;;; The accessor read-off of the setoid pair, as a citable EQUATION: `slot-h'
;;; refuses a hypothesis (no accessor fallback), so mac-h needs a theorem.
(sp (make-wff '(FORALL r (== (REL (RINGOID-SETOID r)) (RINGOID-REL r)))))
(di)
(slot 'REL)
(mac 'RINGOID-SETOID)
(nth-r)
(qrfl)
(r6b-qed! 'r6b-setoid-rel)

;;; ---- the congruence, out of RELATED ------------------------------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(IMPLIES (RELATED (RINGOID-SETOID r) a b)
              (IN ((ADD r) a ((NEG r) b)) (IDL r)))))))
(dk-peel!)
(mac-h 'rko2-related-unfold '(RELATED (RINGOID-SETOID r) a b))
(mac-h 'r6b-setoid-rel '(IN (LIST a b) (REL (RINGOID-SETOID r))))
(let ((u (dk-landed-1 (lambda ()
            (mac-h 'ringoid-rel-mem '(IN (LIST a b) (RINGOID-REL r)))))))
  (dk-split-all! (list u)))
(ass)
(r6b-qed! 'r6b-related-out)

;;; ---- the congruence, into RELATED --------------------------------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
    '(IMPLIES (IN ((ADD r) a ((NEG r) b)) (IDL r))
              (RELATED (RINGOID-SETOID r) a b))))))
(dk-peel!)
(fact 'pair-in-cartesian '(CARR r) '(CARR r) 'a 'b)
(mac 'RELATED)
(mac 'r6b-setoid-rel)
(mac 'ringoid-rel-mem)
(dk-conj-close! (lambda () (ass)))
(r6b-qed! 'r6b-related-in)

;;; ---- the class-of-sum map is a function into the quotient --------------
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (list 'IN r6b-lam
        (list 'FUN (list 'CARTESIAN '(PTS (RINGOID-SETOID r)) '(PTS (RINGOID-SETOID r)))
              '(QUOTIENT (RINGOID-SETOID r)))))))
(dk-peel!)
(fact 'ringoid-setoid-is-setoid 'r)
(fact 'ringoid-carr-in-set 'r)
(mac 'ringoid-setoid-pts)
(let ((ls (dk-opened (lambda () (lam-t)))))
  ;; the SETHOOD of the domain -- a CARTESIAN of two copies of CARR(r)
  (dk-focus! (or (any-pred (lambda (n) (let ((g (dk-goal-of n)))
                                         (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
                           ls)
                 (error "rake-ringoid: no sethood leaf")))
  (mac 'cartesian-set-iff)
  (dk-conj-close! (lambda () (ass)))
  ;; the POINTWISE typing -- one guarded universal per binder-list component
  (dk-focus! (or (any-pred (lambda (n) (let ((g (dk-goal-of n)))
                                         (not (and (pair? g) (eq? (car g) 'IN)
                                                   (eq? (caddr g) 'SET)))))
                           ls)
                 (error "rake-ringoid: no pointwise leaf")))
  (dk-peel!)
  (let* ((g (dk-goal))                          ; (IN (CLASS s ((ADD r) x y)) (QUOTIENT s))
         (t (caddr (cadr g))))                  ; ((ADD r) x y)
    (fact 'r6b-radd-type 'r (cadr t) (caddr t))
    (have! (list 'IN t '(PTS (RINGOID-SETOID r)))
           (lambda () (mac 'ringoid-setoid-pts) (ass)))
    (fact 'class-in-quotient r6b-set t)
    (ass)))
(r6b-qed! 'r6b-rq-add-lam-type)

;;; ---- the class-of-sum map respects the congruence -----------------------
;;; `respects2-unfold' rather than `mac RESPECTS2': its binders are a_ b_ c_ d_,
;;; so nothing is spelled like the lambda's own a and b.
(sp (make-wff (forall-guarded '(r) '((IS-RINGOID r))
  (list 'RESPECTS2 r6b-set r6b-lam))))
(dk-peel!)
(mac 'respects2-unfold)
(mac 'ringoid-setoid-pts)
(let ((landed (dk-peel!)))
  (dk-split-all! landed))
(let* ((g   (dk-goal))                          ; (= (lam x y) (lam u v))
       (l1  (cadr g)) (l2 (caddr g))
       (x   (cadr l1)) (y (caddr l1))
       (u   (cadr l2)) (v (caddr l2)))
  (fact 'r6b-related-out 'r x u)
  (fact 'r6b-related-out 'r y v)
  (fact 'ringoid-ideal-add 'r
        (list '(ADD r) x (list '(NEG r) u))
        (list '(ADD r) y (list '(NEG r) v)))
  (fact 'r6b-rdiff-add 'r x y u v)
  (fact 'r6b-radd-type 'r x y)
  (fact 'r6b-radd-type 'r u v)
  (have! (list 'IN (list '(ADD r) (list '(ADD r) x y)
                         (list '(NEG r) (list '(ADD r) u v)))
               '(IDL r))
         (lambda ()
           (subst (list '= (list '(ADD r) (list '(ADD r) x y)
                                 (list '(NEG r) (list '(ADD r) u v)))
                        (list '(ADD r) (list '(ADD r) x (list '(NEG r) u))
                              (list '(ADD r) y (list '(NEG r) v)))))
           (ass)))
  (fact 'r6b-related-in 'r (list '(ADD r) x y) (list '(ADD r) u v))
  (lam-b)                                       ; reduces BOTH redexes
  (fact 'ringoid-setoid-is-setoid 'r)
  (have! (list 'IN (list '(ADD r) x y) '(PTS (RINGOID-SETOID r)))
         (lambda () (mac 'ringoid-setoid-pts) (ass)))
  (have! (list 'IN (list '(ADD r) u v) '(PTS (RINGOID-SETOID r)))
         (lambda () (mac 'ringoid-setoid-pts) (ass)))
  (fact 'class-eq-iff r6b-set (list '(ADD r) x y) (list '(ADD r) u v))
  ;; the context is twenty-odd formulas by now and `prop' has an atom cap;
  ;; keep the iff and the RELATED fact and nothing else.
  (let ((iff (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IFF))) "the class-eq iff"))
        (rel (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'RELATED)
                                       (pair? (caddr f)) (equal? (car (caddr f)) '(ADD r))))
                      "the RELATED conclusion")))
    (dk-only! iff rel)
    (prop)))
(r6b-qed! 'r6b-add-respects2)

;;; =====================================================================
;;; rq-add-computes.  Statement copied from structure-library/ringoid.scm:139.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(r) '((IS-RINGOID r))
    (forall-guarded '(a b) '((IN a (CARR r)) (IN b (CARR r)))
      '(= ((ADD (RINGOID-QUOTIENT-RING r))
           (CLASS (RINGOID-SETOID r) a) (CLASS (RINGOID-SETOID r) b))
          (CLASS (RINGOID-SETOID r) ((ADD r) a b)))))))
(dk-peel!)
(fact 'ringoid-setoid-is-setoid 'r)
(fact 'r6b-rq-add-lam-type 'r)
(fact 'r6b-add-respects2 'r)
(have! '(IN a (PTS (RINGOID-SETOID r))) (lambda () (mac 'ringoid-setoid-pts) (ass)))
(have! '(IN b (PTS (RINGOID-SETOID r))) (lambda () (mac 'ringoid-setoid-pts) (ass)))
(fact 'rq-add 'r)
(subst (list '== '(ADD (RINGOID-QUOTIENT-RING r)) r6b-d2))
(let ((e (dk-fact! 'descend2-computes r6b-set '(QUOTIENT (RINGOID-SETOID r)) r6b-lam 'a 'b)))
  (lam-b-h e)
  (ass))
(r6b-qed! 'rq-add-computes)
