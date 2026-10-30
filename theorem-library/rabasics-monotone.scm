;;; rabasics-monotone.scm -- calculus.pdf 3.7, complex-analysis.pdf 1.7: a monotone bounded real
;;; sequence converges to its sup (resp. inf).
;;;
;;;   monotone-converges-to-sup   f non-decreasing and bounded above
;;;                                 => lim f = sup { f(k) : k in NN }
;;;   monotone-converges-to-inf   f non-increasing and bounded below
;;;                                 => lim f = inf { f(k) : k in NN },
;;;                               written -sup { -f(k) : k in NN }: the tree has SUP on RR as a
;;;                               primitive and no INF (finding); hbs-inf-point and the companion
;;;                               below state that this term is the greatest lower bound.
;;;   rr-neg-sup-neg-is-glb       for a non-empty set of values bounded below, -sup{-f(k)} is a
;;;                               lower bound of {f(k)} and >= every lower bound (the notes' inf).
;;;   rr-inf-is-glb               INF(s) (rabasics-vocab) is in RR and is the greatest lower bound
;;;                               of a non-empty s subset RR bounded below.
;;;   monotone-converges-to-inf-literal   the inf half with INF: lim f = INF{ f(k) : k in NN }.
;;; Needs the vocabulary file rabasics-vocab (INF) loaded first.
;;;
;;; The route is monotone-convergence-proof's (theorem-library/), which already took the limit to
;;; be SUP of the range and only failed to SAY so: given eps, rr-sup-approx hands back f(N) with
;;; L - eps < f(N), and monotonicity carries it to every n >= N.  The inf half runs the same
;;; argument on the set of NEGATED values.
;;;
;;; Library: analysis (CONVERGES-TO, RR-MS).  Load window: after theorem-library/zero-deriv-off-countable
;;; (nn-antitone-step-implies-le; the latest citation) and monotone-convergence-proof
;;; (nn-monotone-step-implies-le); no citer yet.  Helper prefix: rbm-.

(define (rbm-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "rbm-find: no context formula" what))
          ((pred (car l)) (car l))
          (#t (loop (cdr l))))))

;;; di-split an AND goal to its leaves and run CLOSER on each.
(define (rbm-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (rbm-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; the value term of the range SEP at index u: (f u) or (- (f u))
(define (rbm-val kind f u) (if (eq? kind 'sup) (list f u) (list '- (list f u))))

;;; (IN (val u) S), for u typed in NN with f(u) in RR in context.
(define (rbm-member! kind f S u)
  (if (eq? kind 'inf) (dk-have! (list 'IN (rbm-val kind f u) 'RR)
                                (lambda () (fact 'rr-neg-closed (list f u)) (ass))))
  (dk-have! (list 'IN (rbm-val kind f u) S)
    (lambda ()
      (for-each (lambda (leaf)
                  (dk-focus! leaf)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin (ew u)
                             (rbm-goal-and!
                              (lambda () (if (eq? (car (dk-goal)) '=) (rfl) (ass)))))))
                (dk-opened (lambda () (sep-mi)))))))

;;; The range S is inhabited, inside RR, bounded above; land sup S in RR, its upper-bound universal.
(define (rbm-setup! kind f S bnd bound)
  (let ((sL (list 'SUP S)))
    (fact 'nn-zero-in)
    (fact 'fun-apply-type-c f 'NN 'RR 0)
    (rbm-member! kind f S 0)
    (dk-have! (list 'FORSOME 'x_ (list 'IN 'x_ S))
      (lambda () (ew (rbm-val kind f 0)) (ass)))
    (dk-have! (list 'SUBSET S 'RR)
      (lambda () (mac 'subset-def) (di)
                 (sep-me (rbm-find 'member (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                                            (equal? (caddr a) S)))))
                 (ass)))
    ;; bounded above: by bnd (sup) or by -bnd (inf)
    (fact 'rr-neg-closed bnd)
    (dk-have! (list 'RR-BOUNDED-ABOVE S)
      (lambda ()
        (mac 'rr-bounded-above)
        (ew (if (eq? kind 'sup) bnd (list '- bnd)))
        (mac 'rr-upper-bound)
        (for-each (lambda (leaf)
                    (dk-focus! leaf)
                    (if (eq? (car (dk-goal)) 'IN)
                        (ass)
                        (begin
                          (di)
                          (let ((x (cadr (dk-goal))))
                            (sep-me (rbm-find 'member (lambda (a) (equal? a (list 'IN x S)))))
                            (let ((k (dk-skolem!
                                      (rbm-find 'range-witness
                                        (lambda (a) (and (pair? a) (eq? (car a) 'FORSOME)
                                                         (dk-contains? a x)))))))
                              (inst+ bound k)
                              (fact 'fun-apply-type-c f 'NN 'RR k)
                              (if (eq? kind 'sup)
                                  (begin (subst (list '= x (list f k))) (ass))
                                  (dk-ineq! (list '= x (list '- (list f k)))
                                            (list '<= bnd (list f k)))))))))
                  (dk-opened (lambda () (di))))))
    (fact 'rr-sup-in S)
    (fact 'rr-sup-upper S)
    (if (eq? kind 'inf) (fact 'rr-neg-closed sL))
    (dk-project! (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x S) (list '<= 'x sL)))
                 'rr-upper-bound (list 'RR-UPPER-BOUND S sL))))

(define (rbm-ub sL)
  (rbm-find 'sup-upper
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (let ((b (caddr a)))
                       (and (pair? b) (eq? (car b) 'IMPLIES)
                            (pair? (caddr b)) (eq? (car (caddr b)) '<=)
                            (equal? (caddr (caddr b)) sL)))))))

;;; THE PROOF, for KIND = 'sup or 'inf.  The statement is open (sp done).
(define (rbm-prove! kind)
  (let* ((landed (dk-peel!))
         (rbm-one (lambda (what pred)
                    (let ((ll (filter pred landed)))
                      (if (and (pair? ll) (null? (cdr ll))) (car ll)
                          (error "rbm-prove!: expected one landing" what)))))
         (typ  (rbm-one 'typing (lambda (a) (eq? (car a) 'IN))))      ; (IN f (FUN NN RR))
         (f    (cadr typ))
         (step (rbm-one 'step (lambda (a) (eq? (car a) 'FORALL))))   ; the monotone step
         (bex  (rbm-one 'bound (lambda (a) (eq? (car a) 'FORSOME)))) ; the bound existential
         (bnd  (dk-skolem! bex))
         (bound (rbm-find 'bounding
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                   (dk-contains? a bnd)))))
         (lim  (cadddr (dk-goal)))
         (sL    (if (eq? kind 'sup) lim (cadr lim)))
         (S    (cadr sL)))
    (rbm-setup! kind f S bnd bound)
    (let ((ub (rbm-ub sL)))
      (mac 'converges-to)
      (rbm-goal-and!
       (lambda ()
         (let ((g (dk-goal)))
           (cond ((eq? (car g) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
                 ((eq? (car g) 'IN) (slot 'PTS) (ass))
                 (#t (rbm-eps! kind f S sL lim ub step)))))))))

(define (rbm-eps! kind f S sL lim ub step)
  (let* ((posr (car (filter (lambda (a) (eq? (car a) 'POS-RR)) (dk-peel!))))
         (eps  (cadr posr)))
    (dk-pos-parts! eps)
    (let* ((approx (dk-fact! 'rr-sup-approx S eps))
           (w      (dk-skolem! approx)))
      (sep-me (rbm-find 'w-in-range (lambda (a) (equal? a (list 'IN w S)))))
      (let ((bigN (dk-skolem!
                   (rbm-find 'w-witness
                     (lambda (a) (and (pair? a) (eq? (car a) 'FORSOME)
                                      (dk-contains? a w)))))))
        (ew bigN)
        (rbm-goal-and!
         (lambda ()
           (if (eq? (car (dk-goal)) 'FORALL)
               (rbm-tail! kind f S sL lim ub step bigN w eps)
               (ass))))))))

(define (rbm-tail! kind f S sL lim ub step bigN w eps)
  (let* ((landed (dk-peel!))
         (n_  (cadr (car (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN))) landed)))))
    (fact 'fun-apply-type-c f 'NN 'RR n_)
    (fact 'fun-apply-type-c f 'NN 'RR bigN)
    (rbm-member! kind f S n_)
    (inst+ ub (rbm-val kind f n_))                          ; val(n) <= sL
    (if (eq? kind 'sup)
        (fact 'nn-monotone-step-implies-le f n_ bigN)       ; f(N) <= f(n)
        (fact 'nn-antitone-step-implies-le f n_ bigN))      ; f(n) <= f(N)
    (fact 'rr-sub-in-rr (list f n_) lim)
    (mac 'rr-ms-dist)
    (mac 'rr-abs-bound)
    (rbm-goal-and!
     (lambda ()
       (if (eq? kind 'sup)
           (if (equal? (cadr (dk-goal)) (list '- eps))
               (dk-ineq! (list '< (list '- sL eps) w)
                         (list '= w (list f bigN))
                         (list '<= (list f bigN) (list f n_)))
               (dk-ineq! (list '<= (list f n_) sL)
                         (list '<= 0 eps)))
           (if (equal? (cadr (dk-goal)) (list '- eps))
               (dk-ineq! (list '<= (list '- (list f n_)) sL)
                         (list '<= 0 eps))
               (dk-ineq! (list '< (list '- sL eps) w)
                         (list '= w (list '- (list f bigN)))
                         (list '<= (list f n_) (list f bigN)))))))))

;;; ---------------------------------------------------------------------------
(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f k) (f (succ k)))))
      (IMPLIES (FORSOME bnd (AND (IN bnd RR) (FORALL k (IMPLIES (IN k NN) (<= (f k) bnd)))))
       (CONVERGES-TO RR-MS f (SUP (SEP y_ RR (FORSOME k_ (AND (IN k_ NN) (= y_ (f k_)))))))))))))
(rbm-prove! 'sup)
(qed 'monotone-converges-to-sup)

(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f (succ k)) (f k))))
      (IMPLIES (FORSOME bnd (AND (IN bnd RR) (FORALL k (IMPLIES (IN k NN) (<= bnd (f k))))))
       (CONVERGES-TO RR-MS f
         (- (SUP (SEP y_ RR (FORSOME k_ (AND (IN k_ NN) (= y_ (- (f k_)))))))))))))))
(rbm-prove! 'inf)
(qed 'monotone-converges-to-inf)

;;; ---------------------------------------------------------------------------
;;; rr-neg-sup-neg-is-glb: -sup{-f(k)} is the greatest lower bound of {f(k)}.
(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORSOME bnd (AND (IN bnd RR) (FORALL k (IMPLIES (IN k NN) (<= bnd (f k))))))
      (AND (FORALL k (IMPLIES (IN k NN)
             (<= (- (SUP (SEP y_ RR (FORSOME k_ (AND (IN k_ NN) (= y_ (- (f k_)))))))) (f k))))
           (FORALL b (IMPLIES (IN b RR)
             (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= b (f k))))
               (<= b (- (SUP (SEP y_ RR (FORSOME k_ (AND (IN k_ NN) (= y_ (- (f k_))))))))))))))))))
(let* ((landed (dk-peel!))
       (typ  (car (filter (lambda (a) (eq? (car a) 'IN)) landed)))
       (f    (cadr typ))
       (bex  (car (filter (lambda (a) (eq? (car a) 'FORSOME)) landed)))
       (bnd  (dk-skolem! bex))
       (bound (rbm-find 'bounding (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bnd)))))
       (g1   (cadr (dk-goal)))
       (sL   (cadr (cadr (caddr (caddr g1)))))
       (S    (cadr sL)))
  (rbm-setup! 'inf f S bnd bound)
  (fact 'rr-neg-closed sL)
  (let ((ub (rbm-ub sL)))
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (let* ((pl (dk-peel!))
              (g  (dk-goal)))
         (if (equal? (caddr g) (list '- sL))
             ;; greatest: b a lower bound, so -b bounds S above, so sL <= -b
             (let* ((b  (cadr g))
                    (lb (car (filter (lambda (a) (eq? (car a) 'FORALL)) pl))))
               (fact 'rr-neg-closed b)
               (dk-have! (list 'RR-UPPER-BOUND S (list '- b))
                 (lambda ()
                   (mac 'rr-upper-bound)
                   (for-each (lambda (lf)
                               (dk-focus! lf)
                               (if (eq? (car (dk-goal)) 'IN)
                                   (ass)
                                   (begin
                                     (di)
                                     (let* ((x (cadr (dk-goal))))
                                       (sep-me (rbm-find 'member (lambda (a) (equal? a (list 'IN x S)))))
                                       (let ((k (dk-skolem!
                                                 (rbm-find 'range-witness
                                                   (lambda (a) (and (pair? a) (eq? (car a) 'FORSOME)
                                                                    (dk-contains? a x)))))))
                                         (inst+ lb k)
                                         (fact 'fun-apply-type-c f 'NN 'RR k)
                                         (dk-ineq! (list '= x (list '- (list f k)))
                                                   (list '<= b (list f k))))))))
                             (dk-opened (lambda () (di))))))
               (inst+ (dk-fact! 'rr-sup-least S) (list '- b))
               (dk-ineq! (list '<= sL (list '- b))))
             ;; lower bound: -f(k) <= sL
             (let ((k (cadr (car (filter (lambda (a) (eq? (car a) 'IN)) pl)))))
               (fact 'fun-apply-type-c f 'NN 'RR k)
               (rbm-member! 'inf f S k)
               (inst+ ub (rbm-val 'inf f k))
               (dk-ineq! (list '<= (list '- (list f k)) sL))))))
     (dk-opened (lambda () (di))))))
(qed 'rr-neg-sup-neg-is-glb)

;;; ---------------------------------------------------------------------------
;;; INF (rabasics-vocab): the infimum is the greatest lower bound, and the inf half with INF.

;;; split a nested AND goal into its leaves (returned)
(define (rbm-split-goal!)
  (let loop ((todo (list (proof-state-focus *ps*))) (acc '()))
    (if (null? todo)
        (reverse acc)
        (begin
          (dk-focus! (car todo))
          (if (eq? (car (dk-goal)) 'AND)
              (loop (append (dk-opened (lambda () (di))) (cdr todo)) acc)
              (loop (cdr todo) (cons (car todo) acc)))))))

(sp (make-wff
  '(FORALL s (IMPLIES (SUBSET s RR) (IMPLIES (FORSOME x0 (IN x0 s))
     (IMPLIES (FORSOME bnd (AND (IN bnd RR) (FORALL x (IMPLIES (IN x s) (<= bnd x)))))
       (AND (IN (INF s) RR)
       (AND (FORALL x (IMPLIES (IN x s) (<= (INF s) x)))
            (FORALL b (IMPLIES (IN b RR) (IMPLIES (FORALL x (IMPLIES (IN x s) (<= b x))) (<= b (INF s)))))))))))))
(define rbi-landed (dk-peel!))
(define rbi-sub (car (filter (lambda (f) (eq? (car f) 'SUBSET)) rbi-landed)))
(define rbi-set (cadr rbi-sub))
(define rbi-x0 (dk-skolem! (car (filter (lambda (f) (and (eq? (car f) 'FORSOME) (not (dk-contains? f 'RR)))) rbi-landed))))
(define rbi-bnd (dk-skolem! (car (filter (lambda (f) (and (eq? (car f) 'FORSOME) (dk-contains? f 'RR))) rbi-landed))))
(define rbi-lb (rbm-find 'lower-bound (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f rbi-bnd)))))
(mac 'INF)
(define rbi-S (cadr (cadr (cadr (cadr (dk-goal))))))       ; (AND (IN (- (SUP S)) RR) ...)
(define rbi-L (list 'SUP rbi-S))
;;; x in s: x in RR
(define (rbi-real! x)
  (dk-have! (list 'IN x 'RR)
    (lambda () (mac-h 'subset-def rbi-sub) (inst+ (rbm-find 'sub (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f 'RR)))) x) (ass))))
;;; x in s (typed): (- x) in S
(define (rbi-member! x)
  (rbi-real! x)
  (fact 'rr-neg-closed x)
  (dk-have! (list 'IN (list '- x) rbi-S)
    (lambda ()
      (for-each (lambda (leaf)
                  (dk-focus! leaf)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin (ew x)
                             (rbm-goal-and! (lambda () (if (eq? (car (dk-goal)) '=) (rfl) (ass)))))))
                (dk-opened (lambda () (sep-mi)))))))
;;; FA: forall x in s, b <= x.  Land RR-UPPER-BOUND(S, -b).
(define (rbi-ub-of-lb! b fa)
  (fact 'rr-neg-closed b)
  (dk-have! (list 'RR-UPPER-BOUND rbi-S (list '- b))
    (lambda ()
      (mac 'rr-upper-bound)
      (for-each (lambda (lf)
                  (dk-focus! lf)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin
                        (di)
                        (let ((v (cadr (dk-goal))))
                          (sep-me (rbm-find 'member (lambda (a) (equal? a (list 'IN v rbi-S)))))
                          (let ((x (dk-skolem! (rbm-find 'witness (lambda (a) (and (eq? (car a) 'FORSOME) (dk-contains? a v)))))))
                            (inst+ fa x)
                            (rbi-real! x)
                            (dk-ineq! (list '= v (list '- x)) (list '<= b x)))))))
                (dk-opened (lambda () (di)))))))
(rbi-member! rbi-x0)
(dk-have! (list 'FORSOME 'x_ (list 'IN 'x_ rbi-S)) (lambda () (ew (list '- rbi-x0)) (ass)))
(dk-have! (list 'SUBSET rbi-S 'RR)
  (lambda () (mac 'subset-def) (di)
             (sep-me (rbm-find 'member (lambda (a) (and (eq? (car a) 'IN) (equal? (caddr a) rbi-S)))))
             (ass)))
(rbi-ub-of-lb! rbi-bnd rbi-lb)
(dk-have! (list 'RR-BOUNDED-ABOVE rbi-S) (lambda () (mac 'rr-bounded-above) (ew (list '- rbi-bnd)) (ass)))
(fact 'rr-sup-in rbi-S)
(fact 'rr-sup-upper rbi-S)
(fact 'rr-neg-closed rbi-L)
(dk-project! (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x rbi-S) (list '<= 'x rbi-L)))
             'rr-upper-bound (list 'RR-UPPER-BOUND rbi-S rbi-L))
(define rbi-ub (rbm-ub rbi-L))
(define rbi-least (dk-fact! 'rr-sup-least rbi-S))
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (let ((g (dk-goal)))
     (if (eq? (car g) 'IN)
         (ass)
         (let* ((pl (dk-peel!)) (g2 (dk-goal)))
           (if (equal? (caddr g2) (list '- rbi-L))
               ;; greatest
               (let* ((b  (cadr g2))
                      (fa (car (filter (lambda (f) (eq? (car f) 'FORALL)) pl))))
                 (rbi-ub-of-lb! b fa)
                 (inst+ rbi-least (list '- b))
                 (dk-ineq! (list '<= rbi-L (list '- b))))
               ;; lower bound
               (let ((x (caddr g2)))
                 (rbi-member! x)
                 (inst+ rbi-ub (list '- x))
                 (dk-ineq! (list '<= (list '- x) rbi-L))))))))
 (rbm-split-goal!))
(qed 'rr-inf-is-glb)

;;; the inf half with INF: lim f = INF{ f(k) : k in NN }
(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f (succ k)) (f k))))
      (IMPLIES (FORSOME bnd (AND (IN bnd RR) (FORALL k (IMPLIES (IN k NN) (<= bnd (f k))))))
       (CONVERGES-TO RR-MS f (INF (SEP y_ RR (FORSOME k_ (AND (IN k_ NN) (= y_ (f k_)))))))))))))
(define rbj-landed (dk-peel!))
(define rbj-f (cadr (car (filter (lambda (f) (eq? (car f) 'IN)) rbj-landed))))
(define rbj-R (cadr (cadddr (dk-goal))))                     ; the range SEP
(mac 'INF)
(define rbj-S2 (cadr (cadr (cadddr (dk-goal)))))            ; INF's SEP over the range
(define rbj-SN (list 'SEP 'y_ 'RR (list 'FORSOME 'k_ (list 'AND '(IN k_ NN) (list '= 'y_ (list '- (list rbj-f 'k_)))))))
(fact 'rr-is-set)
(define (rbj-sep-set! t)
  (dk-have! (list 'IN t 'SET)
    (lambda ()
      (dk-have! (list 'SUBSET t 'RR)
        (lambda () (mac 'subset-def) (di)
                   (sep-me (rbm-find 'member (lambda (a) (and (eq? (car a) 'IN) (equal? (caddr a) t)))))
                   (ass)))
      (fact 'subclass-of-set-is-set t 'RR)
      (ass))))
(rbj-sep-set! rbj-S2)
(rbj-sep-set! rbj-SN)
(dk-have! (list 'AND (list 'IN rbj-S2 'SET) (list 'IN rbj-SN 'SET)))
(define rbj-ext (dk-fact! 'extensionality rbj-S2 rbj-SN))
(define rbj-claim (caddr rbj-ext))
(dk-have! rbj-claim
  (lambda ()
    (di)
    (let ((v (cadr (cadr (dk-goal)))))
      (dk-iff! (lambda (g) (equal? g (list 'IN v rbj-SN)))
        (lambda ()                                            ; v in S2 => v in SN
          (sep-me (list 'IN v rbj-S2))
          (let* ((x (dk-skolem! (rbm-find 'wx (lambda (a) (and (eq? (car a) 'FORSOME) (dk-contains? a v))))))
                 (ignore (sep-me (list 'IN x rbj-R)))
                 (k (dk-skolem! (rbm-find 'wk (lambda (a) (and (eq? (car a) 'FORSOME) (dk-contains? a x)))))))
            (fact 'fun-apply-type-c rbj-f 'NN 'RR k)
            (fact 'rr-neg-closed (list rbj-f k))
            (for-each (lambda (leaf)
                        (dk-focus! leaf)
                        (if (eq? (car (dk-goal)) 'IN)
                            (ass)
                            (begin (ew k)
                                   (rbm-goal-and!
                                    (lambda ()
                                      (if (eq? (car (dk-goal)) '=)
                                          (begin (subst (list '= v (list '- x)))
                                                 (subst (list '= x (list rbj-f k)))
                                                 (rfl))
                                          (ass)))))))
                      (dk-opened (lambda () (sep-mi))))))
        (lambda ()                                            ; v in SN => v in S2
          (sep-me (list 'IN v rbj-SN))
          (let* ((k  (dk-skolem! (rbm-find 'wk (lambda (a) (and (eq? (car a) 'FORSOME) (dk-contains? a v))))))
                 (fk (list rbj-f k)))
            (fact 'fun-apply-type-c rbj-f 'NN 'RR k)
            (rbm-member! 'sup rbj-f rbj-R k)
            (for-each (lambda (leaf)
                        (dk-focus! leaf)
                        (if (eq? (car (dk-goal)) 'IN)
                            (ass)
                            (begin (ew fk)
                                   (rbm-goal-and! (lambda () (ass))))))
                      (dk-opened (lambda () (sep-mi))))))))))
(define rbj-eq (list '= rbj-S2 rbj-SN))
(dk-have! rbj-eq (lambda () (if (dk-only! rbj-ext rbj-claim) (prop))))
(subst rbj-eq)
(fact 'monotone-converges-to-inf rbj-f)
(ass)
(qed 'monotone-converges-to-inf-literal)

(display ";; RBM qed failures: ") (display *vnb-qed-failures*) (newline)
;; (probe trailer removed at integration 2026-10-27) (page-audit!)
;; (probe trailer removed at integration 2026-10-27) (report-page-audit)
