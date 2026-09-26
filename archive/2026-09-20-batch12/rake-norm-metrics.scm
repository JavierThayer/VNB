;;; rake-norm-metrics.scm -- rake batch 5 R: continuity projections and the
;;; norm metrics, PROVEN.
;;;
;;; Seven theorems.  Six of them were ASSERTED supports; the seventh is the
;;; general fact the last three are instances of, and it is what makes them
;;; short:
;;;
;;;   ag-norm-metric-is-metric-space   NEW.  For an abelian group g and any
;;;                                    group norm nm on it, the tuple
;;;                                    [carr(g), (u,v) |-> nm(u . v^-1)]
;;;                                    is a METRIC-SPACE.
;;;   continuous-is-continuous-at      structure-library/metric-continuity.scm:81
;;;   uniformly-continuous-is-continuous              metric-continuity.scm:92
;;;   nag-metric-carrier               structure-library/normed-ag-metric.scm:85
;;;   nag-metric-distance                             normed-ag-metric.scm:52
;;;   nag-metric-space-is-metric-space                normed-ag-metric.scm:69
;;;   nvs-metric-is-ms                 theorem-library/vector-taylor-proof.scm:620
;;;
;;; WHY THE GENERAL LEMMA IS STATED OVER AN ABELIAN GROUP and not over a list
;;; of curried laws.  The four metric clauses for d(u,v) = ||u . v^-1|| are not
;;; the group axioms read off: point separation needs cancellation, symmetry
;;; needs (u.v^-1)^-1 = v.u^-1, and the triangle inequality needs
;;; u.w^-1 = (u.v^-1).(v.w^-1).  Each of those is several lines of assoc /
;;; comm / inverse juggling from the raw axioms and one CITATION from the
;;; abelian-group layer -- `abelian-group-opr-interchange',
;;; `abelian-group-inverse-unique', `group-left-inv', `abelian-group-right-id'.
;;; Stating the lemma over `g' buys all of them.  The price is that each
;;; instance must produce an abelian group with the right slots, which the
;;; def-functor views already do.
;;;
;;; HOW THE THREE INSTANCES REACH IT.
;;;   NORMED-AG   NORMED-AG-AS-ABELIAN-GROUP(nag) is the group (views.scm:100),
;;;               its typing axiom gives IS-ABELIAN-GROUP, and four slot
;;;               read-offs -- proved here, both orientations -- move
;;;               `is-group-norm' onto the view's accessors and the goal's
;;;               NAG-METRIC-SPACE tuple onto them too.
;;;   NVS         NORMED-VECTOR-SPACE-AS-NORMED-AG(m) is a NORMED-AG, so
;;;               nag-metric-space-is-metric-space applies to it; the ONE
;;;               remaining step is that NVS-METRIC-SPACE(m) and
;;;               NAG-METRIC-SPACE(that view) are the same tuple, which is one
;;;               `==' proved by unfolding both functoids.
;;;
;;; TWO MECHANICS WORTH KEEPING.
;;; * `qrfl' IS alpha-aware.  NVS-METRIC-SPACE's distance lambda binds [x, y]
;;;   and NAG-METRIC-SPACE's binds [u, v]; after both functoids are unfolded the
;;;   two tuples differ only in those binder names and `qrfl' closes the `=='.
;;; * A view read-off whose TARGET accessor is the SAME SYMBOL as its SOURCE
;;;   accessor (CARR read off CARR) does not settle under one `slot' + `nth-r':
;;;   the LIST element `slot' exposes is itself an accessor application.  Here
;;;   the pair is iterated to a fixpoint (`r5r-slot-close!'); ag-view-read-offs.scm
;;;   meets the same trap in `ras-carr' and puts the right-hand side back by hand.
;;;
;;; LOAD WINDOW [446, end), i.e. immediately after theorem-library/vector-taylor-proof
;;; (position 445).  lo is forced NOT by a theorem but by a CONSTRUCTOR: the
;;; def-functoid NVS-METRIC-SPACE is declared in vector-taylor-proof.scm:28, and
;;; section (7) unfolds it.  The next constraint down is
;;; `abelian-group-opr-interchange' (theorem-library/rake-finsum-laws, 226); then
;;; rake-algebra2 (209, abelian-group-assoc / -right-id / -inverse-unique),
;;; cancellation (191, group-inv-in), finsum-type-proof (182,
;;; group-carrier-closed-opr), subtype-laws (180, abelian-group-opr-comm /
;;; group-identity-in / group-assoc / group-left-id / group-left-inv /
;;; abelian-group-is-group), pair-tuple-sethood (149, pair-in-cartesian),
;;; fun-apply-type-proof (147, fun-apply-type-c), equality-basics (133, eq-sym /
;;; eq-trans), theorem-library/axioms (9, apply-tupling-2), the base theory
;;; (cartesian-set-iff), and the definitional unfolds and view typing axioms of
;;; structure-library (views 53, normed-ag-metric 55, normed-vector-space 56).
;;; No proven theorem cites any of the six supports, so nothing forces hi.
;;;
;;; Dependencies: interactive, proof-debt, driver-kit, prop.

;;; ---- file-local driver (the `r5r-' prefix) ---------------------------

(define r5r-g #f)                       ; the abelian group of the generic lemma
(define r5r-nm #f)                      ; its norm variable
(define (r5r-carr) (list 'CARR r5r-g))
(define (r5r-iden) (list 'IDEN r5r-g))
(define (r5r-opr a b) (list (list 'OPR r5r-g) a b))
(define (r5r-inv a) (list (list 'INV r5r-g) a))
(define (r5r-nrm a) (list r5r-nm a))

(define (r5r-open)
  (filter (lambda (s) (and (not (sequent-node-grounded? s))
                           (null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))

(define (r5r-acc? t head)
  (and (pair? t) (pair? (car t)) (eq? (car (car t)) head)))

(define (r5r-find lst pred what)
  (or (find-first pred lst) (error "r5r-find: missing" what)))

;;; (IN t (CARR g)) into the context, built from the group closure laws.
;;; A no-op when it is already there; ERRORS when the citation does not land --
;;; a silent miss would leave a definedness leaf open until the qed.
(define (r5r-in! t)
  (let ((claim (list 'IN t (r5r-carr))))
    (if (member claim (dk-asms))
        claim
        (begin
          (cond ((r5r-acc? t 'INV)
                 (r5r-in! (cadr t)) (fact 'group-inv-in r5r-g (cadr t)))
                ((r5r-acc? t 'OPR)
                 (r5r-in! (cadr t)) (r5r-in! (caddr t))
                 (fact 'group-carrier-closed-opr r5r-g (cadr t) (caddr t)))
                ((equal? t (r5r-iden)) (fact 'group-identity-in r5r-g))
                (#t (error "r5r-in!: cannot type" (expression->string t))))
          (if (not (member claim (dk-asms)))
              (error "r5r-in!: typing did not land" (expression->string t)))
          claim))))

;;; the universal of the `is-group-norm' unfold -- named by its CONSEQUENT
;;; (a conjunction whose first conjunct is 0 <= nm(u)), never by its head.
(define (r5r-nu)
  (dk-pick (lambda (f)
             (and (pair? f) (eq? (car f) 'FORALL)
                  (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                  (pair? (caddr (caddr f))) (eq? (car (caddr (caddr f))) 'AND)
                  (let ((c1 (cadr (caddr (caddr f)))))
                    (and (pair? c1) (eq? (car c1) '<=) (equal? (cadr c1) 0)))))
           "the group-norm universal"))

;;; the four norm facts at t: 0 <= nm(t), the definiteness IFF, the
;;; inverse-invariance equation, and the subadditivity universal.
(define (r5r-norm-at! t)
  (r5r-in! t)
  (dk-split! (dk-apply! (r5r-nu) t)))

;;; beta-reduce the GOAL to a fixpoint, guarded on progress (`lam-b' only warns
;;; when there is no redex, so a "while there is an application" loop spins).
(define (r5r-beta!)
  (let loop ((n 0))
    (let ((before (dk-goal)))
      (if (< n 12)
          (begin (quietly (lambda () (lam-b)))
                 (if (not (equal? before (dk-goal))) (loop (+ n 1))))))))

;;; ---- the five metric clauses ----------------------------------------

;;; d(u,u) = 0 :  u . u^-1 = e  and  ||e|| = 0.
(define (r5r-self-zero!)
  (let* ((t  (cadr (cadr (dk-goal))))
         (u  (cadr t))
         (iu (caddr t)))
    (r5r-in! iu)
    (fact 'group-left-inv r5r-g u)
    (fact 'abelian-group-opr-comm r5r-g u iu)
    (fact 'eq-trans t (r5r-opr iu u) (r5r-iden))
    (subst (list '= t (r5r-iden)))
    (let* ((atoms (r5r-norm-at! (r5r-iden)))
           (iff   (r5r-find atoms (dk-head? 'IFF) "definiteness iff at the identity"))
           (refl  (list '= (r5r-iden) (r5r-iden))))
      (dk-have! refl (lambda () (rfl)))
      ;; `prop' has an atom cap and this context is deep; keep the two atoms.
      (dk-only! iff refl)
      (prop))))

;;; 0 <= d(u,v) -- the norm's own nonnegativity at u . v^-1.
(define (r5r-nonneg!)
  (let ((t (cadr (caddr (dk-goal)))))
    (r5r-norm-at! t)
    (ass)))

;;; d(u,v) = 0 => u = v.  Definiteness gives u . v^-1 = e; then
;;;   u = u.e = u.(v^-1.v) = (u.v^-1).v = e.v = v.
(define (r5r-separate!)
  ;; The vanishing distance is a HYPOTHESIS, so the redex is on that side and a
  ;; goal-side `lam-b' cannot reach it.
  (let ((red (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (caddr f) 0)
                                       (pair? (cadr f)) (pair? (car (cadr f)))
                                       (eq? (car (car (cadr f))) 'VNB-LAMBDA)))
                      "the unreduced vanishing distance")))
    (lam-b-h red))
  (let* ((h  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (caddr f) 0)
                                       (pair? (cadr f)) (eq? (car (cadr f)) r5r-nm)))
                      "the vanishing distance"))
         (tt (cadr (cadr h)))
         (u  (cadr tt)) (iv (caddr tt)) (v (cadr iv))
         (e  (r5r-iden)))
    (let* ((atoms (r5r-norm-at! tt))
           (iff   (r5r-find atoms (dk-head? 'IFF) "definiteness iff"))
           (ht    (list '= tt e)))
      (dk-have! ht (lambda () (dk-only! iff h) (prop)))
      (r5r-in! iv)
      (r5r-in! (r5r-opr e v))           ; typed BEFORE the rfl that needs it
      (r5r-in! (r5r-opr u e))
      (fact 'abelian-group-assoc r5r-g u iv v)
      (dk-have! (list '= (r5r-opr tt v) (r5r-opr e v))
                (lambda () (subst ht) (rfl)))
      (fact 'group-left-inv r5r-g v)
      (dk-have! (list '= (r5r-opr u (r5r-opr iv v)) (r5r-opr u e))
                (lambda () (subst (list '= (r5r-opr iv v) e)) (rfl)))
      (fact 'abelian-group-right-id r5r-g u)
      (fact 'group-left-id r5r-g v)
      (fact 'eq-sym (r5r-opr u e) u)
      (fact 'eq-sym (r5r-opr u (r5r-opr iv v)) (r5r-opr u e))
      (fact 'eq-trans u (r5r-opr u e) (r5r-opr u (r5r-opr iv v)))
      (fact 'eq-sym (r5r-opr tt v) (r5r-opr u (r5r-opr iv v)))
      (fact 'eq-trans u (r5r-opr u (r5r-opr iv v)) (r5r-opr tt v))
      (fact 'eq-trans u (r5r-opr tt v) (r5r-opr e v))
      (fact 'eq-trans u (r5r-opr e v) v)
      (ass))))

;;; d(u,v) = d(v,u).  (u.v^-1).(v.u^-1) = (u.u^-1).(v^-1.v) = e by INTERCHANGE
;;; after one commutation, so v.u^-1 is THE inverse of u.v^-1
;;; (abelian-group-inverse-unique) and the norm is inverse-invariant.
(define (r5r-symm!)
  (let* ((gl (dk-goal))
         (a  (cadr (cadr gl)))
         (b  (cadr (caddr gl)))
         (u  (cadr a)) (iv (caddr a)) (v (cadr iv)) (iu (r5r-inv u))
         (e  (r5r-iden)))
    (r5r-in! a) (r5r-in! b)
    (r5r-in! (r5r-opr a (r5r-opr iu v)))
    (fact 'abelian-group-opr-comm r5r-g v iu)
    (dk-have! (list '= (r5r-opr a b) (r5r-opr a (r5r-opr iu v)))
              (lambda () (subst (list '= b (r5r-opr iu v))) (rfl)))
    (fact 'abelian-group-opr-interchange r5r-g u iv iu v)
    (fact 'group-left-inv r5r-g u)
    (fact 'abelian-group-opr-comm r5r-g u iu)
    (fact 'eq-trans (r5r-opr u iu) (r5r-opr iu u) e)
    (fact 'group-left-inv r5r-g v)
    (r5r-in! e)
    (fact 'group-left-id r5r-g e)
    (dk-have! (list '= (r5r-opr (r5r-opr u iu) (r5r-opr iv v)) e)
              (lambda ()
                (subst (list '= (r5r-opr u iu) e))
                (subst (list '= (r5r-opr iv v) e))
                (ass)))
    (fact 'eq-trans (r5r-opr a b) (r5r-opr a (r5r-opr iu v))
          (r5r-opr (r5r-opr u iu) (r5r-opr iv v)))
    (fact 'eq-trans (r5r-opr a b) (r5r-opr (r5r-opr u iu) (r5r-opr iv v)) e)
    (fact 'abelian-group-inverse-unique r5r-g a b)
    (r5r-norm-at! a)
    (subst (list '= b (r5r-inv a)))
    (fact 'eq-sym (r5r-nrm (r5r-inv a)) (r5r-nrm a))
    (ass)))

;;; d(u,w) <= d(u,v) + d(v,w).  (u.v^-1).(v.w^-1) = (u.w^-1).(v^-1.v) = u.w^-1,
;;; again by INTERCHANGE after one commutation, and then subadditivity.
(define (r5r-triangle!)
  (let* ((gl (dk-goal))
         (r  (cadr (cadr gl)))
         (p  (cadr (cadr (caddr gl))))
         (q  (cadr (caddr (caddr gl))))
         (u  (cadr p)) (iv (caddr p)) (v (cadr iv))
         (iw (caddr q))
         (e  (r5r-iden)))
    (r5r-in! p) (r5r-in! q) (r5r-in! r)
    (r5r-in! (r5r-opr p (r5r-opr iw v)))
    (fact 'abelian-group-opr-comm r5r-g v iw)
    (dk-have! (list '= (r5r-opr p q) (r5r-opr p (r5r-opr iw v)))
              (lambda () (subst (list '= q (r5r-opr iw v))) (rfl)))
    (fact 'abelian-group-opr-interchange r5r-g u iv iw v)
    (fact 'group-left-inv r5r-g v)
    (fact 'abelian-group-right-id r5r-g r)
    (dk-have! (list '= (r5r-opr r (r5r-opr iv v)) r)
              (lambda () (subst (list '= (r5r-opr iv v) e)) (ass)))
    (fact 'eq-trans (r5r-opr p q) (r5r-opr p (r5r-opr iw v)) (r5r-opr r (r5r-opr iv v)))
    (fact 'eq-trans (r5r-opr p q) (r5r-opr r (r5r-opr iv v)) r)
    (fact 'eq-sym (r5r-opr p q) r)
    (let* ((atoms (r5r-norm-at! p))
           (sub   (r5r-find atoms (dk-head? 'FORALL) "subadditivity universal")))
      (dk-apply! sub q)
      (subst (list '= r (r5r-opr p q)))
      (ass))))

;;; ---- the leaf dispatcher and the loop --------------------------------

(define (r5r-dispatch!)
  (let* ((gl (dk-goal)) (h (car gl)))
    (cond
     ((and (eq? h '=) (pair? (cadr gl)) (eq? (car (cadr gl)) 'LENGTH))
      (len-r) (arith))
     ((and (eq? h 'IN) (equal? (caddr gl) 'SET) (equal? (cadr gl) (r5r-carr)))
      (ass))
     ((and (eq? h 'IN) (equal? (caddr gl) 'SET)
           (pair? (cadr gl)) (eq? (car (cadr gl)) 'CARTESIAN))
      (mac 'cartesian-set-iff))
     ((and (eq? h 'IN) (pair? (cadr gl)) (eq? (car (cadr gl)) 'VNB-LAMBDA))
      (lam-t))
     ((and (eq? h 'IN) (equal? (caddr gl) 'RR))
      (let ((t (cadr (cadr gl))))
        (r5r-in! t)
        (fact 'fun-apply-type-c r5r-nm (r5r-carr) 'RR t)
        (ass)))
     ((eq? h 'is-metric) (mac 'is-metric))
     ((and (eq? h '=) (equal? (caddr gl) 0)) (r5r-self-zero!))
     ((and (eq? h '<=) (equal? (cadr gl) 0)) (r5r-nonneg!))
     ((eq? h '<=) (r5r-triangle!))
     ((and (eq? h '=) (pair? (cadr gl)) (eq? (car (cadr gl)) r5r-nm)) (r5r-symm!))
     ((eq? h '=) (r5r-separate!))
     (#t (error "r5r-dispatch!: unexpected leaf" (expression->string gl))))))

;;; Peel / split every open leaf, then dispatch it.  Guarded on PROGRESS: a
;;; leaf that neither moves nor closes would otherwise be re-focused for ever.
(define (r5r-drive!)
  (let loop ((fuel 400) (prev #f))
    (let ((s (find-first (lambda (s) #t) (r5r-open))))
      (cond ((not s) #t)
            ((<= fuel 0) (error "r5r-drive!: out of fuel"))
            (#t
             (dk-focus! s)
             (let ((mark (cons s (dk-goal))))
               (if (equal? mark prev)
                   (error "r5r-drive!: no progress on" (expression->string (dk-goal))))
               (if (memq (car (dk-goal)) '(FORALL IMPLIES AND))
                   (di)
                   (begin (r5r-beta!) (r5r-dispatch!)))
               (loop (- fuel 1) mark)))))))

;;; A def-functor view's slot read-off, in whichever orientation is asked for.
(define (r5r-slot-close! view acc)
  (mac view)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (< n 8) (not (equal? (cadr g) (caddr g))))
          (begin (quietly (lambda () (slot acc)))
                 (quietly (lambda () (nth-r)))
                 (if (not (equal? (dk-goal) g)) (loop (+ n 1)))))))
  (qrfl))

(define (r5r-readoff! acc src view)
  (let* ((lhs (list acc (list view src)))
         (rhs (list acc src)))
    (dk-have! (list '== lhs rhs) (lambda () (r5r-slot-close! view acc)))
    (dk-have! (list '== rhs lhs) (lambda () (r5r-slot-close! view acc)))))

;;; =====================================================================
;;; (1) the general fact: a group norm induces a metric
;;; =====================================================================

(sp (make-wff '(FORALL g (FORALL nm
     (IMPLIES (IS-ABELIAN-GROUP g)
     (IMPLIES (is-group-norm nm (OPR g) (INV g) (IDEN g) (CARR g))
       (IS-METRIC-SPACE
         (LIST (CARR g)
               (VNB-LAMBDA (LIST u v) (CARTESIAN (CARR g) (CARR g))
                           (nm ((OPR g) u ((INV g) v))))))))))))
(dk-peel-to! 'IS-METRIC-SPACE)
(let* ((gl  (dk-goal))
       (l   (cadr gl))
       (lam (caddr l)))
  (set! r5r-g  (cadr (cadr l)))
  (set! r5r-nm (car (list-ref lam 3))))
(fact 'abelian-group-is-group r5r-g)
;; the carrier's sethood is a conjunct of the IS-X unfold, and `mac-h' is
;; destructive -- so read it off on a side branch.
(dk-have! (list 'IN (r5r-carr) 'SET)
          (lambda () (mac-h 'is-abelian-group (list 'IS-ABELIAN-GROUP r5r-g))
                     (dk-split-all!) (ass)))
(dk-split-all!
 (dk-landed* (lambda () (mac-h 'is-group-norm
                               (list 'is-group-norm r5r-nm (list 'OPR r5r-g)
                                     (list 'INV r5r-g) (list 'IDEN r5r-g)
                                     (list 'CARR r5r-g))))))
(mac 'IS-METRIC-SPACE)
(slot 'PTS)
(slot 'DIST)
(let loop ((n 0))
  (let ((before (dk-goal)))
    (quietly (lambda () (nth-r)))
    (if (and (< n 10) (not (equal? before (dk-goal)))) (loop (+ n 1)))))
(r5r-drive!)
(qed 'ag-norm-metric-is-metric-space)
(topic! 'ag-norm-metric-is-metric-space 'analysis)
(alias! 'ag-norm-metric-is-metric-space
        "a group norm induces a metric on the group")

;;; =====================================================================
;;; (2) continuous-is-continuous-at -- the last conjunct of IS-CONTINUOUS
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-CONTINUOUS s t f)
       (FORALL a (IMPLIES (IN a (PTS s))
         (IS-CONTINUOUS-AT s t f a)))))))))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(let ((pt (list-ref (dk-goal) 4))
      (h  (dk-pick (dk-head? 'IS-CONTINUOUS) "IS-CONTINUOUS")))
  (dk-split-all! (dk-landed* (lambda () (mac-h 'IS-CONTINUOUS h))))
  (let ((univ (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (pair? (caddr f))
                                        (eq? (car (caddr f)) 'IMPLIES)
                                        (pair? (caddr (caddr f)))
                                        (eq? (car (caddr (caddr f)))
                                             'IS-CONTINUOUS-AT)))
                       "the continuity-at universal")))
    (dk-apply! univ pt)
    (ass)))
(qed 'continuous-is-continuous-at)
(topic! 'continuous-is-continuous-at 'topology)

;;; =====================================================================
;;; (3) uniformly-continuous-is-continuous -- the uniform delta serves at
;;; each point.
;;; =====================================================================

(define r5r-pt #f)                      ; the point the continuity lane is at

(define (r5r-uc-eps!)
  (dk-peel!)
  (let* ((pos (dk-pick (dk-head? 'POS-RR) "POS-RR eps"))
         (eps (cadr pos))
         (u   (dk-pick (lambda (f)
                         (and (pair? f) (eq? (car f) 'FORALL)
                              (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                              (pair? (cadr (caddr f)))
                              (eq? (car (cadr (caddr f))) 'POS-RR)
                              (pair? (caddr (caddr f)))
                              (eq? (car (caddr (caddr f))) 'FORSOME)))
                       "the uniform eps-universal"))
         (ex  (dk-apply! u eps))
         (d   (dk-skolem! ex)))
    (ew d)
    (dk-conj-close!
     (lambda ()
       (if (member (dk-goal) (dk-asms))
           (ass)
           (begin
             (dk-peel!)
             (let* ((bs  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '<=)
                                                   (pair? (cadr f))
                                                   (pair? (car (cadr f)))
                                                   (eq? (car (car (cadr f))) 'DIST)))
                                  "the delta premise"))
                    (pt2 (caddr (cadr bs)))
                    (uu  (dk-pick (lambda (f)
                                    (and (pair? f) (eq? (car f) 'FORALL)
                                         (pair? (caddr f))
                                         (eq? (car (caddr f)) 'IMPLIES)
                                         (pair? (caddr (caddr f)))
                                         (eq? (car (caddr (caddr f))) 'FORALL)))
                                  "the skolemized uniform body")))
               (dk-apply! uu r5r-pt pt2)
               (ass))))))))

(define (r5r-uc-inner!)
  (if (member (dk-goal) (dk-asms)) (ass) (r5r-uc-eps!)))

(define (r5r-uc-leaf!)
  (if (member (dk-goal) (dk-asms))
      (ass)
      (begin
        (di)
        (set! r5r-pt (list-ref (dk-goal) 4))
        (mac 'IS-CONTINUOUS-AT)
        (dk-conj-close! r5r-uc-inner!))))

(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-UNIFORMLY-CONTINUOUS s t f)
       (IS-CONTINUOUS s t f)))))))
(dk-peel-to! 'IS-CONTINUOUS)
(let ((h (dk-pick (dk-head? 'IS-UNIFORMLY-CONTINUOUS) "IS-UNIFORMLY-CONTINUOUS")))
  (dk-split-all! (dk-landed* (lambda () (mac-h 'IS-UNIFORMLY-CONTINUOUS h)))))
(mac 'IS-CONTINUOUS)
(dk-conj-close! r5r-uc-leaf!)
(qed 'uniformly-continuous-is-continuous)
(topic! 'uniformly-continuous-is-continuous 'topology)

;;; =====================================================================
;;; (4) nag-metric-carrier -- the first component of the LIST constructor
;;; =====================================================================

(sp (make-wff '(FORALL nag (== (PTS (NAG-METRIC-SPACE nag)) (CARR nag)))))
(di)
(mac 'NAG-METRIC-SPACE)
(slot 'PTS)
(nth-r)
(qrfl)
(qed 'nag-metric-carrier)
(topic! 'nag-metric-carrier 'plumbing)

;;; =====================================================================
;;; (5) nag-metric-distance -- the second component, beta-reduced
;;; =====================================================================

;;; (IN ((OP) a b) COD) from (IN OP (FUN (CARTESIAN DA DB) COD)) -- the
;;; op-typing.scm recipe (apply-tupling-2 rewrites the GOAL, `==' and all),
;;; in a have! lane.
(define (r5r-op2! op a b da db cod)
  (let ((claim (list 'IN (list op a b) cod)))
    (dk-have! claim
      (lambda ()
        (fact 'apply-tupling-2 op a b)
        (subst (list '== (list op a b) (list op (list 'LIST a b))))
        (fact 'pair-in-cartesian da db a b)
        (fact 'fun-apply-type-c op (list 'CARTESIAN da db) cod (list 'LIST a b))
        (ass)))
    claim))

(define (r5r-op1! op a da cod)
  (let ((claim (list 'IN (list op a) cod)))
    (dk-have! claim (lambda () (fact 'fun-apply-type-c op da cod a) (ass)))
    claim))

(sp (make-wff '(FORALL nag
     (IMPLIES (IS-NORMED-AG nag)
       (FORALL u (IMPLIES (IN u (CARR nag))
         (FORALL v (IMPLIES (IN v (CARR nag))
           (= ((DIST (NAG-METRIC-SPACE nag)) u v)
              ((NRM nag) ((OPR nag) u ((INV nag) v))))))))))))
(dk-peel-to! '=)
(dk-split-all! (dk-landed* (lambda () (mac-h 'IS-NORMED-AG '(IS-NORMED-AG nag)))))
;; `=' is the definedness predicate, so the closing `rfl' owes the typing of
;; the norm value: land it (and the two closures under it) BEFORE the beta.
(r5r-op1! '(INV nag) 'v '(CARR nag) '(CARR nag))
(r5r-op2! '(OPR nag) 'u '((INV nag) v) '(CARR nag) '(CARR nag) '(CARR nag))
(r5r-op1! '(NRM nag) '((OPR nag) u ((INV nag) v)) '(CARR nag) 'RR)
(mac 'NAG-METRIC-SPACE)
(slot 'DIST)
(nth-r)
(lam-b)
(rfl)
(qed 'nag-metric-distance)
(topic! 'nag-metric-distance 'constructions)

;;; =====================================================================
;;; (6) nag-metric-space-is-metric-space -- the generic lemma at the
;;; NORMED-AG-AS-ABELIAN-GROUP view
;;; =====================================================================

(define r5r-G '(NORMED-AG-AS-ABELIAN-GROUP nag))

(sp (make-wff '(FORALL nag
     (IMPLIES (IS-NORMED-AG nag)
       (IS-METRIC-SPACE (NAG-METRIC-SPACE nag))))))
(dk-peel-to! 'IS-METRIC-SPACE)
;; the view's typing axiom FIRST: `mac-h' REPLACES IS-NORMED-AG, and that
;; hypothesis is exactly the axiom's antecedent.
(fact 'normed-ag-as-abelian-group-is-abelian-group 'nag)
(dk-split-all! (dk-landed* (lambda () (mac-h 'is-normed-ag '(IS-NORMED-AG nag)))))
(for-each (lambda (acc) (r5r-readoff! acc 'nag 'NORMED-AG-AS-ABELIAN-GROUP))
          '(CARR OPR IDEN INV))
(dk-have! (list 'is-group-norm '(NRM nag) (list 'OPR r5r-G) (list 'INV r5r-G)
                (list 'IDEN r5r-G) (list 'CARR r5r-G))
          (lambda ()
            (for-each (lambda (acc)
                        (subst (list '== (list acc r5r-G) (list acc 'nag))))
                      '(OPR INV IDEN CARR))
            (ass)))
(dk-fact! 'ag-norm-metric-is-metric-space r5r-G '(NRM nag))
(mac 'NAG-METRIC-SPACE)
(for-each (lambda (acc) (subst (list '== (list acc 'nag) (list acc r5r-G))))
          '(OPR INV CARR))
(ass)
(qed 'nag-metric-space-is-metric-space)
(topic! 'nag-metric-space-is-metric-space 'constructions)

;;; =====================================================================
;;; (7) nvs-metric-is-ms -- the norm metric of a normed vector space is the
;;; NORMED-AG metric of its additive normed group
;;; =====================================================================

(define r5r-V '(NORMED-VECTOR-SPACE-AS-NORMED-AG m))

(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m)
                  (IS-METRIC-SPACE (NVS-METRIC-SPACE m))))))
(dk-peel-to! 'IS-METRIC-SPACE)
(fact 'normed-vector-space-as-normed-ag-is-normed-ag 'm)
(dk-fact! 'nag-metric-space-is-metric-space r5r-V)
;; the two constructors build the SAME tuple -- unfold both, read the view's
;; slots off, and close the `==' (which is alpha-aware: the two distance
;; lambdas bind [x, y] and [u, v]).
(dk-have! (list '== '(NVS-METRIC-SPACE m) (list 'NAG-METRIC-SPACE r5r-V))
          (lambda ()
            (mac 'NVS-METRIC-SPACE)
            (mac 'NAG-METRIC-SPACE)
            (mac 'NORMED-VECTOR-SPACE-AS-NORMED-AG)
            (for-each (lambda (acc) (quietly (lambda () (slot acc))))
                      '(CARR OPR INV NRM))
            (let loop ((n 0))
              (let ((g (dk-goal)))
                (quietly (lambda () (nth-r)))
                (if (and (< n 10) (not (equal? g (dk-goal)))) (loop (+ n 1)))))
            (qrfl)))
(subst (list '== '(NVS-METRIC-SPACE m) (list 'NAG-METRIC-SPACE r5r-V)))
(ass)
(qed 'nvs-metric-is-ms)
(topic! 'nvs-metric-is-ms 'analysis)

;;; =====================================================================
;;; NOT DONE HERE -- the three leaves this batch leaves, with their routes
;;; =====================================================================
;;;
;;; (A) nf-metric-space-is-metric-space (structure-library/normed-field-metric.scm:73).
;;;     The generic lemma above applies at NORMED-FIELD-ADDITIVE-AG(nf)
;;;     (views.scm:92, slots CARR ADD ZERO NEG) as soon as
;;;         is-group-norm(FNRM nf, ADD nf, NEG nf, ZERO nf, CARR nf)
;;;     is available.  FOUR of its five conjuncts are conjuncts of `is-norm'
;;;     (the FNRM typing, nonnegativity, definiteness, subadditivity).  The
;;;     fifth, INVERSE-INVARIANCE
;;;         forall a in CARR(nf).  FNRM((NEG nf) a) = FNRM(a),
;;;     IS NOT A CONJUNCT OF is-norm and does not exist anywhere in the tree.
;;;     is-norm has no inverse clause because a FIELD norm gets it from
;;;     MULTIPLICATIVITY, and that derivation is the whole of the work:
;;;
;;;       neg a = (neg one) . a          ring-neg-mul-left at (one, a), then
;;;                                      is-identity MUL ONE to drop `one .';
;;;                                      the ring layer is reached through
;;;                                      NORMED-FIELD-AS-COMMUTATIVE-RING and the
;;;                                      six `normed-field-ring-view-*' read-offs
;;;                                      (theorem-library/normed-field-ring-view.scm),
;;;                                      which are stated view-side, so each use
;;;                                      needs the OTHER orientation too
;;;                                      (r5r-slot-close! above proves either).
;;;       ||neg a|| = ||neg one|| ||a||  multiplicativity
;;;       (neg one).(neg one) = one      ring-neg-mul-left + ring-neg-neg
;;;       so t := ||neg one|| has t.t = s, where s := ||one||, and s = s.s
;;;       CASE one = zero:  every a is zero (ring-mul-zero-left), neg zero = zero
;;;                         (ring-neg-zero), so the claim is an identity.
;;;       CASE one /= zero: s /= 0 by definiteness, s = s.s and rr-no-zero-divisors
;;;                         give s = 1; then t.t = 1 with 0 <= t (nonnegativity)
;;;                         gives t = 1 -- (t-1)(t+1) = 0 by `crs',
;;;                         rr-no-zero-divisors, and `ineq' to kill t = -1.
;;;     Every brick exists; it is ~200-300 lines of equation chaining across two
;;;     branches and was left rather than slogged.  NOTE the case split is not
;;;     optional dressing: `normed-field-zero-not-one' (normed-field.scm:67) is a
;;;     bare `theory-add-axiom!' with no `warrant!', so citing it would make the
;;;     result `trust: none' -- WORSE than the `informal' support it replaces.
;;;     Proving the degenerate branch instead keeps the bill at `modulo 0'.
;;;     The right shape is a separate `nf-norm-neg' theorem; with it,
;;;     nf-metric-space-is-metric-space is the ten lines of section (6) above.
;;;
;;; (B) ip-normed-ag-is-normed-ag (structure-library/complex-inner-product.scm:311).
;;;     Target is IS-NORMED-AG of a LIST, so the generic lemma does not apply;
;;;     what is needed is the packaging (length 5, the four typings, the four
;;;     abelian-group properties -- all literal conjuncts of
;;;     IS-COMPLEX-INNER-PRODUCT-SPACE) plus is-group-norm for
;;;     x |-> SQRT(<x,x>), whose four clauses are: nonnegativity (sqrt-nonneg),
;;;     definiteness (cips-ip-definite plus sqrt's zero law), subadditivity
;;;     (`cips-minkowski', PROVEN in inner-product-inequalities.scm:322 -- the
;;;     one clause with content is already done), and INVERSE-INVARIANCE
;;;     <-x,-x> = <x,x>, which again does not exist.  Its route does NOT need
;;;     the scalar action: additivity in the first argument at y = -x gives
;;;     <0,z> = <x,z> + <-x,z>, hence <-x,z> = -<x,z>; conjugate symmetry
;;;     (cips-ip-conj-sym) and the law "ip(s)(x,x) in rr" turn that into
;;;     <x,-x> = -<x,x>, and one more application gives <-x,-x> = <x,x>.
;;;     Every step is CC arithmetic over the declared laws.  Estimate 250+ lines;
;;;     the norm-value beta (`ip-normed-ag-norm-value' is already definitional)
;;;     is what keeps the lambda out of the metric clauses.
;;;
;;; (C) dual-is-normed-vector-space (structure-library/dual-space.scm:136) --
;;;     ROUTE ONLY, and the route starts outside the proof.  dual-space.scm's own
;;;     header says the statement is VACUOUS while IS-NORMED-VECTOR-SPACE is
;;;     unsatisfiable; that defect was repaired in normed-vector-space.scm
;;;     (2026-08-23, the SCAL slot now holds the RING VIEW), so the statement now
;;;     has content and the header is stale.  Proving it means: DUAL-VEC(m) is
;;;     closed under the pointwise operations (three closure lemmas about
;;;     IS-BOUNDED-LINEAR-FUNCTIONAL, none of which exists), the zero functional is
;;;     in it, and DUAL-NORM is a norm on it -- of whose four clauses only
;;;     nonnegativity is immediate; definiteness, homogeneity and subadditivity
;;;     each need DUAL-NORM's leastness (`dual-norm-least', asserted).  It is a
;;;     file of its own, not a leaf.
