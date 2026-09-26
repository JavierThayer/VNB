;;; ptwise-cauchy-unif.scm -- pointwise Cauchy + equicontinuous on a COMPACT
;;; space  =>  uniformly Cauchy  (the user's notes, Prop 3.33, Cauchy spelling).
;;;
;;;     ptwise-cauchy-compact-equicont-unif:
;;;       forall s, fam.  IS-COMPACT s  =>  fam in FUN(NN, FUN(PTS s, RR))  =>
;;;         IS-EQUICONTINUOUS s RR-MS fam  =>  IS-PTWISE-CAUCHY s fam  =>
;;;         IS-UNIF-CAUCHY s fam
;;;
;;; Statement UNCHANGED from the support it retires
;;; (theorem-library/ascoli-analytic-cores.scm:369, warranted `reference').
;;;
;;; THE PROOF.  Fix eps > 0 and halve it twice: c with 4c = eps.  The cover is
;;; the SET
;;;
;;;     COV = { u in POWER(PTS s) | IS-OPEN s u  and
;;;             forsome n in NN. forall k,l >= n. forall x in u.
;;;               |fam(k)(x) - fam(l)(x)| < eps }
;;;
;;; -- the open subsets on which the family is UNIFORMLY Cauchy at tolerance
;;; eps, each carrying its own threshold.  No centres and no radii are stored,
;;; so nothing has to be recovered from a cover member later: the threshold is
;;; read off the member's own defining property.  This dissolves obstacle (ii)
;;; of scratchpad/triage/metric-normed.md -- "the cover's members must be balls
;;; with RECOVERABLE centres and deltas".  They need not be balls.
;;;
;;;   COV IS AN OPEN COVER.  Members are open by construction; for the union,
;;;   class-extensionality.  A point of the union is in some member, a subset
;;;   of PTS s (power-set-membership).  A point v of PTS s lies in the ball
;;;   BALL(s, v, del) with del the equicontinuity radius at (v, c), and that
;;;   ball is in COV: it is open (ball-is-open), a subset of PTS s, and the
;;;   pointwise-Cauchy threshold cap at (v, c) serves it uniformly -- for y in
;;;   the ball and k, l >= cap,
;;;       |f_k y - f_l y| <= |f_k y - f_k v| + |f_k v - f_l v| + |f_l v - f_l y|
;;;                       <   c + c + c  <  eps,
;;;   one `ineq' certificate over two triangle instances (rr-abs-triangle-c),
;;;   one symmetry (rr-abs-sub-sym), the two equicontinuity hops opened by
;;;   rr-ms-dist and the pointwise hop.  Compare ascoli-analytic-cores.scm,
;;;   whose four-hop estimate this copies with one hop fewer.
;;;
;;;   THE FINITE SUBCOVER.  IS-COMPACT at COV gives SUB subset COV, CARD SUB
;;;   in NN, IS-OPEN-COVER s SUB.  SUB is a set (subclass-of-set-is-set: COV
;;;   is a SEP over POWER(PTS s), a set by power-set).
;;;
;;;   THE MAX.  Each member u of SUB has thresholds
;;;       CAPS(u) = { n in NN | n serves u };
;;;   CHOICE picks one, and the choice is sound because u in COV exhibits a
;;;   member (choose!, driver-kit).  THR = IMAGE(u |-> CHOICE(CAPS u), SUB) is
;;;   finite (card-image-finite) and a subset of NN, so nn-finite-subset-
;;;   bounded gives N in NN with  N <= y => y not in THR  for y in NN.  For
;;;   every member u of SUB the chosen threshold w is in THR, hence not
;;;   N <= w, hence w <= N (rr-leq-total; the other branch is refuted
;;;   propositionally, by `prop' over three named hypotheses).
;;;
;;;   THE ESTIMATE.  For k, l >= N and x in PTS s: x lies in some u in SUB
;;;   (open-cover-covers-point), u in COV, its chosen threshold w <= N <= k, l
;;;   (nn-le-trans-guarded), and the serving property of w at (k, l, x) IS the
;;;   goal.
;;;
;;; NO NEW VOCABULARY: the cover, the threshold sets and the choice map are
;;; TERMS built in the driver (SEP, IMAGE, VNB-LAMBDA, CHOICE), read apart by
;;; the kernel rules sep-mi / sep-me / sep-set / bu-mi / bu-me / lam-b and the
;;; two membership iffs (image-membership-iff, power-set-membership).  Ball
;;; memberships go through the PROVEN unfold equation ball-sep-unfold
;;; (ball-cover-lemmas.scm), never through the `proof'-warranted supports
;;; ball-membership / ball-is-set.
;;;
;;; Two mechanics worth keeping.  `ai' REMOVES the conjunction it splits, so
;;; a guard that a later `fact' must detach WHOLE (ball-is-open's r-condition)
;;; is re-landed with `have!' after the split (pcu-pos-atoms!).  And the last
;;; instantiation of the serving property lands the GOAL itself, which grounds
;;; the node and leaves nothing for a landing check to read -- so it is a bare
;;; `inst+', not `dk-apply!'.
;;;
;;; CITATIONS and load positions (0-based over prover-load, 2026-09-15):
;;;   class-extensionality, power-set, power-set-membership, choice-axiom,
;;;   subset-def, rr-leq-total  -- library.scm / number-systems (primitive);
;;;   image-membership-iff (structure-library/injection, 83);
;;;   metric-self-zero (structure-library/metric-laws, 239);
;;;   fun-apply-type-c (163); rr-sub-in-rr (binary-minus-laws, 162);
;;;   nn-in-rr, nn-le-trans-guarded (nn-order-basics, 168);
;;;   rr-pos-rr-in-rr, rr-lt-of-pos-rr (pos-rr-bridges, 173, via dk-halve!);
;;;   rr-abs-triangle-c, rr-abs-sub-sym (rr-abs-basics, 174);
;;;   rr-pos-halvable (rr-halving, 180); subclass-of-set-is-set, subset-mem-fwd
;;;   (subset-lemmas, 188); card-image-finite (222); nn-finite-subset-bounded
;;;   (225); ball-sep-unfold, open-cover-covers-point (ball-cover-lemmas, 231);
;;;   rr-ms-dist (246); is-equicontinuous (ascoli-arzela-statement, 252);
;;;   is-ptwise-cauchy, is-unif-cauchy (ascoli-analytic-cores, 253);
;;;   ball-is-open (theorem-library/ball-is-open, PROVEN 2026-09-15 -- to be
;;;   loaded between metric-laws and this file; until then the support at
;;;   structure-library/metric-open-sets.scm:80).
;;;
;;; LOAD WINDOW: lo = 254 (right after ascoli-analytic-cores, which DEFINES the
;;; two Cauchy predicates); hi = the citer, which is ascoli-analytic-cores.scm
;;; ITSELF (line 413, the assembly equicont-dense-conv-implies-unif-cauchy).
;;; So the integrator must split that file: the assembly (its last block) has
;;; to move below this file.
;;;
;;; Helper prefix: pcu-.

;;; --- statement (copied from the support's definition site) --------------

(define pcu-stmt
  (forall-guarded '(s fam)
    (list
      '(IS-COMPACT s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(IS-EQUICONTINUOUS s RR-MS fam)
      '(IS-PTWISE-CAUCHY s fam))
    '(IS-UNIF-CAUCHY s fam)))

;;; --- file-local helpers ---------------------------------------------------

(define (pcu-head? f h) (and (pair? f) (eq? (car f) h)))

(define (pcu-mentions? fm sym)
  (let loop ((e fm))
    (cond ((eq? e sym) #t)
          ((pair? e) (or (loop (car e)) (loop (cdr e))))
          (#t #f))))

;; 1-based context index of FORM, for `ineq'.
(define (pcu-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "pcu-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))

;; run THUNK (a branching tactic) and visit each opened leaf with VISIT.
(define (pcu-each-leaf! thunk visit)
  (for-each (lambda (leaf) (dk-focus! leaf) (visit))
            (dk-opened thunk)))

;; P(u, n, eps): threshold n serves the set u at tolerance eps.
(define (pcu-P u n eps)
  `(FORALL k_ (IMPLIES (AND (IN k_ NN) (<= ,n k_))
     (FORALL l_ (IMPLIES (AND (IN l_ NN) (<= ,n l_))
       (FORALL x_ (IMPLIES (IN x_ ,u)
         (< (abs (- ((fam k_) x_) ((fam l_) x_))) ,eps))))))))

;; "some threshold serves u"
(define (pcu-served u eps)
  `(FORSOME n_ (AND (IN n_ NN) ,(pcu-P u 'n_ eps))))

;; the cover: open subsets of PTS s that some threshold serves
(define (pcu-cover eps)
  `(SEP u_ (POWER (PTS s)) (AND (IS-OPEN s u_) ,(pcu-served 'u_ eps))))

;; the thresholds serving u
(define (pcu-caps u eps) `(SEP n_ NN ,(pcu-P u 'n_ eps)))

;; a "served" existential in the context that mentions U
(define (pcu-served? f u)
  (and (pcu-head? f 'FORSOME)
       (let ((b (cadr f)) (body (caddr f)))
         (and (pcu-head? body 'AND)
              (equal? (cadr body) (list 'IN b 'NN))
              (pcu-mentions? f u)))))

;; (IN d RR), (<= 0 d), (NOT (= 0 d)) and their conjunction, off (POS-RR d),
;; which stays in context (mac-h in a lane, the CLAUDE.md trick).
(define (pcu-pos-atoms! d)
  (let ((conj `(AND (IN ,d RR) (AND (<= 0 ,d) (NOT (= 0 ,d))))))
    (dk-have! conj (lambda () (mac-h 'pos-rr `(POS-RR ,d)) (ass)))
    (dk-split-all! (list conj))                 ; `ai' REMOVES the conjunction ...
    (have! conj)))                              ; ... and ball-is-open wants it whole

;; (IN z (BALL s c r)) in context: open it to its SEP atoms -- (IN z (PTS s)),
;; (<= d r), (NOT (= d r)) -- through the PROVEN unfold equation ball-sep-unfold
;; (ball-cover-lemmas.scm) and sep-me, rather than the `proof'-warranted
;; support ball-membership.
(define (pcu-open-ball-h! mem)
  (let ((sm (dk-landed-1 (lambda () (mac-h 'ball-sep-unfold mem)))))
    (dk-split-all! (dk-landed (lambda () (sep-me sm))))))

;; |a - c| <= |a - b| + |b - c| landed (acc-tri! of ascoli-analytic-cores).
(define (pcu-tri! aa bb cc)
  (let ((u (list '- aa bb)) (v (list '- bb cc)) (w (list '- aa cc)))
    (fact 'rr-sub-in-rr aa bb)
    (fact 'rr-sub-in-rr bb cc)
    (fact 'rr-sub-in-rr aa cc)
    (have! (list '<= (list 'abs w) (list '+ (list 'abs u) (list 'abs v)))
      (lambda ()
        (have! (list '= w (list '+ u v)) (lambda () (crs)))
        (subst (list '= w (list '+ u v)))
        (fact 'rr-abs-triangle-c u v)
        (ass)))))

;;; --- the cover is an open cover ------------------------------------------

;; goal (IN v (PTS s)), context (IN v BU): v is in some member, a subset of PTS s.
(define (pcu-bu-in-pts! v bu cov)
  (let* ((landed (dk-landed (lambda () (bu-me `(IN ,v ,bu)))))
         (memC (dk-pick (lambda (f) (and (pcu-head? f 'IN) (equal? (caddr f) cov)
                                         (member f landed)))
                        "the landed member-of-cover"))
         (e (cadr memC)))
    (dk-split-all! (dk-landed (lambda () (sep-me memC))))
    (let ((pw (dk-pick (lambda (f) (and (pcu-head? f 'IN) (eq? (cadr f) e)
                                        (pcu-head? (caddr f) 'POWER)))
                       "the member in POWER(PTS s)")))
      (dk-split-all! (dk-landed (lambda () (mac-h 'power-set-membership pw))))
      (let ((incl (dk-pick (lambda (f) (and (pcu-head? f 'FORALL) (pcu-mentions? f e)
                                            (pcu-mentions? f 'PTS)))
                           "the inclusion universal")))
        (dk-apply! incl v)
        (ass)))))

;; goal P(ball, cap, eps), the serving property of the ball about v.
(define (pcu-serve! v del cap ball eps hh c)
  (let* ((landed (dk-peel!))
         (g (dk-goal))                           ; (< (abs (- ((fam k) y) ((fam l) y))) eps)
         (A (cadr (cadr (cadr g))))
         (B (caddr (cadr (cadr g))))
         (k (cadr (car A))) (l (cadr (car B))) (y (cadr A))
         (memb (dk-pick (lambda (f) (and (pcu-head? f 'IN) (equal? (caddr f) ball)
                                         (member f landed)))
                        "y in the ball"))
         (PCc (dk-pick (lambda (f) (and (pcu-head? f 'FORALL) (pcu-mentions? f cap)
                                        (pcu-mentions? f 'abs)))
                       "the cap universal"))
         (p1 (dk-apply! PCc k l)))               ; guards are the landed ANDs
    (dk-split-all! landed)
    (pcu-open-ball-h! memb)
    (have! `(< ((DIST s) ,v ,y) ,del) (lambda () (mac '<) (from-context!)))
    (let* ((EQd (dk-pick (lambda (f) (and (pcu-head? f 'FORALL) (pcu-mentions? f del)
                                          (pcu-mentions? f 'DIST)))
                         "the delta universal"))
           (fk `(fam ,k)) (fl `(fam ,l))
           (fkv `(,fk ,v)) (fky `(,fk ,y)) (flv `(,fl ,v)) (fly `(,fl ,y)))
      (fact 'fun-apply-type-c 'fam 'NN '(FUN (PTS s) RR) k)
      (fact 'fun-apply-type-c 'fam 'NN '(FUN (PTS s) RR) l)
      (fact 'fun-apply-type-c fk '(PTS s) 'RR v)
      (fact 'fun-apply-type-c fk '(PTS s) 'RR y)
      (fact 'fun-apply-type-c fl '(PTS s) 'RR v)
      (fact 'fun-apply-type-c fl '(PTS s) 'RR y)
      (let ((e1 (dk-apply! EQd k y))              ; d_RR(f_k v, f_k y) < c
            (e2 (dk-apply! EQd l y)))             ; d_RR(f_l v, f_l y) < c
        (mac-h 'rr-ms-dist e1)
        (mac-h 'rr-ms-dist e2)
        (pcu-tri! fky fkv fly)
        (pcu-tri! fkv flv fly)
        (fact 'rr-abs-sub-sym fkv fky)
        (let* ((ab (lambda (u w) `(abs (- ,u ,w))))
               (prem (list
                      `(<= ,(ab fky fly) (+ ,(ab fky fkv) ,(ab fkv fly)))
                      `(<= ,(ab fkv fly) (+ ,(ab fkv flv) ,(ab flv fly)))
                      `(= ,(ab fkv fky) ,(ab fky fkv))
                      `(< ,(ab fkv fky) ,c)
                      `(< ,(ab fkv flv) ,c)
                      `(< ,(ab flv fly) ,c)
                      `(= (+ ,c ,c) ,hh)
                      `(= (+ ,hh ,hh) ,eps)
                      `(< 0 ,c))))
          (apply ineq (map pcu-idx prem)))))))

;; goal (IN ball cov): sep-mi, then the three obligations.
(define (pcu-ball-in-cover! v del cap ball cov eps hh c)
  (pcu-each-leaf!
   (lambda () (sep-mi))
   (lambda ()
     (let ((g (dk-goal)))
       (if (pcu-head? (caddr g) 'POWER)         ; (IN ball (POWER (PTS s)))
           (begin
             (mac 'power-set-membership)
             (dk-conj-close!
              (lambda ()
                (if (pcu-head? (dk-goal) 'FORALL)
                    (let ((mem (car (dk-peel!))))
                      (pcu-open-ball-h! mem)
                      (ass))
                    (begin (mac 'ball-sep-unfold) (sep-set) (ass))))))
           ;; (AND (IS-OPEN s ball) (FORSOME n_ ...))
           (pcu-each-leaf!
            (lambda () (di))
            (lambda ()
              (let ((g (dk-goal)))
                (cond ((pcu-head? g 'IS-OPEN) (fact 'ball-is-open 's v del) (ass))
                      ((pcu-head? g 'FORSOME)
                       (ew cap)
                       (pcu-each-leaf!
                        (lambda () (di))
                        (lambda ()
                          (if (pcu-head? (dk-goal) 'IN)
                              (ass)
                              (pcu-serve! v del cap ball eps hh c)))))
                      (#t (error "pcu-ball-in-cover!: unexpected goal"
                                   (expression->string g))))))))))))

;; goal (IN v BU), context (IN v (PTS s)): witness the equicontinuity ball.
(define (pcu-pts-in-bu! v bu cov eps hh c EQ PC)
  (let* ((del (dk-skolem! (inst*! EQ v c)))
         (cap (dk-skolem! (inst*! PC v c)))
         (ball `(BALL s ,v ,del)))
    (pcu-pos-atoms! del)
    (dk-fact! 'metric-self-zero 's v)
    (pcu-each-leaf!
     (lambda () (bu-mi ball))
     (lambda ()
       (if (equal? (caddr (dk-goal)) ball)          ; (IN v ball)
           (begin (mac 'ball-sep-unfold)
                  (pcu-each-leaf!
                   (lambda () (sep-mi))
                   (lambda ()
                     (if (pcu-head? (dk-goal) 'AND)
                         (begin (subst `(= ((DIST s) ,v ,v) 0))
                                (dk-conj-close!))
                         (ass)))))
           (pcu-ball-in-cover! v del cap ball cov eps hh c))))))

;; goal (IS-OPEN-COVER s cov)
(define (pcu-cover-is-open-cover! cov eps hh c EQ PC)
  (mac 'is-open-cover)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond
         ((pcu-head? g 'IS-METRIC-SPACE) (ass))
         ((pcu-head? g 'FORALL)                     ; members are open
          (let ((mem (car (dk-peel!))))
            (dk-split-all! (dk-landed (lambda () (sep-me mem))))
            (ass)))
         ((pcu-head? g '==)                         ; BIG-UNION == PTS s
          (let ((bu (cadr g)))
            (have! `(= ,bu (PTS s))
              (lambda ()
                (bc* 'class-extensionality)
                (di)
                (let ((v (cadr (cadr (dk-goal)))))  ; (IFF (IN v BU) (IN v (PTS s)))
                  (pcu-each-leaf!
                   (lambda () (di))
                   (lambda ()
                     (if (pcu-head? (caddr (dk-goal)) 'PTS)
                         (pcu-bu-in-pts! v bu cov)
                         (pcu-pts-in-bu! v bu cov eps hh c EQ PC)))))))
            (subst `(= ,bu (PTS s)))
            (qrfl)))
         (#t (error "pcu-cover-is-open-cover!: unexpected conjunct"
                      (expression->string g))))))))

;;; --- the threshold of a member, chosen ------------------------------------

;; x in sub (subset cov): land (IN (CHOICE caps) NN) and P(x, CHOICE caps) with
;; caps = CAPS(x); return caps.
(define (pcu-choose-cap! x sub cov eps)
  (let ((memC (dk-fact! 'subset-mem-fwd sub cov x)))
    (dk-split-all! (dk-landed (lambda () (sep-me memC))))
    (let* ((ex (dk-pick (lambda (f) (pcu-served? f x)) "the served existential"))
           (cap (dk-skolem! ex))
           (caps (pcu-caps x eps)))
      (choose! caps cap
               (lambda () (pcu-each-leaf! (lambda () (sep-mi)) (lambda () (ass)))))
      caps)))

;; goal (SUBSET (IMAGE phi sub) NN)
(define (pcu-image-in-nn! phi sub thr cov eps)
  (let* ((w (subset-by-element!))
         (ex (dk-landed-1 (lambda () (mac-h 'image-membership-iff `(IN ,w ,thr)))))
         (x (dk-skolem! ex))
         (eq (dk-pick (lambda (f) (and (pcu-head? f '=) (pair? (cadr f))
                                       (equal? (car (cadr f)) phi)))
                      "the applied-lambda equation")))
    (lam-b-h eq)                                    ; (= (CHOICE caps) w)
    (let ((caps (pcu-choose-cap! x sub cov eps)))
      (subst `(= ,w (CHOICE ,caps)))
      (ass))))

;; goal (IN w (IMAGE phi sub)) with w = CHOICE(CAPS u), u in sub
(define (pcu-in-image! phi sub u w)
  (mac 'image-membership-iff)
  (ew u)
  (pcu-each-leaf!
   (lambda () (di))
   (lambda ()
     (if (pcu-head? (dk-goal) 'IN)
         (ass)
         (begin (lam-b) (rfl))))))

;;; --- the estimate at threshold N ------------------------------------------

(define (pcu-finish! sub cov thr phi N BND eps)
  (let* ((landed (dk-peel!))
         (g (dk-goal))                 ; (< (abs (- ((fam k) x) ((fam l) x))) eps)
         (A (cadr (cadr (cadr g))))
         (B (caddr (cadr (cadr g))))
         (k (cadr (car A))) (l (cadr (car B))) (x (cadr A)))
    (dk-split-all! landed)
    (let* ((u (dk-skolem! (dk-fact! 'open-cover-covers-point 's sub x)))
           (caps (pcu-choose-cap! u sub cov eps))
           (w `(CHOICE ,caps)))
      (have! `(IN ,w ,thr) (lambda () (pcu-in-image! phi sub u w)))
      (let ((imp (inst*! BND w)))                 ; (IMPLIES (<= N w) (NOT (IN w thr)))
        (dk-fact! 'nn-in-rr N)
        (dk-fact! 'nn-in-rr w)
        (have! `(AND (IN ,N RR) (IN ,w RR)))
        (let ((tot (dk-fact! 'rr-leq-total N w)))   ; (OR (<= N w) (<= w N))
          (have! `(<= ,w ,N)
            (lambda () (dk-only! tot imp `(IN ,w ,thr)) (prop))))
        (dk-fact! 'nn-le-trans-guarded w N k)
        (dk-fact! 'nn-le-trans-guarded w N l)
        (have! `(AND (IN ,k NN) (<= ,w ,k)))
        (have! `(AND (IN ,l NN) (<= ,w ,l)))
        ;; P(u, w): what sep-me landed off (IN w CAPS(u)) -- the SAME builder,
        ;; so this is the context formula and not a reconstruction.  (A pick by
        ;; "FORALL mentioning CHOICE and u" found nn-le-trans-guarded's
        ;; partly-peeled chain first.)
        (let ((Pw (dk-pick (lambda (f) (equal? f (pcu-P u w eps)))
                           "the serving property of the chosen threshold")))
          ;; the last detach lands the GOAL itself, which grounds the node and
          ;; leaves no focus for a landing check -- so no dk-apply! here.
          (let ((r (inst*! Pw k l)))
            (inst+ r x)
            (if (pair? (proof-leaves)) (ass))))))))

;;; --- main ------------------------------------------------------------------

(define (pcu-main!)
  (let* ((me  (car (dk-peel!)))                      ; (POS-RR eps)
         (eps (cadr me))
         (hh  (dk-halve! eps))                        ; hh + hh = eps
         (c   (dk-halve! hh))                         ; c + c = hh
         (cov   (pcu-cover eps)))
    (dk-fact! 'rr-pos-rr-in-rr eps)
    (have! `(IS-OPEN-COVER s ,cov)
      (lambda () (pcu-cover-is-open-cover! cov eps hh c pcu-EQ pcu-PC)))
    (let ((sub (dk-skolem! (dk-apply! pcu-CPT cov))))
      (have! `(IN ,cov SET) (lambda () (sep-set) (fact 'power-set '(PTS s)) (ass)))
      (dk-fact! 'subclass-of-set-is-set sub cov)
      (let* ((phi `(VNB-LAMBDA u_ ,sub (CHOICE ,(pcu-caps 'u_ eps))))
             (thr   `(IMAGE ,phi ,sub)))
        (dk-fact! 'card-image-finite phi sub)
        (have! `(SUBSET ,thr NN) (lambda () (pcu-image-in-nn! phi sub thr cov eps)))
        (let* ((N (dk-skolem! (dk-fact! 'nn-finite-subset-bounded thr)))
               (BND (dk-pick (lambda (f) (and (pcu-head? f 'FORALL) (pcu-mentions? f N)))
                             "the bound universal")))
          (ew N)
          (pcu-each-leaf!
           (lambda () (di))
           (lambda ()
             (if (pcu-head? (dk-goal) 'IN)
                 (ass)
                 (pcu-finish! sub cov thr phi N BND eps)))))))))

(sp (make-wff pcu-stmt))
(dk-peel!)
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-compact '(IS-COMPACT s)))))
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-equicontinuous '(IS-EQUICONTINUOUS s RR-MS fam)))))
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-ptwise-cauchy '(IS-PTWISE-CAUCHY s fam)))))
(define pcu-CPT
  (dk-pick (lambda (f) (and (pcu-head? f 'FORALL) (pcu-mentions? f 'IS-OPEN-COVER)))
           "the finite-subcover law"))
(define pcu-EQ
  (dk-pick (lambda (f) (and (pcu-head? f 'FORALL) (pcu-mentions? f 'DIST)))
           "the equicontinuity universal"))
(define pcu-PC
  (dk-pick (lambda (f) (and (pcu-head? f 'FORALL) (pcu-mentions? f 'abs)))
           "the pointwise-Cauchy universal"))
(have! '(IN (PTS s) SET)
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-metric-space '(IS-METRIC-SPACE s)))))
    (ass)))
(mac 'is-unif-cauchy)
(dk-conj-close!
 (lambda () (if (pcu-head? (dk-goal) 'FORALL) (pcu-main!) (ass))))
(qed 'ptwise-cauchy-compact-equicont-unif)
(topic! 'ptwise-cauchy-compact-equicont-unif 'analysis)
