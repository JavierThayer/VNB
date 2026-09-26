;;; theorem-library/rake-bolzano-weierstrass.scm
;;; ====================================================================
;;; The eps-GRID FINITE COVER of a closed interval -- batch 8-E, item (1) --
;;; and the scaled archimedean property it needs.
;;;
;;;   rr-archimedean-multiple    eps > 0, x in RR  =>  some n in NN has
;;;                              x <= n * eps
;;;   ccint-eps-grid-cover-at    the same cover, at a GIVEN cell count n
;;;                              (the induction carrier)
;;;   ccint-eps-grid-cover       a, b in RR, eps > 0  =>  there is a finite
;;;                              cover C of CCINT(a,b) every member of which
;;;                              has diameter <= eps
;;;   ccint-grid-cover-seq       the same, as a SEQUENCE of covers, one per
;;;                              radius -- the form block-family-combinatorial
;;;                              consumes
;;;
;;; All four `modulo 0'.  What is NOT here -- Bolzano-Weierstrass itself -- is
;;; the footer, with the exact statements and the route, every rung of which is
;;; now a theorem.
;;;
;;; WHY.  8-B's report (scratchpad/triage/RAKE-BATCH8-REPORTS.md) reduced
;;; Ascoli-Arzela to a pointwise Bolzano-Weierstrass, and B-W through the
;;; library's own combinatorial machinery (cover-block-step /
;;; block-family-combinatorial / diagonalization / rr-cauchy-converges) needs
;;; exactly ONE absent construction: a finite cover of a closed real interval
;;; by sets of small diameter.  The tree has no metric SUBSPACE structure, so
;;; [a,b] is not TOTALLY-BOUNDED in any sense the library can state; it is
;;; however COVERED by finitely many short intervals, and IS-FINITE-COVER
;;; (theorem-library/block-family-combinatorial.scm:44) is a statement about a
;;; bare SET, not about a metric space.  That is the gap this file closes.
;;;
;;; THE CONSTRUCTION, and why it is an induction and not a floor function.
;;; The textbook grid is the image of an NN segment under
;;; j |-> [a + j*eps, a + (j+1)*eps], and its coverage proof is the floor
;;; function -- which the tree does not have.  Induction on the CELL COUNT
;;; replaces it: `ccint-eps-grid-cover-at' says
;;;
;;;   n in NN, a b in RR, eps > 0, b <= a + n*eps
;;;     =>  forsome C.  IS-FINITE-COVER(C, CCINT(a,b))
;;;                     and every member of C has diameter <= eps
;;;
;;; with the RIGHT ENDPOINT LEFT FREE under the bound b <= a + n*eps, so that
;;; the step has room to move.  Base n = 0: b <= a, so the single cell
;;; {[a,b]} does it (the interval is a point or empty).  Step: put
;;; mid := a + n*eps, apply the hypothesis at (a, mid) -- legal because
;;; mid <= a + n*eps by reflexivity -- and adjoin the one cell [mid, b], whose
;;; diameter is b - mid <= eps precisely because b <= a + succ(n)*eps.
;;; Coverage splits on rr-leq-total at mid; finiteness is
;;; card-union-singleton-nn, which needs no disjointness.
;;;
;;; The general form then needs a cell count, i.e. an n in NN with
;;; b <= a + n*eps, which is the archimedean property SCALED.  The tree had
;;; only `nn-unbounded-in-rr' (x < n, no scale), so `rr-archimedean-multiple'
;;; is proven first, from it plus `rr-recip-cancel-right'
;;; (x = (x * recip(e)) * e) and `rr-mul-le-right'.  No `crs' call ever sees a
;;; `recip'.
;;;
;;; THE DEGENERATE INTERVAL.  b < a is not excluded and needs no guard:
;;; CCINT(a,b) is then EMPTY, the coverage clause is a SUBSET claim which the
;;; same driver discharges (the element introduced by subset-def carries
;;; a <= x <= b and the case split still decides), and the diameter clause is
;;; about the members of C, not about points of the interval.  a = b is the
;;; base case proper.  No inhabitedness guard is wanted and none is added.
;;;
;;; DIAMETER, spelled without a metric.  `every member of C has diameter
;;; <= eps' is
;;;
;;;   forall U in C. forall p in U. forall q in U.
;;;       p in RR and q in RR and abs(p - q) <= eps
;;;
;;; -- the two typings are part of the statement on purpose: a consumer that
;;; has two points of one cell wants them in RR before it can call `ineq', and
;;; the cells are closed intervals, so ccint-parts supplies the typing here
;;; once instead of at every call site.  Nothing mentions RR-MS, so a consumer
;;; may take the estimate to the metric side with `rr-ms-dist' or leave it
;;; where it is.
;;;
;;; LOAD WINDOW [2926, end).  window.py: lo = load.scm:2925, forced by
;;; `ccint-parts' (theorem-library/bernstein-ccint); the next latest are
;;; rr-recip-cancel-right (rake-dual-norm-spec, 2722), rr-mul-le-right
;;; (rake-hb-leaves, 2718), union-singleton-mem / card-union-singleton-nn
;;; (heine-borel-baby, 2531), ccint-subset-rr (monotone-inverse, 2029),
;;; ccint-membership (ccint-basics, 2011) and the definition of CCINT
;;; (extreme-value, 2005).  hi: nothing cites any of the four yet, so any slot
;;; after 2925 works; immediately after "theorem-library/bernstein-ccint" is
;;; the natural one.  IF A LATER CONSUMER EVER NEEDS THIS FILE EARLIER: only
;;; two citations are above 2100 and both are replaceable -- ccint-parts by
;;; ccint-membership + `prop', and rr-recip-cancel-right by rr-recip-inverse
;;; (number-systems, primitive) plus one quantified `crs' identity -- which
;;; would bring lo down to 2718 and then to ~2531.  The floor is 2029
;;; (ccint-subset-rr), since CCINT is defined at 2005.
;;;
;;; Helper prefix: r9e-.
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r9e-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-bolzano-weierstrass: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (sequent-node-assumptions l)))
                  (proof-open-goals *ps*))
        (error "rake-bolzano-weierstrass: unfinished" name))))

(define (r9e-need pred what lst)
  (or (any-pred pred lst)
      (error "rake-bolzano-weierstrass: missing" what
             (map expression->string lst))))

;;; `ineq' premises are 1-BASED INDICES into the context listing, and one
;;; uncertifiable premise poisons the call: name them by FORMULA.
(define (r9e-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r9e-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))

(define (r9e-ineq! . forms) (apply ineq (map r9e-idx forms)))

;;; (IN (CCINT lo hi) SET) -- a subclass of the set RR.
(define (r9e-ccint-set! lo hi)
  (let ((tm (list 'CCINT lo hi)))
    (have! (list 'IN tm 'SET)
      (lambda ()
        (fact 'rr-is-set)
        (fact 'ccint-subset-rr lo hi)
        (fact 'subclass-of-set-is-set tm 'RR)
        (ass)))))

;;; (IN t (PAIR t t)) -- t is a member of its own singleton.  `pairing-
;;; membership' is an IFF with a CONJUNCTIVE guard, so the AND is `have!'d
;;; first and `prop' finishes from the reflexive equation.
(define (r9e-singleton-mem! tm)
  (have! (list 'IN tm (list 'PAIR tm tm))
    (lambda ()
      (have! (list 'AND (list 'IN tm 'SET) (list 'IN tm 'SET)))
      (let ((iffm (dk-fact! 'pairing-membership tm tm tm))
            (eqf  (list '= tm tm)))
        (have! eqf (lambda () (rfl)))
        (dk-only! iffm eqf)
        (prop)))))

;;; From (IN uv (PAIR tm tm)) in context, land (= uv tm).
(define (r9e-singleton-eq! uv tm huv)
  (let ((iffm (dk-fact! 'pairing-membership tm tm uv)))
    (have! (list '= uv tm)
      (lambda () (dk-only! iffm huv) (prop)))))

;;; From (IN pt uv) and (= uv tm) in context, land (IN pt tm).  There is no
;;; hypothesis-side `subst', so the rewrite happens inside the `have!' lane,
;;; on the GOAL, in the backward direction (the context holds the equation in
;;; either orientation).
(define (r9e-move-mem! pt uv tm)
  (have! (list 'IN pt tm)
    (lambda () (subst (list '= tm uv)) (ass))))

;;; The diameter clause of a cover, and the whole existential claim.
(define (r9e-diam cc ev)
  (list 'FORALL 'uv_
    (list 'IMPLIES (list 'IN 'uv_ cc)
      (list 'FORALL 'pv_
        (list 'IMPLIES '(IN pv_ uv_)
          (list 'FORALL 'qv_
            (list 'IMPLIES '(IN qv_ uv_)
              (list 'AND '(IN pv_ RR)
                (list 'AND '(IN qv_ RR)
                      (list '<= '(ABS (- pv_ qv_)) ev))))))))))

(define (r9e-cover-claim lo hi ev)
  (list 'FORSOME 'cv_
    (list 'AND (list 'IS-FINITE-COVER 'cv_ (list 'CCINT lo hi))
          (r9e-diam 'cv_ ev))))

;;; `ni' opens the base and the step; the step is the branch whose goal speaks
;;; of `succ' (the base's does not, and neither goal's head tells them apart).
(define (r9e-step-goal? g) (dk-contains? g 'succ))

;;; The two points of the diameter goal, read off the GOAL (never off the
;;; context order): the goal is (AND (IN p RR) (AND (IN q RR) (<= ...))).
(define (r9e-diam-points)
  (let ((g (dk-goal)))
    (cons (cadr (cadr g)) (cadr (cadr (caddr g))))))

;;; |p - q| <= eps from a list of linear premises, through the rr-abs-bound
;;; IFF (its right-hand side is READ OFF the instance, so no unary minus is
;;; ever spelled here).
;;; The guard on the last two steps is not decoration: `dk-only!' can leave the
;;; focus leaf GROUNDED (the weakened sequent hash-conses onto a node an earlier
;;; branch already proved -- both branches of the induction reach the same
;;; sequent here), after which focus has moved and a bare `prop' fires on
;;; someone else's goal and prints a countermodel for it.  If the leaf is in
;;; fact still open, skipping the steps leaves it open and `r9e-qed!' says so.
(define (r9e-abs-bound! pv qv ev premises)
  (let ((target (dk-goal)))
    (fact 'rr-sub-in-rr pv qv)
    (let* ((iffm (dk-fact! 'rr-abs-bound (list '- pv qv) ev))
           (rhs  (caddr iffm)))
      (have! rhs
        (lambda ()
          (dk-conj-close! (lambda () (apply r9e-ineq! premises)))))
      (if (equal? (dk-goal) target)
          (begin
            (dk-only! iffm rhs)
            (if (equal? (dk-goal) target) (prop)))))))

;;; =====================================================================
;;; L1.  rr-archimedean-multiple -- the SCALED archimedean property.
;;;
;;;   eps > 0,  x in RR   =>   forsome n in NN.  x <= n * eps
;;;
;;; `nn-unbounded-in-rr' (x < n) is the unscaled form and the only one the
;;; tree had.  Scaling is one reciprocal cancellation: apply it at
;;; t := x * recip(eps), multiply t < n by eps > 0 (rr-mul-le-right), and
;;; rewrite t * eps back to x by `rr-recip-cancel-right'.  `crs' is never
;;; called: it declines anything containing `recip'.
;;; =====================================================================

(sp (make-wff
  '(FORALL ev_
     (IMPLIES (POS-RR ev_)
       (FORALL xv_
         (IMPLIES (IN xv_ RR)
           (FORSOME nv_ (AND (IN nv_ NN) (<= xv_ (* nv_ ev_))))))))))

(dk-peel!)

(fact 'rr-pos-rr-in-rr 'ev_)                    ; (IN ev_ RR)
(fact 'rr-lt-of-pos-rr 'ev_)                    ; (< 0 ev_)
(fact 'rr-pos-ne-zero 'ev_)                     ; (NOT (= ev_ 0))
(have! '(AND (IN ev_ RR) (NOT (= ev_ 0))))
(fact 'rr-recip-closed 'ev_)                    ; (IN (RECIP ev_) RR)
(have! '(AND (IN xv_ RR) (IN (RECIP ev_) RR)))
(fact 'rr-mul-closed 'xv_ '(RECIP ev_))         ; (IN (* xv_ (RECIP ev_)) RR)

(define r9e-a-t '(* xv_ (RECIP ev_)))

(define r9e-a-EX (dk-fact! 'nn-unbounded-in-rr r9e-a-t))
(define r9e-a-n  (dk-skolem! r9e-a-EX))         ; (IN n NN), (< t n)

(fact 'nn-in-rr r9e-a-n)                        ; (IN n RR)
(fact 'rr-lt-implies-le r9e-a-t r9e-a-n)        ; t <= n
(have! '(<= 0 ev_) (lambda () (r9e-ineq! '(< 0 ev_) '(IN ev_ RR))))
(fact 'rr-mul-le-right r9e-a-t r9e-a-n 'ev_)    ; t * ev_ <= n * ev_
(fact 'rr-recip-cancel-right 'xv_ 'ev_)         ; xv_ = (xv_ * recip(ev_)) * ev_

(witness! r9e-a-n
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN)
           (ass)
           (begin
             (subst (list '= 'xv_ (list '* r9e-a-t 'ev_)))
             (ass)))))))

(r9e-qed! 'rr-archimedean-multiple)
(topic! 'rr-archimedean-multiple 'inequalities)
(gloss! 'rr-archimedean-multiple
  "The archimedean property with a scale: for every positive eps and every
   real x there is a natural number n with x <= n * eps.  nn-unbounded-in-rr
   is the case eps = 1; the scale costs one reciprocal cancellation.")

;;; =====================================================================
;;; L2.  ccint-eps-grid-cover-at -- the grid cover at a GIVEN cell count.
;;;
;;;   n in NN, a b in RR, eps > 0, b <= a + n*eps
;;;     =>  forsome C.  IS-FINITE-COVER(C, CCINT(a,b)) and every member of C
;;;                     has diameter <= eps
;;;
;;; Induction on n, THE INDUCTION VARIABLE FIRST (`ni' tests the literal shape
;;; (FORALL n (IMPLIES (IN n NN) ...))).  The right endpoint b is left free
;;; under the bound, which is what lets the step re-use the hypothesis at the
;;; SHORTER interval (a, a + n*eps) and adjoin one cell.
;;; =====================================================================

(define r9e-aux-stmt
  (list 'FORALL 'nv_
    (list 'IMPLIES '(IN nv_ NN)
      (list 'FORALL 'av_
        (list 'IMPLIES '(IN av_ RR)
          (list 'FORALL 'bv_
            (list 'IMPLIES '(IN bv_ RR)
              (list 'FORALL 'ev_
                (list 'IMPLIES '(POS-RR ev_)
                  (list 'IMPLIES '(<= bv_ (+ av_ (* nv_ ev_)))
                        (r9e-cover-claim 'av_ 'bv_ 'ev_)))))))))))

(sp (make-wff r9e-aux-stmt))

;;; ---- the BASE: b <= a + 0*eps, so [a,b] is its own single cell ---------

(define (r9e-base!)
  (let* ((landed (dk-peel!))
         (hle  (r9e-need (dk-head? '<=) "the base bound" landed))
         (bv   (cadr hle))
         (plus (caddr hle))                    ; (+ av_ (* 0 ev_))
         (av   (cadr plus))
         (prod (caddr plus))                   ; (* 0 ev_)
         (ev   (caddr prod))
         (ii   (list 'CCINT av bv))
         (cc   (list 'PAIR ii ii)))
    (fact 'rr-pos-rr-in-rr ev)
    (fact 'rr-lt-of-pos-rr ev)
    ;; a + 0*eps = a, so the interval is a point (or empty)
    (have! (list '= av plus) (lambda () (crs)))
    (have! (list '<= bv av) (lambda () (subst (list '= av plus)) (ass)))
    (r9e-ccint-set! av bv)
    (r9e-singleton-mem! ii)                    ; (IN ii cc)
    (have! (list 'AND (list 'IN ii 'SET) (list 'IN ii 'SET)))
    (fact 'pairing ii ii)                      ; (IN cc SET)
    (fact 'card-singleton ii)                  ; (= (CARD cc) (succ 0))
    (fact 'nn-zero-in)
    (fact 'nn-succ-closed 0)                   ; (IN (succ 0) NN)
    (witness! cc
      (lambda ()
        (dk-conj-close!
         (lambda ()
           (if (eq? (car (dk-goal)) 'IS-FINITE-COVER)
               ;; ---- the finite cover -------------------------------------
               (begin
                 (mac 'IS-FINITE-COVER)
                 (dk-conj-close!
                  (lambda ()
                    (let ((g (dk-goal)))
                      (cond
                        ((eq? (car g) 'SUBSET)
                         (mac 'subset-def)
                         (dk-landed-1 (lambda () (di)))
                         (for-each (lambda (l) (dk-focus! l) (ass))
                                   (dk-opened (lambda () (bu-mi ii)))))
                        ((and (eq? (car g) 'IN) (eq? (caddr g) 'NN))
                         (subst (list '= (list 'CARD cc) '(succ 0)))
                         (ass))
                        (#t (ass)))))))
               ;; ---- the diameter -----------------------------------------
               (let* ((ls  (dk-peel!))
                      (pq  (r9e-diam-points))
                      (pv  (car pq))
                      (qv  (cdr pq))
                      (huv (r9e-need (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                      (equal? (caddr f) cc)))
                                     "the cover member" ls))
                      (uv  (cadr huv)))
                 (r9e-singleton-eq! uv ii huv)
                 (r9e-move-mem! pv uv ii)
                 (r9e-move-mem! qv uv ii)
                 (dk-landed (lambda () (fact 'ccint-parts av bv pv)))
                 (dk-landed (lambda () (fact 'ccint-parts av bv qv)))
                 (dk-split-all!)
                 (dk-conj-close!
                  (lambda ()
                    (let ((g (dk-goal)))
                      (if (eq? (car g) 'IN)
                          (ass)
                          (r9e-abs-bound!
                           pv qv ev
                           (list (list '<= av pv) (list '<= pv bv)
                                 (list '<= av qv) (list '<= qv bv)
                                 (list '<= bv av) (list '< 0 ev)
                                 (list 'IN pv 'RR) (list 'IN qv 'RR)
                                 (list 'IN av 'RR) (list 'IN bv 'RR)
                                 (list 'IN ev 'RR)))))))))))))))

;;; ---- the STEP: one more cell on the right -----------------------------

(define (r9e-step!)
  (let* ((landed (dk-peel!))
         (hle   (r9e-need (dk-head? '<=) "the step bound" landed))
         (bv    (cadr hle))
         (plus  (caddr hle))                   ; (+ av_ (* (succ nv_) ev_))
         (av    (cadr plus))
         (prod  (caddr plus))                  ; (* (succ nv_) ev_)
         (succn (cadr prod))
         (nv    (cadr succn))
         (ev    (caddr prod))
         (ih    (r9e-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f 'IS-FINITE-COVER)))
                          "the induction hypothesis" landed))
         (mid   (list '+ av (list '* nv ev))))
    (fact 'rr-pos-rr-in-rr ev)
    (fact 'rr-lt-of-pos-rr ev)
    (fact 'nn-in-rr nv)
    (have! (list 'AND (list 'IN nv 'RR) (list 'IN ev 'RR)))
    (fact 'rr-mul-closed nv ev)
    (have! (list 'AND (list 'IN av 'RR) (list 'IN (list '* nv ev) 'RR)))
    (fact 'rr-add-closed av (list '* nv ev))   ; (IN mid RR)
    (fact 'rr-leq-reflexive mid)               ; (<= mid mid)
    ;; the shorter interval, by the induction hypothesis
    (let* ((ex  (dk-apply! ih av mid ev))
           (c0  (dk-skolem! ex))
           (ihd (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (dk-contains? f c0)))
                         "the inherited diameter clause")))
      (dk-landed (lambda () (mac-h 'IS-FINITE-COVER
                                   (list 'IS-FINITE-COVER c0 (list 'CCINT av mid)))))
      (dk-split-all!)
      (let* ((hcov (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'SUBSET)
                                             (equal? (cadr f) (list 'CCINT av mid))))
                            "the coverage of the shorter interval"))
             (bu0  (caddr hcov))
             (jj   (list 'CCINT mid bv))
             (cc   (list 'UNION (list 'PAIR jj jj) c0)))
        (r9e-ccint-set! mid bv)
        (have! (list 'AND (list 'IN jj 'SET) (list 'IN jj 'SET)))
        (fact 'pairing jj jj)
        (have! (list 'AND (list 'IN (list 'PAIR jj jj) 'SET) (list 'IN c0 'SET)))
        (fact 'union-set-closure (list 'PAIR jj jj) c0)      ; (IN cc SET)
        (fact 'card-union-singleton-nn c0 jj)                ; (IN (CARD cc) NN)
        (fact 'union-singleton-mem jj c0)                    ; (IN jj cc)
        ;; b <= mid + eps -- the whole content of the step's diameter bound
        (fact 'nn-succ-plus-one nv)                          ; succ(n) = n + 1
        (have! (list '= plus (list '+ mid ev))
               (lambda () (subst (list '= succn (list '+ nv 1))) (crs)))
        (have! (list '<= bv (list '+ mid ev))
               (lambda () (subst (list '= (list '+ mid ev) plus)) (ass)))
        (witness! cc
          (lambda ()
            (dk-conj-close!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IS-FINITE-COVER)
                   ;; ---- the finite cover ---------------------------------
                   (begin
                     (mac 'IS-FINITE-COVER)
                     (dk-conj-close!
                      (lambda ()
                        (let ((g (dk-goal)))
                          (if (eq? (car g) 'SUBSET)
                              (r9e-step-coverage! av bv mid c0 jj cc bu0)
                              (ass))))))
                   ;; ---- the diameter -------------------------------------
                   (r9e-step-diam! av bv mid ev c0 jj cc ihd))))))))))

;;; coverage: a point of [a,b] is left of mid (so the inherited cover catches
;;; it) or right of mid (so the new cell does).
(define (r9e-step-coverage! av bv mid c0 jj cc bu0)
  (mac 'subset-def)
  (let* ((hx (dk-landed-1 (lambda () (di))))
         (xv (cadr hx)))
    (dk-landed (lambda () (fact 'ccint-parts av bv xv)))
    (dk-split-all!)
    (have! (list 'AND (list 'IN xv 'RR) (list 'IN mid 'RR)))
    (let ((ortot (dk-fact! 'rr-leq-total xv mid)))
      (use-cases ortot
        ;; ---- x <= mid: the inherited cover ---------------------------
        (lambda ()
          (let* ((memiff (dk-fact! 'ccint-membership av mid xv))
                 (inshort (list 'IN xv (list 'CCINT av mid))))
            (have! inshort
              (lambda ()
                (dk-only! memiff (list 'IN xv 'RR)
                          (list '<= av xv) (list '<= xv mid))
                (prop)))
            (fact 'subset-mem-fwd (list 'CCINT av mid) bu0 xv)
            (let* ((new (dk-landed (lambda () (bu-me (list 'IN xv bu0)))))
                   (hw  (r9e-need (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                   (equal? (caddr f) c0)))
                                  "the member of the inherited cover" new))
                   (wv  (cadr hw)))
              (for-each
               (lambda (l)
                 (dk-focus! l)
                 (if (equal? (caddr (dk-goal)) cc)
                     (let ((uiff (dk-fact! 'union-membership
                                           (list 'PAIR jj jj) c0 wv)))
                       (dk-only! uiff hw)
                       (prop))
                     (ass)))
               (dk-opened (lambda () (bu-mi wv)))))))
        ;; ---- mid <= x: the new cell ----------------------------------
        (lambda ()
          (let ((memiff (dk-fact! 'ccint-membership mid bv xv)))
            (have! (list 'IN xv jj)
              (lambda ()
                (dk-only! memiff (list 'IN xv 'RR)
                          (list '<= mid xv) (list '<= xv bv))
                (prop)))
            (for-each (lambda (l) (dk-focus! l) (ass))
                      (dk-opened (lambda () (bu-mi jj))))))))))

;;; diameter: a member of the new cover is the new cell (bounded by
;;; b <= mid + eps) or a member of the old one (bounded by the hypothesis).
(define (r9e-step-diam! av bv mid ev c0 jj cc ihd)
  (let* ((ls  (dk-peel!))
         (pq  (r9e-diam-points))
         (pv  (car pq))
         (qv  (cdr pq))
         (huv (r9e-need (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                         (equal? (caddr f) cc)))
                        "the cover member" ls))
         (uv  (cadr huv))
         (uiff (dk-fact! 'union-membership (list 'PAIR jj jj) c0 uv))
         (oform (caddr uiff)))
    (have! oform (lambda () (dk-only! uiff huv) (prop)))
    (use-cases oform
      ;; ---- the new cell -------------------------------------------
      (lambda ()
        (let ((hin (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                             (equal? (cadr f) uv)
                                             (equal? (caddr f) (list 'PAIR jj jj))))
                            "the singleton membership")))
          (r9e-singleton-eq! uv jj hin)
          (r9e-move-mem! pv uv jj)
          (r9e-move-mem! qv uv jj)
          (dk-landed (lambda () (fact 'ccint-parts mid bv pv)))
          (dk-landed (lambda () (fact 'ccint-parts mid bv qv)))
          (dk-split-all!)
          (dk-conj-close!
           (lambda ()
             (let ((g (dk-goal)))
               (if (eq? (car g) 'IN)
                   (ass)
                   (r9e-abs-bound!
                    pv qv ev
                    (list (list '<= mid pv) (list '<= pv bv)
                          (list '<= mid qv) (list '<= qv bv)
                          (list '<= bv (list '+ mid ev)) (list '< 0 ev)
                          (list 'IN pv 'RR) (list 'IN qv 'RR)
                          (list 'IN mid 'RR) (list 'IN bv 'RR)
                          (list 'IN ev 'RR)))))))))
      ;; ---- a member of the inherited cover -------------------------
      (lambda ()
        (dk-apply! ihd uv pv qv)
        (ass)))))

;;; ---- run the induction ------------------------------------------------

(for-each
 (lambda (l)
   (dk-focus! l)
   (let ((g (dk-goal)))
     ;; the STEP goal is (FORALL n (IMPLIES (IN n NN) (IMPLIES P P[succ n])));
     ;; the BASE is P[0], which starts with its own FORALL over `a'.  They are
     ;; told apart by the NN typing of the peeled variable, not by shape.
     (if (r9e-step-goal? g) (r9e-step!) (r9e-base!))))
 (dk-opened (lambda () (ni))))

(r9e-qed! 'ccint-eps-grid-cover-at)
(topic! 'ccint-eps-grid-cover-at 'topology)
(gloss! 'ccint-eps-grid-cover-at
  "The eps-grid cover of a closed interval, at a given cell count: if
   b <= a + n*eps then CCINT(a,b) has a finite cover every member of which has
   diameter at most eps.  Proven by induction on n; the step adjoins the one
   cell [a + n*eps, b].")

;;; =====================================================================
;;; L3.  ccint-eps-grid-cover -- the general form.
;;;
;;; The cell count comes from rr-archimedean-multiple at x := b - a.
;;; =====================================================================

(sp (make-wff
  (list 'FORALL 'av_
    (list 'IMPLIES '(IN av_ RR)
      (list 'FORALL 'bv_
        (list 'IMPLIES '(IN bv_ RR)
          (list 'FORALL 'ev_
            (list 'IMPLIES '(POS-RR ev_)
                  (r9e-cover-claim 'av_ 'bv_ 'ev_)))))))))

(dk-peel!)

(fact 'rr-pos-rr-in-rr 'ev_)
(fact 'rr-sub-in-rr 'bv_ 'av_)                       ; (IN (- bv_ av_) RR)

(define r9e-m-EX (dk-fact! 'rr-archimedean-multiple 'ev_ '(- bv_ av_)))
(define r9e-m-n  (dk-skolem! r9e-m-EX))              ; (IN n NN), (<= (- bv_ av_) (* n ev_))

(fact 'nn-in-rr r9e-m-n)
(have! (list 'AND (list 'IN r9e-m-n 'RR) '(IN ev_ RR)))
(fact 'rr-mul-closed r9e-m-n 'ev_)                   ; (IN (* n ev_) RR)

(have! (list '<= 'bv_ (list '+ 'av_ (list '* r9e-m-n 'ev_)))
  (lambda ()
    (r9e-ineq! (list '<= '(- bv_ av_) (list '* r9e-m-n 'ev_))
               '(IN av_ RR) '(IN bv_ RR)
               (list 'IN (list '* r9e-m-n 'ev_) 'RR))))

(define r9e-m-EX2
  (dk-fact! 'ccint-eps-grid-cover-at r9e-m-n 'av_ 'bv_ 'ev_))
(define r9e-m-cc (dk-skolem! r9e-m-EX2))

(witness! r9e-m-cc (lambda () (dk-conj-close! (lambda () (ass)))))

(r9e-qed! 'ccint-eps-grid-cover)
(topic! 'ccint-eps-grid-cover 'topology)
(gloss! 'ccint-eps-grid-cover
  "Every closed real interval has, for every eps > 0, a FINITE COVER all of
   whose members have diameter at most eps.  The library's stand-in for the
   total boundedness of [a,b], which cannot be stated while the tree has no
   metric subspace structure: IS-FINITE-COVER speaks only of sets.")

;;; =====================================================================
;;; L4.  ccint-grid-cover-seq -- the cover as a SEQUENCE.
;;;
;;;   a, b in RR,  rad(k) > 0 for every k in NN
;;;     =>  forsome cov.  forall k in NN.
;;;           IS-FINITE-COVER(cov(k), CCINT(a,b))  and  every member of cov(k)
;;;           has diameter <= rad(k)
;;;
;;; WHY THIS EXISTS AND WHAT IT COSTS.  `block-family-combinatorial'
;;; (theorem-library/block-family-combinatorial-proof.scm) consumes a SEQUENCE
;;; of finite covers -- the hypothesis is literally
;;; (FORALL k (IMPLIES (IN k NN) (IS-FINITE-COVER (cov k) V))) -- and L3 hands
;;; back ONE cover per eps, existentially.  Turning the one into the other is a
;;; countable choice, and the tree does it the way antiderivable-family-choice
;;; does: the choices are INDEPENDENT, so no dependent choice is needed and
;;; `cov' is a VNB-LAMBDA whose body is a CHOICE over the set of candidates
;;;
;;;     cov := k |-> CHOICE { s in POWER(POWER(RR)) : s is a finite cover of
;;;                           CCINT(a,b) of mesh <= rad(k) }
;;;
;;; and `choose!' discharges the one obligation CHOICE owes, with L3's cover as
;;; the exhibited member.  The AMBIENT SET is what makes this work: a cover of
;;; CCINT(a,b) whose members have the diameter property consists of sets of
;;; reals (the property gives every point of every member in RR, at p = q), so
;;; it lies in POWER(POWER(RR)), which is a set because RR is.  Nothing here is
;;; special to the interval; it is the generic "for each k pick one" move.
;;; =====================================================================

(define r9e-X '(POWER (POWER RR)))

(define (r9e-seq-sep ii radk)
  (list 'SEP 'sv_ r9e-X
    (list 'AND (list 'IS-FINITE-COVER 'sv_ ii) (r9e-diam 'sv_ radk))))

;;; (IN c (POWER (POWER RR))) for a cover c whose diameter clause is DIAMF:
;;; each member is a class of reals (the clause at p = q), hence a subclass of
;;; the set RR, hence a set, hence a member of POWER(RR).
(define (r9e-cover-in-power! cv ii diamf)
  ;; the sethood conjunct of IS-FINITE-COVER, landed in a lane: `mac-h'
  ;; REPLACES the predicate, and the choose! below wants it whole.
  (have! (list 'IN cv 'SET)
    (lambda ()
      (mac-h 'IS-FINITE-COVER (list 'IS-FINITE-COVER cv ii))
      (dk-split-all!)
      (ass)))
  (have! (list 'IN cv r9e-X)
    (lambda ()
      (have! (list 'FORALL 'zv_ (list 'IMPLIES (list 'IN 'zv_ cv)
                                      (list 'IN 'zv_ '(POWER RR))))
        (lambda ()
          (let* ((zv   (dk-di-var!))
                 (ptwf (list 'FORALL 'yv_ (list 'IMPLIES (list 'IN 'yv_ zv)
                                                (list 'IN 'yv_ 'RR)))))
            (have! ptwf
              (lambda ()
                (let ((yv (dk-di-var!)))
                  (dk-split! (dk-apply! diamf zv yv yv))
                  (ass))))
            (have! (list 'IN zv 'SET)
              (lambda ()
                (have! (list 'SUBSET zv 'RR)
                  (lambda ()
                    (mac 'subset-def)
                    (let ((yv (dk-di-var!)))
                      (dk-apply! ptwf yv)
                      (ass))))
                (fact 'rr-is-set)
                (fact 'subclass-of-set-is-set zv 'RR)
                (ass)))
            (fact 'power-mem-intro 'RR zv)
            (ass))))
      (fact 'power-mem-intro '(POWER RR) cv)
      (ass))))

(sp (make-wff
  (list 'FORALL 'av_
    (list 'IMPLIES '(IN av_ RR)
      (list 'FORALL 'bv_
        (list 'IMPLIES '(IN bv_ RR)
          (list 'FORALL 'rd_
            (list 'IMPLIES '(FORALL kv_ (IMPLIES (IN kv_ NN) (POS-RR (rd_ kv_))))
              (list 'FORSOME 'cw_
                (list 'FORALL 'kv_
                  (list 'IMPLIES '(IN kv_ NN)
                    (list 'AND (list 'IS-FINITE-COVER '(cw_ kv_) '(CCINT av_ bv_))
                          (r9e-diam '(cw_ kv_) '(rd_ kv_))))))))))))))

(define r9e-s-landed (dk-peel!))

(define r9e-s-HPOS
  (r9e-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'POS-RR)))
            "the positivity clause" r9e-s-landed))
(define r9e-s-rd (car (cadr (caddr (caddr r9e-s-HPOS)))))
(define r9e-s-ii '(CCINT av_ bv_))
(define r9e-s-cov
  (list 'VNB-LAMBDA 'tv_ 'NN
        (list 'CHOICE (r9e-seq-sep r9e-s-ii (list r9e-s-rd 'tv_)))))

(fact 'rr-is-set)
(fact 'power-set 'RR)                       ; (IN (POWER RR) SET)
(fact 'power-set '(POWER RR))               ; (IN (POWER (POWER RR)) SET)

(witness! r9e-s-cov
  (lambda ()
    (let ((kv (dk-di-var!)))
      (lam-b)                               ; (cov k) -> CHOICE { ... rad(k) ... }
      (dk-apply! r9e-s-HPOS kv)              ; (POS-RR (rad k))
      (let* ((sepk (r9e-seq-sep r9e-s-ii (list r9e-s-rd kv)))
             (exc  (dk-fact! 'ccint-eps-grid-cover 'av_ 'bv_ (list r9e-s-rd kv)))
             (c0   (dk-skolem! exc))
             (diamf (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                              (dk-contains? f c0)))
                             "the diameter clause of the chosen cover")))
        (r9e-cover-in-power! c0 r9e-s-ii diamf)
        (choose! sepk c0
          (lambda ()
            (for-each (lambda (l) (dk-focus! l) (dk-conj-close! (lambda () (ass))))
                      (dk-opened (lambda () (sep-mi))))))
        (ass)))))

(r9e-qed! 'ccint-grid-cover-seq)
(topic! 'ccint-grid-cover-seq 'topology)
(gloss! 'ccint-grid-cover-seq
  "A whole SEQUENCE of grid covers of one closed interval, one per radius of a
   positive radius sequence -- the form block-family-combinatorial consumes.
   The choices are independent, so this is a plain CHOICE over the set of
   candidate covers inside POWER(POWER(RR)), not a dependent choice.")

;;; =====================================================================
;;; WHAT IS LEFT: BOLZANO-WEIERSTRASS, AND WHAT IT NOW COSTS
;;;
;;; With `ccint-grid-cover-seq' in place, EVERY rung of the Bolzano-Weierstrass
;;; route named in 8-B's report is a theorem of the library.  Nothing below is
;;; a gap in the mathematics or in the machinery; what remains is one driver of
;;; the size of theorem-library/cauchy-subseq-proof.scm, which is the same
;;; assembly one abstraction layer up.  The two statements, and the route:
;;;
;;; (A)  rr-interval-seq-has-convergent-subseq  (the textbook form)
;;;
;;;        lo, hi in RR,  h in FUN(NN, CCINT(lo, hi))
;;;          =>  forsome ph. STRICTLY-MONO-NN(ph)
;;;                and forsome pt in RR. CONVERGES-TO(RR-MS, SUBSEQ(h, ph), pt)
;;;
;;;      -- state it with the CODOMAIN hypothesis, not with abs: the abs form
;;;      (|h i| <= bd, which is what `bounded-block-converges' below wants) is
;;;      one `rr-abs-bound' instantiation away, and stating it this way keeps
;;;      the unary minus out of the statement.
;;;
;;;      ROUTE, each step a citation that exists:
;;;        rad  <- null-rr-seq-exists + the NULL-RR-SEQ unfold
;;;                (rad in FUN(NN,RR), POS-RR(rad k), and the threshold clause)
;;;        cov  <- ccint-grid-cover-seq (lo, hi, rad)        [THIS FILE]
;;;        V    := CCINT(lo, hi);  (IN V SET) as r9e-ccint-set! does it
;;;        blk  <- block-family-combinatorial(V, h, cov)     (load.scm:1384)
;;;        ph   <- diagonalization(blk)                      -- strictly
;;;                monotone with ph(j) in blk(k) for every k <= j
;;;        the Cauchy estimate: given eps > 0, the threshold clause of
;;;                NULL-RR-SEQ gives N0 with rad(k) <= eps for k >= N0; for
;;;                m, p >= N0 the diagonal puts ph(m), ph(p) in blk(N0), the
;;;                capture clause puts h(ph m), h(ph p) in ONE member U of
;;;                cov(N0), and the diameter clause of cov(N0) bounds
;;;                |h(ph m) - h(ph p)| by rad(N0) <= eps (rr-leq-transitive).
;;;                NO HALVING is needed -- unlike the metric route, where two
;;;                points of one r-ball are 2r apart, two points of one CELL
;;;                are eps apart.
;;;        the value equation SUBSEQ(h, ph)(k) = h(ph k) at a TYPED k is
;;;                `subseq-apply' (never `mac SUBSEQ' under the binder);
;;;        the typing (IN (SUBSEQ h ph) (FUN NN RR)) is `mac SUBSEQ' +
;;;                dk-lam-t! + fun-apply-type-c twice (rake-ascoli.scm's
;;;                r9b-e-typing! is the four-line model), h being carried from
;;;                FUN(NN, V) to FUN(NN, RR) by fun-codomain-subset +
;;;                ccint-subset-rr;
;;;        then `rr-cauchy-converges' -- which takes the ABS form of Cauchy
;;;                directly, so no metric vocabulary enters -- gives
;;;                CONVERGES(RR-MS, SUBSEQ(h, ph)); `mac-h CONVERGES' and
;;;                dk-skolem! produce the limit, and its typing comes from
;;;                (IN pt (PTS RR-MS)) by `slot-h PTS' IN A have! LANE
;;;                (cauchy-criterion-right.scm:283 is the precedent; firing the
;;;                rr-ms@pts macete by name is what accessor-callsite-audit
;;;                forbids).
;;;
;;; (B)  bounded-block-converges, the statement 8-B asked for, verbatim from
;;;      theorem-library/rake-ascoli.scm's closing block:
;;;
;;;        h in FUN(NN, RR),  (forall i in NN. abs(h i) <= bd),
;;;        J in INF-SUBSETS(NN)
;;;          =>  forsome b_. b_ in INF-SUBSETS(NN) and SUBSET(b_, J)
;;;                and forsome p in RR. CONVERGES-ALONG(RR-MS, h, b_, p)
;;;
;;;      is (A) plus the TRANSPORT ALONG A BLOCK, which is part A of
;;;      theorem-library/rake-block-tower.scm (block-step-converges, :143-:339)
;;;      with "bounded real sequence" in place of "sequence in a SEQ-COMPACT
;;;      space": enumerate J by e := NN-ENUM(J) (nn-enum-spec), apply (A) to
;;;      g := i |-> h(e i), put psi := v |-> e(ph v), take b_ to be the image
;;;      of psi (strictly-mono-image-infinite) and lift the estimate with
;;;      strictly-mono-le-reflect.  That driver is ~120 lines and is COPIED,
;;;      not re-invented -- only the SEQ-COMPACT citation changes.
;;;      The hypothesis abs(h i) <= bd feeds (A) through rr-abs-bound (which
;;;      hands back -bd <= h i and h i <= bd) and ccint-membership, at
;;;      lo := 0 - bd, hi := bd.
;;;
;;; (C)  ascoli-pointwise-diagonal -- the antecedent that
;;;      `ascoli-sequential-from-diagonal' (rake-ascoli.scm) still takes as a
;;;      hypothesis -- is then the RR copy of rake-block-tower.scm PART B:
;;;      dc-on-nn-pred over INF-SUBSETS(NN) with (B) as the totality of the
;;;      step, the index shift S := n |-> f(succ n), the limit read off by
;;;      CHOICE, and finally the diagonalization + coord-block-estimate of
;;;      rake-diagonal-subseq.scm L1.  It needs POINTWISE-BOUNDED (the
;;;      hypothesis of Ascoli that nothing else uses) to supply the bound bd at
;;;      each point of the dense sequence, and it needs NO metric subspace
;;;      structure anywhere -- which was the point of taking this route.
;;;      LOAD ORDER: (C) does NOT have to precede rake-ascoli (load.scm:2390).
;;;      `ascoli-sequential-from-diagonal' takes the diagonal as an ANTECEDENT,
;;;      so the final `ascoli-arzela-sequential' is a THIRD file, wired after
;;;      both, and the whole chain may sit at the end of load.scm.
;;; =====================================================================
