;;; series-cauchy-proof.scm -- THE CAUCHY CRITERION FOR REAL SERIES, PROVEN.
;;;
;;;   series-cauchy-criterion:
;;;     f in FUN(NN,RR),  SERIES-CONVERGES(f),  eps > 0
;;;       =>  forsome bnd in NN.  |S(n_) - S(m)| <= eps   whenever bnd <= m <= n_
;;;
;;; It was an asserted `well-known' support in
;;; theorem-library/series-order-lemmas.scm -- the LAST live entry of that file,
;;; and the one genuinely ANALYTIC asserted leaf of
;;; theorem-library/dominated-convergence.scm, whose own header named it as "the
;;; obvious next target: everything else it would need is now in this file".
;;; The statement here is BYTE-IDENTICAL to the retired support (checked: the
;;; install of this proof under the old name reports "re-installing the same
;;; statement", not the "DIFFERENT statement" warning).
;;;
;;; ------------------------------------------------------------------
;;; THE ARGUMENT, and why it is short.  Convergence NAMES a limit; the two
;;; partial sums are each within eps/2 of it; subtract.  Concretely:
;;;
;;;   SERIES-CONVERGES(f) unfolds to CONVERGES(RR-MS, k |-> S(f,k)), i.e. an
;;;   existential -- skolemize it to get L and the eps-N estimate.
;;;   `rr-pos-halvable' splits eps into d + d with d > 0; the estimate at d
;;;   gives a threshold N.  For bnd := N and N <= m <= n_ the estimate applies
;;;   at BOTH indices, and
;;;       S(n_) - S(m)  =  (S(n_) - L) - (S(m) - L)
;;;   is bounded by |S(n_) - L| + |S(m) - L| <= d + d = eps.
;;;
;;; NO TRIANGLE INEQUALITY is cited, and that is the one technique worth
;;; recording.  `rr-abs-bound' turns the GOAL's absolute value into a pair of
;;; LINEAR bounds (mac on the goal) and `rr-le-abs' / `rr-neg-abs-le' turn each
;;; HYPOTHESIS's absolute value into a pair of linear bounds with the abs term
;;; left standing as an ATOM the oracle can certify (rr-abs-closed).  Everything
;;; in sight is then linear in {S(n_), S(m), L, |S(n_)-L|, |S(m)-L|, d, eps} and
;;; `ineq' decides both halves by Farkas.  This is rr-abs-sum-bound's technique
;;; (rr-abs-basics.scm) rather than rr-limit-unique's, and it is why the whole
;;; endgame is one `mac' and two `ineq's.
;;;
;;; THE eps/2 QUESTION, since `ineq' now folds a constant denominator (so that
;;; e*recip(2) is the rational coefficient 1/2 rather than an opaque atom).
;;; That folding does NOT shorten this proof, and the reason is worth stating:
;;; the cost of the direct route is not the final inequality -- which `ineq'
;;; closes either way -- but manufacturing POS-RR(eps * recip(1+1)) in order to
;;; instantiate the convergence hypothesis at it.  That derivation (nonzero,
;;; reciprocal closed, reciprocal positive, product positive) is fifteen lines
;;; and is EXACTLY the content of `rr-pos-halvable'
;;; (theorem-library/rr-halving.scm), which is PROVEN `modulo 0' and so costs
;;; nothing to cite.  Two lines against fifteen, same bill.
;;;
;;; ------------------------------------------------------------------
;;; WHERE IT LOADS, and why not lower.  dominated-convergence.scm CITES this
;;; name (in `series-tail-small', at its line 668) so the proof has to precede
;;; it, and it does: the route skolemizes the limit straight out of
;;; SERIES-CONVERGES and never touches `series-limit-converges-to' or
;;; `rr-limit-unique' (both of which live in dominated-convergence.scm, BELOW
;;; that citation anyway).  What it does need all loads far above:
;;; comparison-test-proof just above (series-partial-sum-in-rr,
;;; series-partial-sum-seq-apply), rr-abs-basics (rr-abs-bound, rr-le-abs,
;;; rr-neg-abs-le, rr-abs-closed), rr-halving (rr-pos-halvable), rr-ms-dist,
;;; binary-minus-laws (rr-sub-in-rr), nn-order-basics/order-lemmas (nn-in-rr),
;;; metric-completeness (CONVERGES / CONVERGES-TO), power-series
;;; (SERIES-CONVERGES) and driver-kit.

;;; ---- file-local driver helpers (the `scc-' prefix) -------------------

(define (scc-fvs forms) (apply append (map free-vars forms)))

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (scc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "scc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; Skolemize a FORSOME already in the CONTEXT (`obtain' sees only what its own
;;; lane landed); the eigenvariable is read off by free-variable set difference.
(define (scc-skolem! ex)
  (let* ((fv0 (scc-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (scc-fvs (dk-asms)))))
      (if (null? fresh) (error "scc-skolem!: nothing appeared" ex) (car fresh)))))

;;; `ineq' wants 1-based assumption indices, and premises are named ONE BY ONE.
(define (scc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "scc-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (scc-ineq . forms) (apply ineq (map scc-idx forms)))

;;; Close an AND goal conjunct by conjunct.
(define (scc-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (scc-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; (IN x RR) from (POS-RR x), on a SIDE branch: `mac-h' is destructive and the
;;; main branch still wants POS-RR intact.
(define (scc-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; =====================================================================
;;; The statement, reproduced VERBATIM from the retired support.
;;; =====================================================================

(define scc-stmt
  '(FORALL f (IMPLIES (IN f (FUN NN RR))
     (IMPLIES (SERIES-CONVERGES f)
       (FORALL eps (IMPLIES (POS-RR eps)
         (FORSOME bnd (AND (IN bnd NN)
           (FORALL m (IMPLIES (IN m NN) (FORALL n_ (IMPLIES (IN n_ NN)
             (IMPLIES (AND (<= bnd m) (<= m n_))
               (<= (abs (- (SERIES-PARTIAL-SUM f n_)
                           (SERIES-PARTIAL-SUM f m))) eps))))))))))))))

(sp (make-wff scc-stmt))
(dk-peel-to! 'FORSOME)
(define scc-f 'f)
(define scc-eps 'eps)

;;; SERIES-CONVERGES -> CONVERGES -> a named limit L, with its typing pulled
;;; through PTS(RR-MS) = RR.  `mac-h' REPLACES the assumption it unfolds, so the
;;; chain is read off each landing rather than reconstructed.
(define scc-conv
  (dk-landed-1 (lambda () (mac-h 'series-converges (list 'SERIES-CONVERGES scc-f)))))
(define scc-psq (caddr scc-conv))          ; VNB-LAMBDA k NN. SERIES-PARTIAL-SUM(f,k)
(define scc-ex  (dk-landed-1 (lambda () (mac-h 'converges scc-conv))))
(define scc-L   (scc-skolem! scc-ex))
(define scc-cvt (scc-find 'converges-to (dk-head? 'CONVERGES-TO)))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to scc-cvt))
                           (lambda (a) (eq? (car a) 'AND))))
(slot-h 'PTS (list 'IN scc-L '(PTS RR-MS)))

;;; The eps-universal of the limit, at the HALF of eps -- discriminated on
;;; POS-RR, which the tail universal below does not mention.
(define scc-epsu
  (scc-find 'eps-universal
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))
(define scc-hex (dk-fact! 'rr-pos-halvable scc-eps))
(define scc-d   (scc-skolem! scc-hex))     ; POS-RR(d) and d + d = eps
(define scc-tailex (dk-deepest (lambda () (inst+ scc-epsu scc-d))))
(define scc-N   (scc-skolem! scc-tailex))
;;; ... and the threshold estimate itself.  Both universals have head FORALL and
;;; both mention DIST; only the outer one mentions POS-RR.
(define scc-tailu
  (scc-find 'tail-universal
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'DIST)
                     (not (dk-contains? a 'POS-RR))))))

;;; =====================================================================
;;; bnd := N, and the block estimate.
;;; =====================================================================

(dk-ew-split! scc-N
  (lambda () (ass))                         ; N in NN
  (lambda ()
    (dk-peel-to! '<=)
    ;; Read the eigenvariables off the GOAL, never off the context: `dk-asms'
    ;; order is not the peel order.
    (let* ((g   (dk-goal))                  ; |S(f,n_) - S(f,m)| <= eps
           (dif (cadr (cadr g)))
           (Pn  (cadr dif))
           (Pm  (caddr dif))
           (nn_ (caddr Pn))
           (mm  (caddr Pm)))
      (dk-split! (list 'AND (list '<= scc-N mm) (list '<= mm nn_)))
      (fact 'nn-in-rr scc-N) (fact 'nn-in-rr mm) (fact 'nn-in-rr nn_)
      (have! (list '<= scc-N nn_)           ; N <= m <= n_
             (lambda () (scc-ineq (list '<= scc-N mm) (list '<= mm nn_))))
      ;; The threshold estimate at each index, walked down to the surface: the
      ;; partial-sum SEQUENCE applied (series-partial-sum-seq-apply), then the
      ;; RR-MS distance (rr-ms-dist -- a GUARDED macete, so both arguments are
      ;; typed BEFORE it fires), then the two-sided linear bounds on the abs.
      (for-each
       (lambda (i P)
         (dk-deepest (lambda () (inst+ scc-tailu i)))
         (mac-h 'series-partial-sum-seq-apply
                (list '<= (list '(DIST RR-MS) (list scc-psq i) scc-L) scc-d))
         (fact 'series-partial-sum-in-rr i scc-f)
         (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) P scc-L) scc-d))
         (fact 'rr-sub-in-rr P scc-L)
         (fact 'rr-abs-closed (list '- P scc-L))
         (fact 'rr-le-abs (list '- P scc-L))
         (fact 'rr-neg-abs-le (list '- P scc-L)))
       (list mm nn_) (list Pm Pn))
      ;; The goal's abs opens the same way, and Farkas finishes both halves.
      (fact 'rr-sub-in-rr Pn Pm)
      (scc-pos-in-rr! scc-eps)
      (scc-pos-in-rr! scc-d)
      (mac 'rr-abs-bound)
      (scc-and!
       (lambda ()
         (scc-ineq (list '<= (list 'abs (list '- Pn scc-L)) scc-d)
                   (list '<= (list 'abs (list '- Pm scc-L)) scc-d)
                   (list '<= (list '- Pn scc-L) (list 'abs (list '- Pn scc-L)))
                   (list '<= (list '- (list 'abs (list '- Pn scc-L))) (list '- Pn scc-L))
                   (list '<= (list '- Pm scc-L) (list 'abs (list '- Pm scc-L)))
                   (list '<= (list '- (list 'abs (list '- Pm scc-L))) (list '- Pm scc-L))
                   (list '= (list '+ scc-d scc-d) scc-eps)))))))

(qed 'series-cauchy-criterion)
(topic! 'series-cauchy-criterion 'analysis)
(alias! 'series-cauchy-criterion
        "the Cauchy criterion for real series"
        "a convergent series has vanishing blocks")
