;;; rake-dc-consumers.scm -- the consumers of recursive choice (rake batch 8-C).
;;;
;;; cauchy-rapid-subsequence, stated LITERALLY
;;; (structure-library/metric-completeness.scm:117):
;;;
;;;   f Cauchy in s, rad : NN -> RR pointwise positive
;;;     =>  there is phi : NN -> NN, strictly increasing, with
;;;         d(f(phi k), f(phi(succ k))) <= rad(k)  for every k.
;;;
;;; THE ROUTE -- dc-on-nn-pred (rake-dc-on-nn.scm) over NN, the step set being
;;; "a later index whose TAIL is already rad(succ k)-small".  Write
;;;
;;;   TAIL(j, m)  ==  forall p,q in NN.  m <= p and m <= q  =>  d(f p, f q) <= rad j
;;;
;;; -- SPELLED WITH THE BINDERS `m' AND `n_', which is how IS-CAUCHY-SEQ's own
;;; definition spells them, so that the formula skolemized out of the Cauchy
;;; hypothesis at eps := rad(j) IS TAIL(j, N) literally, with no alpha step.
;;; Then
;;;
;;;   tail-witness   forall j in NN. forsome N in NN. TAIL(j, N)      [Cauchy at rad j]
;;;   a              a witness for j = 0
;;;   nxt(k, u)      = { v in NN : u < v and TAIL(succ k, v) }
;;;
;;; and the totality of nxt is: take N with TAIL(succ k, N) and set
;;; v := N + succ(u) -- above N (nn-le-add-right, so TAIL transports by
;;; nn-le-trans-guarded) and above u (nn-le-add-left plus bt-lt-succ and
;;; rr-lt-le-trans).  No MAX, no case split.
;;;
;;; dc-on-nn-pred at (NN, a, nxt) gives FF : NN -> NN with FF(0) = a and
;;; FF(succ k) in nxt(k, FF k), i.e. FF(k) < FF(succ k) and TAIL(succ k, FF(succ k)).
;;; Two consequences close the three conjuncts of the goal:
;;;
;;;   * strict monotonicity: nn-step-mono-ptwise (rake-subseq-leaves.scm) turns
;;;     the consecutive increase into m < n => FF(m) < FF(n).  The support wants
;;;     that explicit form, not STRICTLY-MONO-NN, so the POINTWISE lemma is the
;;;     one to cite (nn-step-strictly-mono would have to be unfolded again).
;;;   * the INVARIANT  forall k in NN. TAIL(k, FF k), by `ni': the base is
;;;     TAIL(0, a) transported along FF(0) = a, and the step is the stage
;;;     property at k -- the induction hypothesis is not used (the recursion
;;;     already carries the invariant one stage at a time).
;;;     With FF(k) <= FF(k) and FF(k) <= FF(succ k) the invariant at k gives
;;;     d(f(FF k), f(FF(succ k))) <= rad(k), which is the last conjunct.
;;;
;;; The metric enters ONLY as an opaque term: no triangle inequality, no
;;; symmetry, no IS-METRIC-SPACE conjunct is ever used.  The proof would read
;;; the same for any two-place term in place of DIST(s).
;;;
;;; STATEMENT CHECK (the species of CLAUDE.md "Writing proof drivers"): clean.
;;; `s' is unguarded but IS-CAUCHY-SEQ(s,f) carries IS-METRIC-SPACE(s) and the
;;; typing of f; rad is FUN-typed and pointwise positive; every index is
;;; NN-typed; the conclusion has no strict `=' and no CHOICE.  It re-installs
;;; as the same statement.
;;;
;;; CITATIONS and their files (load.scm line numbers, 2026-09-19):
;;;   nn-step-mono-ptwise                theorem-library/rake-subseq-leaves   1342
;;;   dc-on-nn-pred                      theorem-library/rake-dc-on-nn         646
;;;   rr-lt-le-trans, rr-lt-implies-le   theorem-library/rr-order-basics
;;;   nn-le-trans-guarded, nn-le-add-left, nn-le-add-right, nn-le-refl,
;;;     nn-in-rr, bt-lt-succ             the NN order block
;;;   fun-apply-type-c                   theorem-library/fun-apply-type-proof
;;;   nn-add-closed, nn-zero-in, nn-succ-closed, nn-is-set   number-systems (primitive)
;;;   IS-CAUCHY-SEQ (the definition)     structure-library/metric-completeness
;;;
;;; LOAD WINDOW: lo = theorem-library/rake-subseq-leaves (the MAXIMUM over the
;;; citations), hi = none -- nothing in the tree cites cauchy-rapid-subsequence
;;; in a proof (only comments do).  The natural slot is immediately after
;;; theorem-library/rake-subseq-leaves.
;;;
;;; No late tactic: `fact', `di', `ni', `lam-b', `lam-b-h', `sep-me', `sep-mi',
;;; `subst' and the dk- kit only.  (`contra', `prep' and `ineq-supply' are not
;;; used; `ineq' is not used either -- every order step is a citation.)
;;;
;;; Helper prefix: r9c-.

;;; ---- file-local driver helpers ----------------------------------------

(define (r9c-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-dc-consumers: ") (display name)
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
        (error "rake-dc-consumers: unfinished" name))))

(define (r9c-head? fm h) (and (pair? fm) (eq? (car fm) h)))

;; run THUNK (a branching tactic) and visit each opened leaf with VISIT.
(define (r9c-each-leaf! thunk visit)
  (for-each (lambda (leaf) (dk-focus! leaf) (visit)) (dk-opened thunk)))

;; goal (IN t (SEP x DOM p)): `sep-mi' and run BODY on the property leaf.  NOT
;; `in-sep!': the domain half is in the context here, so sep-mi grounds it on
;; the spot and only ONE leaf comes back (in-sep! demands both and errors).
(define (r9c-in-sep! dom body)
  (r9c-each-leaf!
   (lambda () (sep-mi))
   (lambda ()
     (let ((g (dk-goal)))
       (if (and (r9c-head? g 'IN) (equal? (caddr g) dom)) (ass) (body))))))

;;; ---- the statement, copied literally ----------------------------------

(sp (make-wff
  '(FORALL s (FORALL f (FORALL rad
     (IMPLIES (AND (IS-CAUCHY-SEQ s f)
              (AND (IN rad (FUN NN RR))
                   (FORALL k (IMPLIES (IN k NN) (POS-RR (rad k))))))
       (FORSOME phi
         (AND (IN phi (FUN NN NN))
         (AND (FORALL m (IMPLIES (IN m NN)
                (FORALL n_ (IMPLIES (IN n_ NN)
                  (IMPLIES (< m n_) (< (phi m) (phi n_)))))))
              (FORALL k (IMPLIES (IN k NN)
                (<= ((DIST s) (f (phi k)) (f (phi (succ k)))) (rad k)))))))))))))

(define r9c-top (dk-peel!))
(dk-split-all! r9c-top)

(define r9c-cauchy
  (dk-pick (lambda (fm) (r9c-head? fm 'IS-CAUCHY-SEQ)) "the Cauchy hypothesis"))
(define r9c-s (cadr r9c-cauchy))
(define r9c-f (caddr r9c-cauchy))
(define r9c-rad
  (cadr (dk-pick (lambda (fm) (and (r9c-head? fm 'IN) (equal? (caddr fm) '(FUN NN RR))))
                 "the typing of rad")))
(define r9c-pos
  (dk-pick (lambda (fm) (and (r9c-head? fm 'FORALL) (dk-contains? fm 'POS-RR)))
           "the pointwise positivity of rad"))

(define (r9c-d a b) (list (list 'DIST r9c-s) a b))

;; TAIL(j, m): every pair of indices at or beyond m is rad(j)-close.  The
;; binders are IS-CAUCHY-SEQ's own (`m' and `n_'), so the formula skolemized
;; out of the Cauchy hypothesis at eps := rad(j) is this formula literally.
(define (r9c-tail jt mt)
  (list 'FORALL 'm
    (list 'IMPLIES '(IN m NN)
      (list 'FORALL 'n_
        (list 'IMPLIES '(IN n_ NN)
          (list 'IMPLIES (list 'AND (list '<= mt 'm) (list '<= mt 'n_))
                (list '<= (r9c-d (list r9c-f 'm) (list r9c-f 'n_))
                      (list r9c-rad jt))))))))

;;; ---- the Cauchy hypothesis, unfolded ----------------------------------

(dk-split-all! (dk-landed (lambda () (mac-h 'is-cauchy-seq r9c-cauchy))))
(dk-split-all!)

(define r9c-cau
  (dk-pick (lambda (fm) (and (r9c-head? fm 'FORALL) (dk-contains? fm 'POS-RR)
                             (dk-contains? fm 'DIST)))
           "the Cauchy universal"))

;;; ---- tail-witness: for every level there is a tail index --------------

(define r9c-tw
  (list 'FORALL 'jj_
    (list 'IMPLIES '(IN jj_ NN)
      (list 'FORSOME 'nv_
        (list 'AND '(IN nv_ NN) (r9c-tail 'jj_ 'nv_))))))

(have! r9c-tw
  (lambda ()
    (let ((jv (dk-di-var!)))
      (dk-apply! r9c-pos jv)                       ; POS-RR (rad j)
      (let* ((ex (dk-apply! r9c-cau (list r9c-rad jv)))
             (nv (dk-skolem! ex)))
        (witness! nv (lambda () (dk-conj-close!)))))))

;;; ---- the base point ---------------------------------------------------

(fact 'nn-zero-in)
(define r9c-a (dk-skolem! (dk-apply! r9c-tw 0)))

;;; ---- the step set and its totality ------------------------------------

(define r9c-nxt
  (list 'VNB-LAMBDA '(LIST kk_ uu_) '(CARTESIAN NN NN)
        (list 'SEP 'vv_ 'NN
              (list 'AND '(< uu_ vv_) (r9c-tail '(succ kk_) 'vv_)))))

;; the antecedent of dc-on-nn-pred, binders SPELLED AS THERE (k, u, y) so the
;; instance IS the support's own hypothesis and `fact' detaches it.
(define r9c-tot
  (list 'FORALL 'k
    (list 'IMPLIES '(IN k NN)
      (list 'FORALL 'u
        (list 'IMPLIES '(IN u NN)
          (list 'FORSOME 'y
            (list 'AND '(IN y NN) (list 'IN 'y (list r9c-nxt 'k 'u)))))))))

(have! r9c-tot
  (lambda ()
    (dk-peel!)
    ;; read the stage and the state off the GOAL -- both landed typings are
    ;; (IN _ NN) and nothing but the goal tells them apart.
    (let* ((app (caddr (caddr (caddr (dk-goal)))))   ; (LAM k u)
           (kv  (cadr app))
           (uv  (caddr app)))
      (lam-b)                                       ; k and u are typed: the redex fires
      (fact 'nn-succ-closed kv)
      (let* ((ex (dk-apply! r9c-tw (list 'succ kv)))
             (nv (dk-skolem! ex))                   ; (IN nv NN), TAIL(succ k, nv)
             (su (list 'succ uv))
             (wv (list '+ nv su))
             (tl (dk-pick (lambda (fm) (and (r9c-head? fm 'FORALL) (dk-contains? fm nv)
                                            (dk-contains? fm 'DIST)))
                          "the tail property at nv")))
        (fact 'nn-succ-closed uv)
        (have! (list 'AND (list 'IN nv 'NN) (list 'IN su 'NN)))
        (fact 'nn-add-closed nv su)                 ; (IN (+ nv (succ u)) NN)
        (fact 'nn-le-add-right su nv)               ; (<= nv (+ nv (succ u)))
        (fact 'nn-le-add-left nv su)                ; (<= (succ u) (+ nv (succ u)))
        (fact 'bt-lt-succ uv)                       ; (< u (succ u))
        (fact 'nn-in-rr uv)
        (fact 'nn-in-rr su)
        (fact 'nn-in-rr wv)
        (have! (list 'AND (list '< uv su) (list '<= su wv)))
        (fact 'rr-lt-le-trans uv su wv)             ; (< u (+ nv (succ u)))
        ;; TAIL(succ k, nv) transports up to wv
        (have! (r9c-tail (list 'succ kv) wv)
          (lambda ()
            (let* ((landed (dk-peel!))
                   (g   (dk-goal))
                   (mv  (cadr (cadr (cadr g))))
                   (n2  (cadr (caddr (cadr g)))))
              (dk-split-all! landed)            ; the two halves of the bound at wv
              (fact 'nn-le-trans-guarded nv wv mv)
              (fact 'nn-le-trans-guarded nv wv n2)
              (have! (list 'AND (list '<= nv mv) (list '<= nv n2)))
              (dk-apply! tl mv n2)
              (ass))))
        (witness! wv
          (lambda ()
            (dk-conj-close!
             (lambda ()
               (if (equal? (caddr (dk-goal)) 'NN)
                   (ass)
                   (r9c-in-sep! 'NN (lambda () (dk-conj-close!))))))))))))

;;; ---- the recursion ----------------------------------------------------

(fact 'nn-is-set)
(define r9c-ff (dk-skolem! (dk-fact! 'dc-on-nn-pred 'NN r9c-a r9c-nxt)))
(define r9c-zero-eq
  (dk-pick (lambda (fm) (and (r9c-head? fm '=) (dk-contains? fm r9c-ff)))
           "the base equation FF(0) = a"))
(define r9c-stage
  (dk-pick (lambda (fm) (and (r9c-head? fm 'FORALL) (dk-contains? fm r9c-ff)))
           "the per-stage step property"))

;; At a TYPED index KV: land (IN (FF (succ k)) NN), (< (FF k) (FF (succ k)))
;; and TAIL(succ k, FF(succ k)).  Returns the list of the two split conjuncts.
(define (r9c-stage-at! kv)
  (fact 'fun-apply-type-c r9c-ff 'NN 'NN kv)          ; TYPE BEFORE YOU BETA
  (let* ((h  (dk-apply! r9c-stage kv))
         (sm (car (dk-landed (lambda () (lam-b-h h)))))
         (ld (dk-landed (lambda () (sep-me sm))))
         (cj (or (any-pred (lambda (fm) (r9c-head? fm 'AND)) ld)
                 (error "r9c-stage-at!: sep-me landed no conjunction"))))
    (dk-split! cj)))

;;; ---- the two universals nn-step-mono-ptwise asks for -------------------

(define r9c-typ
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list 'IN (list r9c-ff 'k_) 'NN))))
(define r9c-stepu
  (list 'FORALL 'k_
        (list 'IMPLIES '(IN k_ NN)
              (list '< (list r9c-ff 'k_) (list r9c-ff '(succ k_))))))

(have! r9c-typ
  (lambda ()
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c r9c-ff 'NN 'NN kv)
      (ass))))

(have! r9c-stepu
  (lambda ()
    (let ((kv (dk-di-var!)))
      (r9c-stage-at! kv)
      (ass))))

;;; ---- the invariant: TAIL(k, FF k) at every stage -----------------------

(define r9c-inv
  (list 'FORALL 'jj_
        (list 'IMPLIES '(IN jj_ NN) (r9c-tail 'jj_ (list r9c-ff 'jj_)))))

(have! r9c-inv
  (lambda ()
    (r9c-each-leaf!
     (lambda () (ni))
     (lambda ()
       (if (dk-contains? (dk-goal) 'succ)
           ;; STEP.  dk-peel! goes all the way into TAIL's body: it lands
           ;; (IN jj NN), the induction hypothesis (unused), (IN m NN),
           ;; (IN n_ NN) and the conjunctive bound, leaving the `<=' atom.
           (let* ((landed (dk-peel!))
                  (g   (dk-goal))
                  (jv  (cadr (cadr (caddr g))))     ; from (rad (succ jj))
                  (mv  (cadr (cadr (cadr g))))
                  (n2  (cadr (caddr (cadr g))))
                  (parts (r9c-stage-at! jv))
                  (tl  (or (any-pred (lambda (fm) (r9c-head? fm 'FORALL)) parts)
                           (error "r9c-inv: the stage landed no tail property"))))
             (dk-apply! tl mv n2)
             (ass))
           ;; BASE: TAIL(0, FF 0), and FF(0) = a with TAIL(0, a) in context.
           (begin
             (subst r9c-zero-eq)
             (ass)))))))

;;; ---- the witness ------------------------------------------------------

(witness! r9c-ff
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (let ((g0 (dk-goal)))
         (if (r9c-head? g0 'IN)
             (ass)
             (begin
               (dk-peel!)
               (let ((g (dk-goal)))
                 (if (r9c-head? g '<)
                     ;; strict monotonicity, from the consecutive increase
                     (let ((mv (cadr (cadr g)))
                           (n2 (cadr (caddr g))))
                       (fact 'nn-step-mono-ptwise n2 r9c-ff mv)
                       (ass))
                     ;; the distance bound at a typed stage
                     (let* ((kv (cadr (caddr g)))
                            (sk (list 'succ kv))
                            (fk (list r9c-ff kv))
                            (fs (list r9c-ff sk)))
                       (fact 'fun-apply-type-c r9c-ff 'NN 'NN kv)
                       (fact 'nn-succ-closed kv)
                       (fact 'fun-apply-type-c r9c-ff 'NN 'NN sk)
                       (dk-apply! r9c-stepu kv)          ; (< (FF k) (FF (succ k)))
                       (fact 'nn-in-rr fk)
                       (fact 'nn-in-rr fs)
                       (fact 'rr-lt-implies-le fk fs)    ; (<= (FF k) (FF (succ k)))
                       (fact 'nn-le-refl fk)
                       (have! (list 'AND (list '<= fk fk) (list '<= fk fs)))
                       (let ((tl (dk-apply! r9c-inv kv)))
                         (dk-apply! tl fk fs)
                         (ass))))))))))))

(r9c-qed! 'cauchy-rapid-subsequence)
(topic! 'cauchy-rapid-subsequence 'analysis)
