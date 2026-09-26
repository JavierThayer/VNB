;;; theorem-library/rake-block-tower.scm
;;; ====================================================================
;;; convergence-block-tower (theorem-library/seq-compact-product.scm:91) --
;;; the refinement-tower core of the cross-coordinate diagonal argument, and
;;; the SOLE remaining leaf of coordinatewise-diagonal-subseq,
;;; seq-compact-countable-product, compact-countable-product and the Ascoli
;;; route.  Three theorems, in dependency order:
;;;
;;;   subseq-value-at         SUBSEQ(f,phi)(k) = f(phi(k)) at a TYPED k
;;;   block-step-converges    ONE refinement step (the totality of the choice)
;;;   convergence-block-tower THE SUPPORT
;;;
;;; THE ROUTE.  The warrant describes a dependent choice over the coordinate
;;; index, and that is what is done here, with the step made citable first.
;;; `block-step-converges' says: in a sequentially compact space, a sequence
;;; indexed by an infinite block J of NN converges along some infinite
;;; sub-block of J.  That is exactly the TOTALITY hypothesis of dc-on-nn-pred
;;; (rake-dc-on-nn.scm, PROVEN) at the carrier INF-SUBSETS(NN) and the step set
;;;
;;;   nxt(k, u) = { b in INF-SUBSETS(NN) : b subset u and coordinate k of seq
;;;                 converges along b to some point of PTS(ms k) },
;;;
;;; so the whole combinatorial content is ONE citation, and the tower the
;;; support asks for is the INDEX SHIFT  S := n |-> f(succ n)  of the chosen
;;; f (the move of theorem-library/block-family-combinatorial-proof): S(n) is a
;;; member of nxt(n, f n), hence nested under S(k) and carrying the
;;; coordinate-n convergence at once.
;;;
;;; THE LIMIT POINT L NEEDS NO SECOND DEPENDENT CHOICE.  The n-th choice does
;;; not depend on the earlier ones, so L is a VNB-LAMBDA whose BODY is a CHOICE
;;; over the set of coordinate-n limits along S(n); that set is inhabited by
;;; the rung's own existential, so `choose!' discharges the one obligation
;;; CHOICE owes.  L is put in PRODUCT-CARRIER by the functoid unfold plus
;;; `bu-mi' at the index -- no sethood of the big union is ever wanted.
;;;
;;; DEFINEDNESS (the LUTINS rule).  Nothing is instantiated at (ms n), at
;;; NN-ENUM(J) or at a CHOICE before it is typed: the factorwise
;;; IS-METRIC-SPACE (r8l-t-HMS), the coordinate typing (r8l-t-HCOORD) and
;;; nn-enum-spec's own FUN typing are landed FIRST, each in its own `have!'
;;; lane where that is destructive.  The statements of `block-step-converges'
;;; and of the two rung lemmas are therefore stated with the value, not with
;;; the applied lambda, wherever a later citation has to match a beta-reduced
;;; goal (r8l-t-Lbody, r8l-t-Sbody).
;;;
;;; LOAD WINDOW [454, 465).
;;;   lo = 454: the latest citation is `product-carrier-coord', proven in
;;;   theorem-library/product-summable (453).  The others: fun-codomain-subset
;;;   (subsequence-principle, 340), nn-enum-spec / strictly-mono-image-infinite
;;;   / strictly-mono-le-reflect (theorem-library/rake-nn-enum, THIS BATCH --
;;;   it must be wired BELOW this file), nn-in-inf-subsets (nn-infinite, 278),
;;;   rake-dc-on-nn (161, dc-on-nn-pred), fun-apply-type-c
;;;   (fun-apply-type-proof, 160), inf-subsets-is-set (154), the definitions
;;;   SEQ-COMPACT / CONVERGES-ALONG (seq-compact-product, 130),
;;;   PRODUCT-CARRIER (structure-library/product-metric, 128), SUBSEQ /
;;;   STRICTLY-MONO-NN (cauchy-subsequence, 90), INF-SUBSETS (85),
;;;   number-systems (34), choice-axiom (theory, 11).
;;;   hi = 465: theorem-library/rake-diagonal-subseq, the only file citing
;;;   convergence-block-tower in a proof.  Position 455, immediately after
;;;   theorem-library/product-is-metric-space (454), is free and works.
;;;   NOT EMPTY, so no splice is needed.
;;;
;;; Helper prefix: r8l-.
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r8l-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-block-tower: ") (display name)
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
        (error "rake-block-tower: unfinished" name))))

;; `lam-b' to a fixpoint.  A fixed-count call leaves an inert step when nothing
;; is left to reduce (CLAUDE.md: loop on a redex test, not on a count).
(define (r8l-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (car (car e)) 'VNB-LAMBDA)) #t)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((r8l-redex? (car l)) #t)
                    (#t (loop (cdr l))))))))

(define (r8l-beta!)
  (let loop ((i 0))
    (if (and (< i 6) (r8l-redex? (dk-goal)))
        (begin (lam-b) (loop (+ i 1))))))

;; The conjunct list of a def-predicate hypothesis, unfolded DESTRUCTIVELY on
;; the current branch (the predicate itself is not wanted again).
(define (r8l-unfold! name form)
  (dk-landed (lambda () (mac-h name form)))
  (dk-split-all!))

;; The FUN NN NN typing carried by STRICTLY-MONO-NN, landed without consuming
;; the predicate.
(define (r8l-fun-typing! ps)
  (have! (list 'IN ps '(FUN NN NN))
    (lambda ()
      (mac-h 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN ps))
      (dk-split-all!)
      (ass))))

;;; =====================================================================
;;; L0.  subseq-value-at -- the VALUE of a subsequence at one TYPED index.
;;;
;;; `mac SUBSEQ' inside a goal unfolds the functoid to (VNB-LAMBDA k NN
;;; (f (phi k))) and `lam-b' then reduces the redex UNDER that binder as well,
;;; owing the unprovable side leaf (IN (phi k) NN) in the outer context where k
;;; is free (measured here on 2026-09-19; the same trap 7-I hit).  Rewriting by
;;; this equation instead touches only the application at the peeled index.
;;;
;;; NOTE FOR THE INTEGRATOR.  This is, verbatim, `subseq-apply' of
;;; theorem-library/rake-diagonal-subseq.scm:104 -- which loads at position 465,
;;; i.e. AFTER this file must sit (it is the file that cites
;;; convergence-block-tower).  If `subseq-apply' is moved to a file below 454,
;;; delete this lemma and cite it.
;;; =====================================================================

(sp (make-wff
  '(FORALL f
     (FORALL phi
       (FORALL k_
         (IMPLIES (IN k_ NN)
           (== ((SUBSEQ f phi) k_) (f (phi k_)))))))))
(dk-peel!)
(mac 'SUBSEQ)
(lam-b)
(qrfl)
(r8l-qed! 'subseq-value-at)
(topic! 'subseq-value-at 'analysis)
(gloss! 'subseq-value-at
  "The reindexed sequence SUBSEQ(f, phi) takes at the natural index k the value
   f(phi(k)).")

;;; =====================================================================
;;; A.  block-step-converges -- ONE refinement step.
;;;
;;;   s sequentially compact, h : NN -> PTS(s), J an infinite index block
;;;   ==> some infinite J_ subset J along which h converges.
;;;
;;; Enumerate J by e := NN-ENUM(J) (nn-enum-spec, rake-nn-enum.scm), apply
;;; SEQ-COMPACT to the composite  g := i |-> h(e i)  to get a strictly monotone
;;; phi and a limit L, put  psi := v |-> e(phi v)  -- strictly monotone with all
;;; its values in J -- and take J_ to be the set of values of psi inside J.
;;; J_ is infinite by strictly-mono-image-infinite; and an index i of J_ past
;;; psi(N) is psi(k) for a k past N (strictly-mono-le-reflect), where
;;; h(i) = h(e(phi k)) = SUBSEQ(g,phi)(k) is already within eps of L.
;;; =====================================================================

(sp (make-wff
  '(FORALL s
     (IMPLIES (SEQ-COMPACT s)
       (FORALL h
         (IMPLIES (IN h (FUN NN (PTS s)))
           (FORALL J
             (IMPLIES (IN J (INF-SUBSETS NN))
               (FORSOME b_
                 (AND (IN b_ (INF-SUBSETS NN))
                 (AND (SUBSET b_ J)
                      (FORSOME p
                        (AND (IN p (PTS s))
                             (CONVERGES-ALONG s h b_ p))))))))))))))

(define r8l-a-landed (dk-peel!))

(define r8l-a-s (cadr (dk-pick (dk-head? 'SEQ-COMPACT) "the sequentially compact factor")))
(define r8l-a-h
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (equal? (caddr f) (list 'FUN 'NN (list 'PTS r8l-a-s)))))
                 "the sequence h")))
(define r8l-a-J
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (equal? (caddr f) '(INF-SUBSETS NN))))
                 "the index block J")))

;; ---- the enumeration of J -------------------------------------------
(define r8l-a-e (list 'NN-ENUM r8l-a-J))

(define r8l-a-e-atoms
  (dk-split-all! (dk-landed (lambda () (fact 'nn-enum-spec r8l-a-J)))))
(define r8l-a-emono
  (or (any-pred (dk-head? 'FORALL) r8l-a-e-atoms)
      (error "block-step: nn-enum-spec landed no monotonicity clause")))

(have! (list 'SUBSET r8l-a-J 'NN)
  (lambda ()
    (mac-h 'inf-subsets-membership (list 'IN r8l-a-J '(INF-SUBSETS NN)))
    (dk-split-all!)
    (ass)))

(fact 'fun-codomain-subset r8l-a-e 'NN r8l-a-J 'NN)      ; e : NN -> NN
(have! (list 'STRICTLY-MONO-NN r8l-a-e)
  (lambda () (mac 'STRICTLY-MONO-NN) (from-context!)))

;; ---- the composite sequence g = i |-> h(e i) --------------------------
(define r8l-a-g (list 'VNB-LAMBDA 'v_ 'NN (list r8l-a-h (list r8l-a-e 'v_))))

(have! (list 'IN r8l-a-g (list 'FUN 'NN (list 'PTS r8l-a-s)))
  (lambda ()
    (dk-lam-t!)
    (let ((iv (dk-di-var!)))
      (fact 'fun-apply-type-c r8l-a-e 'NN 'NN iv)
      (fact 'fun-apply-type-c r8l-a-h 'NN (list 'PTS r8l-a-s) (list r8l-a-e iv))
      (ass))))

;; ---- sequential compactness at g --------------------------------------
(define r8l-a-sc-atoms
  (r8l-unfold! 'SEQ-COMPACT (list 'SEQ-COMPACT r8l-a-s)))
(define r8l-a-scu
  (or (any-pred (dk-head? 'FORALL) r8l-a-sc-atoms)
      (error "block-step: SEQ-COMPACT landed no sequence universal")))

(define r8l-a-EX  (dk-apply! r8l-a-scu r8l-a-g))
(define r8l-a-phi (dk-skolem! r8l-a-EX))
(define r8l-a-EXL (dk-pick (dk-head? 'FORSOME) "the subsequence's limit"))
(define r8l-a-L   (dk-skolem! r8l-a-EXL))

(define r8l-a-phi-atoms
  (r8l-unfold! 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN r8l-a-phi)))
(define r8l-a-phimono
  (or (any-pred (dk-head? 'FORALL) r8l-a-phi-atoms)
      (error "block-step: phi landed no monotonicity clause")))

;; ---- psi = v |-> e(phi v) ---------------------------------------------
(define r8l-a-psi (list 'VNB-LAMBDA 'v_ 'NN (list r8l-a-e (list r8l-a-phi 'v_))))

(have! (list 'STRICTLY-MONO-NN r8l-a-psi)
  (lambda ()
    (mac 'STRICTLY-MONO-NN)
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN)
           (begin
             (dk-lam-t!)
             (let ((iv (dk-di-var!)))
               (fact 'fun-apply-type-c r8l-a-phi 'NN 'NN iv)
               (fact 'fun-apply-type-c r8l-a-e 'NN 'NN (list r8l-a-phi iv))
               (ass)))
           (let* ((ls (dk-peel!))
                  (gl (dk-goal))             ; (< (psi m) (psi n))
                  (mv (cadr (cadr gl)))
                  (nv (cadr (caddr gl))))
             (r8l-beta!)                     ; -> (< (e (phi m)) (e (phi n)))
             (dk-apply! r8l-a-phimono mv nv)
             (fact 'fun-apply-type-c r8l-a-phi 'NN 'NN mv)
             (fact 'fun-apply-type-c r8l-a-phi 'NN 'NN nv)
             (dk-apply! r8l-a-emono (list r8l-a-phi mv) (list r8l-a-phi nv))
             (ass)))))))

(r8l-fun-typing! r8l-a-psi)

(have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list 'IN (list r8l-a-psi 'k_) r8l-a-J)))
  (lambda ()
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c r8l-a-phi 'NN 'NN kv)
      (r8l-beta!)
      (fact 'fun-apply-type-c r8l-a-e 'NN r8l-a-J (list r8l-a-phi kv))
      (ass))))

;; ---- the refined block -------------------------------------------------
(define r8l-a-bmem
  (dk-fact! 'strictly-mono-image-infinite r8l-a-psi r8l-a-J))
(define r8l-a-b (cadr r8l-a-bmem))            ; the SEP, READ OFF the instance

;; ---- the convergence hypothesis, unfolded -----------------------------
(define r8l-a-conv-atoms
  (r8l-unfold! 'CONVERGES-TO
               (list 'CONVERGES-TO r8l-a-s (list 'SUBSEQ r8l-a-g r8l-a-phi) r8l-a-L)))
(define r8l-a-epsu
  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'POS-RR)))
                r8l-a-conv-atoms)
      (error "block-step: CONVERGES-TO landed no eps clause")))

;; ---- the eps lane ------------------------------------------------------
(define (r8l-a-eps!)
  (dk-peel!)
  (let* ((ev   (cadr (dk-pick (dk-head? 'POS-RR) "eps")))
         (ex   (dk-apply! r8l-a-epsu ev))
         (bigN (dk-skolem! ex))
         (tail (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (dk-contains? f bigN)))
                        "the past-the-threshold estimate")))
    (fact 'fun-apply-type-c r8l-a-psi 'NN 'NN bigN)
    (witness! (list r8l-a-psi bigN)
      (lambda ()
        (dk-conj-close!
         (lambda ()
           (if (eq? (car (dk-goal)) 'IN)
               (ass)
               (begin
                 (dk-peel!)
                 (let* ((hmem (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                        (equal? (caddr f) r8l-a-b)))
                                       "the refined-block membership of the index"))
                        (iv (cadr hmem))
                        (fs (dk-landed (lambda () (sep-me (list 'IN iv r8l-a-b)))))
                        (ex2 (or (any-pred (dk-head? 'FORSOME) fs)
                                 (error "block-step: the block membership landed no witness")))
                        (kv  (dk-skolem! ex2)))
                   (have! (list '<= (list r8l-a-psi bigN) (list r8l-a-psi kv))
                     (lambda () (subst (list '= (list r8l-a-psi kv) iv)) (ass)))
                   (fact 'strictly-mono-le-reflect r8l-a-psi bigN kv)
                   (dk-apply! tail kv)
                   (fact 'fun-apply-type-c r8l-a-phi 'NN 'NN kv)
                   (have! (list '== (list r8l-a-h iv)
                                    (list (list 'SUBSEQ r8l-a-g r8l-a-phi) kv))
                     (lambda ()
                       (subst (list '= iv (list r8l-a-psi kv)))
                       ;; the VALUE equation at the TYPED index -- `mac SUBSEQ'
                       ;; here would unfold under the functoid's own binder and
                       ;; `lam-b' would owe the unprovable (IN (phi k) NN).
                       (subst (dk-fact! 'subseq-value-at r8l-a-g r8l-a-phi kv))
                       (r8l-beta!)
                       (qrfl)))
                   (subst (list '= (list r8l-a-h iv)
                                   (list (list 'SUBSEQ r8l-a-g r8l-a-phi) kv)))
                   (ass))))))))))

(witness! r8l-a-b
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (let ((gl (dk-goal)))
         (cond
           ((eq? (car gl) 'SUBSET)
            (mac 'subset-def)
            (let ((xv (dk-di-var!)))
              (sep-me (list 'IN xv r8l-a-b))
              (ass)))
           ((eq? (car gl) 'FORSOME)
            (witness! r8l-a-L
              (lambda ()
                (dk-conj-close!
                 (lambda ()
                   (if (eq? (car (dk-goal)) 'IN)
                       (ass)
                       (begin
                         (mac 'CONVERGES-ALONG)
                         (dk-conj-close!
                          (lambda ()
                            (if (eq? (car (dk-goal)) 'FORALL)
                                (r8l-a-eps!)
                                (ass)))))))))))
           (#t (ass))))))))

(r8l-qed! 'block-step-converges)
(gloss! 'block-step-converges
  "One refinement step of the diagonal argument: in a sequentially compact
   metric space, any sequence indexed by an infinite block of NN converges along
   some infinite sub-block.")
(topic! 'block-step-converges 'analysis)

;;; =====================================================================
;;; B.  convergence-block-tower -- THE SUPPORT, stated literally
;;; (theorem-library/seq-compact-product.scm:91).
;;;
;;; The tower is ONE parametric dependent choice (dc-on-nn-pred, PROVEN in
;;; rake-dc-on-nn.scm) over the set INF-SUBSETS(NN), with the step set
;;;
;;;   nxt(k, u) = { b in INF-SUBSETS(NN) : b subset u and coordinate k of seq
;;;                 converges along b to some point of PTS(ms k) }
;;;
;;; whose TOTALITY is exactly block-step-converges above.  The choice returns
;;; f : NN -> INF-SUBSETS(NN) with f(0) = NN and f(succ k) in nxt(k, f k); the
;;; tower the support asks for is the INDEX SHIFT  S := n |-> f(succ n)  (the
;;; move of theorem-library/block-family-combinatorial-proof), so that S(n) is
;;; already a member of nxt(n, f n) -- nested under S(k) and carrying the
;;; coordinate-n convergence.
;;;
;;; The limit point L needs no second dependent choice: the n-th choice does
;;; not depend on the earlier ones, so L is a VNB-LAMBDA with a CHOICE body
;;; over the (provably inhabited) set of coordinate-n limits along S(n).
;;; =====================================================================

(sp (make-wff
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (SEQ-COMPACT (ms n))))
       (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
         (FORSOME S
           (AND (IN S (FUN NN (INF-SUBSETS NN)))
           (AND (FORALL k (IMPLIES (IN k NN) (SUBSET (S (succ k)) (S k))))
                (FORSOME L
                  (AND (IN L (PRODUCT-CARRIER ms))
                       (FORALL n (IMPLIES (IN n NN)
                         (CONVERGES-ALONG (ms n)
                           (VNB-LAMBDA i NN ((seq i) n))
                           (S n)
                           (L n))))))))))))))))

(define r8l-t-landed (dk-peel!))

(define r8l-t-Hseq
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                            (pair? (caddr (caddr f)))
                            (eq? (car (caddr (caddr f))) 'PRODUCT-CARRIER)))
           "the typing of the product sequence"))
(define r8l-t-seq (cadr r8l-t-Hseq))
(define r8l-t-ms  (cadr (caddr (caddr r8l-t-Hseq))))
(define r8l-t-HSC
  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                 (dk-contains? f 'SEQ-COMPACT)))
                r8l-t-landed)
      (error "block-tower: no factorwise sequential compactness")))
(define r8l-t-X '(INF-SUBSETS NN))

;; coordinate n of seq, spelled as the support spells it
(define (r8l-t-coord n) (list 'VNB-LAMBDA 'i 'NN (list (list r8l-t-seq 'i) n)))

;; ---- each factor is a metric space, each coordinate a sequence in it ----
(define r8l-t-HMS
  (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                          (list 'IS-METRIC-SPACE (list r8l-t-ms 'n_)))))
(have! r8l-t-HMS
    (lambda ()
      (let ((nv (dk-di-var!)))
        (mac-h 'IS-MS-SEQUENCE (list 'IS-MS-SEQUENCE r8l-t-ms))
        (dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                             (dk-contains? f 'IS-METRIC-SPACE)))
                            "the factorwise metric-space clause")
                   nv)
        (ass))))

(define r8l-t-HCOORD
  (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
          (list 'IN (r8l-t-coord 'n_)
                (list 'FUN 'NN (list 'PTS (list r8l-t-ms 'n_)))))))
(have! r8l-t-HCOORD
    (lambda ()
      (let ((nv (dk-di-var!)))
        (dk-lam-t!)
        (let ((iv (dk-di-var!)))
          (fact 'fun-apply-type-c r8l-t-seq 'NN (list 'PRODUCT-CARRIER r8l-t-ms) iv)
          (fact 'product-carrier-coord r8l-t-ms (list r8l-t-seq iv) nv)
          (ass)))))

;; ---- the step set, and its totality ------------------------------------
(define r8l-t-nxt
  (list 'VNB-LAMBDA '(LIST k_ u_) (list 'CARTESIAN 'NN r8l-t-X)
    (list 'SEP 'bb_ r8l-t-X
      (list 'AND (list 'SUBSET 'bb_ 'u_)
        (list 'FORSOME 'p
          (list 'AND (list 'IN 'p (list 'PTS (list r8l-t-ms 'k_)))
                (list 'CONVERGES-ALONG (list r8l-t-ms 'k_) (r8l-t-coord 'k_) 'bb_ 'p)))))))

;; binders k, u, y SPELLED AS IN dc-on-nn-pred, so this instance IS its hypothesis
(define r8l-t-tot
  (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
    (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u r8l-t-X)
      (list 'FORSOME 'y
        (list 'AND (list 'IN 'y r8l-t-X)
              (list 'IN 'y (list r8l-t-nxt 'k 'u)))))))))

(have! r8l-t-tot
  (lambda ()
    (dk-peel!)
    (let* ((kv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (eq? (caddr f) 'NN)))
                              "the stage")))
           (uv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (equal? (caddr f) r8l-t-X)))
                              "the current block"))))
      (lam-b)                                   ; kv and uv are typed
      (dk-apply! r8l-t-HSC kv)
      (dk-apply! r8l-t-HCOORD kv)
      (let* ((ex (dk-fact! 'block-step-converges (list r8l-t-ms kv)
                           (r8l-t-coord kv) uv))
             (bv (dk-skolem! ex)))
        (dk-split-all!)
        (witness! bv
          (lambda ()
            (dk-conj-close!
             (lambda ()
               (let ((gl (dk-goal)))
                 (if (and (pair? (caddr gl)) (eq? (car (caddr gl)) 'SEP))
                     (for-each (lambda (l)
                                 (dk-focus! l)
                                 (dk-conj-close! (lambda () (ass))))
                               (dk-opened (lambda () (sep-mi))))
                     (ass)))))))))))

;; ---- the dependent choice ----------------------------------------------
(fact 'nn-is-set)
(fact 'inf-subsets-is-set 'NN)
(fact 'nn-in-inf-subsets)

(define r8l-t-EX (dk-fact! 'dc-on-nn-pred r8l-t-X 'NN r8l-t-nxt))
(define r8l-t-f  (dk-skolem! r8l-t-EX))
;; `dk-skolem!' splits only the OUTERMOST conjunction of the body; the
;; base/step pair under it may or may not still stand.  Split it if it does.
(let ((c (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                                    (dk-contains? f 'succ)))
                   (dk-asms))))
  (if c (dk-split! c)))

(define r8l-t-fstep
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f r8l-t-f)
                            (dk-contains? f 'succ)))
           "the per-stage step property"))

;; ---- what each rung of the tower carries -------------------------------
(define (r8l-t-Sbody n) (list r8l-t-f (list 'succ n)))

(define r8l-t-HSTEP
  (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
          (list 'AND (list 'SUBSET (r8l-t-Sbody 'n_) (list r8l-t-f 'n_))
            (list 'FORSOME 'p
              (list 'AND (list 'IN 'p (list 'PTS (list r8l-t-ms 'n_)))
                    (list 'CONVERGES-ALONG (list r8l-t-ms 'n_) (r8l-t-coord 'n_)
                          (r8l-t-Sbody 'n_) 'p)))))))
(have! r8l-t-HSTEP
    (lambda ()
      (let ((nv (dk-di-var!)))
        (fact 'nn-succ-closed nv)
        (fact 'fun-apply-type-c r8l-t-f 'NN r8l-t-X nv)
        (let* ((h  (dk-apply! r8l-t-fstep nv))
               (h2 (car (dk-landed (lambda () (lam-b-h h))))))
          (sep-me h2)
          (ass)))))

;; ---- the tower and the limit point --------------------------------------
(define r8l-t-S (list 'VNB-LAMBDA 'n_ 'NN (r8l-t-Sbody 'n_)))

(define (r8l-t-Lbody n)
  (list 'CHOICE
        (list 'SEP 'pp_ (list 'PTS (list r8l-t-ms n))
              (list 'CONVERGES-ALONG (list r8l-t-ms n) (r8l-t-coord n)
                    (r8l-t-Sbody n) 'pp_))))
(define r8l-t-L (list 'VNB-LAMBDA 'n_ 'NN (r8l-t-Lbody 'n_)))

(define r8l-t-HL
  (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
          (list 'AND (list 'IN (r8l-t-Lbody 'n_) (list 'PTS (list r8l-t-ms 'n_)))
                (list 'CONVERGES-ALONG (list r8l-t-ms 'n_) (r8l-t-coord 'n_)
                      (r8l-t-Sbody 'n_) (r8l-t-Lbody 'n_))))))
(have! r8l-t-HL
    (lambda ()
      (let* ((nv (dk-di-var!))
             (sepc (cadr (r8l-t-Lbody nv)))
             (two (dk-split! (dk-apply! r8l-t-HSTEP nv)))
             (ex  (or (any-pred (dk-head? 'FORSOME) two)
                      (error "block-tower: the rung landed no limit point")))
             (pv  (dk-skolem! ex)))
        (dk-apply! r8l-t-HMS nv)
        (choose! sepc pv
          (lambda ()
            (for-each (lambda (l) (dk-focus! l) (ass))
                      (dk-opened (lambda () (sep-mi))))))
        (dk-conj-close! (lambda () (ass))))))

(have! (list 'IN r8l-t-L (list 'PRODUCT-CARRIER r8l-t-ms))
  (lambda ()
    (mac 'PRODUCT-CARRIER)
    (for-each
     (lambda (l)
       (dk-focus! l)
       (let ((gl (dk-goal)))
         (if (eq? (car gl) 'FORALL)
             ;; the pointwise condition of the SEP
             (let ((nv (dk-di-var!)))
               (lam-b)
               (dk-split! (dk-apply! r8l-t-HL nv))
               (ass))
             ;; the FUN typing into the big union
             (begin
               (dk-lam-t!)
               (let ((nv (dk-di-var!)))
                 (for-each (lambda (l2)
                             (dk-focus! l2)
                             (if (eq? (caddr (dk-goal)) 'NN)
                                 (ass)
                                 (begin (dk-split! (dk-apply! r8l-t-HL nv)) (ass))))
                           (dk-opened (lambda () (bu-mi nv)))))))))
     (dk-opened (lambda () (sep-mi))))))

(witness! r8l-t-S
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (let ((gl (dk-goal)))
         (cond
           ;; S : NN -> INF-SUBSETS(NN)
           ((and (eq? (car gl) 'IN) (equal? (caddr gl) (list 'FUN 'NN r8l-t-X)))
            (dk-lam-t!)
            (let ((nv (dk-di-var!)))
              (fact 'nn-succ-closed nv)
              (fact 'fun-apply-type-c r8l-t-f 'NN r8l-t-X (list 'succ nv))
              (ass)))
           ;; the tower is nested
           ((eq? (car gl) 'FORALL)
            (let ((kv (dk-di-var!)))
              (fact 'nn-succ-closed kv)
              (lam-b)
              (dk-split! (dk-apply! r8l-t-HSTEP (list 'succ kv)))
              (ass)))
           ;; the limit point
           (#t
            (witness! r8l-t-L
              (lambda ()
                (dk-conj-close!
                 (lambda ()
                   (if (eq? (car (dk-goal)) 'IN)
                       (ass)
                       (let ((nv (dk-di-var!)))
                         (lam-b)
                         (dk-split! (dk-apply! r8l-t-HL nv))
                         (ass))))))))))))))

(r8l-qed! 'convergence-block-tower)
;; topic! for this name is set in theorem-library/pss-topics.scm -- not repeated here.
