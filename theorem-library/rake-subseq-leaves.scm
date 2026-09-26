;;; rake-subseq-leaves.scm -- the remaining asserted leaves of the
;;; subsequence / diagonalization cluster, PROVEN.
;;;
;;;   nn-step-mono-ptwise   (new, the workhorse)  a POINTWISE-typed sequence
;;;                         g with g(k) < g(succ k) satisfies m < n => g m < g n
;;;   nn-step-strictly-mono theorem-library/diagonalization-lemmas.scm:28
;;;   subsequence-capture   theorem-library/subsequence-capture.scm:24
;;;   null-rr-seq-exists    theorem-library/cauchy-subsequence.scm:144
;;;
;;; Two auxiliaries are proven here as well, both general and both filling a
;;; hole the tree had at this height:
;;;
;;;   nn-step-mono-ptwise     consecutive increase => strict monotonicity, with
;;;                           the typing POINTWISE rather than (IN g (FUN NN NN))
;;;   nn-recip-succ-small-at  recip(eps) < k+1  =>  recip(k+1) < eps, for every k
;;;
;;; LOAD WINDOW: after theorem-library/nn-infinite, before
;;; theorem-library/diagonalization.  (The natural slot is immediately before
;;; theorem-library/nn-nested-subset-chain-proof.)
;;;
;;;   lo is forced by theorem-library/nn-infinite -- `inf-subsets-unfold' and
;;;   `inf-subset-nn-unbounded', both cited by subsequence-capture.  The next
;;;   latest citations are theorem-library/nn-unbounded-in-rr (the archimedean
;;;   property, in null-rr-seq-exists), theorem-library/nn-order-proof
;;;   (nn-le-zero-is-zero), theorem-library/pos-rr-of-lt (nn-recip-succ-pos),
;;;   theorem-library/rr-recip-order (rr-recip-pos), theorem-library/rake-dc-on-nn
;;;   (dc-on-nn-pred), theorem-library/pos-rr-bridges, theorem-library/rr-order-basics,
;;;   theorem-library/nn-order-basics, theorem-library/nn-order-ord and
;;;   theorem-library/fun-apply-type-proof -- all above nn-infinite.  Everything
;;;   else is primitive (number-systems, theory.scm) or a definition site
;;;   (order-predicates for `<'/POS-RR, cauchy-subsequence for STRICTLY-MONO-NN
;;;   and NULL-RR-SEQ, inf-subsets).
;;;
;;;   hi is theorem-library/diagonalization, the earliest file that cites
;;;   nn-step-strictly-mono in a proof.  The other two have later citers
;;;   (theorem-library/cauchy-subseq-proof for null-rr-seq-exists,
;;;   theorem-library/subsequence-principle for subsequence-capture), so the
;;;   binding constraint is diagonalization alone.
;;;
;;; No late tactic is used: everything here is `interactive' + `driver-kit' +
;;; the ineq / crs oracles, all of which load far above the window.
;;;
;;; Helper prefix: rsq-.

;;; ---- file-local driver helpers ---------------------------------------

(define (rsq-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-subseq-leaves: ") (display name)
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
        (error "rake-subseq-leaves: unfinished" name))))

;;; =====================================================================
;;; nn-step-mono-ptwise
;;;
;;;   forall n_ in NN, g.
;;;     (forall k_ in NN. g(k_) in NN)                     -- pointwise typing
;;;     => (forall k_ in NN. g(k_) < g(succ k_))           -- the step
;;;     => forall m_ in NN. m_ < n_ => g(m_) < g(n_)
;;;
;;; The induction variable is OUTERMOST (`ni' tests the literal shape
;;; (FORALL n (IMPLIES (IN n NN) body)) and `di' is greedy), so g and the two
;;; hypotheses are quantified INSIDE the induction: the induction hypothesis
;;; is then the full universal at n_, which is what the step consumes.
;;;
;;; The typing is POINTWISE, not (IN g (FUN NN NN)).  That is what lets
;;; subsequence-capture below reuse it for an f : NN -> S with S a subset of
;;; NN: the tree has no FUN codomain-widening lemma, and a pointwise typing
;;; never needs one.
;;; =====================================================================

(define rsq-aux-stmt
  '(FORALL n_
     (IMPLIES (IN n_ NN)
       (FORALL g
         (IMPLIES (FORALL k_ (IMPLIES (IN k_ NN) (IN (g k_) NN)))
           (IMPLIES (FORALL k_ (IMPLIES (IN k_ NN) (< (g k_) (g (succ k_)))))
             (FORALL m_
               (IMPLIES (IN m_ NN)
                 (IMPLIES (< m_ n_) (< (g m_) (g n_)))))))))))

(sp (make-wff rsq-aux-stmt))
(define rsq-aux-cases (dk-opened (lambda () (ni))))

;; The STEP case is the one `ni' re-quantified over the induction variable:
;; its body is an IMPLIES guarded on (IN _ NN).  The BASE case's body is the
;; next FORALL of the statement.  Discriminate on THAT, never on leaf order.
(define (rsq-step-case? g)
  (and (pair? g) (eq? (car g) 'FORALL)
       (pair? (caddr g)) (eq? (car (caddr g)) 'IMPLIES)
       (pair? (cadr (caddr g))) (eq? (car (cadr (caddr g))) 'IN)
       (eq? (caddr (cadr (caddr g))) 'NN)))

(define (rsq-case what pred)
  (dk-focus! (or (any-pred (lambda (l) (pred (dk-goal-of l))) rsq-aux-cases)
                 (error "nn-step-mono-ptwise: no case" what))))

;; The goal of both cases, after the peel, is (< (g m_) (g <stage>)).
(define (rsq-goal-parts)
  (let ((gl (dk-goal)))
    (if (not (and (pair? gl) (eq? (car gl) '<)
                  (pair? (cadr gl)) (pair? (caddr gl))))
        (error "nn-step-mono-ptwise: goal is not a strict inequality of values"
               (expression->string gl)))
    (list (car (cadr gl))                       ; g
          (cadr (cadr gl))                      ; m_
          (cadr (caddr gl)))))                  ; the stage term

;;; BASE: n_ = 0.  No natural is < 0, so the hypothesis is absurd.
(rsq-case "base" (lambda (gl) (not (rsq-step-case? gl))))
(dk-peel!)
(let* ((p  (rsq-goal-parts))
       (mv (cadr p))
       (zz (caddr p)))
  (dk-split! (dk-landed-1 (lambda () (mac-h '< (list '< mv zz)))))
  (fact 'nn-le-zero-is-zero mv)                 ; (= m_ 0)
  (ai (list 'NOT (list '= mv zz))))

;;; STEP: m_ < succ n_ splits into m_ = n_ and m_ < n_.
(rsq-case "step" rsq-step-case?)
(let* ((landed (dk-peel!))
       (p   (rsq-goal-parts))
       (gv  (car p))
       (mv  (cadr p))
       (nv  (cadr (caddr p)))                   ; the succ's argument
       (sn  (caddr p))                          ; (succ n_)
       ;; the two hypotheses on g, and the induction hypothesis, told apart by
       ;; their CONSEQUENTS: the typing ends in (IN _ NN), the step in a `<',
       ;; the induction hypothesis is the only FORALL binding g.
       (typ (or (any-pred (lambda (f)
                            (and (pair? f) (eq? (car f) 'FORALL)
                                 (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                 (pair? (caddr (caddr f)))
                                 (eq? (car (caddr (caddr f))) 'IN)))
                          landed)
                (error "nn-step-mono-ptwise: no pointwise typing")))
       (stp (or (any-pred (lambda (f)
                            (and (pair? f) (eq? (car f) 'FORALL)
                                 (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                 (pair? (caddr (caddr f)))
                                 (eq? (car (caddr (caddr f))) '<)))
                          landed)
                (error "nn-step-mono-ptwise: no step hypothesis")))
       (ih  (or (any-pred (lambda (f)
                            (and (pair? f) (eq? (car f) 'FORALL)
                                 (eq? (cadr f) gv)))
                          landed)
                (error "nn-step-mono-ptwise: no induction hypothesis"))))
  ;; g(n_) < g(succ n_) -- the step hypothesis at n_
  (dk-apply! stp nv)
  (dk-split! (dk-landed-1 (lambda () (mac-h '< (list '< mv sn)))))
  (fact 'nn-le-succ-cases nv mv)                ; (OR (<= m_ n_) (= m_ (succ n_)))
  (use-cases (list (list '<= mv nv) (list '= mv sn))
    (lambda ()
      (use-em (list '= mv nv)
        (lambda ()                              ; m_ = n_: the step hypothesis itself
          (subst (list '= mv nv))
          (ass))
        (lambda ()                              ; m_ < n_: the induction hypothesis
          (have! (list '< mv nv) (lambda () (mac '<) (from-context!)))
          (dk-apply! ih gv)
          (dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                               (eq? (cadr f) 'm_)))
                              "the induction hypothesis at g")
                     mv)
          (fact 'nn-succ-closed nv)
          (dk-apply! typ mv) (dk-apply! typ nv) (dk-apply! typ sn)
          (fact 'nn-in-rr (list gv mv))
          (fact 'nn-in-rr (list gv nv))
          (fact 'nn-in-rr (list gv sn))
          (have! (list 'AND (list '< (list gv mv) (list gv nv))
                            (list '< (list gv nv) (list gv sn))))
          (fact 'rr-lt-trans (list gv mv) (list gv nv) (list gv sn))
          (ass))))
    (lambda ()                                  ; m_ = succ n_ contradicts m_ /= succ n_
      (ai (list 'NOT (list '= mv sn))))))

(rsq-qed! 'nn-step-mono-ptwise)
(topic! 'nn-step-mono-ptwise 'combinatorial)

;;; =====================================================================
;;; nn-step-strictly-mono -- THE SUPPORT, stated literally
;;; (theorem-library/diagonalization-lemmas.scm:28).
;;; =====================================================================

(sp (make-wff
  '(FORALL g
     (IMPLIES (IN g (FUN NN NN))
       (IMPLIES
         (FORALL k (IMPLIES (IN k NN) (< (g k) (g (succ k)))))
         (STRICTLY-MONO-NN g))))))

(define rsq-sm-landed (dk-peel!))
(define rsq-sm-g
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (equal? (caddr f) '(FUN NN NN))))
                 "the FUN typing of g")))
(define rsq-sm-typ
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list 'IN (list rsq-sm-g 'k_) 'NN))))

(have! rsq-sm-typ
  (lambda ()
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c rsq-sm-g 'NN 'NN kv)
      (ass))))

(mac 'STRICTLY-MONO-NN)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (and (pair? gl) (eq? (car gl) 'IN))
         (ass)
         (let* ((landed (dk-peel!))
                (p  (rsq-goal-parts))
                (mv (cadr p))
                (nv (caddr p)))
           (fact 'nn-step-mono-ptwise nv rsq-sm-g mv)
           (ass))))))

(rsq-qed! 'nn-step-strictly-mono)
(topic! 'nn-step-strictly-mono 'combinatorial)

;;; =====================================================================
;;; subsequence-capture -- THE SUPPORT, stated literally
;;; (theorem-library/subsequence-capture.scm:24).
;;;
;;; The construction the warrant describes, run through the PROVEN recursive
;;; choice `dc-on-nn-pred' (theorem-library/rake-dc-on-nn.scm) rather than
;;; through MIN-NN: the step set at (k,u) is { y in S : u < y }, non-empty by
;;; `inf-subset-nn-unbounded', so no well-foundedness argument is needed and
;;; nothing is asserted.  dc-on-nn-pred returns f : NN -> S with
;;; f(succ k) in { y in S : f(k) < y }, i.e. f(k) < f(succ k); the leap from
;;; consecutive steps to m < n is nn-step-mono-ptwise above, whose typing
;;; hypothesis is POINTWISE -- f is in FUN(NN,S), not FUN(NN,NN), and the tree
;;; has no codomain-widening lemma.
;;; =====================================================================

(sp (make-wff
  '(FORALL S
     (IMPLIES (IN S (INF-SUBSETS NN))
       (FORSOME f
         (AND (IN f (FUN NN S))
              (FORALL m
                (IMPLIES (IN m NN)
                  (FORALL n
                    (IMPLIES (IN n NN)
                      (IMPLIES (< m n) (< (f m) (f n)))))))))))))

(dk-peel!)
(define rsq-sc-S
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (equal? (caddr f) '(INF-SUBSETS NN))))
                 "the INF-SUBSETS typing of S")))

;; S is a set, and every member of S is a natural.  Both are read out of
;; INF-SUBSETS inside `have!' LANES: `mac-h' / `sep-me' CONSUME the hypothesis
;; they open, and the INF-SUBSETS typing is needed again by
;; inf-subset-nn-unbounded on the main branch.
(define (rsq-sc-open-power!)
  (let ((sep (dk-landed-find
              (lambda () (mac-h 'inf-subsets-unfold
                                (list 'IN rsq-sc-S '(INF-SUBSETS NN))))
              (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                               (pair? (caddr f)) (eq? (car (caddr f)) 'SEP))))))
    (sep-me sep)
    (dk-split! (dk-landed-1 (lambda () (mac-h 'power-set-membership
                                              (list 'IN rsq-sc-S '(POWER NN))))))))

(define rsq-sc-sub
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ rsq-sc-S) '(IN z_ NN))))

(have! (list 'IN rsq-sc-S 'SET) (lambda () (rsq-sc-open-power!) (ass)))
(have! rsq-sc-sub                (lambda () (rsq-sc-open-power!) (ass)))

;; a base point: S is unbounded above 0, so S is inhabited.
(fact 'nn-zero-in)
(define rsq-sc-base
  (dk-skolem! (dk-fact! 'inf-subset-nn-unbounded rsq-sc-S 0)))
(dk-split-all!)

;; the step: nxt(k,u) = { y in S : u < y }.  A destructuring VNB-LAMBDA, as in
;; rake-dc-on-nn.scm's relation form; it reduces in its DIRECT two-argument
;; application once both arguments are typed.
(define rsq-sc-nxt
  (list 'VNB-LAMBDA '(LIST k_ u_) (list 'CARTESIAN 'NN rsq-sc-S)
        (list 'SEP 'y_ rsq-sc-S (list '< 'u_ 'y_))))

(define (rsq-sc-tot s nx)
  (list 'FORALL 'k
    (list 'IMPLIES '(IN k NN)
      (list 'FORALL 'u
        (list 'IMPLIES (list 'IN 'u s)
          (list 'FORSOME 'y
            (list 'AND (list 'IN 'y s) (list 'IN 'y (list nx 'k 'u)))))))))

(have! (rsq-sc-tot rsq-sc-S rsq-sc-nxt)
  (lambda ()
    (dk-peel!)
    (let* ((uv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (eq? (caddr f) rsq-sc-S)
                                               (not (eq? (cadr f) rsq-sc-base))))
                              "the current point"))))
      (lam-b)                                   ; both arguments typed: the redex fires
      (dk-apply! rsq-sc-sub uv)                 ; (IN u NN)
      (let ((w (dk-skolem! (dk-fact! 'inf-subset-nn-unbounded rsq-sc-S uv))))
        (dk-split-all!)
        (witness! w
          (lambda ()
            (dk-conj-close!
             (lambda ()
               (let ((gl (dk-goal)))
                 (if (and (pair? (caddr gl)) (eq? (car (caddr gl)) 'SEP))
                     (for-each (lambda (l) (dk-focus! l) (ass))
                               (dk-opened (lambda () (sep-mi))))
                     (ass)))))))))))

(define rsq-sc-f
  (dk-skolem! (dk-fact! 'dc-on-nn-pred rsq-sc-S rsq-sc-base rsq-sc-nxt)))
(dk-split-all!)
(define rsq-sc-stage
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f rsq-sc-f)
                            (dk-contains? f 'succ)))
           "the per-stage step property"))

;; pointwise typing of f into NN, and the consecutive-increase hypothesis:
;; exactly the two antecedents nn-step-mono-ptwise wants.
(define rsq-sc-typ
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list 'IN (list rsq-sc-f 'k_) 'NN))))
(define rsq-sc-step
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
                          (list '< (list rsq-sc-f 'k_)
                                   (list rsq-sc-f '(succ k_))))))

(have! rsq-sc-typ
  (lambda ()
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c rsq-sc-f 'NN rsq-sc-S kv)
      (dk-apply! rsq-sc-sub (list rsq-sc-f kv))
      (ass))))

(have! rsq-sc-step
  (lambda ()
    (let* ((kv (dk-di-var!))
           (h  (dk-apply! rsq-sc-stage kv)))
      (fact 'fun-apply-type-c rsq-sc-f 'NN rsq-sc-S kv)
      (sep-me (car (dk-landed (lambda () (lam-b-h h)))))
      (ass))))

(witness! rsq-sc-f
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (let ((gl (dk-goal)))
         (if (and (pair? gl) (eq? (car gl) 'IN))
             (ass)
             (begin
               (dk-peel!)
               (let* ((p  (rsq-goal-parts))
                      (mv (cadr p))
                      (nv (caddr p)))
                 (fact 'nn-step-mono-ptwise nv rsq-sc-f mv)
                 (ass)))))))))

(rsq-qed! 'subsequence-capture)

;;; =====================================================================
;;; nn-recip-succ-small-at -- 1/(k+1) is below eps at EVERY k past 1/eps.
;;;
;;;   forall eps.  POS-RR(eps)
;;;     =>  forall k_ in NN.  recip(eps) < k_ + 1  =>  recip(k_ + 1) < eps
;;;
;;; The tree has `nn-recip-succ-small' (some k works) but the ANTITONE fact
;;; that turns it into a tail statement -- `nn-recip-succ-antitone' -- is proven
;;; only in theorem-library/sequential-continuity.scm, far BELOW every citer of
;;; null-rr-seq-exists.  This is the pointwise form, which needs no monotonicity
;;; at all: it is nn-recip-succ-small's own two-scaling chain
;;; (theorem-library/nn-recip-succ-small.scm:79-128) with the natural given
;;; rather than produced, so it reaches every k in the tail at once.
;;; =====================================================================

(define (rsq-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rsq-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))

(define (rsq-ineq . forms) (apply ineq (map rsq-idx forms)))

(sp (make-wff
  '(FORALL eps
     (IMPLIES (POS-RR eps)
       (FORALL k_
         (IMPLIES (IN k_ NN)
           (IMPLIES (< (recip eps) (+ k_ 1))
                    (< (recip (+ k_ 1)) eps))))))))

;; POS-RR is not an IN-typing, so `di' peels the quantifier ALONE and the
;; antecedent lands on the next call: loop on the head, not on a count.
(let loop ((i 0))
  (if (and (memq (car (dk-goal)) '(FORALL IMPLIES)) (< i 6))
      (begin (di) (loop (+ i 1)))))
(if (not (equal? (dk-goal) '(< (recip (+ k_ 1)) eps)))
    (error "nn-recip-succ-small-at: unexpected goal after the peel"
           (expression->string (dk-goal))))

(dk-split! (dk-landed-1 (lambda () (mac-h 'pos-rr '(POS-RR eps)))))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'nn-one-in)
(have! '(AND (<= 0 eps) (NOT (= 0 eps))))
(fact 'rr-le-ne-lt 0 'eps)                        ; 0 < eps
(fact 'rr-pos-ne-zero 'eps)                       ; not(eps = 0)
(have! '(AND (IN eps RR) (NOT (= eps 0))))
(fact 'rr-recip-closed 'eps)                      ; recip(eps) in RR
(fact 'rr-recip-inverse 'eps)                     ; eps * recip(eps) = 1
(fact 'rr-recip-pos 'eps)                         ; 0 < recip(eps)

(let* ((n1   '(+ k_ 1))
       (rn1  '(recip (+ k_ 1)))
       (prod '(* eps (+ k_ 1)))
       (HYP  '(< (recip eps) (+ k_ 1)))
       (H1   (list '< '(* eps (recip eps)) prod))
       (E1   '(= (* eps (recip eps)) 1))
       (big  (list '* rn1 prod))
       (H2   (list '< (list '* rn1 1) big))
       (C1   (list '= big (list '* 'eps (list '* n1 rn1))))
       (C2   (list '= (list '* 'eps (list '* n1 rn1)) 'eps))
       (E2   (list '= big 'eps)))
  (fact 'nn-in-rr 'k_)
  (have! '(AND (IN k_ RR) (IN 1 RR)))
  (fact 'rr-add-closed 'k_ 1)                     ; k_ + 1 in RR
  (have! '(AND (IN k_ NN) (IN 1 NN)))
  (fact 'nn-add-closed 'k_ 1)                     ; k_ + 1 in NN
  (have! (list '< 0 n1) (lambda () (rsq-ineq '(< 0 (recip eps)) HYP)))
  (fact 'rr-pos-ne-zero n1)
  (have! (list 'AND (list 'IN n1 'RR) (list 'NOT (list '= n1 0))))
  (fact 'rr-recip-closed n1)                      ; recip(k_+1) in RR
  (fact 'rr-recip-inverse n1)                     ; (k_+1) * recip(k_+1) = 1
  (fact 'rr-recip-pos n1)                         ; 0 < recip(k_+1)
  ;; first scaling: by eps
  (have! (list 'AND '(< 0 eps) HYP))
  (fact 'rr-lt-scale-pos 'eps '(recip eps) n1)    ; H1
  (have! (list 'AND '(IN eps RR) (list 'IN n1 'RR)))
  (fact 'rr-mul-closed 'eps n1)                   ; eps * (k_+1) in RR
  (have! '(AND (IN eps RR) (IN (recip eps) RR)))
  (fact 'rr-mul-closed 'eps '(recip eps))
  (have! (list '< 1 prod) (lambda () (rsq-ineq H1 E1)))
  ;; second scaling: by recip(k_+1)
  (have! (list 'AND (list '< 0 rn1) (list '< 1 prod)))
  (fact 'rr-lt-scale-pos rn1 1 prod)              ; H2
  (have! (list 'AND (list 'IN rn1 'RR) (list 'IN prod 'RR)))
  (fact 'rr-mul-closed rn1 prod)                  ; big in RR
  (have! C1 (lambda () (crs)))
  (have! C2 (lambda () (subst (list '= (list '* n1 rn1) 1)) (crs)))
  (have! E2 (lambda () (subst C1) (ass)))
  (rsq-ineq H2 E2))

(rsq-qed! 'nn-recip-succ-small-at)
(topic! 'nn-recip-succ-small-at 'inequalities)

;;; =====================================================================
;;; null-rr-seq-exists -- THE SUPPORT, stated literally
;;; (theorem-library/cauchy-subsequence.scm:144).
;;;
;;; Witness k |-> recip(k + 1), not the warrant's 2^-k: the tree has no
;;; geometric-decay fact this early, and the reciprocal has both pieces proven
;;; (`nn-recip-succ-pos', theorem-library/pos-rr-of-lt.scm).  The tail bound is
;;; nn-recip-succ-small-at above, fed by the archimedean property
;;; (`nn-unbounded-in-rr') at recip(eps): past that natural every k_+1 exceeds
;;; recip(eps), so every radius from there on is below eps.
;;; =====================================================================

(define rsq-nr-lam '(VNB-LAMBDA k_ NN (recip (+ k_ 1))))

(sp (make-wff '(FORSOME rad (NULL-RR-SEQ rad))))

(witness! rsq-nr-lam
  (lambda ()
    (mac 'NULL-RR-SEQ)
    (dk-conj-close!
     (lambda ()
       (let ((gl (dk-goal)))
         (cond
           ;; (IN LAM (FUN NN RR)) -- lam-t opens the pointwise typing and the
           ;; sethood of NN.  `dk-opened', not `dk-lam-t!': sibling conjuncts
           ;; of this AND are still open and dk-lam-t! diffs leaves GLOBALLY.
           ((and (eq? (car gl) 'IN) (pair? (cadr gl))
                 (eq? (car (cadr gl)) 'VNB-LAMBDA))
            (for-each
             (lambda (l)
               (dk-focus! l)
               (if (eq? (car (dk-goal)) 'FORALL)
                   (let ((kv (dk-di-var!)))
                     (fact 'nn-recip-succ-pos kv)
                     (fact 'rr-pos-rr-in-rr (list 'recip (list '+ kv 1)))
                     (ass))
                   (begin (fact 'nn-is-set) (ass))))
             (dk-opened (lambda () (lam-t)))))
           ;; forall k in NN.  POS-RR(LAM k) -- the GUARD is the NN typing;
           ;; the eps conjunct's guard is a POS-RR.  Discriminate on THAT.
           ((eq? (car (cadr (caddr gl))) 'IN)
            (let ((kv (dk-di-var!)))
              (lam-b)                             ; kv is typed: the redex fires
              (fact 'nn-recip-succ-pos kv)
              (ass)))
           ;; forall eps.  POS-RR(eps) => forsome N in NN. tail below eps
           (#t
            (let loop ((i 0))
              (if (and (memq (car (dk-goal)) '(FORALL IMPLIES)) (< i 2))
                  (begin (di) (loop (+ i 1)))))
            (let* ((ev (cadr (dk-pick (dk-head? 'POS-RR) "the tolerance"))))
              (fact 'rr-pos-rr-in-rr ev)          ; eps in RR
              (fact 'rr-lt-of-pos-rr ev)          ; 0 < eps
              (fact 'rr-pos-ne-zero ev)           ; eps /= 0
              (have! (list 'AND (list 'IN ev 'RR) (list 'NOT (list '= ev 0))))
              (fact 'rr-recip-closed ev)          ; recip(eps) in RR
              (fact 'rr-zero-in)
              (fact 'rr-one-in)
              (fact 'nn-one-in)
              (let* ((parts (dk-split! (dk-fact! 'nn-unbounded-in-rr
                                                 (list 'recip ev))))
                     (bigN  (cadr (or (find-first (dk-head? 'IN) parts)
                                      (error "null-rr-seq-exists: no witness"
                                             parts)))))
                (witness! bigN
                  (lambda ()
                    (dk-conj-close!
                     (lambda ()
                       (let ((g2 (dk-goal)))
                         (if (and (pair? g2) (eq? (car g2) 'IN))
                             (ass)
                             (begin
                               ;; the universal is UNGUARDED (its antecedent is
                               ;; a CONJUNCTION, not an IN-typing), so the first
                               ;; `di' lands nothing and the second lands the AND
                               (let loop ((i 0))
                                 (if (and (memq (car (dk-goal))
                                                '(FORALL IMPLIES))
                                          (< i 3))
                                     (begin (di) (loop (+ i 1)))))
                               (dk-split! (dk-pick
                                           (lambda (f)
                                             (and (pair? f) (eq? (car f) 'AND)
                                                  (pair? (caddr f))
                                                  (eq? (car (caddr f)) '<=)))
                                           "the tail guard"))
                               (let ((kv (cadr (cadr (dk-goal)))))
                               (fact 'nn-in-rr bigN)
                               (fact 'nn-in-rr kv)
                               (have! (list 'AND (list 'IN kv 'RR) '(IN 1 RR)))
                               (fact 'rr-add-closed kv 1)
                               (have! (list '< (list 'recip ev)
                                               (list '+ kv 1))
                                 (lambda ()
                                   (rsq-ineq (list '< (list 'recip ev) bigN)
                                             (list '<= bigN kv))))
                               (fact 'nn-recip-succ-small-at ev kv)
                               (fact 'nn-recip-succ-pos kv)
                               (fact 'rr-pos-rr-in-rr
                                     (list 'recip (list '+ kv 1)))
                               (lam-b)            ; kv typed: the redex fires
                               (rsq-ineq (list '< (list 'recip (list '+ kv 1))
                                                  ev)))))))))))))))))))

(rsq-qed! 'null-rr-seq-exists)
