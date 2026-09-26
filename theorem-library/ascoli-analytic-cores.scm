;;; ascoli-analytic-cores.scm -- the analytic content of Ascoli-Arzelà, machine-proved.
;;; bridge, MACHINE-PROVED, and the one rung it still stands on.
;;;
;;; WHAT CHANGED, AND WHY THE STATEMENT SPLIT IN TWO.
;;;
;;; ascoli-bridge.scm asserted ONE support, `equicont-dense-conv-implies-unif-
;;; cauchy' -- "on a COMPACT space, an equicontinuous family that is Cauchy on a
;;; dense sequence is UNIFORMLY Cauchy" -- and called it "the 3-epsilon core".
;;; The user's own notes (docs/calculus.pdf, ch. 3) do not state it that way,
;;; and the difference is the whole content of this file.  There the argument is
;;; TWO propositions:
;;;
;;;   Lemma 3.36.  X a metric space, {f_k} equicontinuous, D dense, {f_k(y)}
;;;     convergent for y in D.  Then {f_k(a)} is CAUCHY at every a in X.
;;;     -- the 3-epsilon estimate, and it uses NO compactness whatever.
;;;
;;;   Prop 3.33.  X COMPACT and {f_k} equicontinuous.  Then pointwise
;;;     convergence is uniform convergence.
;;;     -- and compactness enters here and only here, as a finite subcover of
;;;        the equicontinuity neighbourhoods plus a max over finitely many
;;;        thresholds.
;;;
;;; Compactness was bundled into the asserted core, and bundling it hid the fact
;;; that three quarters of the statement needs none of it.  Split as the notes
;;; split it, the analytic half is PROVEN here `modulo 0' and what is left owed
;;; is exactly the finite-subcover half, stated on its own as
;;; `ptwise-cauchy-compact-equicont-unif'.
;;;
;;; THE PROOF (equicont-dense-conv-ptwise-cauchy), in the notes' words.  Fix a
;;; and eps.  Halve eps twice, giving c with 4c = eps -- never eps/4, so no
;;; `recip' enters the goal and every step stays linear for `ineq'.
;;; Equicontinuity at (a, c) gives del; density gives y = dseq(m) with
;;; d_s(a,y) < del; the value sequence at y converges, to L say, with threshold
;;; cap at tolerance c.  For k, l >= cap:
;;;
;;;   |f_k(a) - f_l(a)|  <=  |f_k(a)-f_k(y)| + |f_k(y)-L| + |L-f_l(y)| + |f_l(y)-f_l(a)|
;;;                      <   c + c + c + c  =  eps.
;;;
;;; FOUR hops, not three: the middle hop of the paper argument ("{f_k(y)} is
;;; Cauchy") is itself two, because the tree has CONVERGES but no
;;; converges-implies-cauchy -- see the NOTE at the end of this file.
;;;
;;; MECHANICS worth keeping.  The estimate never enters a general metric space:
;;; every bound arrives as ((DIST RR-MS) u v) and is opened to abs(u - v) by
;;; `rr-ms-dist' (proven, modulo 0) the moment it lands, after which `ineq'
;;; certifies the abs atoms itself (ineq-oracle.scm accepts an abs(.) term) and
;;; the whole composition is ONE Fourier-Motzkin certificate over the three
;;; triangle instances, the two |u-v| = |v-u| symmetries and the four hop bounds.
;;; `metric-triangle' and `metric-dist-real' are never cited, which is why the
;;; bill is `modulo 0' and not `modulo {metric-dist-real}'.
;;;
;;; `driver-kit''s `eps-chain' does this composition in one call, for a goal
;;; shaped ((DIST s) x0 xn) < eps.  It is NOT used here and the reason is the
;;; statement: IS-UNIF-CAUCHY and IS-PTWISE-CAUCHY are written with `abs', not
;;; with the RR-MS distance, so the goal has the wrong head for it -- and going
;;; through eps-chain would put `metric-dist-real' (a `well-known' support) into
;;; a bill that is otherwise unconditional.  eps-chain has no caller anywhere in
;;; the tree; this file is the closest thing to one and deliberately declines.
;;;
;;; VOCABULARY MOVED HERE from ascoli-bridge.scm (2026-08-23): IS-DENSE-SEQ,
;;; CONVERGES-ON, IS-UNIF-CAUCHY.  They are unchanged; they moved because the
;;; proofs below need them and this file loads first.  IS-PTWISE-CAUCHY is new.
;;;
;;; Loads after ascoli-arzela-statement (IS-EQUICONTINUOUS), separable,
;;; compactness, metric-completeness (CONVERGES / CONVERGES-TO), rr-ms-dist,
;;; rr-abs-basics (rr-abs-triangle-c, rr-abs-sub-sym), binary-minus-laws
;;; (rr-sub-in-rr), rr-halving (rr-pos-halvable), fun-apply-type-proof.
;;; Binders: dseq (dense seq), cap (threshold, NOT N), lv (the limit value,
;;; NOT L -- it folds onto l, the second running index).
;;; ====================================================================
;;; RETIRED 2026-09-14 (proven): ptwise-cauchy-compact-equicont-unif -- theorem-library/ptwise-cauchy-unif.scm (gloss kept)

;;; ---- vocabulary --------------------------------------------------------

;;; IS-DENSE-SEQ(s, dseq): dseq : NN -> PTS(s) has dense range (every ball meets
;;; it).  IS-SEPARABLE(s) is exactly (FORSOME dseq. IS-DENSE-SEQ s dseq).
(def-predicate 'IS-DENSE-SEQ '(s dseq)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN dseq (FUN NN (PTS s)))
      (forall-guarded 'x '(IN x (PTS s))
        (forall-guarded 'eps '(POS-RR eps)
          (forsome-guarded 'm '(IN m NN)
            '(< ((DIST s) x (dseq m)) eps)))))))
(notation! 'IS-DENSE-SEQ 'kind 'predicate 'arity 2
           'english "$2 is a dense sequence in $1")

;;; CONVERGES-ON(s, fam, dseq): at every point of dseq the real sequence
;;; k |-> fam(k)(dseq(m)) converges.
(def-predicate 'CONVERGES-ON '(s fam dseq)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(IN dseq (FUN NN (PTS s)))
      (forall-guarded 'm '(IN m NN)
        '(CONVERGES RR-MS (VNB-LAMBDA k NN ((fam k) (dseq m))))))))
(notation! 'CONVERGES-ON 'kind 'predicate 'arity 3
           'english "$2 converges at every point of the sequence $3 in $1")

;;; IS-UNIF-CAUCHY(s, fam): fam is uniformly Cauchy -- one threshold cap serves
;;; every point x at once.  (Carries IS-METRIC-SPACE s, so downstream lemmas need
;;; not re-assume it.)
(def-predicate 'IS-UNIF-CAUCHY '(s fam)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      (forall-guarded 'eps '(POS-RR eps)
        (forsome-guarded 'cap '(IN cap NN)
          (forall-guarded 'k '(AND (IN k NN) (<= cap k))
            (forall-guarded 'l '(AND (IN l NN) (<= cap l))
              (forall-guarded 'x '(IN x (PTS s))
                '(< (abs (- ((fam k) x) ((fam l) x))) eps)))))))))
(notation! 'IS-UNIF-CAUCHY 'kind 'predicate 'arity 2
           'english "$2 is uniformly Cauchy on $1")

;;; IS-PTWISE-CAUCHY(s, fam): fam is POINTWISE Cauchy -- the same clause as
;;; IS-UNIF-CAUCHY with the point quantifier moved OUTSIDE the threshold, so cap
;;; may depend on x.  Exactly the difference the compactness rung has to close.
(def-predicate 'IS-PTWISE-CAUCHY '(s fam)
  (conjuncts->and
    (list
      '(IS-METRIC-SPACE s)
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      (forall-guarded 'x '(IN x (PTS s))
        (forall-guarded 'eps '(POS-RR eps)
          (forsome-guarded 'cap '(IN cap NN)
            (forall-guarded 'k '(AND (IN k NN) (<= cap k))
              (forall-guarded 'l '(AND (IN l NN) (<= cap l))
                '(< (abs (- ((fam k) x) ((fam l) x))) eps)))))))))
(notation! 'IS-PTWISE-CAUCHY 'kind 'predicate 'arity 2
           'english "$2 is pointwise Cauchy on $1")

;;; ---- file-local driver helpers (the `acc-' prefix) ----------------------

(define (acc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (begin (di) (loop (+ n 1)))
          n))))

;;; skolemize a FORSOME already in the CONTEXT (`obtain' sees only what its own
;;; lane landed).  Returns (LANDED-FORMULA . (EIGENVARIABLES)); a miss ERRORS,
;;; because dk-landed* errors when nothing lands.
(define (acc-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new    (car landed))
         (fvs-b  (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

;;; di-split an AND goal to its leaves and run CLOSER on each.
(define (acc-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (acc-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; inst+ lands its whole instantiation chain; the detached result is the
;;; landing no other landing contains.
(define (acc-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

;;; (IN x RR) off a POS-RR on a SIDE branch -- `mac-h' REPLACES the hypothesis
;;; and the eps universal above still wants it.
(define (acc-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; (<= 0 x) off a POS-RR, same lane trick.  `ineq' needs it whenever a bound is
;;; SLACK: three hops under c close a goal of size 4c only because c >= 0.
(define (acc-nonneg! x)
  (have! (list '<= 0 x)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; halve a positive real: lands POS-RR(h) and (+ h h) = e; returns h.
(define (acc-halve! e)
  (let* ((sk (acc-skolem! (dk-fact! 'rr-pos-halvable e))))
    (dk-split! (car sk))
    (car (cadr sk))))

(define (acc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "acc-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

;;; A universal whose antecedent is a CONJUNCTION peels the quantifier and lands
;;; NOTHING; the antecedent comes on the next call.  Loop on the LANDING.
(define (acc-di-landed!)
  (let loop ((n 0))
    (let ((ls (dk-landed* (lambda () (di)))))
      (cond ((pair? ls) (car ls))
            ((> n 5) (error "acc-di-landed!: nothing ever landed"))
            (else (loop (+ n 1)))))))

(define (acc-find pred)
  (let loop ((as (dk-asms)))
    (cond ((null? as) (error "acc-find: no assumption matches"))
          ((pred (car as)) (car as))
          (else (loop (cdr as))))))

(define (acc-mentions? fm sym)
  (let loop ((e fm))
    (cond ((eq? e sym) #t)
          ((pair? e) (or (loop (car e)) (loop (cdr e))))
          (else #f))))

;;; |a - c| <= |a - b| + |b - c|, landed as a hypothesis.  The three arguments
;;; must already be typed in RR.  rr-abs-triangle-c is about a SUM, so the
;;; difference is normalised to (a-b) + (b-c) by `crs' and substituted in --
;;; `subst' reaches argument positions, and (- a c) sits in one.
(define (acc-tri! aa bb cc)
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

;;; ---- THE ANALYTIC CORE, PROVEN -----------------------------------------

;;; equicont-dense-conv-ptwise-cauchy: equicontinuity plus convergence on a
;;; dense sequence makes the family Cauchy AT EVERY POINT.  No compactness.

(sp (make-wff
  (forall-guarded '(s fam)
    (list
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(IS-EQUICONTINUOUS s RR-MS fam)
      (forsome-guarded 'dseq '(IS-DENSE-SEQ s dseq) '(CONVERGES-ON s fam dseq)))
    '(IS-PTWISE-CAUCHY s fam))))
(acc-peel!)

;;; the dense sequence, and the three hypotheses unfolded to their working forms
(define acc-sk
  (acc-skolem! '(FORSOME dseq (AND (IS-DENSE-SEQ s dseq) (CONVERGES-ON s fam dseq)))))
(define acc-dseq (car (cadr acc-sk)))
(dk-split! (car acc-sk))
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-equicontinuous '(IS-EQUICONTINUOUS s RR-MS fam)))))
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-dense-seq (list 'IS-DENSE-SEQ 's acc-dseq)))))
(dk-split! (dk-landed-1 (lambda () (mac-h 'converges-on (list 'CONVERGES-ON 's 'fam acc-dseq)))))
(define acc-EQ (list-ref (dk-asms) 3))   ; the equicontinuity universal
(define acc-DE (list-ref (dk-asms) 1))   ; the density universal
(define acc-CO (list-ref (dk-asms) 0))   ; the pointwise-convergence universal

;;; The estimate, at a fixed point and a fixed tolerance.
(define (acc-close! a eps hh c lv yy k l eqd ntc)
  (let* ((fk (list 'fam k)) (fl (list 'fam l))
         (aa (list fk a))   (bb (list fk yy))
         (cc (list fl yy))  (dd (list fl a)))
    ;; the four values are reals
    (fact 'fun-apply-type-c 'fam 'NN (list 'FUN (list 'PTS 's) 'RR) k)
    (fact 'fun-apply-type-c 'fam 'NN (list 'FUN (list 'PTS 's) 'RR) l)
    (fact 'fun-apply-type-c fk (list 'PTS 's) 'RR a)
    (fact 'fun-apply-type-c fk (list 'PTS 's) 'RR yy)
    (fact 'fun-apply-type-c fl (list 'PTS 's) 'RR a)
    (fact 'fun-apply-type-c fl (list 'PTS 's) 'RR yy)
    (let ((e1 (acc-inst! (acc-inst! eqd k) yy))   ; d(f_k(a), f_k(y)) < c
          (e4 (acc-inst! (acc-inst! eqd l) yy))   ; d(f_l(a), f_l(y)) < c
          (n2 (acc-inst! ntc k))                  ; d(seq(k), L) <= c
          (n3 (acc-inst! ntc l)))                 ; d(seq(l), L) <= c
      ;; the value sequence is a VNB-LAMBDA; reduce it in place, then open every
      ;; RR-MS distance to abs (rr-ms-dist is GUARDED, and the arguments were
      ;; typed above -- so no side condition is spawned).
      (let ((b2 (dk-landed-1 (lambda () (lam-b-h n2))))
            (b3 (dk-landed-1 (lambda () (lam-b-h n3)))))
        (for-each (lambda (f) (mac-h 'rr-ms-dist f)) (list e1 e4 b2 b3))
        (acc-tri! aa bb dd)
        (acc-tri! bb lv dd)
        (acc-tri! lv cc dd)
        (fact 'rr-abs-sub-sym lv cc)
        (fact 'rr-abs-sub-sym cc dd)
        ;; ONE certificate.  Name the premises: an untyped atom anywhere in the
        ;; context (d_s(a, dseq(m)), for one) makes an unnamed `ineq' refuse.
        (let* ((ab (lambda (u v) (list 'abs (list '- u v))))
               (prem (list
                      (list '<= (ab aa dd) (list '+ (ab aa bb) (ab bb dd)))
                      (list '<= (ab bb dd) (list '+ (ab bb lv) (ab lv dd)))
                      (list '<= (ab lv dd) (list '+ (ab lv cc) (ab cc dd)))
                      (list '= (ab lv cc) (ab cc lv))
                      (list '= (ab cc dd) (ab dd cc))
                      (list '< (ab aa bb) c)
                      (list '< (ab dd cc) c)
                      (list '<= (ab bb lv) c)
                      (list '<= (ab cc lv) c)
                      (list '= (list '+ c c) hh)
                      (list '= (list '+ hh hh) eps))))
          (apply ineq (map acc-idx prem)))))))

(mac 'is-ptwise-cauchy)
(acc-and!
 (lambda ()
   (if (not (eq? (car (dk-goal)) 'FORALL))
       (ass)                                    ; IS-METRIC-SPACE s / the typing
       (let* ((mx  (dk-landed-1 (lambda () (di))))   ; (IN a (PTS s))
              (a   (cadr mx))
              (me  (dk-landed-1 (lambda () (di))))   ; (POS-RR eps)
              (eps (cadr me)))
         (acc-pos-in-rr! eps)
         (let* ((hh  (acc-halve! eps))                       ; hh + hh = eps
                (c   (acc-halve! hh))                        ; c + c = hh
                (eqd (acc-skolem! (acc-inst! (acc-inst! acc-EQ a) c)))
                (del (car (cadr eqd))))
           (dk-split! (car eqd))
           (let* ((ded (acc-skolem! (acc-inst! (acc-inst! acc-DE a) del)))
                  (m   (car (cadr ded))))
             (dk-split! (car ded))
             (let* ((co1 (acc-inst! acc-CO m))
                    (cf  (dk-landed-1 (lambda () (mac-h 'converges co1))))
                    (skl (acc-skolem! cf))
                    (lv  (car (cadr skl))))
               (dk-split! (dk-landed-1 (lambda () (mac-h 'converges-to (car skl)))))
               (let* ((skn (acc-skolem! (acc-inst! (car (dk-asms)) c)))
                      (cap (car (cadr skn))))
                 (dk-split! (car skn))
                 (let ((eqd* (acc-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                        (acc-mentions? f del)
                                                        (acc-mentions? f 'DIST)))))
                       (ntc* (acc-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                        (acc-mentions? f cap)
                                                        (acc-mentions? f lv)))))
                       (yy   (list acc-dseq m)))
                   (acc-pos-in-rr! hh)
                   (acc-pos-in-rr! c)
                   (slot-h 'PTS (list 'IN lv '(PTS RR-MS)))
                   (fact 'fun-apply-type-c acc-dseq 'NN (list 'PTS 's) m)
                   (ew cap)
                   (acc-and!
                    (lambda ()
                      (if (eq? (car (dk-goal)) 'IN)
                          (ass)                              ; (IN cap NN)
                          (let* ((mk (acc-di-landed!)) (k (cadr (cadr mk))))
                            (dk-split! mk)
                            (let* ((ml (acc-di-landed!)) (l (cadr (cadr ml))))
                              (dk-split! ml)
                              (acc-close! a eps hh c lv yy k l eqd* ntc*)))))))))))))))
(qed 'equicont-dense-conv-ptwise-cauchy)
(topic! 'equicont-dense-conv-ptwise-cauchy 'analysis)
(alias! 'equicont-dense-conv-ptwise-cauchy
        "equicontinuous + convergent on a dense sequence => Cauchy at every point")
(gloss! 'equicont-dense-conv-ptwise-cauchy
  "The user's calculus notes, Lemma 3.36, Cauchy half.  Let fam be an
   equicontinuous sequence of real-valued maps on a metric space s, and suppose
   the values converge at every term of some dense sequence.  Then at EVERY
   point a of s the real sequence k |-> fam(k)(a) is Cauchy.  The estimate is
   |f_k(a)-f_l(a)| <= |f_k(a)-f_k(y)| + |f_k(y)-L| + |L-f_l(y)| + |f_l(y)-f_l(a)|,
   with y a dense-sequence point inside the equicontinuity delta at a and L the
   limit there.  COMPACTNESS IS NOT USED: it is what upgrades this to UNIFORM
   Cauchyness (ptwise-cauchy-compact-equicont-unif), and nothing else.")

;;; ---- the compactness rung (ASSERTED) -----------------------------------

;;; ptwise-cauchy-compact-equicont-unif -- Prop 3.33 of the notes, in the Cauchy
;;; spelling this arc uses.  The ONE thing the dense bridge still owes.
(gloss! 'ptwise-cauchy-compact-equicont-unif
  "Fix eps.  Equicontinuity at each x gives a neighbourhood V_x on which every
   fam(k) varies by less than eps/3; the V_x cover the space, compactness picks
   finitely many V_{x_1},...,V_{x_n}, and pointwise Cauchyness gives a threshold
   cap_i at each of the n centres.  max(cap_1,...,cap_n) then serves every point
   at once, which is uniform Cauchyness.
   WHAT A MACHINE PROOF NEEDS, and neither is in the base: (1) the passage from
   the finite subcover F -- IS-COMPACT delivers a set F with (IN (CARD F) NN) --
   to an INDEXED finite list of centres, i.e. FIN-ENUM over ORD-SEGMENT(CARD F),
   the same conversion `tb-scale-dense-seq' (structure-library/separable.scm)
   declines to mechanise; and (2) a FINITE MAX over that index set, of which the
   tree has only the binary `MAX' (rr-le-max-left / nn-max-closed).  Both are
   set-theoretic bookkeeping over a finite index, not analysis: the analysis of
   the bridge is `equicont-dense-conv-ptwise-cauchy' above, and that is proved.")

;;; ---- CORE A, the ASSEMBLY, MOVED 2026-09-15 to theorem-library/ascoli-assembly.scm:
;;; it cites ptwise-cauchy-compact-equicont-unif, which is now a THEOREM
;;; (theorem-library/ptwise-cauchy-unif.scm) that must load AFTER this file (it
;;; unfolds the Cauchy predicates defined here) and BEFORE the assembly.

;;; ---- A UNIFORM LIMIT OF CONTINUOUS MAPS IS CONTINUOUS, PROVEN -----------
;;;
;;; The notes' Remark 3.32 / the classical 3-epsilon argument, and the half of
;;; ascoli-bridge's CORE B that needs no construction.  Fix a and eps; halve eps
;;; twice to c (4c = eps).  Uniform convergence at tolerance c gives a threshold
;;; cap; take the single member f = fam(cap) -- this is where uniformity is
;;; spent, and where a merely pointwise hypothesis would fail, since f must be
;;; within c of g at BOTH a and b.  Continuity of f at a gives delta.  Then for
;;; d_s(a,b) <= delta,
;;;
;;;   |g(a)-g(b)|  <=  |g(a)-f(a)| + |f(a)-f(b)| + |f(b)-g(b)|  <=  3c  <=  eps,
;;;
;;; the last step needing 0 <= c (acc-nonneg!): three hops under c close a goal
;;; of size 4c only because c is not negative.  `ineq' will not supply that.

(sp (make-wff
  (forall-guarded '(s fam g)
    (list
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(IN g (FUN (PTS s) RR))
      '(FORALL k (IMPLIES (IN k NN) (IS-CONTINUOUS s RR-MS (fam k))))
      '(CONVERGES-UNIFORMLY s fam g))
    '(IS-CONTINUOUS s RR-MS g))))
(acc-peel!)
(dk-split! (dk-landed-1 (lambda () (mac-h 'converges-uniformly '(CONVERGES-UNIFORMLY s fam g)))))
(define acc-UC (car (dk-asms)))          ; the uniform-convergence eps-clause
(define acc-CT (list-ref (dk-asms) 2))   ; k |-> IS-CONTINUOUS s RR-MS (fam k)

;;; the point-universal inside an unfolded IS-CONTINUOUS, instantiated at a.
;;; Discriminated on its CONSEQUENT (IS-CONTINUOUS-AT), never on a symbol.
(define (acc-cont-at! a)
  (acc-inst!
   (acc-find (lambda (f)
               (and (pair? f) (eq? (car f) 'FORALL)
                    (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                    (pair? (caddr (caddr f)))
                    (eq? (car (caddr (caddr f))) 'IS-CONTINUOUS-AT))))
   a))

(define (acc-ulc-finish! a cap del c hh eps)
  (let ((cb  (car (dk-asms)))            ; the delta-clause of f's continuity at a
        (uck (acc-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (eq? (cadr f) 'k))))))
    (ew del)
    (acc-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'POS-RR)
           (ass)
           (let* ((mb (acc-di-landed!)) (b (cadr mb)))   ; (IN b (PTS s))
             (acc-di-landed!)                            ; (<= d_s(a,b) delta)
             (let* ((fc (list 'fam cap))
                    (fa (list fc a)) (fb (list fc b))
                    (ga (list 'g a)) (gb (list 'g b)))
               (fact 'fun-apply-type-c 'fam 'NN (list 'FUN (list 'PTS 's) 'RR) cap)
               (fact 'fun-apply-type-c fc (list 'PTS 's) 'RR a)
               (fact 'fun-apply-type-c fc (list 'PTS 's) 'RR b)
               (fact 'fun-apply-type-c 'g (list 'PTS 's) 'RR a)
               (fact 'fun-apply-type-c 'g (list 'PTS 's) 'RR b)
               ;; the uniform clause is guarded on a CONJUNCTION, which `fact'
               ;; will not split -- assemble it before instantiating.
               (fact 'nn-le-refl cap)
               (have! (list 'AND (list 'IN cap 'NN) (list '<= cap cap)))
               (let ((ux (acc-inst! uck cap)))
                 (acc-inst! ux a)
                 (acc-inst! ux b))
               (mac-h 'rr-ms-dist (acc-inst! cb b))
               (mac 'rr-ms-dist)                         ; arguments typed above
               (acc-tri! ga fa gb)
               (acc-tri! fa fb gb)
               (fact 'rr-abs-sub-sym ga fa)
               (let* ((ab (lambda (u v) (list 'abs (list '- u v))))
                      (prem (list
                             (list '<= (ab ga gb) (list '+ (ab ga fa) (ab fa gb)))
                             (list '<= (ab fa gb) (list '+ (ab fa fb) (ab fb gb)))
                             (list '= (ab ga fa) (ab fa ga))
                             (list '< (ab fa ga) c)
                             (list '< (ab fb gb) c)
                             (list '<= (ab fa fb) c)
                             (list '<= 0 c)
                             (list '= (list '+ c c) hh)
                             (list '= (list '+ hh hh) eps))))
                 (apply ineq (map acc-idx prem))))))))))

(define (acc-ulc-eps! a)
  (let* ((me  (acc-di-landed!)) (eps (cadr me)))
    (acc-pos-in-rr! eps) (acc-nonneg! eps)
    (let* ((hh (acc-halve! eps))
           (c  (acc-halve! hh)))
      (acc-pos-in-rr! hh) (acc-nonneg! hh)
      (acc-pos-in-rr! c)  (acc-nonneg! c)
      (let* ((sk  (acc-skolem! (acc-inst! acc-UC c)))
             (cap (car (cadr sk))))
        (dk-split! (car sk))
        ;; NOTE the hoists: an `inst+' inside the dk-landed-1 thunk would put
        ;; its own chain into the diff, and dk-landed-1 wants exactly one.
        (let ((ct1 (acc-inst! acc-CT cap)))
          (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous ct1)))))
        (let ((cta (acc-cont-at! a)))
          (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous-at cta)))))
        (let* ((sk2 (acc-skolem! (acc-inst! (car (dk-asms)) c)))
               (del (car (cadr sk2))))
          (dk-split! (car sk2))
          (acc-ulc-finish! a cap del c hh eps))))))

;;; IS-METRIC-SPACE(RR-MS) and the PTS(RR-MS) = RR rewrite close the typing
;;; conjuncts of both IS-CONTINUOUS and IS-CONTINUOUS-AT.
(define (acc-ulc-typing! gl)
  (cond ((eq? (car gl) 'IS-METRIC-SPACE)
         (if (eq? (cadr gl) 'RR-MS) (begin (fact 'rr-is-metric-space) (ass)) (ass)))
        ((and (eq? (car gl) 'IN) (equal? (caddr gl) '(PTS s))) (ass))
        (else (slot 'PTS) (ass))))

(mac 'is-continuous)
(acc-and!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (memq (car gl) '(IS-METRIC-SPACE IN))
         (acc-ulc-typing! gl)
         (let* ((ma (acc-di-landed!)) (a (cadr ma)))
           (mac 'is-continuous-at)
           (acc-and!
            (lambda ()
              (let ((g2 (dk-goal)))
                (if (memq (car g2) '(IS-METRIC-SPACE IN))
                    (acc-ulc-typing! g2)
                    (acc-ulc-eps! a))))))))))
(qed 'uniform-limit-continuous)
(topic! 'uniform-limit-continuous 'analysis)
(alias! 'uniform-limit-continuous
        "a uniform limit of continuous maps is continuous")
(gloss! 'uniform-limit-continuous
  "If a sequence of continuous real-valued maps on a metric space converges
   UNIFORMLY to g, then g is continuous.  Classical 3-epsilon: one member of the
   sequence is within eps/4 of g at EVERY point at once, and that member is
   continuous.  Uniformity is spent exactly there -- the same member must
   approximate g at the point and at its neighbour -- which is why the pointwise
   hypothesis does not suffice.  The user's notes, Remark 3.32 and the last line
   of Lemma 3.36; cf. Dieudonne 7.1.")

;;; ---- NOTE: a lemma this arc wanted and the tree does not have -----------
;;;
;;; `CONVERGES(s,f) => IS-CAUCHY-SEQ(s,f)' is nowhere in the tree (grep:
;;; nothing named converges-implies-cauchy or any variant).  Its absence is why
;;; the estimate above has FOUR hops rather than the notes' three: the middle
;;; hop had to be routed through the limit L, at the cost of one extra
;;; triangle instance and one extra symmetry.  In a general metric space it is a
;;; two-hop eps-chain and would cost `metric-dist-real'; at RR-MS it is
;;; unconditional.  A natural PSS entry, and the first consumer is here.
