;;; theorem-library/compact-separable-proof.scm
;;;
;;; compact-metric-is-separable, PROVEN to qed (it was a `reference' support in
;;; structure-library/separable.scm, retired there).
;;;
;;;     IS-COMPACT(s),  (forsome x. x in PTS(s))   =>   IS-SEPARABLE(s)
;;;
;;; The inhabitedness guard is not decoration: the empty metric space is
;;; vacuously compact and has no dense SEQUENCE at all, because FUN is total and
;;; FUN(NN, EMPTY-SET) is empty.  See separable.scm's header.
;;;
;;; THE ROUTE, and where each piece comes from:
;;;
;;;   1. compact => totally bounded            compact-implies-totally-bounded
;;;   2. at scale 1/(k+1) there is a SEQUENCE
;;;      coming 1/(k+1)-close to every point   tb-scale-dense-seq  (separable.scm)
;;;   3. choose one such sequence per scale    dc-on-nn-pred       (dc-on-nn.scm)
;;;   4. collapse the double sequence into
;;;      a single NN-indexed one               nn-flatten          (nn-pairing.scm)
;;;   5. given eps, pick a scale below it      nn-recip-succ-small (order-predicates)
;;;   6. chain the two strict bounds           rr-lt-trans         (order-lemmas)
;;;
;;; Step 2 is the one asserted piece of mathematics, and it is asserted on
;;; purpose: it packages the two steps that are pure plumbing to mechanise --
;;; that the r-net can be taken INSIDE the carrier (neither TOTALLY-BOUNDED nor
;;; finite-ball-subcover-r-net says its net is a subset of PTS(s)), and that a
;;; FINITE net becomes a TOTAL NN-sequence by enumerating it with FIN-ENUM and
;;; padding with x0 outside ORD-SEGMENT(CARD F).  Everything else here is
;;; machine work.  See the warrant on tb-scale-dense-seq.
;;;
;;; Step 3 is where the choice happens, and it is the library's existing
;;; dependent-recursion support rather than a fresh appeal to CHOICE: the step
;;; set NXT(k,u) ignores u and returns the SET of 1/(k+1)-dense sequences, so
;;; "dependent choice with a constant step" IS countable choice.  The base point
;;; is the constant sequence at x0 -- the second use of inhabitedness.
;;;
;;; MECHANICS worth keeping (each cost a probe):
;;;   * `sep-mi' opens its TWO subgoals itself -- it is not an AND that `di'
;;;     then splits.
;;;   * beta-reducing NXT(k, f(k)) in a HYPOTHESIS (`lam-b-h') owes the argument
;;;     typing [k, f(k)] in NN x FUN(NN,PTS s) as an extra leaf; `ci'
;;;     (cartesian-intro) plus fun-apply-type-c discharges it.  This is the
;;;     "lam-b needs the argument TYPED" rule, one level down.
;;;   * `inst+' AUTO-DETACHES when the antecedent is in context, so it lands two
;;;     formulas; take the one no other landing contains (dk-deepest), never
;;;     dk-landed-1.
;;;   * `fact' will not detach rr-lt-trans's AND antecedent -- assemble the
;;;     conjunction with have! first (CLAUDE.md's standing note).
;;;
;;; Loads after nn-pairing (nn-flatten), and so after dc-on-nn, separable,
;;; compactness, order-predicates, order-lemmas and fun-apply-type-proof.

;;; ---- file-local helpers (cs- prefix; the file loads in its own frame) ----

;;; The (NXT k u) application inside a formula.  Found by SHAPE -- do not count
;;; parens through a term this deep.
(define (cs-find-app nxt e)
  (cond ((not (pair? e)) #f)
        ((and (= 3 (length e)) (equal? (car e) nxt)) e)
        (else (let loop ((l e))
                (cond ((not (pair? l)) #f)
                      ((cs-find-app nxt (car l)))
                      (else (loop (cdr l))))))))

;;; The unique context assumption satisfying PRED (errors on a miss: a focus or
;;; lookup helper that returns #f hides every command after it).
(define (cs-asm pred what)
  (or (any-pred pred (dk-asms))
      (error "cs-asm: no assumption" what)))

(define (cs-head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))

;;; Close every leaf a branching tactic just opened, with THUNK deciding by goal.
(define (cs-each-opened tactic each)
  (for-each (lambda (n) (dk-focus! n) (each)) (dk-opened tactic)))

;;; ---- statement ----

(define cs-stmt
  (forall-guarded '(s)
    (list '(IS-COMPACT s)
          '(FORSOME x (IN x (PTS s))))
    '(IS-SEPARABLE s)))

(sp (make-wff cs-stmt))
(dk-peel-to! 'IS-SEPARABLE)

;;; The eigenvariables, read off the context rather than assumed to have kept
;;; their names in the statement.
(define cs-S  (cadr (cs-asm (cs-head? 'IS-COMPACT) "is-compact")))
(define cs-X0 (cadr (dk-landed-1 (lambda () (dk-ai-head! 'FORSOME)))))
(define cs-PTS `(PTS ,cs-S))
(define cs-X   `(FUN NN ,cs-PTS))          ; the space of sequences

;;; ---- what the whole proof needs in context: TB, metric-space, sethood ----

(define cs-TB (dk-fact! 'compact-implies-totally-bounded cs-S))

(have! `(IS-METRIC-SPACE ,cs-S)
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'TOTALLY-BOUNDED cs-TB))))
    (ass)))
(have! `(IN ,cs-PTS SET)
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'IS-METRIC-SPACE
                                              `(IS-METRIC-SPACE ,cs-S)))))
    (ass)))
(have! `(IN ,cs-X SET)                      ; fun-set-iff: both factors are sets
  (lambda ()
    (mac 'fun-set-iff)
    (cs-each-opened (lambda () (di))
                    (lambda ()
                      (if (equal? (dk-goal) '(IN NN SET)) (fact 'nn-is-set))
                      (ass)))))

;;; ---- unfold the goal; its IS-METRIC-SPACE conjunct is now in context ----

(mac 'IS-SEPARABLE)
(cs-each-opened (lambda () (di))
                (lambda () (if (eq? (car (dk-goal)) 'IS-METRIC-SPACE) (ass))))
(dk-focus-goal! "forsome")

;;; ---- the dependent-choice data: base point, step set, totality ----

;;; The constant sequence at x0 -- the dc base point (inhabitedness, use 1 of 2).
(define cs-A `(VNB-LAMBDA n_ NN ,cs-X0))
(have! `(IN ,cs-A ,cs-X)
  (lambda () (dk-lam-t!) (dk-peel-to! 'IN) (ass)))

;;; NXT(k,u) = { g : NN -> PTS(s) | g comes 1/(k+1)-close to every point }.
;;; u is ignored: a constant step turns dependent choice into countable choice.
(define cs-NXT
  `(VNB-LAMBDA (LIST kx ux) (CARTESIAN NN ,cs-X)
     (SEP gx ,cs-X
       ,(forall-guarded '(p) (list `(IN p ,cs-PTS))
          (forsome-guarded 'j '(IN j NN)
            `(< ((DIST ,cs-S) p (gx j)) (recip (+ kx 1))))))))

(define cs-TOT
  (forall-guarded '(k) (list '(IN k NN))
    (forall-guarded '(u) (list `(IN u ,cs-X))
      (forsome-guarded 'y `(IN y ,cs-X) `(IN y ,(list cs-NXT 'k 'u))))))

(have! cs-TOT
  (lambda ()
    (dk-peel-to! 'FORSOME)
    (let* ((app (cs-find-app cs-NXT (dk-goal)))     ; (NXT k u): car is the operator
           (kk  (cadr app))
           (uu  (caddr app))
           (rad `(recip (+ ,kk 1))))
      (fact 'nn-recip-succ-pos kk)                  ; the scale is a positive real
      (let ((ex (dk-fact! 'tb-scale-dense-seq cs-S cs-X0 rad)))
        (dk-split! (dk-landed-1 (lambda () (ai ex))))
        (let ((gg (cadr (cs-asm (lambda (a) (and ((cs-head? 'IN) a)
                                                 (equal? (caddr a) cs-X)
                                                 (not (equal? (cadr a) cs-A))
                                                 (not (eq? (cadr a) uu))))
                                "the chosen dense sequence"))))
          (ew gg)
          (cs-each-opened
            (lambda () (di))
            (lambda ()
              (if (equal? (dk-goal) `(IN ,gg ,cs-X))
                  (ass)
                  (begin (lam-b)                     ; NXT(k,u) -> the SEP
                         (cs-each-opened (lambda () (sep-mi)) ass))))))))))

;;; ---- f : NN -> sequences, with f(succ k) 1/(k+1)-dense; then flatten ----

(define cs-DC (dk-fact! 'dc-on-nn-pred cs-X cs-A cs-NXT))
(dk-split! (dk-landed-1 (lambda () (ai cs-DC))))

(define cs-F
  (cadr (cs-asm (lambda (a) (and ((cs-head? 'IN) a) (equal? (caddr a) `(FUN NN ,cs-X))))
                "the dc sequence f")))
(define cs-STEP
  (cs-asm (lambda (a) (and ((cs-head? 'FORALL) a) (dk-contains? a 'succ)))
          "the dc step law"))

(define cs-FLX (dk-fact! 'nn-flatten cs-PTS cs-F))
(dk-split! (dk-landed-1 (lambda () (ai cs-FLX))))

(define cs-E
  (cadr (cs-asm (lambda (a) (and ((cs-head? 'IN) a) (equal? (caddr a) cs-X)
                                 (symbol? (cadr a)) (not (eq? (cadr a) cs-F))))
                "the flattened sequence e")))
(define cs-FLAT
  (cs-asm (lambda (a) (and ((cs-head? 'FORALL) a) (dk-contains? a cs-E)
                           (dk-contains? a 'FORSOME)))
          "the flattening law"))

;;; ---- e is the dense sequence ----

(ew cs-E)
(cs-each-opened (lambda () (di))
                (lambda () (if (eq? (car (dk-goal)) 'IN) (ass))))
(dk-focus-goal! "forsome")
(dk-peel-to! 'FORSOME)                      ; introduces the point x and eps

(define cs-XX (cadr (cs-asm (lambda (a) (and ((cs-head? 'IN) a)
                                             (equal? (caddr a) cs-PTS)
                                             (not (equal? (cadr a) cs-X0))))
                            "the point x")))
(define cs-EPS (cadr (cs-asm (cs-head? 'POS-RR) "eps")))

;;; A scale below eps, and the dc step at that scale.
(define cs-SM (dk-fact! 'nn-recip-succ-small cs-EPS))
(dk-split! (dk-landed-1 (lambda () (ai cs-SM))))
(define cs-n0
  (cadr (cadr (cadr (cs-asm (lambda (a) (and ((cs-head? '<) a)
                                             (pair? (cadr a))
                                             (eq? (car (cadr a)) 'recip)))
                            "the small scale")))))
(define cs-RAD `(recip (+ ,cs-n0 1)))

(define cs-RED (dk-deepest (lambda () (inst+ cs-STEP cs-n0))))
(define cs-MEM (dk-landed-1 (lambda () (lam-b-h cs-RED))))

;; lam-b-h owes the argument typing [n0, f(n0)] in NN x FUN(NN, PTS s).
(let ((main (proof-state-focus *ps*)))
  (dk-focus-goal! "cartesian")
  (cs-each-opened (lambda () (ci))
                  (lambda ()
                    (if (not (equal? (caddr (dk-goal)) 'NN))
                        (fact 'fun-apply-type-c cs-F 'NN cs-X cs-n0))
                    (ass)))
  (dk-focus! main))

(sep-me cs-MEM)                              ; f(succ n0) IS 1/(n0+1)-dense

;;; The net point near x, its index j, and the index m that hits it in e.
(define cs-PHI
  (cs-asm (lambda (a) (and ((cs-head? 'FORALL) a)
                           (dk-contains? a cs-RAD) (dk-contains? a 'DIST)))
          "the density of f(succ n0)"))
;; inst+ auto-detaches, so it lands two formulas: keep it OUT of the dk-landed-1
;; thunk, which is measuring what the `ai' alone put in the context.
(define cs-NEAREX (dk-deepest (lambda () (inst+ cs-PHI cs-XX))))
(dk-split! (dk-landed-1 (lambda () (ai cs-NEAREX))))

(define cs-NEAR
  (cs-asm (lambda (a) (and ((cs-head? '<) a) (dk-contains? a 'DIST)))
          "the near point"))
(define cs-J  (cadr (caddr (cadr cs-NEAR))))       ; ((DIST s) x ((f (succ n0)) j))
(define cs-PT `((,cs-F (succ ,cs-n0)) ,cs-J))
(define cs-D  `((DIST ,cs-S) ,cs-XX ,cs-PT))

(fact 'nn-succ-closed cs-n0)
(define cs-FL2
  (dk-deepest (lambda ()
                (inst+ (dk-deepest (lambda () (inst+ cs-FLAT `(succ ,cs-n0)))) cs-J))))
(dk-split! (dk-landed-1 (lambda () (ai cs-FL2))))
(define cs-EQ
  (cs-asm (lambda (a) (and ((cs-head? '=) a) (dk-contains? a cs-E)))
          "e(m) = f(succ n0)(j)"))
(define cs-M (cadr (cadr cs-EQ)))

;;; ---- d(x, e(m)) = d(x, f(succ n0)(j)) < 1/(n0+1) < eps ----

(ew cs-M)
(cs-each-opened (lambda () (di))
                (lambda () (if (eq? (car (dk-goal)) 'IN) (ass))))
(dk-focus-goal! "<")
(subst cs-EQ)

(fact 'fun-apply-type-c `(,cs-F (succ ,cs-n0)) 'NN cs-PTS cs-J)
(fact 'metric-dist-real cs-S cs-XX cs-PT)    ; the distance is a real
(fact 'nn-recip-succ-pos cs-n0)
(dk-split! (dk-landed-1 (lambda () (mac-h 'POS-RR `(POS-RR ,cs-RAD)))))
(dk-split! (dk-landed-1 (lambda () (mac-h 'POS-RR `(POS-RR ,cs-EPS)))))

(have! `(AND (< ,cs-D ,cs-RAD) (< ,cs-RAD ,cs-EPS))
       (lambda () (cs-each-opened (lambda () (di)) ass)))
(fact 'rr-lt-trans cs-D cs-RAD cs-EPS)
(ass)

(qed 'compact-metric-is-separable)

(gloss! 'compact-metric-is-separable
  "A compact metric space with at least one point is separable: it has a dense
   sequence.  The inhabitedness hypothesis is not decoration -- the empty metric
   space is compact and has no dense SEQUENCE at all, since FUN(NN, EMPTY-SET) is
   empty; it is separable only in the countable-dense-SUBSET sense, which is not
   the sense IS-SEPARABLE encodes.  Proof: compact => totally bounded, so at each
   scale 1/(k+1) there is a sequence coming that close to every point
   (tb-scale-dense-seq); dependent choice with a constant step picks one per
   scale; nn-flatten re-indexes the resulting double sequence by a single
   natural; and given eps, a scale below eps (nn-recip-succ-small) puts one of
   its terms within eps of any given point.")
(topic! 'compact-metric-is-separable 'topology)
(rests-on 'compact-metric-is-separable '(tb-scale-dense-seq dc-on-nn-pred nn-flatten))
