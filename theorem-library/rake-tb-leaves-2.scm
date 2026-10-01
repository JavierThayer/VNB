;;; rake-tb-leaves-2.scm -- the two totally-bounded leaves that the IS-R-NET
;;; repair of 2026-09-19 unblocked.
;;;
;;;   tb-scale-dense-seq    structure-library/separable.scm:82 (support + warrant!
;;;                         at :90; gloss! at :102 stays), statement UNCHANGED
;;;   tb-rad-ball-cover     theorem-library/cauchy-subsequence.scm:244 (support +
;;;                         warrant! at :264; gloss! at :380 stays), UNCHANGED
;;;
;;; BOTH WERE FALSE UNTIL TODAY, and the defect was not in either statement.  It
;;; was in TOTALLY-BOUNDED, whose net F was bounded only by `(IN (CARD F) NN)'
;;; while every CARD axiom is guarded on sethood, so a proper-class net escaped
;;; the bound entirely.  The counter-model and the user's decision are recorded
;;; at the definition site, structure-library/metric-topology.scm; the repair is
;;; the conjunct `(SUBSET F A)' in IS-R-NET.  What that conjunct buys, and what
;;; these two proofs spend it on, is the sethood of the net:
;;;
;;;     IS-METRIC-SPACE(s)  gives  (IN (PTS s) SET)
;;;     SUBSET F (PTS s)    gives  (IN F SET)        [subclass-of-set-is-set]
;;;
;;; and `(IN F SET)' together with `(IN (CARD F) NN)' is what fin-enum-is-bijection
;;; and centre-set-finite-guarded both demand.
;;;
;;; LOAD WINDOW [structure-library/metric-laws, theorem-library/cauchy-subseq-proof)
;;; -- in load.scm entry numbers, [295, 308).
;;;   lo  is forced by `metric-sym' (structure-library/metric-laws, entry 294),
;;;       the latest citation.  The next latest are `bijection-in-fun' and
;;;       `bijection-surjective' (structure-library/bijection-derived, 289),
;;;       `ball-membership' (theorem-library/rake-balls, 297 -- see NOTE below),
;;;       then card-image-finite (258), rake-inverse-bij (199 --
;;;       fin-enum-is-bijection), subset-lemmas (191, subclass-of-set-is-set and
;;;       subset-mem-fwd), fun-apply-type-proof (160, fun-apply-type-c),
;;;       ord-segment-nn-subset-proof (152), block-family-combinatorial (88,
;;;       IS-FINITE-COVER), structure-library/separable (49), compactness (48),
;;;       order-predicates (39, the `<' and POS-RR definitions), metric-topology
;;;       (27, TOTALLY-BOUNDED / IS-R-NET / BALL), injection.scm (image-set,
;;;       image-membership-iff) and number-systems (nn-is-set).
;;;   NOTE: `ball-membership' (rake-balls, 297) is cited by tb-rad-ball-cover, so
;;;       the true lo is 298.
;;;   hi  is theorem-library/cauchy-subseq-proof (308), the only file that cites
;;;       tb-rad-ball-cover.  tb-scale-dense-seq's only citer is
;;;       theorem-library/compact-separable-proof (458), far above.
;;;       Slot 305 (immediately after theorem-library/rake-tb-leaves) is free and
;;;       is what the integrator should use.
;;; No late tactic is used: `prop', `use-em', `ineq' and the dk- kit only; no
;;; contra / prep / ineq-supply.
;;;
;;; INTEGRATOR: retire
;;;   structure-library/separable.scm:82          support tb-scale-dense-seq
;;;                                  :90          warrant! (keep gloss!/topic!)
;;;   theorem-library/cauchy-subsequence.scm:244  support tb-rad-ball-cover
;;;                                        :264   warrant! (keep gloss!/topic!)
;;; Both warrants describe the net's sethood as a gap to be worked around; with
;;; the 2026-09-19 IS-R-NET conjunct it is not one, so neither text should be
;;; carried into a comment unedited.
;;;
;;; Helper prefix: rt2-.

;;; ---- file-local driver helpers ----------------------------------------

(define (rt2-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-tb-leaves-2: ") (display name)
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
        (error "rake-tb-leaves-2: unfinished proof" name))))

;;; (IN (PTS s) SET) out of IS-METRIC-SPACE(s), in a `have!' LANE -- `mac-h'
;;; REPLACES what it unfolds and the predicate is wanted again afterwards.
;;; (The same three lines as `rkt-pts-in-set!', theorem-library/rake-analysis-
;;; typing.scm:148; that one is local to its own file, as the containment rule
;;; in CLAUDE.md requires, so it is repeated rather than imported.)
(define (rt2-pts-in-set! mm)
  (have! (list 'IN (list 'PTS mm) 'SET)
         (lambda ()
           (dk-split-all!
            (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE mm)))))
           (ass))))

;;; The radius condition TOTALLY-BOUNDED's universal is guarded on, read off
;;; POS-RR in a LANE for the same reason.
(define (rt2-rad-cond! rv)
  (let ((cond_ (list 'AND (list 'IN rv 'RR)
                     (list 'AND (list '<= 0 rv) (list 'NOT (list '= 0 rv))))))
    (have! cond_ (lambda () (mac-h 'POS-RR (list 'POS-RR rv)) (ass)))
    cond_))

;;; Resolve an IF-tower value: `if-true' / `if-false' hand the CONDITION over as
;;; a side goal and leave the main goal untouched, so the value still wants a
;;; `subst'.  CLOSE-COND! discharges the condition branch; VAL is the branch
;;; value the main goal is rewritten to.
(define (rt2-if! ift val close-cond!)
  (let* ((opened (dk-opened (lambda () (if-true ift))))
         (cnd    (cadr ift)))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (equal? (dk-goal) cnd) (close-cond!)
                    (subst (list '= ift val))))
              opened)))

(define (rt2-if-false! ift val close-cond!)
  (let* ((opened (dk-opened (lambda () (if-false ift))))
         (cnd    (list 'NOT (cadr ift))))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (equal? (dk-goal) cnd) (close-cond!)
                    (subst (list '= ift val))))
              opened)))

;;; Focus each leaf a branching step opened, running WHAT on it.
(define (rt2-each! opened what)
  (for-each (lambda (l) (dk-focus! l) (what)) opened))

;;; Does TREE contain SUB anywhere?  Used to tell two sibling goals apart by
;;; the head that occurs in one of them and not in the other.
(define (rt2c-has? tree sub)
  (or (equal? tree sub)
      (and (pair? tree) (any-pred (lambda (t) (rt2c-has? t sub)) tree))))

;;; The unique member of LST satisfying PRED (errors, never returns #f).
(define (rt2c-pick-in lst pred what)
  (let ((hits (filter pred lst)))
    (cond ((null? hits) (error "rt2c: nothing matching" what))
          ((pair? (cdr hits)) (error "rt2c: ambiguous" what))
          (#t (car hits)))))

;;; Peel TWO guarded binders, however `di' chooses to group them.
(define (rt2c-peel2!)
  (let loop ((acc (dk-landed (lambda () (di)))))
    (if (>= (length acc) 2) acc (loop (append acc (dk-landed (lambda () (di))))))))


;;; =======================================================================
;;; tb-scale-dense-seq
;;; =======================================================================
;;;
;;; In a totally bounded space with a point x0, every radius r > 0 admits a
;;; SEQUENCE g : NN -> PTS(s) whose terms come within r of every point.
;;;
;;; THE CONSTRUCTION.  Total boundedness at r gives a finite net F with
;;; SUBSET F (PTS s) (the 2026-09-19 conjunct) and CARD F in NN.  F is a SET
;;; (subclass-of-set-is-set), so FIN-ENUM(F) is a bijection from
;;; ORD-SEGMENT(CARD F) onto F (fin-enum-is-bijection).  That enumeration is
;;; defined only on the segment and FUN is TOTAL, so it is PADDED with x0:
;;;
;;;     g  :=  (VNB-LAMBDA j_ NN (IF (IN j_ ORD-SEGMENT(CARD F))
;;;                                  (FIN-ENUM(F))(j_)
;;;                                  x0))
;;;
;;; Typing is `lam-t' plus an excluded-middle split on the guard: inside the
;;; segment the value is in F, hence in PTS(s); outside it is x0.  Density: the
;;; net gives a centre c within r of p, surjectivity of FIN-ENUM(F) gives an
;;; index z in the segment with FIN-ENUM(F)(z) = c, ord-segment-nn-subset puts z
;;; in NN, and beta + if-true + the equation carry g(z) to c.  The net's clause
;;; is d(c,p), the statement's is d(p, g(z)): one metric-sym.

(sp (make-wff
     (forall-guarded '(s) (list '(TOTALLY-BOUNDED s))
       (forall-guarded '(x0) (list '(IN x0 (PTS s)))
         (forall-guarded '(r) (list '(POS-RR r))
           (forsome-guarded 'g '(IN g (FUN NN (PTS s)))
             (forall-guarded '(p) (list '(IN p (PTS s)))
               (forsome-guarded 'j '(IN j NN)
                 '(< ((DIST s) p (g j)) r)))))))))
(dk-peel!)

;; (1) unfold TOTALLY-BOUNDED and take the net at radius r.
(define rt2-tb
  (dk-split! (dk-landed-1 (lambda () (mac-h 'TOTALLY-BOUNDED '(TOTALLY-BOUNDED s))))))
(define rt2-tb-univ (car (filter (dk-head? 'FORALL) rt2-tb)))
(rt2-rad-cond! 'r)
(define rt2-F (dk-skolem! (dk-apply! rt2-tb-univ 'r)))

;; (2) open the r-net.  Since 2026-09-19 it is a CONJUNCTION: the SUBSET clause
;; and the approximation clause.  One dk-split! on the landing, never a counted di.
(define rt2-net
  (dk-split! (dk-landed-1
              (lambda () (mac-h 'IS-R-NET (list 'IS-R-NET 's rt2-F '(PTS s) 'r))))))
(define rt2-sub   (car (filter (dk-head? 'SUBSET) rt2-net)))
(define rt2-dense (car (filter (dk-head? 'FORALL)  rt2-net)))

;; (3) the sethood the SUBSET clause buys, and the enumeration it unlocks.
(rt2-pts-in-set! 's)
(fact 'subclass-of-set-is-set rt2-F '(PTS s))      ; (IN F SET)
(define rt2-seg  (list 'ORD-SEGMENT (list 'CARD rt2-F)))
(define rt2-enum (list 'FIN-ENUM rt2-F))
(dk-fact! 'fin-enum-is-bijection rt2-F)            ; in BIJECTION(seg, F)
(dk-fact! 'bijection-in-fun rt2-seg rt2-F rt2-enum); in FUN(seg, F)

;; (4) the padded sequence.
(define rt2-g
  (list 'VNB-LAMBDA 'j_ 'NN
        (list 'IF (list 'IN 'j_ rt2-seg) (list rt2-enum 'j_) 'x0)))
(ew rt2-g)

(rt2-each!
 (dk-opened (lambda () (di)))
 (lambda ()
   (if (eq? (car (dk-goal)) 'IN)
       ;; ---- (4a) g is a total function NN -> PTS(s) ----
       (rt2-each!
        (dk-opened (lambda () (lam-t)))
        (lambda ()
          (if (equal? (dk-goal) '(IN NN SET))
              (begin (fact 'nn-is-set) (ass))
              (let* ((iv   (dk-di-var!))
                     (cnd  (list 'IN iv rt2-seg))
                     (ift  (list 'IF cnd (list rt2-enum iv) 'x0)))
                (use-em cnd
                  (lambda ()                           ; inside the segment
                    (rt2-if! ift (list rt2-enum iv) (lambda () (ass)))
                    (dk-fact! 'fun-apply-type-c rt2-enum rt2-seg rt2-F iv)
                    (fact 'subset-mem-fwd rt2-F '(PTS s) (list rt2-enum iv))
                    (ass))
                  (lambda ()                           ; outside: the pad x0
                    (rt2-if-false! ift 'x0 (lambda () (ass)))
                    (ass)))))))
       ;; ---- (4b) every point is within r of some term ----
       (let* ((pv (dk-di-var!))
              (cv (dk-skolem! (dk-apply! rt2-dense pv))))
         (fact 'subset-mem-fwd rt2-F '(PTS s) cv)      ; c in PTS(s)
         (let ((zv (dk-skolem!
                    (dk-fact! 'bijection-surjective rt2-seg rt2-F rt2-enum cv))))
           (fact 'ord-segment-nn-subset (list 'CARD rt2-F) zv)   ; z in NN
           (ew zv)
           (rt2-each!
            (dk-opened (lambda () (di)))
            (lambda ()
              (if (eq? (car (dk-goal)) 'IN)
                  (ass)
                  (let ((ift (list 'IF (list 'IN zv rt2-seg) (list rt2-enum zv) 'x0)))
                    (lam-b)                             ; g(z) -> the IF tower
                    (rt2-if! ift (list rt2-enum zv) (lambda () (ass)))
                    (subst (list '= (list rt2-enum zv) cv))
                    (fact 'metric-sym 's pv cv)         ; d(p,c) = d(c,p)
                    (subst (list '= (list (list 'DIST 's) pv cv)
                                 (list (list 'DIST 's) cv pv)))
                    (mac '<)
                    (dk-conj-close! (lambda () (ass))))))))))))

(rt2-qed! 'tb-scale-dense-seq)
(topic! 'tb-scale-dense-seq 'topology)


;;; =======================================================================
;;; tb-rad-ball-cover
;;; =======================================================================
;;;
;;; The metric-to-combinatorial bridge: a pointwise-positive radius sequence
;;; rad turns total boundedness into a SEQUENCE of finite covers of PTS(s), each
;;; member a rad(k)-ball about a point of PTS(s).
;;;
;;; THE CONSTRUCTION.  The net at level k must be a FUNCTION of k, so it is
;;; named by a choice term rather than obtained by a per-level `obtain':
;;;
;;;   NET(k)  :=  CHOICE { net_ in POWER(PTS s) :
;;;                          CARD(net_) in NN and IS-R-NET(s, net_, PTS(s), rad k) }
;;;   cov     :=  (VNB-LAMBDA k_ NN (IMAGE (VNB-LAMBDA cn_ (PTS s)
;;;                                          (BALL s cn_ (rad k_)))
;;;                                        NET(k_)))
;;;
;;; The separation is over POWER(PTS s) -- and THAT is what the 2026-09-19
;;; IS-R-NET conjunct buys.  Without `SUBSET F (PTS s)' the nets total
;;; boundedness offers need not be subclasses of the carrier, need not be sets,
;;; and there is no set to separate them from; the class of nets could not be
;;; formed, and (see the definition site) the statement below was false anyway.
;;; With it, the net delivered at level k is a member of POWER(PTS s), the
;;; separated class is inhabited, and choice-axiom + sep-me hand back a net with
;;; every property the two conjuncts need.
;;;
;;; The rest is bookkeeping: image-set and card-image-finite make cov(k) a finite
;;; set, the r-net clause plus ball-membership and bu-mi make it cover PTS(s),
;;; and image-membership-iff read backwards identifies its members as balls.

(define (rt2c-netcls radk)
  (list 'SEP 'net_ '(POWER (PTS s))
        (list 'AND (list 'IN (list 'CARD 'net_) 'NN)
              (list 'IS-R-NET 's 'net_ '(PTS s) radk))))
(define (rt2c-fk radk) (list 'CHOICE (rt2c-netcls radk)))
(define (rt2c-bm radk) (list 'VNB-LAMBDA 'cn_ '(PTS s) (list 'BALL 's 'cn_ radk)))
(define rt2c-cov
  (list 'VNB-LAMBDA 'k_ 'NN
        (list 'IMAGE (rt2c-bm '(rad k_)) (rt2c-fk '(rad k_)))))

(sp (make-wff
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL rad
         (IMPLIES (FORALL k (IMPLIES (IN k NN) (POS-RR (rad k))))
           (AND
             (IN (PTS s) SET)
             (FORSOME cov
               (AND
                 (FORALL k
                   (IMPLIES (IN k NN) (IS-FINITE-COVER (cov k) (PTS s))))
                 (FORALL k
                   (IMPLIES (IN k NN)
                     (FORALL U
                       (IMPLIES (IN U (cov k))
                         (FORSOME c
                           (AND (IN c (PTS s))
                                (= U (BALL s c (rad k))))))))))))))))))
(dk-peel!)
(define rt2c-pos (dk-pick (dk-head? 'FORALL) "the rad-positivity universal"))
(define rt2c-tb
  (dk-split! (dk-landed-1 (lambda () (mac-h 'TOTALLY-BOUNDED '(TOTALLY-BOUNDED s))))))
(define rt2c-univ (car (filter (dk-head? 'FORALL) rt2c-tb)))
(rt2-pts-in-set! 's)

;;; The net at one level, forward.  Lands, in the CURRENT branch:
;;;   (IN (CARD NET(k)) NN)   (SUBSET NET(k) (PTS s))   (IN NET(k) SET)
;;; and returns (list NET(k) <the approximation clause of its IS-R-NET>).
(define (rt2c-net! kv anchor)
  (let* ((radk (list 'rad kv))
         (ncls (rt2c-netcls radk))
         (fk   (rt2c-fk radk)))
    ;; ANCHOR.  Several of the steps below hand focus to whatever open leaf the
    ;; kernel's `focus-after-rule' picks, which can be the SIBLING conjunct of
    ;; the goal (found 2026-09-19: the member clause's work was landing on the
    ;; cover clause's leaf).  ANCHOR is a formula in THIS branch's context and in
    ;; no other open leaf, so it names the branch; `stay!' re-focuses on it after
    ;; every step.  CLAUDE.md: never rely on where a tactic leaves focus.
    (let ((stay! (lambda () (dk-focus-ctx! anchor (proof-leaves)))))
    (dk-apply! rt2c-pos kv)                       ; (POS-RR (rad k))
    (stay!)
    ;; (IN (rad k) RR) STANDALONE -- the LUTINS certificate for every later
    ;; instantiation at (rad k); a conjunction does not certify.
    (have! (list 'IN radk 'RR)
           (lambda ()
             (dk-split-all!
              (dk-landed (lambda () (mac-h 'POS-RR (list 'POS-RR radk)))))
             (ass)))
    (stay!)
    (rt2-rad-cond! radk)
    (stay!)
    (let ((wf (dk-skolem! (dk-apply! rt2c-univ radk))))
      (stay!)
      ;; the offered net is a member of POWER(PTS s) -- the SUBSET conjunct.
      ;; Taken in a LANE: mac-h of IS-R-NET would consume the hypothesis the
      ;; sep-mi below still wants.
      (have! (list 'IN wf '(POWER (PTS s)))
        (lambda ()
          (dk-split! (dk-landed-1
                      (lambda () (mac-h 'IS-R-NET (list 'IS-R-NET 's wf '(PTS s) radk)))))
          (fact 'subclass-of-set-is-set wf '(PTS s))
          (mac 'power-set-membership)
          (dk-conj-close!
           (lambda ()
             (if (eq? (car (dk-goal)) 'FORALL)
                 (let ((zv (dk-di-var!)))
                   (fact 'subset-mem-fwd wf '(PTS s) zv)
                   (ass))
                 (ass))))))
      (stay!)
      (have! (list 'IN wf ncls)
        (lambda ()
          (rt2-each! (dk-opened (lambda () (sep-mi)))
                     (lambda () (dk-conj-close! (lambda () (ass)))))))
      (stay!)
      (have! (list 'FORSOME 'net_ (list 'IN 'net_ ncls))
             (lambda () (ew wf) (ass)))
      (stay!)
      (fact 'choice-axiom ncls)                   ; (IN NET(k) ncls)
      (stay!)
      (sep-me (list 'IN fk ncls))
      (stay!)
      (dk-split-all!)
      (stay!)
      (dk-split! (dk-landed-1
                  (lambda () (mac-h 'power-set-membership (list 'IN fk '(POWER (PTS s)))))))
      (stay!)
      (let ((parts (dk-split! (dk-landed-1
                               (lambda () (mac-h 'IS-R-NET (list 'IS-R-NET 's fk '(PTS s) radk)))))))
        (stay!)
        (list fk (car (filter (dk-head? 'FORALL) parts))))))))

(rt2-each!
 (dk-opened (lambda () (di)))
 (lambda ()
   (if (equal? (dk-goal) '(IN (PTS s) SET))
       (ass)
       (begin
         (ew rt2c-cov)
         (rt2-each!
          ;; The MEMBER clause runs FIRST.  It is the only one of the two whose
          ;; peel lands a formula that names its branch -- (IN U (cov k)) -- and
          ;; an anchor is what keeps `focus-after-rule' from carrying the work
          ;; onto the sibling; once it is closed, the cover clause is the only
          ;; open branch and any anchor serves.
          (let ((ls (dk-opened (lambda () (di)))))
            (append (filter (lambda (l) (not (rt2c-has? (dk-goal-of l) 'IS-FINITE-COVER))) ls)
                    (filter (lambda (l) (rt2c-has? (dk-goal-of l) 'IS-FINITE-COVER)) ls)))
          (lambda ()
            (let* ((cover? (if (rt2c-has? (dk-goal) 'IS-FINITE-COVER) #t #f))
                   ;; `di' is GREEDY: on the member clause one call takes the
                   ;; whole FORALL k / IMPLIES / FORALL U / IMPLIES prefix, on
                   ;; the cover clause it stops at IS-FINITE-COVER.  Loop on the
                   ;; LANDING, not on a count.
                   (landed (if cover? (dk-landed (lambda () (di))) (rt2c-peel2!)))
                   (kv   (cadr (rt2c-pick-in landed
                                           (lambda (f) (eq? (caddr f) 'NN))
                                           "(IN k NN)")))
                   (radk (list 'rad kv))
                   (uh   (and (not cover?)
                              (rt2c-pick-in landed
                                          (lambda (f) (not (eq? (caddr f) 'NN)))
                                          "(IN U (cov k))")))
                   (got  (rt2c-net! kv (if cover? (list 'IN kv 'NN) uh)))
                   (fk   (car got))
                   (dense (cadr got))
                   (bm   (rt2c-bm radk))
                   (img  (list 'IMAGE bm fk)))
              (if (not (eq? cover? (if (rt2c-has? (dk-goal) 'IS-FINITE-COVER) #t #f)))
                  (error "rt2c: focus wandered out of the branch; goal is now"
                         (expression->string (dk-goal))))
              (if cover?
                  ;; ---- (1) cov(k) is a finite cover of PTS(s) ----
                  (begin
                    (lam-b)                       ; cov(k) -> IMAGE(bm, NET(k))
                    (mac 'IS-FINITE-COVER)
                    (dk-conj-close!
                     (lambda ()
                       (let ((g (dk-goal)))
                         (cond
                          ((equal? g (list 'IN img 'SET))
                           (fact 'image-set bm fk) (ass))
                          ((equal? g (list 'IN (list 'CARD img) 'NN))
                           (fact 'card-image-finite bm fk) (ass))
                          (#t                      ; PTS(s) subset BIG-UNION
                           (mac 'subset-def)
                           (let* ((pv (dk-di-var!))
                                  (cv (dk-skolem! (dk-apply! dense pv))))
                             (fact 'subset-mem-fwd fk '(PTS s) cv)
                             (rt2-each!
                              (dk-opened (lambda () (bu-mi (list 'BALL 's cv radk))))
                              (lambda ()
                                (if (equal? (cadr (dk-goal)) (list 'BALL 's cv radk))
                                    ;; (IN (BALL s c radk) (IMAGE bm NET(k)))
                                    (begin
                                      (dk-image-goal!)
                                      (ew cv)
                                      (dk-conj-close!
                                       (lambda ()
                                         (if (eq? (car (dk-goal)) 'IN) (ass)
                                             (begin (lam-b) (rfl))))))
                                    ;; (IN p (BALL s c radk))
                                    (begin
                                      (mac 'ball-membership)
                                      (dk-conj-close! (lambda () (ass))))))))))))))
                  ;; ---- (2) every member of cov(k) is a rad(k)-ball ----
                  (let* ((uv  (cadr uh))
                         (im  (dk-landed-1 (lambda () (lam-b-h uh))))
                         (ex  (dk-landed-1 (lambda () (mac-h 'image-membership-iff im))))
                         (cv  (dk-skolem! ex))
                         ;; TYPE THE ARGUMENT FIRST.  `lam-b-h' of the image
                         ;; equation reduces (bm c) and OWES (IN c (PTS s)) --
                         ;; the ball map's domain -- if the typing is not in
                         ;; context when it runs; the owed leaf then sits open
                         ;; to the end of the proof (2026-09-19).
                         (ty  (fact 'subset-mem-fwd fk '(PTS s) cv))
                         (eqf (dk-landed-1
                               (lambda ()
                                 (lam-b-h (dk-pick (lambda (f)
                                                     (and (pair? f) (eq? (car f) '=)
                                                          (equal? (caddr f) uv)))
                                                   "the image equation"))))))
                    (fact 'equality-symmetry (cadr eqf) uv)
                    (ew cv)
                    (dk-conj-close! (lambda () (ass))))))))))))

(rt2-qed! 'tb-rad-ball-cover)
(topic! 'tb-rad-ball-cover 'combinatorial)
