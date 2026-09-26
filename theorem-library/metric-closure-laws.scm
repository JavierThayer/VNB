;;; metric-closure-laws.scm -- CLOSURE, INTERIOR and the CLOSED BALL.
;;;
;;; The tree DEFINES CLOSURE and INTERIOR (theorem-library/baire-category.scm:10-18)
;;; and proves nothing whatever about them, and it has no closed ball at all.  This
;;; file supplies the missing laws.  Nothing here retires a support: every statement
;;; is new.  (batch 12-F, 2026-09-20.)
;;;
;;; CLOSED-BALL(s, c, r) = { y in PTS(s) : d(s)(c,y) <= r } is a NEW def-functoid;
;;; its text is scratchpad/mcl/closed-ball-def.scm and its home is
;;; structure-library/metric-topology.scm, beside BALL.
;;;
;;; WHAT IS PROVEN, in order (25 theorems, every one `modulo 0'):
;;;
;;;   rr-lt-not-le / rr-not-le-lt    the two missing order bridges: a < b => not(b <= a)
;;;                                  and not(a <= b) => b < a.  HOME: rr-order-basics.
;;;   closed-ball-sep-unfold         the three functoid unfold EQUATIONS, so that
;;;   closure-sep-unfold             `mac-h' can open one inside a hypothesis (a
;;;   interior-sep-unfold            functoid's own name cannot -- CLAUDE.md).
;;;   closed-ball-membership         the three SEP read-offs, as IFFs
;;;   closure-membership
;;;   interior-membership
;;;   closed-ball-is-set
;;;   closure-in-carrier             CLOSURE(s,A) subset PTS(s)
;;;   interior-in-carrier            INTERIOR(s,A) subset PTS(s)
;;;   interior-in-set                INTERIOR(s,A) subset A
;;;   closure-contains               A subset PTS(s) => A subset CLOSURE(s,A)
;;;   ball-in-closed-ball            BALL(s,c,r) subset CLOSED-BALL(s,c,r)
;;;   closed-ball-in-ball            r < q => CLOSED-BALL(s,c,r) subset BALL(s,c,q)
;;;   interior-mem-intro             an open u with x in u subset A puts x in INTERIOR
;;;   interior-is-open               INTERIOR(s,A) is open
;;;   closure-is-closed              CLOSURE(s,A) is closed
;;;   closed-ball-is-closed          a closed ball is closed
;;;   closure-in-closed              C closed, A subset C  =>  CLOSURE(s,A) subset C
;;;   closure-of-ball-in-closed-ball the closure of a ball lies in the closed ball
;;;   closed-set-limit-in            a limit of a sequence inside a closed set is in it
;;;   closure-is-set / interior-is-set
;;;   nowhere-dense-ball-point       A nowhere dense  =>  every ball holds a point
;;;                                  off CLOSURE(s,A)
;;;   nowhere-dense-closed-ball      ... and, below any prescribed bound, a CLOSED
;;;                                  ball inside it missing CLOSURE(s,A).  The Baire step.
;;;
;;; CHECKED AT THE EDGES.  On the EMPTY space every statement is vacuous (the three
;;; separations are empty and the universals over their points are vacuous).  At a
;;; NEGATIVE radius CLOSED-BALL is empty and closed-ball-is-closed still holds --
;;; which is why it is guarded on `r in RR' and not on POS-RR r.  closed-ball-in-ball
;;; needs r < q STRICTLY, and is guarded on the CENTRE lying in PTS(s), without which
;;; nothing types the distance (the `ball-mem-from-le' scar, rake-balls.scm).
;;;
;;; CITATIONS and 0-based load positions over load.scm's file list:
;;;   primitive (library.scm): subset-def, complement-in-membership,
;;;     class-extensionality; number-systems.scm rr-leq-reflexive,
;;;     rr-leq-antisymmetric, rr-leq-total.
;;;   definitional: the is-open / is-closed / converges-to / pos-rr / `<' unfolds;
;;;     the BALL / CLOSURE / INTERIOR / CLOSED-BALL functoid unfolds.
;;;   proven: rr-le-ne-lt (rr-order-basics, 200), rr-pos-rr-in-rr /
;;;     rr-lt-of-pos-rr (pos-rr-bridges, 202), rr-pos-rr-of-lt, rr-lt-diff-pos,
;;;     rr-sub-in-rr (binary-minus-laws, 185), subset-mem-fwd / subset-trans
;;;     (subset-lemmas, 219), complement-in-subset (intersection-of-laws, 243),
;;;     metric-dist-real (op-typing, 259), ball-sep-unfold (ball-cover-lemmas, 339),
;;;     metric-sym / metric-triangle (metric-laws, 342), ball-is-open
;;;     (ball-is-open, 343), ball-membership / ball-is-set / ball-mem-from-le
;;;     (rake-balls, 347).
;;;   The DEFINITIONS of CLOSURE / INTERIOR are in theorem-library/baire-category.scm
;;;   (384), so this file must load after it.
;;;
;;; LOAD WINDOW [385, end).  lo = 385 is forced by baire-category (384), which holds
;;; the CLOSURE / INTERIOR definitions -- every other citation is at 347 or below.
;;; Nothing yet cites anything proven here, so hi is the end of the list; the natural
;;; slot is immediately after baire-category.
;;;
;;; Helper prefix: mcl-.

;;; --- file-local helpers ---------------------------------------------------

(define (mcl-head? f h) (and (pair? f) (eq? (car f) h)))

;;; The CLOSURE / INTERIOR bodies, at an arbitrary point term, spelled with the
;;; DEFINITION's own binders (`u', `y') so that nothing has to be alpha-matched.
(define (mcl-closure-body pt av)
  `(FORALL u (IMPLIES (AND (IS-OPEN s u) (IN ,pt u))
     (FORSOME y (AND (IN y u) (IN y ,av))))))
(define (mcl-interior-body pt av)
  `(FORSOME u (AND (IS-OPEN s u) (AND (IN ,pt u) (SUBSET u ,av)))))

;;; (POS-RR e) in context -> its three atoms and the AND of them, which is the
;;; antecedent ball-is-open / ball-center-in are guarded on (`fact' will not split
;;; a conjunctive antecedent).  Returns that AND.
(define (mcl-pos-parts! e)
  (fact 'rr-pos-rr-in-rr e)
  (let ((lt (dk-fact! 'rr-lt-of-pos-rr e)))
    (dk-split! (dk-landed-1 (lambda () (mac-h '< lt)))))
  (fact 'rr-lt-of-pos-rr e)         ; mac-h CONSUMED (< 0 e); put it back, several
                                    ; citations below want the strict atom itself
  (have-f! `(AND (IN ,e RR) (AND (<= 0 ,e) (NOT (= 0 ,e))))))

;;; (IN z (BALL s c r)) in context -> (IN z (PTS s)), (<= d r), (NOT (= d r)).
(define (mcl-ball-h! mem)
  (dk-split-all! (dk-landed (lambda () (mac-h 'ball-membership mem)))))

;;; =====================================================================
;;; 0.  THE TWO ORDER BRIDGES `rr-lt-not-le' and `rr-not-le-lt' were proven here
;;; (batch 12-F) and MOVED at integration, 2026-09-20, to their home,
;;; theorem-library/rr-order-basics.scm.
;;; =====================================================================

;;; =====================================================================
;;; 1.  THE THREE UNFOLD EQUATIONS
;;; =====================================================================
;;; CLAUDE.md's recipe: a def-functoid installs a rewrite MACETE only, so `mac-h'
;;; cannot open one inside an assumption by the functoid's own name.  The unfold
;;; EQUATION, proven, is what it can name.

(sp (make-wff '(FORALL s (FORALL c (FORALL r
   (== (CLOSED-BALL s c r) (SEP y (PTS s) (<= ((DIST s) c y) r))))))))
(di) (mac 'CLOSED-BALL) (qrfl)
(qed 'closed-ball-sep-unfold)
(topic! 'closed-ball-sep-unfold 'plumbing)

(sp (make-wff '(FORALL s (FORALL A
   (== (CLOSURE s A)
       (SEP x (PTS s)
         (FORALL u (IMPLIES (AND (IS-OPEN s u) (IN x u))
           (FORSOME y (AND (IN y u) (IN y A)))))))))))
(di) (mac 'CLOSURE) (qrfl)
(qed 'closure-sep-unfold)
(topic! 'closure-sep-unfold 'plumbing)

(sp (make-wff '(FORALL s (FORALL A
   (== (INTERIOR s A)
       (SEP x (PTS s)
         (FORSOME u (AND (IS-OPEN s u) (AND (IN x u) (SUBSET u A))))))))))
(di) (mac 'INTERIOR) (qrfl)
(qed 'interior-sep-unfold)
(topic! 'interior-sep-unfold 'plumbing)

;;; =====================================================================
;;; 2.  THE THREE MEMBERSHIP READ-OFFS
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL c (FORALL r (FORALL y
   (IFF (IN y (CLOSED-BALL s c r))
        (AND (IN y (PTS s)) (<= ((DIST s) c y) r)))))))))
(di)
(dk-iff! (dk-head? 'AND)
  (lambda ()
    (mac-h 'closed-ball-sep-unfold '(IN y (CLOSED-BALL s c r)))
    (sep-me '(IN y (SEP y (PTS s) (<= ((DIST s) c y) r))))
    (prop))
  (lambda ()
    (dk-split-all!)
    (mac 'CLOSED-BALL)
    (in-sep! (lambda () (ass)) (lambda () (ass)))))
(qed 'closed-ball-membership)
(gloss! 'closed-ball-membership
  "y lies in CLOSED-BALL(s,c,r) iff y is a point of s with d(s)(c,y) <= r.")
(topic! 'closed-ball-membership 'topology)

(sp (make-wff '(FORALL s (FORALL A (FORALL x
   (IFF (IN x (CLOSURE s A))
        (AND (IN x (PTS s))
             (FORALL u (IMPLIES (AND (IS-OPEN s u) (IN x u))
               (FORSOME y (AND (IN y u) (IN y A))))))))))))
(di)
(dk-iff! (dk-head? 'AND)
  (lambda ()
    (mac-h 'closure-sep-unfold '(IN x (CLOSURE s A)))
    (sep-me '(IN x (SEP x (PTS s)
                     (FORALL u (IMPLIES (AND (IS-OPEN s u) (IN x u))
                       (FORSOME y (AND (IN y u) (IN y A))))))))
    (prop))
  (lambda ()
    (dk-split-all!)
    (mac 'CLOSURE)
    (in-sep! (lambda () (ass)) (lambda () (ass)))))
(qed 'closure-membership)
(gloss! 'closure-membership
  "x lies in CLOSURE(s,A) iff x is a point of s every open neighbourhood of which
   meets A.  The read-off of the closure, in both directions.")
(topic! 'closure-membership 'topology)

(sp (make-wff '(FORALL s (FORALL A (FORALL x
   (IFF (IN x (INTERIOR s A))
        (AND (IN x (PTS s))
             (FORSOME u (AND (IS-OPEN s u) (AND (IN x u) (SUBSET u A)))))))))))
(di)
(dk-iff! (dk-head? 'AND)
  (lambda ()
    (mac-h 'interior-sep-unfold '(IN x (INTERIOR s A)))
    (sep-me '(IN x (SEP x (PTS s)
                     (FORSOME u (AND (IS-OPEN s u) (AND (IN x u) (SUBSET u A)))))))
    (prop))
  (lambda ()
    (dk-split-all!)
    (mac 'INTERIOR)
    (in-sep! (lambda () (ass)) (lambda () (ass)))))
(qed 'interior-membership)
(gloss! 'interior-membership
  "x lies in INTERIOR(s,A) iff x is a point of s with an open neighbourhood
   contained in A.")
(topic! 'interior-membership 'topology)

;;; =====================================================================
;;; 3.  SETHOOD AND THE THREE ELEMENTARY INCLUSIONS
;;; =====================================================================

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL c (FORALL r (IN (CLOSED-BALL s c r) SET)))))))
(dk-peel!)
(mac 'CLOSED-BALL) (sep-set)
(dk-split-all! (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)))))
(ass)
(qed 'closed-ball-is-set)
(topic! 'closed-ball-is-set 'plumbing)

(sp (make-wff '(FORALL s (FORALL A (SUBSET (CLOSURE s A) (PTS s))))))
(di)
(let ((z (subset-by-element!)))
  (dk-split! (dk-landed-1 (lambda () (mac-h 'closure-membership (list 'IN z '(CLOSURE s A))))))
  (ass))
(qed 'closure-in-carrier)
(topic! 'closure-in-carrier 'topology)

(sp (make-wff '(FORALL s (FORALL A (SUBSET (INTERIOR s A) (PTS s))))))
(di)
(let ((z (subset-by-element!)))
  (dk-split! (dk-landed-1 (lambda () (mac-h 'interior-membership (list 'IN z '(INTERIOR s A))))))
  (ass))
(qed 'interior-in-carrier)
(topic! 'interior-in-carrier 'topology)

(sp (make-wff '(FORALL s (FORALL A (SUBSET (INTERIOR s A) A)))))
(di)
(let ((z (subset-by-element!)))
  (dk-split! (dk-landed-1 (lambda () (mac-h 'interior-membership (list 'IN z '(INTERIOR s A))))))
  (let ((uv (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the interior witness"))))
    (fact 'subset-mem-fwd uv 'A z)
    (ass)))
(qed 'interior-in-set)
(gloss! 'interior-in-set
  "The interior of A is contained in A: its points carry an open neighbourhood
   inside A, and lie in it.")
(topic! 'interior-in-set 'topology)

(sp (make-wff '(FORALL s (FORALL A
   (IMPLIES (SUBSET A (PTS s)) (SUBSET A (CLOSURE s A)))))))
(dk-peel!)
(let ((z (subset-by-element!)))
  (mac 'closure-membership)
  (dk-conj-close!
   (lambda ()
     (if (mcl-head? (dk-goal) 'FORALL)
         (begin (dk-split-all! (dk-peel!))
                (ew z)
                (dk-conj-close!))
         ;; NOT `(fact 'subset-mem-fwd 'A '(PTS s) z)': this statement carries no
         ;; IS-METRIC-SPACE(s), so nothing certifies (PTS s) DEFINED and the
         ;; instantiation owes `pts(s) = pts(s)' -- the cold load of 2026-09-20 left
         ;; exactly that leaf open.  Unfold the hypothesis and instantiate at the
         ;; VARIABLE instead.
         (let ((u (dk-landed-1 (lambda () (mac-h 'subset-def '(SUBSET A (PTS s)))))))
           (dk-apply! u z)
           (ass))))))
(qed 'closure-contains)
(gloss! 'closure-contains
  "A set of points is contained in its own closure: each of its points is a witness
   for itself in every neighbourhood it lies in.")
(topic! 'closure-contains 'topology)

;;; =====================================================================
;;; 4.  THE TWO BALLS
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL c (FORALL r
   (SUBSET (BALL s c r) (CLOSED-BALL s c r)))))))
(di)
(let ((z (subset-by-element!)))
  (mcl-ball-h! (list 'IN z '(BALL s c r)))
  (mac 'closed-ball-membership)
  (dk-conj-close!))
(qed 'ball-in-closed-ball)
(gloss! 'ball-in-closed-ball
  "The open r-ball sits inside the closed r-ball -- the strict bound implies the
   non-strict one.  No guard: both sides are separations over PTS(s).")
(topic! 'ball-in-closed-ball 'topology)

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL c (IMPLIES (IN c (PTS s))
       (FORALL r (IMPLIES (IN r RR)
         (FORALL q (IMPLIES (IN q RR)
           (IMPLIES (< r q)
             (SUBSET (CLOSED-BALL s c r) (BALL s c q)))))))))))))
(dk-peel!)
(let ((z (subset-by-element!)))
  (dk-split! (dk-landed-1
              (lambda () (mac-h 'closed-ball-membership (list 'IN z '(CLOSED-BALL s c r))))))
  (fact 'metric-dist-real 's 'c z)
  (let ((d (list (list 'DIST 's) 'c z)))
    (have! (list '< d 'q) (lambda () (dk-ineq! (list '<= d 'r) '(< r q))))
    (dk-split! (dk-landed-1 (lambda () (mac-h '< (list '< d 'q)))))
    (mac 'ball-membership)
    (dk-conj-close!)))
(qed 'closed-ball-in-ball)
(gloss! 'closed-ball-in-ball
  "A closed ball sits inside every strictly larger open ball: d(c,y) <= r < q.
   Guarded on the centre (which is what types the distance) and on both radii.")
(topic! 'closed-ball-in-ball 'topology)

;;; =====================================================================
;;; 5.  THE INTERIOR IS OPEN
;;; =====================================================================

;;; interior-mem-intro -- the one way into an interior: an OPEN u with
;;; x in u subset A.  Curried, so `fact' detaches the three antecedents one at a
;;; time against the live context.
(sp (make-wff '(FORALL s (FORALL A (FORALL u (FORALL x
   (IMPLIES (IS-OPEN s u)
     (IMPLIES (SUBSET u A)
       (IMPLIES (IN x u) (IN x (INTERIOR s A)))))))))))
(dk-peel!)
(have! '(IN x (PTS s))
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-open '(IS-OPEN s u)))))
    (fact 'subset-mem-fwd 'u '(PTS s) 'x)
    (ass)))
(mac 'interior-membership)
(dk-conj-close!
 (lambda ()
   (if (mcl-head? (dk-goal) 'FORSOME)
       (begin (ew 'u) (dk-conj-close!))
       (ass))))
(qed 'interior-mem-intro)
(gloss! 'interior-mem-intro
  "Any open u with x in u and u contained in A puts x in the interior of A.
   Curried antecedents.")
(topic! 'interior-mem-intro 'topology)

;;; The closure universal of an unfolded (IN x (CLOSURE s A)), discriminated on the
;;; SHAPE of its antecedent -- (AND (IS-OPEN s u) (IN x u)).  Head alone is not
;;; enough: ball-center-in's own chain leaves a FORALL/IMPLIES with a conjunctive
;;; antecedent in the context, and a head-only finder picks it (met 2026-09-20).
(define (mcl-closure-univ)
  (dk-pick (lambda (f)
             (and (mcl-head? f 'FORALL) (mcl-head? (caddr f) 'IMPLIES)
                  (let ((ante (cadr (caddr f))))
                    (and (mcl-head? ante 'AND)
                         (mcl-head? (cadr ante) 'IS-OPEN)))))
           "the closure universal"))

;;; The interior universal of an unfolded IS-OPEN, picked by the SET its guard
;;; ranges over -- never by head alone (several are in context at once).
(define (mcl-interior-univ set)
  (dk-pick (lambda (f)
             (and (mcl-head? f 'FORALL) (mcl-head? (caddr f) 'IMPLIES)
                  (let ((ante (cadr (caddr f))))
                    (and (mcl-head? ante 'IN) (equal? (caddr ante) set)))))
           "the interior universal"))

;;; DESTRUCTIVE in (IS-OPEN s u): split it, instantiate its interior universal at
;;; Y, skolemize; return the radius.
(define (mcl-radius! op y)
  (dk-split-all! (dk-landed (lambda () (mac-h 'is-open op))))
  (dk-skolem! (dk-apply! (mcl-interior-univ (caddr op)) y)))

;;; goal: forall y in INTERIOR(s,A). forsome r. POS-RR r and BALL(s,y,r) subset
;;; INTERIOR(s,A).  The witnessing open u of y is open, the ball inside it is open
;;; too, and every point of that ball has the BALL itself as its own witness.
(define (mcl-interior-open!)
  (let* ((mem (car (dk-peel!)))                    ; (IN y (INTERIOR s A))
         (yv  (cadr mem)))
    (dk-split-all! (dk-landed (lambda () (mac-h 'interior-membership mem))))
    (let* ((uv (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the interior witness")))
           (r0 (mcl-radius! (list 'IS-OPEN 's uv) yv))
           (bl (list 'BALL 's yv r0)))
      (mcl-pos-parts! r0)
      (fact 'ball-is-set 's yv r0)
      (fact 'ball-is-open 's yv r0)
      (fact 'subset-trans bl uv 'A)
      (ew r0)
      (dk-conj-close!
       (lambda ()
         (if (mcl-head? (dk-goal) 'POS-RR)
             (ass)
             (let ((w (subset-by-element!)))
               (dk-fact! 'interior-mem-intro 's 'A bl w)
               (ass))))))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IS-OPEN s (INTERIOR s A)))))))
(dk-peel!)
(mac 'is-open)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((mcl-head? g 'IS-METRIC-SPACE) (ass))
           ((mcl-head? g 'SUBSET) (fact 'interior-in-carrier 's 'A) (ass))
           ((mcl-head? g 'FORALL) (mcl-interior-open!))
           (#t (error "interior-is-open: unexpected conjunct"
                      (expression->string g)))))))
(qed 'interior-is-open)
(gloss! 'interior-is-open
  "The interior of any class A is an open subset of the space.")
(topic! 'interior-is-open 'topology)

;;; =====================================================================
;;; 6.  THE CLOSURE IS CLOSED
;;; =====================================================================
;;; The content is in the complement.  y is a point of s OUTSIDE the closure, so
;;; SOME open u holds y and misses A (the negated closure condition, opened with
;;; `push-not-h' -- two alternations, two calls).  A ball of y inside u then misses
;;; the CLOSURE as well: a point w of that ball which lay in the closure would have
;;; to meet A inside the ball itself, and the ball is inside u.

(define (mcl-not-in! f body)                 ; have! (NOT F), proved by refutation
  (have! (list 'NOT f) (lambda () (di) (body) (ai (list 'NOT f)))))

;;; goal (SUBSET (BALL s yv r0) (COMPLEMENT-IN (PTS s) (CLOSURE s A))), with
;;; (SUBSET (BALL s yv r0) uv) and UNIV = forall z in uv. not(z in A) -- the
;;; guarded shape `push-not-h' leaves behind, not the De Morgan conjunction.
(define (mcl-exterior-ball! yv uv r0 univ)
  (let* ((w  (subset-by-element!))
         (bl (list 'BALL 's yv r0)))
    ;; the typing only -- in a LANE, because mac-h CONSUMES the ball membership
    ;; and the membership itself is the guard of the closure universal below.
    (have! (list 'IN w '(PTS s))
           (lambda () (mcl-ball-h! (list 'IN w bl)) (ass)))
    (mcl-not-in! (list 'IN w '(CLOSURE s A))
      (lambda ()
        (dk-split-all!
         (dk-landed (lambda () (mac-h 'closure-membership (list 'IN w '(CLOSURE s A))))))
        (let ((cu (mcl-closure-univ)))
          (have! (list 'AND (list 'IS-OPEN 's bl) (list 'IN w bl)))
          (let ((zv (dk-skolem! (dk-apply! cu bl))))
            (fact 'subset-mem-fwd bl uv zv)
            (dk-apply! univ zv)            ; detaches (IN zv uv): (NOT (IN zv A))
            (ai (list 'NOT (list 'IN zv 'A)))))))
    (mac 'complement-in-membership)
    (dk-conj-close! (lambda () (ass)))))

;;; goal: forall y in PTS(s)\CLOSURE(s,A). forsome r. POS-RR r and
;;; BALL(s,y,r) subset PTS(s)\CLOSURE(s,A).
(define (mcl-closure-exterior!)
  (let* ((mem (car (dk-peel!)))
         (yv  (cadr mem)))
    (dk-split-all! (dk-landed (lambda () (mac-h 'complement-in-membership mem))))
    (let ((neg (list 'NOT (mcl-closure-body yv 'A))))
      (have! neg
        (lambda ()
          (di)
          (have! (list 'IN yv '(CLOSURE s A))
                 (lambda () (mac 'closure-membership) (dk-conj-close!)))
          (ai (list 'NOT (list 'IN yv '(CLOSURE s A))))))
      (push-not-h neg)
      (let ((uv (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the pushed existential"))))
        (push-not-h (dk-pick (lambda (f) (and (mcl-head? f 'NOT)
                                              (mcl-head? (cadr f) 'FORSOME)))
                             "the negated existential"))
        (let* ((univ (dk-pick (lambda (f) (and (mcl-head? f 'FORALL)
                                               (mcl-head? (caddr f) 'IMPLIES)
                                               (mcl-head? (caddr (caddr f)) 'NOT)))
                              "the exterior universal"))
               (r0   (mcl-radius! (list 'IS-OPEN 's uv) yv)))
          (mcl-pos-parts! r0)
          (fact 'ball-is-set 's yv r0)
          (fact 'ball-is-open 's yv r0)
          (ew r0)
          (dk-conj-close!
           (lambda ()
             (if (mcl-head? (dk-goal) 'POS-RR)
                 (ass)
                 (mcl-exterior-ball! yv uv r0 univ)))))))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IS-CLOSED s (CLOSURE s A)))))))
(dk-peel!)
(mac 'is-closed)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((mcl-head? g 'IS-METRIC-SPACE) (ass))
           ((mcl-head? g 'SUBSET) (fact 'closure-in-carrier 's 'A) (ass))
           ((mcl-head? g 'IS-OPEN)
            (mac 'is-open)
            (dk-conj-close!
             (lambda ()
               (let ((h (dk-goal)))
                 (cond ((mcl-head? h 'IS-METRIC-SPACE) (ass))
                       ((mcl-head? h 'SUBSET)
                        (let ((z (subset-by-element!)))
                          (dk-split-all!
                           (dk-landed (lambda () (mac-h 'complement-in-membership
                                                        (list 'IN z (cadr h))))))
                          (ass)))
                       ((mcl-head? h 'FORALL) (mcl-closure-exterior!))
                       (#t (error "closure-is-closed: unexpected inner conjunct"
                                  (expression->string h))))))))
           (#t (error "closure-is-closed: unexpected conjunct"
                      (expression->string g)))))))
(qed 'closure-is-closed)
(gloss! 'closure-is-closed
  "The closure of any class A is a closed subset of the space: a point outside it
   has an open neighbourhood missing A, and a ball inside that neighbourhood misses
   the closure.")
(topic! 'closure-is-closed 'topology)

;;; =====================================================================
;;; 7.  A CLOSED BALL IS CLOSED
;;; =====================================================================
;;; Guarded on r in RR, NOT on POS-RR r: at r < 0 the closed ball is empty and the
;;; statement still holds, and the proof never divides the cases.  A point y with
;;; d(c,y) > r carries the ball of radius t = d(c,y) - r, and the reverse triangle
;;; inequality keeps every point of that ball outside.

;;; goal (SUBSET (BALL s yv t0) (COMPLEMENT-IN (PTS s) (CLOSED-BALL s c r))),
;;; with t0 = d(c,yv) - r and (< r d(c,yv)) in context.
(define (mcl-cball-exterior-ball! yv t0)
  (let* ((w   (subset-by-element!))
         (bl  (list 'BALL 's yv t0))
         (dyw (list (list 'DIST 's) yv w))
         (dwy (list (list 'DIST 's) w yv))
         (dcw (list (list 'DIST 's) 'c w))
         (dcy (list (list 'DIST 's) 'c yv)))
    (mcl-ball-h! (list 'IN w bl))
    (fact 'metric-dist-real 's yv w)
    (fact 'metric-dist-real 's 'c w)
    (fact 'metric-dist-real 's w yv)
    (fact 'metric-sym 's w yv)                       ; d(w,yv) = d(yv,w)
    (fact 'metric-triangle 's 'c w yv)               ; d(c,yv) <= d(c,w) + d(w,yv)
    (have! (list '< dyw t0) (lambda () (mac '<) (from-context!)))
    (have! (list '< 'r dcw)
           (lambda () (dk-ineq! (list '<= dcy (list '+ dcw dwy))
                                (list '= dwy dyw)
                                (list '< dyw t0))))
    (dk-fact! 'rr-lt-not-le 'r dcw)                  ; NOT (d(c,w) <= r)
    (mcl-not-in! (list 'IN w '(CLOSED-BALL s c r))
      (lambda ()
        (dk-split-all!
         (dk-landed (lambda () (mac-h 'closed-ball-membership
                                      (list 'IN w '(CLOSED-BALL s c r))))))
        (ai (list 'NOT (list '<= dcw 'r)))))
    (mac 'complement-in-membership)
    (dk-conj-close! (lambda () (ass)))))

;;; goal: forall y in PTS(s)\CLOSED-BALL(s,c,r). forsome t. POS-RR t and
;;; BALL(s,y,t) subset PTS(s)\CLOSED-BALL(s,c,r).
(define (mcl-cball-exterior!)
  (let* ((mem (car (dk-peel!)))
         (yv  (cadr mem)))
    (dk-split-all! (dk-landed (lambda () (mac-h 'complement-in-membership mem))))
    (fact 'metric-dist-real 's 'c yv)
    (let ((dcy (list (list 'DIST 's) 'c yv)))
      (mcl-not-in! (list '<= dcy 'r)
        (lambda ()
          (have! (list 'IN yv '(CLOSED-BALL s c r))
                 (lambda () (mac 'closed-ball-membership) (dk-conj-close! (lambda () (ass)))))
          (ai (list 'NOT (list 'IN yv '(CLOSED-BALL s c r))))))
      (dk-fact! 'rr-not-le-lt dcy 'r)                ; (< r d(c,yv))
      (dk-fact! 'rr-lt-diff-pos 'r dcy)              ; (< 0 (- d(c,yv) r))
      (fact 'rr-sub-in-rr dcy 'r)
      (let ((t0 (list '- dcy 'r)))
        (dk-fact! 'rr-pos-rr-of-lt t0)
        (ew t0)
        (dk-conj-close!
         (lambda ()
           (if (mcl-head? (dk-goal) 'POS-RR)
               (ass)
               (mcl-cball-exterior-ball! yv t0))))))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL c (IMPLIES (IN c (PTS s))
       (FORALL r (IMPLIES (IN r RR)
         (IS-CLOSED s (CLOSED-BALL s c r))))))))))
(dk-peel!)
(mac 'is-closed)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((mcl-head? g 'IS-METRIC-SPACE) (ass))
           ((mcl-head? g 'SUBSET)
            (let ((z (subset-by-element!)))
              (dk-split! (dk-landed-1
                          (lambda () (mac-h 'closed-ball-membership
                                            (list 'IN z '(CLOSED-BALL s c r))))))
              (ass)))
           ((mcl-head? g 'IS-OPEN)
            (mac 'is-open)
            (dk-conj-close!
             (lambda ()
               (let ((h (dk-goal)))
                 (cond ((mcl-head? h 'IS-METRIC-SPACE) (ass))
                       ((mcl-head? h 'SUBSET)
                        (let ((z (subset-by-element!)))
                          (dk-split-all!
                           (dk-landed (lambda () (mac-h 'complement-in-membership
                                                        (list 'IN z (cadr h))))))
                          (ass)))
                       ((mcl-head? h 'FORALL) (mcl-cball-exterior!))
                       (#t (error "closed-ball-is-closed: unexpected inner conjunct"
                                  (expression->string h))))))))
           (#t (error "closed-ball-is-closed: unexpected conjunct"
                      (expression->string g)))))))
(qed 'closed-ball-is-closed)
(gloss! 'closed-ball-is-closed
  "A closed ball is a closed set.  Guarded on the centre being a point and the
   radius a real -- at a negative radius the ball is empty and the statement still
   holds.")
(topic! 'closed-ball-is-closed 'topology)

;;; =====================================================================
;;; 8.  THE CLOSURE IS THE SMALLEST CLOSED SUPERSET
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL A (FORALL cst
   (IMPLIES (IS-CLOSED s cst)
     (IMPLIES (SUBSET A cst)
       (SUBSET (CLOSURE s A) cst))))))))
(dk-peel!)
(let ((z (subset-by-element!)))
  (dk-split-all! (dk-landed (lambda () (mac-h 'closure-membership
                                              (list 'IN z '(CLOSURE s A))))))
  ;; NAME the closure universal here, before any citation puts another
  ;; FORALL/IMPLIES in the context.
  (let ((cu (mcl-closure-univ)))
  (pbc)                                       ; assume (NOT (IN z cst)); goal FALSITY
  (have! (list 'IN z '(COMPLEMENT-IN (PTS s) cst))
         (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass)))))
  (dk-split-all! (dk-landed (lambda () (mac-h 'is-closed '(IS-CLOSED s cst)))))
  (let* ((comp '(COMPLEMENT-IN (PTS s) cst))
         (r0   (mcl-radius! (list 'IS-OPEN 's comp) z))
         (bl   (list 'BALL 's z r0)))
    (mcl-pos-parts! r0)
    (fact 'ball-is-set 's z r0)
    (fact 'ball-is-open 's z r0)
    (fact 'ball-center-in 's z r0)
    (have! (list 'AND (list 'IS-OPEN 's bl) (list 'IN z bl)))
    (let* ((yv (dk-skolem! (dk-apply! cu bl))))
      (fact 'subset-mem-fwd bl comp yv)
      (fact 'subset-mem-fwd 'A 'cst yv)
      (dk-split-all! (dk-landed (lambda () (mac-h 'complement-in-membership
                                                  (list 'IN yv comp)))))
      (ai (list 'NOT (list 'IN yv 'cst)))))))
(qed 'closure-in-closed)
(gloss! 'closure-in-closed
  "The closure of A is contained in every closed set containing A -- so it is the
   smallest one.  A point of the closure outside a closed C would carry a ball
   inside the complement of C, and that ball must meet A, hence C.")
(topic! 'closure-in-closed 'topology)

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL c (IMPLIES (IN c (PTS s))
       (FORALL r (IMPLIES (IN r RR)
         (SUBSET (CLOSURE s (BALL s c r)) (CLOSED-BALL s c r))))))))))
(dk-peel!)
(fact 'ball-is-set 's 'c 'r)
(fact 'closed-ball-is-set 's 'c 'r)
(fact 'closed-ball-is-closed 's 'c 'r)
(fact 'ball-in-closed-ball 's 'c 'r)
(dk-fact! 'closure-in-closed 's '(BALL s c r) '(CLOSED-BALL s c r))
(ass)
(qed 'closure-of-ball-in-closed-ball)
(gloss! 'closure-of-ball-in-closed-ball
  "The closure of an open ball lies inside the closed ball of the same radius.
   (Equality can fail -- in a discrete space the open 1-ball is a point and the
   closed 1-ball is everything -- so this is the inclusion, not an equation.)")
(topic! 'closure-of-ball-in-closed-ball 'topology)

;;; =====================================================================
;;; 9.  A LIMIT OF A SEQUENCE INSIDE A CLOSED SET STAYS IN IT
;;; =====================================================================
;;; If L were outside A it would sit in the OPEN complement, so some ball about L
;;; would miss A entirely; but the tail of the sequence enters every such ball.
;;; The convergence bound is NON-strict (d(f n, L) <= eps) and ball membership is
;;; STRICT, so the radius is halved (dk-halve!) before it is used.

(define (mcl-univ-with pred what)            ; a FORALL/IMPLIES whose ANTECEDENT fits
  (dk-pick (lambda (f)
             (and (mcl-head? f 'FORALL) (mcl-head? (caddr f) 'IMPLIES)
                  (pred (cadr (caddr f)) (caddr (caddr f)))))
           what))

(sp (make-wff '(FORALL s (FORALL A (FORALL f (FORALL L
   (IMPLIES (IS-CLOSED s A)
     (IMPLIES (CONVERGES-TO s f L)
       (IMPLIES (FORALL n (IMPLIES (IN n NN) (IN (f n) A)))
         (IN L A))))))))))
(dk-peel!)
(dk-split-all! (dk-landed (lambda () (mac-h 'converges-to '(CONVERGES-TO s f L)))))
(let ((cvu (mcl-univ-with (lambda (a c) (mcl-head? a 'POS-RR)) "the convergence universal"))
      (ptw (mcl-univ-with (lambda (a c) (and (mcl-head? a 'IN) (equal? (caddr a) 'NN)
                                             (mcl-head? c 'IN)))
                          "the pointwise membership")))
  (pbc)                                      ; assume (NOT (IN L A)); goal FALSITY
  (have! '(IN L (COMPLEMENT-IN (PTS s) A))
         (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass)))))
  (dk-split-all! (dk-landed (lambda () (mac-h 'is-closed '(IS-CLOSED s A)))))
  (let* ((comp '(COMPLEMENT-IN (PTS s) A))
         (r0   (mcl-radius! (list 'IS-OPEN 's comp) 'L)))
    (mcl-pos-parts! r0)
    (fact 'ball-is-set 's 'L r0)
    (let* ((hlf (dk-halve! r0))
           (nv  (dk-skolem! (dk-apply! cvu hlf)))
           (tail (mcl-univ-with (lambda (a c) (and (mcl-head? a 'IN) (equal? (caddr a) 'NN)
                                                   (mcl-head? c 'IMPLIES)))
                                "the tail universal")))
      (fact 'nn-le-refl nv)
      (dk-apply! tail nv)                    ; (<= ((DIST s) (f nv) L) hlf)
      (dk-apply! ptw nv)                     ; (IN (f nv) A)
      (let* ((fn  (list 'f nv))
             (dfl (list (list 'DIST 's) fn 'L))
             (dlf (list (list 'DIST 's) 'L fn)))
        (fact 'subset-mem-fwd 'A '(PTS s) fn)
        (fact 'metric-dist-real 's fn 'L)
        (fact 'metric-dist-real 's 'L fn)    ; BOTH orientations: `ineq' certifies an
                                             ; atom only from a STANDALONE (IN t RR)
        (fact 'metric-sym 's fn 'L)          ; d(f nv, L) = d(L, f nv)
        (have! (list '<= dlf hlf)
               (lambda () (dk-ineq! (list '= dfl dlf) (list '<= dfl hlf))))
        (have! (list '< hlf r0)
               (lambda () (dk-ineq! (list '= (list '+ hlf hlf) r0) (list '< 0 hlf))))
        (have! (list 'AND (list 'IN fn '(PTS s))
                     (list 'AND (list 'IN hlf 'RR)
                           (list 'AND (list 'IN r0 'RR)
                                 (list 'AND (list '<= dlf hlf) (list '< hlf r0))))))
        (dk-fact! 'ball-mem-from-le 's 'L fn hlf r0)
        (fact 'subset-mem-fwd (list 'BALL 's 'L r0) comp fn)
        (dk-split-all! (dk-landed (lambda () (mac-h 'complement-in-membership
                                                    (list 'IN fn comp)))))
        (ai (list 'NOT (list 'IN fn 'A)))))))
(qed 'closed-set-limit-in)
(gloss! 'closed-set-limit-in
  "A convergent sequence whose terms all lie in a CLOSED set has its limit there
   too.  The characteristic property of closed sets in a metric space.")
(topic! 'closed-set-limit-in 'topology)

;;; =====================================================================
;;; 10.  NOWHERE DENSITY IN TERMS OF BALLS
;;; =====================================================================
;;; Sethood first: CLOSURE and INTERIOR are separations over PTS(s), and their
;;; sethood is what lets a driver INSTANTIATE at them (the LUTINS definedness
;;; certificate wants a typing, CLAUDE.md).

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IN (CLOSURE s A) SET))))))
(dk-peel!)
(mac 'CLOSURE) (sep-set)
(dk-split-all! (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)))))
(ass)
(qed 'closure-is-set)
(topic! 'closure-is-set 'plumbing)

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IN (INTERIOR s A) SET))))))
(dk-peel!)
(mac 'INTERIOR) (sep-set)
(dk-split-all! (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)))))
(ass)
(qed 'interior-is-set)
(topic! 'interior-is-set 'plumbing)

;;; nowhere-dense-ball-point -- the working form of "nowhere dense": EVERY ball of
;;; positive radius holds a point off the CLOSURE of A.  If it did not, the ball
;;; -- open, and holding its own centre -- would put the centre in
;;; INTERIOR(s, CLOSURE(s,A)), which the definition says is empty.
(sp (make-wff '(FORALL s (FORALL A (IMPLIES (IS-NOWHERE-DENSE s A)
     (FORALL c (IMPLIES (IN c (PTS s))
       (FORALL r (IMPLIES (POS-RR r)
         (FORSOME x (AND (IN x (BALL s c r))
                         (NOT (IN x (CLOSURE s A))))))))))))))
(dk-peel!)
(dk-split-all! (dk-landed (lambda () (mac-h 'is-nowhere-dense '(IS-NOWHERE-DENSE s A)))))
(pbc)
(push-not-h (dk-pick (lambda (f) (and (mcl-head? f 'NOT) (mcl-head? (cadr f) 'FORSOME)))
                     "the negated existential"))
(let ((univ (mcl-univ-with (lambda (a c) (and (mcl-head? a 'IN)
                                              (mcl-head? (caddr a) 'BALL)))
                           "the pushed universal")))
  (mcl-pos-parts! 'r)
  (fact 'ball-is-set 's 'c 'r)
  (fact 'closure-is-set 's 'A)
  (fact 'ball-is-open 's 'c 'r)
  (fact 'ball-center-in 's 'c 'r)
  (have! '(SUBSET (BALL s c r) (CLOSURE s A))
         (lambda ()
           (let ((z (subset-by-element!)))
             (dk-apply! univ z)
             (prop))))
  (dk-fact! 'interior-mem-intro 's '(CLOSURE s A) '(BALL s c r) 'c)
  (have! '(IN c EMPTY-SET)
         (lambda () (subst '(= EMPTY-SET (INTERIOR s (CLOSURE s A)))) (ass)))
  (fact 'empty-set-has-no-members 'c)
  (ai '(NOT (IN c EMPTY-SET))))
(qed 'nowhere-dense-ball-point)
(gloss! 'nowhere-dense-ball-point
  "A is nowhere dense exactly when no ball is swallowed by its closure: every ball
   of positive radius contains a point outside CLOSURE(s,A).  This is the forward
   direction, and the form every Baire-style construction uses.")
(topic! 'nowhere-dense-ball-point 'topology)

;;; nowhere-dense-closed-ball -- the Baire step, as a single brick.  Inside any
;;; ball, and under any prescribed bound on the radius, a nowhere-dense A leaves
;;; room for a CLOSED ball that misses its closure entirely.
;;;
;;; The point x off CLOSURE(s,A) inside BALL(s,c,r) comes from
;;; nowhere-dense-ball-point.  Two open sets hold it -- the ball itself and the
;;; complement of the closure, open because the closure is closed -- so two radii
;;; t1, t2 do; m = min(t1,t2), h = m/2, q = min(h, bnd) is then STRICTLY below both,
;;; and closed-ball-in-ball turns that into the two inclusions.  No INTERSECTION
;;; operator is needed: the two radii are taken separately.
(define (mcl-min! u v)                       ; a positive w with w <= u and w <= v
  (dk-skolem! (dk-fact! 'rr-min-pos u v)))

(sp (make-wff '(FORALL s (FORALL A (IMPLIES (IS-NOWHERE-DENSE s A)
   (FORALL c (IMPLIES (IN c (PTS s))
     (FORALL r (IMPLIES (POS-RR r)
       (FORALL bnd (IMPLIES (POS-RR bnd)
         (FORSOME x (AND (IN x (PTS s))
           (FORSOME q (AND (POS-RR q)
             (AND (<= q bnd)
                  (AND (SUBSET (CLOSED-BALL s x q) (BALL s c r))
                       (FORALL z (IMPLIES (IN z (CLOSED-BALL s x q))
                                          (NOT (IN z (CLOSURE s A))))))))))))))))))))))
(dk-peel!)
;; the typing conjunct only, and in a LANE: mac-h CONSUMES the hypothesis, and
;; nowhere-dense-ball-point is cited below with IS-NOWHERE-DENSE as its antecedent.
(have! '(IS-METRIC-SPACE s)
       (lambda ()
         (dk-split-all!
          (dk-landed (lambda () (mac-h 'is-nowhere-dense '(IS-NOWHERE-DENSE s A)))))
         (ass)))
(mcl-pos-parts! 'r)
(mcl-pos-parts! 'bnd)
(fact 'ball-is-set 's 'c 'r)
(fact 'closure-is-set 's 'A)
(fact 'ball-is-open 's 'c 'r)
(let ((xv (dk-skolem! (dk-fact! 'nowhere-dense-ball-point 's 'A 'c 'r))))
  ;; the typing in a LANE: the ball membership itself is the guard mcl-radius!
  ;; detaches below, and mac-h would consume it.
  (have! (list 'IN xv '(PTS s))
         (lambda () (mcl-ball-h! (list 'IN xv '(BALL s c r))) (ass)))
  (let ((comp '(COMPLEMENT-IN (PTS s) (CLOSURE s A))))
    (have! (list 'IN xv comp)
           (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass)))))
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-closed
                                                (dk-fact! 'closure-is-closed 's 'A)))))
    (let* ((t1 (mcl-radius! '(IS-OPEN s (BALL s c r)) xv))
           (t2 (mcl-radius! (list 'IS-OPEN 's comp) xv)))
      (fact 'rr-pos-rr-in-rr t1) (fact 'rr-lt-of-pos-rr t1)
      (fact 'rr-pos-rr-in-rr t2) (fact 'rr-lt-of-pos-rr t2)
      (let* ((mm (mcl-min! t1 t2)))
        (dk-fact! 'rr-pos-rr-of-lt mm)
        (let* ((hh (dk-halve! mm))
               (qq (mcl-min! hh 'bnd)))
          (dk-fact! 'rr-pos-rr-of-lt qq)
          (for-each
           (lambda (rad)
             (have! (list '< qq rad)
                    (lambda () (dk-ineq! (list '<= qq hh) (list '= (list '+ hh hh) mm)
                                         (list '< 0 hh) (list '<= mm rad)))))
           (list t1 t2))
          (fact 'closed-ball-is-set 's xv qq)
          (fact 'ball-is-set 's xv t1)
          (fact 'ball-is-set 's xv t2)
          (dk-fact! 'closed-ball-in-ball 's xv qq t1)
          (dk-fact! 'closed-ball-in-ball 's xv qq t2)
          (let ((cb (list 'CLOSED-BALL 's xv qq)))
            (fact 'subset-trans cb (list 'BALL 's xv t1) '(BALL s c r))
            (fact 'subset-trans cb (list 'BALL 's xv t2) comp)
            (ew xv)
            (dk-conj-close!
             (lambda ()
               (if (not (mcl-head? (dk-goal) 'FORSOME))
                   (ass)
                   (begin
                     (ew qq)
                     (dk-conj-close!
                      (lambda ()
                        (if (not (mcl-head? (dk-goal) 'FORALL))
                            (ass)
                            (let ((zv (cadr (car (dk-peel!)))))
                              (fact 'subset-mem-fwd cb comp zv)
                              (dk-split-all!
                               (dk-landed (lambda () (mac-h 'complement-in-membership
                                                            (list 'IN zv comp)))))
                              (ass)))))))))))))))
(qed 'nowhere-dense-closed-ball)
(gloss! 'nowhere-dense-closed-ball
  "Inside any ball, and below any prescribed positive bound on the radius, a
   nowhere-dense set leaves room for a CLOSED ball missing its closure.  The single
   step of the Baire category construction.")
(topic! 'nowhere-dense-closed-ball 'topology)
