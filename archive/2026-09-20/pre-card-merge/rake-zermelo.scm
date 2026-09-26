;;; rake-zermelo.scm -- CARD-free Zermelo: every set bijects with an ordinal
;;; segment.  Rung 3 of the Zermelo L1 ladder (zen-step.scm is rungs 1 and 2).
;;;
;;;   zermelo-bijection   forall S in SET.  forsome al in ORD.  forsome phi.
;;;                         phi in BIJECTION(ORD-SEGMENT al, S)
;;;
;;; No CARD anywhere -- which is the point: `well-ordering-principle'
;;; (theorem-library/well-ordering.scm) states the same fact with the ordinal
;;; NAMED as CARD(S), and CARD is axiomatised rather than defined, so that
;;; statement is part of what gives CARD its meaning.  Here the ordinal is
;;; produced, not named.
;;;
;;; THE CONSTRUCTION is ZEN, installed in zen-step.scm by ordinal recursion:
;;; "choose from S something that avoids every value chosen earlier".  Three
;;; facts about it are already proven there, all `modulo 0':
;;;
;;;   zen-step      ZEN(S,al) = CHOICE { y in S : forall c ORD-LT al. ZEN(S,c) /= y }
;;;   zen-hits      that avoid-set inhabited  =>  ZEN(S,al) IS one of its members
;;;   zen-exhausts  S in SET  =>  some ordinal's avoid-set is EMPTY
;;;
;;; The bijection is the enumeration read off ZEN below the LEAST exhausting
;;; ordinal.  Five theorems, in dependency order:
;;;
;;;   zermelo-least-ordinal   the least exhausting ordinal exists: an al whose
;;;                           avoid-set is empty and BELOW which every stage's
;;;                           avoid-set is still inhabited.
;;;   zen-enum-in-fun         below al every stage hits, so the enumeration
;;;                           lambda is in FUN(ORD-SEGMENT al, S)   [lam-t]
;;;   zen-enum-injective      the later of two stages avoids the earlier one
;;;   zen-enum-surjective     at al nothing is left to avoid, so everything in
;;;                           S was already chosen
;;;   zermelo-bijection       the three conjuncts of bijection-membership-iff
;;;
;;; WHY LEASTNESS.  zen-exhausts gives SOME exhausting ordinal; the enumeration
;;; is only total (and only injective) below the FIRST one.  Leastness is got by
;;; `ord-well-ordered' applied to the SET of exhausting ordinals BELOW
;;; succ(al0) -- a SEP over an ordinal segment, hence a set.  The class of ALL
;;; exhausting ordinals would be a COMP and no formula installed in this tree
;;; contains one; the bounded form needs nothing new.
;;;
;;; SURJECTIVITY is the one place the emptiness of the avoid-set at al is used,
;;; and it is used contrapositively: if w in S were missed by every stage below
;;; al, then w would BE a member of the avoid-set at al, which is empty.
;;;
;;; THE SET IS BOUND AS `S', NEVER `X'.  The reader case-folds, so a binder
;;; spelled X is the eigenvariable x of `choice-axiom' and of `ord-well-ordered's
;;; own subset clause; zen-step.scm records the two runs that cost.
;;;
;;; Needs: zen-step.scm (zen-step is not cited directly, zen-hits and
;;; zen-exhausts are), ord-well-ordered-proof.scm, the primitive ordinal shelf
;;; (ordinals.scm), bijection-membership-iff (structure-library/bijection.scm,
;;; `definitional'), interactive + proof-debt + driver-kit.
;;;
;;; LOAD WINDOW [332, end).  lo is forced by theorem-library/zen-step (position
;;; 331, the maximum over the citations); nothing cites these theorems, so no
;;; citer forces hi.
;;;
;;; Helper prefix: r6j-.

;;; ---- the shapes, built by CONSTRUCTOR, never transcribed ---------------
;;; Every formula below that must MATCH something zen-step.scm installed is
;;; built by these, so the two files cannot drift in binder spelling.

;; the avoid-set at bound A over carrier XV: { y in XV : forall c < A. ZEN(XV,c) /= y }
(define (r6j-avoid xv a)
  (list 'SEP 'y_ xv
        (list 'FORALL 'c_ (list 'IMPLIES (list 'ORD-LT 'c_ a)
                                (list 'NOT (list '= (list 'ZEN xv 'c_) 'y_))))))

;; "the avoid-set at A is inhabited" -- the antecedent zen-hits detaches
(define (r6j-inhab xv a) (list 'FORSOME 'x (list 'IN 'x (r6j-avoid xv a))))

;; zen-exhausts' conclusion at XV
(define (r6j-exhausts xv)
  (list 'FORSOME 'alpha
        (list 'AND '(IN alpha ORD) (list 'NOT (r6j-inhab xv 'alpha)))))

;; "every stage strictly below AL still has something to choose"
(define (r6j-below al xv)
  (list 'FORALL 'cz (list 'IMPLIES (list 'ORD-LT 'cz al) (r6j-inhab xv 'cz))))

;; the enumeration itself
(define (r6j-phi al xv)
  (list 'VNB-LAMBDA 'a_ (list 'ORD-SEGMENT al) (list 'ZEN xv 'a_)))

;;; ---- driver helpers ---------------------------------------------------

(define (r6j-find pred lst what)
  (or (any-pred pred lst) (error "rake-zermelo: not found --" what)))
(define (r6j-asm pred what) (r6j-find pred (dk-asms) what))

(define (r6j-subject-of pred lst what) (cadr (r6j-find pred lst what)))
(define (r6j-in? cls) (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) cls))))

(define (r6j-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-zermelo: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (sequent-node-assertion l)))
                    (newline))
                  (proof-leaves))
        (error "rake-zermelo: unfinished" name))))

;; (ORD-LT v b) in context  ->  (IN v ORD), (ORD-LE v b), (NOT (= v b))
(define (r6j-ord-of-lt! v b)
  (fact 'ord-lt-iff v b)
  (ai (list 'IFF (list 'ORD-LT v b)
            (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b)))))
  (detach! (list 'IMPLIES (list 'ORD-LT v b)
                 (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b)))))
  (dk-split! (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b))))
  (fact 'ord-le-closure v b)
  (dk-split! (list 'AND (list 'IN v 'ORD) (list 'IN b 'ORD))))

;; (ORD-LE v b) and (NOT (= v b)) in context  ->  (ORD-LT v b)
(define (r6j-lt-of-le-neq! v b)
  (have! (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b))))
  (fact 'ord-lt-iff v b)
  (ai (list 'IFF (list 'ORD-LT v b)
            (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b)))))
  (detach! (list 'IMPLIES (list 'AND (list 'ORD-LE v b) (list 'NOT (list '= v b)))
                 (list 'ORD-LT v b))))

;; segment membership, both ways.  (IN b ORD) must be in context.
(define (r6j-seg-iff! v b)
  (fact 'ord-segment-membership b v)
  (ai (list 'IFF (list 'IN v (list 'ORD-SEGMENT b)) (list 'ORD-LT v b))))
(define (r6j-seg->lt! v b)
  (r6j-seg-iff! v b)
  (detach! (list 'IMPLIES (list 'IN v (list 'ORD-SEGMENT b)) (list 'ORD-LT v b))))
(define (r6j-lt->seg! v b)
  (r6j-seg-iff! v b)
  (detach! (list 'IMPLIES (list 'ORD-LT v b) (list 'IN v (list 'ORD-SEGMENT b)))))

;; the proven bridge of zen-step.scm:  v ORD-LT succ(b)  <->  v ORD-LE b
(define (r6j-succ-bridge! v b)
  (fact 'ord-lt-succ-iff-le b v)
  (ai (list 'IFF (list 'ORD-LT v (list 'succ_ORD b)) (list 'ORD-LE v b))))

;;; =====================================================================
;;; zermelo-least-ordinal -- the FIRST ordinal at which ZEN runs out.
;;;
;;;   S in SET  |-  forsome al in ORD.  the avoid-set at al is EMPTY,
;;;                 and at every stage strictly below al it is inhabited.
;;;
;;; zen-exhausts hands over SOME exhausting al0.  The exhausting ordinals at
;;; or below al0 form the SET
;;;
;;;     CL = { a in ORD-SEGMENT(succ al0) : the avoid-set at a is empty }
;;;
;;; -- a separation over a set, so `ord-well-ordered' applies to it, and al0
;;; itself witnesses that it is nonempty.  Its least member m is the answer:
;;; anything strictly below m that exhausted would lie in CL (it is below
;;; m <= al0 < succ al0) and so be >= m.
;;;
;;; The antecedent handed to `ord-well-ordered' is taken FROM THE PROVER, not
;;; written out: its subset clause binds `x', and CL carries a bound `x' of its
;;; own inside the inhabitation, so a hand transcription is one capture-rename
;;; away from a formula that matches nothing (zen-step.scm's class-extensionality
;;; note, same trap).
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 'S
           (list 'IMPLIES '(IN S SET)
                 (list 'FORSOME 'al
                       (list 'AND '(IN al ORD)
                             (list 'AND (list 'NOT (r6j-inhab 'S 'al))
                                   (r6j-below 'al 'S))))))))

(define r6j-t1-peel (dk-peel!))
(define r6j-S (r6j-subject-of (r6j-in? 'SET) r6j-t1-peel "the set being enumerated"))

(fact 'zen-exhausts r6j-S)
(define r6j-al0 (dk-skolem! (r6j-exhausts r6j-S)))
(define R6J-SAL (list 'succ_ORD r6j-al0))
(fact 'ord-succ-in r6j-al0)                      ; (IN succ(al0) ORD)
(fact 'ord-succ-above r6j-al0)                   ; (ORD-LT al0 succ(al0))
(r6j-lt->seg! r6j-al0 R6J-SAL)                   ; (IN al0 (ORD-SEGMENT succ(al0)))

(define R6J-CL
  (list 'SEP 'a_ (list 'ORD-SEGMENT R6J-SAL)
        (list 'NOT (r6j-inhab r6j-S 'a_))))

;; membership in CL, from the two facts, and back out again
(define (r6j-cl-intro!)
  (for-each (lambda (l) (dk-focus! l) (ass))
            (dk-opened (lambda () (sep-mi)))))

(fact 'ord-well-ordered R6J-CL)
(define r6j-owo
  (r6j-asm (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'FORSOME)
                            (dk-contains? f R6J-CL)))
           "ord-well-ordered at the class of exhausting ordinals"))

(have! (cadr r6j-owo)
  (lambda ()
    (for-each
     (lambda (l)
       (dk-focus! l)
       (if (eq? (car (dk-goal)) 'FORSOME)
           ;; nonempty: al0 is in CL
           (begin (ew r6j-al0) (r6j-cl-intro!))
           ;; subset of ORD
           (let* ((landed (dk-peel!))
                  (v (r6j-subject-of (r6j-in? R6J-CL) landed "the peeled member of CL")))
             (sep-me (list 'IN v R6J-CL))
             (r6j-seg->lt! v R6J-SAL)
             (r6j-ord-of-lt! v R6J-SAL)
             (ass))))
     (dk-opened (lambda () (di))))))
(detach! r6j-owo)

(define r6j-m (dk-skolem! (caddr r6j-owo)))
(define r6j-least
  (r6j-asm (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                            (pair? (caddr (caddr f)))
                            (eq? (car (caddr (caddr f))) 'ORD-LE)))
           "the leastness of m"))

(sep-me (list 'IN r6j-m R6J-CL))                 ; segment membership + emptiness at m
(r6j-seg->lt! r6j-m R6J-SAL)
(r6j-ord-of-lt! r6j-m R6J-SAL)                   ; (IN m ORD)
(r6j-succ-bridge! r6j-m r6j-al0)
(detach! (list 'IMPLIES (list 'ORD-LT r6j-m R6J-SAL) (list 'ORD-LE r6j-m r6j-al0)))

;; the branch that does the work: nothing below m exhausts
(define (r6j-below-branch!)
  (let* ((landed (dk-peel!))
         (cv (cadr (r6j-find (lambda (f) (and (pair? f) (eq? (car f) 'ORD-LT)))
                             landed "the peeled bound"))))
    (pbc)                                        ; assume the avoid-set at cv is empty
    (r6j-ord-of-lt! cv r6j-m)                    ; (IN cv ORD), (ORD-LE cv m), (NOT (= cv m))
    (have! (list 'AND (list 'ORD-LE cv r6j-m) (list 'ORD-LE r6j-m r6j-al0)))
    (fact 'ord-le-trans cv r6j-m r6j-al0)        ; (ORD-LE cv al0)
    (r6j-succ-bridge! cv r6j-al0)
    (detach! (list 'IMPLIES (list 'ORD-LE cv r6j-al0) (list 'ORD-LT cv R6J-SAL)))
    (r6j-lt->seg! cv R6J-SAL)
    (have! (list 'IN cv R6J-CL) r6j-cl-intro!)
    (dk-apply! r6j-least cv)                     ; (ORD-LE m cv)
    (have! (list 'AND (list 'ORD-LE r6j-m cv) (list 'ORD-LE cv r6j-m)))
    (fact 'ord-le-antisymm r6j-m cv)             ; (= m cv)
    (have! (list '= cv r6j-m) (lambda () (fact 'eq-sym r6j-m cv) (ass)))
    (ai (list 'NOT (list '= cv r6j-m)))))

(ew r6j-m)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'FORALL) (r6j-below-branch!) (ass))))

(r6j-qed! 'zermelo-least-ordinal)
(topic! 'zermelo-least-ordinal 'constructions)

;;; =====================================================================
;;; zen-enum-in-fun -- the enumeration is a set function on the segment.
;;;
;;;   al in ORD,  S in SET,  every stage below al still inhabited
;;;     |-  (VNB-LAMBDA a_ in ORD-SEGMENT(al). ZEN(S,a_))  in  FUN(ORD-SEGMENT al, S)
;;;
;;; `lam-t' opens TWO leaves: the SETHOOD of the domain -- ord-segment-is-set,
;;; landed BEFORE the call so dk-set-close! finds it by `ass' -- and the
;;; pointwise typing, which is zen-hits plus one `sep-me': what ZEN chooses at
;;; a stage with anything left to choose is a member of the avoid-set, and the
;;; avoid-set is a separation of S.
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 'al
       (list 'IMPLIES '(IN al ORD)
         (list 'FORALL 'S
           (list 'IMPLIES '(IN S SET)
             (list 'IMPLIES (r6j-below 'al 'S)
                   (list 'IN (r6j-phi 'al 'S)
                         (list 'FUN '(ORD-SEGMENT al) 'S)))))))))

(define r6j-t2-peel (dk-peel!))
(define r6j-t2-al (r6j-subject-of (r6j-in? 'ORD) r6j-t2-peel "the segment bound"))
(define r6j-t2-S  (r6j-subject-of (r6j-in? 'SET) r6j-t2-peel "the set being enumerated"))
(define r6j-t2-below
  (r6j-find (dk-head? 'FORALL) r6j-t2-peel "the below-al inhabitation hypothesis"))

;; the pointwise typing lane, shared with the injectivity proof:
;; (IN v (ORD-SEGMENT al)) in context  ->  (IN (ZEN S v) S), plus the avoid-set
;; body at v, which is what says v avoids every earlier stage.
(define (r6j-hits! xv below v al)
  (r6j-seg->lt! v al)
  (r6j-ord-of-lt! v al)
  (dk-apply! below v)
  (fact 'zen-hits v xv)
  (sep-me (list 'IN (list 'ZEN xv v) (r6j-avoid xv v))))

(fact 'ord-segment-is-set r6j-t2-al)
(dk-lam-t!)
(let* ((landed (dk-peel!))
       (v (r6j-subject-of (r6j-in? (list 'ORD-SEGMENT r6j-t2-al)) landed
                          "the peeled stage")))
  (r6j-hits! r6j-t2-S r6j-t2-below v r6j-t2-al)
  (ass))

(r6j-qed! 'zen-enum-in-fun)
(topic! 'zen-enum-in-fun 'constructions)

;;; =====================================================================
;;; zen-enum-injective -- two stages below al cannot choose the same thing.
;;;
;;;   al in ORD,  S in SET,  every stage below al still inhabited
;;;     |-  forall a1_, a2_ in ORD-SEGMENT(al).  PHI(a1_) = PHI(a2_) => a1_ = a2_
;;;
;;; ORD-LE is total, so one of the two stages is the later; at the later one
;;; zen-hits says the value chosen avoids every EARLIER value, and the avoid-set
;;; body instantiated at the earlier stage is exactly the disequality wanted.
;;; The second case needs both the disequality and the equation REVERSED, each
;;; its own cut -- `subst' rewrites every occurrence, which is the lesson
;;; zorn-route-two's z2-neq-sym! and zen-step's ze-clash! record.
;;;
;;; `lam-b-h' reduces BOTH redexes of the hypothesis in one call, and it may:
;;; the two arguments are typed in the lambda's own domain by the peel.
;;; =====================================================================

(define (r6j-inj-conj al xv)
  (list 'FORALL 'a1_
    (list 'IMPLIES (list 'IN 'a1_ (list 'ORD-SEGMENT al))
      (list 'FORALL 'a2_
        (list 'IMPLIES (list 'IN 'a2_ (list 'ORD-SEGMENT al))
          (list 'IMPLIES (list '= (list (r6j-phi al xv) 'a1_)
                                  (list (r6j-phi al xv) 'a2_))
                '(= a1_ a2_)))))))

(sp (make-wff
     (list 'FORALL 'al
       (list 'IMPLIES '(IN al ORD)
         (list 'FORALL 'S
           (list 'IMPLIES '(IN S SET)
             (list 'IMPLIES (r6j-below 'al 'S) (r6j-inj-conj 'al 'S))))))))

(define r6j-t3-peel (dk-peel!))
(define r6j-t3-al (r6j-subject-of (r6j-in? 'ORD) r6j-t3-peel "the segment bound"))
(define r6j-t3-S  (r6j-subject-of (r6j-in? 'SET) r6j-t3-peel "the set being enumerated"))
(define r6j-t3-below
  (r6j-find (dk-head? 'FORALL) r6j-t3-peel "the below-al inhabitation hypothesis"))

;; lo < hi below al, and the two stages chose the same element: absurd.
;; FLIP? when the context equation runs hi-to-lo rather than lo-to-hi.
(define (r6j-clash! lo hi flip?)
  (if flip?
      (have! (list 'NOT (list '= lo hi))
        (lambda () (di) (fact 'eq-sym lo hi) (ai (list 'NOT (list '= hi lo))))))
  (r6j-lt-of-le-neq! lo hi)
  (dk-apply! r6j-t3-below hi)
  (fact 'zen-hits hi r6j-t3-S)
  (let ((body (dk-landed-find
               (lambda () (sep-me (list 'IN (list 'ZEN r6j-t3-S hi)
                                        (r6j-avoid r6j-t3-S hi))))
               (dk-head? 'FORALL))))
    (inst+ body lo))
  (if flip? (fact 'eq-sym (list 'ZEN r6j-t3-S hi) (list 'ZEN r6j-t3-S lo)))
  (ai (list 'NOT (list '= (list 'ZEN r6j-t3-S lo) (list 'ZEN r6j-t3-S hi)))))

(let* ((g  (dk-goal))                              ; (= a1 a2)
       (u  (cadr g))
       (v  (caddr g))
       (eq (r6j-find (dk-head? '=) r6j-t3-peel "the applied-lambda equation")))
  (lam-b-h eq)                                     ; both redexes, one call
  (r6j-seg->lt! u r6j-t3-al) (r6j-ord-of-lt! u r6j-t3-al)
  (r6j-seg->lt! v r6j-t3-al) (r6j-ord-of-lt! v r6j-t3-al)
  (pbc)
  (have! (list 'AND (list 'IN u 'ORD) (list 'IN v 'ORD)))
  (fact 'ord-le-total u v)
  (use-cases (list 'OR (list 'ORD-LE u v) (list 'ORD-LE v u))
    (lambda () (r6j-clash! u v #f))
    (lambda () (r6j-clash! v u #t))))

(r6j-qed! 'zen-enum-injective)
(topic! 'zen-enum-injective 'constructions)

;;; =====================================================================
;;; zen-enum-surjective -- at al there is nothing left, so nothing was missed.
;;;
;;;   al in ORD,  S in SET,  the avoid-set at al is EMPTY
;;;     |-  forall w in S.  forsome z in ORD-SEGMENT(al).  PHI(z) = w
;;;
;;; Contrapositive, and that is the whole argument: were w missed by every
;;; stage below al, w would satisfy the avoid-set's own condition at al, so
;;; `sep-mi' would put it IN the avoid-set -- which the hypothesis says is
;;; empty.  No case analysis and no leastness; emptiness at al is used here and
;;; nowhere else.
;;; =====================================================================

(define (r6j-surj-conj al xv)
  (list 'FORALL 'w
    (list 'IMPLIES (list 'IN 'w xv)
      (list 'FORSOME 'z
        (list 'AND (list 'IN 'z (list 'ORD-SEGMENT al))
              (list '= (list (r6j-phi al xv) 'z) 'w))))))

(sp (make-wff
     (list 'FORALL 'al
       (list 'IMPLIES '(IN al ORD)
         (list 'FORALL 'S
           (list 'IMPLIES '(IN S SET)
             (list 'IMPLIES (list 'NOT (r6j-inhab 'S 'al))
                   (r6j-surj-conj 'al 'S))))))))

(define r6j-t4-peel (dk-peel!))
(define r6j-t4-al (r6j-subject-of (r6j-in? 'ORD) r6j-t4-peel "the segment bound"))
(define r6j-t4-S  (r6j-subject-of (r6j-in? 'SET) r6j-t4-peel "the set being enumerated"))
(define r6j-t4-w  (r6j-subject-of (r6j-in? r6j-t4-S) r6j-t4-peel "the element to be hit"))

(define r6j-t4-neg (dk-landed-1 (lambda () (pbc))))   ; NOT (forsome z. ...)
(define R6J-T4-EX (cadr r6j-t4-neg))

;; the avoid-set body at w: every stage below al chose something else -- which
;; is the negated existential, one stage at a time.
(define (r6j-surj-body!)
  (let* ((landed (dk-peel!))
         (cv (cadr (r6j-find (dk-head? 'ORD-LT) landed "the peeled stage"))))
    (r6j-lt->seg! cv r6j-t4-al)                  ; type cv BEFORE the beta
    (di)                                         ; assume ZEN(S,cv) = w
    (have! R6J-T4-EX
      (lambda ()
        (ew cv)
        (dk-conj-close!
         (lambda () (if (eq? (car (dk-goal)) '=) (begin (lam-b) (ass)) (ass))))))
    (ai r6j-t4-neg)))

(have! (list 'IN r6j-t4-w (r6j-avoid r6j-t4-S r6j-t4-al))
  (lambda ()
    (for-each (lambda (l)
                (dk-focus! l)
                (if (eq? (car (dk-goal)) 'IN) (ass) (r6j-surj-body!)))
              (dk-opened (lambda () (sep-mi))))))
(have! (r6j-inhab r6j-t4-S r6j-t4-al) (lambda () (ew r6j-t4-w) (ass)))
(ai (list 'NOT (r6j-inhab r6j-t4-S r6j-t4-al)))

(r6j-qed! 'zen-enum-surjective)
(topic! 'zen-enum-surjective 'constructions)

;;; =====================================================================
;;; zermelo-bijection -- the assembly.
;;;
;;;   S in SET  |-  forsome al in ORD, phi.  phi in BIJECTION(ORD-SEGMENT al, S)
;;;
;;; The least exhausting ordinal is the al; the enumeration lambda is the phi;
;;; `mac' the defining iff BACKWARD on the goal and the three conjuncts are the
;;; three theorems above, cited at (al, S).  The two universal conjuncts share
;;; head and binder shape, so they are told apart by what sits UNDER the guard:
;;; a FORALL (injectivity) or a FORSOME (surjectivity) -- never by position.
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 'S
       (list 'IMPLIES '(IN S SET)
         (list 'FORSOME 'al
           (list 'AND '(IN al ORD)
                 (list 'FORSOME 'phi
                       '(IN phi (BIJECTION (ORD-SEGMENT al) S)))))))))

(define r6j-t5-peel (dk-peel!))
(define r6j-t5-S (r6j-subject-of (r6j-in? 'SET) r6j-t5-peel "the set being enumerated"))

(fact 'zermelo-least-ordinal r6j-t5-S)
(define r6j-t5-al
  (dk-skolem! (list 'FORSOME 'al
                    (list 'AND '(IN al ORD)
                          (list 'AND (list 'NOT (r6j-inhab r6j-t5-S 'al))
                                (r6j-below 'al r6j-t5-S))))))

(define (r6j-bij-conjunct!)
  (let ((g (dk-goal)))
    (if (eq? (car g) 'IN)
        (fact 'zen-enum-in-fun r6j-t5-al r6j-t5-S)
        (if (eq? (car (caddr (caddr g))) 'FORALL)
            (fact 'zen-enum-injective  r6j-t5-al r6j-t5-S)
            (fact 'zen-enum-surjective r6j-t5-al r6j-t5-S)))
    (ass)))

(ew r6j-t5-al)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IN)
       (ass)
       (begin (ew (r6j-phi r6j-t5-al r6j-t5-S))
              (mac 'bijection-membership-iff)
              (dk-conj-close! r6j-bij-conjunct!)))))

(r6j-qed! 'zermelo-bijection)
(topic! 'zermelo-bijection 'constructions)

;;; =====================================================================
;;; WHAT SEPARATES THIS FROM `well-ordering-principle' (asserted,
;;; theorem-library/well-ordering.scm:10, `well-known')
;;;
;;;   well-ordering-principle   forall S in SET. forsome phi.
;;;                               phi in BIJECTION(ORD-SEGMENT(CARD S), S)
;;;   zermelo-bijection         forall S in SET. forsome al in ORD, phi.
;;;                               phi in BIJECTION(ORD-SEGMENT al, S)
;;;
;;; The ONLY difference is that the support NAMES the ordinal `CARD S' where
;;; this theorem produces one.  Everything else -- the bijection, its direction,
;;; the class it lives in -- is character for character the same.  So the gap is
;;; entirely about CARD, and it has two halves.
;;;
;;; (1) AGAINST THE AXIOMATISED CARD.  cardinality.scm states the enumeration
;;;     fact only in the FINITE case: `card-finite-bij' is exactly
;;;     well-ordering-principle guarded on (IN (CARD A) NN).  No axiom in that
;;;     file relates CARD S to an ordinal that bijects with S when S is
;;;     infinite, so zermelo-bijection cannot reach the support at all: al and
;;;     CARD S are, to the theory, two unrelated ordinals.  Dropping the
;;;     finiteness guard from `card-finite-bij' would BE the support (and would
;;;     make it derivable from this theorem only in the sense that the axiom
;;;     asserts it).  The honest reading is the one well-ordering.scm's own
;;;     warrant gives: the support is part of what gives the axiomatised CARD
;;;     its meaning, and no proof of it in terms of that CARD is possible.
;;;
;;; (2) UNDER THE IDENTIFICATION CARD := CARD-STAR.  CARD-STAR (card-defined.scm)
;;;     is the IOTA "least ordinal al such that S bijects with ORD-SEGMENT(al),
;;;     and no smaller one does".  The CARD-STAR form
;;;
;;;         phi in BIJECTION(ORD-SEGMENT (CARD-STAR S), S)
;;;
;;;     is NOT one step from this theorem.  `card*-from-body' (card-finite.scm)
;;;     reduces it to exhibiting cd-body(S, al) for the al produced here, and
;;;     cd-body has two clauses this file does not supply:
;;;
;;;     * DIRECTION.  cd-body's existence clause is BIJECTION(S, ORD-SEGMENT al)
;;;       -- S first -- and zermelo-bijection gives the segment first.  That is
;;;       now ONE citation: `inverse-bij-is-bijection' (rake-inverse-bij.scm,
;;;       proven modulo 0, 2026-09-17).  Note what it costs: INVERSE-BIJ is
;;;       defined by CHOICE, which card-defined.scm's header says Track A exists
;;;       not to need.  That objection has no force on THIS rung -- ZEN is built
;;;       on CHOICE from the start -- but it does mean the inversion cannot be
;;;       reused to keep the finite layer choice-free.
;;;
;;;     * LEASTNESS, and this is the real gap.  cd-body's third clause says no
;;;       beta ORD-LT al bijects with S.  `zermelo-least-ordinal' proves a
;;;       DIFFERENT minimality: al is the least ordinal at which THIS
;;;       enumeration runs out.  Converting one into the other needs ordinal
;;;       pigeonhole -- no injection ORD-SEGMENT(al) -> ORD-SEGMENT(beta) for
;;;       beta ORD-LT al -- and the tree has pigeonhole only for NN segments
;;;       (`pigeonhole-segments', `pigeonhole-segments-gen', an `ni' induction
;;;       on n_ in NN with `succ', not `succ_ORD').  The ordinal statement is a
;;;       theorem in its own right, not a re-indexing of that one.
;;;
;;; (3) THE CHEAP IDENTIFICATION, if it is wanted.  A SEGMENT-FIRST cardinal --
;;;     IOTA al. al in ORD and forsome phi. phi in BIJECTION(ORD-SEGMENT al, S)
;;;     and no smaller ordinal has one -- denotes for EVERY set as soon as
;;;     zermelo-bijection is available, by exactly the argument
;;;     `zermelo-least-ordinal' runs above (bound the candidates by
;;;     ORD-SEGMENT(succ al0), separate, `ord-well-ordered'), with uniqueness by
;;;     cd-body-unique's argument and no pigeonhole anywhere.  Then
;;;     well-ordering-principle is one `subst' away.  What it would break is
;;;     `card-star-segment' (card-defined.scm), whose leastness proof uses
;;;     pigeonhole in the A-first direction and would then need the inverse.
;;;     Direction is therefore the decision to revisit, not the ladder.
;;; =====================================================================
