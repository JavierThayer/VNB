;;; finite-ball-subcover-proof.scm -- machine proof of the centre-extraction
;;; lemma  finite-ball-subcover-r-net  (calculus.pdf Prop 3.12, the step that
;;; closes compact => totally bounded), with the choice of centres made
;;; EXPLICIT via the global Hilbert epsilon.  Run:
;;;   ./prover calculus/finite-ball-subcover-proof.scm
;;;
;;; Background: a member of BALL-COVER(s,r) is stored as the SET B(c,r); the map
;;; x |-> B(x,r) is not injective, so recovering "the centre" needs choice.  We
;;; name it: CENTRES(s,B,r) is the centres of B, CHOICE(CENTRES s B r) picks one
;;; (defined because the set is inhabited -- the iota/epsilon proviso), and
;;; CENTRE-SET(s,r,F) = IMAGE(B |-> CHOICE(CENTRES s B r), F) is the chosen
;;; centre set.  Construction + supporting membership/finiteness lemmas live in
;;; structure-library/compactness.scm.
;;;
;;; Two theorems, both to QED:
;;;
;;;   chosen-centre-is-centre  -- the epsilon choice is SOUND: for a cover ball
;;;     U, CHOICE(CENTRES s U r) is in X(s) and B(.,r) = U.  Proof: U in the
;;;     cover makes CENTRES(s,U,r) inhabited (ball-cover-mem-fwd + centres-mem-
;;;     build), so choice-axiom lands the pick in it, and the CENTRES slices give
;;;     both conjuncts.
;;;
;;;   finite-ball-subcover-r-net -- a finite subcover F gives the finite r-net
;;;     CENTRE-SET(s,r,F).  Finiteness is centre-set-finite-guarded; for the r-net
;;;     condition, a point p sits in some cover ball U (open-cover-covers-point),
;;;     whose chosen centre (chosen-centre-is-centre) is in CENTRE-SET
;;;     (centre-set-contains-choice) and within r of p (ball-point-le/ne).
;;;
;;; Forward steps (fact/ai) introduce eigenvariables: the centre of U in the
;;; soundness proof, the subcover, the cover ball about p.  Their MACHINE names
;;; (c_<n>, f_<n>, u_<n>) ride on the global *fresh-counter*, which is monotone
;;; and never reset (expressions.scm G-8), so the exact suffix depends on how
;;; much of the library loaded first -- this file used to run early (c_2, f_3,
;;; u_4) but now runs after ~300 eigenvars.  So we do NOT hard-code the names:
;;; fbsr-eig captures whatever `ai' just minted (the context eigenvar with the
;;; given prefix and the largest numeric suffix) and we reference that.
(define (fbsr-eig prefix)
  (let ((best #f) (bestn -1))
    (for-each
     (lambda (a)
       (for-each
        (lambda (v)
          (let* ((s (symbol->string v)) (i (string-search-forward "_" s 0)))
            (when (and i (> i 0) (< (+ i 1) (string-length s))
                       (string=? (string-head s i) prefix)
                       (char-numeric? (string-ref s (+ i 1))))
              (let ((n (string->number (string-tail s (+ i 1)))))
                (when (and n (> n bestn)) (set! bestn n) (set! best v))))))
        (free-vars a)))
     ;; was (proof-tex--focus-asms): a proof-tex.scm helper that loads 200 entries later (2026-09-14)
     (dk-asms))
    (or best (error "fbsr-eig: no eigenvar with prefix in context" prefix))))

;;; ===== chosen-centre-is-centre =====
(sp (make-wff
  '(FORALL s (FORALL r (FORALL U
     (IMPLIES (IN U (BALL-COVER s r))
       (AND (IN (CHOICE (CENTRES s U r)) (PTS s))
            (= (BALL s (CHOICE (CENTRES s U r)) r) U))))))))
(di)
(fact 'ball-cover-mem-fwd 's 'r 'U)          ; exists c. c in PTS(s) and B(c,r)=U
(ai 1) (ai 1)                                ; eigenvar c* ; c* in PTS(s) ; B(c*,r)=U
(define c* (fbsr-eig "c"))                     ; capture the centre eigenvar ai just minted
(fact 'centres-mem-build 's 'U 'r c*)         ; c* in CENTRES(s,U,r)  (witness of inhabited)
;; 2026-09-18 (LUTINS instantiation): both `bc*'s below instantiate at
;; CHOICE(CENTRES(s,U,r)), and a CHOICE is never certified defined.  Landing
;; the choice membership FORWARD -- which is the same choice-axiom the two
;; `bc*'s reach backward -- puts (IN (CHOICE ...) (CENTRES s U r)) in the
;; context, and `asm-establishes-defined?' reads it off there.  The guard is
;; witnessed by the centre c* the `ai' above minted.
(have! '(FORSOME c (IN c (CENTRES s U r))) (lambda () (ew c*) (ass)))
(fact 'choice-axiom '(CENTRES s U r))
(di)                                          ; split the goal conjunction
;; conjunct 1: CHOICE(CENTRES s U r) in PTS(s)
(bc* 'centres-in-carrier ((b 'u) (r 'r)))     ; -> CHOICE(...) in CENTRES(s,U,r)
(bc* 'choice-axiom ())                        ; -> CENTRES(s,U,r) inhabited
(ew c*) (ass)                                 ;    witnessed by c*
;; conjunct 2: B(s, CHOICE(...), r) = U
(bc* 'centres-ball-eq ())
(bc* 'choice-axiom ())
(ew c*) (ass)
(qed 'chosen-centre-is-centre)

;;; ===== finite-ball-subcover-r-net =====
(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
       (IMPLIES (FORSOME F (AND (SUBSET F (BALL-COVER s r))
                           (AND (IN (CARD F) NN) (IS-OPEN-COVER s F))))
         (FORSOME N (AND (IN (CARD N) NN) (IS-R-NET s N (PTS s) r))))))))))
(di) (di) (di) (di) (di)                      ; peel s,r and move metric/r-cond/exists-F to hyps
(ai 1) (ai 1) (ai 1)                          ; eigenvar f* ; subcover, |f*| in NN, open-cover
(define f* (fbsr-eig "f"))                     ; capture the subcover eigenvar
(ew (list 'CENTRE-SET 's 'r f*))               ; the r-net = chosen centres of f*
;; ----- the sethood chain, established BEFORE the goal's conjunction is split
;; (moved above the split 2026-09-19): conjunct I needs `f* in SET' for
;; centre-set-finite-guarded, and conjunct II now needs it again for the
;; `lam-t' of the choice function.  A `fact' landed inside one branch does not
;; reach its sibling, so the chain is paid once, here.
;;
;; REPOINTED 2026-09-15 (wave 7).  The support `centre-set-finite'
;; (structure-library/compactness.scm:167) is FALSE as written: it has no
;; `F in SET', and CARD is an uninterpreted head that constrains nothing about a
;; proper class F.  Its guarded twin `centre-set-finite-guarded'
;; (theorem-library/card-image-finite.scm) is PROVEN, and the guard costs this
;; proof exactly one sethood lane, which the context already pays for:
;;   PTS(s) is a set                 -- a typing conjunct of IS-METRIC-SPACE(s);
;;   BALL-COVER(s,r) is a set        -- it IS the image of PTS(s) (image-set);
;;   f* SUBSET BALL-COVER(s,r)       -- a premise, so subclass-of-set-is-set
;;                                      (theorem-library/subset-lemmas) types f*.
(have! '(IN (PTS s) SET)
  (lambda ()
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'is-metric-space '(IS-METRIC-SPACE s)))))
    (ass)))
(have! '(IN (BALL-COVER s r) SET)
  (lambda ()
    (mac 'BALL-COVER)                          ; -> (IN (IMAGE LAM (PTS s)) SET)
    (let ((im (cadr (dk-goal))))
      (fact 'image-set (cadr im) (caddr im)))
    (ass)))
(fact 'subclass-of-set-is-set f* '(BALL-COVER s r))   ; (IN f* SET)
(di)                                           ; split the goal conjunction
;; conjunct I: |CENTRE-SET(s,r,f*)| in NN.
(fact 'centre-set-finite-guarded 's 'r f*)
(ass)
;; conjunct II: IS-R-NET(s, CENTRE-SET(s,r,f*), PTS(s), r)
(mac 'IS-R-NET)
(di)                                           ; IS-R-NET is a CONJUNCTION since
                                               ; 2026-09-19: the SUBSET clause,
                                               ; then the approximation clause.
;; ----- II(a): SUBSET(CENTRE-SET(s,r,f*), PTS(s)).
;;
;; The conjunct added to IS-R-NET on 2026-09-19 (structure-library/metric-
;; topology.scm, where the defect it repairs is recorded).  It is free for this
;; construction, which is the point of the repair: the net is the IMAGE of f*
;; under the choice function  B |-> CHOICE(CENTRES(s,B,r)), and
;; `chosen-centre-is-centre' -- proven above in this file -- places every one of
;; those chosen centres in PTS(s).
;;
;; The lane is the one theorem-library/rake-compose-typing.scm:92 uses for
;; ran-subset-codomain: unfold the inclusion pointwise, read the image
;; membership back through `image-membership-iff' as "w is the chosen centre of
;; some ball B of f*", beta-reduce that equation in the HYPOTHESIS (`lam-b-h';
;; B is typed, which is what lam-b needs), flip it with `equality-symmetry' so
;; `subst' can carry the goal from w to the chosen centre, and close by the
;; centre's own typing.  `image-subset-codomain' (structure-library/
;; injection.scm) would say the whole thing in one citation, but it is an
;; UNWARRANTED axiom and would put this proof's bill at trust: none;
;; image-membership-iff, which the route below uses instead, is definitional.
(mac 'CENTRE-SET)                              ; -> SUBSET(IMAGE(lam, f*), PTS(s))
(define fbsr-lam (cadr (cadr (dk-goal))))      ; the choice lambda, COPIED off the
                                               ; goal, never rebuilt by hand
(mac 'subset-def)                              ; -> forall w. w in IMAGE(..) => w in PTS(s)
(define fbsr-mem (dk-landed-1 (lambda () (di))))  ; (IN w (IMAGE lam f*))
(define fbsr-w (cadr fbsr-mem))
(define fbsr-b                                 ; the ball of f* whose centre w is
  (dk-skolem!
   (dk-landed-1 (lambda () (mac-h 'image-membership-iff fbsr-mem)))))
(define fbsr-eq                                ; (= (CHOICE (CENTRES s B r)) w)
  (dk-landed-1
   (lambda ()
     (lam-b-h (dk-pick (lambda (fbsr-f)
                         (and (pair? fbsr-f) (eq? (car fbsr-f) '=)
                              (equal? (caddr fbsr-f) fbsr-w)))
                       "the image-membership equation")))))
(fact 'equality-symmetry (cadr fbsr-eq) fbsr-w) ; (= w (CHOICE (CENTRES s B r)))
(subst (list '= fbsr-w (cadr fbsr-eq)))         ; goal: CHOICE(...) in PTS(s)
(fact 'subset-mem-fwd f* '(BALL-COVER s r) fbsr-b)
(dk-split! (dk-fact! 'chosen-centre-is-centre 's 'r fbsr-b))
(ass)
;; ----- II(b): every point of PTS(s) has a centre of the net within r.
(di) (di)                                      ; fix p ; assume p in PTS(s)
(fact 'open-cover-covers-point 's f* 'p)       ; exists U. U in f* and p in U
(ai 1) (ai 1)                                  ; eigenvar u* ; u* in f* ; p in u*
(define u* (fbsr-eig "u"))                     ; capture the cover-ball eigenvar
(fact 'subset-mem-fwd f* '(BALL-COVER s r) u*) ; u* in BALL-COVER(s,r)
(fact 'chosen-centre-is-centre 's 'r u*)       ; CHOICE(CENTRES s u* r): in PTS(s), B(.,r)=u*
(ai 1)                                          ; split that conjunction
(ew (list 'CHOICE (list 'CENTRES 's u* 'r)))   ; the witnessing centre near p
(di)                                           ; split: membership ; distance
;; c in CENTRE-SET(s,r,f*)
;; centre-set-contains-choice is GUARDED (2026-09-17): its antecedent is now the
;; CONJUNCTION "u* is in the family AND u* has a centre at radius r".  The second
;; conjunct is what makes CHOICE(CENTRES(s,u*,r)) denote at all -- unguarded, the
;; support asserted the definedness of an unspecified term (theorem-library/
;; rake-analysis2.scm's header).  It is free here: chosen-centre-is-centre, cited
;; four lines up, has already put the chosen centre in PTS(s) with BALL(.,r) = u*,
;; which is exactly centres-mem-build's pair of premises.  `fact' will not split a
;; conjunctive antecedent, so the AND is landed before the citation.
(fact 'centres-mem-build 's u* 'r (list 'CHOICE (list 'CENTRES 's u* 'r)))
(have! (list 'FORSOME 'c_ (list 'IN 'c_ (list 'CENTRES 's u* 'r)))
  (lambda () (ew (list 'CHOICE (list 'CENTRES 's u* 'r))) (ass)))
(have! (list 'AND (list 'IN u* f*)
             (list 'FORSOME 'c_ (list 'IN 'c_ (list 'CENTRES 's u* 'r)))))
(fact 'centre-set-contains-choice 's 'r f* u*)
(ass)
;; d(c,p) < r  (split into <= and /=, each forward from the cover ball u*)
(di)
(fact 'ball-point-le 's (list 'CHOICE (list 'CENTRES 's u* 'r)) 'r u* 'p) (ass)
(fact 'ball-point-ne 's (list 'CHOICE (list 'CENTRES 's u* 'r)) 'r u* 'p) (ass)
(qed 'finite-ball-subcover-r-net)
