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
;;;     CENTRE-SET(s,r,F).  Finiteness is centre-set-finite; for the r-net
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
     (proof-tex--focus-asms))
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
(di)                                           ; split the goal conjunction
;; conjunct I: |CENTRE-SET(s,r,f*)| in NN
(bc* 'centre-set-finite ((s 's) (r 'r)))
(ass)
;; conjunct II: IS-R-NET(s, CENTRE-SET(s,r,f*), PTS(s), r)
(mac 'IS-R-NET)
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
(bc* 'centre-set-contains-choice ())
(ass)
;; d(c,p) < r  (split into <= and /=, each forward from the cover ball u*)
(di)
(fact 'ball-point-le 's (list 'CHOICE (list 'CENTRES 's u* 'r)) 'r u* 'p) (ass)
(fact 'ball-point-ne 's (list 'CHOICE (list 'CENTRES 's u* 'r)) 'r u* 'p) (ass)
(qed 'finite-ball-subcover-r-net)
