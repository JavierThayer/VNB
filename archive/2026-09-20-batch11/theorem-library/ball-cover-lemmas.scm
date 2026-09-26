;;; ball-cover-lemmas.scm -- the membership plumbing under
;;; finite-ball-subcover-r-net, PROVEN (2026-09-14).
;;;
;;; calculus/finite-ball-subcover-proof.scm machine-proves
;;; `chosen-centre-is-centre' and `finite-ball-subcover-r-net' but loads AFTER
;;; its citer compact-tb-proof, so both citing bills carry the SUPPORT.  Of the
;;; nine compactness.scm supports that proof cites, eight are membership facts
;;; about SEP / IMAGE / BIG-UNION constructors (class A in the triage); this
;;; file proves seven of them, so that the calculus file, once moved up, bills
;;; only `centre-set-finite' (the finite-image lemma, class B) and
;;; `centre-set-contains-choice' (blocked on definedness, see the end).
;;;
;;; Mechanism, once per constructor: the functoid's unfold EQUATION is a
;;; theorem (`(di) (mac 'X) (qrfl)', the CLAUDE.md recipe), and `mac-h' of that
;;; theorem opens the constructor inside a HYPOTHESIS, where `mac-h' by the
;;; functoid's own name cannot.  Then `sep-me' / `image-membership-iff' /
;;; `bu-me' read the membership apart.
;;;
;;;   centres-unfold, ball-cover-unfold, centre-set-unfold, ball-sep-unfold
;;;                              the four unfold equations
;;;   centres-mem-build          c in PTS(s), B(c,r) = B  =>  c in CENTRES(s,B,r)
;;;   centres-in-carrier         c in CENTRES(s,B,r)  =>  c in PTS(s)
;;;   centres-ball-eq            c in CENTRES(s,B,r)  =>  B(c,r) = B
;;;   ball-cover-mem-fwd         U in BALL-COVER(s,r)  =>  exists c in PTS(s). B(c,r) = U
;;;   open-cover-covers-point    IS-OPEN-COVER(s,F), p in PTS(s)  =>  exists U in F. p in U
;;;   ball-point-le / -ne        p in W, B(c,r) = W  =>  d(c,p) <= r  /  d(c,p) /= r
;;;
;;; Window: [subset-lemmas, compact-tb-proof).  Nothing here cites a theorem
;;; later than the kernel rules and the `image-membership-iff' axiom
;;; (structure-library/injection); the only proven citation is none.  The hi
;;; bound is the citer compact-tb-proof (calculus/), which must follow this file
;;; together with calculus/finite-ball-subcover-proof.  Helper prefix `bcl-'.

(define (bcl-close-all!)                     ; every leaf a branching step opened
  (for-each (lambda (l) (dk-focus! l) (ass)) (proof-leaves)))

;;; ---- the four unfold equations -------------------------------------------

(sp (make-wff '(FORALL s (FORALL B (FORALL r
   (== (CENTRES s B r) (SEP c (PTS s) (= (BALL s c r) B))))))))
(di) (mac 'CENTRES) (qrfl)
(qed 'centres-unfold)
(topic! 'centres-unfold 'plumbing)

(sp (make-wff '(FORALL s (FORALL r
   (== (BALL-COVER s r) (IMAGE (VNB-LAMBDA c (PTS s) (BALL s c r)) (PTS s)))))))
(di) (mac 'BALL-COVER) (qrfl)
(qed 'ball-cover-unfold)
(topic! 'ball-cover-unfold 'plumbing)

(sp (make-wff '(FORALL s (FORALL r (FORALL F
   (== (CENTRE-SET s r F) (IMAGE (VNB-LAMBDA B F (CHOICE (CENTRES s B r))) F)))))))
(di) (mac 'CENTRE-SET) (qrfl)
(qed 'centre-set-unfold)
(topic! 'centre-set-unfold 'plumbing)

(sp (make-wff '(FORALL s (FORALL c (FORALL r
   (== (BALL s c r)
       (SEP y (PTS s) (AND (<= ((DIST s) c y) r) (NOT (= ((DIST s) c y) r))))))))))
(di) (mac 'BALL) (qrfl)
(qed 'ball-sep-unfold)
(topic! 'ball-sep-unfold 'plumbing)

;;; ---- CENTRES: the three SEP slices ----------------------------------------

(sp (make-wff '(FORALL s (FORALL B (FORALL r (FORALL c
   (IMPLIES (IN c (PTS s)) (IMPLIES (= (BALL s c r) B) (IN c (CENTRES s B r))))))))))
(dk-peel!)
(mac 'centres-unfold)
(dk-opened (lambda () (sep-mi)))
(bcl-close-all!)
(qed 'centres-mem-build)

(sp (make-wff '(FORALL s (FORALL B (FORALL r (FORALL c
   (IMPLIES (IN c (CENTRES s B r)) (IN c (PTS s)))))))))
(dk-peel!)
(mac-h 'centres-unfold '(IN c (CENTRES s B r)))
(sep-me '(IN c (SEP c (PTS s) (= (BALL s c r) B))))
(ass)
(qed 'centres-in-carrier)

(sp (make-wff '(FORALL s (FORALL B (FORALL r (FORALL c
   (IMPLIES (IN c (CENTRES s B r)) (= (BALL s c r) B))))))))
(dk-peel!)
(mac-h 'centres-unfold '(IN c (CENTRES s B r)))
(sep-me '(IN c (SEP c (PTS s) (= (BALL s c r) B))))
(ass)
(qed 'centres-ball-eq)

;;; ---- BALL-COVER: a member is a ball about a centre in PTS(s) --------------

(sp (make-wff '(FORALL s (FORALL r (FORALL U
   (IMPLIES (IN U (BALL-COVER s r))
            (FORSOME c (AND (IN c (PTS s)) (= (BALL s c r) U)))))))))
(dk-peel!)
(mac-h 'ball-cover-unfold '(IN U (BALL-COVER s r)))
(let* ((ex (dk-landed-1
            (lambda ()
              (mac-h 'image-membership-iff
                     '(IN U (IMAGE (VNB-LAMBDA c (PTS s) (BALL s c r)) (PTS s)))))))
       (cc (dk-skolem! ex))
       (eq (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                     (pair? (cadr f)) (pair? (car (cadr f)))
                                     (eq? (caar (cadr f)) 'VNB-LAMBDA)))
                    "the applied-lambda equation")))
  (lam-b-h eq)                                ; (BALL s cc r) = U, cc in PTS(s) known
  (ew cc)
  (dk-conj-close!))
(qed 'ball-cover-mem-fwd)

;;; ---- IS-OPEN-COVER: every point lies in some member --------------------

(sp (make-wff '(FORALL s (FORALL F (IMPLIES (IS-OPEN-COVER s F)
   (FORALL p (IMPLIES (IN p (PTS s)) (FORSOME U (AND (IN U F) (IN p U))))))))))
(dk-peel!)
(dk-split-all! (dk-landed (lambda () (mac-h 'is-open-cover '(IS-OPEN-COVER s F)))))
(have! '(IN p (BIG-UNION U F U))
  (lambda () (subst '(== (BIG-UNION U F U) (PTS s))) (ass)))
(let* ((landed (dk-landed (lambda () (bu-me '(IN p (BIG-UNION U F U))))))
       (mem (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'F)
                                      (member f landed)))
                     "the landed index membership")))
  (ew (cadr mem))
  (dk-conj-close!))
(qed 'open-cover-covers-point)

;;; ---- the two ball-point slices --------------------------------------------

(define (bcl-ball-point!)                     ; context: p in W, B(c,r) = W
  (have! '(IN p (BALL s c r)) (lambda () (subst '(= (BALL s c r) W)) (ass)))
  (mac-h 'ball-sep-unfold '(IN p (BALL s c r)))
  (dk-split-all!
   (dk-landed
    (lambda ()
      (sep-me '(IN p (SEP y (PTS s) (AND (<= ((DIST s) c y) r) (NOT (= ((DIST s) c y) r)))))))))
  (ass))

(sp (make-wff '(FORALL s (FORALL c (FORALL r (FORALL W (FORALL p
   (IMPLIES (IN p W) (IMPLIES (= (BALL s c r) W) (<= ((DIST s) c p) r))))))))))
(dk-peel!)
(bcl-ball-point!)
(qed 'ball-point-le)

(sp (make-wff '(FORALL s (FORALL c (FORALL r (FORALL W (FORALL p
   (IMPLIES (IN p W) (IMPLIES (= (BALL s c r) W) (NOT (= ((DIST s) c p) r)))))))))))
(dk-peel!)
(bcl-ball-point!)
(qed 'ball-point-ne)

;;; ---- centre-set-contains-choice: NOT proven here, deliberately -----------
;;;
;;;   U in F  =>  CHOICE(CENTRES s U r) in CENTRE-SET(s, r, F)
;;;
;;; Image intro with witness U and one beta leave  t = t  with
;;; t = CHOICE(CENTRES s U r), and `rfl' closes (= t t) only for a term the
;;; context WITNESSES defined ((IN t _) or (= t _), primitive-inferences.scm
;;; `asm-establishes-defined?'); CHOICE is not a total head.  From `U in F'
;;; alone nothing says CENTRES(s,U,r) is inhabited, so the statement as
;;; written asserts the definedness of an epsilon over a possibly empty class.
;;; With the guard its one citer has in hand -- U in BALL-COVER(s,r), whence
;;; CENTRES(s,U,r) is inhabited (ball-cover-mem-fwd + centres-mem-build) and
;;; choice-axiom lands CHOICE(...) in it -- the same script closes modulo 0
;;; (scratchpad/bcl/csc-probe.scm).  Restating the support is not this file's
;;; call; it stays asserted.
