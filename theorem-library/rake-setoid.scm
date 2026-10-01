;;; rake-setoid.scm -- BATCH F of the 2026-09-17 rake: setoids and carriers.
;;; Seven asserted leaves of the PSS, PROVEN.  Every statement here is its
;;; support's statement UNCHANGED.
;;;
;;;   class-is-set        structure-library/setoid.scm:105
;;;   quotient-is-set     structure-library/setoid.scm:161
;;;   proj-in-fun         structure-library/setoid.scm:169
;;;   descend-in-fun      structure-library/setoid.scm:214
;;;   descend2-in-fun     structure-library/setoid.scm:299
;;;   vec-is-set          theorem-library/hahn-banach-full-proof.scm:87   (add-to-pss)
;;;   vspace-vec-is-set   theorem-library/noetherian-maximal-proof.scm:250 (add-to-pss)
;;;
;;; Six auxiliary theorems are installed beside them, one line each:
;;;   class-unfold / proj-unfold / quotient-unfold -- the three functoid
;;;       unfolding EQUATIONS.  `def-functoid' installs a rewrite macete and NO
;;;       theorem, so `mac' unfolds CLASS/PROJ/QUOTIENT in a GOAL and `mac-h'
;;;       cannot unfold them in an ASSUMPTION; the equation is what mac-h
;;;       rebuilds its rule from.  Proved `(di) (mac 'F) (qrfl)' --
;;;       poly-membership.scm's recipe.  `==', not `=': a bare SEP / IMAGE /
;;;       VNB-LAMBDA term is not syntactically defined, so `rfl' would owe a
;;;       definedness witness it does not need.
;;;   respects-unfold / respects2-unfold -- the same for the two functoids whose
;;;       body is a FORMULA, so an IFF rather than an equation, closed by `prop'.
;;;   is-vector-space-unfold -- VECTOR-SPACE is declared `same-shape-as MODULE'
;;;       plus a law, which installs the MACETE `is-vector-space' and no
;;;       theorem; `mac-h 'IS-VECTOR-SPACE' warns "unknown theorem/macete" and
;;;       no-ops, where `mac-h 'IS-RING' and `mac-h 'IS-NORMED-VECTOR-SPACE'
;;;       both work.  The two conjuncts are exactly what `mac' produces.
;;;
;;; THE SHAPES.
;;;   * SEP sethood (class-is-set): `mac' the functoid, `sep-set', and the
;;;     domain sethood is IS-SETOID's own carriers conjunct.
;;;   * IMAGE sethood (quotient-is-set): `image-set' -- replacement, primitive.
;;;   * lambda FUN-typing (proj-in-fun, descend-in-fun, descend2-in-fun): `mac'
;;;     the functoid, `lam-t', close the SETHOOD leaf off the two above, prove
;;;     the pointwise typing.  For PROJ that is one `ew' into
;;;     image-membership-iff.  For DESCEND/DESCEND2 it is the content of the
;;;     batch: a class in the quotient is the image of a representative
;;;     (quotient-unfold, image-membership-iff, one beta on PROJ), and on it
;;;     `iota-d' posts existence-and-uniqueness for the description and then
;;;     GRANTS its defining property.  Existence is a in [a] -- reflexivity of
;;;     REL, projected out of IS-SETOID.  Uniqueness is RESPECTS: every a' in
;;;     [a] has a ~ a', so f(a') = f(a).  With the property granted the value IS
;;;     some f(a'), and fun-apply-type-c types it into Z.
;;;   * a conjunct of a defining IFF (vec-is-set, vspace-vec-is-set): `mac-h'
;;;     the unfold, `dk-split-all!', `ass' -- subtype-laws.scm's stl--project!.
;;;
;;; THE MAC-H TRAP, met twice.  `mac-h' REPLACES the hypothesis it unfolds, so
;;; unfolding IS-SETOID deletes the hypothesis every `fact' guarded on IS-SETOID
;;; needs -- in proj-in-fun the unfold done before `lam-t' left `fact
;;; 'class-is-set' landing the raw universal and `rfl' with no definedness
;;; witness.  Each unfold below therefore happens on the LEAF that needs it and
;;; nowhere earlier; `lam-t' gives its two leaves independent contexts, which is
;;; what makes that free.
;;;
;;; THE CASE FOLD, worth naming once.  descend-in-fun's codomain binder is `Z'
;;; and DESCEND's IOTA binder is `z' -- ONE symbol after the fold.  The pointwise
;;; goal reads `(IN (IOTA z P) z)', the outer z free (the codomain), the inner z
;;; bound; `validate-wff!' says so ("symbol z is both bound and free") and the
;;; formula is nonetheless the intended one, the kernel keeping the two apart.
;;; Nothing below names either by hand: every term is read off the goal.
;;;
;;; LOAD WINDOW [166, 442).
;;;   lo = 166: the latest citation is `pair-in-cartesian'
;;;             (theorem-library/pair-tuple-sethood, position 165).  Next latest
;;;             are fun-apply-type-c (theorem-library/fun-apply-type-proof, 163),
;;;             driver-kit (140), interactive (136), image-set and
;;;             image-membership-iff (structure-library/injection, 83),
;;;             structure-library/normed-vector-space (63),
;;;             structure-library/module (54), structure-library/setoid (25),
;;;             and apply-tupling-2 / cartesian-set-iff (the base theory, 15).
;;;   hi = 442: theorem-library/noetherian-maximal-proof (442) asserts
;;;             vspace-vec-is-set at :250 and cites it at :295;
;;;             theorem-library/hahn-banach-full-proof (443) does the same for
;;;             vec-is-set at :87 / :331.  NOTHING else in the tree cites any of
;;;             the seven, so the five setoid leaves alone would want
;;;             [166, end).  One file suffices: 166 < 442.
;;;
;;; Helper prefix `rks-'.  All helpers are file-local.

(define (rks-hyp h what) (dk-pick (dk-head? h) what))
(define (rks-find pred what) (dk-pick pred what))
(define (rks-in-head h)
  (lambda (f) (and (pair? f) (eq? (car f) 'IN) (pair? (caddr f))
                   (eq? (car (caddr f)) h))))
(define (rks-goal-head? n h) (eq? (car (dk-goal-of n)) h))
(define (rks-set-leaf? n)
  (let ((g (dk-goal-of n)))
    (and (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
(define (rks-eq-to c)
  (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (caddr f) c))))

;; The reflexivity conjunct of is-equivalence, by SHAPE:
;;   (FORALL u (IMPLIES (IN u crr) (IN (LIST u u) rho)))
;; Discriminated on the CONSEQUENT (the repeated variable in the pair), never on
;; a symbol it contains -- symmetry and transitivity mention the same ones.
(define (rks-refl-shape? f)
  (and (pair? f) (eq? (car f) 'FORALL)
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES)
              (let ((cq (caddr b)))
                (and (pair? cq) (eq? (car cq) 'IN)
                     (pair? (cadr cq)) (eq? (car (cadr cq)) 'LIST)
                     (= (length (cadr cq)) 3)
                     (eq? (cadr (cadr cq)) (caddr (cadr cq)))))))))

;; goal (RELATED s a a).  DESTRUCTIVE -- it unfolds IS-SETOID, so it is only
;; ever called on a leaf that needs nothing else from it.
(define (rks-related-refl! a)
  (mac-h 'IS-SETOID (rks-hyp 'IS-SETOID "the IS-SETOID hypothesis"))
  (dk-split-all!)
  (mac-h 'IS-EQUIVALENCE (rks-hyp 'IS-EQUIVALENCE "the is-equivalence conjunct"))
  (let ((cs (dk-split-all!)))
    (mac 'RELATED)
    (dk-apply! (or (any-pred rks-refl-shape? cs)
                   (error "rake-setoid: no reflexivity conjunct in the split"))
               a)
    (ass)))

;; goal (IN a (CLASS s a)) -- class-self, inline: a SEP membership whose two
;; obligations are the typing (in context) and reflexivity.
(define (rks-class-self! a)
  (mac 'CLASS)
  (let ((ls (dk-opened (lambda () (sep-mi)))))
    (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'IN)) ls))
    (ass)
    (dk-focus! (any-pred (lambda (n) (not (rks-goal-head? n 'IN))) ls))
    (rks-related-refl! a)))

;; hypothesis (IN x (CLASS s a))  ->  (IN x (PTS s)) and (RELATED s a x)
(define (rks-class-open! mem)
  (mac-h 'class-unfold mem)
  (sep-me (rks-find (lambda (f) (and ((rks-in-head 'SEP) f) (equal? (cadr f) (cadr mem))))
                    "the class membership, as a SEP"))
  (dk-split-all!))

;; hypothesis (IN c (QUOTIENT s))  ->  a representative a, with (= (CLASS s a) c)
;; in context.  The quotient is the IMAGE of PROJ, so this is
;; image-membership-iff plus one beta reduction of the projection.
(define (rks-rep! mem)
  (let ((c (cadr mem)))
    (mac-h 'quotient-unfold mem)
    (dk-image-hyp!
           (rks-find (lambda (f) (and ((rks-in-head 'IMAGE) f) (equal? (cadr f) c)))
                     "the image membership"))
    (let ((a (dk-skolem! (rks-hyp 'FORSOME "the representative existential"))))
      (mac-h 'proj-unfold (rks-find (rks-eq-to c) "the PROJ equation"))
      (lam-b-h (rks-find (rks-eq-to c) "the beta redex"))
      a)))

;; goal (IN (ff a b) cod) for ff : CARTESIAN(dom,dom) -> cod.  op-typing.scm's
;; tupling bridge: a structure-style operation eats one PAIR while the parser
;; emits the curried (f a b), and apply-tupling-2 is stated with `==' (both
;; sides undefined when f is not tuple-typed), which `subst' takes as happily
;; as a `='.
(define (rks-app2-close! ff a b dom cod)
  (fact 'apply-tupling-2 ff a b)
  (subst (list '== (list ff a b) (list ff (list 'LIST a b))))
  (fact 'pair-in-cartesian dom dom a b)
  (fact 'fun-apply-type-c ff (list 'CARTESIAN dom dom) cod (list 'LIST a b))
  (ass))

(define (rks-app2-have! ff a b dom cod)
  (have! (list 'IN (list ff a b) cod)
         (lambda () (rks-app2-close! ff a b dom cod))))

;;; =====================================================================
;;; The unfolding equations.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL a
   (== (CLASS s a) (SEP b_ (PTS s) (RELATED s a b_)))))))
(di) (mac 'CLASS) (qrfl)
(qed 'class-unfold)
(gloss! 'class-unfold
  "CLASS(s,a) is the separation { b in PTS(s) : a ~ b }, as a citable equation.
   Cite it with mac-h to open a class membership that sits in a hypothesis --
   which the CLASS macete alone cannot do, def-functoid installing no theorem.")
(topic! 'class-unfold 'plumbing)

(sp (make-wff '(FORALL s (== (PROJ s) (VNB-LAMBDA a_ (PTS s) (CLASS s a_))))))
(di) (mac 'PROJ) (qrfl)
(qed 'proj-unfold)
(gloss! 'proj-unfold
  "PROJ(s) is the lambda a |-> [a] on PTS(s), as a citable equation.")
(topic! 'proj-unfold 'plumbing)

(sp (make-wff '(FORALL s (== (QUOTIENT s) (IMAGE (PROJ s) (PTS s))))))
(di) (mac 'QUOTIENT) (qrfl)
(qed 'quotient-unfold)
(gloss! 'quotient-unfold
  "QUOTIENT(s) is the image of PTS(s) under the class map, as a citable
   equation.  With image-membership-iff it is how a proof picks a
   representative for a member of the quotient.")
(topic! 'quotient-unfold 'plumbing)

(sp (make-wff '(FORALL s (FORALL f (IFF (RESPECTS s f)
   (FORALL a_ (IMPLIES (IN a_ (PTS s))
     (FORALL b_ (IMPLIES (IN b_ (PTS s))
       (IMPLIES (RELATED s a_ b_) (= (f a_) (f b_))))))))))))
(di) (mac 'RESPECTS) (prop)
(qed 'respects-unfold)
(topic! 'respects-unfold 'plumbing)

(sp (make-wff '(FORALL s (FORALL f (IFF (RESPECTS2 s f)
   (FORALL a_ (FORALL b_ (FORALL c_ (FORALL d_
     (IMPLIES (IN a_ (PTS s)) (IMPLIES (IN b_ (PTS s))
       (IMPLIES (IN c_ (PTS s)) (IMPLIES (IN d_ (PTS s))
         (IMPLIES (AND (RELATED s a_ c_) (RELATED s b_ d_))
                  (= (f a_ b_) (f c_ d_))))))))))))))))
(di) (mac 'RESPECTS2) (prop)
(qed 'respects2-unfold)
(topic! 'respects2-unfold 'plumbing)

(sp (make-wff '(FORALL m (IFF (IS-VECTOR-SPACE m)
   (AND (IS-MODULE m) (IS-FIELD-RING (SCAL m)))))))
(di) (mac 'IS-VECTOR-SPACE) (prop)
(qed 'is-vector-space-unfold)
(gloss! 'is-vector-space-unfold
  "A vector space is a module whose scalars are a field, as a citable
   equivalence.  VECTOR-SPACE is declared same-shape-as MODULE, which installs
   the unfolding MACETE and no theorem, so mac-h cannot unfold IS-VECTOR-SPACE
   in a hypothesis without this.")
(topic! 'is-vector-space-unfold 'plumbing)

;;; =====================================================================
;;; class-is-set -- an equivalence class is a set.
;;; CLASS(s,a) is a SEP over PTS(s); `sep-set' reduces sethood of a separation
;;; to sethood of its domain, which is IS-SETOID's carriers conjunct.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (PTS s))
       (IN (CLASS s a) SET)))))))
(dk-peel!)
(mac-h 'IS-SETOID (rks-hyp 'IS-SETOID "the IS-SETOID hypothesis"))
(dk-split-all!)
(mac 'CLASS)
(sep-set)
(ass)
(qed 'class-is-set)
(topic! 'class-is-set 'plumbing)

;;; =====================================================================
;;; quotient-is-set -- the quotient is a set.
;;; QUOTIENT(s) is the IMAGE of the set PTS(s); `image-set' is replacement,
;;; primitive since 2026-07-28.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (IN (QUOTIENT s) SET)))))
(dk-peel!)
(mac-h 'IS-SETOID (rks-hyp 'IS-SETOID "the IS-SETOID hypothesis"))
(dk-split-all!)
(mac 'QUOTIENT)
(fact 'image-set '(PROJ s) '(PTS s))
(ass)
(qed 'quotient-is-set)
(topic! 'quotient-is-set 'plumbing)

;;; =====================================================================
;;; proj-in-fun -- PROJ(s) : PTS(s) -> QUOTIENT(s).
;;; `lam-t' opens the pointwise typing and the sethood of PTS(s).  The pointwise
;;; leaf says CLASS(s,a) lies in the IMAGE of PROJ(s): witness a, and the
;;; equation (PROJ s)(a) = CLASS(s,a) is one beta reduction.  `rfl' wants the
;;; term DEFINED, which class-is-set supplies -- and which is why IS-SETOID must
;;; still be in the context here (see THE MAC-H TRAP in the header).
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (IN (PROJ s) (FUN (PTS s) (QUOTIENT s)))))))
(dk-peel!)
(mac 'PROJ)
(let ((ls (dk-opened (lambda () (lam-t)))))
  ;; the sethood of the domain
  (dk-focus! (any-pred rks-set-leaf? ls))
  (mac-h 'IS-SETOID (rks-hyp 'IS-SETOID "the IS-SETOID hypothesis"))
  (dk-split-all!)
  (ass)
  ;; the pointwise typing
  (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORALL)) ls))
  (dk-peel!)
  (let* ((g  (dk-goal))                        ; (IN (CLASS s a) (QUOTIENT s))
         (ss (cadr (cadr g)))
         (a0 (caddr (cadr g))))
    (mac 'QUOTIENT)
    (dk-image-goal!)
    (ew a0)
    (let ((cs (dk-opened (lambda () (di)))))
      (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'IN)) cs))
      (ass)
      (dk-focus! (any-pred (lambda (n) (rks-goal-head? n '=)) cs))
      (mac 'PROJ)
      (lam-b)
      (fact 'class-is-set ss a0)
      (rfl))))
(qed 'proj-in-fun)
(topic! 'proj-in-fun 'plumbing)

;;; =====================================================================
;;; descend-in-fun -- DESCEND(s,f) : QUOTIENT(s) -> Z.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL Z (FORALL f
       (IMPLIES (AND (IN f (FUN (PTS s) Z)) (RESPECTS s f))
         (IN (DESCEND s f) (FUN (QUOTIENT s) Z)))))))))
(dk-peel!)
(dk-split-all!)
(mac 'DESCEND)
(let ((ls (dk-opened (lambda () (lam-t)))))
  ;; the sethood of the domain
  (dk-focus! (any-pred rks-set-leaf? ls))
  (fact 'quotient-is-set (cadr (cadr (dk-goal))))
  (ass)
  ;; the pointwise typing
  (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORALL)) ls))
  (dk-peel!)
  (let* ((g   (dk-goal))                       ; (IN (IOTA z ...) Z)
         (it  (cadr g))
         (cod (caddr g))
         (fun (rks-find (rks-in-head 'FUN) "f's FUN typing"))
         (ff  (cadr fun))
         (dom (cadr (caddr fun)))
         (cm  (rks-find (rks-in-head 'QUOTIENT) "c in the quotient"))
         (cc  (cadr cm))
         (ss  (cadr (caddr cm)))
         (aa  (rks-rep! cm)))
    (subst (list '= cc (list 'CLASS ss aa)))
    (let* ((it2 (cadr (dk-goal)))
           (ls2 (dk-opened (lambda () (iota-d it2)))))
      ;; (1) the defining property, granted: the value IS f of some class member
      (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'IN)) ls2))
      (let ((a1 (dk-skolem! (rks-hyp 'FORSOME "the granted defining property"))))
        (rks-class-open!
          (rks-find (lambda (f) (and ((rks-in-head 'CLASS) f) (equal? (cadr f) a1)))
                    "the class membership of the granted witness"))
        (fact 'fun-apply-type-c ff dom cod a1)
        (subst (list '= it2 (list ff a1)))
        (ass))
      ;; (2) existence and uniqueness of the description
      (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORSOME)) ls2))
      (ew (list ff aa))
      (let ((cs (dk-opened (lambda () (di)))))
        ;; existence: the representative itself
        (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORSOME)) cs))
        (ew aa)
        (let ((es (dk-opened (lambda () (di)))))
          (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'IN)) es))
          (rks-class-self! aa)
          (dk-focus! (any-pred (lambda (n) (rks-goal-head? n '=)) es))
          (fact 'fun-apply-type-c ff dom cod aa)
          (rfl))
        ;; uniqueness: RESPECTS pins the value
        (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORALL)) cs))
        (dk-peel!)
        (let ((a2 (dk-skolem! (rks-hyp 'FORSOME "the competing description"))))
          (rks-class-open!
            (rks-find (lambda (f) (and ((rks-in-head 'CLASS) f) (equal? (cadr f) a2)))
                      "the class membership of the competitor"))
          (mac-h 'respects-unfold (rks-hyp 'RESPECTS "the RESPECTS hypothesis"))
          (dk-apply! (rks-hyp 'FORALL "the unfolded RESPECTS universal") aa a2)
          (subst (list '= (caddr (dk-goal)) (list ff a2)))
          (ass))))))
(qed 'descend-in-fun)
(topic! 'descend-in-fun 'set-quotient)

;;; =====================================================================
;;; descend2-in-fun -- DESCEND2(s,f) : QUOTIENT(s) x QUOTIENT(s) -> Z.
;;; The two-slot twin, and the multi-binder VNB-LAMBDA case of `lam-t' (added
;;; 2026-08-14): the binder list is read componentwise against the CARTESIAN
;;; domain, so the pointwise leaf is one guarded universal per component.  The
;;; statement is written with `forall-guarded' exactly as the support writes it,
;;; so the installed formula is the same one.
;;; Two differences from the unary case: the domain sethood is a CARTESIAN
;;; (cartesian-set-iff), and f eats a PAIR, so every typing of (f a b) goes
;;; through the apply-tupling-2 bridge.  The RESPECTS2 antecedent is a
;;; CONJUNCTION, which `fact' will not split, so it is landed whole by `have!'
;;; before the instantiation.
;;; =====================================================================
(sp (make-wff
  (forall-guarded '(s) '((IS-SETOID s))
    (forall-guarded '(Z f)
        '((IN f (FUN (CARTESIAN (PTS s) (PTS s)) Z)) (RESPECTS2 s f))
      '(IN (DESCEND2 s f) (FUN (CARTESIAN (QUOTIENT s) (QUOTIENT s)) Z))))))
(dk-peel!)
(mac 'DESCEND2)
(let ((ls (dk-opened (lambda () (lam-t)))))
  ;; the sethood of the domain -- a CARTESIAN of two quotients
  (dk-focus! (any-pred rks-set-leaf? ls))
  (fact 'quotient-is-set (cadr (cadr (cadr (dk-goal)))))
  (mac 'cartesian-set-iff)
  (dk-conj-close! (lambda () (ass)))
  ;; the pointwise typing
  (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORALL)) ls))
  (dk-peel!)
  (let* ((g   (dk-goal))
         (it  (cadr g))
         (cod (caddr g))
         (p   (caddr it))                      ; (FORSOME a (AND (IN a c) (FORSOME b (AND (IN b d) EQ))))
         (q   (caddr p))
         (cc  (caddr (cadr q)))
         (r   (caddr q))
         (dd  (caddr (cadr (caddr r))))
         (fun (rks-find (rks-in-head 'FUN) "f's FUN typing"))
         (ff  (cadr fun))
         (dom (cadr (cadr (caddr fun))))
         (ss  (cadr (rks-hyp 'RESPECTS2 "the RESPECTS2 hypothesis")))
         (aa  (rks-rep! (list 'IN cc (list 'QUOTIENT ss))))
         (bb  (rks-rep! (list 'IN dd (list 'QUOTIENT ss)))))
    (subst (list '= cc (list 'CLASS ss aa)))
    (subst (list '= dd (list 'CLASS ss bb)))
    (let* ((it2 (cadr (dk-goal)))
           (ls2 (dk-opened (lambda () (iota-d it2)))))
      ;; (1) the defining property, granted
      (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'IN)) ls2))
      (let* ((a1 (dk-skolem! (rks-hyp 'FORSOME "the granted property, outer")))
             (b1 (dk-skolem! (rks-hyp 'FORSOME "the granted property, inner"))))
        (rks-class-open!
          (rks-find (lambda (f) (and ((rks-in-head 'CLASS) f) (equal? (cadr f) a1)))
                    "the first class membership"))
        (rks-class-open!
          (rks-find (lambda (f) (and ((rks-in-head 'CLASS) f) (equal? (cadr f) b1)))
                    "the second class membership"))
        (subst (list '= it2 (list ff a1 b1)))
        (rks-app2-close! ff a1 b1 dom cod))
      ;; (2) existence and uniqueness
      (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORSOME)) ls2))
      (rks-app2-have! ff aa bb dom cod)        ; the definedness `rfl' will want
      (ew (list ff aa bb))
      (let ((cs (dk-opened (lambda () (di)))))
        ;; existence: the two representatives
        (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORSOME)) cs))
        (ew aa)
        (let ((es (dk-opened (lambda () (di)))))
          (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'IN)) es))
          (rks-class-self! aa)
          (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORSOME)) es))
          (ew bb)
          (let ((fs (dk-opened (lambda () (di)))))
            (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'IN)) fs))
            (rks-class-self! bb)
            (dk-focus! (any-pred (lambda (n) (rks-goal-head? n '=)) fs))
            (rfl)))
        ;; uniqueness: RESPECTS2 pins the value in both slots
        (dk-focus! (any-pred (lambda (n) (rks-goal-head? n 'FORALL)) cs))
        (dk-peel!)
        (let* ((a2 (dk-skolem! (rks-hyp 'FORSOME "the competitor, outer")))
               (b2 (dk-skolem! (rks-hyp 'FORSOME "the competitor, inner"))))
          (rks-class-open!
            (rks-find (lambda (f) (and ((rks-in-head 'CLASS) f) (equal? (cadr f) a2)))
                      "the competitor's first class membership"))
          (rks-class-open!
            (rks-find (lambda (f) (and ((rks-in-head 'CLASS) f) (equal? (cadr f) b2)))
                      "the competitor's second class membership"))
          (have! (list 'AND (list 'RELATED ss aa a2) (list 'RELATED ss bb b2))
                 (lambda () (dk-conj-close! (lambda () (ass)))))
          (mac-h 'respects2-unfold (rks-hyp 'RESPECTS2 "the RESPECTS2 hypothesis"))
          (dk-apply! (rks-hyp 'FORALL "the unfolded RESPECTS2 universal") aa bb a2 b2)
          (subst (list '= (caddr (dk-goal)) (list ff a2 b2)))
          (ass))))))
(qed 'descend2-in-fun)
(topic! 'descend2-in-fun 'set-quotient)

;;; =====================================================================
;;; vec-is-set -- the vectors of a normed vector space are a set.
;;; The `(carriers VEC)' slot of declare-structure NORMED-VECTOR-SPACE
;;; contributes (IN (VEC m) SET) verbatim to the IS-NORMED-VECTOR-SPACE iff.
;;; =====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IS-NORMED-VECTOR-SPACE m) (IN (VEC m) SET)))))
(dk-peel!)
(mac-h 'IS-NORMED-VECTOR-SPACE
       (rks-hyp 'IS-NORMED-VECTOR-SPACE "the normed-vector-space hypothesis"))
(dk-split-all!)
(ass)
(qed 'vec-is-set)
(topic! 'vec-is-set 'analysis)

;;; =====================================================================
;;; vspace-vec-is-set -- and of a vector space.
;;; IS-VECTOR-SPACE is IS-MODULE plus a condition on the scalars, and MODULE's
;;; own carriers slot is where (IN (VEC m) SET) lives; two unfolds, not one.
;;; =====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IS-VECTOR-SPACE m) (IN (VEC m) SET)))))
(dk-peel!)
(mac-h 'is-vector-space-unfold (rks-hyp 'IS-VECTOR-SPACE "the vector-space hypothesis"))
(dk-split-all!)
(mac-h 'IS-MODULE (rks-hyp 'IS-MODULE "the module conjunct"))
(dk-split-all!)
(ass)
(qed 'vspace-vec-is-set)
(topic! 'vspace-vec-is-set 'analysis)
