;;; hom-kinds.scm -- the category laws for the arrows the generic driver of
;;; hom-laws.scm does not reach: the FAMILY slot kinds, and two carriers.
;;;
;;; Batch 39 (2026-09-28; docs/categories-per-structure-2026-09-28.md).  The hom
;;; generator (structures.scm, build-hom-axiom) has two slot kinds it did not
;;; have before:
;;;
;;;   (family F C)          F(s) a set of subsets of the carrier C(s) -- a
;;;                         sigma-algebra, a topology.  Generated clause:
;;;                           forall u in F(t). PREIMAGE(s, f, u) in F(s)
;;;   (family-fun M F R)    M(s) a function on the family F(s) -- a measure.
;;;                         Generated clause:
;;;                           forall u in F(t). M(t)(u) = M(s)(PREIMAGE(s, f, u))
;;;
;;; so the default arrows of MEASURABLE-SPACE are the measurable maps and those of
;;; MEASURE-SPACE the measure-preserving measurable maps (they were "f arbitrary
;;; and SIGMA(a) = SIGMA(b)", the wrong arrows).  The generic driver of
;;; hom-laws.scm closes a clause of the composite by instantiating the f clause
;;; at the eigenvariable, which is right for preservation and wrong for a
;;; pull-back (u lives in F(c), not F(b)); so the two structures leave its list
;;; and are proved HERE, by one driver over the slot list with a rule per KIND:
;;;
;;;   identity   PREIMAGE(s, ID, u) = u        (u is a subset of PTS(s))
;;;   composite  PREIMAGE(s, g o f, u) = PREIMAGE(s, f, PREIMAGE(t, g, u))
;;;              -- a family clause: g's clause at u, then f's at its preimage;
;;;              -- a family-fun clause: M(c)(u) = M(b)(g^-1 u) = M(a)(f^-1 g^-1 u).
;;;
;;; hom-NAME-member-iff and hom-NAME-in-set are the generic ones (they see only
;;; the predicate), copied from hom-laws.scm.
;;;
;;; SETOID (two carriers PTS, REL): structures.scm now installs its hom-set as a
;;; set of PAIRS, HOM-SETOID(a, b) = {p in CARTESIAN(FUN(PTS a, PTS b), FUN(REL a,
;;; REL b)) : IS-HOM-SETOID(a, b, NTH(1, p), NTH(2, p))}; its four laws are here
;;; too, componentwise.
;;;
;;; Nothing is asserted; every qed is expected modulo 0.
;;; Window: after theorem-library/hom-laws (with MEASURABLE-SPACE and
;;; MEASURE-SPACE removed from its *hml-generated*), before hom-functors, which
;;; cites hom-NAME-compose / -in-set / -member-iff for both.

;;; --- names ------------------------------------------------------------------
(define (hmk-is name) (symbol-append 'IS- name))
(define (hmk-hom name) (structure-hom-name name))
(define (hmk-hom-def name) (symbol-append (structure-hom-name name) '-def))
(define (hmk-set name) (symbol-append 'HOM- name))
(define (hmk-thm name suffix) (symbol-append 'hom- name suffix))
(define (hmk-slots name) (structure-def-slots (find-shape-structure name)))
(define (hmk-carriers name)
  (map car (filter (lambda (s) (eq? (cadr s) 'carrier)) (hmk-slots name))))
(define (hmk-carrier name)
  (let ((cs (hmk-carriers name)))
    (if (= (length cs) 1) (car cs) (error "hmk-carrier: not single-carrier" name))))

;;; --- formula utilities (hom-laws.scm's, under this file's prefix) ------------
(define (hmk-inst thm . terms)
  (let loop ((f (lookup-theorem thm)) (ts terms))
    (if (null? ts) f
        (loop (subst-free (quantifier-var f) (car ts) (quantifier-body f)) (cdr ts)))))
(define (hmk-conjuncts f)
  (if (dk-head-is? f 'AND)
      (append (hmk-conjuncts (cadr f)) (hmk-conjuncts (caddr f)))
      (list f)))
(define (hmk-and fs)
  (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (hmk-and (cdr fs)))))
(define (hmk-ctx f who)
  (or (dk-ctx-form f) (error "hom-kinds: not in context --" who (expression->string f))))
(define (hmk-done! name)
  (if (proof-done? *ps*) (qed name) (error "hom-kinds: failed to prove" name)))
(define (hmk-index g lst)
  (let loop ((l lst) (i 0))
    (cond ((null? l) #f)
          ((eq? #t (vnb-guard (lambda () (alpha-equiv? (car l) g)))) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (hmk-replace e s t)
  (cond ((equal? e s) t)
        ((pair? e) (map (lambda (x) (hmk-replace x s t)) e))
        (#t e)))

;;; the slot typings (IN (ACC v) X) among the conjuncts of IS-NAME(v), landed in a
;;; lane so that IS-NAME(v) survives
(define (hmk-land-typings! name v)
  (let* ((accs (map car (hmk-slots name)))
         (ts (filter (lambda (c) (and (dk-head-is? c 'IN) (pair? (cadr c)) (= (length (cadr c)) 2)
                                      (memq (car (cadr c)) accs) (equal? (cadr (cadr c)) v)
                                      (not (dk-asm? c))))
                     (hmk-conjuncts (caddr (hmk-inst (hmk-is name) v))))))
    (if (pair? ts)
        (let ((conj (hmk-and ts)))
          (dk-have! conj
            (lambda ()
              (mac-h (hmk-is name) (hmk-ctx (list (hmk-is name) v) "IS-NAME"))
              (dk-split-all!)
              (dk-conj-close!)))
          (if (pair? (cdr ts)) (dk-split-all! (list (hmk-ctx conj "typings"))))))))

;;; x in B from A in POWER(B) and x in A (power-set-membership, in a lane)
(define (hmk-sub-elt! x a-set b-set)
  (let ((goal (list 'IN x b-set)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (mac-h 'power-set-membership (hmk-ctx (list 'IN a-set (list 'POWER b-set)) "power typing"))
            (dk-split-all!)
            (dk-apply! (hmk-ctx (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z a-set) (list 'IN 'z b-set)))
                                "the inclusion")
                       x)
            (ass))))
    (hmk-ctx goal "sub-element")))

;;; H => H[S:=T] on a lane, detached (no hypothesis-side subst in the kernel)
(define (hmk-rewrite-hyp! h eq)
  (let* ((h2  (hmk-replace h (cadr eq) (caddr eq)))
         (imp (list 'IMPLIES h h2)))
    (if (not (dk-asm? h2))
        (begin
          (dk-have! imp (lambda () (subst eq) (di) (ass)))
          (detach! (hmk-ctx imp "the rewriting implication"))))
    (hmk-ctx h2 "the rewritten hypothesis")))

;;; A = B for two classes, by class-extensionality.  Through `dk-have!', not
;;; `detach-with!': the family and the family-fun clause of one structure are
;;; peeled at the SAME eigenvariable in sibling branches with the same context,
;;; so the second branch's pointwise lemma is hash-consed onto the first's,
;;; already grounded -- which `have!' reports as "no side goal" and dk-have!
;;; accepts.
(define (hmk-class-eq! a-cls b-cls fwd bwd)
  (let ((ch (dk-cite! 'class-extensionality a-cls b-cls)))
    (if (not (dk-asm? (list '= a-cls b-cls)))
     (begin
      (dk-have! (cadr ch)
      (lambda ()
        (di)
        (let ((x (cadr (cadr (dk-goal)))))
          (for-each (lambda (lf)
                      (dk-focus! lf)
                      (if (equal? (caddr (dk-goal)) b-cls) (fwd x) (bwd x)))
                    (dk-opened (lambda () (di)))))))
      (detach! (hmk-ctx ch "class-extensionality instance"))))
    (hmk-ctx (list '= a-cls b-cls) "the class equation")))

;;; close a membership goal through PREIMAGE and AND layers, then CLOSER
(define (hmk-preimage-close! closer)
  (let ((g (dk-goal)))
    (cond ((dk-asm? g) (ass))
          ((dk-head-is? g 'AND) (dk-conj-close! (lambda () (hmk-preimage-close! closer))))
          ((and (dk-head-is? g 'IN) (dk-head-is? (caddr g) 'PREIMAGE))
           (mac 'preimage-membership)
           (hmk-preimage-close! closer))
          (#t (closer)))))

;;; --- membership and sethood (generic; hom-laws.scm's drivers) ----------------
(define (hmk-prove-member-iff! name)
  (let ((cacc (hmk-carrier name)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL f
           (IFF (IN f (,(hmk-set name) a b))
                (AND (IN f (FUN (,cacc a) (,cacc b))) (,(hmk-hom name) a b f))))))))
    (dk-peel!)
    (mac (hmk-set name))
    (for-each
      (lambda (lf)
        (dk-focus! lf)
        (if (dk-head-is? (dk-goal) 'AND)
            (begin
              (sep-me (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (dk-head-is? (caddr x) 'SEP)))
                               "the SEP membership"))
              (dk-conj-close!))
            (begin
              (dk-split-all!)
              (in-sep! (lambda () (ass)) (lambda () (ass))))))
      (dk-opened (lambda () (di))))
    (hmk-done! (hmk-thm name '-member-iff))))

(define (hmk-carrier-set! name v)
  (let ((goal (list 'IN (list (hmk-carrier name) v) 'SET)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (mac-h (hmk-is name) (hmk-ctx (list (hmk-is name) v) "IS-NAME"))
            (dk-split-all!)
            (ass))))))

(define (hmk-prove-in-set! name)
  (sp (make-wff `(FORALL a (FORALL b (IMPLIES (,(hmk-is name) a) (IMPLIES (,(hmk-is name) b)
                   (IN (,(hmk-set name) a b) SET)))))))
  (dk-peel!)
  (let* ((hs (cadr (dk-goal))) (va (cadr hs)) (vb (caddr hs)))
    (hmk-carrier-set! name va)
    (hmk-carrier-set! name vb)
    (mac (hmk-set name))
    (sep-set)
    (mac 'fun-set-iff)
    (dk-conj-close!)
    (hmk-done! (hmk-thm name '-in-set))))

;;; --- the FAMILY kinds: identity ------------------------------------------------
;;;
;;; The clause kind is read off the goal conjunct: a FAMILY clause ends in
;;; (IN (PREIMAGE ...) (F v)), a FAMILY-FUN clause in (= ((M v) u) ((M v) pre)).
;;; Either way the preimage under the identity is rewritten to u.

;;; PREIMAGE(v, ID-FUN(PTS v), u) = u, for u in F(v) with F(v) in POWER(POWER(PTS v))
(define (hmk-preimage-id! v fam u)
  (let* ((pv  (list 'PTS v))
         (idf (list 'ID-FUN pv))
         (pre (list 'PREIMAGE v idf u)))
    (hmk-sub-elt! u (list fam v) (list 'POWER pv))
    (hmk-class-eq! pre u
      (lambda (x)                                  ; x in PREIMAGE => x in u
        (mac-h 'preimage-membership (hmk-ctx (list 'IN x pre) "x in preimage"))
        (dk-split-all!)
        (hmk-rewrite-hyp! (list 'IN (list idf x) u) (dk-cite! 'id-fun-apply pv x))
        (ass))
      (lambda (x)                                  ; x in u => x in PREIMAGE
        (hmk-sub-elt! x u pv)
        (hmk-preimage-close!
          (lambda ()
            (subst (dk-cite! 'id-fun-apply pv x))
            (ass)))))))

;;; the FAMILY slot F whose members guard the clause (FORALL u (IMPLIES (IN u (F v)) ...))
(define (hmk-clause-family c)
  (let* ((imp (and (dk-head-is? c 'FORALL) (caddr c)))
         (grd (and (dk-head-is? imp 'IMPLIES) (cadr imp)))
         (cls (and (dk-head-is? grd 'IN) (caddr grd))))
    (and (pair? cls) (car cls))))

(define (hmk-prove-family-id! name)
  (sp (make-wff `(FORALL a (IMPLIES (,(hmk-is name) a) (,(hmk-hom name) a a (ID-FUN (PTS a)))))))
  (dk-peel!)
  (let* ((v (cadr (dk-goal))) (pv (list 'PTS v)))
    (hmk-land-typings! name v)
    (mac (hmk-hom-def name))
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond ((dk-asm? g) (ass))
                ((and (dk-head-is? g 'IN) (dk-head-is? (cadr g) 'ID-FUN))
                 (dk-cite! 'id-fun-type pv) (ass))
                ((dk-head-is? g 'FORALL)
                 (let* ((fam (hmk-clause-family g))
                        (landed (dk-peel!))
                        (u (cadr (car landed)))
                        (e (hmk-preimage-id! v fam u)))
                   (subst e)
                   (if (dk-head-is? (dk-goal) '=) (rfl) (ass))))
                (#t (error "hmk-prove-family-id!: unknown clause" (expression->string g)))))))
    (hmk-done! (hmk-thm name '-id))))

;;; --- the FAMILY kinds: composition -----------------------------------------------

;;; PREIMAGE(s, g o f, u) = PREIMAGE(s, f, PREIMAGE(t, g, u))
(define (hmk-preimage-compose! vs vt vf vg u cu)
  (let* ((ps  (list 'PTS vs))
         (gf  (list 'COMPOSE vg vf))
         (pre (list 'PREIMAGE vs gf u))
         (pg  (list 'PREIMAGE vt vg u))
         (pfg (list 'PREIMAGE vs vf pg)))
    (hmk-class-eq! pre pfg
      (lambda (x)
        (mac-h 'preimage-membership (hmk-ctx (list 'IN x pre) "x in preimage"))
        (dk-split-all!)
        (let ((ex (dk-apply! cu x)))
          (hmk-rewrite-hyp! (list 'IN (list gf x) u) ex))
        (dk-cite! 'fun-apply-type-c vf ps (list 'PTS vt) x)
        (hmk-preimage-close! (lambda () (ass))))
      (lambda (x)
        (mac-h 'preimage-membership (hmk-ctx (list 'IN x pfg) "x in preimage"))
        (dk-split-all!)
        (mac-h 'preimage-membership (hmk-ctx (list 'IN (list vf x) pg) "f x in preimage"))
        (dk-split-all!)
        (hmk-preimage-close!
          (lambda ()
            (subst (dk-apply! cu x))
            (ass)))))))

;;; the conjunct of CONJ that is F's family clause (a FORALL guarded by F, ending in IN)
(define (hmk-family-clause conj fam)
  (find-first (lambda (c) (and (eq? (hmk-clause-family c) fam)
                               (dk-head-is? (caddr (caddr c)) 'IN)))
              conj))

(define (hmk-prove-family-compose! name)
  (let ((hom (hmk-hom name)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL f (FORALL g
           (IMPLIES (,hom a b f) (IMPLIES (,hom b c g) (,hom a c (COMPOSE g f)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (vs (cadr gl)) (vw (caddr gl)) (gf (cadddr gl))
           (vg (cadr gf)) (vf (caddr gf))
           (hf (dk-pick (lambda (x) (and (dk-head-is? x hom) (equal? (cadddr x) vf))) "the f hom"))
           (vt (caddr hf))
           (hg (hmk-ctx (list hom vt vw vg) "the g hom"))
           (ps (list 'PTS vs)) (pt (list 'PTS vt)) (pw (list 'PTS vw))
           (fconj (hmk-conjuncts (caddr (hmk-inst (hmk-hom-def name) vs vt vf))))
           (gconj (hmk-conjuncts (caddr (hmk-inst (hmk-hom-def name) vt vw vg))))
           (cconj (hmk-conjuncts (caddr (hmk-inst (hmk-hom-def name) vs vw gf)))))
      (mac-h (hmk-hom-def name) hf)
      (mac-h (hmk-hom-def name) hg)
      (dk-split-all!)
      (hmk-land-typings! name vs)
      (dk-have! (list 'AND (list 'IN vf (list 'FUN ps pt)) (list 'IN vg (list 'FUN pt pw))))
      (let ((cu (dk-cite! 'compose-apply ps pt pw vg vf)))
        (mac (hmk-hom-def name))
        (dk-conj-close!
          (lambda ()
            (let ((g (dk-goal)))
              (cond ((dk-asm? g) (ass))
                    ((and (dk-head-is? g 'IN) (dk-head-is? (cadr g) 'COMPOSE))
                     (dk-cite! 'compose-type ps pt pw vg vf) (ass))
                    ((dk-head-is? g 'FORALL)
                     (let* ((i   (or (hmk-index g cconj) (error "hmk: unknown conjunct" (expression->string g))))
                            (fam (hmk-clause-family g))
                            (uf  (hmk-ctx (hmk-family-clause fconj fam) "f family clause"))
                            (ug  (hmk-ctx (hmk-family-clause gconj fam) "g family clause"))
                            (landed (dk-peel!))
                            (u   (cadr (car landed)))
                            (pg  (list 'PREIMAGE vt vg u))
                            (pfg (list 'PREIMAGE vs vf pg)))
                       (dk-apply! ug u)                    ; g^-1 u in F(t)
                       (dk-apply! uf pg)                   ; f^-1 g^-1 u in F(s)
                       (let ((e (hmk-preimage-compose! vs vt vf vg u cu)))
                         (if (dk-head-is? (dk-goal) '=)
                             ;; family-fun: M(w)(u) = M(t)(g^-1 u) = M(s)(f^-1 g^-1 u)
                             (let* ((mg (dk-apply! (hmk-ctx (list-ref gconj i) "g transport clause") u))
                                    (mf (dk-apply! (hmk-ctx (list-ref fconj i) "f transport clause") pg)))
                               (subst e)
                               (subst mg)
                               (ass))
                             (begin (subst e) (ass))))))
                    (#t (error "hmk-prove-family-compose!: unknown clause" (expression->string g))))))))
      (hmk-done! (hmk-thm name '-compose)))))

(for-each (lambda (name)
            (hmk-prove-member-iff! name)
            (hmk-prove-family-id! name)
            (hmk-prove-family-compose! name)
            (hmk-prove-in-set! name))
          '(MEASURABLE-SPACE MEASURE-SPACE))

;;; --- SETOID: two carriers, arrows are PAIRS of maps -------------------------------
;;;
;;;   hom-setoid-member-iff  p in HOM-SETOID(a, b) iff p in CARTESIAN(FUN(PTS a, PTS b),
;;;                          FUN(REL a, REL b)) and IS-HOM-SETOID(a, b, NTH(1, p), NTH(2, p))
;;;   hom-setoid-id          IS-SETOID(a) => IS-HOM-SETOID(a, a, ID-FUN(PTS a), ID-FUN(REL a))
;;;   hom-setoid-compose     componentwise
;;;   hom-setoid-in-set      IS-SETOID(a) => IS-SETOID(b) => HOM-SETOID(a, b) in SET
;;;
;;; The generated IS-HOM-SETOID has no clause beyond the two typings (SETOID has
;;; no operation slot): the relation is a CARRIER, so a setoid arrow is a map of
;;; points together with a map of related pairs, unrelated to each other.  That
;;; is what the declaration says; the arrows one wants (f maps related points to
;;; related points) are a declare-category! away, and are not built here.

(sp (make-wff '(FORALL a (FORALL b (FORALL p
       (IFF (IN p (HOM-SETOID a b))
            (AND (IN p (CARTESIAN (FUN (PTS a) (PTS b)) (FUN (REL a) (REL b))))
                 (IS-HOM-SETOID a b (NTH 1 p) (NTH 2 p)))))))))
(dk-peel!)
(mac 'HOM-SETOID)
(for-each
  (lambda (lf)
    (dk-focus! lf)
    (if (dk-head-is? (dk-goal) 'AND)
        (begin
          (sep-me (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (dk-head-is? (caddr x) 'SEP)))
                           "the SEP membership"))
          (dk-conj-close!))
        (begin
          (dk-split-all!)
          (in-sep! (lambda () (ass)) (lambda () (ass))))))
  (dk-opened (lambda () (di))))
(hmk-done! 'hom-setoid-member-iff)

(sp (make-wff '(FORALL a (IMPLIES (IS-SETOID a)
       (IS-HOM-SETOID a a (ID-FUN (PTS a)) (ID-FUN (REL a)))))))
(dk-peel!)
(let ((v (cadr (dk-goal))))
  (hmk-land-typings! 'SETOID v)
  (mac 'IS-HOM-SETOID-def)
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond ((dk-asm? g) (ass))
              (#t (dk-cite! 'id-fun-type (cadr (cadr g))) (ass)))))))
(hmk-done! 'hom-setoid-id)

(sp (make-wff '(FORALL a (FORALL b (FORALL c (FORALL f1 (FORALL f2 (FORALL g1 (FORALL g2
       (IMPLIES (IS-HOM-SETOID a b f1 f2) (IMPLIES (IS-HOM-SETOID b c g1 g2)
         (IS-HOM-SETOID a c (COMPOSE g1 f1) (COMPOSE g2 f2)))))))))))))
(dk-peel!)
(let* ((gl (dk-goal)) (va (cadr gl)) (vc (caddr gl))
       (c1 (cadddr gl)) (c2 (car (cddddr gl)))
       (vg1 (cadr c1)) (vf1 (caddr c1)) (vg2 (cadr c2)) (vf2 (caddr c2))
       (hf (dk-pick (lambda (x) (and (dk-head-is? x 'IS-HOM-SETOID) (equal? (cadddr x) vf1)))
                    "the f hom"))
       (vb (caddr hf))
       (hg (hmk-ctx (list 'IS-HOM-SETOID vb vc vg1 vg2) "the g hom")))
  (mac-h 'IS-HOM-SETOID-def hf)
  (mac-h 'IS-HOM-SETOID-def hg)
  (dk-split-all!)
  (hmk-land-typings! 'SETOID va)
  (mac 'IS-HOM-SETOID-def)
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond ((dk-asm? g) (ass))
              (#t                                  ; (IN (COMPOSE gi fi) (FUN (C a) (C c)))
               (let* ((gf (cadr g)) (gi (cadr gf)) (fi (caddr gf))
                      (ca (cadr (caddr g))) (cc (caddr (caddr g)))
                      (cb (list (car ca) vb)))
                 (dk-have! (list 'AND (list 'IN fi (list 'FUN ca cb)) (list 'IN gi (list 'FUN cb cc))))
                 (dk-cite! 'compose-type ca cb cc gi fi)
                 (ass))))))))
(hmk-done! 'hom-setoid-compose)

(sp (make-wff '(FORALL a (FORALL b (IMPLIES (IS-SETOID a) (IMPLIES (IS-SETOID b)
       (IN (HOM-SETOID a b) SET)))))))
(dk-peel!)
(let* ((hs (cadr (dk-goal))) (va (cadr hs)) (vb (caddr hs)))
  (hmk-land-typings! 'SETOID va)
  (hmk-land-typings! 'SETOID vb)
  (mac 'HOM-SETOID)
  (sep-set)
  (mac 'cartesian-set-iff)
  (mac 'fun-set-iff)
  (dk-conj-close!))
(hmk-done! 'hom-setoid-in-set)

;;; --- the view that forgets the measure is a functor ---------------------------
;;;
;;; measure-space-as-measurable-space-functorial:
;;;   IS-HOM-MEASURE-SPACE(a, b, f) => IS-HOM-MEASURABLE-SPACE(V a, V b, f),
;;;   V = MEASURE-SPACE-AS-MEASURABLE-SPACE.
;;; functoriality.scm's sweep proves a view's functoriality by rewriting every
;;; target accessor of V(a) to the source accessor of a and finding each target
;;; conjunct literally among the source's.  The family clause defeats it: the
;;; view occurs INSIDE PREIMAGE(V a, f, u), a functoid of the structure, which the
;;; accessor rewriting cannot reach (unfolding V there leaves PREIMAGE([PTS a,
;;; SIGMA a], f, u), not PREIMAGE(a, f, u)).  So it is proved here, where
;;; PREIMAGE(V a, f, u) = PREIMAGE(a, f, u) is one class equation (the two
;;; structures have the same PTS), and the sweep must skip a view whose
;;; functoriality is already a theorem.
(define (hmk-view-eq! acc v)                 ; (== (ACC (V v)) (ACC v)), by the slot read-off
  (let ((vv (list 'MEASURE-SPACE-AS-MEASURABLE-SPACE v)))
    (dk-have! (list '== (list acc vv) (list acc v))
      (lambda () (slot acc) (mac 'MEASURE-SPACE-AS-MEASURABLE-SPACE) (nth-r) (slot acc) (qrfl)))
    (hmk-ctx (list '== (list acc vv) (list acc v)) "view read-off")))

(sp (make-wff '(FORALL a (FORALL b (FORALL f (IMPLIES (IS-HOM-MEASURE-SPACE a b f)
       (IS-HOM-MEASURABLE-SPACE (MEASURE-SPACE-AS-MEASURABLE-SPACE a)
                                (MEASURE-SPACE-AS-MEASURABLE-SPACE b) f)))))))
(dk-peel!)
(let* ((gl (dk-goal)) (vva (cadr gl)) (vvb (caddr gl)) (vf (cadddr gl))
       (va (cadr vva)) (vb (cadr vvb)))
  (mac-h 'IS-HOM-MEASURE-SPACE-def (hmk-ctx (list 'IS-HOM-MEASURE-SPACE va vb vf) "the hom"))
  (dk-split-all!)
  (dk-cite! 'measure-space-as-measurable-space-is-measurable-space va)
  (dk-cite! 'measure-space-as-measurable-space-is-measurable-space vb)
  (for-each (lambda (v) (hmk-view-eq! 'PTS v) (hmk-view-eq! 'SIGMA v)) (list va vb))
  (let ((uf (hmk-ctx (hmk-family-clause (dk-asms) 'SIGMA) "the family clause")))
    (mac 'IS-HOM-MEASURABLE-SPACE-def)
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (cond
            ((dk-asm? g) (ass))
            ((dk-head-is? g 'IN)                   ; f in FUN(PTS(V a), PTS(V b))
             (subst (list '= (list 'PTS vva) (list 'PTS va)))
             (subst (list '= (list 'PTS vvb) (list 'PTS vb)))
             (ass))
            (#t
             (let* ((landed (dk-peel!)) (u (cadr (car landed)))
                    (pre1 (list 'PREIMAGE vva vf u)) (pre0 (list 'PREIMAGE va vf u)))
               (dk-have! (list 'IN u (list 'SIGMA vb))
                 (lambda () (subst (list '= (list 'SIGMA vb) (list 'SIGMA vvb))) (ass)))
               (dk-apply! uf u)
               (let ((e (hmk-class-eq! pre1 pre0
                          (lambda (x)
                            (mac-h 'preimage-membership (hmk-ctx (list 'IN x pre1) "x in preimage"))
                            (dk-split-all!)
                            (hmk-preimage-close!
                              (lambda () (subst (list '= (list 'PTS va) (list 'PTS vva))) (ass))))
                          (lambda (x)
                            (mac-h 'preimage-membership (hmk-ctx (list 'IN x pre0) "x in preimage"))
                            (dk-split-all!)
                            (hmk-preimage-close!
                              (lambda () (subst (list '= (list 'PTS vva) (list 'PTS va))) (ass)))))))
                 (subst e)
                 (subst (list '= (list 'SIGMA vva) (list 'SIGMA va)))
                 (ass))))))))))
(hmk-done! 'measure-space-as-measurable-space-functorial)
