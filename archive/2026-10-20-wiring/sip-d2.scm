;;; sip-d2.scm -- THE CLOSEST POINT OF A CLOSED CONVEX SET in a real Hilbert space, by the
;;; COMPLEXIFICATION route, and the variational inequality (the notes' Proposition 1.20).
;;; (SIP-D2, 2026-10-19; scratchpad/triage/SIP-D2.md.)  All PROVEN modulo 0.  Vocabulary:
;;; structure-library/sip-hilbert-vocab.scm (IS-REAL-HILBERT-SPACE, IS-CONVEX-SUBSET).
;;;
;;; Source: the user's notes topological-vector-space.pdf, Ch. 1 s.3, Proposition 1.20.
;;;
;;; THE ROUTE (the user's decision, 2026-10-19).  For a real Hilbert space v,
;;; w = CSIP-CIPS(COMPLEXIFY(v)) is a complex Hilbert space (complexify-hilbert, sip-d1.scm).
;;; A convex set cs of v gives the set cs x cs of w; it is closed when cs is
;;; (complexify-closed), nonempty when cs is, and closed under MIDPOINTS -- the midpoint of
;;; two pairs, (1/2)(p + q) with the real scalar 1/2 = 1/2 + 0 i, is the pair of the convex
;;; combinations (1 - 1/2) p_i + (1/2) q_i.  (It is not a complex subspace, nor convex for
;;; complex scalars: only midpoints are asked.)  hilbert-closest-point-midpoint
;;; (hilbert-projection.scm) at the point (x, 0) gives a pair (a, b) of cs x cs with
;;;   |a - x|^2 + |b|^2 = d_w((a, b), (x, 0))^2 <= d_w((c, b), (x, 0))^2 = |c - x|^2 + |b|^2
;;; for every c in cs, so a is the closest point of cs to x.  No parallelogram or
;;; minimizing-sequence argument is run here.
;;;
;;; WHY cs x cs AND NOT cs x {0} (the brief's wording): both are closed under midpoints and
;;; both give the same a; cs x cs is closed by complexify-closed as it stands, while
;;; cs x {0} wants a closedness lemma for a product A x B of two different sets (the
;;; complexify-closure-comp lemmas are stated for kk x kk) and the closedness of {0}.
;;;
;;; THE VARIATIONAL INEQUALITY, NECESSARY: a closest point a of a convex set satisfies
;;; <x - a, c - a> <= 0 for c in cs.  From |a - x|^2 <= |(1-t) a + t c - x|^2 for t in
;;; [0, 1]:  2 t o <= t^2 q with o = <x - a, c - a>, q = |c - a|^2.  If o > 0, rr-scale-eps
;;; gives s > 0 with q t <= o for 0 <= t <= s; at t = s (when s <= 1) 2 s o <= s (s q) <= s o,
;;; and at t = 1 (when 1 < s) 2 o <= q <= o; both contradict o > 0.  No division.
;;; Sufficiency is real-convex-variational-closest (sip-d1.scm), uniqueness
;;; real-convex-closest-unique (sip-d1.scm).
;;;
;;; Helper prefix: sd2- (the sipd- kit of sip-d1.scm, copied: a theorem-library file's
;;; defines are local to it).
;;;
;;; LOAD WINDOW: after theorem-library/sip-d1 (complexify-hilbert, complexify-closed, cxw-*,
;;; real-convex-variational-closest); hilbert-closest-point-midpoint is in
;;; theorem-library/hilbert-projection (spliced there from hp-midpoint.scm, 2026-10-20).  Nothing cites this file.  Library: analysis.
(define (sd2-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** sip-d2: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "sip-d2: unfinished" name))))

;;; ==========================================================================================
;;; THE EXPANSION KIT on the real form (the `hpr-' device of hilbert-projection.scm, real case:
;;; no conjugation; symmetry instead).
;;; ==========================================================================================
(define (sd2-pin!) (if (not (dk-asm? '(= (SCAL v) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))))
                        (fact 'sip-scal-pin 'v)))
(define (sd2-op? e op) (and (pair? e) (equal? (car e) (list op 'v))))
(define (sd2-sub a b) (list '(VADD v) a (list '(VNEG v) b)))
(define (sd2-add a b) (list '(VADD v) a b))
(define (sd2-act c a) (list '(ACT v) c a))
(define (sd2-ip a b) (list '(RIP v) a b))
(define (sd2-q a) (sd2-ip a a))
(define (sd2-qd a b) (sd2-q (sd2-sub a b)))
;;; type a vector expression (VADD / VNEG / VZERO / ACT at a real scalar) by citation
(define (sd2-vt x)
  (let ((want (list 'IN x '(VEC v))))
    ;; the PARTS are typed even when X itself is in context: the laws want them
    (cond ((sd2-op? x 'VADD) (sd2-vt (cadr x)) (sd2-vt (caddr x)))
          ((sd2-op? x 'VNEG) (sd2-vt (cadr x)))
          ((sd2-op? x 'ACT) (sd2-pin!) (sd2-vt (caddr x)) (dk-real! (cadr x))))
    (cond ((dk-asm? want) x)
          ((equal? x '(VZERO v)) (dk-cite! 'module-vzero-in-sip-as-module 'v) x)
          ((sd2-op? x 'VADD) (dk-cite! 'module-vadd-type-sip-as-module 'v (cadr x) (caddr x)) x)
          ((sd2-op? x 'VNEG) (dk-cite! 'module-vneg-type-sip-as-module 'v (cadr x)) x)
          ((sd2-op? x 'ACT) (dk-cite! 'hbs-act-in-sip-as-module 'v (cadr x) (caddr x)) x)
          (#t (error "sd2-vt: cannot type" (expression->string x))))))
(define (sd2-ft x y) (sd2-vt x) (sd2-vt y) (dk-cite! 'sip-rip-type 'v x y))
(define (sd2-compound? e) (or (sd2-op? e 'VADD) (sd2-op? e 'VNEG) (sd2-op? e 'ACT) (equal? e '(VZERO v))))
(define (sd2-find-redex e)
  (cond ((not (pair? e)) #f)
        ((and (sd2-op? e 'RIP) (= (length e) 3) (or (sd2-compound? (cadr e)) (sd2-compound? (caddr e)))) e)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((sd2-find-redex (car l)) => (lambda (x) x))
                    (#t (loop (cdr l))))))))
(define (sd2-open-law! r)
  (let ((a (cadr r)) (b (caddr r)))
    (sd2-vt a) (sd2-vt b)
    (cond ((sd2-op? a 'VADD) (dk-cite! 'sip-rip-add-left 'v (cadr a) (caddr a) b))
          ((sd2-op? a 'VNEG) (dk-cite! 'sip-rip-neg-left 'v (cadr a) b))
          ((sd2-op? a 'ACT)  (dk-real! (cadr a)) (dk-cite! 'sip-rip-homog-left 'v (cadr a) (caddr a) b))
          ((equal? a '(VZERO v)) (dk-cite! 'sip-rip-zero-left 'v b))
          ((sd2-op? b 'VADD) (dk-cite! 'sip-rip-add-right 'v a (cadr b) (caddr b)))
          ((sd2-op? b 'VNEG) (dk-cite! 'sip-rip-neg-right 'v a (cadr b)))
          ((sd2-op? b 'ACT)  (dk-real! (cadr b)) (dk-cite! 'sip-rip-homog-right 'v (cadr b) a (caddr b)))
          ((equal? b '(VZERO v)) (dk-cite! 'sip-rip-zero-right 'v a))
          (#t (error "sd2-open-law!: not a redex" (expression->string r))))))
;;; the form atoms <a, b> of an expression
(define (sd2-atoms e)
  (cond ((not (pair? e)) '())
        ((and (sd2-op? e 'RIP) (= (length e) 3)) (list e))
        (#t (append-map sd2-atoms (if (list? e) e '())))))
;;; every <b, a> with <a, b> also present (a, b distinct) rewritten to <a, b>; every atom typed
(define (sd2-symmetrize!)
  (let loop ((done '()))
    (let* ((ats (sd2-atoms (dk-goal)))
           (hit (find-first (lambda (t)
                              (let ((rev (sd2-ip (caddr t) (cadr t))))
                                (and (not (equal? (cadr t) (caddr t)))
                                     (member rev ats)
                                     (not (member rev done)))))
                            ats)))
      (if hit
          (let ((rev (sd2-ip (caddr hit) (cadr hit))))
            (sd2-ft (cadr hit) (caddr hit))
            (dk-cite! 'sip-rip-sym 'v (cadr hit) (caddr hit))
            (subst (list '= rev hit))
            (loop (cons hit done))))))
  (for-each (lambda (t) (sd2-ft (cadr t) (caddr t))) (sd2-atoms (dk-goal))))
;;; EXPAND the goal: open every form value at a constructed vector, then symmetrize.
(define (sd2-expand!)
  (let loop ((fuel 200))
    (if (<= fuel 0) (error "sd2-expand!: out of fuel"))
    (let ((r (sd2-find-redex (dk-goal))))
      (if r
          (begin (subst (sd2-open-law! r)) (loop (- fuel 1)))
          (sd2-symmetrize!)))))
;;; an identity between form values, by expansion and crs
(define (sd2-ip-eq! goal)
  (if (not (dk-asm? goal))
      (dk-have! goal (lambda () (sd2-expand!) (if (not (proof-done? *ps*)) (crs)))))
  goal)
;;; a VECTOR identity A = B in a pre-Hilbert space (PHS and SIP of v in context):
;;; <A - B, A - B> = 0 by expansion, then definiteness, then A - B = 0 gives A = B.
(define (sd2-vec-eq! a b)
  (let ((goal (list '= a b)))
    (if (not (dk-asm? goal))
        (let ((d (sd2-sub a b)))
          (sd2-vt a) (sd2-vt b) (sd2-vt d)
          (sd2-ip-eq! (list '= (sd2-q d) 0))
          (dk-cite! 'phs-definite 'v d)
          (dk-cite! 'frm-v-sub-zero-eq-sip-as-module 'v a b)))
    goal))
;;; the right-nested conjunction of FS, landed from its conjuncts in context
(define (sd2-and fs) (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (sd2-and (cdr fs)))))
(define (sd2-have-and! . fs)
  (let ((c (sd2-and fs)))
    (dk-have! c (lambda () (dk-conj-close! dk-ass!)))
    c))
;;; an IFF instance used forwards / backwards (hilbert-projection.scm's hpr-iff-fwd! / -bwd!)
(define (sd2-iff-fwd! thm . args)
  (let ((iff (apply dk-cite! thm args)))
    (ai iff)
    (detach! (list 'IMPLIES (cadr iff) (caddr iff)))
    (if (dk-head-is? (caddr iff) 'AND) (dk-split-all! (list (caddr iff))))
    (caddr iff)))
(define (sd2-iff-bwd! thm . args)
  (let ((iff (apply dk-cite! thm args)))
    (if (not (dk-asm? (caddr iff)))
        (dk-have! (caddr iff) (lambda () (dk-conj-close! dk-ass!))))
    (ai iff)
    (detach! (list 'IMPLIES (caddr iff) (cadr iff)))
    (cadr iff)))
;;; with (IN q RR), (<= 0 q) in context: (IN (SQRT q) RR), (<= 0 (SQRT q)), SQRT(q)^2 = q
(define (sd2-sqrt! q)
  (if (not (dk-asm? (list 'IN (list 'SQRT q) 'RR)))
      (begin
        (sd2-have-and! (list 'IN q 'RR) (list '<= 0 q))
        (dk-split! (dk-cite! 'sqrt-nonneg q))
        (dk-cite! 'sqrt-sq q)))
  (list 'SQRT q))
;;; <u, u> typed, nonnegative, and its square root's facts
(define (sd2-q-facts! u)
  (sd2-ft u u)
  (dk-cite! 'sip-rip-self-nonneg 'v u)
  (sd2-sqrt! (sd2-q u)))


;;; ==========================================================================================
;;; (3) THE COMPLEXIFICATION AS A COMPLEX INNER PRODUCT SPACE: w = CSIP-CIPS(COMPLEXIFY(v)).
;;; Its operations on pairs, read through the read-offs of sip-b.scm.
;;; ==========================================================================================
(define sd2-pairs '(CARTESIAN (VEC v) (VEC v)))
(define sd2-cx '(COMPLEXIFY v))
(define sd2-w '(CSIP-CIPS (COMPLEXIFY v)))
(define (sd2-w-acc acc) (list acc sd2-w))
(define (sd2-n1 x) (list 'NTH 1 x))
(define (sd2-n2 x) (list 'NTH 2 x))
;;; x in C: its components typed, and x = [x1, x2] in context
(define (sd2-open-pair! x)
  (if (not (and (dk-asm? (list 'IN (sd2-n1 x) '(VEC v))) (dk-asm? (list 'IN (sd2-n2 x) '(VEC v)))))
      (begin
        (dk-split-all! (list (dk-cite! 'cartesian-nth x '(VEC v) '(VEC v))))
        (dk-cite! 'cartesian-pair-eq x '(VEC v) '(VEC v)))))
;;; p = (LIST a b), a, b typable vectors: (IN p C)
(define (sd2-pair-in! p)
  (sd2-vt (cadr p)) (sd2-vt (caddr p))
  (dk-cite! 'pair-in-cartesian '(VEC v) '(VEC v) (cadr p) (caddr p)))
(define (sd2-cx-base!)
  (sd2-pin!)
  (if (not (dk-asm? (list 'IS-COMPLEX-SEMI-INNER-PRODUCT-SPACE sd2-cx))) (dk-cite! 'complexify-is-csip 'v)))
;;; (IN x C) in context: land (IN x (VEC c))
(define (sd2-in-vec-c! x)
  (dk-cite! 'complexify-vec 'v)
  (let ((want (list 'IN x (list 'VEC sd2-cx))))
    (if (not (dk-asm? want)) (dk-rewrite-h! (list 'IN x sd2-pairs) sd2-pairs (list 'VEC sd2-cx)))
    want))
(define (sd2-sp-sip body) (sp (make-wff (list 'FORALL 'v (list 'IMPLIES '(IS-SEMI-INNER-PRODUCT-SPACE v) body)))))
(define (sd2-sp-phs body) (sp (make-wff (list 'FORALL 'v (list 'IMPLIES '(IS-PRE-HILBERT-SPACE v) body)))))
(define (sd2-rw! e) (subst (list '= (cadr e) (caddr e))))
(define (sd2-close-eq!) (if (not (proof-done? *ps*)) (rfl)))

(define (sd2-sub-open! kk)               ; IS-SUBMODULE(v, kk) in context: kk in VEC v
  (dk-cite! 'submodule-subset 'v kk))
(define (sd2-in-kk-pair! z kk)           ; z in kk x kk: components in kk and in VEC v, z = [z1, z2]
  (dk-split-all! (list (dk-cite! 'cartesian-nth z kk kk)))
  (dk-cite! 'subset-mem-fwd kk '(VEC v) (sd2-n1 z))
  (dk-cite! 'subset-mem-fwd kk '(VEC v) (sd2-n2 z))
  (dk-cite! 'cartesian-pair-eq z kk kk)
  (dk-cite! 'pair-in-cartesian '(VEC v) '(VEC v) (sd2-n1 z) (sd2-n2 z))
  (dk-rewrite-h! (list 'IN (list 'LIST (sd2-n1 z) (sd2-n2 z)) sd2-pairs) (list 'LIST (sd2-n1 z) (sd2-n2 z)) z))
;;; (SUBSET kk (VEC v)) in context: land (SUBSET (CARTESIAN kk kk) C), pointwise (the tree's
;;; cartesian-mono lives in theorem-library/product-measure, library measure, which an analysis
;;; file may not cite)
(define (sd2-mm-sub! kk)
  (let ((g (list 'SUBSET (list 'CARTESIAN kk kk) sd2-pairs)))
    (dk-have! g (lambda () (mac 'subset-def)
                           (let* ((lk (dk-peel!)) (z (cadr (car lk)))) (sd2-in-kk-pair! z kk) (ass))))
    g))

;;; ==========================================================================================
;;; (1) Two facts about w = CSIP-CIPS(COMPLEXIFY v)
;;; ==========================================================================================
(define (sd2-wsub p q) (list (sd2-w-acc 'VADD) p (list (sd2-w-acc 'VNEG) q)))
(define (sd2-wqd p q) (let ((d (sd2-wsub p q))) (list (sd2-w-acc 'IP) d d)))
(define (sd2-qsum p q) (list '+ (sd2-qd (sd2-n1 p) (sd2-n1 q)) (sd2-qd (sd2-n2 p) (sd2-n2 q))))
(define sd2-mm '(CARTESIAN cs cs))

;;; the squared distance of w: <p - q, p - q>_w = |p1 - q1|^2 + |p2 - q2|^2
(sd2-sp-phs (forall-guarded '(px_ qx_) (list (list 'IN 'px_ sd2-pairs) (list 'IN 'qx_ sd2-pairs))
               (list '= (sd2-wqd 'px_ 'qx_) (sd2-qsum 'px_ 'qx_))))
(dk-peel!)
(fact 'phs-is-sip 'v)
(sd2-cx-base!)
(dk-cite! 'cxw-is-cips 'v)
(sd2-open-pair! 'px_) (sd2-open-pair! 'qx_)
(let* ((nq (list 'LIST (list '(VNEG v) (sd2-n1 'qx_)) (list '(VNEG v) (sd2-n2 'qx_))))
       (d (list 'LIST (sd2-sub (sd2-n1 'px_) (sd2-n1 'qx_)) (sd2-sub (sd2-n2 'px_) (sd2-n2 'qx_)))))
  (sd2-pair-in! nq) (sd2-pair-in! d)
  (subst (dk-cite! 'cxw-vneg-value 'v 'qx_))
  (subst (dk-cite! 'cxw-vadd-value 'v 'px_ nq))
  (nth-r)
  (subst (dk-cite! 'cxw-ip-self 'v d))
  (nth-r)
  (sd2-ft (sd2-sub (sd2-n1 'px_) (sd2-n1 'qx_)) (sd2-sub (sd2-n1 'px_) (sd2-n1 'qx_)))
  (sd2-ft (sd2-sub (sd2-n2 'px_) (sd2-n2 'qx_)) (sd2-sub (sd2-n2 'px_) (sd2-n2 'qx_)))
  (dk-real! (sd2-qsum 'px_ 'qx_))
  (sd2-close-eq!))
(sd2-qed! 'cxw-dist-sq)
(alias! 'cxw-dist-sq "the squared distance of the complexification is the sum of the squared distances of the components")

;;; cs x cs is closed under midpoints in w, for cs convex
(define (sd2-midclosed ks)
  (list 'FORALL 'hm1_ (list 'IMPLIES (list 'IN 'hm1_ ks)
    (list 'FORALL 'hm2_ (list 'IMPLIES (list 'IN 'hm2_ ks)
      (list 'IN (list (sd2-w-acc 'ACT) 1/2 (list (sd2-w-acc 'VADD) 'hm1_ 'hm2_)) ks))))))
(sd2-sp-phs (list 'FORALL 'cs (list 'IMPLIES '(IS-CONVEX-SUBSET v cs) (sd2-midclosed sd2-mm))))
(define sd2-lk (dk-peel!))
(fact 'phs-is-sip 'v)
(sd2-cx-base!)
(let* ((cv (sd2-iff-fwd! 'is-convex-subset 'v 'cs))
       (all (caddr cv))
       (sm (caddr (cadr (dk-goal))))       ; the goal: (IN ((ACT w) 1/2 ((VADD w) p q)) cs x cs)
       (p (cadr sm)) (q (caddr sm)))
  (sd2-in-kk-pair! p 'cs)
  (sd2-in-kk-pair! q 'cs)
  (let* ((s1 (sd2-add (sd2-n1 p) (sd2-n1 q)))
         (s2 (sd2-add (sd2-n2 p) (sd2-n2 q)))
         (sl (list 'LIST s1 s2)))
    (subst (dk-cite! 'cxw-vadd-value 'v p q))
    (sd2-pair-in! sl)
    (dk-have! '(IN 1/2 CC) (lambda () (arith)))
    (dk-have! '(IN 1/2 RR) (lambda () (arith)))
    (dk-have! '(IN 0 RR) (lambda () (arith)))
    (subst (dk-cite! 'cxw-act-value 'v 1/2 sl))
    (nth-r)
    (dk-have! '(= 1/2 (+ 1/2 (* 0 +i))) (lambda () (crs)))
    (dk-split-all! (list (dk-cite! 'cc-re-im-of 1/2 1/2 0)))
    (subst '(= (real-part 1/2) 1/2))
    (subst '(= (imag-part 1/2) 0))
    (dk-have! '(<= 0 1/2) (lambda () (arith)))
    (dk-have! '(<= 1/2 1) (lambda () (arith)))
    (let* ((g (cadr (dk-goal)))             ; (LIST comp1 comp2)
           (k1 (cadr g)) (k2 (caddr g))
           (m1 (dk-apply! all (sd2-n1 p) (sd2-n1 q) 1/2))
           (m2 (dk-apply! all (sd2-n2 p) (sd2-n2 q) 1/2))
           (c1 (cadr m1)) (c2 (cadr m2)))
      (sd2-vec-eq! k1 c1)
      (sd2-vec-eq! k2 c2)
      (subst (list '= k1 c1))
      (subst (list '= k2 c2))
      (dk-cite! 'pair-in-cartesian 'cs 'cs c1 c2)
      (if (not (proof-done? *ps*)) (ass)))))
(sd2-qed! 'cxw-convex-midpoint-closed)
(alias! 'cxw-convex-midpoint-closed "for a convex set C, C x C is closed under midpoints in the complexification")

;;; ==========================================================================================
;;; (2) PROPOSITION 1.20: the closest point of a nonempty closed convex set exists
;;; ==========================================================================================
(sp (make-wff (forall-guarded '(v cs x_)
   (list '(IS-REAL-HILBERT-SPACE v) '(IS-CONVEX-SUBSET v cs) '(FORSOME sne_ (IN sne_ cs))
         '(IS-CLOSED (SIP-METRIC-SPACE v) cs) '(IN x_ (VEC v)))
   (list 'FORSOME 'sca_ (list 'AND '(IN sca_ cs)
     (list 'FORALL 'scb_ (list 'IMPLIES '(IN scb_ cs) (list '<= (sd2-qd 'sca_ 'x_) (sd2-qd 'scb_ 'x_)))))))))
(dk-peel!)
(dk-cite! 'real-hilbert-space-is-phs 'v)
(fact 'phs-is-sip 'v)
(sd2-cx-base!)
(dk-cite! 'complexify-hilbert 'v)
(dk-cite! 'cxw-vec 'v)
(dk-cite! 'cxw-is-cips 'v)
(dk-cite! 'cxw-convex-midpoint-closed 'v 'cs)
(dk-cite! 'complexify-closed 'v 'cs)
(let* ((cv (sd2-iff-fwd! 'is-convex-subset 'v 'cs))
       (c0 (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f 'sne_)))
                                "the nonemptiness of cs")))
       (xi '(LIST x_ (VZERO v))))
  (sd2-mm-sub! 'cs)
  (dk-rewrite-h! (list 'SUBSET sd2-mm sd2-pairs) sd2-pairs (sd2-w-acc 'VEC))
  (dk-cite! 'pair-in-cartesian 'cs 'cs c0 c0)
  (dk-have! (list 'FORSOME 'hke_ (list 'IN 'hke_ sd2-mm))
    (lambda () (witness! (list 'LIST c0 c0) (lambda () (ass)))))
  (sd2-pair-in! xi)
  (dk-rewrite-h! (list 'IN xi sd2-pairs) sd2-pairs (sd2-w-acc 'VEC))
  (let* ((p (dk-skolem! (dk-cite! 'hilbert-closest-point-midpoint sd2-w sd2-mm xi)))
         (mn (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'hdp_) (memq p (free-vars f))))
                      "the minimality of the pair"))
         (a (sd2-n1 p)) (b (sd2-n2 p)))
    (sd2-in-kk-pair! p 'cs)
    (dk-have! (list 'FORALL 'scb_ (list 'IMPLIES '(IN scb_ cs) (list '<= (sd2-qd a 'x_) (sd2-qd 'scb_ 'x_))))
      (lambda ()
        (let* ((lk (dk-peel!)) (c (cadr (car lk))) (q (list 'LIST c b)))
          (dk-cite! 'subset-mem-fwd 'cs '(VEC v) c)
          (dk-cite! 'pair-in-cartesian 'cs 'cs c b)
          (sd2-pair-in! q)
          (let* ((le (dk-apply! mn q))
                 (e1 (dk-nth-h! (dk-cite! 'cxw-dist-sq 'v p xi)))
                 (e2 (dk-nth-h! (dk-cite! 'cxw-dist-sq 'v q xi)))
                 (l1 (dk-rewrite-h! le (cadr e1) (caddr e1)))
                 (l2 (dk-rewrite-h! l1 (cadr e2) (caddr e2))))
            (sd2-q-facts! (sd2-sub a 'x_))
            (sd2-q-facts! (sd2-sub c 'x_))
            (sd2-q-facts! (sd2-sub b '(VZERO v)))
            (dk-ineq! l2)))))
    (witness! a (lambda () (dk-conj-close! dk-ass!)))))
(sd2-qed! 'real-convex-closest-point)
(alias! 'real-convex-closest-point "the closest point of a nonempty closed convex set of a real Hilbert space exists (Proposition 1.20)")

;;; ==========================================================================================
;;; (3) THE VARIATIONAL INEQUALITY IS NECESSARY: a closest point a of a convex set has
;;; <x - a, c - a> <= 0 for every c of the set (semidefinite form suffices).
;;; ==========================================================================================
;; at t in [0, 1] (typed, with its bounds in context): the convex point m_t, the minimality
;; at it, and |m_t - x|^2 = |a - x|^2 + (TT - 2 TO) with TT, TO the names given.  Returns
;; (le . id).
(define (sd2-at-t! all mn c qa tv to-name tt-name to-term tt-term)
  (let* ((m (dk-apply! all 'a_ c tv))
         (mt (cadr m))
         (le (begin (dk-cite! 'subset-mem-fwd 'cs '(VEC v) mt) (dk-apply! mn mt)))
         (qm (sd2-qd mt 'x_))
         (id (list '= qm (list '+ qa (list '- tt-name (list '* 2 to-name))))))
    (sd2-q-facts! (sd2-sub mt 'x_))
    (dk-have! id
      (lambda ()
        (if (not (equal? to-name to-term)) (subst (list '= to-name to-term)))
        (if (not (equal? tt-name tt-term)) (subst (list '= tt-name tt-term)))
        (sd2-expand!)
        (if (not (proof-done? *ps*)) (crs))))
    (cons le id)))

(define sd2-lk0 #f)
(sp (make-wff (forall-guarded '(v cs x_ a_)
   '((IS-SEMI-INNER-PRODUCT-SPACE v) (IS-CONVEX-SUBSET v cs) (IN x_ (VEC v)) (IN a_ cs))
   (list 'IMPLIES (list 'FORALL 'scd_ (list 'IMPLIES '(IN scd_ cs) (list '<= (sd2-qd 'a_ 'x_) (sd2-qd 'scd_ 'x_))))
         (list 'FORALL 'scc_ (list 'IMPLIES '(IN scc_ cs) (list '<= (sd2-ip (sd2-sub 'x_ 'a_) (sd2-sub 'scc_ 'a_)) 0)))))))
(set! sd2-lk0 (dk-peel!))
(sd2-pin!)
(let* ((mn (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'scd_))) "the minimality of a"))
       (c (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (eq? (caddr f) 'cs) (not (eq? (cadr f) 'a_)))) sd2-lk0)))
       (cv (sd2-iff-fwd! 'is-convex-subset 'v 'cs))
       (all (caddr cv))
       (o (sd2-ip (sd2-sub 'x_ 'a_) (sd2-sub c 'a_)))
       (q (sd2-qd c 'a_))
       (qa (sd2-qd 'a_ 'x_)))
  (dk-cite! 'subset-mem-fwd 'cs '(VEC v) 'a_)
  (dk-cite! 'subset-mem-fwd 'cs '(VEC v) c)
  (sd2-ft (sd2-sub 'x_ 'a_) (sd2-sub c 'a_))
  (sd2-q-facts! (sd2-sub c 'a_))
  (sd2-q-facts! (sd2-sub 'a_ 'x_))
  (dk-have! '(IN 0 RR) (lambda () (arith)))
  (dk-have! '(IN 1 RR) (lambda () (arith)))
  (use-em (list '<= o 0)
    (lambda () (ass))
    (lambda ()
      (dk-cite! 'rr-not-le-lt o 0)
      (dk-cite! 'rr-pos-rr-of-lt o)
      (let* ((s (dk-skolem! (dk-cite! 'rr-scale-eps q o)))
             (small (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (memq s (free-vars f))))
                             "the rr-scale-eps universal")))
        (dk-cite! 'rr-pos-rr-in-rr s)
        (dk-cite! 'rr-lt-of-pos-rr s)
        (dk-have! (list '<= 0 s) (lambda () (dk-ineq! (list '< 0 s))))
        (use-em (list '<= s 1)
          (lambda ()                        ; t = s:  2 s o <= s (s q) <= s o, and s o > 0
            (dk-have! (list '<= s s) (lambda () (dk-ineq!)))
            (let* ((sm (dk-apply! small s))  ; q s <= o
                   (so (list '* s o))
                   (sq (list '* s q))
                   (ssq (list '* s sq)))
              (dk-have! (list 'IN so 'RR) (lambda () (type-term)))
              (dk-have! (list 'IN sq 'RR) (lambda () (type-term)))
              (dk-have! (list 'IN ssq 'RR) (lambda () (type-term)))
              (let* ((na (dk-name! so))
                     (nb (dk-name! ssq))
                     (r (sd2-at-t! all mn c qa s na nb so ssq))
                     (pos (dk-rewrite-h! (dk-cite! 'rr-mul-pos s o) so na))
                     (qs (begin (dk-have! (list 'IN (list '* q s) 'RR) (lambda () (type-term))) (list '* q s)))
                     (mul (dk-cite! 'rr-mul-le-right qs o s)))
                (dk-have! (list '= ssq (list '* (list '* q s) s)) (lambda () (crs)))
                (dk-have! (list '= so (list '* o s)) (lambda () (crs)))
                (dk-have! (list '<= nb na)
                  (lambda ()
                    (subst (list '= nb ssq)) (subst (list '= na so))
                    (subst (list '= ssq (list '* (list '* q s) s)))
                    (subst (list '= so (list '* o s)))
                    (ass)))
                (dk-ineq! (car r) (cdr r) (list '<= nb na) pos))))
          (lambda ()                        ; 1 < s, t = 1:  2 o <= q <= o
            (dk-cite! 'rr-not-le-lt s 1)
            (dk-have! '(<= 0 1) (lambda () (arith)))
            (dk-have! '(<= 1 1) (lambda () (arith)))
            (dk-have! (list '<= 1 s) (lambda () (dk-ineq! (list '< 1 s))))
            (let* ((sm (dk-apply! small 1))  ; q * 1 <= o
                   (r (sd2-at-t! all mn c qa 1 o q o q)))
              (dk-ineq! (car r) (cdr r) sm (list '< 0 o)))))))))
(sd2-qed! 'real-convex-variational-necessary)
(alias! 'real-convex-variational-necessary "a closest point of a convex set satisfies the variational inequality (Proposition 1.20)")

;;; ==========================================================================================
;;; (4) PROPOSITION 1.20 AS THE NOTES STATE IT (with the nonemptiness the notes leave tacit):
;;; there is a unique closest point; and the closest point is CHARACTERISED by the
;;; variational inequality.
;;; ==========================================================================================
(define (sd2-closest y) (list 'FORALL 'scc_ (list 'IMPLIES '(IN scc_ cs) (list '<= (sd2-qd y 'x_) (sd2-qd 'scc_ 'x_)))))
;;; cite THM at ARGS and detach what is left of the chain (each antecedent must be in context)
(define (sd2-cite-all! thm . args)
  (let loop ((r (apply dk-cite! thm args)))
    (if (dk-head-is? r 'IMPLIES) (loop (dk-landed-1 (lambda () (detach! r)))) r)))

(sp (make-wff (forall-guarded '(v cs x_)
   (list '(IS-REAL-HILBERT-SPACE v) '(IS-CONVEX-SUBSET v cs) '(FORSOME sne_ (IN sne_ cs))
         '(IS-CLOSED (SIP-METRIC-SPACE v) cs) '(IN x_ (VEC v)))
   (list 'FORSOME 'sca_ (list 'AND '(IN sca_ cs)
     (list 'AND (sd2-closest 'sca_)
       (list 'FORALL 'scb_ (list 'IMPLIES '(IN scb_ cs) (list 'IMPLIES (sd2-closest 'scb_) '(= scb_ sca_))))))))))
(dk-peel!)
(dk-cite! 'real-hilbert-space-is-phs 'v)
(let ((a (dk-skolem! (dk-cite! 'real-convex-closest-point 'v 'cs 'x_))))
  (witness! a
    (lambda ()
      (dk-conj-close!
        (lambda ()
          (if (and (dk-head-is? (dk-goal) 'FORALL) (dk-contains? (dk-goal) 'scb_))
              (let* ((lk (dk-peel!))
                     (b (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (eq? (caddr f) 'cs))) lk))))
                (sd2-cite-all! 'real-convex-closest-unique 'v 'cs 'x_ b a)
                (ass))
              (ass)))))))
(sd2-qed! 'real-convex-closest-point-unique)
(alias! 'real-convex-closest-point-unique "a nonempty closed convex set of a real Hilbert space has exactly one closest point to each x (Proposition 1.20)")

(sp (make-wff (forall-guarded '(v cs x_ a_)
   '((IS-SEMI-INNER-PRODUCT-SPACE v) (IS-CONVEX-SUBSET v cs) (IN x_ (VEC v)) (IN a_ cs))
   (list 'IFF (list 'FORALL 'scd_ (list 'IMPLIES '(IN scd_ cs) (list '<= (sd2-qd 'a_ 'x_) (sd2-qd 'scd_ 'x_))))
              (list 'FORALL 'scc_ (list 'IMPLIES '(IN scc_ cs) (list '<= (sd2-ip (sd2-sub 'x_ 'a_) (sd2-sub 'scc_ 'a_)) 0)))))))
(dk-peel!)
(sd2-pin!)
(sd2-iff-fwd! 'is-convex-subset 'v 'cs)
(dk-iff! (lambda (g) (dk-contains? g 'scc_))
  (lambda () (sd2-cite-all! 'real-convex-variational-necessary 'v 'cs 'x_ 'a_) (ass))
  (lambda () (sd2-cite-all! 'real-convex-variational-closest 'v 'cs 'x_ 'a_) (ass)))
(sd2-qed! 'real-convex-closest-iff-variational)
(alias! 'real-convex-closest-iff-variational "a point of a convex set is the closest point to x iff <x - a, c - a> <= 0 on the set")
