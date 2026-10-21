;;; hp-midpoint.scm -- the closest-point theorem of hilbert-projection.scm for a
;;; NONEMPTY CLOSED set CLOSED UNDER MIDPOINTS, instead of a closed submodule.
;;; Agent SIP-D2, 2026-10-19 (scratchpad/triage/SIP-D2.md; the user's decision of
;;; 2026-10-19 on SIP-D-REPORT.md finding 1).  All PROVEN modulo 0.
;;;
;;;   cips-dist-sq-inf-midpoint        (a) of hilbert-projection's s.(4), for a
;;;                                    nonempty SUBSET kk of VEC(v)
;;;   cips-midpoint-estimate-midpoint  (b), the book's (2.6), for kk closed under
;;;                                    p, q |-> (1/2)(p + q)
;;;   hilbert-closest-point-midpoint   (c)-(d), kk nonempty, closed, midpoint-closed
;;;   cips-dist-sq-inf-via-midpoint, cips-midpoint-estimate-via-midpoint,
;;;   hilbert-closest-point-via-midpoint
;;;                                    the three submodule statements of
;;;                                    hilbert-projection.scm, word for word, as
;;;                                    corollaries (a submodule is a nonempty
;;;                                    subset closed under midpoints)
;;;
;;; The proofs of the general forms are hilbert-projection.scm's, adapted: the only
;;; uses of IS-SUBMODULE there were `kk subset VEC(v)' (submodule-subset), a point
;;; of kk (submodule-vzero-in) and the midpoint (submodule-vadd-closed,
;;; submodule-act-closed at 1/2).  The minimizing-sequence argument is unchanged.
;;; The helpers are copied from that file with the prefix `hpm-' (a theorem-library
;;; file's defines are local to it).
;;;
;;; SPLICE PLAN (for the integrator, when hilbert-projection.scm is claimed).  In s.(4) of
;;; hilbert-projection.scm: (1) add the statement builders `hpm-midclosed', `hpm-nonempty',
;;; `hpm-inf-concl', `hpm-lb', `hpm-est-concl', `hpm-cp-concl' as `hpr-' helpers; (2) put
;;; the three general theorems, under their -midpoint names, where cips-dist-sq-inf,
;;; cips-midpoint-estimate and hilbert-closest-point now stand (their proofs below, with `hpm-'
;;; read as `hpr-' -- the copied helpers are hilbert-projection's own); (3) re-prove the three
;;; OLD names as the corollaries below (`hpm-submodule-hyps!' and four lines each), under the
;;; old names; (4) drop this file.  The -via-midpoint names exist only so that this file can be
;;; probed beside the band's hilbert-projection; they are alpha-identical to the old statements
;;; (checked on the probe image), so no citer changes.

;;; LOAD WINDOW.  After theorem-library/hilbert-projection (every lemma it cites is
;;; there or earlier).  Nothing in it is SIP vocabulary.

;;; ====================================================================
;;; File-local driver (the `hpm-' prefix), copied from hilbert-projection.scm.
;;; ====================================================================

;;; The inner product space every helper below talks about: the eigenvariable
;;; the proof's peel minted for it, set by each proof.
(define hpm-v 'v)
(define (hpm-ip a b) (list (list 'IP hpm-v) a b))
(define (hpm-sub a b) (list (list 'VADD hpm-v) a (list (list 'VNEG hpm-v) b)))
(define (hpm-add a b) (list (list 'VADD hpm-v) a b))
(define (hpm-act c a) (list (list 'ACT hpm-v) c a))
(define (hpm-q a) (hpm-ip a a))

(define (hpm-op? e op)
  (and (pair? e) (pair? (car e)) (eq? (car (car e)) op) (equal? (cadr (car e)) hpm-v)))
(define (hpm-zero? e) (equal? e (list 'VZERO hpm-v)))

;;; land (IN e (VEC v)) for a vector term built from typed atoms
(define (hpm-vt! e)
  (let ((goal (list 'IN e (list 'VEC hpm-v))))
    (cond ((and (dk-asm? goal) (not (or (hpm-op? e 'VADD) (hpm-op? e 'VNEG) (hpm-op? e 'ACT))))
           goal)
          ((dk-asm? goal)                  ; typed: still type the parts, which the laws need
           (cond ((hpm-op? e 'VADD) (hpm-vt! (cadr e)) (hpm-vt! (caddr e)))
                 ((hpm-op? e 'VNEG) (hpm-vt! (cadr e)))
                 ((hpm-op? e 'ACT)  (hpm-ct! (cadr e)) (hpm-vt! (caddr e))))
           goal)
          ((hpm-op? e 'VADD) (hpm-vt! (cadr e)) (hpm-vt! (caddr e))
                             (dk-cite! 'cips-vadd-type hpm-v (cadr e) (caddr e)) goal)
          ((hpm-op? e 'VNEG) (hpm-vt! (cadr e))
                             (dk-cite! 'cips-vneg-type hpm-v (cadr e)) goal)
          ((hpm-op? e 'ACT)  (hpm-ct! (cadr e)) (hpm-vt! (caddr e))
                             (dk-cite! 'cips-act-type hpm-v (cadr e) (caddr e)) goal)
          ((hpm-zero? e) (dk-cite! 'cips-vzero-in hpm-v) goal)
          (#t (error "hpm-vt!: no typing for the vector" (expression->string e))))))

;;; land (IN c CC) for a scalar term
(define (hpm-ct! c)
  (let ((goal (list 'IN c 'CC)))
    (cond ((dk-asm? goal) goal)
          ((eqv? c +i) (dk-cite! 'cc-i-in) goal)
          ((number? c) (dk-have! goal (lambda () (arith))) goal)
          ((dk-asm? (list 'IN c 'RR)) (dk-cite! 'rr-subset-cc c) goal)
          ((hpm-op? c 'IP) (hpm-vt! (cadr c)) (hpm-vt! (caddr c))
                           (dk-cite! 'cips-ip-type hpm-v (cadr c) (caddr c)) goal)
          ((and (pair? c) (eq? (car c) 'conjugate))
           (hpm-ct! (cadr c)) (dk-cite! 'cc-conjugate-closed (cadr c)) goal)
          ((and (pair? c) (memq (car c) '(* +)) (= (length c) 3))
           (hpm-ct! (cadr c)) (hpm-ct! (caddr c))
           (hpm-have-and! (list 'IN (cadr c) 'CC) (list 'IN (caddr c) 'CC))
           (dk-cite! (if (eq? (car c) '*) 'cc-mul-closed 'cc-add-closed) (cadr c) (caddr c)) goal)
          ((and (pair? c) (eq? (car c) '-) (= (length c) 3))
           (hpm-ct! (cadr c)) (hpm-ct! (caddr c))
           (dk-cite! 'cc-sub-in-cc (cadr c) (caddr c)) goal)
          ((and (pair? c) (eq? (car c) '-) (= (length c) 2))
           (hpm-ct! (cadr c)) (dk-cite! 'cc-neg-closed (cadr c)) goal)
          (#t (dk-have! goal (lambda () (type-term))) goal))))

;;; the first inner-product term in E (preorder) with a compound argument
(define (hpm-find-redex e)
  (cond ((not (pair? e)) #f)
        ((and (hpm-op? e 'IP) (= (length e) 3)
              (or (hpm-compound? (cadr e)) (hpm-compound? (caddr e))))
         e)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((hpm-find-redex (car l)) => (lambda (x) x))
                    (#t (loop (cdr l))))))))
(define (hpm-compound? e)
  (or (hpm-op? e 'VADD) (hpm-op? e 'VNEG) (hpm-op? e 'ACT) (hpm-zero? e)))

;;; the law instance that opens the redex <a, b>
(define (hpm-open-law! r)
  (let ((a (cadr r)) (b (caddr r)))
    (hpm-vt! a) (hpm-vt! b)
    (cond ((hpm-op? a 'VADD) (dk-cite! 'cips-ip-add-left hpm-v (cadr a) (caddr a) b))
          ((hpm-op? a 'VNEG) (dk-cite! 'cips-ip-neg-left hpm-v (cadr a) b))
          ((hpm-op? a 'ACT)  (dk-cite! 'cips-ip-homog-left hpm-v (cadr a) (caddr a) b))
          ((hpm-zero? a)     (dk-cite! 'cips-ip-zero-left hpm-v b))
          ((hpm-op? b 'VADD) (dk-cite! 'cips-ip-add-right hpm-v a (cadr b) (caddr b)))
          ((hpm-op? b 'VNEG) (dk-cite! 'cips-ip-neg-right hpm-v a (cadr b)))
          ((hpm-op? b 'ACT)  (dk-cite! 'cips-ip-conj-homog-right hpm-v (cadr b) a (caddr b)))
          ((hpm-zero? b)     (dk-cite! 'cips-ip-zero-right hpm-v a))
          (#t (error "hpm-open-law!: not a redex" (expression->string r))))))

;;; a conjugate that can be pushed inwards: of a real (a numeral, or typed RR
;;; in context), of a product, sum, negation or conjugate, of an inner product
(define (hpm-conj-redex? e)
  (and (pair? e) (eq? (car e) 'conjugate) (= (length e) 2)
       (let ((x (cadr e)))
         (or (number? x) (dk-asm? (list 'IN x 'RR))
             (and (pair? x) (memq (car x) '(* + conjugate)))
             (and (pair? x) (eq? (car x) '-) (= (length x) 2))
             (and (hpm-op? x 'IP) (= (length x) 3))))))
(define (hpm-find-real-conj e)
  (cond ((not (pair? e)) #f)
        ((hpm-conj-redex? e) e)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((hpm-find-real-conj (car l)) => (lambda (x) x))
                    (#t (loop (cdr l))))))))

;;; EXPAND the goal: every inner product of a constructed vector is opened by
;;; its law (first argument first), and every conjugate of a real is dropped,
;;; until the goal is a polynomial in inner products of ATOMS.  Loops on a redex
;;; test, never on a count.
(define (hpm-expand!)
  (let loop ((fuel 200))
    (if (<= fuel 0) (error "hpm-expand!: out of fuel"))
    (let ((r (hpm-find-redex (dk-goal))))
      (if r
          (let ((eq (hpm-open-law! r)))
            (subst eq)
            (loop (- fuel 1)))
          (let ((c (hpm-find-real-conj (dk-goal))))
            (if c
                (begin
                  (hpm-push-conj! c)
                  (loop (- fuel 1)))))))))

;;; one step of pushing a conjugate inwards
(define (hpm-push-conj! c)
  (let ((x (cadr c)))
    (cond ((or (number? x) (dk-asm? (list 'IN x 'RR)))
           (if (number? x) (dk-have! (list 'IN x 'RR) (lambda () (arith))))
           (subst (dk-cite! 'cc-conjugate-fixes-rr x)))
          ((hpm-op? x 'IP)
           (hpm-vt! (cadr x)) (hpm-vt! (caddr x))
           (dk-cite! 'cips-ip-conj-sym hpm-v (cadr x) (caddr x))
           (subst (list '= c (hpm-ip (caddr x) (cadr x)))))
          ((eq? (car x) 'conjugate)
           (hpm-ct! (cadr x)) (subst (dk-cite! 'cc-conjugate-involution (cadr x))))
          ((eq? (car x) '-)
           (hpm-ct! (cadr x)) (subst (dk-cite! 'cc-conjugate-neg (cadr x))))
          (#t
           (hpm-ct! (cadr x)) (hpm-ct! (caddr x))
           (hpm-have-and! (list 'IN (cadr x) 'CC) (list 'IN (caddr x) 'CC))
           (subst (dk-cite! (if (eq? (car x) '*) 'cc-conjugate-mul 'cc-conjugate-add)
                            (cadr x) (caddr x)))))))

;;; with (IN a RR) and (0 <= a) in context: land (IN (SQRT a) RR), 0 <= SQRT(a)
;;; and SQRT(a) * SQRT(a) = a
(define (hpm-sqrt! a)
  (if (not (dk-asm? (list 'IN (list 'SQRT a) 'RR)))
      (begin
        (dk-have! (list 'AND (list 'IN a 'RR) (list '<= 0 a)))
        (dk-split! (dk-cite! 'sqrt-nonneg a))
        (dk-cite! 'sqrt-sq a))))

;;; <u,u> is real and nonnegative
(define (hpm-q-facts! u)
  (hpm-vt! u)
  (dk-cite! 'cips-ip-self-real hpm-v u)
  (dk-cite! 'cips-ip-self-nonneg hpm-v u))

;;; rewrite ||u|| * ||u|| in the goal to <u, u>
(define (hpm-norm-sq! u)
  (hpm-vt! u)
  (subst (dk-cite! 'ip-norm-unfold hpm-v u))
  (hpm-q-facts! u)
  (hpm-sqrt! (hpm-q u))
  (subst (dk-cite! 'sqrt-sq (hpm-q u))))
(define (hpm-nsq u) (list '* (list 'IP-NORM hpm-v u) (list 'IP-NORM hpm-v u)))

;;; an IFF instance used forwards: cite THM at ARGS, land its right side (split)
(define (hpm-iff-fwd! thm . args)
  (let ((iff (apply dk-cite! thm args)))
    (ai iff)
    (detach! (list 'IMPLIES (cadr iff) (caddr iff)))
    (if (dk-head-is? (caddr iff) 'AND) (dk-split-all! (list (caddr iff))))
    (caddr iff)))

;;; an IFF instance used backwards: its right side's conjuncts are in context;
;;; land the left side and return it
(define (hpm-iff-bwd! thm . args)
  (let ((iff (apply dk-cite! thm args)))
    (if (not (dk-asm? (caddr iff)))
        (dk-have! (caddr iff) (lambda () (dk-conj-close! dk-ass!))))
    (ai iff)
    (detach! (list 'IMPLIES (caddr iff) (cadr iff)))
    (cadr iff)))

;;; the right-nested conjunction of FS, landed from its conjuncts in context
(define (hpm-and fs)
  (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (hpm-and (cdr fs)))))
(define (hpm-have-and! . fs)
  (let ((c (hpm-and fs)))
    (dk-have! c (lambda () (dk-conj-close! dk-ass!)))
    c))

;;; type every inner product of atoms in the goal (crs wants its atoms in CC)
(define (hpm-type-ips! e)
  (cond ((not (pair? e)) #t)
        ((hpm-op? e 'IP) (hpm-ct! e))
        ((and (eq? (car e) 'conjugate) (= (length e) 2)) (hpm-ct! e))
        (#t (for-each hpm-type-ips! e))))

(define (hpm-qd p xi) (hpm-q (hpm-sub p xi)))

;;; Q(A) = Q(B) for two expressions of one vector, by expansion
(define (hpm-q-eq! a b)
  (let ((goal (list '= (hpm-q a) (hpm-q b))))
    (if (not (dk-asm? goal))
        (begin (hpm-vt! a) (hpm-vt! b)
               (dk-have! goal (lambda () (hpm-expand!) (hpm-type-ips! (dk-goal)) (crs)))))
    goal))

;;; (c)-(d) THE CLOSEST POINT.  The minimizing sequence is a function symbol
;;; (dk-abstract!) whose value at n is CHOICE of the n-th approximation set.
(define hpm-cp-aa #f)                 ; alpha^2, skolemised
(define hpm-cp-apx #f)                ; forall n. exists phi in K with the n-bound
(define (hpm-cp-set n)
  (list 'SEP 'hcz_ 'kk (list '<= (hpm-qd 'hcz_ 'xi) (list '+ hpm-cp-aa (list 'recip (list '+ n 1))))))

;;; with n in NN: land (IN (CHOICE S_n) S_n) and the two facts it carries
(define (hpm-cp-choice! n)
  (let* ((ss (hpm-cp-set n))
         (ch (list 'CHOICE ss))
         (mem (list 'IN ch ss)))
    (if (not (dk-asm? mem))
        (let* ((ex (dk-apply! hpm-cp-apx n))
               (q (dk-skolem! ex)))
          (choose-mem! ss q (lambda () (in-sep! (lambda () (ass)) (lambda () (ass)))))))
    (sep-me mem)
    (dk-split-all!)
    ch))

;;; the Cauchy estimate at m, n >= N:  d(g m, g n) <= eps
(define (hpm-cp-cauchy-pair! ms g ee eps e4 small m n)
  (let* ((gm (list g m)) (gn (list g n))
         (pw (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'hcn_)))
                      "the pointwise bound")))
    (dk-split! (dk-apply! pw m))
    (dk-split! (dk-apply! pw n))
    (for-each (lambda (k) (dk-cite! 'subset-mem-fwd 'kk '(VEC v) k)) (list gm gn))
    (let ((est (dk-apply! (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'p1_)))
                                   "the (2.6) estimate")
                          gm gn))
          (rm (list 'recip (list '+ m 1)))
          (rn (list 'recip (list '+ n 1))))
      (for-each (lambda (k) (dk-cite! 'nn-recip-succ-pos k)
                            (dk-cite! 'rr-pos-rr-in-rr (list 'recip (list '+ k 1))))
                (list m n))
      (let ((bm (dk-apply! small m)) (bn (dk-apply! small n)))
        (for-each hpm-q-facts! (list (hpm-sub gm gn) (hpm-sub gm 'xi) (hpm-sub gn 'xi)))
        (let* ((q (hpm-qd gm gn)) (s (list 'SQRT q)))
          (dk-have! (list '<= q ee)
            (lambda () (dk-ineq! est bm bn (list '= e4 (list '* 1/4 ee))
                                 (list '<= (hpm-qd gm 'xi) (list '+ hpm-cp-aa rm))
                                 (list '<= (hpm-qd gn 'xi) (list '+ hpm-cp-aa rn)))))
          (hpm-sqrt! q)
          (hpm-have-and! (list 'IN q 'RR) (list '<= 0 q))
          (hpm-have-and! (list 'IN ee 'RR) (list '<= q ee))
          (dk-cite! 'sqrt-mono q ee)
          (subst (dk-cite! 'ip-metric-space-dist 'v gm gn))
          (dk-ineq! (list '<= s (list 'SQRT ee)) (list '= (list 'SQRT ee) eps)))))))

;;; the tail of g lies in the closed ball about xi of radius SQRT(aa + d)
(define (hpm-cp-tail-in-ball! ms g d r small n)
  (let* ((gn (list g n))
         (pw (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'hcn_)))
                      "the pointwise bound"))
         (rn (list 'recip (list '+ n 1))))
    (dk-split! (dk-apply! pw n))
    (dk-cite! 'subset-mem-fwd 'kk '(VEC v) gn)
    (dk-cite! 'nn-recip-succ-pos n)
    (dk-cite! 'rr-pos-rr-in-rr rn)
    (let ((bn (dk-apply! small n))
          (q (hpm-qd 'xi gn)))
      (hpm-q-facts! (hpm-sub 'xi gn))
      (hpm-q-facts! (hpm-sub gn 'xi))
      (hpm-q-eq! (hpm-sub 'xi gn) (hpm-sub gn 'xi))
      (dk-have! (list '<= q (list '+ hpm-cp-aa d))
        (lambda () (dk-ineq! bn (list '= q (hpm-qd gn 'xi))
                             (list '<= (hpm-qd gn 'xi) (list '+ hpm-cp-aa rn)))))
      (hpm-have-and! (list 'IN q 'RR) (list '<= 0 q))
      (hpm-have-and! (list 'IN (list '+ hpm-cp-aa d) 'RR) (list '<= q (list '+ hpm-cp-aa d)))
      (dk-cite! 'sqrt-mono q (list '+ hpm-cp-aa d))
      (dk-cite! 'ip-metric-space-pts 'v)
      (dk-have! (list 'IN gn (list 'PTS ms))
        (lambda () (subst (list '== (list 'PTS ms) '(VEC v))) (ass)))
      (dk-have! (list '<= (list (list 'DIST ms) 'xi gn) r)
        (lambda () (subst (dk-cite! 'ip-metric-space-dist 'v 'xi gn)) (ass)))
      (hpm-iff-bwd! 'closed-ball-membership ms 'xi r gn)
      (ass))))


;;; ====================================================================
;;; The hypotheses
;;; ====================================================================

;;; kk is closed under midpoints: p, q in kk => (1/2)(p + q) in kk
(define (hpm-midclosed ks)
  (list 'FORALL 'hm1_ (list 'IMPLIES (list 'IN 'hm1_ ks)
    (list 'FORALL 'hm2_ (list 'IMPLIES (list 'IN 'hm2_ ks)
      (list 'IN (hpm-act 1/2 (hpm-add 'hm1_ 'hm2_)) ks))))))
;;; kk is nonempty
(define (hpm-nonempty ks) (list 'FORSOME 'hke_ (list 'IN 'hke_ ks)))

;;; the conclusions, shared by the general forms and the corollaries
(define hpm-inf-concl
  (list 'FORSOME 'aa
    (hpm-and
      (list '(IN aa RR)
            '(<= 0 aa)
            (list 'FORALL 'hdp_ (list 'IMPLIES '(IN hdp_ kk) (list '<= 'aa (hpm-qd 'hdp_ 'xi))))
            (list 'FORALL 'hdn_ (list 'IMPLIES '(IN hdn_ NN)
               (list 'FORSOME 'hdq_ (list 'AND '(IN hdq_ kk)
                  (list '<= (hpm-qd 'hdq_ 'xi) '(+ aa (recip (+ hdn_ 1))))))))))))
(define hpm-lb (list 'FORALL 'hdp_ (list 'IMPLIES '(IN hdp_ kk) (list '<= 'aa (hpm-qd 'hdp_ 'xi)))))
(define hpm-est-concl
  (forall-guarded '(p1_ p2_) '((IN p1_ kk) (IN p2_ kk))
    (list '<= (hpm-qd 'p1_ 'p2_)
          (list '- (list '+ (list '* 2 (hpm-qd 'p1_ 'xi)) (list '* 2 (hpm-qd 'p2_ 'xi)))
                   '(* 4 aa)))))
(define hpm-cp-concl
  (list 'FORSOME 'hcp_
    (list 'AND '(IN hcp_ kk)
      (list 'FORALL 'hdp_ (list 'IMPLIES '(IN hdp_ kk)
                                (list '<= (hpm-qd 'hcp_ 'xi) (hpm-qd 'hdp_ 'xi)))))))

;;; ====================================================================
;;; (a) the infimum of the squared distance from xi to a nonempty subset kk
;;; ====================================================================
(set! hpm-v 'v)
(sp (make-wff (forall-guarded '(v kk xi)
   (list '(IS-COMPLEX-INNER-PRODUCT-SPACE v) '(SUBSET kk (VEC v)) (hpm-nonempty 'kk) '(IN xi (VEC v)))
   hpm-inf-concl)))
(dk-peel!)
(let* ((ss (list 'SEP 'hrs_ 'RR
                 (list 'FORSOME 'hrp_ (list 'AND '(IN hrp_ kk) (list '= 'hrs_ (list '- (hpm-qd 'hrp_ 'xi)))))))
       (in-kk! (lambda (p) (dk-cite! 'subset-mem-fwd 'kk '(VEC v) p)))
       (neg-in-ss! (lambda (p)             ; p in kk: land -Q(p - xi) in ss
                     (in-kk! p)
                     (hpm-q-facts! (hpm-sub p 'xi))
                     (dk-cite! 'rr-neg-closed (hpm-qd p 'xi))
                     (dk-have! (list 'IN (list '- (hpm-qd p 'xi)) ss)
                       (lambda ()
                         (in-sep! (lambda () (ass))
                                  (lambda () (witness! p (lambda () (dk-conj-close!
                                     (lambda () (if (dk-head-is? (dk-goal) 'IN) (ass) (rfl))))))))))))
       (open-ss! (lambda (w)               ; w in ss: land p in kk, w = -Q(p - xi); return p
                   (sep-me (list 'IN w ss))
                   (let ((ex (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (memq w (free-vars f))))
                                      "the separation's existential")))
                     (dk-skolem! ex))))
       (k0 (dk-skolem! (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f 'hke_)))
                                "the nonemptiness of kk"))))
  (dk-have! (list 'SUBSET ss 'RR)
    (lambda () (mac 'subset-def) (let ((zv (dk-di-var!))) (sep-me (list 'IN zv ss)) (dk-split-all!) (ass))))
  (neg-in-ss! k0)
  (dk-have! (list 'FORSOME 'hrx_ (list 'IN 'hrx_ ss))
    (lambda () (witness! (list '- (hpm-qd k0 'xi)) (lambda () (ass)))))
  (dk-have! '(IN 0 RR) (lambda () (arith)))
  (dk-have! (list 'FORALL 'hrx_ (list 'IMPLIES (list 'IN 'hrx_ ss) '(<= hrx_ 0)))
    (lambda ()
      (dk-peel!)
      (let* ((w (cadr (dk-goal)))
             (p (open-ss! w)))
        (in-kk! p)
        (hpm-q-facts! (hpm-sub p 'xi))
        (dk-ineq! (list '= w (list '- (hpm-qd p 'xi))) (list '<= 0 (hpm-qd p 'xi))))))
  (dk-have! (list 'RR-UPPER-BOUND ss 0) (lambda () (hpm-iff-bwd! 'rr-upper-bound ss 0) (ass)))
  (dk-have! (list 'FORSOME 'hrb_ (list 'RR-UPPER-BOUND ss 'hrb_)) (lambda () (witness! 0 (lambda () (ass)))))
  (hpm-iff-bwd! 'rr-bounded-above ss)
  (let* ((sg (list 'SUP ss))
         (aa (list '- sg)))
    (dk-cite! 'rr-sup-in ss)
    (dk-cite! 'rr-sup-least ss 0)
    (dk-have! (list '<= 0 aa) (lambda () (dk-ineq! (list '<= sg 0))))
    (dk-cite! 'rr-sup-upper ss)
    (let ((ub (caddr (hpm-iff-fwd! 'rr-upper-bound ss sg))))
      (dk-cite! 'rr-neg-closed sg)
      (dk-have! (list 'FORALL 'hdp_ (list 'IMPLIES '(IN hdp_ kk) (list '<= aa (hpm-qd 'hdp_ 'xi))))
        (lambda ()
          (dk-peel!)
          (let ((p (cadr (cadr (caddr (dk-goal))))))
            (neg-in-ss! p)
            (let ((le (dk-apply! ub (list '- (hpm-qd p 'xi)))))
              (dk-ineq! le)))))
      (dk-have! (list 'FORALL 'hdn_ (list 'IMPLIES '(IN hdn_ NN)
                  (list 'FORSOME 'hdq_ (list 'AND '(IN hdq_ kk)
                     (list '<= (hpm-qd 'hdq_ 'xi) (list '+ aa '(recip (+ hdn_ 1))))))))
        (lambda ()
          (dk-peel!)
          (let* ((nv (car (filter (lambda (x) (dk-asm? (list 'IN x 'NN))) (free-vars (dk-goal)))))
                 (d (list 'recip (list '+ nv 1))))
            (dk-cite! 'nn-recip-succ-pos nv)
            (dk-cite! 'rr-pos-rr-in-rr d)
            (dk-cite! 'rr-lt-of-pos-rr d)
            (let* ((ex (dk-cite! 'rr-sup-approx ss d))
                   (w (dk-skolem! ex))
                   (p (open-ss! w)))
              (in-kk! p)
              (hpm-q-facts! (hpm-sub p 'xi))
              (witness! p
                (lambda ()
                  (dk-conj-close!
                    (lambda ()
                      (if (dk-head-is? (dk-goal) 'IN) (ass)
                          (dk-ineq! (list '< (list '- sg d) w)
                                    (list '= w (list '- (hpm-qd p 'xi)))))))))))))
      (witness! aa (lambda () (dk-conj-close! dk-ass!))))))
(qed 'cips-dist-sq-inf-midpoint)
(topic! 'cips-dist-sq-inf-midpoint 'analysis)

;;; ====================================================================
;;; (b) the book's (2.6) for a set closed under midpoints: for phi, psi in kk,
;;;     ||phi - psi||^2 <= 2 (||phi - xi||^2 + ||psi - xi||^2) - 4 alpha^2,
;;; for any lower bound alpha^2 of the squared distance.
;;; ====================================================================
(set! hpm-v 'v)
(sp (make-wff (forall-guarded '(v kk xi aa)
   (list '(IS-COMPLEX-INNER-PRODUCT-SPACE v) '(SUBSET kk (VEC v)) (hpm-midclosed 'kk)
         '(IN xi (VEC v)) '(IN aa RR) hpm-lb)
   hpm-est-concl)))
(dk-peel!)
(let* ((lb (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'hdp_))) "the lower bound"))
       (mc (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'hm1_))) "the midpoint closure"))
       (sum (hpm-add 'p1_ 'p2_))
       (mid (hpm-act 1/2 sum)))
  (dk-cite! 'subset-mem-fwd 'kk '(VEC v) 'p1_)
  (dk-cite! 'subset-mem-fwd 'kk '(VEC v) 'p2_)
  (dk-have! '(IN 1/2 CC) (lambda () (arith)))
  (dk-apply! mc 'p1_ 'p2_)
  (dk-cite! 'subset-mem-fwd 'kk '(VEC v) mid)
  (let ((le (dk-apply! lb mid)))
    (for-each (lambda (u) (hpm-q-facts! u))
              (list (hpm-sub 'p1_ 'p2_) (hpm-sub 'p1_ 'xi) (hpm-sub 'p2_ 'xi) (hpm-sub mid 'xi)))
    (let ((id (list '= (hpm-qd 'p1_ 'p2_)
                    (list '- (list '+ (list '* 2 (hpm-qd 'p1_ 'xi)) (list '* 2 (hpm-qd 'p2_ 'xi)))
                             (list '* 4 (hpm-qd mid 'xi))))))
      (dk-have! id (lambda () (hpm-expand!) (hpm-type-ips! (dk-goal)) (crs)))
      (dk-ineq! id le))))
(qed 'cips-midpoint-estimate-midpoint)
(topic! 'cips-midpoint-estimate-midpoint 'inequalities)

;;; ====================================================================
;;; (c)-(d) THE CLOSEST POINT of a nonempty closed set closed under midpoints
;;; ====================================================================
(set! hpm-v 'v)
(sp (make-wff (forall-guarded '(v kk xi)
   (list '(IS-HILBERT-SPACE v) '(SUBSET kk (VEC v)) (hpm-nonempty 'kk) (hpm-midclosed 'kk)
         '(IS-CLOSED (IP-METRIC-SPACE v) kk) '(IN xi (VEC v)))
   hpm-cp-concl)))
(dk-peel!)
(dk-cite! 'hilbert-space-is-cips 'v)
(dk-cite! 'hilbert-space-complete 'v)
(define hpm-ms '(IP-METRIC-SPACE v))
(dk-cite! 'ip-metric-space-is-metric-space 'v)
(dk-cite! 'ip-metric-space-pts 'v)
(let* ((ex (dk-cite! 'cips-dist-sq-inf-midpoint 'v 'kk 'xi))
       (aa (dk-skolem! ex)))
  (set! hpm-cp-aa aa)
  (set! hpm-cp-apx (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'hdn_)))
                            "the approximation universal"))
  (dk-cite! 'cips-midpoint-estimate-midpoint 'v 'kk 'xi aa))
(define hpm-cp-g
  (car (dk-abstract! 'NN 'kk (lambda (n) (list 'CHOICE (hpm-cp-set n)))
                     (lambda (n) (hpm-cp-choice! n) (ass)))))
(define hpm-cp-ve (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f hpm-cp-g)
                                            (dk-contains? f 'CHOICE)))
                           "the value equation"))
;; pointwise: g(n) in K and ||g(n) - xi||^2 <= aa + 1/(n+1)
(dk-have! (list 'FORALL 'hcn_ (list 'IMPLIES '(IN hcn_ NN)
            (list 'AND (list 'IN (list hpm-cp-g 'hcn_) 'kk)
                       (list '<= (hpm-qd (list hpm-cp-g 'hcn_) 'xi)
                             (list '+ hpm-cp-aa '(recip (+ hcn_ 1)))))))
  (lambda ()
    (dk-peel!)
    (let* ((n (car (filter (lambda (x) (dk-asm? (list 'IN x 'NN))) (free-vars (dk-goal)))))
           (ch (hpm-cp-choice! n)))
      (subst (dk-apply! hpm-cp-ve n))
      (dk-conj-close! dk-ass!))))
;; g is a sequence of points of the metric space
(dk-rewrite-h! '(SUBSET kk (VEC v)) '(VEC v) (list 'PTS hpm-ms))
(dk-cite! 'fun-codomain-superset hpm-cp-g 'NN 'kk (list 'PTS hpm-ms))
;; g is Cauchy
(dk-have! (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps)
            (list 'FORSOME 'hnn_ (list 'AND '(IN hnn_ NN)
              (list 'FORALL 'm (list 'IMPLIES '(IN m NN)
                (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                  (list 'IMPLIES '(AND (<= hnn_ m) (<= hnn_ n_))
                    (list '<= (list (list 'DIST hpm-ms) (list hpm-cp-g 'm) (list hpm-cp-g 'n_)) 'eps))))))))))
  (lambda ()
    (dk-peel!)
    (let* ((eps (cadr (dk-pick (dk-head? 'POS-RR) "eps"))))
      (dk-cite! 'rr-pos-rr-in-rr eps)
      (dk-cite! 'rr-lt-of-pos-rr eps)
      (dk-cite! 'rr-mul-pos eps eps)
      (dk-have! (list 'IN (list '* eps eps) 'RR) (lambda () (type-term)))
      (let* ((ee (dk-name! (list '* eps eps)))
             (e4 (list '* 1/4 ee)))
        (dk-rewrite-h! (list '< 0 (list '* eps eps)) (list '* eps eps) ee)
        (dk-have! (list 'IN e4 'RR) (lambda () (type-term)))
        (dk-have! (list '< 0 e4) (lambda () (dk-ineq! (list '< 0 ee))))
        (dk-cite! 'rr-pos-rr-of-lt e4)
        (dk-have! (list '= e4 (list '* 1/4 ee)) (lambda () (rfl)))
        (dk-have! (list '<= 0 ee) (lambda () (dk-ineq! (list '< 0 ee))))
        (dk-have! (list '<= 0 eps) (lambda () (dk-ineq! (list '< 0 eps))))
        (dk-have! (list '= (list '* eps eps) ee)
          (lambda () (subst (list '= ee (list '* eps eps))) (rfl)))
        (hpm-have-and! (list 'IN ee 'RR) (list '<= 0 ee))
        (hpm-have-and! (list 'IN eps 'RR) (list '<= 0 eps))
        (dk-cite! 'sqrt-char ee eps)
        (hpm-sqrt! ee)
        (let* ((ex (dk-cite! 'recip-succ-small e4))
               (nn0 (dk-skolem! ex))
               (small (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (memq nn0 (free-vars f))))
                               "the recip bound")))
          (witness! nn0
            (lambda ()
              (dk-conj-close!
                (lambda ()
                  (if (dk-head-is? (dk-goal) 'IN) (ass)
                      (begin
                        (dk-peel!)
                        (dk-split-all!)
                        (let* ((g (dk-goal))
                               (m (cadr (cadr (cadr g)))) (n (cadr (caddr (cadr g)))))
                          (hpm-cp-cauchy-pair! hpm-ms hpm-cp-g ee eps e4 small m n)))))))))))))
(hpm-iff-bwd! 'is-cauchy-seq hpm-ms hpm-cp-g)
;; complete: g converges to some L, and L is in K
(define hpm-cp-l
  (let* ((cv (dk-apply! (dk-cite! 'complete-cauchy-converges hpm-ms) hpm-cp-g))
         (ex (hpm-iff-fwd! 'converges hpm-ms hpm-cp-g)))
    (dk-skolem! ex)))
(dk-cite! 'closed-limit-in hpm-ms 'kk hpm-cp-g hpm-cp-l)
(dk-rewrite-h! '(SUBSET kk (PTS (IP-METRIC-SPACE v))) (list 'PTS hpm-ms) '(VEC v))
(dk-cite! 'subset-mem-fwd 'kk '(VEC v) hpm-cp-l)
(dk-have! (list 'IN 'xi (list 'PTS hpm-ms))
  (lambda () (subst (list '== (list 'PTS hpm-ms) '(VEC v))) (ass)))
;; (d) ||L - xi||^2 <= aa + d for every d > 0, by one closed ball
(hpm-q-facts! (hpm-sub hpm-cp-l 'xi))
(hpm-q-facts! (hpm-sub 'xi hpm-cp-l))
(hpm-q-eq! (hpm-sub 'xi hpm-cp-l) (hpm-sub hpm-cp-l 'xi))
(dk-have! (list 'FORALL 'hcd_ (list 'IMPLIES '(POS-RR hcd_)
            (list '<= (hpm-qd hpm-cp-l 'xi) (list '+ hpm-cp-aa 'hcd_))))
  (lambda ()
    (dk-peel!)
    (let* ((d (cadr (dk-pick (dk-head? 'POS-RR) "d")))
           (ad (list '+ hpm-cp-aa d))
           (r (list 'SQRT ad))
           (cb (list 'CLOSED-BALL hpm-ms 'xi r)))
      (dk-cite! 'rr-pos-rr-in-rr d)
      (dk-cite! 'rr-lt-of-pos-rr d)
      (dk-have! (list 'IN ad 'RR) (lambda () (type-term)))
      (dk-have! (list '<= 0 ad) (lambda () (dk-ineq! (list '<= 0 hpm-cp-aa) (list '< 0 d))))
      (hpm-sqrt! ad)
      (dk-cite! 'closed-ball-is-closed hpm-ms 'xi r)
      (let* ((ex (dk-cite! 'recip-succ-small d))
             (nn0 (dk-skolem! ex))
             (small (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (memq nn0 (free-vars f))))
                             "the recip bound")))
        (dk-have! (list 'FORALL 'hct_ (list 'IMPLIES '(IN hct_ NN)
                    (list 'IMPLIES (list '<= nn0 'hct_) (list 'IN (list hpm-cp-g 'hct_) cb))))
          (lambda ()
            (dk-peel!)
            (let ((n (cadr (cadr (dk-goal)))))
              (hpm-cp-tail-in-ball! hpm-ms hpm-cp-g d r small n))))
        (dk-cite! 'closed-set-limit-in-tail hpm-ms cb hpm-cp-g hpm-cp-l nn0)
        (hpm-iff-fwd! 'closed-ball-membership hpm-ms 'xi r hpm-cp-l)
        (let* ((q (hpm-qd 'xi hpm-cp-l))
               (s (list 'SQRT q))
               (de (dk-cite! 'ip-metric-space-dist 'v 'xi hpm-cp-l)))
          (hpm-sqrt! q)
          (dk-rewrite-h! (list '<= (cadr de) r) (cadr de) s)
          (dk-cite! 'rr-mul-le-right s r s)
          (dk-cite! 'rr-mul-le-right s r r)
          (dk-have! (list '= (list '* r s) (list '* s r)) (lambda () (crs)))
          (dk-have! (list '<= q ad)
            (lambda () (dk-le-chain! q (list '* s s) (list '* r s) (list '* s r) (list '* r r) ad)))
          (dk-ineq! (list '<= q ad) (list '= q (hpm-qd hpm-cp-l 'xi))))))))
(dk-cite! 'rr-le-of-le-add-all-pos (hpm-qd hpm-cp-l 'xi) hpm-cp-aa)
(witness! hpm-cp-l
  (lambda ()
    (dk-conj-close!
      (lambda ()
        (if (dk-head-is? (dk-goal) 'IN) (ass)
            (begin
              (dk-peel!)
              (let* ((p (cadr (cadr (caddr (dk-goal)))))
                     (lb (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f 'hdp_)
                                                   (not (dk-contains? f 'p1_))))
                                  "the lower bound")))
                (dk-cite! 'subset-mem-fwd 'kk '(VEC v) p)
                (hpm-q-facts! (hpm-sub p 'xi))
                (dk-ineq! (dk-apply! lb p) (list '<= (hpm-qd hpm-cp-l 'xi) hpm-cp-aa)))))))))
(qed 'hilbert-closest-point-midpoint)
(topic! 'hilbert-closest-point-midpoint 'analysis)

;;; ====================================================================
;;; The submodule statements of hilbert-projection.scm, as corollaries
;;; ====================================================================

;;; with IS-COMPLEX-INNER-PRODUCT-SPACE(v) and IS-SUBMODULE(v, kk) in context: land
;;; kk subset VEC(v), kk nonempty, and kk closed under midpoints
(define (hpm-submodule-hyps!)
  (dk-cite! 'submodule-subset 'v 'kk)
  (dk-cite! 'submodule-vzero-in 'v 'kk)
  (dk-have! (hpm-nonempty 'kk) (lambda () (witness! '(VZERO v) (lambda () (ass)))))
  (dk-have! (hpm-midclosed 'kk)
    (lambda ()
      (dk-peel!)
      (let* ((g (dk-goal))                 ; (IN ((ACT v) 1/2 ((VADD v) p q)) kk)
             (sum (caddr (cadr g)))
             (p (cadr sum)) (q (caddr sum)))
        (dk-cite! 'cips-scal-carrier 'v)
        (dk-have! '(IN 1/2 CC) (lambda () (arith)))
        (dk-rewrite-h! '(IN 1/2 CC) 'CC '(CARR (SCAL v)))
        (dk-cite! 'submodule-vadd-closed 'v 'kk p q)
        (dk-cite! 'submodule-act-closed 'v 'kk 1/2 sum)
        (ass)))))

(set! hpm-v 'v)
(sp (make-wff (forall-guarded '(v kk xi)
   '((IS-COMPLEX-INNER-PRODUCT-SPACE v) (IS-SUBMODULE v kk) (IN xi (VEC v)))
   hpm-inf-concl)))
(dk-peel!)
(hpm-submodule-hyps!)
(dk-cite! 'cips-dist-sq-inf-midpoint 'v 'kk 'xi)
(ass)
(qed 'cips-dist-sq-inf-via-midpoint)
(topic! 'cips-dist-sq-inf-via-midpoint 'analysis)

(set! hpm-v 'v)
(sp (make-wff (forall-guarded '(v kk xi aa)
   (list '(IS-COMPLEX-INNER-PRODUCT-SPACE v) '(IS-SUBMODULE v kk) '(IN xi (VEC v)) '(IN aa RR) hpm-lb)
   hpm-est-concl)))
(dk-peel!)
(hpm-submodule-hyps!)
(let* ((g (dk-goal))                       ; (<= <p1 - p2, p1 - p2> ...)
       (x (cadr (cadr g)))
       (p1 (cadr x)) (p2 (cadr (caddr x)))
       (est (dk-cite! 'cips-midpoint-estimate-midpoint 'v 'kk 'xi 'aa)))
  (dk-apply! est p1 p2)
  (ass))
(qed 'cips-midpoint-estimate-via-midpoint)
(topic! 'cips-midpoint-estimate-via-midpoint 'inequalities)

(set! hpm-v 'v)
(sp (make-wff (forall-guarded '(v kk xi)
   '((IS-HILBERT-SPACE v) (IS-SUBMODULE v kk) (IS-CLOSED (IP-METRIC-SPACE v) kk) (IN xi (VEC v)))
   hpm-cp-concl)))
(dk-peel!)
(dk-cite! 'hilbert-space-is-cips 'v)
(hpm-submodule-hyps!)
(dk-cite! 'hilbert-closest-point-midpoint 'v 'kk 'xi)
(ass)
(qed 'hilbert-closest-point-via-midpoint)
(topic! 'hilbert-closest-point-via-midpoint 'analysis)
