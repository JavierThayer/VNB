;;; road-juxtaposition-laws.scm -- THE JUXTAPOSITION OF ROADS (Dieudonne 9.6, the notes'
;;; Proposition 3.1), THE TRIANGULAR ROAD, AND THE LENGTH OF A ROAD (the notes' (53)).
;;; Batch 37, 2026-09-26.  The vocabulary is structure-library/road-juxtaposition.scm
;;; (JUXTA, ROAD-LENGTH, TRI-ROAD, TRI-ROAD-DERIV).
;;;
;;; THE FILE IN ORDER.
;;;   (0) the four unfold equations.
;;;   (1) juxta-apply-left / -right / -right-closed (the values), juxta-in-fun, the trace:
;;;       juxta-trace-subset (always) and juxta-trace (= the union, under p(b) = q(b)).
;;;   (2) right-/left-limit-within-local (a one-sided limit sees a half-neighbourhood only),
;;;       REGULATED-ON-GLUE (regulated on [a, c] and on [c, b] => regulated on [a, b]; the
;;;       value at c is free), JUXTA-IS-ROAD (Dieudonne 9.6).
;;;   (3) line-int-interior-congruence (the integral sees the path on [a, b] and the
;;;       derivative on (a, b)), LINE-INT-JUXTA (Proposition 3.1, juxtaposition form),
;;;       LINE-INT-CONCAT (the notes' (49): gamma || rho with rho shifted by an affine map).
;;;   (5a-c) road-length-regulated / -primitive / -in-rr / -nonneg, pw-int-interior-
;;;       congruence, ROAD-LENGTH-JUXTA (additivity).
;;;   (4) the shifted segment: seg-shift-is-road / -trace / -length / -line-int,
;;;       road-length-segment; the triangle: TRI-ROAD-IS-ROAD, TRI-ROAD-TRACE,
;;;       TRI-INT-IS-LINE-INT (docs/goursat-definitions-2026-09-25.md, item 2; -conv3 under
;;;       goursat's hypothesis CONV3(a, b, c) subset u), ROAD-LENGTH-TRI
;;;       (the perimeter).
;;;   (5d-e) LINE-INT-LENGTH-BOUND (the notes' (53)), road-length-affine-reparam.
;;;
;;; STATEMENTS.  Every function lives on its interval.  The endpoint condition is a strict
;;; `pgam1(b) = pgam2(b)' between typed values.  The hypotheses on f are exactly those of
;;; `line-int-exists' (u subset CC, f in FUN(u, CC), continuous on the subspace u); the
;;; antecedents are curried.  No new axiom, support or stamp.
;;;
;;; LOAD WINDOW.  lo = theorem-library/goursat (seg-path-is-road, seg-path-apply); also
;;; line-int-reparam (road-affine-reparam, line-int-affine-reparam, trace-affine-reparam,
;;; pw-int-affine-subst, affine-reparam-ccint-in, trace-restrict-subset), line-int-laws
;;; (line-int-adjacent, road-restrict, line-int-abs-bound, line-int-value,
;;; regulated-on-magnitude), pw-int-order (pw-int-monotone, pw-int-nonneg), primitive-glue.
;;; No citer yet: hi = none.
;;;
;;; Helper prefix: jxl-.

;;; ---- file-local driver helpers ---------------------------------------

(define (jxl-head g) (and (pair? g) (car g)))
(define (jxl-op? t op n) (and (pair? t) (eq? (car t) op) (= (length t) n)))

(define (jxl-close-by! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))

;;; x in CCINT(lo,hi) / OOINT(lo,hi) from the bounds (all in context).
(define (jxl-in-ccint! z lo hi prems)
  (let ((f (list 'IN z (list 'CCINT lo hi))))
    (if (not (dk-asm? f))
        (dk-have! f (lambda () (mac 'ccint-membership) (jxl-close-by! prems))))
    f))
(define (jxl-in-ooint! z lo hi prems)
  (let ((f (list 'IN z (list 'OOINT lo hi))))
    (if (not (dk-asm? f))
        (dk-have! f (lambda () (mac 'ooint-membership) (jxl-close-by! prems))))
    f))

;;; (IN (CCINT lo hi) SET) landed.
(define (jxl-set! lo hi)
  (let ((f (list 'IN (list 'CCINT lo hi) 'SET)))
    (if (not (dk-asm? f))
        (begin
          (if (not (dk-asm? '(IN RR SET))) (fact 'rr-is-set))
          (fact 'ccint-subset-rr lo hi)
          (fact 'subclass-of-set-is-set (list 'CCINT lo hi) 'RR)))
    f))

;;; the three parts of a CCINT / OOINT membership in context, landed (the membership kept).
(define (jxl-cc-parts! z lo hi)
  (if (not (and (dk-asm? (list 'IN z 'RR)) (dk-asm? (list '<= lo z)) (dk-asm? (list '<= z hi))))
      (dk-split-all! (list (dk-cite! 'ccint-parts lo hi z)))))
(define (jxl-oo-parts! y lo hi)
  (if (not (dk-asm? (list 'IN y 'RR))) (fact 'ooint-elt-in-rr lo hi y))
  (if (not (dk-asm? (list '< lo y)))
      (dk-have! (list '< lo y)
        (lambda () (dk-split-all! (dk-landed* (lambda ()
                     (mac-h 'ooint-membership (list 'IN y (list 'OOINT lo hi))))))
                   (ass))))
  (if (not (dk-asm? (list '< y hi)))
      (dk-have! (list '< y hi)
        (lambda () (dk-split-all! (dk-landed* (lambda ()
                     (mac-h 'ooint-membership (list 'IN y (list 'OOINT lo hi))))))
                   (ass)))))

;;; In context (NOT (<= z b)) with z, b in RR: land (< b z).
(define (jxl-not-le->lt! z b)
  (let ((f (list '< b z)))
    (if (not (dk-asm? f)) (dk-cite! 'rr-not-le-lt z b))
    f))

;;; =====================================================================
;;; (0) THE UNFOLD EQUATIONS (a functoid is unfolded in a hypothesis only through a theorem)
;;; =====================================================================
(sp (make-wff '(FORALL jxp_ (FORALL jxq_ (FORALL jxa_ (FORALL jxb_ (FORALL jxc_
  (== (JUXTA jxp_ jxq_ jxa_ jxb_ jxc_)
      (VNB-LAMBDA jxt_ (CCINT jxa_ jxc_) (IF (<= jxt_ jxb_) (jxp_ jxt_) (jxq_ jxt_)))))))))))
(di)
(mac 'JUXTA)
(qrfl)
(qed 'juxta-unfold)
(topic! 'juxta-unfold 'analysis)

(sp (make-wff '(FORALL rld_ (FORALL rla_ (FORALL rlb_
  (== (ROAD-LENGTH rld_ rla_ rlb_)
      (PW-INT (VNB-LAMBDA rlt_ (CCINT rla_ rlb_) (magnitude (rld_ rlt_))) rla_ rlb_)))))))
(di)
(mac 'ROAD-LENGTH)
(qrfl)
(qed 'road-length-unfold)
(topic! 'road-length-unfold 'analysis)

(sp (make-wff '(FORALL tra_ (FORALL trb_ (FORALL trc_
  (== (TRI-ROAD tra_ trb_ trc_)
      (JUXTA (JUXTA (SEG-PATH tra_ trb_)
                    (VNB-LAMBDA trs_ (CCINT 1 2) ((SEG-PATH trb_ trc_) (- trs_ 1)))
                    0 1 2)
             (VNB-LAMBDA trs_ (CCINT 2 3) ((SEG-PATH trc_ tra_) (- trs_ 2)))
             0 2 3)))))))
(di)
(mac 'TRI-ROAD)
(qrfl)
(qed 'tri-road-unfold)
(topic! 'tri-road-unfold 'analysis)

(sp (make-wff '(FORALL tra_ (FORALL trb_ (FORALL trc_
  (== (TRI-ROAD-DERIV tra_ trb_ trc_)
      (JUXTA (JUXTA (SEG-DERIV tra_ trb_)
                    (VNB-LAMBDA trs_ (CCINT 1 2) ((SEG-DERIV trb_ trc_) (- trs_ 1)))
                    0 1 2)
             (VNB-LAMBDA trs_ (CCINT 2 3) ((SEG-DERIV trc_ tra_) (- trs_ 2)))
             0 2 3)))))))
(di)
(mac 'TRI-ROAD-DERIV)
(qrfl)
(qed 'tri-road-deriv-unfold)
(topic! 'tri-road-deriv-unfold 'analysis)

;;; =====================================================================
;;; (1) THE VALUES AND THE TYPING OF A JUXTAPOSITION
;;; =====================================================================
(define jxl-ift '(IF (<= t b) (p t) (q t)))

(sp (make-wff "forall([p, q, a in rr, b in rr, c in rr, t in ccint(a, b)], b <= c implies
   (juxta(p, q, a, b, c))(t) == p(t))"))
(dk-peel!)
(jxl-cc-parts! 't 'a 'b)
(jxl-in-ccint! 't 'a 'c '((IN a RR) (IN b RR) (IN c RR) (IN t RR) (<= a t) (<= t b) (<= b c)))
(mac 'JUXTA)
(dk-lam-b!)
(dk-if-branch! #t jxl-ift #f (dk-lane (lambda () (dk-lane-if! qrfl))))
(qed 'juxta-apply-left)
(topic! 'juxta-apply-left 'analysis)

(sp (make-wff "forall([p, q, a in rr, b in rr, c in rr, t in ccint(b, c)], a <= b implies b < t implies
   (juxta(p, q, a, b, c))(t) == q(t))"))
(dk-peel!)
(jxl-cc-parts! 't 'b 'c)
(jxl-in-ccint! 't 'a 'c '((IN a RR) (IN b RR) (IN c RR) (IN t RR) (<= a b) (<= b t) (<= t c)))
(mac 'JUXTA)
(dk-lam-b!)
(dk-if-branch! #f jxl-ift
  (lambda () (fact 'rr-lt-not-le 'b 't) (ass))
  (dk-lane (lambda () (dk-lane-if! qrfl))))
(qed 'juxta-apply-right)
(topic! 'juxta-apply-right 'analysis)

(sp (make-wff "forall([p, q, a in rr, b in rr, c in rr], a <= b implies p(b) = q(b) implies
   forall([t in ccint(b, c)], (juxta(p, q, a, b, c))(t) == q(t)))"))
(dk-peel!)
(jxl-cc-parts! 't 'b 'c)
(jxl-in-ccint! 't 'a 'c '((IN a RR) (IN b RR) (IN c RR) (IN t RR) (<= a b) (<= b t) (<= t c)))
(mac 'JUXTA)
(dk-lam-b!)
(dk-case-if! jxl-ift
  (lambda (true? v)
    (if true?
        (begin
          (dk-have! '(= t b) (lambda () (dk-ineq! '(IN t RR) '(IN b RR) '(<= t b) '(<= b t))))
          (subst '(= t b))
          (subst '(= (p b) (q b)))
          (qrfl))
        (qrfl))))
(qed 'juxta-apply-right-closed)
(topic! 'juxta-apply-right-closed 'analysis)

(sp (make-wff "forall([p, q, a in rr, b in rr, c in rr, cod], a <= b implies b <= c implies
   p in fun(ccint(a, b), cod) implies q in fun(ccint(b, c), cod) implies
   juxta(p, q, a, b, c) in fun(ccint(a, c), cod))"))
(dk-peel!)
(jxl-set! 'a 'c)
(mac 'JUXTA)
(dk-lam-type!
 (lambda ()
   (let* ((z (dk-di-var!))
          (ift (list 'IF (list '<= z 'b) (list 'p z) (list 'q z))))
     (jxl-cc-parts! z 'a 'c)
     (dk-case-if! ift
       (lambda (true? v)
         (if true?
             (jxl-in-ccint! z 'a 'b (list '(IN a RR) '(IN b RR) (list 'IN z 'RR) (list '<= 'a z) (list '<= z 'b)))
             (begin
               (jxl-not-le->lt! z 'b)
               (jxl-in-ccint! z 'b 'c (list '(IN b RR) '(IN c RR) (list 'IN z 'RR) (list '< 'b z) (list '<= z 'c)))))
         (fact 'fun-apply-type-c (if true? 'p 'q) (if true? '(CCINT a b) '(CCINT b c)) 'cod z)
         (if (not (sequent-node-grounded? (proof-state-focus *ps*))) (ass))))))
 ass)
(qed 'juxta-in-fun)
(topic! 'juxta-in-fun 'analysis)

;;; (OR (<= x y) (<= y x)) landed, x and y typed in context (rr-leq-total's antecedent is a
;;; conjunction, which `fact' does not split).
(define (jxl-le-total! x y)
  (let ((f (list 'OR (list '<= x y) (list '<= y x))))
    (if (not (dk-asm? f))
        (begin
          (let ((c (list 'AND (list 'IN x 'RR) (list 'IN y 'RR))))
            (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (ass)))))))
          (fact 'rr-leq-total x y)))
    f))

;;; ---- the trace -------------------------------------------------------
;;; w in TRACE(g, lo, hi) in context: land t in CCINT(lo, hi) and g(t) = w; return t.
(define (jxl-trace-elim! w g lo hi)
  (let ((img (list 'IN w (list 'IMAGE g (list 'CCINT lo hi)))))
    (dk-have! img
      (lambda ()
        (dk-cite! 'trace-unfold g lo hi)
        (subst (list '= (list 'IMAGE g (list 'CCINT lo hi)) (list 'TRACE g lo hi)))
        (ass)))
    (mac-h 'image-membership-iff img)
    (let ((t (dk-skolem! (dk-pick (lambda (f) (and (jxl-op? f 'FORSOME 3) (dk-contains? f w)
                                                   (dk-contains? f g)))
                                  "the image existential"))))
      (dk-split-all!)
      t)))

(define jxl-jj '(JUXTA p q a b c))
(define jxl-tp '(TRACE p a b))
(define jxl-tq '(TRACE q b c))
(define jxl-tj (list 'TRACE jxl-jj 'a 'c))
(define jxl-un (list 'UNION jxl-tp jxl-tq))

(sp (make-wff "forall([p, q, a in rr, b in rr, c in rr], a <= b implies b <= c implies
   p in fun(ccint(a, b), cc) implies q in fun(ccint(b, c), cc) implies
   trace(juxta(p, q, a, b, c), a, c) subset union(trace(p, a, b), trace(q, b, c)))"))
(dk-peel!)
(let* ((w (subset-by-element!))
       (t (jxl-trace-elim! w jxl-jj 'a 'c)))
  (jxl-cc-parts! t 'a 'c)
  (jxl-le-total! t 'b)
  (use-cases (list 'OR (list '<= t 'b) (list '<= 'b t))
    (lambda ()
      (jxl-in-ccint! t 'a 'b (list '(IN a RR) '(IN b RR) (list 'IN t 'RR) (list '<= 'a t) (list '<= t 'b)))
      (dk-cite! 'juxta-apply-left 'p 'q 'a 'b 'c t)
      (dk-cite! 'trace-value-in 'p 'a 'b t)
      (dk-have! (list 'IN w jxl-tp)
        (lambda ()
          (subst (list '= w (list jxl-jj t)))
          (subst (list '= (list jxl-jj t) (list 'p t)))
          (ass)))
      (mac 'union-membership)
      (prop))
    (lambda ()
      (dk-cite! 'trace-value-in 'q 'b 'c t)
      (fact 'rr-le-cases 'b t)
      (use-cases (list 'OR (list '< 'b t) (list '= 'b t))
        (lambda ()
          (jxl-in-ccint! t 'b 'c (list '(IN c RR) '(IN b RR) (list 'IN t 'RR) (list '<= 'b t) (list '<= t 'c)))
          (dk-cite! 'juxta-apply-right 'p 'q 'a 'b 'c t)
          (dk-cite! 'trace-value-in 'q 'b 'c t)
          (dk-have! (list 'IN w jxl-tq)
            (lambda ()
              (subst (list '= w (list jxl-jj t)))
              (subst (list '= (list jxl-jj t) (list 'q t)))
              (ass)))
          (mac 'union-membership)
          (prop))
        (lambda ()
          ;; t = b: J(b) = p(b), a point of p's trace
          (if (not (dk-asm? '(<= b b))) (fact 'rr-leq-reflexive 'b))
          (jxl-in-ccint! 'b 'a 'b (list '(IN a RR) '(IN b RR) '(<= a b) '(<= b b)))
          (dk-cite! 'juxta-apply-left 'p 'q 'a 'b 'c 'b)
          (dk-cite! 'trace-value-in 'p 'a 'b 'b)
          (dk-have! (list 'IN w jxl-tp)
            (lambda ()
              (subst (list '= w (list jxl-jj t)))
              (subst (list '= t 'b))
              (subst (list '= (list jxl-jj 'b) '(p b)))
              (ass)))
          (mac 'union-membership)
          (prop))))))
(qed 'juxta-trace-subset)
(topic! 'juxta-trace-subset 'analysis)

(sp (make-wff "forall([p, q, a in rr, b in rr, c in rr], a <= b implies b <= c implies
   p in fun(ccint(a, b), cc) implies q in fun(ccint(b, c), cc) implies p(b) = q(b) implies
   trace(juxta(p, q, a, b, c), a, c) = union(trace(p, a, b), trace(q, b, c)))"))
(dk-peel!)
(define jxl-tr-sub (dk-cite! 'juxta-trace-subset 'p 'q 'a 'b 'c))
(dk-cite! 'juxta-in-fun 'p 'q 'a 'b 'c 'CC)
(define jxl-tr-sup
  (dk-have! (list 'SUBSET jxl-un jxl-tj)
    (lambda ()
      (let ((w (subset-by-element!)))
        (mac-h 'union-membership (list 'IN w jxl-un))
        (use-cases (list 'OR (list 'IN w jxl-tp) (list 'IN w jxl-tq))
          (lambda ()
            (let ((t (jxl-trace-elim! w 'p 'a 'b)))
              (jxl-cc-parts! t 'a 'b)
              (jxl-in-ccint! t 'a 'c (list '(IN a RR) '(IN b RR) '(IN c RR) (list 'IN t 'RR)
                                           (list '<= 'a t) (list '<= t 'b) '(<= b c)))
              (dk-cite! 'juxta-apply-left 'p 'q 'a 'b 'c t)
              (dk-cite! 'trace-value-in jxl-jj 'a 'c t)
              (subst (list '= w (list 'p t)))
              (subst (list '= (list 'p t) (list jxl-jj t)))
              (ass)))
          (lambda ()
            (let ((t (jxl-trace-elim! w 'q 'b 'c)))
              (jxl-cc-parts! t 'b 'c)
              (jxl-in-ccint! t 'a 'c (list '(IN a RR) '(IN b RR) '(IN c RR) (list 'IN t 'RR)
                                           (list '<= 'b t) (list '<= t 'c) '(<= a b)))
              (dk-cite! 'juxta-apply-right-closed 'p 'q 'a 'b 'c t)
              (dk-cite! 'trace-value-in jxl-jj 'a 'c t)
              (subst (list '= w (list 'q t)))
              (subst (list '= (list 'q t) (list jxl-jj t)))
              (ass))))))))
(dk-cite! 'trace-is-set jxl-jj 'a 'c)
(dk-cite! 'trace-is-set 'p 'a 'b)
(dk-cite! 'trace-is-set 'q 'b 'c)
(dk-have! (list 'AND (list 'IN jxl-tp 'SET) (list 'IN jxl-tq 'SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'union-set-closure jxl-tp jxl-tq)
(dk-have! (list 'AND (list 'IN jxl-tj 'SET) (list 'IN jxl-un 'SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(define jxl-tr-ext (begin (fact 'extensionality jxl-tj jxl-un) (iff-for (list '= jxl-tj jxl-un))))
(define jxl-tr-body
  (dk-have! (list 'FORALL 'jxw_ (list 'IFF (list 'IN 'jxw_ jxl-tj) (list 'IN 'jxw_ jxl-un)))
    (lambda ()
      (di)
      (let* ((v (cadr (cadr (dk-goal))))
             (i1 (dk-cite! 'subset-mem-fwd jxl-tj jxl-un v))
             (i2 (dk-cite! 'subset-mem-fwd jxl-un jxl-tj v)))
        (dk-only! i1 i2)
        (prop)))))
(dk-only! jxl-tr-ext (list 'FORALL 'jxw_ (list 'IFF (list 'IN 'jxw_ jxl-tj) (list 'IN 'jxw_ jxl-un))))
(prop)
(qed 'juxta-trace)
(topic! 'juxta-trace 'analysis)

;;; =====================================================================
;;; (2a) ONE-SIDED LIMITS ARE LOCAL.  A right limit of g within V at x is a right limit
;;; within W of every f on W that agrees with g on a right half-neighbourhood (x, x + r) of x
;;; inside W, that half-neighbourhood lying in V.  Left: the same on (x - r, x).  The delta
;;; of g is cut down to min(delta, r) (rr-min-pos).
;;; =====================================================================
(define (jxl-lim-local! right?)
  (let* ((pred (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN))
         (ls (dk-peel!)))
    (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred 'g 'jlv_ 'jlx_ 'jll_)))))
    (let ((cl (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm 'ABS)))
                       "the limit clause of g"))
          (am (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm 'jlr_)
                                         (not (dk-contains? fm '==))))
                       "the neighbourhood lies in V"))
          (av (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm '==)))
                       "f agrees with g near x")))
      (fact 'rr-pos-rr-in-rr 'jlr_)
      (fact 'rr-lt-of-pos-rr 'jlr_)
      (mac pred)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (jxl-head (dk-goal)) 'FORALL))
             (ass)
             (let* ((pe (dk-peel!))
                    (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
                    (dl (dk-skolem! (dk-apply! cl e))))
               (dk-split-all!)
               (fact 'rr-pos-rr-in-rr dl)
               (fact 'rr-lt-of-pos-rr dl)
               (let* ((c2 (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm dl)))
                                  "the delta clause"))
                     (w (dk-skolem! (dk-fact! 'rr-min-pos dl 'jlr_))))
                 (dk-split-all!)
                 (ew w)
                 (dk-conj-close!
                  (lambda ()
                    (if (eq? (jxl-head (dk-goal)) 'POS-RR)
                        (begin (if (not (dk-asm? (list 'POS-RR w))) (fact 'rr-pos-rr-of-lt w)) (ass))
                        (let* ((ls2 (dk-peel!))
                               (t (cadr (car (filter (lambda (fm) (and (jxl-op? fm 'IN 3)
                                                                       (eq? (caddr fm) 'jlw_)))
                                                     ls2))))
                               (prems (list '(IN jlx_ RR) (list 'IN t 'RR) (list 'IN dl 'RR)
                                            '(IN jlr_ RR) (list 'IN w 'RR)
                                            (list '<= w dl) (list '<= w 'jlr_))))
                          (fact 'subset-mem-fwd 'jlw_ 'RR t)
                          (if right?
                              (begin
                                (dk-have! (list '< t (list '+ 'jlx_ dl))
                                  (lambda () (apply dk-ineq! (append prems (list (list '< t (list '+ 'jlx_ w)))))))
                                (dk-have! (list '< t (list '+ 'jlx_ 'jlr_))
                                  (lambda () (apply dk-ineq! (append prems (list (list '< t (list '+ 'jlx_ w))))))))
                              (begin
                                (dk-have! (list '< (list '- 'jlx_ dl) t)
                                  (lambda () (apply dk-ineq! (append prems (list (list '< (list '- 'jlx_ w) t))))))
                                (dk-have! (list '< (list '- 'jlx_ 'jlr_) t)
                                  (lambda () (apply dk-ineq! (append prems (list (list '< (list '- 'jlx_ w) t))))))))
                          (dk-apply! am t)
                          (dk-apply! c2 t)
                          (dk-apply! av t)
                          (subst (list '== (list 'f t) (list 'g t)))
                          (ass)))))))))))))

(sp (make-wff "forall([g, jlv_, f, jlw_, jlx_, jll_, jlr_], is-right-limit-within(g, jlv_, jlx_, jll_) implies
   jlw_ subset rr implies f in fun(jlw_, rr) implies pos-rr(jlr_) implies
   forall([jlt_ in jlw_], jlx_ < jlt_ implies jlt_ < jlx_ + jlr_ implies jlt_ in jlv_) implies
   forall([jlt_ in jlw_], jlx_ < jlt_ implies jlt_ < jlx_ + jlr_ implies f(jlt_) == g(jlt_)) implies
   is-right-limit-within(f, jlw_, jlx_, jll_))"))
(jxl-lim-local! #t)
(qed 'right-limit-within-local)
(topic! 'right-limit-within-local 'analysis)

(sp (make-wff "forall([g, jlv_, f, jlw_, jlx_, jll_, jlr_], is-left-limit-within(g, jlv_, jlx_, jll_) implies
   jlw_ subset rr implies f in fun(jlw_, rr) implies pos-rr(jlr_) implies
   forall([jlt_ in jlw_], jlx_ - jlr_ < jlt_ implies jlt_ < jlx_ implies jlt_ in jlv_) implies
   forall([jlt_ in jlw_], jlx_ - jlr_ < jlt_ implies jlt_ < jlx_ implies f(jlt_) == g(jlt_)) implies
   is-left-limit-within(f, jlw_, jlx_, jll_))"))
(jxl-lim-local! #f)
(qed 'left-limit-within-local)
(topic! 'left-limit-within-local 'analysis)

;;; =====================================================================
;;; (2b) REGULATED FUNCTIONS GLUE.  f1 regulated on [a, c], f2 on [c, b], f on [a, b] equal
;;; to f1 on [a, c) and to f2 on (c, b]: f is regulated on [a, b].  The value of f at c is
;;; free.  Each one-sided limit of f is one of f1 or f2, moved by the locality lemmas: a
;;; right limit at x < c is f1's (the half-neighbourhood (x, c) stays left of c), at x >= c
;;; f2's; a left limit at x <= c is f1's, at x > c f2's (the half-neighbourhood (c, x)).
;;; =====================================================================
(define jxl-ab '(CCINT a b))
(define jxl-ac '(CCINT a c))
(define jxl-cb '(CCINT c b))

(sp (make-wff "forall([a in rr, c in rr, b in rr], a < c implies c < b implies
   forall([f1, f2, f], is-regulated-on(f1, a, c) implies is-regulated-on(f2, c, b) implies
     f in fun(ccint(a, b), rr) implies
     forall([t in ccint(a, c)], t < c implies f(t) == f1(t)) implies
     forall([t in ccint(c, b)], c < t implies f(t) == f2(t)) implies
     is-regulated-on(f, a, b)))"))
(dk-peel!)
(define (jxl-rg-open! fn)
  (let ((ps (dk-split-all! (dk-landed* (lambda ()
              (mac-h 'IS-REGULATED-ON (list 'IS-REGULATED-ON fn
                                            (if (eq? fn 'f1) 'a 'c) (if (eq? fn 'f1) 'c 'b))))))))
    (cons (car (filter (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN))) ps))
          (car (filter (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'IS-LEFT-LIMIT-WITHIN))) ps)))))
(define jxl-rg-1 (jxl-rg-open! 'f1))
(define jxl-rg-2 (jxl-rg-open! 'f2))
(define jxl-rg-ag1 (dk-pick (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'f1) (dk-contains? g '==)))
                            "f agrees with f1"))
(define jxl-rg-ag2 (dk-pick (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'f2) (dk-contains? g '==)))
                            "f agrees with f2"))
(fact 'ccint-subset-rr 'a 'b)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(fact 'rr-pos-rr-of-lt 1)
(define jxl-rg-base '((IN a RR) (IN b RR) (IN c RR) (< a c) (< c b)))

;;; the limit of FN at X (in context: X in DOM and the guard), moved to f by the locality
;;; lemma at radius R; NEAR-IN proves (for the neighbourhood point t) t in DOM, NEAR-AG the
;;; agreement's guard.
(define (jxl-rg-move! right? fn x r dom ag)
  (let* ((l (dk-skolem! (dk-apply! ((if right? car cdr) (if (eq? fn 'f1) jxl-rg-1 jxl-rg-2)) x))))
    (ew l)
    (dk-chain! (dk-cite! (if right? 'right-limit-within-local 'left-limit-within-local)
                         fn dom 'f jxl-ab x l r)
      (lambda (ante)
        (lambda ()
          (let* ((ls (dk-peel!))
                 (t (cadr (car (filter (lambda (fm) (and (jxl-op? fm 'IN 3) (equal? (caddr fm) jxl-ab))) ls))))
                 (prems (append jxl-rg-base
                                (list (list 'IN x 'RR) (list 'IN t 'RR) (list 'IN r 'RR))
                                (filter (lambda (fm) (memq (jxl-head fm) '(< <=)))
                                        (append ls (dk-asms))))))
            (jxl-cc-parts! t 'a 'b)
            (let ((prems (append prems (list (list '<= 'a t) (list '<= t 'b)))))
              (if (eq? fn 'f1)
                  (jxl-in-ccint! t 'a 'c prems)
                  (jxl-in-ccint! t 'c 'b prems))
              (if (dk-contains? (dk-goal) '==)
                  (let ((g (if (eq? fn 'f1) (list '< t 'c) (list '< 'c t))))
                    (if (not (dk-asm? g)) (dk-have! g (lambda () (apply dk-ineq! prems))))
                    (dk-apply! ag t)
                    (ass))
                  (ass)))))))
    (ass)))

(mac 'IS-REGULATED-ON)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (not (eq? (jxl-head gl) 'FORALL))
         (if (jxl-op? gl '< 3) (dk-ineq! '(IN a RR) '(IN b RR) '(IN c RR) '(< a c) '(< c b)) (ass))
         (let* ((right? (dk-contains? gl 'IS-RIGHT-LIMIT-WITHIN))
                (x (dk-di-var!)))
           (dk-peel!)
           (jxl-cc-parts! x 'a 'b)
           (let ((xp (append jxl-rg-base (list (list 'IN x 'RR) (list '<= 'a x) (list '<= x 'b)
                                               (if right? (list '< x 'b) (list '< 'a x))))))
             (if right?
                 (use-em (list '<= 'c x)
                   (lambda ()
                     (jxl-in-ccint! x 'c 'b (append xp (list (list '<= 'c x))))
                     (jxl-rg-move! #t 'f2 x 1 jxl-cb jxl-rg-ag2))
                   (lambda ()
                     (jxl-not-le->lt! 'c x)
                     (jxl-in-ccint! x 'a 'c (append xp (list (list '< x 'c))))
                     (fact 'rr-sub-in-rr 'c x)
                     (dk-have! (list '< 0 (list '- 'c x)) (lambda () (apply dk-ineq! (append xp (list (list '< x 'c))))))
                     (fact 'rr-pos-rr-of-lt (list '- 'c x))
                     (jxl-rg-move! #t 'f1 x (list '- 'c x) jxl-ac jxl-rg-ag1)))
                 (use-em (list '<= x 'c)
                   (lambda ()
                     (jxl-in-ccint! x 'a 'c (append xp (list (list '<= x 'c))))
                     (jxl-rg-move! #f 'f1 x 1 jxl-ac jxl-rg-ag1))
                   (lambda ()
                     (jxl-not-le->lt! x 'c)
                     (jxl-in-ccint! x 'c 'b (append xp (list (list '< 'c x))))
                     (fact 'rr-sub-in-rr x 'c)
                     (dk-have! (list '< 0 (list '- x 'c)) (lambda () (apply dk-ineq! (append xp (list (list '< 'c x))))))
                     (fact 'rr-pos-rr-of-lt (list '- x 'c))
                     (jxl-rg-move! #f 'f2 x (list '- x 'c) jxl-cb jxl-rg-ag2))))))))))
(qed 'regulated-on-glue)
(topic! 'regulated-on-glue 'analysis)
(alias! 'regulated-on-glue
        "a function regulated on two adjacent intervals is regulated on their union")

;;; =====================================================================
;;; (2c) THE JUXTAPOSITION OF TWO ROADS IS A ROAD (Dieudonne 9.6).  Coordinatewise: the
;;; real (imaginary) part of the juxtaposed path is the glue of the two real (imaginary)
;;; parts, a primitive of the glue of the derivatives' parts by `primitive-glue'; the glued
;;; derivative parts are regulated by `regulated-on-glue'; continuity of the path is that
;;; of its two coordinates (`is-path-of-coords').
;;; =====================================================================
(define jxl-jx  '(JUXTA pgam1 pgam2 a b c))
(define jxl-jxd '(JUXTA dgam1 dgam2 a b c))
(define (jxl-coord proj fn lo hi)
  (list 'VNB-LAMBDA 'pat_ (list 'CCINT lo hi) (list proj (list fn 'pat_))))

;;; road read-offs of (PG, DG) on [LO, HI]
(define (jxl-road-facts! pg dg lo hi)
  (fact 'is-road-is-path pg dg lo hi)
  (fact 'is-path-in-fun pg lo hi)
  (fact 'is-road-dgam-in-fun pg dg lo hi)
  (let ((ep (dk-cite! 'is-path-endpoints pg lo hi)))
    (if (not (and (dk-asm? (list 'IN lo 'RR)) (dk-asm? (list 'IN hi 'RR)) (dk-asm? (list '< lo hi))))
        (dk-split-all! (list ep)))))

;;; (IN (proj (fn z)) RR) for fn in FUN(dom, CC), z in dom (in context)
(define (jxl-part-rr! proj fn dom z)
  (let ((v (list proj (list fn z))))
    (if (not (dk-asm? (list 'IN (list fn z) 'CC))) (fact 'fun-apply-type-c fn dom 'CC z))
    (if (not (dk-asm? (list 'IN v 'RR)))
        (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr) (list fn z)))
    v))

;;; the coordinate lambda (proj o fn) over DOM typed in FUN(DOM, RR)
(define (jxl-coord-type! proj fn lo hi)
  (let ((lam (jxl-coord proj fn lo hi))
        (dom (list 'CCINT lo hi)))
    (jxl-set! lo hi)
    (if (not (dk-asm? (list 'IN lam (list 'FUN dom 'RR))))
        (dk-have! (list 'IN lam (list 'FUN dom 'RR))
          (lambda ()
            (dk-lam-type!
             (lambda ()
               (let ((z (dk-di-var!)))
                 (jxl-part-rr! proj fn dom z)
                 (ass)))
             ass))))
    lam))

;;; an agreement antecedent (FORALL t (IMPLIES (IN t I) ... (== (L1 t) (L2 t)))) between
;;; coordinate lambdas, closed by the juxtaposition value law VALUE-LAW cited at P Q.
(define (jxl-agree! p q proj)
  (lambda ()
    (let* ((ls (dk-peel!))
           (mem (car (filter (lambda (fm) (and (jxl-op? fm 'IN 3) (pair? (caddr fm))
                                               (memq (car (caddr fm)) '(CCINT OOINT))))
                             ls)))
           (t (cadr mem))
           (iv (caddr mem))
           (lo (cadr iv)) (hi (caddr iv))
           (prems (list '(IN a RR) '(IN b RR) '(IN c RR) '(< a b) '(< b c) (list 'IN t 'RR))))
      (if (eq? (car iv) 'OOINT)
          (begin (jxl-oo-parts! t lo hi)
                 (set! prems (append prems (list (list '< lo t) (list '< t hi))))
                 (jxl-in-ccint! t lo hi prems))
          (begin (jxl-cc-parts! t lo hi)
                 (set! prems (append prems (list (list '<= lo t) (list '<= t hi))))))
      (jxl-in-ccint! t 'a 'c prems)
      (if (eq? lo 'a)
          (dk-cite! 'juxta-apply-left p q 'a 'b 'c t)
          (if (or (eq? (car iv) 'OOINT) (dk-asm? (list '< 'b t)))
              (begin (if (not (dk-asm? (list '< 'b t))) (dk-have! (list '< 'b t) (lambda () (apply dk-ineq! prems))))
                     (dk-cite! 'juxta-apply-right p q 'a 'b 'c t))
              (dk-cite! 'juxta-apply-right-closed p q 'a 'b 'c t)))
      ((dk-lane (lambda ()
         (dk-lam-b!)
         (dk-lane-if! (lambda () (subst (list '= (list (list 'JUXTA p q 'a 'b 'c) t)
                                             (list (if (eq? lo 'a) p q) t)))))
         (dk-lane-if! qrfl)))))))

(sp (make-wff "forall([pgam1, dgam1, pgam2, dgam2, a, b, c], is-road(pgam1, dgam1, a, b) implies
   is-road(pgam2, dgam2, b, c) implies pgam1(b) = pgam2(b) implies
   is-road(juxta(pgam1, pgam2, a, b, c), juxta(dgam1, dgam2, a, b, c), a, c))"))
(dk-peel!)
(jxl-road-facts! 'pgam1 'dgam1 'a 'b)
(jxl-road-facts! 'pgam2 'dgam2 'b 'c)
(dk-have! '(< a c) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(IN c RR) '(< a b) '(< b c))))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(dk-have! '(<= b c) (lambda () (dk-ineq! '(IN c RR) '(IN b RR) '(< b c))))
(fact 'rr-leq-reflexive 'b)
(jxl-in-ccint! 'b 'a 'b '((IN a RR) (IN b RR) (<= a b) (<= b b)))
(jxl-in-ccint! 'b 'b 'c '((IN c RR) (IN b RR) (<= b c) (<= b b)))
(dk-cite! 'juxta-in-fun 'pgam1 'pgam2 'a 'b 'c 'CC)
(dk-cite! 'juxta-in-fun 'dgam1 'dgam2 'a 'b 'c 'CC)
(fact 'ccint-subset-rr 'a 'c)
(for-each
 (lambda (proj)
   (let ((g1 (jxl-coord-type! proj 'pgam1 'a 'b))
         (f1 (jxl-coord-type! proj 'dgam1 'a 'b))
         (g2 (jxl-coord-type! proj 'pgam2 'b 'c))
         (f2 (jxl-coord-type! proj 'dgam2 'b 'c))
         (g  (jxl-coord-type! proj jxl-jx 'a 'c))
         (f  (jxl-coord-type! proj jxl-jxd 'a 'c))
         (anti (if (eq? proj 'real-part) 'is-road-re-antiderivative 'is-road-im-antiderivative))
         (regu (if (eq? proj 'real-part) 'is-road-re-regulated 'is-road-im-regulated)))
     (fact anti 'pgam1 'dgam1 'a 'b)
     (fact anti 'pgam2 'dgam2 'b 'c)
     (fact regu 'pgam1 'dgam1 'a 'b)
     (fact regu 'pgam2 'dgam2 'b 'c)
     (jxl-part-rr! proj 'pgam2 '(CCINT b c) 'b)
     (jxl-part-rr! proj 'pgam1 '(CCINT a b) 'b)
     (dk-have! (list '= (list g1 'b) (list g2 'b))
       (dk-lane (lambda ()
         (dk-lam-b!)
         (dk-lane-if! (lambda () (subst '(= (pgam1 b) (pgam2 b)))))
         (dk-lane-if! rfl))))
     (dk-chain! (dk-cite! 'primitive-glue 'a 'b 'c g1 f1 g2 f2 g f)
       (lambda (ante)
         (if (dk-contains? ante 'pgam1)
             (jxl-agree! 'pgam1 'pgam2 proj)
             (jxl-agree! 'dgam1 'dgam2 proj))))
     (dk-chain! (dk-cite! 'regulated-on-glue 'a 'b 'c f1 f2 f)
       (lambda (ante) (jxl-agree! 'dgam1 'dgam2 proj)))
     (fact 'primitive-continuous g f 'a 'c)))
 '(real-part imag-part))
(dk-chain! (dk-cite! 'is-path-of-coords 'a 'c jxl-jx (jxl-coord 'real-part jxl-jx 'a 'c) (jxl-coord 'imag-part jxl-jx 'a 'c))
  (lambda (ante)
    (lambda ()
      (let* ((ls (dk-peel!))
             (y (cadr (car (filter (lambda (fm) (jxl-op? fm 'IN 3)) ls)))))
        (jxl-part-rr! (if (dk-contains? ante 'real-part) 'real-part 'imag-part) jxl-jx '(CCINT a c) y)
        ((dk-lane (lambda () (dk-lam-b!) (dk-lane-if! rfl))))))))
(mac 'IS-ROAD)
(dk-conj-close! (lambda () (ass)))
(qed 'juxta-is-road)
(topic! 'juxta-is-road 'analysis)
(alias! 'juxta-is-road "the juxtaposition of two roads with a common endpoint is a road")

;;; =====================================================================
;;; (3a) THE LINE INTEGRAL SEES THE PATH ON [a, b] AND THE DERIVATIVE ON (a, b) ONLY.
;;; For the road (pgam, dgam) and f continuous on u around the trace, any qgam agreeing with
;;; pgam on [a, b] and qdg agreeing with dgam on (a, b) give the same integral: a primitive
;;; of a coordinate of t |-> f(pgam(t)) dgam(t) is one of t |-> f(qgam(t)) qdg(t)
;;; (`primitive-integrand-interior-congruence'), and `line-int-value' reads the integral
;;; off any pair of primitives.
;;; =====================================================================
(define jxl-H
  "u subset cc implies f in fun(u, cc) implies forall([rgy_ in u], is-continuous-at(subspace-ms(nf-metric-space(cc-normed-field), u), nf-metric-space(cc-normed-field), f, rgy_)) implies ")

;;; (IN (pg z) u) for z in [lo, hi] from trace(pg, lo, hi) subset u
(define (jxl-in-u! pg z lo hi)
  (let ((f (list 'IN (list pg z) 'u)))
    (if (not (dk-asm? f))
        (begin
          (dk-cite! 'trace-value-in pg lo hi z)
          (dk-cite! 'subset-mem-fwd (list 'TRACE pg lo hi) 'u (list pg z))))
    f))

;;; the integrand coordinate t |-> proj(f(pg(t)) dg(t)) over [lo, hi], and its typing
(define (jxl-integrand proj pg dg lo hi)
  (list 'VNB-LAMBDA 'pat_ (list 'CCINT lo hi)
        (list proj (list '* (list 'f (list pg 'pat_)) (list dg 'pat_)))))

;;; type f(PGU z) * dg(z) for z in DOM, PGU z already in u
(define (jxl-prod-cc! pgz dg dom z)
  (let ((fz (list 'f pgz)) (dz (list dg z)))
    (if (not (dk-asm? (list 'IN fz 'CC))) (fact 'fun-apply-type-c 'f 'u 'CC pgz))
    (if (not (dk-asm? (list 'IN dz 'CC))) (fact 'fun-apply-type-c dg dom 'CC z))
    (if (not (dk-asm? (list 'AND (list 'IN fz 'CC) (list 'IN dz 'CC))))
        (dk-have! (list 'AND (list 'IN fz 'CC) (list 'IN dz 'CC)) (lambda () (dk-conj-close! (lambda () (ass))))))
    (if (not (dk-asm? (list 'IN (list '* fz dz) 'CC))) (fact 'cc-mul-closed fz dz))
    (list '* fz dz)))

(sp (make-wff (string-append "forall([u, f, pgam, dgam, a, b], " jxl-H
  "is-road(pgam, dgam, a, b) implies trace(pgam, a, b) subset u implies
   forall([qgam in fun(ccint(a, b), cc), qdg in fun(ccint(a, b), cc)],
     forall([t in ccint(a, b)], qgam(t) == pgam(t)) implies
     forall([t in ooint(a, b)], qdg(t) == dgam(t)) implies
     line-int(f, qgam, qdg, a, b) = line-int(f, pgam, dgam, a, b)))")))
(dk-peel!)
(jxl-road-facts! 'pgam 'dgam 'a 'b)
(jxl-set! 'a 'b)
(fact 'ccint-subset-rr 'a 'b)
(fact 'ooint-subset-ccint 'a 'b)
(define jxl-lc-agp (dk-pick (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'qgam) (dk-contains? g '==)))
                            "qgam agrees with pgam"))
(define jxl-lc-agd (dk-pick (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'qdg) (dk-contains? g '==)))
                            "qdg agrees with dgam"))
(define jxl-lc-w
  (let* ((ex (dk-fact! 'line-int-exists 'u 'f 'pgam 'dgam 'a 'b))
         (w1 (dk-skolem! ex))
         (w2 (dk-skolem! (dk-pick (lambda (fm) (and ((dk-head? 'FORSOME) fm) (dk-contains? fm w1)))
                                  "the second primitive"))))
    (dk-split-all!)
    (list w1 w2)))
(define (jxl-lc-prim w proj)
  (dk-pick (lambda (fm) (and ((dk-head? 'IS-PRIMITIVE) fm) (eq? (cadr fm) w))) "a primitive of line-int-exists"))
(for-each
 (lambda (w proj)
   (let* ((pr (jxl-lc-prim w proj))
          (phi-u (caddr pr))
          (rp (jxl-integrand proj 'pgam 'dgam 'a 'b))
          (rq (jxl-integrand proj 'qgam 'qdg 'a 'b)))
     ;; the two reduced integrands, typed
     (for-each
      (lambda (lam q?)
        (dk-have! (list 'IN lam '(FUN (CCINT a b) RR))
          (lambda ()
            (dk-lam-type!
             (lambda ()
               (let ((z (dk-di-var!)))
                 (jxl-in-u! 'pgam z 'a 'b)
                 (if q?
                     (begin
                       (dk-apply! jxl-lc-agp z)
                       (subst (list '= (list 'qgam z) (list 'pgam z)))))
                 (let ((pz (jxl-prod-cc! (list 'pgam z) (if q? 'qdg 'dgam) '(CCINT a b) z)))
                   (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr) pz)
                   (ass))))
             ass))))
      (list rp rq) (list #f #t))
     ;; w is a primitive of the reduced pgam integrand ...
     (dk-chain! (dk-cite! 'pw-antiderivative-integrand-congruence w phi-u rp 'a 'b)
       (lambda (ante)
         (lambda ()
           (let ((z (dk-di-var!)))
             ((dk-lane (lambda () (dk-lam-b!) (dk-lane-if! qrfl))))))))
     ;; ... and of the qgam one
     (dk-chain! (dk-cite! 'primitive-integrand-interior-congruence w rp rq 'a 'b)
       (lambda (ante)
         (lambda ()
           (let ((z (dk-di-var!)))
             (fact 'subset-mem-fwd '(OOINT a b) '(CCINT a b) z)
             (dk-apply! jxl-lc-agp z)
             (dk-apply! jxl-lc-agd z)
             ((dk-lane (lambda ()
                (dk-lam-b!)
                (dk-lane-if! (lambda () (subst (list '= (list 'qgam z) (list 'pgam z)))))
                (dk-lane-if! (lambda () (subst (list '= (list 'qdg z) (list 'dgam z)))))
                (dk-lane-if! qrfl))))))))))
 jxl-lc-w '(real-part imag-part))
(define jxl-lc-vq (dk-cite! 'line-int-value 'f 'qgam 'qdg 'a 'b (car jxl-lc-w) (cadr jxl-lc-w)))
(define jxl-lc-vp (dk-cite! 'line-int-value 'f 'pgam 'dgam 'a 'b (car jxl-lc-w) (cadr jxl-lc-w)))
(subst jxl-lc-vq)
(subst (list '= (caddr jxl-lc-vp) (cadr jxl-lc-vp)))
(rfl)
(qed 'line-int-interior-congruence)
(topic! 'line-int-interior-congruence 'analysis)

;;; =====================================================================
;;; (3b) PROPOSITION 3.1 (path additivity), Dieudonne's juxtaposition form: the integral
;;; along the juxtaposition of (pgam1, dgam1) on [a, b] and (pgam2, dgam2) on [b, c] is the
;;; sum of the two integrals.  `line-int-adjacent' splits the juxtaposed road at b; the
;;; restriction to [a, b] agrees with pgam1 everywhere and its derivative with dgam1; the
;;; restriction to [b, c] agrees with pgam2 on [b, c] (the endpoint condition) and its
;;; derivative with dgam2 on (b, c) -- at b it carries dgam1(b), which the integral does not
;;; see (`line-int-interior-congruence').
;;; =====================================================================
;;; the restriction of JJ to [lo, hi]
(define (jxl-rs jj lo hi) (list 'RESTRICT jj (list 'CCINT lo hi)))

;;; line-int(f, P, D, lo, hi) = line-int(f, restrict(J), restrict(JD), lo, hi) landed, for
;;; (P, D) = (pgam1, dgam1) on [a, b] (LEFT? #t) or (pgam2, dgam2) on [b, c].  In context:
;;; the restricted road, its trace in u, the juxtaposition typings.
(define (jxl-piece! left? j jd p1 p2 d1 d2)
  (let* ((lo (if left? 'a 'b)) (hi (if left? 'b 'c))
         (rj (jxl-rs j lo hi)) (rjd (jxl-rs jd lo hi))
         (p (if left? p1 p2)) (d (if left? d1 d2))
         (prems (list '(IN a RR) '(IN b RR) '(IN c RR) '(< a b) '(< b c))))
    (dk-chain! (dk-cite! 'line-int-interior-congruence 'u 'f rj rjd lo hi p d)
      (lambda (ante)
        (lambda ()
          (let* ((ls (dk-peel!))
                 (mem (car (filter (lambda (fm) (and (jxl-op? fm 'IN 3) (pair? (caddr fm))
                                                     (memq (car (caddr fm)) '(CCINT OOINT))))
                                   ls)))
                 (t (cadr mem))
                 (open? (eq? (car (caddr mem)) 'OOINT))
                 (path? (dk-contains? (dk-goal) p))
                 (jj (if path? j jd))
                 (prems prems))
            (if open?
                (begin (jxl-oo-parts! t lo hi)
                       (set! prems (append prems (list (list 'IN t 'RR) (list '< lo t) (list '< t hi)))))
                (begin (jxl-cc-parts! t lo hi)
                       (set! prems (append prems (list (list 'IN t 'RR) (list '<= lo t) (list '<= t hi))))))
            (jxl-in-ccint! t lo hi prems)
            (jxl-in-ccint! t 'a 'c prems)
            (dk-cite! 'restrict-apply jj (list 'CCINT lo hi) t)
            (cond (left? (dk-cite! 'juxta-apply-left (if path? p1 d1) (if path? p2 d2) 'a 'b 'c t))
                  (path? (dk-cite! 'juxta-apply-right-closed p1 p2 'a 'b 'c t))
                  (#t (dk-cite! 'juxta-apply-right d1 d2 'a 'b 'c t)))
            ((dk-lane (lambda ()
               (subst (list '= (list (jxl-rs jj lo hi) t) (list jj t)))
               (dk-lane-if! (lambda () (subst (list '= (list jj t) (list (if path? p d) t)))))
               (dk-lane-if! qrfl))))))))))

(sp (make-wff (string-append "forall([u, f, pgam1, dgam1, pgam2, dgam2, a, b, c], " jxl-H
  "is-road(pgam1, dgam1, a, b) implies is-road(pgam2, dgam2, b, c) implies pgam1(b) = pgam2(b) implies
   trace(pgam1, a, b) subset u implies trace(pgam2, b, c) subset u implies
   line-int(f, juxta(pgam1, pgam2, a, b, c), juxta(dgam1, dgam2, a, b, c), a, c) =
     line-int(f, pgam1, dgam1, a, b) + line-int(f, pgam2, dgam2, b, c))")))
(dk-peel!)
(jxl-road-facts! 'pgam1 'dgam1 'a 'b)
(jxl-road-facts! 'pgam2 'dgam2 'b 'c)
(define jxl-pj-prems '((IN a RR) (IN b RR) (IN c RR) (< a b) (< b c)))
(dk-have! '(<= a b) (lambda () (apply dk-ineq! jxl-pj-prems)))
(dk-have! '(<= b c) (lambda () (apply dk-ineq! jxl-pj-prems)))
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'c)
(dk-cite! 'juxta-in-fun 'pgam1 'pgam2 'a 'b 'c 'CC)
(dk-cite! 'juxta-in-fun 'dgam1 'dgam2 'a 'b 'c 'CC)
(dk-cite! 'juxta-is-road 'pgam1 'dgam1 'pgam2 'dgam2 'a 'b 'c)
;; the trace of the juxtaposition lies in u
(dk-cite! 'juxta-trace-subset 'pgam1 'pgam2 'a 'b 'c)
(define jxl-pj-un '(UNION (TRACE pgam1 a b) (TRACE pgam2 b c)))
(dk-have! (list 'SUBSET jxl-pj-un 'u)
  (lambda ()
    (let* ((w (subset-by-element!))
           (um (dk-cite! 'union-membership '(TRACE pgam1 a b) '(TRACE pgam2 b c) w))
           (i1 (dk-cite! 'subset-mem-fwd '(TRACE pgam1 a b) 'u w))
           (i2 (dk-cite! 'subset-mem-fwd '(TRACE pgam2 b c) 'u w)))
      (dk-only! um i1 i2 (list 'IN w jxl-pj-un))
      (prop))))
(fact 'subset-trans (list 'TRACE jxl-jx 'a 'c) jxl-pj-un 'u)
;; split at b
(jxl-in-ooint! 'b 'a 'c jxl-pj-prems)
(define jxl-pj-split (dk-cite! 'line-int-adjacent 'u 'f jxl-jx jxl-jxd 'a 'c 'b))
;; the two restricted roads, their traces in u
(dk-cite! 'road-restrict jxl-jx jxl-jxd 'a 'c 'a 'b)
(dk-cite! 'road-restrict jxl-jx jxl-jxd 'a 'c 'b 'c)
(dk-cite! 'trace-restrict-subset jxl-jx 'a 'c 'a 'b)
(dk-cite! 'trace-restrict-subset jxl-jx 'a 'c 'b 'c)
(fact 'subset-trans (list 'TRACE (jxl-rs jxl-jx 'a 'b) 'a 'b) (list 'TRACE jxl-jx 'a 'c) 'u)
(fact 'subset-trans (list 'TRACE (jxl-rs jxl-jx 'b 'c) 'b 'c) (list 'TRACE jxl-jx 'a 'c) 'u)
(define jxl-pj-l (jxl-piece! #t jxl-jx jxl-jxd 'pgam1 'pgam2 'dgam1 'dgam2))
(define jxl-pj-r (jxl-piece! #f jxl-jx jxl-jxd 'pgam1 'pgam2 'dgam1 'dgam2))
(fact 'line-int-in-cc 'u 'f 'pgam1 'dgam1 'a 'b)
(fact 'line-int-in-cc 'u 'f 'pgam2 'dgam2 'b 'c)
(subst jxl-pj-split)
(subst (list '= (caddr jxl-pj-l) (cadr jxl-pj-l)))
(subst (list '= (caddr jxl-pj-r) (cadr jxl-pj-r)))
(rfl)
(qed 'line-int-juxta)
(topic! 'line-int-juxta 'analysis)
(alias! 'line-int-juxta "path additivity: the integral along a juxtaposition is the sum of the integrals")

;;; =====================================================================
;;; (3c) THE NOTES' FORM OF PROPOSITION 3.1, equation (49): gamma on [a, b], rho on [c, d]
;;; with gamma(b) = rho(c) (the endpoint of gamma is the initial point of rho).  The
;;; concatenation gamma || rho is the juxtaposition of gamma with rho SHIFTED to
;;; [b, b + (d - c)], s |-> rho(c + (s - b)) -- "we can shift the domain of definition of a
;;; path by an affine mapping without affecting the value of the integral" (the notes, (48));
;;; the shift is `road-affine-reparam' / `line-int-affine-reparam' with slope 1.
;;; =====================================================================
(define jxl-e '(+ b (- d c)))
(define jxl-sh (list 'VNB-LAMBDA 'jxs_ (list 'CCINT 'b jxl-e) '(prho (+ c (- jxs_ b)))))
(define jxl-shd (list 'VNB-LAMBDA 'jxs_ (list 'CCINT 'b jxl-e) '(drho (+ c (- jxs_ b)))))

(sp (make-wff (string-append "forall([u, f, pgam, dgam, prho, drho, a, b, c, d], " jxl-H
  "is-road(pgam, dgam, a, b) implies is-road(prho, drho, c, d) implies pgam(b) = prho(c) implies
   trace(pgam, a, b) subset u implies trace(prho, c, d) subset u implies
   line-int(f, juxta(pgam, vnb-lambda(jxs_, ccint(b, b + (d - c)), prho(c + (jxs_ - b))), a, b, b + (d - c)),
               juxta(dgam, vnb-lambda(jxs_, ccint(b, b + (d - c)), drho(c + (jxs_ - b))), a, b, b + (d - c)),
               a, b + (d - c)) =
     line-int(f, pgam, dgam, a, b) + line-int(f, prho, drho, c, d))")))
(dk-peel!)
(jxl-road-facts! 'pgam 'dgam 'a 'b)
(jxl-road-facts! 'prho 'drho 'c 'd)
(fact 'rr-sub-in-rr 'd 'c)
(fact 'rr-add-in-rr 'b '(- d c))
(fact 'rr-sub-in-rr 'c 'b)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(define jxl-lc-prems (list '(IN a RR) '(IN b RR) '(IN c RR) '(IN d RR) '(< a b) '(< c d)
                           (list 'IN jxl-e 'RR) '(IN (- d c) RR) '(IN (- c b) RR)))
(dk-have! (list '< 'b jxl-e) (lambda () (apply dk-ineq! jxl-lc-prems)))
(dk-have! (list '= '(+ (- c b) (* 1 b)) 'c) (lambda () (apply dk-ineq! jxl-lc-prems)))
(dk-have! (list '= (list '+ '(- c b) (list '* 1 jxl-e)) 'd) (lambda () (apply dk-ineq! jxl-lc-prems)))
(jxl-set! 'b jxl-e)
(fact 'ccint-subset-rr 'b jxl-e)
;;; a point z of [b, e]: c + (z - b) typed, in [c, d], equal to (c - b) + 1 * z
(define (jxl-lc-pt! z)
  (jxl-cc-parts! z 'b jxl-e)
  (let* ((w (list '+ 'c (list '- z 'b)))
         (ps (append jxl-lc-prems (list (list 'IN z 'RR) (list '<= 'b z) (list '<= z jxl-e)))))
    (fact 'rr-sub-in-rr z 'b)
    (fact 'rr-add-in-rr 'c (list '- z 'b))
    (jxl-in-ccint! w 'c 'd (append ps (list (list 'IN (list '- z 'b) 'RR) (list 'IN w 'RR))))
    (fact 'rr-mul-in-rr 1 z)
    (let ((eqn (list '= (list '+ '(- c b) (list '* 1 z)) w)))
      (if (not (dk-asm? eqn))
          (dk-have! eqn (lambda () (apply dk-ineq! (append ps (list (list 'IN (list '- z 'b) 'RR)
                                                                   (list 'IN w 'RR)
                                                                   (list 'IN (list '* 1 z) 'RR))))))))
    w))
;;; the shifted road and its derivative typed
(for-each
 (lambda (lam fn)
   (dk-have! (list 'IN lam (list 'FUN (list 'CCINT 'b jxl-e) 'CC))
     (lambda ()
       (dk-lam-type!
        (lambda ()
          (let* ((z (dk-di-var!)) (w (jxl-lc-pt! z)))
            (fact 'fun-apply-type-c fn '(CCINT c d) 'CC w)
            (ass)))
        ass))))
 (list jxl-sh jxl-shd) '(prho drho))
;;; the reparametrisation hypotheses: prho, drho at (c - b) + 1 * z
(define (jxl-lc-agree! deriv?)
  (lambda ()
    (let* ((z (dk-di-var!)) (w (jxl-lc-pt! z)))
      ((dk-lane (lambda ()
         (dk-lam-b!)
         (dk-lane-if! (lambda () (subst (list '= (list '+ '(- c b) (list '* 1 z)) w))))
         (if deriv?
             (dk-lane-if! (lambda ()
               (fact 'fun-apply-type-c 'drho '(CCINT c d) 'CC w)
               (subst (dk-cite! 'cc-one-mul (list 'drho w))))))
         (dk-lane-if! qrfl)))))))
(define jxl-lc-provers
  (lambda (ante)
    (if (dk-contains? ante 'drho) (jxl-lc-agree! #t) (jxl-lc-agree! #f))))
(dk-chain! (dk-cite! 'road-affine-reparam 'c 'd 'b jxl-e 1 '(- c b) 'prho 'drho jxl-sh jxl-shd)
           jxl-lc-provers)
(dk-chain! (dk-cite! 'trace-affine-reparam 'c 'd 'b jxl-e 1 '(- c b) 'prho jxl-sh) jxl-lc-provers)
(dk-split-all!)
(fact 'subset-trans (list 'TRACE jxl-sh 'b jxl-e) '(TRACE prho c d) 'u)
(define jxl-lc-rp
  (dk-chain! (dk-cite! 'line-int-affine-reparam 'u 'f 'prho 'drho 'c 'd 'b jxl-e 1 '(- c b) jxl-sh jxl-shd)
             jxl-lc-provers))
;;; the endpoint condition for the shifted road: sh(b) = prho(c) = pgam(b)
(fact 'rr-leq-reflexive 'b)
(jxl-in-ccint! 'b 'b jxl-e (append jxl-lc-prems (list '(<= b b) (list '< 'b jxl-e))))
(define jxl-lc-wb (jxl-lc-pt! 'b))
(dk-have! (list '= '(pgam b) (list jxl-sh 'b))
  (dk-lane (lambda ()
    (dk-lam-b!)
    (dk-lane-if! (lambda () (dk-have! (list '= jxl-lc-wb 'c) (lambda () (apply dk-ineq! (list '(IN b RR) '(IN c RR) (list 'IN jxl-lc-wb 'RR) '(IN (- b b) RR) (list '= '(+ (- c b) (* 1 b)) 'c) (list '= (list '+ '(- c b) (list '* 1 'b)) jxl-lc-wb)))))
                            (subst (list '= jxl-lc-wb 'c))))
    (dk-lane-if! (lambda () (subst '(= (pgam b) (prho c)))))
    (dk-lane-if! rfl))))
(define jxl-lc-sum
  (dk-cite! 'line-int-juxta 'u 'f 'pgam 'dgam jxl-sh jxl-shd 'a 'b jxl-e))
(fact 'line-int-in-cc 'u 'f 'pgam 'dgam 'a 'b)
(fact 'line-int-in-cc 'u 'f 'prho 'drho 'c 'd)
(subst jxl-lc-sum)
(subst jxl-lc-rp)
(rfl)
(qed 'line-int-concat)
(topic! 'line-int-concat 'analysis)
(alias! 'line-int-concat "the notes' Proposition 3.1: the integral along gamma || rho is the sum")

;;; =====================================================================
;;; (5a) THE LENGTH OF A ROAD.  t |-> |dgam(t)| is regulated (`regulated-on-magnitude' on
;;; the two regulated coordinates of dgam), hence has a primitive
;;; (`regulated-on-has-primitive'); ROAD-LENGTH, its PW-INT, is then a real number, >= 0.
;;; =====================================================================
(define (jxl-mag dg lo hi)
  (list 'VNB-LAMBDA 'rlt_ (list 'CCINT lo hi) (list 'magnitude (list dg 'rlt_))))

;;; |z| = |re z + im z * i| for z = DZ in CC in context: closes a goal
;;; (== X (magnitude (+ (real-part DZ) (* (imag-part DZ) +i)))) whose X is (magnitude DZ)
(define (jxl-mag-re-im! dz)
  (let ((rq (list 'real-part dz)) (iq (list 'imag-part dz)))
    (fact 'real-part-in-rr dz)
    (fact 'imag-part-in-rr dz)
    (dk-cite! 'cc-re-im-decompose dz)
    (fact 'rr-subset-cc iq)
    (fact 'cc-i-in)
    (dk-have! (list 'AND (list 'IN iq 'CC) '(IN +i CC)) (lambda () (dk-conj-close! (lambda () (ass)))))
    (fact 'cc-mul-comm iq '+i)
    ((dk-lane (lambda ()
       (subst (list '= (list '* iq '+i) (list '* '+i iq)))
       (dk-lane-if! (lambda () (subst (list '= (list '+ rq (list '* '+i iq)) dz))))
       (dk-lane-if! qrfl))))))

(define (jxl-mag-type! dg lo hi)
  (let ((mm (jxl-mag dg lo hi)) (dom (list 'CCINT lo hi)))
    (jxl-set! lo hi)
    (if (not (dk-asm? (list 'IN mm (list 'FUN dom 'RR))))
        (dk-have! (list 'IN mm (list 'FUN dom 'RR))
          (lambda ()
            (dk-lam-type!
             (lambda ()
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c dg dom 'CC z)
                 (fact 'cc-magnitude-closed (list dg z))
                 (ass)))
             ass))))
    mm))

(sp (make-wff "forall([pgam, dgam, a, b], is-road(pgam, dgam, a, b) implies
   is-regulated-on(vnb-lambda(rlt_, ccint(a, b), magnitude(dgam(rlt_))), a, b))"))
(dk-peel!)
(jxl-road-facts! 'pgam 'dgam 'a 'b)
(fact 'is-road-re-regulated 'pgam 'dgam 'a 'b)
(fact 'is-road-im-regulated 'pgam 'dgam 'a 'b)
(define jxl-rl-m (jxl-mag-type! 'dgam 'a 'b))
(dk-chain! (dk-cite! 'regulated-on-magnitude (jxl-coord 'real-part 'dgam 'a 'b) (jxl-coord 'imag-part 'dgam 'a 'b)
                     jxl-rl-m 'a 'b)
  (lambda (ante)
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'fun-apply-type-c 'dgam '(CCINT a b) 'CC z)
        (dk-lam-b!)
        (jxl-mag-re-im! (list 'dgam z))))))
(ass)
(qed 'road-length-regulated)
(topic! 'road-length-regulated 'analysis)

(sp (make-wff "forall([pgam, dgam, a, b], is-road(pgam, dgam, a, b) implies
   forsome([rlg_], is-primitive(rlg_, vnb-lambda(rlt_, ccint(a, b), magnitude(dgam(rlt_))), a, b)))"))
(dk-peel!)
(jxl-road-facts! 'pgam 'dgam 'a 'b)
(dk-cite! 'road-length-regulated 'pgam 'dgam 'a 'b)
(define jxl-rl-g (dk-skolem! (dk-fact! 'regulated-on-has-primitive 'a 'b (jxl-mag 'dgam 'a 'b))))
(ew jxl-rl-g)
(ass)
(qed 'road-length-primitive)
(topic! 'road-length-primitive 'analysis)

;;; (the primitive of |dgam| on [LO, HI], skolemised; returns it)
(define (jxl-len-prim! pg dg lo hi)
  (let ((g (dk-skolem! (dk-fact! 'road-length-primitive pg dg lo hi))))
    g))

(sp (make-wff "forall([pgam, dgam, a, b], is-road(pgam, dgam, a, b) implies road-length(dgam, a, b) in rr)"))
(dk-peel!)
(define jxl-rl-g2 (jxl-len-prim! 'pgam 'dgam 'a 'b))
(mac 'ROAD-LENGTH)
(fact 'pw-int-in-rr jxl-rl-g2 (jxl-mag 'dgam 'a 'b) 'a 'b)
(ass)
(qed 'road-length-in-rr)
(topic! 'road-length-in-rr 'analysis)

(sp (make-wff "forall([pgam, dgam, a, b], is-road(pgam, dgam, a, b) implies 0 <= road-length(dgam, a, b))"))
(dk-peel!)
(jxl-road-facts! 'pgam 'dgam 'a 'b)
(define jxl-rl-g3 (jxl-len-prim! 'pgam 'dgam 'a 'b))
(mac 'ROAD-LENGTH)
(dk-chain! (dk-cite! 'pw-int-nonneg jxl-rl-g3 (jxl-mag 'dgam 'a 'b) 'a 'b)
  (lambda (ante)
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'fun-apply-type-c 'dgam '(CCINT a b) 'CC z)
        (fact 'cc-magnitude-nonneg (list 'dgam z))
        ((dk-lane (lambda () (dk-lam-b!) (dk-lane-if! ass))))))))
(ass)
(qed 'road-length-nonneg)
(topic! 'road-length-nonneg 'analysis)

;;; =====================================================================
;;; (5b) PW-INT SEES THE INTEGRAND ON (a, b) ONLY -- the integral form of
;;; `primitive-integrand-interior-congruence'.
;;; =====================================================================
(sp (make-wff "forall([pwf_, pphi_, ppsi_, a, b], is-primitive(pwf_, pphi_, a, b) implies
   ppsi_ in fun(ccint(a, b), rr) implies forall([pay_ in ooint(a, b)], pphi_(pay_) == ppsi_(pay_)) implies
   pw-int(pphi_, a, b) = pw-int(ppsi_, a, b))"))
(dk-peel!)
(fact 'primitive-integrand-interior-congruence 'pwf_ 'pphi_ 'ppsi_ 'a 'b)
(define jxl-pic-1 (dk-cite! 'pw-int-value 'pwf_ 'pphi_ 'a 'b))
(define jxl-pic-2 (dk-cite! 'pw-int-value 'pwf_ 'ppsi_ 'a 'b))
(subst jxl-pic-1)
(subst (list '= (caddr jxl-pic-2) (cadr jxl-pic-2)))
(rfl)
(qed 'pw-int-interior-congruence)
(topic! 'pw-int-interior-congruence 'analysis)

;;; =====================================================================
;;; (5c) LENGTH IS ADDITIVE UNDER JUXTAPOSITION (from pw-int-adjacent).
;;; =====================================================================
(sp (make-wff "forall([pgam1, dgam1, pgam2, dgam2, a, b, c], is-road(pgam1, dgam1, a, b) implies
   is-road(pgam2, dgam2, b, c) implies pgam1(b) = pgam2(b) implies
   road-length(juxta(dgam1, dgam2, a, b, c), a, c) = road-length(dgam1, a, b) + road-length(dgam2, b, c))"))
(dk-peel!)
(jxl-road-facts! 'pgam1 'dgam1 'a 'b)
(jxl-road-facts! 'pgam2 'dgam2 'b 'c)
(define jxl-lj-prems '((IN a RR) (IN b RR) (IN c RR) (< a b) (< b c)))
(dk-have! '(<= a b) (lambda () (apply dk-ineq! jxl-lj-prems)))
(dk-have! '(<= b c) (lambda () (apply dk-ineq! jxl-lj-prems)))
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'c)
(dk-cite! 'juxta-in-fun 'dgam1 'dgam2 'a 'b 'c 'CC)
(dk-cite! 'juxta-is-road 'pgam1 'dgam1 'pgam2 'dgam2 'a 'b 'c)
(define jxl-lj-m (jxl-mag jxl-jxd 'a 'c))
(define jxl-lj-g (jxl-len-prim! jxl-jx jxl-jxd 'a 'c))
(define jxl-lj-g1 (jxl-len-prim! 'pgam1 'dgam1 'a 'b))
(define jxl-lj-g2 (jxl-len-prim! 'pgam2 'dgam2 'b 'c))
(fact 'primitive-integrand-in-fun jxl-lj-g jxl-lj-m 'a 'c)
(jxl-in-ooint! 'b 'a 'c jxl-lj-prems)
(define jxl-lj-split (dk-cite! 'pw-int-adjacent 'a 'c 'b jxl-lj-g jxl-lj-m))
(fact 'ccint-subset-ccint 'a 'c 'a 'b)
(fact 'ccint-subset-ccint 'a 'c 'b 'c)
;;; pw-int(|dgam_k|, lo, hi) = pw-int(restrict(M, [lo, hi]), lo, hi)
(define (jxl-lj-piece! left?)
  (let* ((lo (if left? 'a 'b)) (hi (if left? 'b 'c))
         (dk (if left? 'dgam1 'dgam2)) (gk (if left? jxl-lj-g1 jxl-lj-g2))
         (rm (list 'RESTRICT jxl-lj-m (list 'CCINT lo hi))))
    (fact 'restrict-in-fun jxl-lj-m '(CCINT a c) 'RR (list 'CCINT lo hi))
    (fact 'ooint-subset-ccint lo hi)
    (dk-chain! (dk-cite! 'pw-int-interior-congruence gk (jxl-mag dk lo hi) rm lo hi)
      (lambda (ante)
        (lambda ()
          (let* ((t (dk-di-var!))
                 (prems (append jxl-lj-prems (list (list 'IN t 'RR)))))
            (jxl-oo-parts! t lo hi)
            (set! prems (append prems (list (list '< lo t) (list '< t hi))))
            (jxl-in-ccint! t lo hi prems)
            (jxl-in-ccint! t 'a 'c prems)
            (dk-cite! 'restrict-apply jxl-lj-m (list 'CCINT lo hi) t)
            (if left?
                (dk-cite! 'juxta-apply-left 'dgam1 'dgam2 'a 'b 'c t)
                (dk-cite! 'juxta-apply-right 'dgam1 'dgam2 'a 'b 'c t))
            ((dk-lane (lambda ()
               (subst (list '= (list rm t) (list jxl-lj-m t)))
               (dk-lam-b!)
               (dk-lane-if! (lambda () (subst (list '= (list jxl-jxd t) (list dk t)))))
               (dk-lane-if! qrfl))))))))))
(define jxl-lj-l (jxl-lj-piece! #t))
(define jxl-lj-r (jxl-lj-piece! #f))
(fact 'pw-int-in-rr jxl-lj-g1 (jxl-mag 'dgam1 'a 'b) 'a 'b)
(fact 'pw-int-in-rr jxl-lj-g2 (jxl-mag 'dgam2 'b 'c) 'b 'c)
(mac 'ROAD-LENGTH)
(subst jxl-lj-split)
(subst (list '= (caddr jxl-lj-l) (cadr jxl-lj-l)))
(subst (list '= (caddr jxl-lj-r) (cadr jxl-lj-r)))
(rfl)
(qed 'road-length-juxta)
(topic! 'road-length-juxta 'analysis)
(alias! 'road-length-juxta "the length of a juxtaposition of roads is the sum of the lengths")

;;; =====================================================================
;;; (4a) THE SEGMENT SHIFTED TO [k, k + 1]: s |-> SEG-PATH(p, q)(s - k), with derivative
;;; s |-> SEG-DERIV(p, q)(s - k): a road (`road-affine-reparam', slope 1, offset -k), with
;;; the segment's trace; and the length of a segment.
;;; =====================================================================
(define jxl-shp '(VNB-LAMBDA trs_ (CCINT k m) ((SEG-PATH p q) (- trs_ k))))
(define jxl-shd2 '(VNB-LAMBDA trs_ (CCINT k m) ((SEG-DERIV p q) (- trs_ k))))
(define jxl-sh-prems '((IN k RR) (IN m RR) (= m (+ k 1)) (IN (- k) RR)))

;;; the shift set-up: p q in CC, k m in RR, m = k + 1 in context
(define (jxl-sh-setup!)
  (fact 'rr-zero-in)
  (fact 'rr-one-in)
  (fact 'rr-zero-lt-one)
  (fact 'rr-neg-closed 'k)
  (dk-have! '(< k m) (lambda () (apply dk-ineq! jxl-sh-prems)))
  (dk-have! '(= (+ (- k) (* 1 k)) 0) (lambda () (apply dk-ineq! jxl-sh-prems)))
  (dk-have! '(= (+ (- k) (* 1 m)) 1) (lambda () (apply dk-ineq! jxl-sh-prems)))
  (dk-cite! 'seg-path-is-road 'p 'q)
  (jxl-road-facts! '(SEG-PATH p q) '(SEG-DERIV p q) 0 1)
  (jxl-set! 'k 'm)
  (fact 'ccint-subset-rr 'k 'm))

;;; z in [k, m]: z - k in [0, 1], and (-k) + 1 * z = z - k
(define (jxl-sh-pt! z)
  (jxl-cc-parts! z 'k 'm)
  (let ((ps (append jxl-sh-prems (list (list 'IN z 'RR) (list '<= 'k z) (list '<= z 'm)))))
    (fact 'rr-sub-in-rr z 'k)
    (jxl-in-ccint! (list '- z 'k) 0 1 (append ps (list (list 'IN (list '- z 'k) 'RR))))
    (fact 'rr-mul-in-rr 1 z)
    (let ((eqn (list '= (list '+ '(- k) (list '* 1 z)) (list '- z 'k))))
      (if (not (dk-asm? eqn))
          (dk-have! eqn (lambda () (apply dk-ineq! (append ps (list (list 'IN (list '- z 'k) 'RR)
                                                                   (list 'IN (list '* 1 z) 'RR))))))))
    (list '- z 'k)))

(define (jxl-sh-type! lam fn)
  (dk-have! (list 'IN lam '(FUN (CCINT k m) CC))
    (lambda ()
      (dk-lam-type!
       (lambda ()
         (let* ((z (dk-di-var!)) (w (jxl-sh-pt! z)))
           (fact 'fun-apply-type-c fn '(CCINT 0 1) 'CC w)
           (ass)))
       ass))))

(define (jxl-sh-agree! ante)
  (let ((deriv? (dk-contains? ante 'SEG-DERIV)))
    (lambda ()
      (let* ((z (dk-di-var!)) (w (jxl-sh-pt! z)))
        ((dk-lane (lambda ()
           (dk-lam-b!)
           (dk-lane-if! (lambda () (subst (list '= (list '+ '(- k) (list '* 1 z)) w))))
           (if deriv?
               (dk-lane-if! (lambda ()
                 (fact 'fun-apply-type-c '(SEG-DERIV p q) '(CCINT 0 1) 'CC w)
                 (subst (dk-cite! 'cc-one-mul (list '(SEG-DERIV p q) w))))))
           (dk-lane-if! qrfl))))))))

(sp (make-wff "forall([p in cc, q in cc, k in rr, m in rr], m = k + 1 implies
   is-road(vnb-lambda(trs_, ccint(k, m), (seg-path(p, q))(trs_ - k)),
           vnb-lambda(trs_, ccint(k, m), (seg-deriv(p, q))(trs_ - k)), k, m))"))
(dk-peel!)
(jxl-sh-setup!)
(jxl-sh-type! jxl-shp '(SEG-PATH p q))
(jxl-sh-type! jxl-shd2 '(SEG-DERIV p q))
(dk-chain! (dk-cite! 'road-affine-reparam 0 1 'k 'm 1 '(- k) '(SEG-PATH p q) '(SEG-DERIV p q) jxl-shp jxl-shd2)
           jxl-sh-agree!)
(ass)
(qed 'seg-shift-is-road)
(topic! 'seg-shift-is-road 'analysis)

(sp (make-wff "forall([p in cc, q in cc, k in rr, m in rr], m = k + 1 implies
   trace(vnb-lambda(trs_, ccint(k, m), (seg-path(p, q))(trs_ - k)), k, m) = trace(seg-path(p, q), 0, 1))"))
(dk-peel!)
(jxl-sh-setup!)
(jxl-sh-type! jxl-shp '(SEG-PATH p q))
(dk-split-all! (list (dk-chain! (dk-cite! 'trace-affine-reparam 0 1 'k 'm 1 '(- k) '(SEG-PATH p q) jxl-shp)
                                jxl-sh-agree!)))
;;; two traces, each a subset of the other: equal (extensionality)
(define (jxl-set-eq! s1 s2 set1 set2)
  (set1) (set2)
  (dk-have! (list 'AND (list 'IN s1 'SET) (list 'IN s2 'SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
  (let ((ext (begin (fact 'extensionality s1 s2) (iff-for (list '= s1 s2))))
        (body (list 'FORALL 'jxw_ (list 'IFF (list 'IN 'jxw_ s1) (list 'IN 'jxw_ s2)))))
    (dk-have! body
      (lambda ()
        (di)
        (let* ((v (cadr (cadr (dk-goal))))
               (i1 (dk-cite! 'subset-mem-fwd s1 s2 v))
               (i2 (dk-cite! 'subset-mem-fwd s2 s1 v)))
          (dk-only! i1 i2)
          (prop))))
    (dk-only! ext body)
    (prop)))
(jxl-set-eq! (list 'TRACE jxl-shp 'k 'm) '(TRACE (SEG-PATH p q) 0 1)
             (lambda () (dk-cite! 'trace-is-set jxl-shp 'k 'm))
             (lambda () (dk-cite! 'trace-is-set '(SEG-PATH p q) 0 1)))
(qed 'seg-shift-trace)
(topic! 'seg-shift-trace 'analysis)

;;; the length of a segment (shifted or not): pw-int of the constant |q - p|
(define (jxl-seg-len! lam lo hi shifted?)
  (let ((mm (jxl-mag lam lo hi))
        (x '(magnitude (- q p))))
    (fact 'cc-sub-in-cc 'q 'p)
    (fact 'cc-magnitude-closed '(- q p))
    (dk-have! (list 'IN mm (list 'FUN (list 'CCINT lo hi) 'RR))
      (lambda ()
        (dk-lam-type!
         (lambda ()
           (let* ((z (dk-di-var!)))
             (if shifted? (jxl-sh-pt! z))
             (fact 'fun-apply-type-c lam (list 'CCINT lo hi) 'CC z)
             (fact 'cc-magnitude-closed (list lam z))
             (ass)))
         ass)))
    (mac 'ROAD-LENGTH)
    (let ((cst (dk-chain! (dk-cite! 'pw-int-const lo hi x mm)
                 (lambda (ante)
                   (lambda ()
                     (let* ((z (dk-di-var!))
                            (w (if shifted? (jxl-sh-pt! z) z)))
                       ((dk-lane (lambda ()
                          (dk-lam-b!)
                          (dk-lane-if! (lambda () (mac 'SEG-DERIV)))
                          (dk-lane-if! (lambda () (dk-lam-b!)))
                          (dk-lane-if! qrfl))))))))))
      (subst cst)
      (dk-have! (list '= (list '- hi lo) 1) (lambda () (apply dk-ineq! (append (if shifted? jxl-sh-prems '()) '()))))
      (subst (list '= (list '- hi lo) 1))
      (dk-ineq! (list 'IN x 'RR)))))

(sp (make-wff "forall([p in cc, q in cc], road-length(seg-deriv(p, q), 0, 1) = magnitude(q - p))"))
(dk-peel!)
(dk-cite! 'seg-path-is-road 'p 'q)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(jxl-road-facts! '(SEG-PATH p q) '(SEG-DERIV p q) 0 1)
(jxl-set! 0 1)
(jxl-seg-len! '(SEG-DERIV p q) 0 1 #f)
(qed 'road-length-segment)
(topic! 'road-length-segment 'analysis)

(sp (make-wff "forall([p in cc, q in cc, k in rr, m in rr], m = k + 1 implies
   road-length(vnb-lambda(trs_, ccint(k, m), (seg-deriv(p, q))(trs_ - k)), k, m) = magnitude(q - p))"))
(dk-peel!)
(jxl-sh-setup!)
(jxl-sh-type! jxl-shd2 '(SEG-DERIV p q))
(jxl-seg-len! jxl-shd2 'k 'm #t)
(qed 'seg-shift-length)
(topic! 'seg-shift-length 'analysis)

(sp (make-wff (string-append "forall([u, f], " jxl-H
  "forall([p in cc, q in cc, k in rr, m in rr], m = k + 1 implies trace(seg-path(p, q), 0, 1) subset u implies
     line-int(f, vnb-lambda(trs_, ccint(k, m), (seg-path(p, q))(trs_ - k)),
                 vnb-lambda(trs_, ccint(k, m), (seg-deriv(p, q))(trs_ - k)), k, m) =
       line-int(f, seg-path(p, q), seg-deriv(p, q), 0, 1)))")))
(dk-peel!)
(jxl-sh-setup!)
(jxl-sh-type! jxl-shp '(SEG-PATH p q))
(jxl-sh-type! jxl-shd2 '(SEG-DERIV p q))
(dk-chain! (dk-cite! 'line-int-affine-reparam 'u 'f '(SEG-PATH p q) '(SEG-DERIV p q) 0 1 'k 'm 1 '(- k) jxl-shp jxl-shd2)
           jxl-sh-agree!)
(ass)
(qed 'seg-shift-line-int)
(topic! 'seg-shift-line-int 'analysis)

;;; =====================================================================
;;; (4b) THE TRIANGULAR ROAD: a road on [0, 3], its trace the three sides, the integral
;;; along it TRI-INT (the promise of docs/goursat-definitions-2026-09-25.md, item 2), its
;;; length the perimeter.
;;; =====================================================================
(define jxl-sab '(SEG-PATH a b))
(define jxl-dab '(SEG-DERIV a b))
(define jxl-p2 '(VNB-LAMBDA trs_ (CCINT 1 2) ((SEG-PATH b c) (- trs_ 1))))
(define jxl-d2 '(VNB-LAMBDA trs_ (CCINT 1 2) ((SEG-DERIV b c) (- trs_ 1))))
(define jxl-p3 '(VNB-LAMBDA trs_ (CCINT 2 3) ((SEG-PATH c a) (- trs_ 2))))
(define jxl-d3 '(VNB-LAMBDA trs_ (CCINT 2 3) ((SEG-DERIV c a) (- trs_ 2))))
(define jxl-j1 (list 'JUXTA jxl-sab jxl-p2 0 1 2))
(define jxl-jd1 (list 'JUXTA jxl-dab jxl-d2 0 1 2))
(define jxl-j2 (list 'JUXTA jxl-j1 jxl-p3 0 2 3))
(define jxl-jd2 (list 'JUXTA jxl-jd1 jxl-d3 0 2 3))

(define (jxl-num! n)
  (let ((f (list 'IN n 'RR)))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (arith))))
    f))

;;; a, b, c in CC in context: the three sides as roads, the two juxtapositions as roads,
;;; the typings and the two endpoint conditions.
(define (jxl-tri-setup!)
  (for-each jxl-num! '(0 1 2 3))
  (fact 'rr-zero-lt-one)
  (let ((nums '((IN 0 RR) (IN 1 RR) (IN 2 RR) (IN 3 RR))))
    (for-each (lambda (f) (dk-have! f (lambda () (apply dk-ineq! nums))))
              '((< 1 2) (< 2 3) (<= 0 1) (<= 1 2) (<= 2 3) (<= 0 2) (<= 1 1) (<= 2 2)
                (= 2 (+ 1 1)) (= 3 (+ 2 1)) (= (- 1 1) 0) (= (- 2 1) 1) (= (- 2 2) 0)))
    (jxl-in-ccint! 1 0 1 nums) (jxl-in-ccint! 1 1 2 nums) (jxl-in-ccint! 0 0 1 nums)
    (jxl-in-ccint! 2 1 2 nums) (jxl-in-ccint! 2 2 3 nums) (jxl-in-ccint! 2 0 2 nums))
  (dk-cite! 'seg-path-is-road 'a 'b)
  (dk-cite! 'seg-shift-is-road 'b 'c 1 2)
  (dk-cite! 'seg-shift-is-road 'c 'a 2 3)
  (jxl-road-facts! jxl-sab jxl-dab 0 1)
  (jxl-road-facts! jxl-p2 jxl-d2 1 2)
  (jxl-road-facts! jxl-p3 jxl-d3 2 3)
  (for-each (lambda (pq) (fact 'cc-sub-in-cc (car pq) (cadr pq))) '((b a) (c b) (a c)))
  (fact 'rr-subset-cc 0)
  (fact 'rr-subset-cc 1)
  ;; the endpoint conditions
  (let ((v1 (dk-cite! 'seg-path-apply 'a 'b 1))
        (v0 (dk-cite! 'seg-path-apply 'b 'c 0)))
    (dk-have! (list '= (list jxl-sab 1) (list jxl-p2 1))
      (dk-lane (lambda ()
        (subst v1)
        (dk-lam-b!)
        (dk-lane-if! (lambda () (subst '(= (- 1 1) 0))))
        (dk-lane-if! (lambda () (subst v0)))
        (dk-lane-if! crs)))))
  (dk-cite! 'juxta-is-road jxl-sab jxl-dab jxl-p2 jxl-d2 0 1 2)
  (jxl-road-facts! jxl-j1 jxl-jd1 0 2)
  (dk-cite! 'juxta-apply-right jxl-sab jxl-p2 0 1 2 2)
  (let ((v1 (dk-cite! 'seg-path-apply 'b 'c 1))
        (v0 (dk-cite! 'seg-path-apply 'c 'a 0)))
    (dk-have! (list '= (list jxl-j1 2) (list jxl-p3 2))
      (dk-lane (lambda ()
        (subst (list '= (list jxl-j1 2) (list jxl-p2 2)))
        (dk-lam-b!)
        (dk-lane-if! (lambda () (subst '(= (- 2 1) 1))))
        (dk-lane-if! (lambda () (subst '(= (- 2 2) 0))))
        (dk-lane-if! (lambda () (subst v1)))
        (dk-lane-if! (lambda () (subst v0)))
        (dk-lane-if! crs)))))
  (dk-cite! 'juxta-is-road jxl-j1 jxl-jd1 jxl-p3 jxl-d3 0 2 3)
  (jxl-road-facts! jxl-j2 jxl-jd2 0 3))

(sp (make-wff "forall([a in cc, b in cc, c in cc], is-road(tri-road(a, b, c), tri-road-deriv(a, b, c), 0, 3))"))
(dk-peel!)
(jxl-tri-setup!)
(mac 'TRI-ROAD)
(mac 'TRI-ROAD-DERIV)
(ass)
(qed 'tri-road-is-road)
(topic! 'tri-road-is-road 'analysis)

(define jxl-t-ab '(TRACE (SEG-PATH a b) 0 1))
(define jxl-t-bc '(TRACE (SEG-PATH b c) 0 1))
(define jxl-t-ca '(TRACE (SEG-PATH c a) 0 1))

(sp (make-wff "forall([a in cc, b in cc, c in cc], trace(tri-road(a, b, c), 0, 3) =
   union(union(trace(seg-path(a, b), 0, 1), trace(seg-path(b, c), 0, 1)), trace(seg-path(c, a), 0, 1)))"))
(dk-peel!)
(jxl-tri-setup!)
(mac 'TRI-ROAD)
(define jxl-tt-2 (dk-cite! 'juxta-trace jxl-j1 jxl-p3 0 2 3))
(define jxl-tt-1 (dk-cite! 'juxta-trace jxl-sab jxl-p2 0 1 2))
(define jxl-tt-s2 (dk-cite! 'seg-shift-trace 'b 'c 1 2))
(define jxl-tt-s3 (dk-cite! 'seg-shift-trace 'c 'a 2 3))
(subst jxl-tt-2)
(subst jxl-tt-1)
(subst jxl-tt-s2)
(subst jxl-tt-s3)
(rfl)
(qed 'tri-road-trace)
(topic! 'tri-road-trace 'analysis)

(sp (make-wff (string-append "forall([u, f], " jxl-H
  "forall([a in cc, b in cc, c in cc], trace(seg-path(a, b), 0, 1) subset u implies
     trace(seg-path(b, c), 0, 1) subset u implies trace(seg-path(c, a), 0, 1) subset u implies
     tri-int(f, a, b, c) = line-int(f, tri-road(a, b, c), tri-road-deriv(a, b, c), 0, 3)))")))
(dk-peel!)
(jxl-tri-setup!)
;; the traces of the shifted sides and of the first juxtaposition lie in u
(define jxl-ti-s2 (dk-cite! 'seg-shift-trace 'b 'c 1 2))
(define jxl-ti-s3 (dk-cite! 'seg-shift-trace 'c 'a 2 3))
(dk-have! (list 'SUBSET (list 'TRACE jxl-p2 1 2) 'u) (lambda () (subst jxl-ti-s2) (ass)))
(dk-have! (list 'SUBSET (list 'TRACE jxl-p3 2 3) 'u) (lambda () (subst jxl-ti-s3) (ass)))
(dk-cite! 'juxta-trace-subset jxl-sab jxl-p2 0 1 2)
(define jxl-ti-un (list 'UNION jxl-t-ab (list 'TRACE jxl-p2 1 2)))
(dk-have! (list 'SUBSET jxl-ti-un 'u)
  (lambda ()
    (let* ((w (subset-by-element!))
           (um (dk-cite! 'union-membership jxl-t-ab (list 'TRACE jxl-p2 1 2) w))
           (i1 (dk-cite! 'subset-mem-fwd jxl-t-ab 'u w))
           (i2 (dk-cite! 'subset-mem-fwd (list 'TRACE jxl-p2 1 2) 'u w)))
      (dk-only! um i1 i2 (list 'IN w jxl-ti-un))
      (prop))))
(fact 'subset-trans (list 'TRACE jxl-j1 0 2) jxl-ti-un 'u)
;; the two juxtapositions and the two shifts
(define jxl-ti-j1 (dk-cite! 'line-int-juxta 'u 'f jxl-sab jxl-dab jxl-p2 jxl-d2 0 1 2))
(define jxl-ti-j2 (dk-cite! 'line-int-juxta 'u 'f jxl-j1 jxl-jd1 jxl-p3 jxl-d3 0 2 3))
(define jxl-ti-l2 (dk-cite! 'seg-shift-line-int 'u 'f 'b 'c 1 2))
(define jxl-ti-l3 (dk-cite! 'seg-shift-line-int 'u 'f 'c 'a 2 3))
(for-each (lambda (pq)
            (dk-cite! 'seg-path-is-road (car pq) (cadr pq))
            (fact 'line-int-in-cc 'u 'f (list 'SEG-PATH (car pq) (cadr pq)) (list 'SEG-DERIV (car pq) (cadr pq)) 0 1))
          '((a b) (b c) (c a)))
(mac 'TRI-INT)
(mac 'SEG-INT)
(mac 'TRI-ROAD)
(mac 'TRI-ROAD-DERIV)
(subst jxl-ti-j2)
(subst jxl-ti-j1)
(subst jxl-ti-l2)
(subst jxl-ti-l3)
(define (jxl-cc-add! x y)
  (dk-have! (list 'AND (list 'IN x 'CC) (list 'IN y 'CC)) (lambda () (dk-conj-close! (lambda () (ass)))))
  (fact 'cc-add-closed x y)
  (list '+ x y))
(let ((l (lambda (p q) (list 'LINE-INT 'f (list 'SEG-PATH p q) (list 'SEG-DERIV p q) 0 1))))
  (jxl-cc-add! (jxl-cc-add! (l 'a 'b) (l 'b 'c)) (l 'c 'a)))
(rfl)
(qed 'tri-int-is-line-int)
(topic! 'tri-int-is-line-int 'analysis)
(alias! 'tri-int-is-line-int "the integral around a triangle is the integral along the triangular road")

(sp (make-wff "forall([a in cc, b in cc, c in cc], road-length(tri-road-deriv(a, b, c), 0, 3) =
   (magnitude(b - a) + magnitude(c - b)) + magnitude(a - c))"))
(dk-peel!)
(jxl-tri-setup!)
(define jxl-lt-2 (dk-cite! 'road-length-juxta jxl-j1 jxl-jd1 jxl-p3 jxl-d3 0 2 3))
(define jxl-lt-1 (dk-cite! 'road-length-juxta jxl-sab jxl-dab jxl-p2 jxl-d2 0 1 2))
(define jxl-lt-s1 (dk-cite! 'road-length-segment 'a 'b))
(define jxl-lt-s2 (dk-cite! 'seg-shift-length 'b 'c 1 2))
(define jxl-lt-s3 (dk-cite! 'seg-shift-length 'c 'a 2 3))
(for-each (lambda (d) (fact 'cc-magnitude-closed d)) '((- b a) (- c b) (- a c)))
(mac 'TRI-ROAD-DERIV)
(subst jxl-lt-2)
(subst jxl-lt-1)
(subst jxl-lt-s1)
(subst jxl-lt-s2)
(subst jxl-lt-s3)
(fact 'rr-add-in-rr '(magnitude (- b a)) '(magnitude (- c b)))
(fact 'rr-add-in-rr '(+ (magnitude (- b a)) (magnitude (- c b))) '(magnitude (- a c)))
(rfl)
(qed 'road-length-tri)
(topic! 'road-length-tri 'analysis)
(alias! 'road-length-tri "the length of the triangular road is the perimeter")

;;; =====================================================================
;;; (5d) THE ESTIMATE (53) of the notes: |int_gamma f| <= L(gamma) * M when |f| <= M on
;;; the trace.  From (54) (`line-int-abs-bound'): |int_gamma f| <= int |f(gamma)| |gamma'|;
;;; that integrand is regulated (a product of two regulated magnitudes), so it has a
;;; primitive, and `pw-int-monotone' against M |gamma'| (`pw-antiderivative-real-mul')
;;; gives int |f(gamma)| |gamma'| <= M int |gamma'| = M L(gamma).
;;; =====================================================================
(sp (make-wff (string-append "forall([u, f, pgam, dgam, a, b], " jxl-H
  "is-road(pgam, dgam, a, b) implies trace(pgam, a, b) subset u implies
   forall([bnd in rr], forall([bny_ in trace(pgam, a, b)], magnitude(f(bny_)) <= bnd) implies
     magnitude(line-int(f, pgam, dgam, a, b)) <= road-length(dgam, a, b) * bnd))")))
(dk-peel!)
(jxl-road-facts! 'pgam 'dgam 'a 'b)
(jxl-set! 'a 'b)
(fact 'ccint-subset-rr 'a 'b)
(define jxl-lb-hyp (dk-pick (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'bnd))) "|f| <= bnd on the trace"))
(define jxl-lb-dom '(CCINT a b))
(define jxl-lb-fm '(VNB-LAMBDA rlt_ (CCINT a b) (magnitude (f (pgam rlt_)))))
(define jxl-lb-md (jxl-mag 'dgam 'a 'b))
(define jxl-lb-lb '(VNB-LAMBDA rlt_ (CCINT a b) (* (magnitude (f (pgam rlt_))) (magnitude (dgam rlt_)))))
(define jxl-lb-mm '(VNB-LAMBDA rlt_ (CCINT a b) (* bnd (magnitude (dgam rlt_)))))
;;; z in [a, b]: f(pgam z), dgam z, their magnitudes typed
(define (jxl-lb-pt! z)
  (jxl-in-u! 'pgam z 'a 'b)
  (fact 'fun-apply-type-c 'f 'u 'CC (list 'pgam z))
  (fact 'fun-apply-type-c 'dgam jxl-lb-dom 'CC z)
  (fact 'cc-magnitude-closed (list 'f (list 'pgam z)))
  (fact 'cc-magnitude-closed (list 'dgam z)))
(define (jxl-lb-type! lam body-type!)
  (dk-have! (list 'IN lam (list 'FUN jxl-lb-dom 'RR))
    (lambda ()
      (dk-lam-type!
       (lambda ()
         (let ((z (dk-di-var!)))
           (jxl-lb-pt! z)
           (body-type! z)
           (ass)))
       ass))))
(jxl-lb-type! jxl-lb-fm (lambda (z) #t))
(jxl-mag-type! 'dgam 'a 'b)
(jxl-lb-type! jxl-lb-lb (lambda (z) (fact 'rr-mul-in-rr (list 'magnitude (list 'f (list 'pgam z)))
                                           (list 'magnitude (list 'dgam z)))))
(jxl-lb-type! jxl-lb-mm (lambda (z) (fact 'rr-mul-in-rr 'bnd (list 'magnitude (list 'dgam z)))))
;; (54)
(define jxl-lb-54
  (dk-chain! (dk-cite! 'line-int-abs-bound 'u 'f 'pgam 'dgam 'a 'b jxl-lb-lb)
    (lambda (ante)
      (lambda ()
        (let ((z (dk-di-var!)))
          (dk-lam-b!)
          (dk-lane-if! qrfl))))))
;; the integrand of (54) is regulated, hence has a primitive
(dk-split-all! (list (dk-cite! 'continuous-on-compose-regulated 'u 'f 'pgam 'a 'b)))
(define jxl-lb-rf '(VNB-LAMBDA pat_ (CCINT a b) (real-part (f (pgam pat_)))))
(define jxl-lb-if '(VNB-LAMBDA pat_ (CCINT a b) (imag-part (f (pgam pat_)))))
(dk-chain! (dk-cite! 'regulated-on-magnitude jxl-lb-rf jxl-lb-if jxl-lb-fm 'a 'b)
  (lambda (ante)
    (lambda ()
      (let ((z (dk-di-var!)))
        (jxl-lb-pt! z)
        (dk-lam-b!)
        (jxl-mag-re-im! (list 'f (list 'pgam z)))))))
(dk-cite! 'road-length-regulated 'pgam 'dgam 'a 'b)
(dk-chain! (dk-cite! 'regulated-on-mul jxl-lb-fm jxl-lb-md jxl-lb-lb 'a 'b)
  (lambda (ante)
    (lambda ()
      (let ((z (dk-di-var!)))
        (dk-lam-b!)
        (dk-lane-if! qrfl)))))
(define jxl-lb-gl (dk-skolem! (dk-fact! 'regulated-on-has-primitive 'a 'b jxl-lb-lb)))
;; a primitive of bnd |dgam|, and its integral bnd * L
(define jxl-lb-g (jxl-len-prim! 'pgam 'dgam 'a 'b))
(fact 'primitive-in-fun jxl-lb-g jxl-lb-md 'a 'b)
(define jxl-lb-gh (list 'VNB-LAMBDA 'rlt_ jxl-lb-dom (list '* 'bnd (list jxl-lb-g 'rlt_))))
(dk-have! (list 'IN jxl-lb-gh (list 'FUN jxl-lb-dom 'RR))
  (lambda ()
    (dk-lam-type!
     (lambda ()
       (let ((z (dk-di-var!)))
         (fact 'fun-apply-type-c jxl-lb-g jxl-lb-dom 'RR z)
         (fact 'rr-mul-in-rr 'bnd (list jxl-lb-g z))
         (ass)))
     ass)))
(dk-split-all!
 (list (dk-chain! (dk-cite! 'pw-antiderivative-real-mul 'a 'b jxl-lb-g jxl-lb-md 'bnd jxl-lb-gh jxl-lb-mm)
         (lambda (ante)
           (lambda ()
             (let ((z (dk-di-var!)))
               (dk-lam-b!)
               (dk-lane-if! qrfl)))))))
;; monotonicity: |f(pgam)| |dgam| <= bnd |dgam| pointwise
(define jxl-lb-mono
  (dk-chain! (dk-cite! 'pw-int-monotone jxl-lb-gl jxl-lb-lb jxl-lb-gh jxl-lb-mm 'a 'b)
    (lambda (ante)
      (lambda ()
        (let ((z (dk-di-var!)))
          (jxl-lb-pt! z)
          (dk-cite! 'trace-value-in 'pgam 'a 'b z)
          (dk-apply! jxl-lb-hyp (list 'pgam z))
          (fact 'cc-magnitude-nonneg (list 'dgam z))
          (fact 'rr-mul-le-right (list 'magnitude (list 'f (list 'pgam z))) 'bnd (list 'magnitude (list 'dgam z)))
          (dk-lam-b!)
          (dk-lane-if! ass))))))
;; assemble
(define jxl-lb-pmd (list 'PW-INT jxl-lb-md 'a 'b))
(define jxl-lb-pmm (list 'PW-INT jxl-lb-mm 'a 'b))
(define jxl-lb-plb (list 'PW-INT jxl-lb-lb 'a 'b))
(fact 'pw-int-in-rr jxl-lb-g jxl-lb-md 'a 'b)
(fact 'pw-int-in-rr jxl-lb-gl jxl-lb-lb 'a 'b)
(fact 'pw-int-in-rr jxl-lb-gh jxl-lb-mm 'a 'b)
(fact 'line-int-in-cc 'u 'f 'pgam 'dgam 'a 'b)
(fact 'cc-magnitude-closed '(LINE-INT f pgam dgam a b))
(dk-have! (list 'AND (list 'IN jxl-lb-pmd 'RR) '(IN bnd RR)) (lambda () (dk-conj-close! (lambda () (ass)))))
(define jxl-lb-comm (dk-cite! 'rr-mul-comm jxl-lb-pmd 'bnd))
(mac 'ROAD-LENGTH)
(subst jxl-lb-comm)
(subst (list '= (list '* 'bnd jxl-lb-pmd) jxl-lb-pmm))
(dk-ineq! '(IN (magnitude (LINE-INT f pgam dgam a b)) RR) (list 'IN jxl-lb-plb 'RR) (list 'IN jxl-lb-pmm 'RR)
          (list '<= '(magnitude (LINE-INT f pgam dgam a b)) jxl-lb-plb) (list '<= jxl-lb-plb jxl-lb-pmm))
(qed 'line-int-length-bound)
(topic! 'line-int-length-bound 'analysis)
(alias! 'line-int-length-bound "the estimate (53): the integral is at most the length times a bound of |f|")

;;; =====================================================================
;;; (5e) LENGTH IS INVARIANT UNDER AN INCREASING AFFINE REPARAMETRISATION (the chain rule
;;; with |phi'| = l constant): the hypotheses of `road-affine-reparam' for the derivative.
;;; From `pw-int-affine-subst' with |l * dgam(m + l z)| = l |dgam(m + l z)|.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr, lrpc_ in rr, lrpd_ in rr, lrpl_ in rr, lrpm_ in rr], 0 < lrpl_ implies
   lrpm_ + lrpl_ * lrpc_ = a implies lrpm_ + lrpl_ * lrpd_ = b implies lrpc_ < lrpd_ implies
   forall([pgam, dgam, lrpk_], is-road(pgam, dgam, a, b) implies lrpk_ in fun(ccint(lrpc_, lrpd_), cc) implies
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpk_(lrpz_) == lrpl_ * dgam(lrpm_ + lrpl_ * lrpz_)) implies
     road-length(lrpk_, lrpc_, lrpd_) = road-length(dgam, a, b)))"))
(dk-peel!)
(jxl-road-facts! 'pgam 'dgam 'a 'b)
(define jxl-ra-ag (dk-pick (lambda (g) (and ((dk-head? 'FORALL) g) (dk-contains? g 'lrpk_) (dk-contains? g '==)))
                           "the derivative of the reparametrisation"))
(define jxl-ra-dom '(CCINT lrpc_ lrpd_))
(define jxl-ra-g (jxl-len-prim! 'pgam 'dgam 'a 'b))
(fact 'primitive-in-fun jxl-ra-g (jxl-mag 'dgam 'a 'b) 'a 'b)
(jxl-mag-type! 'dgam 'a 'b)
(jxl-mag-type! 'lrpk_ 'lrpc_ 'lrpd_)
(fact 'rr-subset-cc 'lrpl_)
(dk-have! '(<= 0 lrpl_) (lambda () (dk-ineq! '(IN lrpl_ RR) '(< 0 lrpl_))))
(fact 'rr-abs-of-nonneg 'lrpl_)
(fact 'rr-magnitude-is-abs 'lrpl_)
;;; z in [c, d]: w = m + l z in [a, b], typed
(define (jxl-ra-pt! z)
  (let ((w (list '+ 'lrpm_ (list '* 'lrpl_ z))))
    (dk-cite! 'affine-reparam-ccint-in 'a 'b 'lrpc_ 'lrpd_ 'lrpl_ 'lrpm_ z)
    (fact 'ccint-elt-in-rr 'a 'b w)
    w))
(define jxl-ra-gh (list 'VNB-LAMBDA 'rlt_ jxl-ra-dom (list jxl-ra-g '(+ lrpm_ (* lrpl_ rlt_)))))
(jxl-set! 'lrpc_ 'lrpd_)
(dk-have! (list 'IN jxl-ra-gh (list 'FUN jxl-ra-dom 'RR))
  (lambda ()
    (dk-lam-type!
     (lambda ()
       (let* ((z (dk-di-var!)) (w (jxl-ra-pt! z)))
         (fact 'fun-apply-type-c jxl-ra-g '(CCINT a b) 'RR w)
         (ass)))
     ass)))
(define jxl-ra-res
  (dk-chain! (dk-cite! 'pw-int-affine-subst 'a 'b 'lrpc_ 'lrpd_ 'lrpl_ 'lrpm_ jxl-ra-g (jxl-mag 'dgam 'a 'b)
                       jxl-ra-gh (jxl-mag 'lrpk_ 'lrpc_ 'lrpd_))
    (lambda (ante)
      (let ((deriv? (dk-contains? ante 'lrpk_)))
        (lambda ()
          (let* ((z (dk-di-var!)) (w (jxl-ra-pt! z)))
            (if (not deriv?)
                (begin (dk-lam-b!) (dk-lane-if! qrfl))
                (let ((dw (list 'dgam w)))
                  (fact 'fun-apply-type-c 'dgam '(CCINT a b) 'CC w)
                  (dk-apply! jxl-ra-ag z)
                  (dk-have! (list 'AND '(IN lrpl_ CC) (list 'IN dw 'CC)) (lambda () (dk-conj-close! (lambda () (ass)))))
                  (fact 'cc-magnitude-mul 'lrpl_ dw)
                  (dk-lam-b!)
                  (dk-lane-if! (lambda () (subst (list '= (list 'lrpk_ z) (list '* 'lrpl_ dw)))))
                  (dk-lane-if! (lambda () (subst (list '= (list 'magnitude (list '* 'lrpl_ dw))
                                                        (list '* '(magnitude lrpl_) (list 'magnitude dw))))))
                  (dk-lane-if! (lambda () (subst '(= (magnitude lrpl_) (ABS lrpl_)))))
                  (dk-lane-if! (lambda () (subst '(= (ABS lrpl_) lrpl_))))
                  (dk-lane-if! qrfl)))))))))
(dk-split-all! (list jxl-ra-res))
(mac 'ROAD-LENGTH)
(ass)
(qed 'road-length-affine-reparam)
(topic! 'road-length-affine-reparam 'analysis)

;;; the same with the goursat hypothesis: the convex hull of the vertices inside u
(sp (make-wff (string-append "forall([u, f], " jxl-H
  "forall([a in cc, b in cc, c in cc], conv3(a, b, c) subset u implies
     tri-int(f, a, b, c) = line-int(f, tri-road(a, b, c), tri-road-deriv(a, b, c), 0, 3)))")))
(dk-peel!)
(dk-split-all! (list (dk-cite! 'conv3-vertices-in 'a 'b 'c)))
(for-each (lambda (pq)
            (dk-cite! 'conv3-seg-trace 'a 'b 'c (car pq) (cadr pq))
            (fact 'subset-trans (list 'TRACE (list 'SEG-PATH (car pq) (cadr pq)) 0 1) '(CONV3 a b c) 'u))
          '((a b) (b c) (c a)))
(dk-cite! 'tri-int-is-line-int 'u 'f 'a 'b 'c)
(ass)
(qed 'tri-int-is-line-int-conv3)
(topic! 'tri-int-is-line-int-conv3 'analysis)
