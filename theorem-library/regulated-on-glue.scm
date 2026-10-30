;;; regulated-on-glue.scm -- lemmas MOVED 2026-10-30 (wave-2 integration) out of theorem-library/road-juxtaposition-laws.scm
;;; into library analysis, for the library gate: cited by calint-regulated-step (analysis); pure real analysis.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   left-limit-within-local regulated-on-glue right-limit-within-local

;;; ---- helper defines copied from road-juxtaposition-laws.scm ----
(define (jxl-head g) (and (pair? g) (car g)))
(define (jxl-op? t op n) (and (pair? t) (eq? (car t) op) (= (length t) n)))
(define (jxl-close-by! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))
(define (jxl-in-ccint! z lo hi prems)
  (let ((f (list 'IN z (list 'CCINT lo hi))))
    (if (not (dk-asm? f))
        (dk-have! f (lambda () (mac 'ccint-membership) (jxl-close-by! prems))))
    f))
(define (jxl-cc-parts! z lo hi)
  (if (not (and (dk-asm? (list 'IN z 'RR)) (dk-asm? (list '<= lo z)) (dk-asm? (list '<= z hi))))
      (dk-split-all! (list (dk-cite! 'ccint-parts lo hi z)))))
(define (jxl-not-le->lt! z b)
  (let ((f (list '< b z)))
    (if (not (dk-asm? f)) (dk-cite! 'rr-not-le-lt z b))
    f))
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
(define jxl-ab '(CCINT a b))
(define jxl-ac '(CCINT a c))
(define jxl-cb '(CCINT c b))

;;; ---- the moved proofs ----
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

