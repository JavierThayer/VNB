;;; isom2-dense.scm -- calculus.pdf Remark 3.32 and Lemma 3.36 in full: the pointwise
;;; limit of an equicontinuous sequence is continuous, and an equicontinuous sequence into
;;; a COMPLETE space that converges on a dense sequence converges everywhere to a
;;; continuous limit.  Agent ISOM, 2026-10-26.
;;;
;;;   equicont-ptwise-limit-continuous      (Remark 3.32, for a sequence)
;;;     fam equicontinuous from s to t, fam -> g pointwise  ==>  g continuous
;;;   equicont-dense-limit-continuous       (Lemma 3.36)
;;;     t complete, fam equicontinuous, dq dense in s, fam(k)(dq(m)) convergent for
;;;     every m  ==>  some g with fam -> g pointwise and g continuous from s to t
;;;
;;; The notes assume X compact; the proof does not use it, and the statement is made
;;; without it.  The limit's continuity: for b within delta/2 of a and k past the
;;; thresholds at a and b, d(g a, g b) <= d(g a, f_k a) + d(f_k a, f_k b) + d(f_k b, g b).
;;;
;;; WINDOW.  Citations: isom-dense.scm (equicont-dense-ptwise-limit, ptwise-limit-function),
;;; the vocabulary isom-vocab.scm, is-continuous, is-continuous-at, metric laws.
;;; lo = after isom-dense.scm; hi = none.  Library: analysis.
;;;
;;; Helper prefix: idc-.

(define (idc-head g) (and (pair? g) (car g)))
(define (idc-iff-rhs! iff)
  (let ((rhs (caddr iff)))
    (dk-have! rhs (lambda () (prop)))
    (if (eq? (idc-head rhs) 'AND) (dk-split-all! (list rhs)))
    rhs))
(define (idc-and! a b)
  (let ((f (list 'AND a b)))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! (lambda () (ass))))))
    f))
(define (idc-dt a b) (list '(DIST t) a b))
(define (idc-ds a b) (list '(DIST s) a b))
(define (idc-real! a b)
  (let ((r (list 'IN (idc-dt a b) 'RR)))
    (if (not (dk-asm? r)) (fact 'metric-dist-real 't a b))
    r))
(define (idc-pt! f x)
  (if (not (dk-asm? (list 'IN (list f x) '(PTS t)))) (fact 'fun-apply-type-c f '(PTS s) '(PTS t) x))
  (list f x))

(sp (make-wff '(FORALL s (FORALL t (FORALL fam (FORALL g
     (IMPLIES (IS-EQUICONTINUOUS s t fam)
       (IMPLIES (CONVERGES-PTWISE-TO s t fam g)
         (IS-CONTINUOUS s t g)))))))))
(dk-peel!)
(idc-iff-rhs! (dk-cite! 'is-equicontinuous 's 't 'fam))
(idc-iff-rhs! (dk-cite! 'converges-ptwise-to 's 't 'fam 'g))
(define idc-E (dk-pick (lambda (h) (and (eq? (idc-head h) 'FORALL) (dk-contains? h 'del))) "equicontinuity"))
(define idc-P (dk-pick (lambda (h) (and (eq? (idc-head h) 'FORALL) (dk-contains? h 'POS-RR) (dk-contains? h 'g)))
                       "the pointwise clause"))
(define (idc-thr! x e)
  (let* ((n (dk-skolem! (dk-apply! idc-P x e)))
         (cl (dk-pick (lambda (h) (and (eq? (idc-head h) 'FORALL) (dk-contains? h n))) "the threshold clause")))
    (cons n cl)))
(mac 'is-continuous)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (idc-head (dk-goal)) 'FORALL))
       (ass)
       (let ((a (dk-di-var!)))
         (mac 'is-continuous-at)
         (dk-conj-close!
          (lambda ()
            (if (not (eq? (idc-head (dk-goal)) 'FORALL))
                (ass)
                (let* ((pe (dk-peel!))
                       (eps (cadr (car (filter (lambda (f) (eq? (idc-head f) 'POS-RR)) pe))))
                       (h1 (dk-halve! eps))
                       (c (dk-halve! h1))
                       (del (dk-skolem! (dk-apply! idc-E a c)))
                       (ecl (dk-pick (lambda (h) (and (eq? (idc-head h) 'FORALL) (dk-contains? h del))) "the delta clause"))
                       (dh (dk-halve! del)))
                  (ew dh)
                  (dk-conj-close!
                   (lambda ()
                     (if (not (eq? (idc-head (dk-goal)) 'FORALL))
                         (ass)
                         (let* ((pb (dk-peel!))
                                (b (cadr (car (filter (lambda (f) (eq? (idc-head f) 'IN)) pb))))
                                (t1 (idc-thr! a c)) (t2 (idc-thr! b c))
                                (n1 (car t1)) (n2 (car t2))
                                (k (list '+ n1 n2)))
                           (idc-and! (list 'IN n1 'NN) (list 'IN n2 'NN))
                           (fact 'nn-add-closed n1 n2)
                           (dk-have! (list '<= n1 k) (lambda () (dk-nn!)))
                           (dk-have! (list '<= n2 k) (lambda () (dk-nn!)))
                           (fact 'metric-dist-real 's a b)
                           (fact 'rr-pos-rr-in-rr dh)
                           (fact 'rr-pos-rr-in-rr del)
                           (dk-have! (list '< (idc-ds a b) del)
                             (lambda () (dk-ineq! (list '<= (idc-ds a b) dh) (list '= (list '+ dh dh) del)
                                                  (list '< 0 dh) (list 'IN (idc-ds a b) 'RR)
                                                  (list 'IN dh 'RR) (list 'IN del 'RR))))
                           (let* ((F (list 'fam k)))
                             (fact 'fun-apply-type-c 'fam 'NN '(FUN (PTS s) (PTS t)) k)
                             (let ((Fa (idc-pt! F a)) (Fb (idc-pt! F b)) (ga (idc-pt! 'g a)) (gb (idc-pt! 'g b)))
                               (dk-apply! (cdr t1) k)
                               (dk-apply! (cdr t2) k)
                               (dk-apply! ecl k b)
                               (fact 'metric-triangle 't ga Fa gb)
                               (fact 'metric-triangle 't Fa Fb gb)
                               (fact 'metric-sym 't ga Fa)
                               (fact 'rr-pos-rr-in-rr c)
                               (fact 'rr-pos-rr-in-rr h1)
                               (fact 'rr-pos-rr-in-rr eps)
                               (fact 'rr-lt-of-pos-rr c)
                               (apply dk-ineq!
                                      (list (list '<= (idc-dt ga gb) (list '+ (idc-dt ga Fa) (idc-dt Fa gb)))
                                            (list '<= (idc-dt Fa gb) (list '+ (idc-dt Fa Fb) (idc-dt Fb gb)))
                                            (list '= (idc-dt ga Fa) (idc-dt Fa ga))
                                            (list '<= (idc-dt Fa ga) c) (list '<= (idc-dt Fb gb) c)
                                            (list '< (idc-dt Fa Fb) c)
                                            (list '= (list '+ c c) h1) (list '= (list '+ h1 h1) eps)
                                            (idc-real! ga gb) (idc-real! ga Fa) (idc-real! Fa gb)
                                            (idc-real! Fa Fb) (idc-real! Fb gb) (idc-real! Fa ga)
                                            (list '< 0 c)
                                            (list 'IN c 'RR) (list 'IN h1 'RR) (list 'IN eps 'RR)))))))))))))))))
(qed 'equicont-ptwise-limit-continuous)
(topic! 'equicont-ptwise-limit-continuous 'analysis)
(alias! 'equicont-ptwise-limit-continuous "the pointwise limit of an equicontinuous sequence is continuous")

(sp (make-wff '(FORALL s (FORALL t (FORALL fam (FORALL dq
     (IMPLIES (IS-COMPLETE t)
       (IMPLIES (IS-EQUICONTINUOUS s t fam)
         (IMPLIES (IS-DENSE-SEQ s dq)
           (IMPLIES (FORALL m (IMPLIES (IN m NN)
                      (FORSOME y (AND (IN y (PTS t))
                        (CONVERGES-TO t (VNB-LAMBDA k NN ((fam k) (dq m))) y)))))
             (FORSOME g (AND (CONVERGES-PTWISE-TO s t fam g) (IS-CONTINUOUS s t g)))))))))))))
(dk-peel!)
(idc-iff-rhs! (dk-cite! 'is-equicontinuous 's 't 'fam))
(dk-project! '(IS-METRIC-SPACE t) 'is-complete '(IS-COMPLETE t))
(fact 'equicont-dense-ptwise-limit 's 't 'fam 'dq)
(define idc-g (dk-skolem! (dk-cite! 'ptwise-limit-function 's 't 'fam)))
(fact 'equicont-ptwise-limit-continuous 's 't 'fam idc-g)
(ew idc-g)
(dk-conj-close! (lambda () (ass)))
(qed 'equicont-dense-limit-continuous)
(topic! 'equicont-dense-limit-continuous 'analysis)
(alias! 'equicont-dense-limit-continuous
        "an equicontinuous sequence into a complete space convergent on a dense sequence has a continuous pointwise limit")
