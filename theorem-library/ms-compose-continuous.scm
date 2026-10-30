;;; compose.scm -- COMPOSITION OF CONTINUOUS MAPS BETWEEN METRIC SPACES, the global form.  Agent KIT-8, 2026-10-26.
;;; Destination: theorem-library/ (library analysis), right after the file proving ms-compose-continuous-at
;;; (theorem-library/ms-continuity-algebra.scm).  The POINTWISE theorems already exist and are NOT restated:
;;;   ms-compose-continuous-at : f cont. at a, g cont. at f(a)  =>  z |-> g(f z) cont. at a  (lambda over PTS(s))
;;;   ms-compose-continuous-on : the same with the lambda's domain written D, PTS(s) == D
;;; New here: the IS-CONTINUOUS forms.  Helper prefix kc-.

(define (kc-and! . fs)
  (let ((c (let loop ((fs fs)) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(loop (cdr fs)))))))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!))))))
    c))
;; IS-CONTINUOUS(S, T, F) in context: return its pointwise universal
(define (kc-univ! s t f)
  (dk-project! `(FORALL a (IMPLIES (IN a (PTS ,s)) (IS-CONTINUOUS-AT ,s ,t ,f a))) 'is-continuous `(IS-CONTINUOUS ,s ,t ,f)))
;; the global statement, the lambda over DOM (PTS s itself, or a D with PTS(s) == D)
(define (kc-prove! name dom-eq?)
  (sp (make-wff
        (if dom-eq?
            '(FORALL s (FORALL dd (IMPLIES (== (PTS s) dd) (FORALL tm (FORALL u (FORALL f (FORALL g
               (IMPLIES (IS-CONTINUOUS s tm f) (IMPLIES (IS-CONTINUOUS tm u g)
                 (IS-CONTINUOUS s u (VNB-LAMBDA msz_ dd (g (f msz_)))))))))))))
            '(FORALL s (FORALL tm (FORALL u (FORALL f (FORALL g
               (IMPLIES (IS-CONTINUOUS s tm f) (IMPLIES (IS-CONTINUOUS tm u g)
                 (IS-CONTINUOUS s u (VNB-LAMBDA msz_ (PTS s) (g (f msz_))))))))))))))
  (dk-peel!)
  (let* ((uf (kc-univ! 's 'tm 'f)) (ug (kc-univ! 'tm 'u 'g)))
    (dk-project! '(IS-METRIC-SPACE s) 'is-continuous '(IS-CONTINUOUS s tm f))
    (dk-project! '(IS-METRIC-SPACE u) 'is-continuous '(IS-CONTINUOUS tm u g))
    (dk-project! '(IN f (FUN (PTS s) (PTS tm))) 'is-continuous '(IS-CONTINUOUS s tm f))
    (dk-project! '(IN g (FUN (PTS tm) (PTS u))) 'is-continuous '(IS-CONTINUOUS tm u g))
    (dk-cite! 'ms-pts-is-set 's)
    (mac 'IS-CONTINUOUS)
    (if dom-eq? (subst '(== dd (PTS s))))
    (dk-conj-close!
      (lambda ()
        (cond
          ((dk-asm? (dk-goal)) (dk-ass!))
          ((dk-head-is? (dk-goal) 'IN)
           (for-each (lambda (l)
                       (dk-focus! l)
                       (if (dk-head-is? (dk-goal) 'FORALL)
                           (let* ((landed (dk-landed (lambda () (dk-peel!))))
                                  (x (cadr (find-first (lambda (h) (dk-head-is? h 'IN)) landed))))
                             (kc-and! '(IN f (FUN (PTS s) (PTS tm))) `(IN ,x (PTS s)))
                             (dk-cite! 'fun-apply-type 'f '(PTS s) '(PTS tm) x)
                             (kc-and! '(IN g (FUN (PTS tm) (PTS u))) `(IN (f ,x) (PTS tm)))
                             (dk-cite! 'fun-apply-type 'g '(PTS tm) '(PTS u) `(f ,x))
                             (dk-ass!))
                           (dk-ass!)))
                     (dk-opened (lambda () (lam-t)))))
          (#t
           (let* ((landed (dk-landed (lambda () (dk-peel!))))
                  (x (cadr (find-first (lambda (h) (dk-head-is? h 'IN)) landed))))
             (dk-apply! uf x)
             (kc-and! '(IN f (FUN (PTS s) (PTS tm))) `(IN ,x (PTS s)))
             (dk-cite! 'fun-apply-type 'f '(PTS s) '(PTS tm) x)
             (dk-apply! ug `(f ,x))
             (dk-cite! 'ms-compose-continuous-at 's 'tm 'u 'f 'g x)
             (dk-ass!)))))))
  (qed name))

(kc-prove! 'ms-compose-continuous #f)
(kc-prove! 'ms-compose-continuous-dom #t)
