;;; rake-asm-1.scm -- RAKE-ASM agent RA-1 (2026-10-12): elementary assumptions PROVEN.
;;;
;;; Each theorem below is stated LITERALLY as the axiom it replaces, under the same
;;; name; nothing here is asserted.  Helper prefix: ra1-.
;;;
;;;   semigroup-assoc                     projection of IS-SEMIGROUP / is-associative
;;;   normed-ag-nrm-{type,nonneg,definite,subadditive}
;;;                                       projections of IS-NORMED-AG / is-group-norm
;;;   injection-in-fun, injection-injective
;;;                                       projections of injection-membership-iff
;;;   injection-set-iff, bijection-set-iff
;;;                                       INJECTION / BIJECTION(X,Y) is a subclass of the
;;;                                       set FUN(X,Y) (fun-set-iff, subclass-of-set-is-set)
;;;   qq-is-commutative-ring, qq-is-integral-domain
;;;                                       zz-integral-domain.scm's driver over QQ-RING; QQ
;;;                                       has no zero divisors because it has inverses
;;;   rr-archimedean-floor (NEW helper)   r > 0, s >= 0 => some w in NN: w r - r <= s < w r
;;;   qq-dense-in-rr                      a = w r - K r with r = recip(n+1) < eps
;;;
;;;   zero-ring-is-ring, ring-prod-is-ring
;;;                                       IS-RING of the two tuples, once structure-library/
;;;                                       ring.scm wrote their NEG binder `p' (2026-10-12;
;;;                                       lam-t refused the old `(LIST p)')
;;;   ring-prod-n-is-ring(-ind)           RA-2's induction, moved here because it cites the
;;;                                       two above and rake-asm-1 loads after rake-asm-2
;;;
;;; LOAD WINDOW [rake-bolzano-weierstrass, end of load).  lo: rr-archimedean-multiple
;;; (theorem-library/rake-bolzano-weierstrass.scm) is the latest citation; the others
;;; are nn-least-element (through minimize!), nn-pos-is-succ, zz-ring-is-ring
;;; (qq-is-ring), nn-recip-succ-small, subset-lemmas, transport (surface-goal!), and
;;; number-systems / pos-rr / rr-order basics, field-ring-view (singleton-membership),
;;; all earlier.  hi: nothing in the tree cites any of the names proven here.

;;; ---- file-local helpers --------------------------------------------------------
(define (ra1-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; ra1: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "ra1: proof not complete" name)))
  (qed name))

(define (ra1-hyp head what) (dk-pick (dk-head? head) what))

;; the eigenvariable of the typing (IN v C) among LANDED whose class is C
(define (ra1-var-of landed cls)
  (let ((f (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) cls)))
                       landed)))
    (if f (cadr f) (error "ra1-var-of: no typing in" cls (map expression->string landed)))))

;;; =================================================================================
;;; semigroup-assoc: the is-associative conjunct of IS-SEMIGROUP, unfolded (alpha).
(sp (make-wff
  '(FORALL s
     (IMPLIES (IS-SEMIGROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((OPR s) ((OPR s) a b) c)
                ((OPR s) a ((OPR s) b c)))))))))))))
(di) (di)
(mac-h 'is-semigroup (ra1-hyp 'IS-SEMIGROUP "the IS-SEMIGROUP hypothesis"))
(dk-split-all!)
(mac-h 'is-associative (ra1-hyp 'is-associative "the is-associative conjunct"))
(ass)
(ra1-done! 'semigroup-assoc)
(topic! 'semigroup-assoc 'algebra)

;;; =================================================================================
;;; The four NORMED-AG norm laws: unfold IS-NORMED-AG, then its is-group-norm conjunct
;;; (operation-properties.scm), instantiate the pointwise universal at the peeled
;;; eigenvariables, split.
(define (ra1-nag-open!)
  (mac-h 'is-normed-ag (ra1-hyp 'IS-NORMED-AG "the IS-NORMED-AG hypothesis"))
  (dk-split-all!)
  (mac-h 'is-group-norm (ra1-hyp 'is-group-norm "the is-group-norm conjunct"))
  (dk-split-all!))

;; the pointwise clause (FORALL u (IMPLIES (IN u (CARR s)) ...)) of is-group-norm, at a
(define (ra1-nag-at! s a)
  (let* ((ptw (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                        (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                        (equal? (caddr (cadr (caddr f))) (list 'CARR s))
                                        (dk-contains? f '<=)))
                       "the pointwise is-group-norm clause"))
         (r   (dk-apply! ptw a)))
    (if (and (pair? r) (eq? (car r) 'AND)) (dk-split! r) (list r))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (IN (NRM s) (FUN (CARR s) RR))))))
(di) (di)
(ra1-nag-open!)
(ass)
(ra1-done! 'normed-ag-nrm-type)
(topic! 'normed-ag-nrm-type 'analysis)

(sp (make-wff
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (<= 0 ((NRM s) a))))))))
(let* ((landed (dk-peel!))
       (s (cadr (ra1-hyp 'IS-NORMED-AG "hyp")))
       (a (ra1-var-of landed (list 'CARR s))))
  (ra1-nag-open!)
  (ra1-nag-at! s a)
  (ass))
(ra1-done! 'normed-ag-nrm-nonneg)
(topic! 'normed-ag-nrm-nonneg 'analysis)

(sp (make-wff
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (IFF (= ((NRM s) a) 0) (= a (IDEN s)))))))))
(let* ((landed (dk-peel!))
       (s (cadr (ra1-hyp 'IS-NORMED-AG "hyp")))
       (a (ra1-var-of landed (list 'CARR s))))
  (ra1-nag-open!)
  (ra1-nag-at! s a)
  (dk-split-all!)
  (ass))
(ra1-done! 'normed-ag-nrm-definite)
(topic! 'normed-ag-nrm-definite 'analysis)

(sp (make-wff
  '(FORALL s (IMPLIES (IS-NORMED-AG s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (<= ((NRM s) ((OPR s) a b))
             (+ ((NRM s) a) ((NRM s) b)))))))))))
(let* ((landed (dk-peel!))
       (s  (cadr (ra1-hyp 'IS-NORMED-AG "hyp")))
       (vs (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                              (equal? (caddr f) (list 'CARR s))))
                             landed)))
       (a (car vs)) (b (cadr vs)))
  (ra1-nag-open!)
  (ra1-nag-at! s a)
  (dk-split-all!)
  (let ((sub (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                       (not (dk-contains? f 'IFF))
                                       (dk-contains? f a)))
                      "the subadditivity clause at a")))
    (dk-apply! sub b))
  (ass))
(ra1-done! 'normed-ag-nrm-subadditive)
(topic! 'normed-ag-nrm-subadditive 'analysis)

;;; =================================================================================
;;; injection-in-fun / injection-injective: the two conjuncts of the definitional
;;; injection-membership-iff.
(sp (make-wff
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (INJECTION X Y))
               (IN phi (FUN X Y))))))))
(dk-peel!)
(mac-h 'injection-membership-iff (ra1-hyp 'IN "the INJECTION membership"))
(dk-split-all!)
(ass)
(ra1-done! 'injection-in-fun)
(topic! 'injection-in-fun 'plumbing)

(sp (make-wff
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (INJECTION X Y))
               (FORALL a
                 (IMPLIES (IN a X)
                   (FORALL b
                     (IMPLIES (IN b X)
                       (IMPLIES (= (phi a) (phi b)) (= a b))))))))))))
(let* ((landed (dk-peel!))
       (mem (find-first (lambda (f) (and (dk-head-is? f 'IN) (dk-head-is? (caddr f) 'INJECTION)))
                        landed))
       (dom (cadr (caddr mem)))
       (vs (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) dom))) landed))))
  (mac-h 'injection-membership-iff mem)
  (dk-split-all!)
  (dk-apply! (dk-pick (dk-head? 'FORALL) "the injectivity clause") (car vs) (cadr vs))
  (ass))
(ra1-done! 'injection-injective)
(topic! 'injection-injective 'plumbing)

;;; =================================================================================
;;; injection-set-iff / bijection-set-iff: the class is included in FUN(X, Y), which is
;;; a set when X and Y are (fun-set-iff); subclass-of-set-is-set finishes.
(define (ra1-subclass-set! cls memb-iff)
  (dk-peel!)
  (dk-split-all!)
  (dk-have! '(IN (FUN X Y) SET)
    (lambda () (mac 'fun-set-iff) (dk-conj-close! (lambda () (ass)))))
  (dk-have! (list 'SUBSET cls '(FUN X Y))
    (lambda ()
      (mac 'subset-def)
      (let* ((landed (dk-peel!))
             (mem (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (equal? (caddr f) cls)))
                              landed)))
        (if (not mem) (error "ra1-subclass-set!: no membership landed"))
        (mac-h memb-iff mem)
        (dk-split-all!)
        (ass))))
  (fact 'subclass-of-set-is-set cls '(FUN X Y))
  (ass))

(sp (make-wff
  '(FORALL X (FORALL Y
      (IMPLIES (AND (IN X SET) (IN Y SET))
               (IN (INJECTION X Y) SET))))))
(ra1-subclass-set! '(INJECTION X Y) 'injection-membership-iff)
(ra1-done! 'injection-set-iff)
(topic! 'injection-set-iff 'plumbing)

(sp (make-wff
  '(FORALL X
     (FORALL Y
       (IMPLIES (AND (IN X SET) (IN Y SET))
                (IN (BIJECTION X Y) SET))))))
(ra1-subclass-set! '(BIJECTION X Y) 'bijection-membership-iff)
(ra1-done! 'bijection-set-iff)
(topic! 'bijection-set-iff 'plumbing)

;;; =================================================================================
;;; qq-is-commutative-ring / qq-is-integral-domain: zz-integral-domain.scm's driver.
(define (ra1-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))
(define (ra1-split-goals!)
  (let split ((fuel 20))
    (let ((andl (find-first
                 (lambda (s) (dk-head-is? (dk-goal-of s) 'AND))
                 (ra1-open))))
      (if andl
          (begin
            (if (= fuel 0) (error "ra1: AND split did not terminate"))
            (dk-focus! andl) (di) (split (- fuel 1)))))))

(sp (make-wff '(IS-COMMUTATIVE-RING QQ-RING)))
(mac 'is-commutative-ring-def)
(quietly (lambda () (surface-goal! 'QQ-RING)))
(ra1-split-goals!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (equal? (dk-goal) '(IS-RING QQ-RING))
       (begin (fact 'qq-is-ring) (ass))
       (let* ((landed (dk-peel!))
              (vs (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN))) landed))))
         (dk-have! (list 'AND (list 'IN (car vs) 'QQ) (list 'IN (cadr vs) 'QQ)))
         (fact 'qq-mul-comm (car vs) (cadr vs))
         (ass))))
 (ra1-open))
(ra1-done! 'qq-is-commutative-ring)
(topic! 'qq-is-commutative-ring 'algebra)

;; QQ has no zero divisors: a . b = 0, b /= 0  =>  a = a . (b . recip b) = (a . b) . recip b = 0.
(define (ra1-qq-nzd!)
  (let* ((landed (dk-peel!))
         (vs (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN))) landed)))
         (a (car vs)) (b (cadr vs))
         (ab (list '* a b)) (rb (list 'recip b)))
    (use-em (list '= b 0)
      (lambda () (oi-r) (ass))
      (lambda ()
        (oi-l)
        (dk-have! (list 'AND (list 'IN b 'QQ) (list 'NOT (list '= b 0))))
        (fact 'qq-recip-closed b)
        (fact 'qq-recip-inverse b)
        (dk-have! (list 'AND (list 'IN a 'QQ) (list 'AND (list 'IN b 'QQ) (list 'IN rb 'QQ))))
        (fact 'qq-mul-assoc a b rb)
        (dk-have! (list 'AND (list 'IN a 'QQ) (list 'IN b 'QQ)))
        (fact 'qq-mul-closed a b)
        (dk-have! (list 'AND (list 'IN ab 'QQ) (list 'IN rb 'QQ)))
        (fact 'qq-mul-closed ab rb)
        (dk-have! (list '= (list '* ab rb) a)
          (lambda ()
            (subst (list '= (list '* ab rb) (list '* a (list '* b rb))))
            (subst (list '= (list '* b rb) 1))
            (crs)))
        (subst (list '= a (list '* ab rb)))
        (subst (list '= ab 0))
        (crs)))))

(sp (make-wff '(IS-INTEGRAL-DOMAIN QQ-RING)))
(mac 'is-integral-domain-def)
(quietly (lambda () (surface-goal! 'QQ-RING)))
(ra1-split-goals!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (let ((g (dk-goal)))
     (cond ((equal? g '(IS-COMMUTATIVE-RING QQ-RING))
            (fact 'qq-is-commutative-ring) (ass))
           ((dk-head-is? g 'NOT) (arith))
           (#t (ra1-qq-nzd!)))))
 (ra1-open))
(ra1-done! 'qq-is-integral-domain)
(topic! 'qq-is-integral-domain 'algebra)

;;; =================================================================================
;;; rr-archimedean-floor (helper, proven here): for r > 0 and s >= 0 there is a natural
;;; w with  w r - r <= s < w r.  Let w be the LEAST natural with s < w r (minimize!;
;;; the archimedean property gives one).  If w = 0 the lower bound is -r <= s; if
;;; w = q + 1, q fails the guard, so q r <= s.
;;; Stated with its own binders r, s so that the minimize! guard names only them:
;;; a guard that names a counter-minted eigenvariable (a skolem witness) does not
;;; replay from the page -- see RAKE-ASM-1-REPORT.md, kit finding 2.

;; (IN t QQ) from (IN t NN)
(define (ra1-nn-qq! t)
  (if (not (dk-asm? (list 'IN t 'QQ)))
      (begin (dk-cite! 'nn-subset-zz t) (dk-cite! 'zz-subset-qq t))))
(define (ra1-and2! p q) (dk-have! (list 'AND p q)))
(define (ra1-rr-mul! u v)
  (if (not (dk-asm? (list 'IN (list '* u v) 'RR)))
      (begin (ra1-and2! (list 'IN u 'RR) (list 'IN v 'RR)) (dk-cite! 'rr-mul-closed u v))))
(define (ra1-qq-mul! u v)
  (if (not (dk-asm? (list 'IN (list '* u v) 'QQ)))
      (begin (ra1-and2! (list 'IN u 'QQ) (list 'IN v 'QQ)) (dk-cite! 'qq-mul-closed u v))))

(sp (make-wff
  '(FORALL r (IMPLIES (POS-RR r)
     (FORALL s (IMPLIES (IN s RR)
       (IMPLIES (<= 0 s)
         (FORSOME w (AND (IN w NN)
                         (AND (< s (* w r))
                              (<= (- (* w r) r) s)))))))))))
(define ra1-fl-landed (dk-peel!))
(define ra1-fr (cadr (find-first (dk-head? 'POS-RR) ra1-fl-landed)))
(define ra1-fs (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (eq? (caddr f) 'RR))) ra1-fl-landed)))
(dk-cite! 'rr-pos-rr-in-rr ra1-fr)
(dk-cite! 'rr-lt-of-pos-rr ra1-fr)
(define (ra1-guard v) (list 'AND (list 'IN v 'NN) (list '< ra1-fs (list '* v ra1-fr))))
(define ra1-s1 (list '+ ra1-fs 1))
(fact 'rr-one-in)
(ra1-and2! (list 'IN ra1-fs 'RR) '(IN 1 RR))
(dk-cite! 'rr-add-closed ra1-fs 1)
(define ra1-m0 (dk-skolem! (dk-fact! 'rr-archimedean-multiple ra1-fr ra1-s1)))
(dk-cite! 'nn-in-rr ra1-m0)
(ra1-rr-mul! ra1-m0 ra1-fr)
(dk-have! (list 'FORSOME 'rkv_ (ra1-guard 'rkv_))
  (lambda ()
    (ew ra1-m0)
    (dk-conj-close!
      (lambda ()
        (if (dk-head-is? (dk-goal) 'IN) (ass)
            (dk-ineq! (list '<= ra1-s1 (list '* ra1-m0 ra1-fr))))))))
(define ra1-mzres (minimize! '(rkv_) (ra1-guard 'rkv_) 'rkv_))
(define ra1-main (proof-state-focus *ps*))
(define ra1-w (car (car ra1-mzres)))
(if (cadr ra1-mzres)
    (begin (dk-focus! (cadr ra1-mzres)) (dk-peel!) (dk-split-all!) (ass)))
(if (caddr ra1-mzres) (error "ra1: minimize! posted NONEMPTY"))
(dk-focus! ra1-main)
(define ra1-gw (dk-pick (lambda (f) (equal? f (ra1-guard ra1-w))) "the guard at the minimiser"))
(define ra1-minf (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (dk-contains? f ra1-w))) "minimality"))
(dk-split! ra1-gw)
(dk-cite! 'nn-in-rr ra1-w)
(ra1-rr-mul! ra1-w ra1-fr)
(define ra1-wr (list '* ra1-w ra1-fr))
(define ra1-low (list '<= (list '- ra1-wr ra1-fr) ra1-fs))
(dk-have! ra1-low
  (lambda ()
    (use-em (list '= ra1-w 0)
      (lambda ()
        (dk-have! (list '= (list '* 0 ra1-fr) 0) (lambda () (crs)))
        (subst (list '= ra1-w 0))
        (dk-ineq! (list '= (list '* 0 ra1-fr) 0) (list '<= 0 ra1-fs) (list '< 0 ra1-fr)))
      (lambda ()
        (fact 'nn-zero-in)
        (dk-cite! 'nn-pos-of-nonzero ra1-w)
        (dk-cite! 'nn-lt-succ-le 0 ra1-w)
        (dk-have! (list '<= 1 ra1-w) (lambda () (dk-nn! (list '<= '(succ 0) ra1-w))))
        (let* ((q (dk-skolem! (dk-fact! 'nn-pos-is-succ ra1-w)))
               (qr (list '* q ra1-fr)))
          (dk-cite! 'nn-succ-plus-one q)
          (dk-cite! 'nn-in-rr q)
          (ra1-rr-mul! q ra1-fr)
          (dk-have! (list '= ra1-wr (list '+ qr ra1-fr))
            (lambda ()
              (subst (list '= ra1-w (list 'succ q)))
              (subst (list '= (list 'succ q) (list '+ q 1)))
              (crs)))
          (use-em (list '<= qr ra1-fs)
            (lambda ()
              (dk-ineq! (list '= ra1-wr (list '+ qr ra1-fr)) (list '<= qr ra1-fs)))
            (lambda ()
              (dk-cite! 'rr-not-le-lt qr ra1-fs)
              (ra1-and2! (list 'IN q 'NN) (list '< ra1-fs qr))
              (dk-apply! ra1-minf q)
              (let ((weq (dk-rewrite-h! (list '= ra1-w (list 'succ q)) (list 'succ q) (list '+ q 1))))
                (dk-ineq! weq (list '<= ra1-w q))))))))))
(ew ra1-w)
(dk-conj-close! (lambda () (ass)))
(ra1-done! 'rr-archimedean-floor)
(topic! 'rr-archimedean-floor 'inequalities)

;;; =================================================================================
;;; qq-dense-in-rr.  Take n with recip(n+1) < eps (nn-recip-succ-small) and name
;;; r = recip(n+1), a positive rational below eps.  Take K in NN with -x <= K r
;;; (rr-archimedean-multiple), put s = x + K r >= 0, and take w from
;;; rr-archimedean-floor: w r - r <= s < w r.  The rational a = w r - K r then
;;; satisfies 0 < a - x <= r < eps.
(sp (make-wff
  (forall-guarded '(eps x)
    (list '(POS-RR eps) '(IN x RR))
    (forsome-guarded 'a '(IN a QQ)
      (conjuncts->and
        (list '(< (- a eps) x)
              '(< x (+ a eps))))))))
(define ra1-landed (dk-peel!))
(define ra1-eps (cadr (find-first (dk-head? 'POS-RR) ra1-landed)))
(define ra1-x (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (eq? (caddr f) 'RR))) ra1-landed)))
(dk-cite! 'rr-pos-rr-in-rr ra1-eps)
(dk-cite! 'rr-lt-of-pos-rr ra1-eps)
;; 1. a positive rational r below eps: r = recip(n + 1)
(define ra1-n (dk-skolem! (dk-fact! 'nn-recip-succ-small ra1-eps)))
(define ra1-nn (list '+ ra1-n 1))
(fact 'nn-one-in)
(ra1-and2! (list 'IN ra1-n 'NN) '(IN 1 NN))
(dk-cite! 'nn-add-closed ra1-n 1)
(ra1-nn-qq! ra1-nn)
(dk-cite! 'qq-subset-rr ra1-nn)
(dk-have! (list 'NOT (list '= ra1-nn 0)) (lambda () (dk-nn!)))
(dk-have! (list '< 0 ra1-nn) (lambda () (dk-nn!)))
(ra1-and2! (list 'IN ra1-nn 'QQ) (list 'NOT (list '= ra1-nn 0)))
(dk-cite! 'qq-recip-closed ra1-nn)
(define ra1-t (list 'recip ra1-nn))
(dk-cite! 'qq-subset-rr ra1-t)
(dk-cite! 'rr-recip-pos ra1-nn)
(define ra1-r (dk-name! ra1-t))
(define ra1-req (list '= ra1-r ra1-t))
(dk-have! (list 'IN ra1-r 'QQ) (lambda () (subst ra1-req) (ass)))
(dk-have! (list '< 0 ra1-r) (lambda () (subst ra1-req) (ass)))
(dk-have! (list '< ra1-r ra1-eps) (lambda () (subst ra1-req) (ass)))
(dk-cite! 'rr-pos-rr-of-lt ra1-r)
;; 2. K in NN with -x <= K r, and s = x + K r >= 0
(dk-cite! 'rr-neg-closed ra1-x)
(define ra1-k (dk-skolem! (dk-fact! 'rr-archimedean-multiple ra1-r (list '- ra1-x))))
(dk-cite! 'nn-in-rr ra1-k)
(ra1-rr-mul! ra1-k ra1-r)
(define ra1-kr (list '* ra1-k ra1-r))
(define ra1-s (list '+ ra1-x ra1-kr))
(ra1-and2! (list 'IN ra1-x 'RR) (list 'IN ra1-kr 'RR))
(dk-cite! 'rr-add-closed ra1-x ra1-kr)
(dk-have! (list '<= 0 ra1-s) (lambda () (dk-ineq! (list '<= (list '- ra1-x) ra1-kr))))
;; 3. w with w r - r <= s < w r
(define ra1-fw
  (dk-skolem! (dk-fact! 'rr-archimedean-floor ra1-r ra1-s)))
(define ra1-wr2 (list '* ra1-fw ra1-r))
(dk-cite! 'nn-in-rr ra1-fw)
(ra1-rr-mul! ra1-fw ra1-r)
;; 4. the witness a = w r - K r
(define ra1-a (list '- ra1-wr2 ra1-kr))
(ra1-nn-qq! ra1-fw)
(ra1-nn-qq! ra1-k)
(ra1-qq-mul! ra1-fw ra1-r)
(ra1-qq-mul! ra1-k ra1-r)
(dk-have! (list 'IN ra1-a 'QQ)
  (lambda ()
    (mac 'binary-minus-def)
    (dk-cite! 'qq-neg-closed ra1-kr)
    (ra1-and2! (list 'IN ra1-wr2 'QQ) (list 'IN (list '- ra1-kr) 'QQ))
    (dk-cite! 'qq-add-closed ra1-wr2 (list '- ra1-kr))
    (ass)))
(ew ra1-a)
(dk-conj-close!
  (lambda ()
    (if (dk-head-is? (dk-goal) 'IN)
        (ass)
        (dk-ineq! (list '<= (list '- ra1-wr2 ra1-r) ra1-s) (list '< ra1-s ra1-wr2)
                  (list '< ra1-r ra1-eps) (list '< 0 ra1-eps)))))
(ra1-done! 'qq-dense-in-rr)
(topic! 'qq-dense-in-rr 'inequalities)

;;; =================================================================================
;;; zero-ring-is-ring / ring-prod-is-ring (spliced 2026-10-12, after the user's repair of
;;; the NEG slot binder in structure-library/ring.scm: `p', no longer `(LIST p)').
;;; Unfold IS-RING; read the six slots off the tuple; close each conjunct by its shape:
;;; the typings by lam-t and pointwise closure, the laws by unfolding the property,
;;; beta-reducing the slot lambdas (typing every argument first) and rewriting each
;;; component with the factor ring's law.  ZERO-RING's carrier is {0}, read through
;;; SINGLETON (singleton-membership); RING-PROD's elements are pairs (cartesian-nth,
;;; cartesian-pair-eq, pair-in-cartesian).

(define ra1-z '(MAKE-SET (LIST 0)))

;; land (IN 0 {0})
(define (ra1-zero-in-z!)
  (if (not (dk-asm? (list 'IN 0 ra1-z)))
      (begin
        (dk-have! '(IN 0 (SINGLETON 0))
          (lambda () (mac 'singleton-membership)
            (dk-conj-close! (lambda ()
              (if (dk-head-is? (dk-goal) 'IN)
                  (begin (fact 'nn-zero-in) (fact 'membership-implies-sethood 0 'NN) (ass))
                  (rfl))))))
        (fact 'singleton-unfold 0)
        (dk-rewrite-h! '(IN 0 (SINGLETON 0)) '(SINGLETON 0) ra1-z))))
;; land (= u 0) from (IN u {0})
(define (ra1-eq-zero! u)
  (fact 'singleton-unfold 0)
  (let ((m (dk-rewrite-h! (list 'IN u ra1-z) ra1-z '(SINGLETON 0))))
    (dk-have! (list '= u 0)
      (lambda ()
        (mac-h 'singleton-membership m)
        (dk-split-all!)
        (ass)))))
(define (ra1-z-set!)
  (dk-have! (list 'IN ra1-z 'SET)
    (lambda ()
      (fact 'nn-is-set)
      (dk-have! '(IN (LIST 0) (TUPLES NN)) (lambda () (ti) (fact 'nn-zero-in) (ass)))
      (dk-have! '(AND (IN (LIST 0) (TUPLES NN)) (IN NN SET)))
      (fact 'make-set-sethood 'NN '(LIST 0))
      (ass))))

(define (ra1-z-leaf!)
  (let ((g (dk-goal)))
    (cond
      ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'LENGTH)) (len-r) (arith))
      ((equal? g (list 'IN ra1-z 'SET)) (ra1-z-set!))
      ((equal? g (list 'IN 0 ra1-z)) (ra1-zero-in-z!) (ass))
      ((and (dk-head-is? g 'IN) (dk-head-is? (cadr g) 'VNB-LAMBDA))
       (ra1-z-set!)
       (for-each
        (lambda (l)
          (dk-focus! l)
          (let ((h (dk-goal)))
            (cond ((dk-head-is? h 'FORALL) (dk-peel!) (ra1-zero-in-z!) (ass))
                  ((equal? h (list 'IN ra1-z 'SET)) (ass))
                  (#t (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass)))))))
        (dk-opened (lambda () (lam-t)))))
      (#t
       (mac (car g))
       (let* ((landed (dk-peel!))
              (vs (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) ra1-z))) landed))))
         (ra1-zero-in-z!)
         (for-each ra1-eq-zero! vs)
         (dk-conj-close!
          (lambda ()
            (if (not (and (dk--redex? (dk-goal)) (dk-lam-b!)))
                (let ((h (dk-goal)))
                  (for-each (lambda (v) (if (dk-contains? h v) (subst (list '= v 0)))) vs)
                  (rfl))))))))))

(sp (make-wff '(IS-RING ZERO-RING)))
(mac 'IS-RING)
(mac 'zero-ring-def)
(for-each (lambda (acc) (slot acc)) '(CARR ADD MUL NEG ZERO ONE))
(let loop ((k 0)) (if (and (< k 10) (dk-contains? (dk-goal) 'NTH)) (begin (nth-r) (loop (+ k 1)))))
(ra1-split-goals!)
(for-each (lambda (l) (if (not (sequent-node-grounded? l)) (begin (dk-focus! l) (ra1-z-leaf!))))
          (ra1-open))
(ra1-done! 'zero-ring-is-ring)
(topic! 'zero-ring-is-ring 'algebra)

;;; SCRATCH (not for the library): IS-RING of RING-PROD with the NEG slot's binder
;;; written as a plain variable -- the repair proposed in the RA-1 report.
;; the two rings, read off the hypotheses after the peel
(define ra1p-x #f)
(define ra1p-y #f)
(define (ra1p-cx) (list 'CARR ra1p-x))
(define (ra1p-cy) (list 'CARR ra1p-y))
(define (ra1p-c) (list 'CARTESIAN (ra1p-cx) (ra1p-cy)))

;; type a term in its class, by its shape; lands (IN t cls)
(define (ra1p-ty! t cls)
  (cond
    ((dk-asm? (list 'IN t cls)) #t)
    ((and (dk-head-is? t 'LIST) (dk-head-is? cls 'CARTESIAN) (= (length t) 3) (= (length cls) 3))
     (ra1p-ty! (cadr t) (cadr cls))
     (ra1p-ty! (caddr t) (caddr cls))
     (dk-cite! 'pair-in-cartesian (cadr cls) (caddr cls) (cadr t) (caddr t)))
    ((dk-head-is? t 'NTH)
     (let ((u (caddr t)))
       (ra1p-ty! u (ra1p-c))
       (dk-split! (dk-cite! 'cartesian-nth u (ra1p-cx) (ra1p-cy)))))
    ((and (pair? t) (pair? (car t)))
     (let* ((op (car (car t))) (rg (cadr (car t))) (args (cdr t)) (cr (list 'CARR rg)))
       (for-each (lambda (a) (ra1p-ty! a cr)) args)
       (case op
         ((ADD) (dk-have! (list 'AND (list 'IS-RING rg)
                                (list 'AND (list 'IN (car args) cr) (list 'IN (cadr args) cr))))
                (dk-cite! 'ring-carrier-closed-add rg (car args) (cadr args)))
         ((MUL) (dk-cite! 'ring-carrier-closed-mul rg (car args) (cadr args)))
         ((NEG) (dk-cite! 'ring-neg-in-carr rg (car args)))
         (else (error "ra1p-ty!: no route for" (expression->string t))))))
    ((and (pair? t) (eq? (car t) 'ZERO)) (dk-cite! 'ring-zero-in (cadr t)))
    ((and (pair? t) (eq? (car t) 'ONE)) (dk-cite! 'ring-one-in (cadr t)))
    (#t (error "ra1p-ty!: no route for" (expression->string t) (expression->string cls))))
  (if (not (dk-asm? (list 'IN t cls)))
      (error "ra1p-ty!: typing did not land" (expression->string (list 'IN t cls)))))

(define (ra1p-c-set!)
  (dk-have! (list 'IN (ra1p-c) 'SET)
    (lambda ()
      (mac 'cartesian-set-iff)
      (dk-conj-close!
        (lambda () (dk-cite! 'ring-carr-in-set (cadr (cadr (dk-goal)))) (ass))))))

;; NTH of a literal list, reduced in the goal to a fixpoint
(define (ra1p-nth-lit? e)
  (cond ((not (pair? e)) #f)
        ((and (eq? (car e) 'NTH) (pair? (cdr e)) (pair? (cddr e)) (dk-head-is? (caddr e) 'LIST)) #t)
        (#t (or (ra1p-nth-lit? (car e)) (ra1p-nth-lit? (cdr e))))))
(define (ra1p-nth-norm!)
  (let loop ((k 0)) (if (and (< k 10) (ra1p-nth-lit? (dk-goal))) (begin (nth-r) (loop (+ k 1))))))

;; the redexes of a term: applications whose head is a VNB-LAMBDA
(define (ra1p-redexes e)
  (cond ((not (pair? e)) '())
        ((dk-head-is? (car e) 'VNB-LAMBDA) (cons e (append-map ra1p-redexes (cdr e))))
        (#t (append-map ra1p-redexes e))))
(define (ra1p-has-lambda? e) (dk-contains? e 'VNB-LAMBDA))

;; beta to a fixpoint: type every redex argument that is free of redexes, one lam-b
;; pass, type whatever argument typing it posted as an owed leaf, normalise NTHs.
(define (ra1p-beta!)
  (let loop ((k 0))
    (ra1p-nth-norm!)
    (let ((rs (ra1p-redexes (dk-goal))))
      (if (and (pair? rs) (< k 10))
          (let ((main (proof-state-focus *ps*)) (goal (dk-goal)))
            (for-each (lambda (r)
                        (for-each (lambda (a) (if (not (ra1p-has-lambda? a)) (ra1p-ty! a (ra1p-c))))
                                  (cdr r)))
                      rs)
            (let* ((opened (dk-opened (lambda () (lam-b))))
                   (owed (filter (lambda (l) (dk-head-is? (dk-goal-of l) 'IN)) opened))
                   (mains (filter (lambda (l) (not (dk-head-is? (dk-goal-of l) 'IN))) opened)))
              (for-each (lambda (l)
                          (if (not (sequent-node-grounded? l))
                              (begin (dk-focus! l)
                                     (ra1p-ty! (cadr (dk-goal)) (caddr (dk-goal)))
                                     (ass))))
                        owed)
              (cond ((pair? mains) (dk-focus! (car mains)))
                    ((not (sequent-node-grounded? main)) (dk-focus! main)))
              (loop (+ k 1))))))))

;; close (= L R): L a literal LIST, R a literal LIST or a variable of C.
;; EQS: the component equations (theorem instances) already in context.
(define (ra1p-here! closer)
  (let ((leaf (proof-state-focus *ps*)))
    (closer)
    (if (not (sequent-node-grounded? leaf))
        (error "ra1p-here!: leaf still open" (expression->string (dk-goal-of leaf))))))
(define (ra1p-close-eq! eqs)
  (let* ((origin (proof-state-focus *ps*)) (g (dk-goal)) (l (cadr g)) (r (caddr g)))
    (if (not (dk-head-is? g '=)) (error "ra1p-close-eq!: not an equation" (expression->string g)))
    (if (symbol? r)
        (let ((pr (list 'LIST (list 'NTH 1 r) (list 'NTH 2 r))))
          (ra1p-ty! pr (ra1p-c))
          (dk-cite! 'cartesian-pair-eq r (ra1p-cx) (ra1p-cy))
          (dk-have! (list '= l pr) (lambda () (ra1p-close-eq! eqs)))
          (dk-cite! 'eq-sym r pr)
          (dk-cite! 'eq-trans l pr r)
          (if (not (sequent-node-grounded? origin)) (ra1p-here! ass)))
        (begin
          (ra1p-ty! r (ra1p-c))
          (for-each (lambda (e)
                      (if (and (not (sequent-node-grounded? origin)) (dk-contains? (dk-goal) (cadr e)))
                          (subst e)))
                    eqs)
          (if (not (sequent-node-grounded? origin)) (ra1p-here! rfl))))))

;; one law: unfold, peel, type the variables' components, land the component
;; instances of the theorems THMS (each (name . arity)), beta, close.
(define (ra1p-law! thms)
  (mac (car (dk-goal)))
  (let* ((landed (dk-peel!))
         (vs (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) (ra1p-c)))) landed)))
         (eqs '()))
    (for-each (lambda (v) (ra1p-ty! (list 'NTH 1 v) (ra1p-cx)) (ra1p-ty! (list 'NTH 2 v) (ra1p-cy))) vs)
    (for-each
      (lambda (th)
        (for-each
          (lambda (k rg)
            (let* ((args (map (lambda (v) (list 'NTH k v)) (list-head vs (cdr th))))
                   (e (apply dk-cite! (car th) rg args)))
              (set! eqs (cons e eqs))))
          '(1 2) (list ra1p-x ra1p-y)))
      thms)
    (dk-conj-close!
      (lambda ()
        (ra1p-beta!)
        (ra1p-close-eq! eqs)))))

(sp (make-wff '(FORALL X (IMPLIES (IS-RING X)
      (FORALL Y (IMPLIES (IS-RING Y)
        (IS-RING (RING-PROD X Y))))))))
(dk-peel!)
(set! ra1p-x (cadr (cadr (dk-goal))))
(set! ra1p-y (caddr (cadr (dk-goal))))
(define ra1p-p (list 'RING-PROD ra1p-x ra1p-y))
(define ra1p-body
  (subst-free* (list (cons 'x ra1p-x) (cons 'y ra1p-y))
   '(LIST
     (CARTESIAN (CARR X) (CARR Y))
     (VNB-LAMBDA (LIST p q) (CARTESIAN (CARTESIAN (CARR X) (CARR Y)) (CARTESIAN (CARR X) (CARR Y)))
       (LIST ((ADD X) (NTH 1 p) (NTH 1 q))
             ((ADD Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA (LIST p q) (CARTESIAN (CARTESIAN (CARR X) (CARR Y)) (CARTESIAN (CARR X) (CARR Y)))
       (LIST ((MUL X) (NTH 1 p) (NTH 1 q))
             ((MUL Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA p (CARTESIAN (CARR X) (CARR Y))       ; the REPAIRED binder
       (LIST ((NEG X) (NTH 1 p))
             ((NEG Y) (NTH 2 p))))
     (LIST (ZERO X) (ZERO Y))
     (LIST (ONE X) (ONE Y)))))
(mac 'IS-RING)
(for-each
  (lambda (acc val)
    (let ((eq (list '== (list acc ra1p-p) val)))
      (dk-have! eq (lambda () (mac 'RING-PROD)
                         (let loop ((k 0))
                           (if (and (< k 6) (not (alpha-equiv? (cadr (dk-goal)) (caddr (dk-goal)))))
                               (begin (slot acc) (ra1p-nth-norm!) (loop (+ k 1)))))
                         (qrfl)))
      (subst eq)))
  '(CARR ADD MUL NEG ZERO ONE) (cdr ra1p-body))
(ra1-split-goals!)
(for-each
  (lambda (l)
    (if (not (sequent-node-grounded? l))
        (begin
          (dk-focus! l)
          (let ((g (dk-goal)))
            (cond
              ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'LENGTH)) (mac 'RING-PROD) (len-r) (arith))
              ((equal? g (list 'IN (ra1p-c) 'SET)) (ra1p-c-set!))
              ((and (dk-head-is? g 'IN) (dk-head-is? (cadr g) 'VNB-LAMBDA))
               (ra1p-c-set!)
               (for-each
                 (lambda (lf)
                   (dk-focus! lf)
                   (let ((h (dk-goal)))
                     (cond ((dk-head-is? h 'FORALL)
                            (dk-peel!) (ra1p-ty! (cadr (dk-goal)) (caddr (dk-goal))) (ass))
                           ((equal? h (list 'IN (ra1p-c) 'SET)) (ass))
                           (#t (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass)))))))
                 (dk-opened (lambda () (lam-t)))))
              ((dk-head-is? g 'IN) (ra1p-ty! (cadr g) (caddr g)) (ass))
              ((dk-head-is? g 'is-associative)
               (ra1p-law! (if (dk-contains? g 'ADD) '((ring-add-assoc . 3)) '((ring-mul-assoc . 3)))))
              ((dk-head-is? g 'is-commutative) (ra1p-law! '((ring-add-comm . 2))))
              ((dk-head-is? g 'is-identity)
               (ra1p-law! (if (dk-contains? g 'ADD)
                              '((ring-add-left-id . 1) (ring-add-right-id . 1))
                              '((ring-mul-left-id . 1) (ring-mul-right-id . 1)))))
              ((dk-head-is? g 'has-inverses) (ra1p-law! '((ring-add-left-inv . 1) (ring-add-right-inv . 1))))
              ((dk-head-is? g 'is-distributive) (ra1p-law! '((ring-left-dist . 3) (ring-right-dist . 3))))
              (#t (error "ra1p: unexpected conjunct" (expression->string g))))))))
  (ra1-open))
(ra1-done! 'ring-prod-is-ring)
(topic! 'ring-prod-is-ring 'algebra)

;; the three parts of use-induction's answer (RA-2's ra2-ind!, renamed)
(define (ra1-ind!)
  (let ((br (use-induction)))
    (list (cdr (assq 'base br)) (cdr (assq 'step br))
          (cdr (assq 'ih br)) (cdr (assq 'var br)))))

;;; =====================================================================
;;; ring-prod-n-is-ring, through ring-prod-n-is-ring-ind (n outermost).
;;; RA-2's proof, moved here: it cites zero-ring-is-ring and ring-prod-is-ring.
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL f
      (IMPLIES (FORALL i (IMPLIES (IN i NN) (IS-RING (f i))))
        (IS-RING (RING-PROD-N f n))))))))
(let* ((br (ra1-ind!)) (base (car br)) (step (cadr br)) (ih (caddr br)) (v (cadddr br)))
  (dk-focus! base)
  (dk-peel!)
  (fact 'ring-prod-n-zero 'f)
  (subst '(== (RING-PROD-N f 0) ZERO-RING))
  (fact 'zero-ring-is-ring)
  (ass)
  (dk-focus! step)
  (let* ((hyp (car (dk-peel!)))
         (pn (list 'RING-PROD-N 'f v)) (fv (list 'f v)))
    (fact 'ring-prod-n-succ 'f v)
    (subst (list '== (list 'RING-PROD-N 'f (list 'succ v)) (list 'RING-PROD pn fv)))
    (dk-apply! ih 'f)
    (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                         (equal? (caddr (caddr h)) (list 'IS-RING (list 'f (cadr h))))))
                        "the ring hypothesis")
               v)
    (fact 'ring-prod-is-ring pn fv)
    (ass)))
(ra1-done! 'ring-prod-n-is-ring-ind)
(topic! 'ring-prod-n-is-ring-ind 'algebra)

(sp (make-wff
 '(FORALL f
      (FORALL n (IMPLIES (IN n NN)
        (IMPLIES (FORALL i (IMPLIES (IN i NN) (IS-RING (f i))))
          (IS-RING (RING-PROD-N f n))))))))
(dk-peel!)
(fact 'ring-prod-n-is-ring-ind 'n 'f)
(ass)
(ra1-done! 'ring-prod-n-is-ring)
(topic! 'ring-prod-n-is-ring 'algebra)

(display ";; ra1 qed failures: ") (write *vnb-qed-failures*) (newline)
