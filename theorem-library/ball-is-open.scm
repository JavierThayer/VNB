;;; ball-is-open.scm -- an open ball is an open set.
;;;
;;;     ball-is-open:
;;;       forall s.  IS-METRIC-SPACE s  =>  forall x in PTS s.  forall r.
;;;         r in RR and 0 <= r and not (0 = r)  =>  IS-OPEN s (BALL s x r)
;;;
;;; Statement UNCHANGED from the support it retires
;;; (structure-library/metric-open-sets.scm:80, warranted `proof').  It is the
;;; one leaf left in the bill of ptwise-cauchy-compact-equicont-unif
;;; (theorem-library/ptwise-cauchy-unif.scm), which builds an open cover out
;;; of equicontinuity balls.
;;;
;;; THE PROOF is the warrant's own sentence.  IS-OPEN unfolds to: s is a metric
;;; space, the ball is a subset of PTS s, and every point y of it has a ball
;;; BALL(s, y, t) inside it.  Take t = r - d(x,y), positive because d(x,y) < r
;;; (rr-lt-diff-pos, rr-pos-rr-of-lt).  A point z of BALL(s, y, t) has
;;; d(x,z) <= d(x,y) + d(y,z) < d(x,y) + t = r (metric-triangle, one `ineq'
;;; certificate), so z is in BALL(s, x, r).  Ball memberships are opened and
;;; closed through the PROVEN unfold equation ball-sep-unfold
;;; (ball-cover-lemmas.scm) and the SEP rules, not through ball-membership.
;;;
;;; CITATIONS and load positions (0-based over prover-load, 2026-09-15):
;;;   subset-def (library.scm, primitive); rr-sub-in-rr (binary-minus-laws,
;;;   162); rr-lt-diff-pos (rr-order-basics, 172); rr-pos-rr-of-lt
;;;   (pos-rr-of-lt, 179); metric-dist-real (op-typing, 194, PROVEN there);
;;;   ball-sep-unfold (ball-cover-lemmas, 231); metric-triangle
;;;   (structure-library/metric-laws, 239).
;;;
;;; LOAD WINDOW [metric-laws + 1, ptwise-cauchy-unif): lo is forced by
;;; metric-triangle (239), the latest citation; hi by the first citer,
;;; theorem-library/ptwise-cauchy-unif.scm (the only citer in the tree besides
;;; pss-topics, which loads far below).
;;;
;;; Helper prefix: bio-.

(define bio-stmt
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL r (IMPLIES (AND (IN r RR) (AND (<= 0 r) (NOT (= 0 r))))
         (IS-OPEN s (BALL s x r)))))))))

(define (bio-head? f h) (and (pair? f) (eq? (car f) h)))

;; 1-based context index of FORM, for `ineq'.
(define (bio-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "bio-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))

;; run THUNK (a branching tactic) and visit each opened leaf with VISIT.
(define (bio-each-leaf! thunk visit)
  (for-each (lambda (leaf) (dk-focus! leaf) (visit))
            (dk-opened thunk)))

;; (IN z (BALL s c r)) in context: land its SEP atoms (IN z (PTS s)),
;; (<= d r), (NOT (= d r)).
(define (bio-open-ball-h! mem)
  (let ((sm (dk-landed-1 (lambda () (mac-h 'ball-sep-unfold mem)))))
    (dk-split-all! (dk-landed (lambda () (sep-me sm))))))

(define (bio-dist a b) `((DIST s) ,a ,b))

;; goal (SUBSET (BALL s y t) (BALL s x r)), with t = r - d(x,y)
(define (bio-inner-ball-inside! y t)
  (let* ((z (subset-by-element!))                   ; (IN z (BALL s y t))
         (dxy (bio-dist 'x y)) (dyz (bio-dist y z)) (dxz (bio-dist 'x z)))
    (bio-open-ball-h! `(IN ,z (BALL s ,y ,t)))
    (have! `(< ,dyz ,t) (lambda () (mac '<) (from-context!)))
    (fact 'metric-dist-real 's y z)
    (fact 'metric-dist-real 's 'x z)
    (let ((tri (dk-fact! 'metric-triangle 's 'x y z)))  ; d(x,z) <= d(x,y) + d(y,z)
      (have! `(< ,dxz r)
        (lambda () (ineq (bio-idx tri) (bio-idx `(< ,dyz ,t)))))
      (let ((lt (dk-landed-1 (lambda () (mac-h '< `(< ,dxz r))))))
        (dk-split! lt))                              ; (<= d r), (NOT (= d r))
      (mac 'ball-sep-unfold)
      (bio-each-leaf! (lambda () (sep-mi))
                      (lambda () (dk-conj-close!))))))

;; goal: forall y in BALL(s,x,r). forsome t. POS-RR t and BALL(s,y,t) subset BALL(s,x,r)
(define (bio-interior!)
  (let* ((mem (car (dk-peel!)))                    ; (IN y (BALL s x r))
         (y   (cadr mem))
         (dxy (bio-dist 'x y))
         (t   `(- r ,dxy)))
    (bio-open-ball-h! mem)
    (fact 'metric-dist-real 's 'x y)
    (have! `(< ,dxy r) (lambda () (mac '<) (from-context!)))
    (dk-fact! 'rr-lt-diff-pos dxy 'r)               ; 0 < r - d(x,y)
    (fact 'rr-sub-in-rr 'r dxy)
    (dk-fact! 'rr-pos-rr-of-lt t)                   ; POS-RR t
    (ew t)
    (bio-each-leaf! (lambda () (di))
                    (lambda ()
                      (if (bio-head? (dk-goal) 'POS-RR)
                          (ass)
                          (bio-inner-ball-inside! y t))))))

(sp (make-wff bio-stmt))
(dk-split-all! (dk-peel!))
(mac 'is-open)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((bio-head? g 'IS-METRIC-SPACE) (ass))
           ((bio-head? g 'SUBSET)
            (let ((z (subset-by-element!)))
              (bio-open-ball-h! `(IN ,z (BALL s x r)))
              (ass)))
           ((bio-head? g 'FORALL) (bio-interior!))
           (#t (error "ball-is-open: unexpected conjunct" (expression->string g)))))))
(qed 'ball-is-open)
(topic! 'ball-is-open 'topology)
