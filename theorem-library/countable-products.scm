;;; countable-products.scm -- wave of 2026-11-09/10 (agent BA-ONB3), wired 2026-11-10 from scratchpad/baonb3-1109/b3-count.scm.
;;; Library: analysis.

;;; b3-count.scm -- COUNTABILITY: an enumeration of a nonempty countable set, and the product of
;;; two countable sets.  Agent BA-ONB3, 2026-11-09.  Prefix b3n-.  Nothing asserted.
;;; DESTINATION: theorem-library/countable-products.scm.  Library: analysis (beside countable.scm).
;;; LOAD WINDOW: after the file proving countable-cases / countable-of-enum / countable-subset /
;;; countable-empty and after the NNPAIR laws (nnpair-type, nnfst-nnpair, nnsnd-nnpair); cites nothing
;;; of this wave.
(define (b3n-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; b3n: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l) (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))
        (error "b3n: proof not complete" name)))
  (qed name)
  (topic! name 'analysis))
(define (b3n-open?) (not (sequent-node-grounded? (proof-state-focus *ps*))))
(define (b3n-close!) (cond ((not (b3n-open?)) #t) ((dk-asm? (dk-goal)) (ass)) (#t (rfl))))
(define (b3n-and! a b) (dk-have! (list 'AND a b) (lambda () (dk-conj-close! (lambda () (ass))))))
(define (b3n-onto e d) (list 'FORALL 'rqy_ (list 'IMPLIES (list 'IN 'rqy_ d) (list 'FORSOME 'rqn_ (list 'AND '(IN rqn_ NN) (list '= 'rqy_ (list e 'rqn_)))))))
(define (b3n-enum d) (list 'FORSOME 'rqe_ (list 'AND (list 'IN 'rqe_ (list 'FUN 'NN d)) (b3n-onto 'rqe_ d))))
;; IS-COUNTABLE d in context: lands d in SET and the disjunction, returns the disjunction
(define (b3n-cases! d)
  (let ((c (dk-cite! 'countable-cases d)))
    (dk-split! c)
    (dk-pick (lambda (a) (and (dk-head-is? a 'OR) (equal? (cadr a) (list '= d 'EMPTY-SET)))) "the cases")))

;;; ===========================================================================
;;; countable-enum-nonempty: a nonempty countable set is the image of an enumeration NN -> d,
;;; with repetitions allowed.
(sp (make-wff
  (list 'FORALL 'dset (list 'IMPLIES '(IS-COUNTABLE dset)
    (list 'IMPLIES '(FORSOME x0 (IN x0 dset)) (b3n-enum 'dset))))))
(dk-peel!)
(define b3n-x0 (dk-skolem! (dk-pick (lambda (a) (dk-head-is? a 'FORSOME)) "nonempty")))
(define b3n-or (b3n-cases! 'dset))
(dk-have! '(NOT (= dset EMPTY-SET))
  (lambda ()
    (di)
    (dk-rewrite-h! (list 'IN b3n-x0 'dset) 'dset 'EMPTY-SET)
    (fact 'empty-set-has-no-members b3n-x0)
    (prop)))
(dk-have! (caddr b3n-or) (lambda () (dk-close-if! (lambda () (dk-only! b3n-or '(NOT (= dset EMPTY-SET)))) prop)))
(b3n-close!)
(b3n-done! 'countable-enum-nonempty)

;;; ===========================================================================
;;; countable-cartesian: the product of two countable sets is countable.  When neither is empty,
;;; n |-> [ea(nnfst n), eb(nnsnd n)] enumerates it; when one is empty, so is the product.
(sp (make-wff
  '(FORALL sa (FORALL sb (IMPLIES (IS-COUNTABLE sa) (IMPLIES (IS-COUNTABLE sb) (IS-COUNTABLE (CARTESIAN sa sb))))))))
(dk-peel!)
(define b3n-C '(CARTESIAN sa sb))
(define b3n-ora (b3n-cases! 'sa))
(define b3n-orb (b3n-cases! 'sb))
(b3n-and! '(IN sa SET) '(IN sb SET))
(let ((iff (dk-cite! 'cartesian-set-iff 'sa 'sb)))
  (dk-have! (list 'IN b3n-C 'SET) (lambda () (dk-close-if! (lambda () (dk-only! iff '(AND (IN sa SET) (IN sb SET)))) prop))))
;; d (sa or sb) = EMPTY-SET in context, idx its coordinate: the product is countable
(define (b3n-empty-case! d idx)
  (dk-have! (list 'SUBSET b3n-C 'EMPTY-SET)
    (lambda ()
      (mac 'subset-def)
      (let* ((w (cadr (car (dk-peel!)))) (pw (list 'NTH idx w)))
        (dk-cite! 'cartesian-membership-nth 'sa 'sb w)
        (dk-have! (list 'IN pw d) (lambda () (prop)))
        (dk-rewrite-h! (list 'IN pw d) d 'EMPTY-SET)
        (fact 'empty-set-has-no-members pw)
        (dk-close-if! (lambda () (dk-only! (list 'IN pw 'EMPTY-SET) (list 'NOT (list 'IN pw 'EMPTY-SET)))) prop))))
  (fact 'countable-empty)
  (fact 'countable-subset b3n-C 'EMPTY-SET)
  (b3n-close!))
(define b3n-L '(VNB-LAMBDA b3n_ NN (LIST (ea (nnfst b3n_)) (eb (nnsnd b3n_)))))
(define (b3n-main!)
  (dk-have! (caddr b3n-ora) (lambda () (dk-close-if! (lambda () (dk-only! b3n-ora '(NOT (= sa EMPTY-SET)))) prop)))
  (dk-have! (caddr b3n-orb) (lambda () (dk-close-if! (lambda () (dk-only! b3n-orb '(NOT (= sb EMPTY-SET)))) prop)))
  (let* ((ea (dk-skolem! (caddr b3n-ora) #t))
         (eb (dk-skolem! (caddr b3n-orb) #t))
         (L (list 'VNB-LAMBDA 'b3n_ 'NN (list 'LIST (list ea '(nnfst b3n_)) (list eb '(nnsnd b3n_)))))
         (onta (dk-pick (lambda (a) (and (dk-head-is? a 'FORALL) (dk-contains? a ea))) "onto a"))
         (ontb (dk-pick (lambda (a) (and (dk-head-is? a 'FORALL) (dk-contains? a eb))) "onto b")))
    (dk-have! (list 'IN L (list 'FUN 'NN b3n-C))
      (lambda () (dk-lam-type! (lambda () (let* ((k (dk-di-var!)) (k1 (list 'nnfst k)) (k2 (list 'nnsnd k)))
                                             (fact 'nnfst-type k) (fact 'nnsnd-type k)
                                             (fact 'fun-apply-type-c ea 'NN 'sa k1) (fact 'fun-apply-type-c eb 'NN 'sb k2)
                                             (fact 'pair-in-cartesian 'sa 'sb (list ea k1) (list eb k2))
                                             (b3n-close!)))
                               (lambda () (fact 'nn-is-set) (ass)))))
    (dk-have! (b3n-onto L b3n-C)
      (lambda ()
        (let* ((w (cadr (car (dk-peel!)))) (w1 (list 'NTH 1 w)) (w2 (list 'NTH 2 w)))
          (dk-split-all! (list (dk-landed-1 (lambda () (mac-h 'cartesian-membership-nth (list 'IN w b3n-C))))))
          (let* ((i (dk-skolem! (dk-apply! onta w1) #t))
                 (j (dk-skolem! (dk-apply! ontb w2) #t))
                 (n (list 'nnpair i j)))
            (b3n-and! (list 'IN i 'NN) (list 'IN j 'NN))
            (fact 'nnpair-type i j)
            (ew n)
            (dk-conj-close!
              (lambda ()
                (if (dk-asm? (dk-goal)) (ass)
                    (begin
                      (dk-lam-b!)
                      (fact 'nnfst-nnpair i j) (fact 'nnsnd-nnpair i j)
                      (subst (list '= (list 'nnfst n) i))
                      (subst (list '= (list 'nnsnd n) j))
                      (subst (list '= (list ea i) w1))
                      (subst (list '= (list eb j) w2))
                      (b3n-close!)))))))))
    (fact 'countable-of-enum b3n-C L)
    (b3n-close!)))
(use-em '(= sa EMPTY-SET)
  (lambda () (b3n-empty-case! 'sa 1))
  (lambda () (use-em '(= sb EMPTY-SET)
               (lambda () (b3n-empty-case! 'sb 2))
               (lambda () (b3n-main!)))))
(b3n-done! 'countable-cartesian)
