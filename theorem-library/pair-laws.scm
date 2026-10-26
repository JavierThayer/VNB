;;; pair-laws.scm -- plain facts about pairs and cartesian products, in CORE.
;;;
;;; CLEANUP-1 (2026-10-25).  Four lemmas that were proven where a higher library
;;; first needed them, and so set a load floor under every later user:
;;;
;;;   cartesian-nth            was finsum-fiber.scm        (algebra)
;;;   cartesian-pair-eq        was monalg-is-ring.scm      (algebra)
;;;   pair-in-cartesian-parts  was strand-messages-laws.scm (strand)
;;;   node-pair-injective      was strand-space-laws.scm   (strand)
;;;
;;; Same names, same statements (copied literally).  No helper of the old files.
;;;
;;; Load window: lo = theorem-library/pair-tuple-sethood (pair-in-cartesian,
;;; cited by cartesian-pair-eq); everything else is kernel (cartesian-decompose is
;;; the procedural macete of library.scm, nth-r) or the driver kit.  Earliest slot:
;;; directly after "theorem-library/pair-tuple-sethood" in load.scm.  Library: core.

;;; z in X x Y  =>  NTH(1,z) in X and NTH(2,z) in Y
(sp (make-wff '(FORALL x_ (FORALL aa (FORALL bb
   (IMPLIES (IN x_ (CARTESIAN aa bb))
     (AND (IN (NTH 1 x_) aa) (IN (NTH 2 x_) bb))))))))
;; `mac' BEFORE any `di': cartesian-decompose rewrites the antecedent in place.
(mac 'cartesian-decompose)
(di) (di)
(let lp ((k 0))                            ; skolemize the two existentials
  (let ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
    (if (and ex (< k 5)) (begin (dk-split! ex) (lp (+ k 1))))))
(subst (dk-pick (lambda (a) (and (pair? a) (eq? (car a) '=) (eq? (cadr a) 'x_))) "x_ = [u,v]"))
(nth-r)
(dk-close-all! (lambda () (di)))
(qed 'cartesian-nth)
(gloss! 'cartesian-nth
  "A member of a cartesian product is the pair of its projections: z in X x Y
   implies NTH(1,z) in X and NTH(2,z) in Y.  What every typing of a lambda whose
   domain is a product needs, and what matmul-assoc-summand-type asserts.")
(topic! 'cartesian-nth 'plumbing)

;;; z in X x Y  =>  z = [NTH(1,z), NTH(2,z)]
(sp (make-wff '(FORALL x_ (FORALL aa (FORALL bb
   (IMPLIES (IN x_ (CARTESIAN aa bb))
     (= x_ (LIST (NTH 1 x_) (NTH 2 x_)))))))))
(mac 'cartesian-decompose)
(dk-peel!)
(let lp ((k 0))
  (let ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
    (if (and ex (< k 5)) (begin (dk-split! ex) (lp (+ k 1))))))
(let* ((eq (dk-pick (lambda (a) (and (pair? a) (eq? (car a) '=) (eq? (cadr a) 'x_))) "x_ = [u,v]"))
       (pr (caddr eq)))
  (fact 'pair-in-cartesian 'aa 'bb (cadr pr) (caddr pr))
  (subst eq)
  (nth-r)
  (rfl))
(qed 'cartesian-pair-eq)

;;; [u, v] in X x Y  =>  u in X and v in Y   (cartesian-nth at a literal pair)
(sp (make-wff '(FORALL X (FORALL Y (FORALL u (FORALL v
   (IMPLIES (IN (LIST u v) (CARTESIAN X Y)) (AND (IN u X) (IN v Y)))))))))
(dk-peel!)
(let* ((hyp (dk-pick (lambda (a) (and (dk-head-is? a 'IN) (pair? (caddr a))
                                      (eq? (car (caddr a)) 'CARTESIAN)))
                     "[u,v] in X x Y"))
       (pr  (cadr hyp)) (cx (caddr hyp))
       (cj  (dk-fact! 'cartesian-nth pr (cadr cx) (caddr cx))))
  (for-each (lambda (f) (dk-nth-h! f)) (dk-split! cj))
  (dk-conj-close! (lambda () (ass))))
(qed 'pair-in-cartesian-parts)
(topic! 'pair-in-cartesian-parts 'plumbing)

;;; [k, a] = [j, b]  =>  k = j and a = b
(sp (make-wff '(FORALL k (FORALL a (FORALL j (FORALL b
   (IMPLIES (= (LIST k a) (LIST j b)) (AND (= k j) (= a b)))))))))
(dk-peel!)
(let* ((hyp (dk-pick (lambda (a) (and (dk-head-is? a '=) (dk-head-is? (cadr a) 'LIST)
                                      (dk-head-is? (caddr a) 'LIST)))
                     "[k,a] = [j,b]"))
       (l1 (cadr hyp)) (l2 (caddr hyp)))
  (dk-conj-close!
    (lambda ()
      (let* ((i (if (equal? (cadr (dk-goal)) (cadr l1)) 1 2))
             (y (list-ref l2 i)))
        (dk-have! `(= (NTH ,i ,l2) ,y) (lambda () (nth-r) (rfl)))
        (subst `(= ,y (NTH ,i ,l2)))
        (subst `(= ,l2 ,l1))
        (nth-r)
        (rfl)))))
(qed 'node-pair-injective)
(topic! 'node-pair-injective 'constructions)
