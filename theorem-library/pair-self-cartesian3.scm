;;; pair-self-cartesian3.scm -- three generic set lemmas: a set is the one member of its own
;;; singleton PAIR(a, a) (pair-self-member, pair-self-eq), and the ternary product of three sets is a
;;; set (cartesian3-set).
;;;
;;; MOVED here from theorem-library/strand-messages-laws.scm (agent S-2 / S-1's proofs, 2026-10-06) by
;;; agent META-W1, 2026-10-16, so that the META library, which cites all three, imports `core' only
;;; (META-1 report, obstacle 3.11).  The statements are unchanged; the drivers are the originals with
;;; the strand file's local helpers (sml-keep-prop!, sml-cart-open!, sml-unpack!) replaced by their
;;; verbatim copies in driver-kit.scm (dk-meta-keep-prop!, dk-meta-cart-open!, dk-meta-unpack!) and
;;; the sethood of the binary product U x (V x W) by the local psc-set!.  Helper prefix: psc-.
;;; Every theorem below bills `modulo 0'.
;;;
;;; LOAD WINDOW: after theorem-library/pair-tuple-sethood (pair-in-cartesian) and subset-lemmas
;;; (subclass-of-set-is-set); before strand-messages-laws, strand-space-laws and the META laws files,
;;; which cite them, and before the first proof that runs driver-kit's dk-meta-unpack! or
;;; dk-meta-close-in! on a tag PAIR(n, n).  Library: core.

;;; -----------------------------------------------------------------------
;;; 1. A set is the only member of its own singleton PAIR(a, a).

(sp (make-wff '(FORALL a (IMPLIES (IN a SET) (IN a (PAIR a a))))))
(di)
(dk-have! '(AND (IN a SET) (IN a SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'pairing-membership 'a 'a)
(inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-head-is? (caddr f) 'IFF)))
                 "the pairing universal")
        'a)
(dk-have! '(OR (= a a) (= a a)) (lambda () (oi-l) (rfl)))
(dk-meta-keep-prop! (iff-for '(IN a (PAIR a a))) '(OR (= a a) (= a a)))
(qed 'pair-self-member)

(sp (make-wff '(FORALL a (FORALL x (IMPLIES (IN a SET) (IMPLIES (IN x (PAIR a a)) (= x a)))))))
(di) (di) (di)
(dk-have! '(AND (IN a SET) (IN a SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'pairing-membership 'a 'a)
(inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-head-is? (caddr f) 'IFF)))
                 "the pairing universal")
        'x)
(dk-meta-keep-prop! (iff-for '(IN x (PAIR a a))) '(IN x (PAIR a a)))
(qed 'pair-self-eq)

;;; -----------------------------------------------------------------------
;;; 2. The ternary product is a set by REPLACEMENT over the binary product U x (V x W) (S-1).

;; (IN t SET) for t a symbol whose sethood is in context, or a binary CARTESIAN of such terms.
(define (psc-set! t)
  (let ((goal `(IN ,t SET)))
    (cond
      ((dk-asm? goal) goal)
      ((and (pair? t) (eq? (car t) 'CARTESIAN) (= (length t) 3))
       (psc-set! (cadr t)) (psc-set! (caddr t))
       (let ((both `(AND (IN ,(cadr t) SET) (IN ,(caddr t) SET))))
         (dk-have! both (lambda () (dk-conj-close! (lambda () (ass)))))
         (fact 'cartesian-set-iff (cadr t) (caddr t))
         (dk-have! goal (lambda () (dk-meta-keep-prop! (iff-for goal) both)))
         goal))
      (#t (error "psc-set!: no route to the sethood of" (expression->string t))))))

(define psc-phi
  '(VNB-LAMBDA cqp_ (CARTESIAN U (CARTESIAN V W))
     (LIST (NTH 1 cqp_) (NTH 1 (NTH 2 cqp_)) (NTH 2 (NTH 2 cqp_)))))

(sp (make-wff '(FORALL U (FORALL V (FORALL W
   (IMPLIES (IN U SET) (IMPLIES (IN V SET) (IMPLIES (IN W SET) (IN (CARTESIAN U V W) SET)))))))))
(dk-peel!)
(let* ((ww '(CARTESIAN U (CARTESIAN V W)))
       (img `(IMAGE ,psc-phi ,ww))
       (sub `(SUBSET (CARTESIAN U V W) ,img)))
  (psc-set! ww)
  (fact 'image-set psc-phi ww)
  (dk-have! sub
    (lambda ()
      (mac 'subset-def)
      (di)
      (let* ((x (cadr (dk-goal)))
             (vs (dk-meta-unpack! (dk-meta-cart-open! `(IN ,x (CARTESIAN U V W)))))
             (a1 (car vs)) (a2 (cadr vs)) (a3 (caddr vs))
             (pr `(LIST ,a1 (LIST ,a2 ,a3))))
        (dk-image-goal!)
        (ew pr)
        (fact 'pair-in-cartesian 'V 'W a2 a3)
        (fact 'pair-in-cartesian 'U '(CARTESIAN V W) a1 `(LIST ,a2 ,a3))
        (dk-each-leaf! (lambda () (di))
          (lambda ()
            (if (dk-head-is? (dk-goal) 'IN)
                (ass)
                (begin
                  (dk-lam-b!)
                  (let loop () (if (dk-contains? (dk-goal) 'NTH) (begin (nth-r) (loop))))
                  (subst (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) x))) (dk-asms)))
                  (rfl))))))))
  (fact 'subclass-of-set-is-set '(CARTESIAN U V W) img)
  (ass))
(qed 'cartesian3-set)

;;; -----------------------------------------------------------------------
;;; Topics.

(for-each (lambda (n) (topic! n 'plumbing)) '(pair-self-member pair-self-eq cartesian3-set))
