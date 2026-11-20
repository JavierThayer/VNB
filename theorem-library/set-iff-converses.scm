;;; set-iff-converses.scm -- the TRUE converses of the two sethood axioms, PROVEN.
;;;
;;;   fun-set-converse          A in SET, A inhabited, FUN(A,B) in SET  =>  B in SET
;;;   cartesian-set-converse-1  CARTESIAN(A,B) in SET, B inhabited      =>  A in SET
;;;   cartesian-set-converse-2  CARTESIAN(A,B) in SET, A inhabited      =>  B in SET
;;;
;;; The third converse the repair calls for, FUN(A,B) inhabited => A in SET, is
;;; fun-domain-in-set (theorem-library/rake-analysis2.scm), already proven.
;;;
;;; fun-set-iff and cartesian-set-iff (library.scm) were IFFs until 2026-11-20.  Their
;;; "only if" halves are false in every model of NBG: CARTESIAN(EMPTY-SET, ORD) and
;;; FUN(EMPTY-SET, ORD) are sets while ORD is not, and FUN(ORD, B) is empty for every B.
;;; The axioms keep their "if" halves.  What remains true of the converse is below,
;;; each guard necessary:
;;;   * fun-set-converse needs A IN SET: FUN(ORD, ORD) is empty, so a set, and ORD is not
;;;     one.  It needs A inhabited: FUN(EMPTY-SET, ORD) = {EMPTY-SET}.
;;;   * cartesian-set-converse-1 needs B inhabited: CARTESIAN(ORD, EMPTY-SET) is empty.
;;;
;;; The arguments are replacement (image-set), not the axioms' converse, which no
;;; proof here cites:
;;;   * fun: fix a0 in A.  For b in B the constant function (x in A |-> b) is in
;;;     FUN(A,B) (lambda-type: b in B, A in SET) and takes the value b at a0, so B is
;;;     included in IMAGE(f |-> f(a0), FUN(A,B)), a set; subclass-of-set-is-set.
;;;   * cartesian-1: fix b0 in B.  For a in A, [a, b0] is in CARTESIAN(A,B) and its
;;;     first entry is a, so A is included in IMAGE(p |-> NTH(1,p), CARTESIAN(A,B)).
;;;     cartesian-2 is the same with the second entry.
;;;
;;; Floor: subset-lemmas (subclass-of-set-is-set), structure-library/injection
;;; (image-set, image-membership-iff).

;; Peel the statement: every leading universal and every antecedent.
(define sic-peel!
  (lambda ()
    (let loop ((n 0))
      (if (and (< n 8) (memq (car (dk-goal)) '(FORALL IMPLIES))) (begin (di) (loop (+ n 1)))))))

;; The last landed context formula with head HEAD.
(define (sic-asm-with head) (find (lambda (a) (and (pair? a) (eq? (car a) head))) (reverse (dk-asms))))

;; Close every open leaf whose goal is not in SKIP: by assumption, by reflexivity, or
;; after reducing an NTH of a literal list.  Errors on anything else.
(define (sic-close-new! skip)
  (let loop ((rounds 0))
    (let ((ls (filter (lambda (l) (not (member (dk-goal-of l) skip))) (dk-open-leaves))))
      (if (and (pair? ls) (< rounds 12))
          (let ((l (car ls)))
            (dk-focus! l)
            (let ((g (dk-goal)))
              (cond ((dk-asm? g) (ass))
                    ((and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl))
                    (else (nth-r)
                          (if (equal? (dk-goal) g)
                              (error "sic-close-new!: cannot close" (expression->string g))))))
            (loop (+ rounds 1)))))))

;; Goal x in IMAGE(phi, S) with the witness w in S and phi(w) = x by beta (and NTH).
;; G1 is the goal of the enclosing proof, left alone.
(define (sic-image-mem! g1 phi S w)
  (let* ((g0 (dk-goal)) (x (cadr g0))
         (iff (dk-cite! 'image-membership-iff phi S x)) (rhs (caddr iff))
         (eqn `(= (,phi ,w) ,x)))
    (dk-have! rhs
      (lambda ()
        (di)
        (sic-close-new! (list g1 g0 rhs (caddr rhs)))
        (dk-focus! (find (lambda (l) (equal? (dk-goal-of l) (caddr rhs))) (dk-open-leaves)))
        (ew w) (di)
        (sic-close-new! (list g1 g0 rhs eqn))
        (dk-focus! (find (lambda (l) (equal? (dk-goal-of l) eqn)) (dk-open-leaves)))
        (dk-lam-b!)
        (sic-close-new! (list g1 g0 rhs))))
    (prop)))

;;; ---------------------------------------------------------------------------
;;; fun-set-converse
(sp (make-wff '(FORALL A (FORALL B
                 (IMPLIES (IN A SET)
                   (IMPLIES (FORSOME u_ (IN u_ A))
                     (IMPLIES (IN (FUN A B) SET) (IN B SET))))))))
(sic-peel!)
(let* ((g1 (dk-goal)) (bB (cadr g1))
       (fs (find (lambda (a) (and (pair? a) (eq? (car a) 'IN) (pair? (cadr a)) (eq? (car (cadr a)) 'FUN))) (dk-asms)))
       (S (cadr fs)) (aA (cadr S))
       (a0 (dk-skolem! (sic-asm-with 'FORSOME)))
       (phi `(VNB-LAMBDA kf_ ,S (kf_ ,a0)))
       (img `(IMAGE ,phi ,S)))
  (dk-have! `(SUBSET ,bB ,img)
    (lambda ()
      (mac 'subset-def) (di)
      (let* ((bv (cadr (dk-goal))) (kb `(VNB-LAMBDA kx_ ,aA ,bv)))
        (dk-cite! 'membership-implies-sethood bv bB)
        (dk-have! `(IN ,kb ,S)
          (lambda ()
            (for-each (lambda (leaf) (dk-focus! leaf)
                        (if (eq? (car (dk-goal)) 'FORALL) (begin (di) (ass)) (ass)))
                      (dk-opened (lambda () (lam-t))))))
        (sic-image-mem! g1 phi S kb))))
  (dk-cite! 'image-set phi S)
  (dk-cite! 'subclass-of-set-is-set bB img)
  (dk-close-if-asm!))
(qed 'fun-set-converse)
(topic! 'fun-set-converse 'plumbing)

;;; ---------------------------------------------------------------------------
;;; cartesian-set-converse-1 / -2: the factor SIDE is a set when the other is inhabited.
(define (sic-cartesian! side)
  (sic-peel!)
  (let* ((g1 (dk-goal))
         (cs (find (lambda (a) (and (pair? a) (eq? (car a) 'IN) (pair? (cadr a)) (eq? (car (cadr a)) 'CARTESIAN))) (dk-asms)))
         (C (cadr cs)) (aA (cadr C)) (bB (caddr C))
         (w0 (dk-skolem! (sic-asm-with 'FORSOME)))
         (tgt (if (= side 1) aA bB))
         (phi `(VNB-LAMBDA cp_ ,C (NTH ,side cp_)))
         (img `(IMAGE ,phi ,C)))
    (dk-have! `(SUBSET ,tgt ,img)
      (lambda ()
        (mac 'subset-def) (di)
        (let* ((v (cadr (dk-goal))) (t (if (= side 1) `(LIST ,v ,w0) `(LIST ,w0 ,v))))
          (dk-cite! 'membership-implies-sethood v tgt)
          (dk-have! `(IN ,t ,C) (lambda () (for-each (lambda (leaf) (dk-focus! leaf) (ass)) (dk-opened (lambda () (ci))))))
          (sic-image-mem! g1 phi C t))))
    (dk-cite! 'image-set phi C)
    (dk-cite! 'subclass-of-set-is-set tgt img)
    (dk-close-if-asm!)))

(sp (make-wff '(FORALL A (FORALL B
                 (IMPLIES (IN (CARTESIAN A B) SET)
                   (IMPLIES (FORSOME v_ (IN v_ B)) (IN A SET)))))))
(sic-cartesian! 1)
(qed 'cartesian-set-converse-1)
(topic! 'cartesian-set-converse-1 'plumbing)

(sp (make-wff '(FORALL A (FORALL B
                 (IMPLIES (IN (CARTESIAN A B) SET)
                   (IMPLIES (FORSOME u_ (IN u_ A)) (IN B SET)))))))
(sic-cartesian! 2)
(qed 'cartesian-set-converse-2)
(topic! 'cartesian-set-converse-2 'plumbing)
