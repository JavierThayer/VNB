;;; rake-finsum-fubini-c.scm -- finsum-fubini-c, moved out of rake-finsum-laws.scm on
;;; 2026-09-17 (rake batch M) because it cites finsum-fubini, now PROVEN in
;;; rake-finsum-core.scm, which loads after rake-finsum-laws.  Window: after
;;; rake-finsum-core, before finsum-fiber (its earliest citer).  Helper prefix rkj-
;;; kept from the origin file (own environment).
(define (rkj-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkj: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkj: proof not complete" name))))

(define (rkj-pick-head head what) (dk-pick (dk-head? head) what))

;; the unique context formula (IN v SET) whose v is a symbol

;;; ------------------------------------------------------------------ fubini-c
;;; finsum-fubini-c -- theorem-library/finsum-fubini.scm:34, copied literally.
;;; It is finsum-fubini with the set/finiteness premises CURRIED, so the proof
;;; is one AND-introduction per index set and one citation.  finsum-fubini
;;; itself is an ASSERTED support (warranted `informal', founder-warrants.scm),
;;; so this is the one leaf here that chains: the bill is {finsum-fubini}, a
;;; BETTER tier than the `well-known' this support carried.
(define rkj-fubini-c-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL X (IMPLIES (IN X SET) (IMPLIES (IN (CARD X) NN)
     (FORALL Y (IMPLIES (IN Y SET) (IMPLIES (IN (CARD Y) NN)
     (FORALL f (IMPLIES (IN f (FUN (CARTESIAN X Y) (CARR ag)))
       (= (FINSUM ag (VNB-LAMBDA i X (FINSUM ag (VNB-LAMBDA j Y (f (LIST i j))) Y)) X)
          (FINSUM ag (VNB-LAMBDA j Y (FINSUM ag (VNB-LAMBDA i X (f (LIST i j))) X)) Y))))))))))))
)
(sp (make-wff rkj-fubini-c-stmt))
(dk-peel!)
(let* ((agv (cadr (rkj-pick-head 'IS-ABELIAN-GROUP "IS-ABELIAN-GROUP ag")))
       (ft  (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                      (pair? (caddr a)) (eq? (car (caddr a)) 'FUN)
                                      (pair? (cadr (caddr a)))
                                      (eq? (car (cadr (caddr a))) 'CARTESIAN)))
                     "f in FUN(CARTESIAN X Y, CARR ag)"))
       (fv  (cadr ft))
       (xv  (cadr (cadr (caddr ft))))
       (yv  (caddr (cadr (caddr ft)))))
  (display ";; rkj fubini vars: ") (display (list agv xv yv fv)) (newline)
  (have! (list 'AND (list 'IN xv 'SET) (list 'IN (list 'CARD xv) 'NN)))
  (have! (list 'AND (list 'IN yv 'SET) (list 'IN (list 'CARD yv) 'NN)))
  (dk-fact! 'finsum-fubini agv xv yv fv)
  (ass))
(rkj-check! 'finsum-fubini-c)
(qed 'finsum-fubini-c)
