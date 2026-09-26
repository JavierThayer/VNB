;;; ---------------------------------------------------------------------------
;;; ord-segment-self:  n in NN => n not in ORD-SEGMENT(n).
;;; n in OS(n) iff ORD-LT(n,n) (ord-segment-membership) iff ORD-LE(n,n) and n /= n
;;; (ord-lt-iff); n = n by reflexivity.

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (NOT (IN n (ORD-SEGMENT n)))))))
(let* ((nv  (dk-di-var!))                              ; lands (IN n NN); goal is the NOT
       (hyp (dk-landed-1 (lambda () (di)))))           ; assumes (IN n (OS n)); goal FALSITY
  (dk-fact! 'nn-subset-ord nv)                          ; (IN n ORD)
  (fsi-mac-h! 'ord-segment-membership hyp)              ; -> (ORD-LT n n)
  (fsi-mac-h! 'ord-lt-iff (dk-pick (dk-head? 'ORD-LT) "ORD-LT n n"))
  (dk-split! (dk-pick (dk-head? 'AND) "ord-lt-iff conjunction"))
  (have! `(= ,nv ,nv) (lambda () (rfl)))
  (ai `(NOT (= ,nv ,nv))))
(fsi-check-done! 'ord-segment-self)
(qed 'ord-segment-self)

;;; ---------------------------------------------------------------------------
;;; fin-enum-is-bijection:  S finite => FIN-ENUM(S) in BIJECTION(OS(CARD S), S).
;;; FIN-ENUM S is CHOICE of that class; card-finite-bij says the class is inhabited.

(sp (make-wff '(FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (IN (FIN-ENUM S) (BIJECTION (ORD-SEGMENT (CARD S)) S)))))))
(let* ((landed (dk-peel!))
       (sv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                          "S in SET"))))
  (mac 'FIN-ENUM)                                       ; goal (IN (CHOICE B) B)
  (have! `(AND (IN ,sv SET) (IN (CARD ,sv) NN)))
  (dk-fact! 'card-finite-bij sv)                        ; (FORSOME phi (IN phi B))
  (bc* 'choice-axiom () (ass)))
(fsi-check-done! 'fin-enum-is-bijection)
(qed 'fin-enum-is-bijection)

;;; ---------------------------------------------------------------------------
;;; sum-ag-segment-congruence:  SUM-AG(ag,_,n) reads only the indices in OS(n).
;;;
;;;   n in NN => forall ag g h.  (forall i in OS(n). g i == h i)
;;;                              => SUM-AG(ag,g,n) == SUM-AG(ag,h,n)
;;;
;;; NN-induction: base is sum-ag-zero on both sides; step is sum-ag-succ on both sides,
;;; the hypothesis at n (n in OS(succ n)) for the top term and the IH for the rest, whose
;;; own guard is the hypothesis restricted to OS(n) (ord-segment-nn-succ, left disjunct).
;;; No typing is needed: the recursion equations are unguarded in ag and f.

(define fsi-congruence-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (FORALL g (FORALL h
       (IMPLIES (FORALL i (IMPLIES (IN i (ORD-SEGMENT n)) (== (g i) (h i))))
                (== (SUM-AG ag g n) (SUM-AG ag h n)))))))))

(sp (make-wff fsi-congruence-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (fsi-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (fsi-leaf leaves (lambda (g) (dk-contains? g 'succ)) "induction step")))
  ;; base: both sides are IDEN(ag)
  (dk-focus! base)
  (dk-peel!)
  (mac 'sum-ag-zero)
  (qrfl)
  (fsi-grounded! base 'congruence-base)
  ;; step
  (dk-focus! step)
  (let* ((landed (dk-peel!))                            ; (IN n NN), the IH, the agreement
         (nv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN)))
                             "n in NN")))
         (agree? (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                  (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                                  (pair? (cadr (caddr f))) (eq? (car (cadr (caddr f))) 'IN)
                                  (pair? (caddr (cadr (caddr f))))
                                  (eq? (car (caddr (cadr (caddr f)))) 'ORD-SEGMENT))))
         (hh  (dk-pick agree? "the agreement hypothesis on OS(succ n)"))
         (ih  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (not (agree? f)))) "the IH"))
         (gl  (fsi-goal))                               ; (== (SUM-AG ag g (succ n)) (SUM-AG ag h (succ n)))
         (agv (cadr (cadr gl))) (gv (caddr (cadr gl))) (hv (caddr (caddr gl))))
    (mac 'sum-ag-succ)                                  ; both sides
    (have! `(IN ,nv (ORD-SEGMENT (succ ,nv)))
           (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! hh nv)                                   ; (== (g n) (h n))
    (subst `(== (,gv ,nv) (,hv ,nv)))
    (have! `(FORALL i (IMPLIES (IN i (ORD-SEGMENT ,nv)) (== (,gv i) (,hv i))))
           (lambda ()
             (let ((iv (dk-di-var!)))
               (have! `(IN ,iv (ORD-SEGMENT (succ ,nv)))
                      (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! hh iv)
               (ass))))
    (dk-apply! ih agv gv hv)                            ; (== (SUM-AG ag g n) (SUM-AG ag h n))
    (subst `(== (SUM-AG ,agv ,gv ,nv) (SUM-AG ,agv ,hv ,nv)))
    (qrfl)))
(fsi-check-done! 'sum-ag-segment-congruence)
(qed 'sum-ag-segment-congruence)

