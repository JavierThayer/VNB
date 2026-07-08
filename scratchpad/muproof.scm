;;; muproof.scm -- drive matunit-col-shift (Lemma 3.3) to QED.  Loads AFTER load.scm.
;;; Run: VNB_SKIP_PROOFS=1 mit-scheme --heap 120000 --load load.scm --load scratchpad/muproof.scm

(define (last-node) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (refocus! n) (set-proof-state-focus! *ps* n))
(define (mu-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mu-di*) (let lp () (let* ((g (mu-goal)) (h (and (pair? g) (car g))))
                   (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (probe tag)
  (display ";; --- ") (display tag) (display " ---") (newline)
  (display ";; GOAL: ") (write (mu-goal)) (newline)
  (display ";; OPEN: ") (display (length (dg-ungrounded-nodes (proof-state-dg *ps*)))) (newline))

;; EM / cases helpers (from scratch-wo.scm)
(define (em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (last-node)))
    (pbc)
    (cut `(NOT ,P))
    (let ((use-notp (last-node)))
      (di)
      (cut `(OR ,P (NOT ,P)))
      (let ((use-or2 (last-node))) (oi-l) (ass) (refocus! use-or2))
      (ai `(NOT (OR ,P (NOT ,P))))
      (refocus! use-notp))
    (cut `(OR ,P (NOT ,P)))
    (let ((use-or3 (last-node))) (oi-r) (ass) (refocus! use-or3))
    (ai `(NOT (OR ,P (NOT ,P))))
    (refocus! use-or)))
(define (cases P) (em P) (ai `(OR ,P (NOT ,P))) (last-node))

;; term abbreviations
(define RAG '(RING-ADDITIVE-AG A))
(define FF  '(VNB-LAMBDA j ((MUL A) (ENTRY P i j) (ENTRY (MATUNIT A n k l) j c))))
(define INT '(INTERVAL 1 n))

(define THM-WFF
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL P (FORALL k (FORALL l
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN k (INTERVAL 1 n))
       (IMPLIES (IN l (INTERVAL 1 n))
       (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
       (FORALL c (IMPLIES (IN c (INTERVAL 1 n))
         (= (ENTRY (MATMUL A P (MATUNIT A n k l)) i c)
            (IF (= c l) (ENTRY P i k) (ZERO A))))))))))))))))))

(set! *vnb-quiet* #t)   ; suppress per-command state dumps (huge fact-accumulated contexts)
(sp (make-wff THM-WFF))
(mu-di*)
(probe "after di*")

;; expand the product entry to a FINSUM
(fact 'matunit-type 'A 'n 'k 'l)   ; (IN (MATUNIT A n k l) (MAT n n (CARR A))) -- matmul-entry's 2nd antecedent
(fact 'matmul-entry 'A 'm 'n 'n 'P '(MATUNIT A n k l) 'i 'c)
(subst `(= (ENTRY (MATMUL A P (MATUNIT A n k l)) i c)
           (FINSUM ,RAG ,FF ,INT)))
(probe "after matmul-entry + subst")

;; finsum-single-support antecedents (all but the VANISH premise)
(fact 'ring-additive-ag-is-abelian-group 'A)
(fact 'interval-in-set 1 'n)
(fact 'interval-card-in-nn 1 'n)
(fact 'matunit-summand-type 'A 'm 'n 'P 'k 'l 'i 'c)
(probe "after 4 finsum antecedents")

;; VANISH: forall jz in [1,n], jz/=k => FF(jz) = ID(RAG)
(define VANISH
  `(FORALL jz (IMPLIES (IN jz ,INT)
     (IMPLIES (NOT (= jz k))
       (= (,FF jz) (ID ,RAG))))))
(cut VANISH)
(define uMAIN (last-node))
  ;; prove VANISH
  (di) (di) (di)
  (probe "VANISH after di di di")
  (lam-b)
  (probe "VANISH after lam-b")
  (fact 'matunit-entry-off-row 'A 'n 'k 'l 'jz 'c)
  (subst `(= (ENTRY (MATUNIT A n k l) jz c) (ZERO A)))
  (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'i 'jz)
  (fact 'ring-mul-zero-right 'A '(ENTRY P i jz))
  (subst `(= ((MUL A) (ENTRY P i jz) (ZERO A)) (ZERO A)))
  (fact 'ras-id 'A)
  (subst `(= (ID (RING-ADDITIVE-AG A)) (ZERO A)))
  (rfl)
  (probe "VANISH branch done?")
(refocus! uMAIN)

;; collapse the finsum
(fact 'finsum-single-support RAG INT FF 'k)
(subst `(= (FINSUM ,RAG ,FF ,INT) (,FF k)))
(probe "after finsum collapse + subst")
(lam-b)
(probe "after lam-b of (FF k)")

;; resolve the matrix-unit entry on the k-row
(fact 'matunit-entry-k-row 'A 'n 'k 'l 'c)
(subst `(= (ENTRY (MATUNIT A n k l) k c) (IF (= c l) (ONE A) (ZERO A))))
(fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'i 'k)
(probe "leaf before case-split")

;; case split on (= c l)
(define uNOTcl (cases '(= c l)))
;; ---- (= c l) branch (current focus) ----
(if-true '(IF (= c l) (ONE A) (ZERO A)))
(define uPl (last-node)) (ass) (refocus! uPl)
(subst '(= (IF (= c l) (ONE A) (ZERO A)) (ONE A)))
(if-true '(IF (= c l) (ENTRY P i k) (ZERO A)))
(define uPr (last-node)) (ass) (refocus! uPr)
(subst '(= (IF (= c l) (ENTRY P i k) (ZERO A)) (ENTRY P i k)))
(fact 'ring-mul-right-id 'A '(ENTRY P i k))
(subst '(= ((MUL A) (ENTRY P i k) (ONE A)) (ENTRY P i k)))
(rfl)
(probe "c=l branch done?")
;; ---- (NOT (= c l)) branch ----
(refocus! uNOTcl)
(if-false '(IF (= c l) (ONE A) (ZERO A)))
(define uNl (last-node)) (ass) (refocus! uNl)
(subst '(= (IF (= c l) (ONE A) (ZERO A)) (ZERO A)))
(if-false '(IF (= c l) (ENTRY P i k) (ZERO A)))
(define uNr (last-node)) (ass) (refocus! uNr)
(subst '(= (IF (= c l) (ENTRY P i k) (ZERO A)) (ZERO A)))
(fact 'ring-mul-zero-right 'A '(ENTRY P i k))
(subst '(= ((MUL A) (ENTRY P i k) (ZERO A)) (ZERO A)))
(rfl)

(newline)
(display (if (proof-done? *ps*)
             ";; *** matunit-col-shift: PROOF COMPLETE ***"
             ";; !!! matunit-col-shift: STILL OPEN"))
(newline)
(display ";; ungrounded nodes: ") (display (length (dg-ungrounded-nodes (proof-state-dg *ps*)))) (newline)
