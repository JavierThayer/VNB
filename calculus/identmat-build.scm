;;; identmat-build.scm -- warm-up proof: IDENTMAT is a left identity for MATMUL.
;;;   IS-RING(A), P in MAT(n,n,CARR A)  |-  MATMUL(A, IDENTMAT(A,n), P) = P
;;; via matrix-entry-extensionality: entries agree because the (i,k) entry is a
;;; FINSUM whose only surviving term (j=i) is 1*P_ik = P_ik.

(define (idg) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ida) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (idany p l) (let lp ((l l)) (cond ((null? l) #f)((p (car l))(car l))(else (lp (cdr l))))))
(define (idhd? h e) (and (pair? e) (eq? (car e) h)))
(define (idfind p) (idany p (ida)))
(define (idleaves)
  (filter (lambda (nd)(and (not (sequent-node-grounded? nd))(null? (sequent-node-in-arrows nd))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (idfocus! raw)
  (let lp ((ls (idleaves)))
    (cond ((null? ls)(error "no leaf =" raw))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) raw)
           (set-proof-state-focus! *ps* (car ls))(car ls))
          (else (lp (cdr ls))))))
(define (iddi*) (let lp () (let* ((g (idg))(h (and (pair? g)(car g))))
                             (when (memq h '(FORALL IMPLIES)) (di) (lp)))))
(define (dump tag) (newline)(display ";;; -- ")(display tag)(display " --")(newline)
  (display ";; goal: ")(display (expression->string (idg)))(newline)
  (display ";; asms:")(newline)
  (for-each (lambda (a)(display ";;   ")(display (expression->string a))(newline)) (ida)))

(sp '(FORALL a (IMPLIES (IS-RING a)
       (FORALL n (IMPLIES (IN n NN)
       (FORALL p (IMPLIES (IN p (MAT n n (CARR a)))
         (= (MATMUL a (IDENTMAT a n) p) p))))))))
(iddi*)
(dump "after intro (goal = MATMUL I p = p)")

;; ---- typing: IDENTMAT and the product are n-by-n over CARR a ----
(fact 'identmat-type 'a 'n)                         ; IN (IDENTMAT a n) (MAT n n (CARR a))
(fact 'matmul-type 'a 'n 'n 'n '(IDENTMAT a n) 'p)  ; IN (MATMUL a (IDENTMAT a n) p) (MAT n n (CARR a))
(dump "after typing")

;; ---- entry agreement (cut; proof deferred to fill next) ----
(define ENTRYEQ
  '(FORALL i (IMPLIES (IN i (INTERVAL 1 n))
     (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (MATMUL a (IDENTMAT a n) p) i j) (ENTRY p i j)))))))
(cut ENTRYEQ)

;; ===== prove ENTRYEQ =====  (cut auto-focuses this subgoal)
(iddi*)                                    ; intro i, j (+ their INTERVAL memberships)
(define ig (idg))                          ; (= (ENTRY MM i j) (ENTRY p i j))
(define ii (list-ref (cadr ig) 2))
(define jj (list-ref (cadr ig) 3))
(display ";; i=") (display ii) (display " j=") (display jj) (newline)
;; expand the (i,j) product entry to its FINSUM
(fact 'matmul-entry 'a 'n 'n 'n '(IDENTMAT a n) 'p ii jj)
(define Hmm (idfind (lambda (x) (and (idhd? '= x) (idhd? 'ENTRY (cadr x)) (idhd? 'FINSUM (caddr x))))))
(define FIN (caddr Hmm))                   ; (FINSUM ag F S)
(define AG  (list-ref FIN 1))
(define FF  (list-ref FIN 2))
(define SS  (list-ref FIN 3))
(subst Hmm)                                ; goal -> (= FIN (ENTRY p i j))
(dump "ENTRYEQ leaf after matmul-entry+subst (goal should be = FINSUM (ENTRY p i j))")
(display ";; captured F = ") (write FF) (newline)
(display ";; captured ag = ") (write AG) (newline)
