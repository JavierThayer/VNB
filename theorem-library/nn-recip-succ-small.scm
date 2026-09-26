;;; nn-recip-succ-small.scm -- 1/(n+1) gets below any positive eps, PROVEN.
;;;
;;;   forall eps.  POS-RR(eps)  =>  forsome n_ in NN.  recip(n_ + 1) < eps
;;;
;;; Statement byte-for-byte the support of the same name in
;;; structure-library/order-predicates.scm (line 156).  It is the corollary of
;;; the archimedean property that eps-arguments actually consume, and it CHAINS
;;; to nn-unbounded-in-rr (theorem-library/nn-unbounded-in-rr.scm).
;;;
;;; THE PROOF.  Not the antitone route the retired warrant sketches (that one
;;; ends at recip(n+1) <= recip(recip eps) and still owes recip(recip eps) = eps
;;; and a strictness argument).  Two scalings instead, both by rr-lt-scale-pos:
;;;
;;;   recip(eps) < n            nn-unbounded-in-rr at x = recip(eps)
;;;   recip(eps) < n + 1        ineq
;;;   1 < eps * (n + 1)         scale by eps > 0; eps * recip(eps) = 1
;;;   recip(n+1) * 1 < recip(n+1) * (eps * (n+1))
;;;                             scale by recip(n+1) > 0
;;;   recip(n+1) * (eps * (n+1)) = eps
;;;                             crs, then (n+1) * recip(n+1) = 1, then crs
;;;   recip(n+1) < eps          ineq, the two products as opaque atoms
;;;
;;; `ineq' treats a product of two non-constant terms as an opaque atom (see
;;; structure-library/ineq-oracle.scm, vnb->linear), which is exactly what the
;;; last step wants; the atoms only have to be typed in RR (rr-mul-closed).
;;;
;;; WHAT IT COSTS.  `modulo 0' once nn-unbounded-in-rr is a theorem; on the
;;; band, where that name is still the support, the bill is
;;; modulo {nn-unbounded-in-rr}.  Everything else: rr-recip-closed /
;;; rr-recip-inverse / rr-mul-closed / rr-add-closed / nn-add-closed (primitive),
;;; rr-le-ne-lt / rr-pos-ne-zero / rr-lt-scale-pos (rr-order-basics, 137),
;;; rr-recip-pos (rr-recip-order, 142), nn-in-rr (136), nn-one-in (135).
;;;
;;; LOAD WINDOW.  Its own citations are all at or below rr-recip-order (142),
;;; so the window is [lo, 180) with lo = wherever nn-unbounded-in-rr lands + 1;
;;; hi is the earliest citer, compact-separable-proof (180).  With
;;; nn-unbounded-in-rr sitting above rr-sup-approx (288) the window is EMPTY:
;;; rr-sup-approx has to move up first (its own citations are subset-lemmas
;;; 147, rr-order-basics 137, binary-minus-laws 131).

;;; ---- file-local driver helpers (the `nrs-' prefix) --------------------

(define (nrs-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "nrs-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (nrs-ineq . forms) (apply ineq (map nrs-idx forms)))

;;; ---- the statement ---------------------------------------------------

(define nrs-stmt
  (forall-guarded 'eps '(POS-RR eps)
    (forsome-guarded 'n_ '(IN n_ NN)
      '(< (recip (+ n_ 1)) eps))))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff nrs-stmt))
;; POS-RR is not an IN-typing, so `di' peels the quantifier ALONE and the
;; antecedent lands on the next call: loop on the head, not on a count.
(let loop ((k 0))
  (if (and (memq (car (dk-goal)) '(FORALL IMPLIES)) (< k 4))
      (begin (di) (loop (+ k 1)))))

(dk-split! (dk-landed-1 (lambda () (mac-h 'pos-rr '(POS-RR eps)))))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'nn-one-in)
(have! '(AND (<= 0 eps) (NOT (= 0 eps))))
(fact 'rr-le-ne-lt 0 'eps)                        ; 0 < eps
(fact 'rr-pos-ne-zero 'eps)                       ; not(eps = 0)
(have! '(AND (IN eps RR) (NOT (= eps 0))))
(fact 'rr-recip-closed 'eps)                      ; recip(eps) in RR
(fact 'rr-recip-inverse 'eps)                     ; eps * recip(eps) = 1
(fact 'rr-recip-pos 'eps)                         ; 0 < recip(eps)

(let* ((ex    (dk-fact! 'nn-unbounded-in-rr '(recip eps)))
       (parts (dk-split! ex))
       (n     (cadr (or (find-first (dk-head? 'IN) parts)
                        (error "nrs: no landed membership" parts))))
       (n1    (list '+ n 1))
       (rn1   (list 'recip n1))
       (prod  (list '* 'eps n1))                  ; eps * (n+1)
       (H1    (list '< '(* eps (recip eps)) prod))
       (E1    '(= (* eps (recip eps)) 1))
       (big   (list '* rn1 prod))                 ; recip(n+1) * (eps * (n+1))
       (H2    (list '< (list '* rn1 1) big))
       (C1    (list '= big (list '* 'eps (list '* n1 rn1))))
       (C2    (list '= (list '* 'eps (list '* n1 rn1)) 'eps))
       (E2    (list '= big 'eps)))
  ;; typings of n and n + 1
  (fact 'nn-in-rr n)
  (have! (list 'AND (list 'IN n 'RR) '(IN 1 RR)))
  (fact 'rr-add-closed n 1)                       ; n + 1 in RR
  (have! (list 'AND (list 'IN n 'NN) '(IN 1 NN)))
  (fact 'nn-add-closed n 1)                       ; n + 1 in NN
  (have! (list '< 0 n1)
    (lambda () (nrs-ineq '(< 0 (recip eps)) (list '< '(recip eps) n))))
  (have! (list '< '(recip eps) n1)
    (lambda () (nrs-ineq (list '< '(recip eps) n))))
  (fact 'rr-pos-ne-zero n1)
  (have! (list 'AND (list 'IN n1 'RR) (list 'NOT (list '= n1 0))))
  (fact 'rr-recip-closed n1)                      ; recip(n+1) in RR
  (fact 'rr-recip-inverse n1)                     ; (n+1) * recip(n+1) = 1
  (fact 'rr-recip-pos n1)                         ; 0 < recip(n+1)
  ;; first scaling: by eps
  (have! (list 'AND '(< 0 eps) (list '< '(recip eps) n1)))
  (fact 'rr-lt-scale-pos 'eps '(recip eps) n1)    ; H1
  (have! (list 'AND '(IN eps RR) (list 'IN n1 'RR)))
  (fact 'rr-mul-closed 'eps n1)                   ; eps * (n+1) in RR
  (have! '(AND (IN eps RR) (IN (recip eps) RR)))
  (fact 'rr-mul-closed 'eps '(recip eps))         ; eps * recip(eps) in RR
  (have! (list '< 1 prod) (lambda () (nrs-ineq H1 E1)))
  ;; second scaling: by recip(n+1)
  (have! (list 'AND (list '< 0 rn1) (list '< 1 prod)))
  (fact 'rr-lt-scale-pos rn1 1 prod)              ; H2
  (have! (list 'AND (list 'IN rn1 'RR) (list 'IN prod 'RR)))
  (fact 'rr-mul-closed rn1 prod)                  ; big in RR
  ;; big = eps
  (have! C1 (lambda () (crs)))
  (have! C2 (lambda () (subst (list '= (list '* n1 rn1) 1)) (crs)))
  (have! E2 (lambda () (subst C1) (ass)))
  ;; the witness is n itself: the statement's term is recip(n_ + 1)
  (ew n)
  (for-each (lambda (k)
              (dk-focus! k)
              (if (eq? (car (dk-goal)) 'IN) (ass) (nrs-ineq H2 E2)))
            (dk-opened (lambda () (di)))))

(qed 'nn-recip-succ-small)
(topic! 'nn-recip-succ-small 'inequalities)
(alias! 'nn-recip-succ-small "1/(n+1) below any positive eps" "reciprocals of the naturals are small")
