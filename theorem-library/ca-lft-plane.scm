;;; ca-lft-plane.scm -- the point at infinity, the extended plane C u {oo}, and the values of
;;; LFT(a, b, c, d) and HOMOG-POINT(u, v) (complex-analysis.pdf s. 1.6, eq. (8) and (9)).
;;; CA-LFT, 2026-10-19.  Library: complex-analysis.  Vocabulary: structure-library/ca-lft-vocab.scm.
;;;
;;;   (cc-inf-in-set, cc-inf-not-in-cc: PRIMITIVE, in the vocabulary file)
;;;   cc-ne-inf             z in CC implies z /= CC-INF
;;;   cc-hat-membership     x in C u {oo} iff x in CC or x = CC-INF
;;;   cc-subset-cc-hat, cc-inf-in-cc-hat
;;;
;;;   cc-in-cc-hat, cc-hat-in-set, cc-div-closed
;;;   lft-at-inf-pole, lft-at-inf, lft-at-pole, lft-at-finite     the four values of (8) on C u {oo}
;;;   homog-point-at-inf, homog-point-finite                       the two values of phi (9)
;;;   lft-in-fun, homog-point-in-cc-hat                            typings
;;;
;;; Helper prefix clp-.

(define (clp-finish-ass!)
  (if (not (sequent-node-grounded? (proof-state-focus *ps*))) (ass)))

;;; cc-inf-in-set and cc-inf-not-in-cc are PRIMITIVE (structure-library/ca-lft-vocab.scm, the
;;; user's decision of 2026-10-19: CC-INF is a fresh constant).

(sp (make-wff '(FORALL z (IMPLIES (IN z CC) (NOT (= z CC-INF))))))
(let ((z (dk-di-var!)))
  (di)
  (fact 'cc-inf-not-in-cc)
  (dk-have! '(IN CC-INF CC) (lambda () (subst (list '= 'CC-INF z)) (ass)))
  (prop))
(qed 'cc-ne-inf)

(sp (make-wff '(FORALL x (IFF (IN x CC-HAT) (OR (IN x CC) (= x CC-INF))))))
(di)
(mac 'cc-hat-def)
(let ((x (cadr (cadr (dk-goal)))))
  (fact 'cc-inf-in-set)
  (fact 'union-membership 'CC '(SINGLETON CC-INF) x)
  (fact 'singleton-membership 'CC-INF x)
  (dk-have! (list 'IMPLIES (list '= x 'CC-INF) (list 'IN x 'SET))
    (lambda () (di) (subst (list '= x 'CC-INF)) (ass)))
  (prop))
(qed 'cc-hat-membership)

(sp (make-wff '(SUBSET CC CC-HAT)))
(let ((z (subset-by-element!)))
  (fact 'cc-hat-membership z)
  (prop))
(qed 'cc-subset-cc-hat)

(sp (make-wff '(IN CC-INF CC-HAT)))
(fact 'cc-hat-membership 'CC-INF)
(dk-have! '(= CC-INF CC-INF) (lambda () (rfl)))
(prop)
(qed 'cc-inf-in-cc-hat)

(sp (make-wff "forall([z in cc], z in cc-hat)"))
(let ((z (dk-di-var!)))
  (fact 'cc-hat-membership z)
  (prop))
(qed 'cc-in-cc-hat)

(sp (make-wff "forall([y in set], singleton(y) in set)"))
(let ((y (dk-di-var!)))
  (fact 'power-set y)
  (dk-have! (list 'SUBSET (list 'SINGLETON y) (list 'POWER y))
    (lambda ()
      (let ((x (subset-by-element!)))
        (fact 'singleton-membership y x)
        (let* ((pm  (dk-cite! 'power-set-membership y x))
               (all (caddr (caddr pm))))
          (dk-have! (list '= x y) (lambda () (prop)))
          (dk-have! (list 'IN x 'SET) (lambda () (prop)))
          (dk-have! all (lambda () (dk-peel!) (subst (list '= y x)) (ass)))
          (prop)))))
  (dk-cite! 'subclass-of-set-is-set (list 'SINGLETON y) (list 'POWER y))
  (clp-finish-ass!))
(qed 'singleton-is-set)

(sp (make-wff '(IN CC-HAT SET)))
(mac 'cc-hat-def)
(fact 'cc-is-set)
(fact 'cc-inf-in-set)
(dk-cite! 'singleton-is-set 'CC-INF)
(dk-have! '(AND (IN CC SET) (IN (SINGLETON CC-INF) SET)) (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'union-set-closure 'CC '(SINGLETON CC-INF))
(clp-finish-ass!)
(qed 'cc-hat-in-set)

;;; ---------------------------------------------------------------------------
;;; Helpers for the value lemmas.

(define (clp-vars landed)               ; the eigenvariables of the typings DK-PEEL! landed, in order
  (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)))) landed)))

(define (clp-conj fs)
  (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (clp-conj (cdr fs)))))

;;; cite THM at TERMS after landing the conjunction of FS (its conjunctive antecedent)
(define (clp-cite-and! thm fs . terms)
  (let ((c (clp-conj fs)))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (ass))))))
    (apply dk-cite! thm terms)))

(define (clp-first-if t)
  (cond ((not (pair? t)) #f)
        ((eq? (car t) 'IF) t)
        (#t (let loop ((ts (cdr t)))
              (cond ((null? ts) #f)
                    ((clp-first-if (car ts)) => (lambda (x) x))
                    (#t (loop (cdr ts))))))))

(define (clp-if! true? close-cond)       ; resolve the outermost IF of the goal
  (let ((ift (or (clp-first-if (dk-goal)) (error "clp-if!: no IF in the goal" (expression->string (dk-goal))))))
    (dk-if-branch! true? ift close-cond (lambda () #t))))

(define (clp-finish!)                   ; close a leftover reflexive goal on the focus
  (let ((leaf (proof-state-focus *ps*)))
    (if (and (not (sequent-node-grounded? leaf)) (dk-head-is? (dk-goal) '=)
             (equal? (cadr (dk-goal)) (caddr (dk-goal))))
        (rfl))))

(define (clp-type! t)                   ; land (IN t CC) by type-term
  (if (not (dk-asm? (list 'IN t 'CC)))
      (dk-have! (list 'IN t 'CC) (lambda () (type-term)))))

(define (clp-div! x y)                  ; land (IN (/ x y) CC) from x, y typed, y /= 0
  (clp-type! x) (clp-type! y)
  (if (not (dk-asm? (list 'IN (list '* x (list 'recip y)) 'CC)))
      (dk-cite! 'cc-div-closed x y)))

(sp (make-wff "forall([x in cc, y in cc], not(y = 0) implies x / y in cc)"))
(let ((vs (clp-vars (dk-peel!))))
  (let ((x (car vs)) (y (cadr vs)))
    (clp-cite-and! 'cc-recip-closed (list (list 'IN y 'CC) (list 'NOT (list '= y 0))) y)
    (clp-cite-and! 'cc-mul-closed (list (list 'IN x 'CC) (list 'IN (list 'recip y) 'CC)) x (list 'recip y))
    (if (pair? (dk-open-leaves)) (ass))))
(qed 'cc-div-closed)


;;; Goal (= ((VNB-LAMBDA v D body) z) RHS), z typed in D: prove body[v:=z] = RHS on a lane by RESOLVE,
;;; land its sethood from RHS's, then beta.  Beta owes (IN body[v:=z] SET) when body is an IF tower
;;; whose conditions are not decided in context.
(define (clp-beta-at! resolve rhs-set!)
  (let* ((g   (dk-goal))
         (app (cadr g))
         (lam (car app))
         (z   (cadr app))
         (b2  (subst-free (cadr lam) z (cadddr lam)))
         (rhs (caddr g)))
    (dk-have! (list '= b2 rhs) resolve)
    (dk-have! (list 'IN b2 'SET)
      (lambda () (subst (list '= b2 rhs)) (rhs-set! rhs)))
    (dk-lam-b!)
    (clp-finish-ass!)))

(define (clp-set-inf! t) (fact 'cc-inf-in-set) (clp-finish-ass!))
(define (clp-set-cc! t) (dk-cite! 'membership-implies-sethood t 'CC) (clp-finish-ass!))
;;; ---------------------------------------------------------------------------
;;; The four values of (8).

(sp (make-wff "forall([a in cc, b in cc, c in cc, d in cc], c = 0 implies (lft(a, b, c, d))(cc-inf) = cc-inf)"))
(dk-peel!)
(fact 'cc-inf-in-cc-hat)
(mac 'LFT)
(dk-lam-b!)
(clp-if! #t (lambda () (rfl)))
(clp-if! #t #f)
(clp-finish!)
(qed 'lft-at-inf-pole)

(sp (make-wff "forall([a in cc, b in cc, c in cc, d in cc], not(c = 0) implies (lft(a, b, c, d))(cc-inf) = a / c)"))
(let ((vs (clp-vars (dk-peel!))))
  (clp-div! (car vs) (caddr vs))
  (fact 'cc-inf-in-cc-hat)
  (mac 'LFT)
  (dk-lam-b!)
  (clp-if! #t (lambda () (rfl)))
  (clp-if! #f #f)
  (clp-finish!))
(qed 'lft-at-inf)

(sp (make-wff "forall([a in cc, b in cc, c in cc, d in cc, z in cc], c * z + d = 0 implies (lft(a, b, c, d))(z) = cc-inf)"))
(let ((vs (clp-vars (dk-peel!))))
  (let ((z (list-ref vs 4)))
    (dk-cite! 'cc-in-cc-hat z)
    (dk-cite! 'cc-ne-inf z)
    (mac 'LFT)
    (clp-beta-at! (lambda () (clp-if! #f #f) (clp-if! #t #f) (clp-finish!)) clp-set-inf!)))
(qed 'lft-at-pole)

(sp (make-wff "forall([a in cc, b in cc, c in cc, d in cc, z in cc], not(c * z + d = 0) implies (lft(a, b, c, d))(z) = (a * z + b) / (c * z + d))"))
(let ((vs (clp-vars (dk-peel!))))
  (let ((a (list-ref vs 0)) (b (list-ref vs 1)) (c (list-ref vs 2)) (d (list-ref vs 3)) (z (list-ref vs 4)))
    (dk-cite! 'cc-in-cc-hat z)
    (dk-cite! 'cc-ne-inf z)
    (clp-div! (list '+ (list '* a z) b) (list '+ (list '* c z) d))
    (mac 'LFT)
    (clp-beta-at! (lambda () (clp-if! #f #f) (clp-if! #f #f) (clp-finish!)) clp-set-cc!)))
(qed 'lft-at-finite)

;;; The two values of phi (9).

(sp (make-wff "forall([u in cc], homog-point(u, 0) = cc-inf)"))
(dk-peel!)
(mac 'HOMOG-POINT)
(clp-if! #t (lambda () (rfl)))
(clp-finish!)
(qed 'homog-point-at-inf)

(sp (make-wff "forall([u in cc, v in cc], not(v = 0) implies homog-point(u, v) = u / v)"))
(let ((vs (clp-vars (dk-peel!))))
  (clp-div! (car vs) (cadr vs))
  (mac 'HOMOG-POINT)
  (clp-if! #f #f)
  (clp-finish!))
(qed 'homog-point-finite)

;;; Typings.

(define (clp-case-ifs! closer)          ; split every IF of an (IN t C) goal, CLOSER at the leaves
  (let ((ift (clp-first-if (dk-goal))))
    (if ift
        (dk-case-if! ift (lambda (tv val) (clp-case-ifs! closer)))
        (closer))))

(define (clp-hat-closer!)               ; goal (IN t CC-HAT) for the three kinds of value
  (let ((t (cadr (dk-goal))))
    (cond ((eq? t 'CC-INF) (fact 'cc-inf-in-cc-hat) (if (pair? (dk-open-leaves)) (clp-finish-ass!)))
          ((and (dk-head-is? t '*) (dk-head-is? (caddr t) 'recip))
           (clp-div! (cadr t) (cadr (caddr t))) (dk-cite! 'cc-in-cc-hat t) (clp-finish-ass!))
          (#t (error "clp-hat-closer!: unexpected value" (expression->string t))))))


(sp (make-wff "forall([u in cc, v in cc], homog-point(u, v) in cc-hat)"))
(dk-peel!)
(mac 'HOMOG-POINT)
(clp-case-ifs! clp-hat-closer!)
(qed 'homog-point-in-cc-hat)

(sp (make-wff "forall([a in cc, b in cc, c in cc, d in cc], lft(a, b, c, d) in fun(cc-hat, cc-hat))"))
(dk-peel!)
(mac 'LFT)
(dk-lam-type!
  (lambda ()
    (let ((z (dk-di-var!)))
      (dk-cite! 'cc-hat-membership z)
      (clp-case-ifs!
        (lambda ()
          (if (dk-asm? (list 'NOT (list '= z 'CC-INF)))
              (dk-have! (list 'IN z 'CC) (lambda () (prop))))
          (clp-hat-closer!)))))
  (lambda () (fact 'cc-hat-in-set) (clp-finish-ass!)))
(qed 'lft-in-fun)
