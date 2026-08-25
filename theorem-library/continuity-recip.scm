;;; continuity-recip.scm -- THE RECIPROCAL OF A NON-VANISHING CONTINUOUS MAP,
;;; PROVEN `modulo 0'.
;;;
;;;   h in FUN(RR,RR),  h(x) /= 0 for every real x,  h continuous at p
;;;      =>  x |-> recip(h(x))  is a function RR -> RR, and is continuous at p
;;;
;;; This is the EIGHTH member of the pointwise continuity algebra and the first
;;; one the tree did not already have in some form: const, identity, sum,
;;; product, difference, negation, pointwise-equality transfer and composition
;;; are in continuity-basics/-sum/-product/-sub/-transfer/-compose, and nothing
;;; anywhere said anything about a reciprocal or a quotient.  It is the one
;;; genuine analytic lemma under the INVERSE FUNCTION THEOREM
;;; (theorem-library/inverse-function.scm), whose Caratheodory factor is
;;; recip o phi o g.
;;;
;;; WHY THE NOWHERE-ZERO HYPOTHESIS IS ON THE MAP AND NOT ON THE POINT.
;;; `recip' is PARTIAL: rr-recip-closed and rr-recip-inverse (number-systems.scm)
;;; are both guarded on `a /= 0', and there is no `recip 0' convention.  So
;;; (VNB-LAMBDA x RR (recip x)) is NOT a member of FUN(RR,RR) -- `lam-t' would
;;; owe (IN (recip 0) RR), which is false -- and "recip is continuous at c /= 0"
;;; is not a statement this vocabulary can make about a bare map at all.  The
;;; theorem is therefore stated about a COMPOSITE x |-> recip(h(x)) with h
;;; nowhere zero, which is total by construction; that is also the form a
;;; quotient rule would want, and it is the form the inverse function theorem
;;; needs (there h = phi o g, nowhere zero because f is injective).  A
;;; conditional total extension (VNB-LAMBDA x RR (IF (= x 0) 0 (recip x))) --
;;; the `IF' idiom of finsum.scm's ENUM-FAM -- would give the bare-map reading,
;;; at the cost of a case split at every use; it is not needed here.
;;;
;;; THE PROOF, and the one thing that makes it short.  It is an eps/delta
;;; argument -- there is no way round that; the reciprocal is the first member
;;; of the algebra whose modulus of continuity depends on WHERE you are, so a
;;; preliminary bound is unavoidable.  What keeps it to one page is refusing to
;;; bound |1/h(b)| at all.  The naive route needs |1/z| <= 2/|c|, i.e. the
;;; reciprocal of a compound term, and the tree has no recip-of-a-product law
;;; and no `|recip u| = recip |u|' (that lemma does not exist -- checked).
;;; Instead everything is done with the single ring identity
;;;
;;;     (1/c - 1/z) * (c*z)  =  z - c            c = h(p),  z = h(b)
;;;
;;; -- a `crs' identity in the opaque generators recip(c), recip(z) once the two
;;; inverse equations collapse c*recip(c) and z*recip(z) to 1 -- and then
;;; `rr-abs-mult' twice, giving
;;;
;;;     D * |c| * |z|  =  |z - c|,      D = |1/c - 1/z|.
;;;
;;; With M = |c| > 0, halve it (rr-pos-halvable) to M = m + m; continuity at
;;; radius w <= m forces |z| >= m by the reverse triangle inequality, so
;;; D*(M*m) <= D*(M*|z|) = |z-c| <= w.  Choose w <= eps*(M*m) as well
;;; (rr-min-pos on the two radii), and the whole estimate is
;;;
;;;     D * K  <=  eps * K,     K = M*m > 0,
;;;
;;; from which `rr-nonneg-cancel-pos' strips K.  No reciprocal is ever bounded,
;;; no new lemma is minted, and every nonlinear step goes through
;;; `rr-le-scale-nonneg' or `crs' -- never through `ineq', which linearises a
;;; product of two variables into an opaque atom.
;;;
;;; WHAT IT COSTS: `modulo 0'.
;;;
;;; DRIVER NOTES.
;;;
;;; * `rc-open!' is DESTRUCTIVE by design.  `fact' detaches on the LITERAL
;;;   formula, so the conjuncts of a POS-RR have to land in the branch the
;;;   citations run in -- a `have!' lane that unfolds POS-RR and closes leaves
;;;   the main branch with the folded predicate and nothing else, and the next
;;;   `fact' then lands its implication chain undetached and the following
;;;   `obtain' reports "no existential landed" several steps away from the
;;;   cause.  So every use of the FOLDED POS-RR (here: `rr-pos-halvable' on M)
;;;   must happen BEFORE the `rc-open!' that consumes it.
;;; * `mac rr-ms-dist' is GUARDED: it declines silently on a goal whose two
;;;   points are not already typed in context.  Both reciprocals are typed
;;;   before the beta step, not after.
;;; * `slot-h PTS' is destructive too, so the delta-universal is instantiated at
;;;   b BEFORE b's membership is slotted down from PTS(RR-MS) to RR.
;;;
;;; Loads beside continuity-basics/-sum/-product/-transfer/-sub/-compose and
;;; before inverse-function.  Needs metric-continuity (IS-CONTINUOUS-AT),
;;; rr-ms-dist, rr-abs-basics (rr-abs-mult, rr-abs-reverse-triangle,
;;; rr-abs-sub-sym, rr-abs-zero, rr-le-abs), rr-order-basics (rr-le-ne-lt,
;;; rr-le-scale-nonneg, rr-nonneg-cancel-pos, rr-min-pos, rr-lt-implies-le,
;;; rr-pos-ne-zero, rr-sub-in-rr), rr-recip-order (rr-mul-pos), rr-halving
;;; (rr-pos-halvable), fun-apply-type-proof (fun-apply-type-c), driver-kit.

;;; ---- file-local driver helpers (the `rc-' prefix) --------------------

(define (rc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1))) #t))))
(define (rc-split!)
  (let loop ((b 40))
    (when (> b 0)
      (let ((t (let scan ((as (dk-asms)))
                 (cond ((null? as) #f)
                       ((and (pair? (car as)) (memq (caar as) '(AND FORSOME))) (car as))
                       (else (scan (cdr as)))))))
        (when t (ai t) (loop (- b 1)))))))
(define (rc-find what p)
  (let lp ((l (dk-asms)))
    (cond ((null? l) (error "rc-find" what)) ((p (car l)) (car l)) (else (lp (cdr l))))))
(define (rc-idx f)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rc-idx: not in context" f))
          ((equal? (car l) f) i) (else (lp (cdr l) (+ i 1))))))
(define (rc-ineq . fs) (apply ineq (map rc-idx fs)))
(define (rc-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (rc-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (rc-redex? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (rc-redex? (car g)) (rc-redex? (cdr g)))) (else #f)))
(define (rc-beta!)
  (let loop ((n 8))
    (if (and (> n 0) (rc-redex? (dk-goal)))
        (let ((b (dk-goal))) (lam-b) (if (equal? (dk-goal) b) #t (loop (- n 1)))) #t)))
(define (rc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new) ((> n 4) (error "rc-di-landed!")) (else (loop (+ n 1)))))))
(define (rc-obtain what lane)
  (let ((v (obtain lane))) (if (not v) (error "rc-obtain" what)) v))
;; c in RR, 0 < c  ==>  POS-RR(c) in context
(define (rc-pos! c)
  (fact 'rr-lt-implies-le 0 c)
  (fact 'rr-pos-ne-zero c)
  (fact 'neq-sym c 0)
  (have! (list 'POS-RR c) (lambda () (mac 'pos-rr) (from-context!))))
;; POS-RR(c) in context ==> its three conjuncts AND (< 0 c) in the MAIN context.
;; DESTRUCTIVE (`mac-h'): every use of the FOLDED POS-RR(c) must already have
;; happened.  A `have!' lane would not do: `fact' detaches on the literal
;; formula, so the conjuncts have to land in the branch the citations run in.
(define (rc-open! c)
  (mac-h 'pos-rr (list 'POS-RR c))
  (rc-split!)
  (have! (list 'AND (list '<= 0 c) (list 'NOT (list '= 0 c))))
  (fact 'rr-le-ne-lt 0 c))


;;; =====================================================================
;;; (1) x |-> recip(h(x)) is a function RR -> RR, when h never vanishes.
;;;
;;; `lam-t' opens TWO leaves -- the pointwise typing of the body and the
;;; SETHOOD of the domain -- and `dk-lam-t!' discharges the second.
;;; =====================================================================

(sp (make-wff (forall-guarded 'h '(IN h (FUN RR RR))
   '(IMPLIES (FORALL x (IMPLIES (IN x RR) (NOT (= (h x) 0))))
             (IN (VNB-LAMBDA x RR (recip (h x))) (FUN RR RR))))))
(rc-peel!)
(dk-lam-t!)
(let* ((landed (dk-landed (lambda () (di)))) (z (cadr (car landed))))
  (fact 'fun-apply-type-c 'h 'RR 'RR z)
  (inst+ (rc-find 'nz (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (dk-contains? u 'NOT)))) z)
  (have! (list 'AND (list 'IN (list 'h z) 'RR) (list 'NOT (list '= (list 'h z) 0))))
  (fact 'rr-recip-closed (list 'h z))
  (ass))
(qed 'recip-lam-in-fun)
(topic! 'recip-lam-in-fun 'analysis)
(alias! 'recip-lam-in-fun "the reciprocal of a nowhere-zero real function is a function")

;;; =====================================================================
;;; (2) recip-continuous-at.
;;; =====================================================================
(define rc-h #f) (define rc-p #f) (define rc-lam #f)
(define rc-nz #f) (define rc-c #f) (define rc-mm #f) (define rc-m2 #f)

(sp (make-wff (forall-guarded '(h p)
   (list '(IN h (FUN RR RR))
         '(FORALL x (IMPLIES (IN x RR) (NOT (= (h x) 0))))
         '(IS-CONTINUOUS-AT RR-MS RR-MS h p))
   '(IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (recip (h x))) p))))
(rc-peel!)
(let* ((g0 (dk-goal)))
  (set! rc-lam (list-ref g0 3))
  (set! rc-p (list-ref g0 4))
  (set! rc-h (car (cadr (list-ref rc-lam 3)))))
(set! rc-nz (rc-find 'nz (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (dk-contains? u 'NOT)))))
(fact 'recip-lam-in-fun rc-h)
(fact 'rr-zero-in)
(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS rc-h rc-p))
(rc-split!)
(slot-h 'PTS (list 'IN rc-p '(PTS RR-MS)))
(set! rc-c (list rc-h rc-p))
(set! rc-mm (list 'abs rc-c))
(fact 'fun-apply-type-c rc-h 'RR 'RR rc-p)
(inst+ rc-nz rc-p)
(fact 'rr-abs-closed rc-c)
(fact 'rr-abs-nonneg rc-c)
(have! (list 'NOT (list '= rc-mm 0)) (lambda () (mac 'rr-abs-zero) (ass)))
(fact 'neq-sym rc-mm 0)
(have! (list 'AND (list '<= 0 rc-mm) (list 'NOT (list '= 0 rc-mm))))
(fact 'rr-le-ne-lt 0 rc-mm)
(rc-pos! rc-mm)
(set! rc-m2 (rc-obtain 'half (lambda () (fact 'rr-pos-halvable rc-mm))))
(rc-split!)
(rc-open! rc-m2)
(have! (list 'AND (list 'IN rc-mm 'RR) (list 'IN rc-m2 'RR)))
(fact 'rr-mul-closed rc-mm rc-m2)
(fact 'rr-mul-pos rc-mm rc-m2)

(define (rc-eps-universal)
  (rc-find 'epsu (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                  (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)))))
(define (rc-delta-universal d)
  (rc-find 'deltau (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                    (dk-contains? f 'DIST) (dk-contains? f d)
                                    (not (dk-contains? f 'POS-RR))))))

(define (rc-inner! eps kk tt w dl)
  (let* ((landed (rc-di-landed!))
         (mem (or (find-first (lambda (u) (and (pair? u) (eq? (car u) 'IN))) landed)
                  (error "rc-inner!: no membership")))
         (b (cadr mem)))
    (if (not (find-first (lambda (u) (and (pair? u) (eq? (car u) '<=))) landed))
        (rc-di-landed!))
    (inst+ (rc-delta-universal dl) b)
    (slot-h 'PTS mem)
    (let* ((z (list rc-h b)) (az (list 'abs z))
           (rc (list 'recip rc-c)) (rz (list 'recip z))
           (dif (list '- rc rz)) (dd (list 'abs dif))
           (cz (list '* rc-c z)) (mz (list '* rc-mm az)))
      (fact 'fun-apply-type-c rc-h 'RR 'RR b)
      (inst+ rc-nz b)
      (have! (list 'AND (list 'IN rc-c 'RR) (list 'IN z 'RR)))
      (fact 'rr-sub-in-rr rc-c z)
      (fact 'rr-abs-closed (list '- rc-c z))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) rc-c z) w))
      (have! (list 'AND (list 'IN rc-c 'RR) (list 'NOT (list '= rc-c 0))))
      (fact 'rr-recip-closed rc-c) (fact 'rr-recip-inverse rc-c)
      (have! (list 'AND (list 'IN z 'RR) (list 'NOT (list '= z 0))))
      (fact 'rr-recip-closed z) (fact 'rr-recip-inverse z)
      (fact 'rr-sub-in-rr rc rz)
      (fact 'rr-abs-closed dif) (fact 'rr-abs-nonneg dif)
      (rc-beta!)
      (mac 'rr-ms-dist)
      ;; |z| >= m2
      (fact 'rr-abs-closed z) (fact 'rr-abs-nonneg z)
      (fact 'rr-abs-reverse-triangle rc-c z)
      (fact 'rr-sub-in-rr rc-mm az)
      (fact 'rr-abs-closed (list '- rc-mm az))
      (fact 'rr-le-abs (list '- rc-mm az))
      (have! (list '<= rc-m2 az)
        (lambda () (rc-ineq (list '<= (list '- rc-mm az) (list 'abs (list '- rc-mm az)))
                            (list '<= (list 'abs (list '- rc-mm az)) (list 'abs (list '- rc-c z)))
                            (list '<= (list 'abs (list '- rc-c z)) w)
                            (list '<= w rc-m2)
                            (list '= (list '+ rc-m2 rc-m2) rc-mm))))
      ;; (1/c - 1/z)*(c*z) = z - c
      (fact 'rr-mul-closed rc-c z)
      (fact 'rr-sub-in-rr z rc-c)
      (fact 'rr-abs-closed (list '- z rc-c))
      (let ((expand (list '- (list '* (list '* rc-c rc) z) (list '* (list '* z rz) rc-c))))
        (have! (list '= (list '* dif cz) (list '- z rc-c))
          (lambda ()
            (have! (list '= (list '* dif cz) expand) (lambda () (crs)))
            (subst (list '= (list '* dif cz) expand))
            (subst (list '= (list '* rc-c rc) 1))
            (subst (list '= (list '* z rz) 1))
            (crs))))
      (have! (list 'AND (list 'IN dif 'RR) (list 'IN cz 'RR)))
      (fact 'rr-abs-mult dif cz)
      (fact 'rr-abs-mult rc-c z)          ; the AND is already in context
      (have! (list '= (list '* dd mz) (list 'abs (list '- z rc-c)))
        (lambda ()
          (fact 'eq-sym (list 'abs cz) mz)
          (subst (list '= mz (list 'abs cz)))
          (fact 'eq-sym (list 'abs (list '* dif cz)) (list '* dd (list 'abs cz)))
          (subst (list '= (list '* dd (list 'abs cz)) (list 'abs (list '* dif cz))))
          (subst (list '= (list '* dif cz) (list '- z rc-c)))
          (rfl)))
      (fact 'rr-abs-sub-sym z rc-c)
      (have! (list '<= (list 'abs (list '- z rc-c)) w)
        (lambda () (subst (list '= (list 'abs (list '- z rc-c)) (list 'abs (list '- rc-c z)))) (ass)))
      (have! (list 'AND (list 'IN rc-mm 'RR) (list 'IN az 'RR)))
      (fact 'rr-mul-closed rc-mm az)
      (have! (list 'AND (list '<= 0 rc-mm) (list '<= rc-m2 az)))
      (fact 'rr-le-scale-nonneg rc-mm rc-m2 az)
      (have! (list 'AND (list 'IN dd 'RR) (list 'IN kk 'RR)))
      (fact 'rr-mul-closed dd kk)
      (have! (list 'AND (list 'IN dd 'RR) (list 'IN mz 'RR)))
      (fact 'rr-mul-closed dd mz)
      (have! (list 'AND (list '<= 0 dd) (list '<= kk mz)))
      (fact 'rr-le-scale-nonneg dd kk mz)
      (have! (list '<= (list '* dd kk) tt)
        (lambda () (rc-ineq (list '<= (list '* dd kk) (list '* dd mz))
                            (list '= (list '* dd mz) (list 'abs (list '- z rc-c)))
                            (list '<= (list 'abs (list '- z rc-c)) w)
                            (list '<= w tt))))
      (fact 'rr-sub-in-rr eps dd)
      (have! (list 'AND (list 'IN kk 'RR) (list 'IN (list '- eps dd) 'RR)))
      (fact 'rr-mul-closed kk (list '- eps dd))
      (have! (list '<= 0 (list '* kk (list '- eps dd)))
        (lambda ()
          (have! (list '= (list '* kk (list '- eps dd)) (list '- tt (list '* dd kk)))
                 (lambda () (crs)))
          (subst (list '= (list '* kk (list '- eps dd)) (list '- tt (list '* dd kk))))
          (rc-ineq (list '<= (list '* dd kk) tt))))
      (fact 'rr-nonneg-cancel-pos kk (list '- eps dd))
      (rc-ineq (list '<= 0 (list '- eps dd))))))

(define (rc-eps!)
  (let* ((pos (car (rc-di-landed!)))
         (eps (cadr pos))
         (kk (list '* rc-mm rc-m2))
         (tt (list '* eps kk)))
    (rc-open! eps)
    (have! (list 'AND (list 'IN eps 'RR) (list 'IN kk 'RR)))
    (fact 'rr-mul-closed eps kk)
    (fact 'rr-mul-pos eps kk)
    (let ((w (rc-obtain 'w (lambda () (fact 'rr-min-pos rc-m2 tt)))))
      (rc-split!)
      (rc-pos! w)
      (let ((dl (rc-obtain 'delta (lambda () (inst+ (rc-eps-universal) w)))))
        (rc-split!)
        (ew dl)
        (rc-and! (lambda ()
                   (if (eq? (car (dk-goal)) 'FORALL) (rc-inner! eps kk tt w dl) (ass))))))))

(mac 'is-continuous-at)
(rc-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'FORALL) (rc-eps!))
           ((and (eq? (car g) 'IN) (dk-contains? g 'PTS)) (slot 'PTS) (ass))
           (else (ass))))))
(qed 'recip-continuous-at)
(topic! 'recip-continuous-at 'analysis)
(alias! 'recip-continuous-at "the reciprocal of a nowhere-zero continuous map is continuous")
