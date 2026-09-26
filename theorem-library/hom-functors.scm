;;; hom-functors.scm -- the Hom functors: Hom(a, -) covariant, Hom(-, b)
;;; contravariant, as maps on hom-sets.
;;;
;;; They are TERMS built from COMPOSE, not new functoids (batch 33, the user's
;;; brief): for a set S of functions,
;;;
;;;   POST(h, S)  =  VNB-LAMBDA hmpf_ S (COMPOSE h hmpf_)       f |-> h o f
;;;   PRE(k, S)   =  VNB-LAMBDA hmpf_ S (COMPOSE hmpf_ k)       f |-> f o k
;;;
;;; (hmf-post / hmf-pre below build them; the binder `hmpf_' is used by nothing
;;; else in the tree).  Per single-carrier structure NAME (all 26: the 22 with a
;;; generated hom, FIELD, and the three overrides), PROVEN from hom-laws.scm:
;;;
;;;   hom-NAME-post-type  IS-NAME(a) => h in HOM-NAME(b, c)
;;;                       => POST(h, HOM-NAME(a, b)) in FUN(HOM-NAME(a, b), HOM-NAME(a, c))
;;;   hom-NAME-pre-type   IS-NAME(b) => k in HOM-NAME(c, a)
;;;                       => PRE(k, HOM-NAME(a, b)) in FUN(HOM-NAME(a, b), HOM-NAME(c, b))
;;;
;;; (the one object not reached by the arrow's hom-set membership -- a for POST,
;;; b for PRE -- is a hypothesis: the domain HOM-NAME(a, b) must be a SET for the
;;; lambda to be a function, hom-NAME-in-set).  The functor laws hold ONCE, for
;;; any set S of functions, no structure involved:
;;;
;;;   post-id       a, b in SET, f in S, f in FUN(a, b)  =>  POST(ID-FUN(b), S)(f) = f
;;;   post-compose  a, b in SET, f in FUN(a, b), h in FUN(b, c), k in FUN(c, u),
;;;                 f in S, COMPOSE(h, f) in S2
;;;                 =>  POST(COMPOSE(k, h), S)(f) = POST(k, S2)(POST(h, S)(f))
;;;   pre-id        a in SET, f in S, f in FUN(a, b)  =>  PRE(ID-FUN(a), S)(f) = f
;;;   pre-compose   a, b in SET, k in FUN(a, b), h in FUN(b, c), f in FUN(c, u),
;;;                 f in S, COMPOSE(f, h) in S2
;;;                 =>  PRE(COMPOSE(h, k), S)(f) = PRE(k, S2)(PRE(h, S)(f))
;;;
;;; S2 is the set the intermediate composite lives in (for hom-sets: S =
;;; HOM(a, b), S2 = HOM(a, b') resp. HOM(a', b)); its membership is what the
;;; outer beta-reduction is licensed by, so it is a hypothesis, discharged at a
;;; hom-set by hom-NAME-post-type / -pre-type.  The laws are the POINTWISE
;;; equalities; they are compose-id-left / -right and compose-assoc
;;; (id-fun-laws.scm) under a beta step.
;;;
;;; Window: after hom-laws.scm.  Batch 33 (2026-09-25).

(define (hmf-post h s) (list 'VNB-LAMBDA 'hmpf_ s (list 'COMPOSE h 'hmpf_)))
(define (hmf-pre k s)  (list 'VNB-LAMBDA 'hmpf_ s (list 'COMPOSE 'hmpf_ k)))

(define (hmf-carrier name)
  (let* ((sd (find-shape-structure name))
         (cs (map car (filter (lambda (s) (eq? (cadr s) 'carrier)) (structure-def-slots sd)))))
    (if (= (length cs) 1) (car cs) (error "hmf-carrier: not single-carrier" name))))
(define (hmf-is name) (symbol-append 'IS- name))
(define (hmf-hom name) (structure-hom-name name))
(define (hmf-hom-def name) (symbol-append (structure-hom-name name) '-def))
(define (hmf-set name) (symbol-append 'HOM- name))
(define (hmf-thm name suffix) (symbol-append 'hom- name suffix))
(define (hmf-ctx f who)
  (or (dk-ctx-form f) (error "hom-functors: not in context --" who (expression->string f))))
(define (hmf-done! name)
  (if (proof-done? *ps*) (qed name) (error "hom-functors: failed to prove" name)))

;;; (IN (C v) SET), down the refinement chain to the shape, in a lane
(define (hmf-carrier-set! name v)
  (let ((goal (list 'IN (list (hmf-carrier name) v) 'SET)))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (let loop ((nm name))
              (let ((shape? (if (lookup-structure nm) #t #f)))
                (mac-h (if shape? (hmf-is nm) (symbol-append 'is- nm '-def))
                       (hmf-ctx (list (hmf-is nm) v) "IS-NAME"))
                (dk-split-all!)
                (if (not shape?)
                    (loop (definitional-structure-parent (lookup-definitional-structure nm))))))
            (ass))))))

;;; open f in HOM-NAME(x, y) into its typing and its hom (the membership consumed)
(define (hmf-open-member! name f x y)
  (mac-h (hmf-thm name '-member-iff) (hmf-ctx (list 'IN f (list (hmf-set name) x y)) "membership"))
  (dk-split-all!))

;;; IS-NAME(v) off IS-HOM-NAME(...) in context: its first (or second) conjunct
(define (hmf-object! name v hom)
  (if (not (dk-asm? (list (hmf-is name) v)))
      (dk-have! (list (hmf-is name) v)
        (lambda ()
          (mac-h (hmf-hom-def name) (hmf-ctx hom "the hom"))
          (dk-split-all!)
          (ass)))))

;;; the pointwise closer: (IN (COMPOSE outer inner) (HOM-NAME x z)) from the two
;;; homs in context
(define (hmf-close-composite! name x y z outer inner)
  (let* ((cacc (hmf-carrier name))
         (cx (list cacc x)) (cy (list cacc y)) (cz (list cacc z)))
    (dk-cite! (hmf-thm name '-compose) x y z inner outer)
    (dk-have! (list 'AND (list 'IN inner (list 'FUN cx cy)) (list 'IN outer (list 'FUN cy cz))))
    (dk-cite! 'compose-type cx cy cz outer inner)
    (mac (hmf-thm name '-member-iff))
    (dk-conj-close!)))

(define (hmf-prove-post-type! name)
  (let ((hs (hmf-set name)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL h
           (IMPLIES (,(hmf-is name) a) (IMPLIES (IN h (,hs b c))
             (IN ,(hmf-post 'h (list hs 'a 'b)) (FUN (,hs a b) (,hs a c)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (lam (cadr gl)) (dom (caddr lam)) (va (cadr dom)) (vb (caddr dom))
           (vh (cadr (cadddr lam))) (vc (caddr (caddr (caddr gl)))))
      (hmf-open-member! name vh vb vc)
      (hmf-object! name vb (list (hmf-hom name) vb vc vh))
      (hmf-carrier-set! name va)
      (dk-cite! (hmf-thm name '-in-set) va vb)
      (dk-lam-type!
        (lambda ()
          (let* ((landed (dk-peel!)) (vf (cadr (car landed))))
            (hmf-open-member! name vf va vb)
            (hmf-close-composite! name va vb vc vh vf)))
        (lambda () (ass)))
      (hmf-done! (hmf-thm name '-post-type)))))

(define (hmf-prove-pre-type! name)
  (let ((hs (hmf-set name)))
    (sp (make-wff `(FORALL a (FORALL b (FORALL c (FORALL k
           (IMPLIES (,(hmf-is name) b) (IMPLIES (IN k (,hs c a))
             (IN ,(hmf-pre 'k (list hs 'a 'b)) (FUN (,hs a b) (,hs c b)))))))))))
    (dk-peel!)
    (let* ((gl (dk-goal)) (lam (cadr gl)) (dom (caddr lam)) (va (cadr dom)) (vb (caddr dom))
           (vk (caddr (cadddr lam))) (vc (cadr (caddr (caddr gl)))))
      (hmf-open-member! name vk vc va)
      (hmf-object! name va (list (hmf-hom name) vc va vk))
      (hmf-object! name vc (list (hmf-hom name) vc va vk))
      (hmf-carrier-set! name vc)
      (dk-cite! (hmf-thm name '-in-set) va vb)
      (dk-lam-type!
        (lambda ()
          (let* ((landed (dk-peel!)) (vf (cadr (car landed))))
            (hmf-open-member! name vf va vb)
            (hmf-close-composite! name vc va vb vf vk)))
        (lambda () (ass)))
      (hmf-done! (hmf-thm name '-pre-type)))))

(for-each (lambda (name) (hmf-prove-post-type! name) (hmf-prove-pre-type! name))
  '(SEMIGROUP MONOID COMM-MONOID GROUP ABELIAN-GROUP
    RING COMMUTATIVE-RING INTEGRAL-DOMAIN EUCLIDEAN-RING PID FIELD-RING FIELD
    NORMED-AG NORMED-FIELD MODULE VECTOR-SPACE NORMED-VECTOR-SPACE
    COMPLEX-INNER-PRODUCT-SPACE METRIC-SPACE PSEUDOMETRIC-SPACE C-METRIC-SPACE
    MEASURABLE-SPACE MEASURE-SPACE TOP-SPACE METRIZABLE-TOP-SPACE RINGOID))

;;; --- the functor laws, once --------------------------------------------------

(define (hmf-stmt vars antes concl)
  (fold-right (lambda (v b) (list 'FORALL v b))
              (fold-right (lambda (a b) (list 'IMPLIES a b)) concl antes)
              vars))
(define (hmf-typing-of fn)
  (caddr (dk-pick (lambda (x) (and (dk-head-is? x 'IN) (equal? (cadr x) fn)
                                    (dk-head-is? (caddr x) 'FUN)))
                  "a FUN typing")))

;;; post-id: POST(ID-FUN(b), s)(f) = f
(sp (make-wff (hmf-stmt '(a b s f)
                '((IN a SET) (IN b SET) (IN f s) (IN f (FUN a b)))
                (list '= (list (hmf-post '(ID-FUN b) 's) 'f) 'f))))
(dk-peel!)
(let* ((f (caddr (dk-goal))) (ty (hmf-typing-of f)))
  (dk-lam-b!)
  (dk-cite! 'compose-id-left (cadr ty) (caddr ty) f)
  (ass))
(hmf-done! 'post-id)

;;; pre-id: PRE(ID-FUN(a), s)(f) = f
(sp (make-wff (hmf-stmt '(a b s f)
                '((IN a SET) (IN f s) (IN f (FUN a b)))
                (list '= (list (hmf-pre '(ID-FUN a) 's) 'f) 'f))))
(dk-peel!)
(let* ((f (caddr (dk-goal))) (ty (hmf-typing-of f)))
  (dk-lam-b!)
  (dk-cite! 'compose-id-right (cadr ty) (caddr ty) f)
  (ass))
(hmf-done! 'pre-id)

;;; post-compose: POST(k o h, s)(f) = POST(k, s2)(POST(h, s)(f))
(sp (make-wff (hmf-stmt '(a b c u s s2 f h k)
                '((IN a SET) (IN b SET) (IN f (FUN a b)) (IN h (FUN b c)) (IN k (FUN c u))
                  (IN f s) (IN (COMPOSE h f) s2))
                (list '= (list (hmf-post '(COMPOSE k h) 's) 'f)
                         (list (hmf-post 'k 's2) (list (hmf-post 'h 's) 'f))))))
(dk-peel!)
(let* ((outer (cadr (dk-goal)))                  ; (POST(k o h, s) f)
       (f (cadr outer)) (kh (cadr (cadddr (car outer)))) (k (cadr kh)) (h (caddr kh))
       (fab (hmf-typing-of f)) (fbc (hmf-typing-of h)) (fcu (hmf-typing-of k)))
  (dk-lam-b!)
  (let ((e (dk-cite! 'compose-assoc (cadr fab) (caddr fab) (caddr fbc) (caddr fcu) f h k)))
    (dk-cite! 'eq-sym (cadr e) (caddr e))
    (ass)))
(hmf-done! 'post-compose)

;;; pre-compose: PRE(h o k, s)(f) = PRE(k, s2)(PRE(h, s)(f))
(sp (make-wff (hmf-stmt '(a b c u s s2 f h k)
                '((IN a SET) (IN b SET) (IN k (FUN a b)) (IN h (FUN b c)) (IN f (FUN c u))
                  (IN f s) (IN (COMPOSE f h) s2))
                (list '= (list (hmf-pre '(COMPOSE h k) 's) 'f)
                         (list (hmf-pre 'k 's2) (list (hmf-pre 'h 's) 'f))))))
(dk-peel!)
(let* ((outer (cadr (dk-goal)))                  ; (PRE(h o k, s) f)
       (f (cadr outer)) (hk (caddr (cadddr (car outer)))) (h (cadr hk)) (k (caddr hk))
       (fab (hmf-typing-of k)) (fbc (hmf-typing-of h)) (fcu (hmf-typing-of f)))
  (dk-lam-b!)
  (dk-cite! 'compose-assoc (cadr fab) (caddr fab) (caddr fbc) (caddr fcu) k h f)
  (ass))
(hmf-done! 'pre-compose)
