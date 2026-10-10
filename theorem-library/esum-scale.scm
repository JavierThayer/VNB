;;; ====================================================================
;;; theorem-library/esum-scale.scm -- MEASURE-5-A, 2026-10-10.
;;; Homogeneity of ESUM, and a scaled measure is a measure.
;;;
;;; THE THEOREMS (every one `modulo 0'):
;;;   esum-scale-ptwise   c real >= 0, g, h in FUN(D, [0,+inf]), h(z) = c g(z) on D
;;;                       ==> ESUM(h) = c ESUM(g)                (products by etimes)
;;;   esum-scale          c real >= 0, f in FUN(D, [0,+inf])
;;;                       ==> ESUM(z |-> c f(z)) = c ESUM(f)
;;;   measure-scale       IS-MEASURE(X, cA, mu), c real >= 0
;;;                       ==> IS-MEASURE(X, cA, es |-> c mu(es))
;;;                       (the binder is spelled msx_, not es: the corollary in
;;;                       lebesgue-translation-invariant.scm instantiates this with a free
;;;                       variable es in context, and a binder es beside it draws the
;;;                       kernel's "bound and free" warning)
;;;
;;; THE ROUTE.  ESUM(f) is the ESUP of the finite partial sums (structure-library/
;;; extended-sum.scm), so everything goes through esum-upper / esum-least.  A partial
;;; sum of h is c times the partial sum of g (rps-finsum-scale-ptwise), and
;;; multiplication by c is monotone (etimes-mono-left):
;;;   ESUM(h) <= c ESUM(g)   each partial sum of h is c (a partial sum of g) <= c ESUM(g);
;;;   c ESUM(g) <= ESUM(h)   for c = 0 the left side is 0 (etimes-zero-left: the tree's
;;;                          convention 0 * (+inf) = 0, so NO guard is needed at c = 0);
;;;                          for c > 0 put r = recip(c): each partial sum of g is
;;;                          r (c (partial sum of g)) = r (partial sum of h) <= r ESUM(h)
;;;                          (etimes-assoc-real, etimes-one-left), so ESUM(g) <= r ESUM(h)
;;;                          and c ESUM(g) <= c (r ESUM(h)) = ESUM(h).
;;; measure-scale: the four conjuncts of IS-MEASURE; countable additivity is
;;; esum-scale-ptwise at D = NN.
;;;
;;; LOAD WINDOW: after "theorem-library/integral-laws" (load.scm 3387), which proves
;;; rps-finsum-scale-ptwise, etimes-mono-left, etimes-assoc-real, etimes-one-left and
;;; etimes-zero-right; esum-in / esum-upper / esum-least are rake-esum-defined (1315);
;;; everything else earlier.  libraries.sexp: library measure.
;;; ====================================================================

(define esc-m 'RR-POS-STAR-ADD-MONOID)
(define (esc-fs f s) (list 'FINSUM esc-m f s))

;;; (IN c RR-POS-STAR) from (IN c RR), (<= 0 c)
(define (esc-rps! c)
  (if (not (dk-asm? (list 'IN c 'RR-POS-STAR)))
      (let ((inst (dk-cite! 'rr-pos-star-membership c)))
        (dk-have! (list 'IN c 'RR-POS-STAR)
          (lambda () (dk-only! inst (list 'IN c 'RR) (list '<= 0 c)) (prop))))))

;;; the conjunction of P ..., each in context
(define (esc-and! . ps)
  (let ((f (let build ((l ps)) (if (null? (cdr l)) (car l) (list 'AND (car l) (build (cdr l)))))))
    (dk-have! f (lambda () (dk-conj-close! dk-ass!)))
    f))

;;; cite THM at ARGS; detach every antecedent (each in context); return the consequent
(define (esc-cite! thm . args)
  (let loop ((r (apply dk-cite! thm args)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (if (dk-asm? (caddr r))
            (loop (caddr r))
            (loop (dk-landed-1 (lambda () (detach! r)))))
        r)))

;;; (IN x y) typed etimes term from x, y in RR-POS-STAR in context
(define (esc-et! x y)
  (let ((ty (list 'IN (list 'etimes x y) 'RR-POS-STAR)))
    (if (not (dk-asm? ty))
        (begin (esc-and! (list 'IN x 'RR-POS-STAR) (list 'IN y 'RR-POS-STAR))
               (fact 'etimes-closed x y)))
    ty))

;;; f in FUN(dd, RR-POS-STAR) in context: land (IN dd SET), (= (DOM f) dd) and
;;; (IN f (FUN (DOM f) RR-POS-STAR)), the shape the ESUM laws want
(define (esc-dom! f dd)
  (let ((ty (list 'IN f (list 'FUN dd 'RR-POS-STAR))))
    (if (not (dk-asm? (list 'IN dd 'SET)))
        (fact 'fun-domain-in-set dd 'RR-POS-STAR f))
    (dk-project! (list 'IN f (list 'FUN dd)) 'fun-codomain-iff ty)
    (esc-and! (list 'IN f (list 'FUN dd)) (list 'IN dd 'SET))
    (fact 'dom-of-fun dd f)
    (let ((dd2 (dk-ctx-form (list 'AND (list 'IN (list 'DOM f) 'SET) (list '= (list 'DOM f) dd)))))
      (if dd2 (dk-split-all! (list dd2))))
    (dk-have! (list 'IN f (list 'FUN (list 'DOM f) 'RR-POS-STAR))
      (lambda () (subst (list '= (list 'DOM f) dd)) (ass)))))

;;; the partial-sum bound esum-least wants: every finite S inside DOM f has
;;; FINSUM(f, S) <= b
(define (esc-bound f b)
  (list 'FORALL 's
    (list 'IMPLIES (list 'AND '(IN s SET) (list 'AND '(IN (CARD s) NN) (list 'SUBSET 's (list 'DOM f))))
          (list '<= (esc-fs f 's) b))))

;;; inside the bound's proof for F (one of g, h): peel S, return it, with
;;; (SUBSET S dd), the finiteness guards, and the two partial sums typed and
;;; FINSUM(h, S) = c FINSUM(g, S) landed
(define (esc-partial! dd)
  (dk-peel!)
  (dk-split-all!)
  (let* ((sv (cadddr (cadr (dk-goal))))
         (ptw '(FORALL z_ (IMPLIES (IN z_ dd) (= (h z_) (etimes c (g z_)))))))
    (for-each
      (lambda (f)
        (if (dk-asm? (list 'SUBSET sv (list 'DOM f)))
            (dk-rewrite-h! (list 'SUBSET sv (list 'DOM f)) (list 'DOM f) dd)))
      '(g h))
    (for-each
      (lambda (f)
        (if (not (dk-asm? (list 'SUBSET sv (list 'DOM f))))
            (dk-rewrite-h! (list 'SUBSET sv dd) dd (list 'DOM f)))
        (let ((fin (esc-and! (list 'IN sv 'SET) (list 'IN (list 'CARD sv) 'NN) (list 'SUBSET sv (list 'DOM f)))))
          (esc-cite! 'esum-partial-sum-type f sv)
          (esc-cite! 'esum-upper f sv)))
      '(g h))
    (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ sv) '(IN (g z_) RR-POS-STAR)))
      (lambda ()
        (let ((zv (dk-di-var!)))
          (fact 'subset-mem-fwd sv dd zv)
          (fact 'fun-apply-type-c 'g dd 'RR-POS-STAR zv)
          (ass))))
    (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ sv) '(= (h z_) (etimes c (g z_)))))
      (lambda ()
        (let ((zv (dk-di-var!)))
          (fact 'subset-mem-fwd sv dd zv)
          (dk-apply! ptw zv)
          (ass))))
    (esc-cite! 'rps-finsum-scale-ptwise 'c sv 'g 'h)
    sv))

(sp (make-wff '(FORALL c (IMPLIES (IN c RR) (IMPLIES (<= 0 c)
   (FORALL dd (FORALL g (FORALL h
     (IMPLIES (IN g (FUN dd RR-POS-STAR))
     (IMPLIES (IN h (FUN dd RR-POS-STAR))
     (IMPLIES (FORALL z_ (IMPLIES (IN z_ dd) (= (h z_) (etimes c (g z_)))))
        (= (ESUM h) (etimes c (ESUM g))))))))))))))
(dk-peel!)
(esc-rps! 'c)
(esc-dom! 'g 'dd)
(esc-dom! 'h 'dd)
(fact 'esum-in 'g)
(fact 'esum-in 'h)
(let* ((eg '(ESUM g)) (eh '(ESUM h)) (ceg (list 'etimes 'c eg)))
  (esc-et! 'c eg)
  ;; (a) ESUM(h) <= c ESUM(g)
  (dk-have! (list '<= eh ceg)
    (lambda ()
      (dk-have! (esc-bound 'h ceg)
        (lambda ()
          (let* ((sv (esc-partial! 'dd))
                 (fg (esc-fs 'g sv)) (fh (esc-fs 'h sv)))
            (esc-and! (list 'IN fg 'RR-POS-STAR) (list 'IN eg 'RR-POS-STAR))
            (esc-cite! 'etimes-mono-left 'c fg eg)
            (subst (list '= fh (list 'etimes 'c fg)))
            (ass))))
      (esc-and! (list 'IN ceg 'RR-POS-STAR) (esc-bound 'h ceg))
      (esc-cite! 'esum-least 'h ceg)
      (ass)))
  ;; (b) c ESUM(g) <= ESUM(h)
  (dk-have! (list '<= ceg eh)
    (lambda ()
      (use-em '(= c 0)
        (lambda ()
          (fact 'etimes-zero-left eg)
          (dk-have! (list '= ceg 0) (lambda () (subst '(= c 0)) (ass)))
          (subst (list '= ceg 0))
          (fact 'rr-pos-star-nonneg eh)
          (ass))
        (lambda ()
          (dk-have! '(< 0 c)
            (lambda ()
              (mac '<)
              (dk-conj-close!
                (lambda ()
                  (if (not (dk-ass!))
                      (begin (di)
                             (fact 'equality-symmetry 0 'c)
                             (dk-only! '(= c 0) '(NOT (= c 0)))
                             (prop)))))))
          (let* ((r '(recip c)) (reh (list 'etimes r eh)))
            (esc-and! '(IN c RR) '(NOT (= c 0)))
            (fact 'rr-recip-closed 'c)
            (fact 'rr-recip-pos 'c)
            (fact 'rr-recip-inverse 'c)
            (dk-have! '(IN 0 RR) (lambda () (type-term)))
            (fact 'rr-lt-implies-le 0 r)
            (esc-rps! r)
            (esc-and! (list 'IN r 'RR) '(IN c RR))
            (fact 'rr-mul-comm r 'c)
            (dk-have! (list '= (list '* r 'c) 1)
              (lambda () (subst (list '= (list '* r 'c) (list '* 'c r))) (ass)))
            (esc-et! r eh)
            ;; ESUM(g) <= r ESUM(h)
            (dk-have! (esc-bound 'g reh)
              (lambda ()
                (let* ((sv (esc-partial! 'dd))
                       (fg (esc-fs 'g sv)) (fh (esc-fs 'h sv)))
                  (esc-and! (list 'IN fh 'RR-POS-STAR) (list 'IN eh 'RR-POS-STAR))
                  (let* ((l0 (esc-cite! 'etimes-mono-left r fh eh))
                         (l1 (dk-rewrite-h! l0 fh (list 'etimes 'c fg)))
                         (as (esc-cite! 'etimes-assoc-real r 'c fg))
                         (l2 (dk-rewrite-h! l1 (cadr as) (caddr as)))
                         (l3 (dk-rewrite-h! l2 (list '* r 'c) 1))
                         (one (esc-cite! 'etimes-one-left fg))
                         (l4 (dk-rewrite-h! l3 (cadr one) (caddr one))))
                    (ass)))))
            (esc-and! (list 'IN reh 'RR-POS-STAR) (esc-bound 'g reh))
            (esc-cite! 'esum-least 'g reh)
            (esc-and! (list 'IN eg 'RR-POS-STAR) (list 'IN reh 'RR-POS-STAR))
            (let* ((l0 (esc-cite! 'etimes-mono-left 'c eg reh))
                   (as (esc-cite! 'etimes-assoc-real 'c r eh))
                   (l1 (dk-rewrite-h! l0 (cadr as) (caddr as)))
                   (l2 (dk-rewrite-h! l1 (list '* 'c r) 1))
                   (one (esc-cite! 'etimes-one-left eh))
                   (l3 (dk-rewrite-h! l2 (cadr one) (caddr one))))
              (ass)))))))
  (esc-and! (list 'IN eh 'RR-POS-STAR) (list 'IN ceg 'RR-POS-STAR))
  (esc-and! (list '<= eh ceg) (list '<= ceg eh))
  (fact 'rr-pos-star-le-antisymm eh ceg)
  (ass))
(qed 'esum-scale-ptwise)
(topic! 'esum-scale-ptwise 'analysis)

(sp (make-wff '(FORALL c (IMPLIES (IN c RR) (IMPLIES (<= 0 c)
   (FORALL dd (FORALL f (IMPLIES (IN f (FUN dd RR-POS-STAR))
     (= (ESUM (VNB-LAMBDA esz_ dd (etimes c (f esz_)))) (etimes c (ESUM f)))))))))))
(dk-peel!)
(esc-rps! 'c)
(fact 'fun-domain-in-set 'dd 'RR-POS-STAR 'f)
(let ((lam '(VNB-LAMBDA esz_ dd (etimes c (f esz_)))))
  (dk-have! (list 'IN lam '(FUN dd RR-POS-STAR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((zv (dk-di-var!)))
            (fact 'fun-apply-type-c 'f 'dd 'RR-POS-STAR zv)
            (esc-et! 'c (list 'f zv))
            (ass)))
        (lambda () (ass)))))
  (dk-have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ dd) (list '= (list lam 'z_) '(etimes c (f z_)))))
    (lambda ()
      (let ((zv (dk-di-var!)))
        (fact 'fun-apply-type-c 'f 'dd 'RR-POS-STAR zv)
        (esc-et! 'c (list 'f zv))
        (if (not (dk-lam-b!)) (rfl)))))
  (esc-cite! 'esum-scale-ptwise 'c 'dd 'f lam)
  (ass))
(qed 'esum-scale)
(topic! 'esum-scale 'analysis)

;;; ====================================================================
;;; a scaled measure is a measure
;;; ====================================================================

(define (esc-disj m)
  (forall-guarded '(i_ j_) '((IN i_ NN) (IN j_ NN) (NOT (= i_ j_)))
    '(= (INTERSECTION (f_ i_) (f_ j_)) EMPTY-SET)))
(define (esc-add m)
  (forall-guarded '(f_) (list '(IN f_ (FUN NN cA)) (esc-disj m))
    (list '= (list m '(BIG-UNION n_ NN (f_ n_)))
          (list 'ESUM (list 'VNB-LAMBDA 'n_ 'NN (list m '(f_ n_)))))))

(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (IMPLIES (IS-MEASURE omega cA mu)
   (FORALL c (IMPLIES (IN c RR) (IMPLIES (<= 0 c)
     (IS-MEASURE omega cA (VNB-LAMBDA msx_ cA (etimes c (mu msx_)))))))))))))
(dk-peel!)
(esc-rps! 'c)
(let* ((ism '(IS-MEASURE omega cA mu))
       (nu '(VNB-LAMBDA msx_ cA (etimes c (mu msx_))))
       (sa '(IS-SIGMA-ALGEBRA omega cA)))
  (dk-project! sa 'IS-MEASURE ism)
  (dk-project! '(IN mu (FUN cA RR-POS-STAR)) 'IS-MEASURE ism)
  (dk-project! '(= (mu EMPTY-SET) 0) 'IS-MEASURE ism)
  (dk-project! (esc-add 'mu) 'IS-MEASURE ism)
  (fact 'fun-domain-in-set 'cA 'RR-POS-STAR 'mu)
  (fact 'nn-is-set)
  ;; nu is a [0,+inf]-valued function on cA
  (dk-have! (list 'IN nu '(FUN cA RR-POS-STAR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((zv (dk-di-var!)))
            (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR zv)
            (esc-et! 'c (list 'mu zv))
            (ass)))
        (lambda () (ass)))))
  ;; nu(empty) = 0
  (fact 'sigma-algebra-empty-in 'omega 'cA)
  (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR 'EMPTY-SET)
  (esc-et! 'c '(mu EMPTY-SET))
  (dk-have! (list '= (list nu 'EMPTY-SET) 0)
    (lambda ()
      (dk-lam-b!)
      (subst '(= (mu EMPTY-SET) 0))
      (fact 'etimes-zero-right 'c)
      (ass)))
  ;; countable additivity
  (dk-have! (esc-add nu)
    (lambda ()
      (let* ((landed (dk-peel!))
             (fv (cadr (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) '(FUN NN cA)))) landed)))
             (bu (list 'BIG-UNION 'n_ 'NN (list fv 'n_)))
             (gl (list 'VNB-LAMBDA 'n_ 'NN (list 'mu (list fv 'n_))))
             (hl (cadr (caddr (dk-goal))))
             (mbu (list 'mu bu)))
        (fact 'sigma-algebra-union-closed 'omega 'cA fv)
        (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR bu)
        (esc-et! 'c mbu)
        (dk-apply! (esc-add 'mu) fv)
        (dk-have! (list 'IN gl '(FUN NN RR-POS-STAR))
          (lambda ()
            (dk-lam-type!
              (lambda ()
                (let ((kv (dk-di-var!)))
                  (fact 'fun-apply-type-c fv 'NN 'cA kv)
                  (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR (list fv kv))
                  (ass)))
              (lambda () (ass)))))
        (dk-have! (list 'IN hl '(FUN NN RR-POS-STAR))
          (lambda ()
            (dk-lam-type!
              (lambda ()
                (let ((kv (dk-di-var!)))
                  (fact 'fun-apply-type-c fv 'NN 'cA kv)
                  (fact 'fun-apply-type-c nu 'cA 'RR-POS-STAR (list fv kv))
                  (ass)))
              (lambda () (ass)))))
        (dk-have! (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ NN) (list '= (list hl 'z_) (list 'etimes 'c (list gl 'z_)))))
          (lambda ()
            (let ((zv (dk-di-var!)))
              (fact 'fun-apply-type-c fv 'NN 'cA zv)
              (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR (list fv zv))
              (esc-et! 'c (list 'mu (list fv zv)))
              (if (not (dk-lam-b!)) (rfl)))))
        (let ((sc (esc-cite! 'esum-scale-ptwise 'c 'NN gl hl)))
          (dk-have! (list '= (list nu bu) (list 'etimes 'c mbu))
            (lambda () (if (not (dk-lam-b!)) (rfl))))
          (subst (list '= (list nu bu) (list 'etimes 'c mbu)))
          (subst sc)
          (subst (list '= (list 'ESUM gl) mbu))
          (rfl)))))
  (mac 'IS-MEASURE)
  (dk-conj-close! dk-ass!))
(qed 'measure-scale)
(topic! 'measure-scale 'analysis)

(gloss! 'esum-scale
  "Homogeneity of the extended sum: for a real c >= 0 and a [0,+inf]-valued family f,
   the sum of c f(z) is c times the sum of f (with 0 times +inf = 0).")
(gloss! 'measure-scale
  "A measure multiplied by a real constant c >= 0 is again a measure on the same sigma-algebra.")
