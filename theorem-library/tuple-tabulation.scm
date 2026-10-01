;;; tuple-tabulation.scm -- TABULATION: the missing generation principle for
;;; tuples and matrices, and the honest replacement for `matof-exists'.
;;;
;;; WHAT IS PROVED HERE (eleven theorems, every one `modulo 0'):
;;;
;;;   tab-succ-add             succ(a) + b = succ(a + b)          [local copy]
;;;   tuple-tabulation-offset  forall n in NN, A, f, k in NN.
;;;                              (forall i in [1,n]. f(k+i) in A)
;;;                              => forsome L in TUPLES(A). LENGTH(L) = n
;;;                                 and forall i in [1,n]. NTH(i,L) = f(k+i)
;;;   tuple-tabulation         the same at k = 0 -- THE LIST TABULATION LEMMA
;;;   row-tabulation-offset    the same with a two-argument entry map g(c,k+j)
;;;   row-tabulation           the same at k = 0
;;;   matrix-tabulation        forall m in NN, A, g, n in NN, k in NN.
;;;                              (forall i in [1,m], j in [1,n]. g(k+i,j) in A)
;;;                              => forsome P in TUPLES(TUPLES A). LENGTH(P) = m
;;;                                 and every row has length n
;;;                                 and NTH(j,NTH(i,P)) = g(k+i,j)
;;;   mat-tabulation-exists    the same delivered as membership in MAT(m,n,X)
;;;   matof-exists-image       the same with X = IMAGE(g, [1,m] x [1,n])
;;;   entry-of-matof-guarded   ENTRY(MATOF(m,n,g), i, j) = g(i,j)
;;;   matof-exists             the CANONICAL name, guarded on m, n in NN only:
;;;                            [] for m = 0, matof-exists-image otherwise
;;;                            (see the block at the end)
;;;   entry-of-matof           the CANONICAL name, guarded on m, n in NN only:
;;;                            entry-of-matof-guarded, 1 <= m read off the index
;;;
;;; ---------------------------------------------------------------------
;;; WHY THIS FILE EXISTS: `matof-exists' WAS FALSE
;;;
;;; Until 2026-09-16 `matof-exists' was an asserted support in
;;; structure-library/matrix.scm with UNQUANTIFIED dimensions --
;;;
;;;   forall m, n, g. forsome P. P in MAT(m,n,IMAGE(g,box)) and ...
;;;
;;; -- and `mat-rows-in-nn' (theorem-library/mat-basics.scm) reads `m in NN'
;;; out of any member of MAT(m,n,X).  So the support proved `forall m. m in NN',
;;; hence `ORD in NN', hence by `membership-implies-sethood' `ORD in SET',
;;; against `burali-forti'.  FALSITY in twelve lines; measured on the band
;;; 2026-09-15 (the probe is scratchpad/mx/mx-probe3.scm).  `entry-of-matof'
;;; was unguarded the same way.  Both are now THEOREMS (the block at the end of
;;; this file) with these hypotheses, each necessary:
;;;
;;;   (IN m NN), (IN n NN)   the dimensions of a matrix are natural numbers
;;;                          (mat-rows-in-nn, mat-cols-in-nn).
;;;   definedness of g       `=' is the definedness predicate and
;;;                          `image-membership-iff' puts g(x) in IMAGE(g,S) only
;;;                          when g(x) is DEFINED.  An arbitrary applied variable
;;;                          g need not be.  It is supplied as `(IN (g i j) SET)'
;;;                          on the index box -- exactly what `rfl' accepts as a
;;;                          definedness witness -- and at the MAT-level form as
;;;                          the stronger `(IN (g i j) X)', which is the
;;;                          hypothesis matof-in-mat already carries.
;;;
;;; The twins proved first in this file (`mat-tabulation-exists',
;;; `matof-exists-image', `entry-of-matof-guarded') carry a THIRD hypothesis,
;;; `(<= 1 m)': they build the matrix row by row and read the column count off
;;; row 1.  Under the definitions in force until 2026-09-16 that hypothesis was
;;; FORCED -- SIZE(P) was [LENGTH P, LENGTH(NTH 1 P)], NTH(1,[]) is out of
;;; range, and MAT(0,n,X) could be shown neither inhabited nor empty -- and
;;; the canonical names could not be installed without it, which stranded
;;; `spans-fg-base' (its witness is MATOF(0, 1, ...)).  matrix.scm now makes
;;; SIZE total and MAT's membership vacuous in the column count at zero rows,
;;; so [] is in MAT(0,n,X) for every natural n (`nil-in-mat') and the canonical
;;; statements drop `1 <= m' by a case split on m = 0.
;;;
;;; `entry-of-matof-guarded' spells its outer index binders `u_' `v_': the old
;;; support spelled them `i' `j', which are also MATOF's own IOTA binders, so
;;; the unfolded goal carries two distinct variables spelled `i' and two
;;; spelled `j' (validate-wff! says so; CLAUDE.md, "Case folding", rule 4).
;;; The canonical `entry-of-matof' keeps the old spelling, for its citers.
;;;
;;; ---------------------------------------------------------------------
;;; THE PROOF, and the one design decision in it
;;;
;;; Everything is one induction, run five times through ONE driver.  The tuple is
;;; built by PREPENDING -- CONS puts the new entry at index 1 and shifts the rest
;;; up (nth-cons-1, nth-cons-succ) -- because CONS is the only tuple constructor
;;; the theory has: there is no APPEND and no snoc, and `INSERT-LAST' (finsum.scm)
;;; cannot serve (its lambda has domain NN).  Appending would have been the
;;; direction that needs no re-indexing; prepending needs the tabulated map to be
;;; SHIFTED by one at every step, and that is the whole difficulty.
;;;
;;; The shift is carried in the ARITHMETIC, not in the function.  The lemma
;;; tabulates  i |-> f(k+i)  with an explicit offset k, and the step applies the
;;; induction hypothesis at k := succ k, using
;;;
;;;     succ(k) + i  =  succ(k + i)  =  k + succ(i)
;;;
;;; (tab-succ-add, nn-add-succ).  The alternative -- instantiating the induction
;;; hypothesis at "the function i |-> f(i+1)" -- is not available: VNB has no
;;; term former for it that beta-reduces under an arbitrary applied variable, and
;;; application is NOT curried, so partial application does not build one either
;;; (`(g(a))(j)' and `g(a,j)' are different terms; checked, and `qrfl' refuses
;;; the equation).  That is also why the two-index `row-tabulation' is a separate
;;; statement rather than an instance of `tuple-tabulation': neither is an
;;; instance of the other, so the file shares the DRIVER instead of the statement.
;;; The driver reads the entry template off the GOAL -- it is
;;; `(head arg1 ... argN (+ k i))' in both -- so `tb-step!' and `tb-base!' are
;;; written once and used for both shapes.
;;;
;;; The index case split in the step is `i = 1' or `i = succ q with 1 <= q <= n',
;;; by nn-pos-is-succ then nn-zero-or-succ.  `q <= n' is derived from
;;; `succ q <= succ n' through nn-le-succ-cases rather than through
;;; `nn-succ-le-cancel', which is an asserted support (order-lemmas.scm:345):
;;; the two-case detour costs ten lines and keeps the bill at `modulo 0'.
;;;
;;; ---------------------------------------------------------------------
;;; LOAD WINDOW: after theorem-library/tuple-extensionality (entry-unfold and
;;; matrix-entry-extensionality, the latest citations) and before
;;; theorem-library/matof-in-mat -- i.e. between them, load.scm:1010/1011.
;;; Nothing cites these theorems yet, so the upper end is free; that slot is
;;; where matof-in-mat would cite them if it is rewired (see the report).
;;; Also needs, all far above: list-recursion (CONS), nn-arith (nn-add-succ),
;;; nn-order-ord, nn-order-basics, nn-order-via-rr, nn-parity-proof,
;;; nn-pos-is-succ, interval-membership, pair-tuple-sethood, equality-basics,
;;; mat-basics, axioms (apply-tupling-2).  It deliberately does NOT cite
;;; nn-pairing: that file loads BELOW matof-in-mat, which is why `tab-succ-add'
;;; is proved here.  (nn-pairing had its own copy, `nn-succ-add'; that
;;; duplicate was removed 2026-09-20 and nn-pairing cites this one.)
;;;
;;; Helper prefixes: tb- (tuples), mtb- (matrices), mte- (MAT), eom- (ENTRY).
;;; ---------------------------------------------------------------------

;;; ---- helpers (tb- prefix) --------------------------------------------

(define (tb-final f)
  (if (and (pair? f) (memq (car f) '(FORALL IMPLIES))) (tb-final (caddr f)) f))

(define (tb-rep t old new)
  (cond ((equal? t old) new)
        ((pair? t) (map (lambda (u) (tb-rep u old new)) t))
        (#t t)))

;; the (+ OFF IV) subterm of E -- the offset index, wherever it sits.
(define (tb-plus e iv)
  (let loop ((t e))
    (if (pair? t)
        (if (and (eq? (car t) '+) (= (length t) 3) (equal? (caddr t) iv))
            t
            (let scan ((l (cdr t)))
              (if (null? l) #f (or (loop (car l)) (scan (cdr l))))))
        #f)))

(define (tb-guard v hi)
  (list 'AND (list 'IN v 'NN) (list 'AND (list '<= 1 v) (list '<= v hi))))

(define (tb-hyp iv hi e aa)
  (list 'FORALL iv (list 'IMPLIES (tb-guard iv hi) (list 'IN e aa))))

;; have! a conjunction all of whose conjuncts are in context, closed by `ass'
;; alone (the default closer sends (IN 1 NN) to the arith ORACLE, which would
;; then appear on the bill).
(define (tb-and! f) (have! f (lambda () (dk-conj-close! (lambda () (ass))))))

;; the FORSOME goal, taken apart:  (L A N IV E)
(define (tb-goal-parts)
  (let ((g (dk-goal)))
    (if (not (eq? (car g) 'FORSOME)) (error "tb-goal-parts: not a FORSOME" g))
    (let* ((lv   (cadr g))
           (body (caddr g))
           (aa   (cadr (caddr (cadr body))))
           (rest (caddr body))
           (nt   (caddr (cadr rest)))
           (univ (caddr rest))
           (iv   (cadr univ))
           (e    (caddr (caddr (caddr univ)))))
      (list lv aa nt iv e))))

(define (tb-typed-var landed)
  (let ((f (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN)))
                       landed)))
    (if (not f) (error "tb-typed-var: no (IN v NN) among" landed))
    (cadr f)))

;;; ---- base:  n = 0, the empty tuple ------------------------------------

(define (tb-base!)
  (let ((aa (cadr (tb-goal-parts))))
    (fact 'empty-in-tuples aa)
    (fact 'length-of-empty)
    (ew '(LIST))
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (if (eq? (car g) 'FORALL)
             (let* ((landed (dk-split-all! (dk-peel!)))
                    (i0     (tb-typed-var landed)))
               (fact 'nn-not-le-zero-pos i0)
               (ai (list 'NOT (list '<= i0 0))))
             (ass)))))))

;;; ---- step ------------------------------------------------------------

;; the shifted membership hypothesis: E with offset succ k, over [1, nv]
(define (tb-shift-hyp! hyp k0 nv)
  (let* ((landed (dk-split-all! (dk-peel!)))
         (j      (tb-typed-var landed)))
    (fact 'nn-succ-closed j)
    (fact 'nn-one-le-succ j)
    (fact 'nn-succ-mono j nv)
    (tb-and! (tb-guard (list 'succ j) (list 'succ nv)))
    (dk-apply! hyp (list 'succ j))
    (fact 'tab-succ-add k0 j)
    (fact 'nn-add-succ k0 j)
    (fact 'eq-sym (list '+ k0 (list 'succ j)) (list 'succ (list '+ k0 j)))
    (subst (list '= (list '+ (list 'succ k0) j) (list 'succ (list '+ k0 j))))
    (subst (list '= (list 'succ (list '+ k0 j)) (list '+ k0 (list 'succ j))))
    (ass)))

;;   q <= nv  from  i = succ q  and  i <= succ nv,  without nn-succ-le-cancel.
(define (tb-q-le! i0 q0 nv)
  (let ((disj (dk-fact! 'nn-le-succ-cases nv i0)))
    (use-cases disj
      (lambda ()                                     ; i0 <= nv
        (fact 'nn-le-succ q0)
        (have! (list '<= q0 i0)
               (lambda () (subst (list '= i0 (list 'succ q0))) (ass)))
        (fact 'nn-le-trans-guarded q0 i0 nv)
        (ass))
      (lambda ()                                     ; i0 = succ nv
        (fact 'eq-sym i0 (list 'succ q0))
        (have! (list '= (list 'succ q0) (list 'succ nv))
               (lambda () (subst (list '= (list 'succ q0) i0)) (ass)))
        (fact 'nn-succ-inj q0 nv)
        (fact 'nn-le-refl nv)
        (subst (list '= q0 nv))
        (ass)))))

(define (tb-entries! h m0 nv k0 entu)
  (let* ((landed (dk-split-all! (dk-peel!)))
         (i0     (tb-typed-var landed))
         (ex     (dk-fact! 'nn-pos-is-succ i0))
         (q0     (dk-skolem! ex)))
    (have! (list '<= q0 nv) (lambda () (tb-q-le! i0 q0 nv)))
    (use-cases (dk-fact! 'nn-zero-or-succ q0)
      (lambda ()                                     ; q0 = 0, so i0 = 1
        (fact 'nn-one-is-succ-zero)
        (fact 'eq-sym 1 '(succ 0))
        (have! (list '= i0 1)
               (lambda () (subst (list '= i0 (list 'succ q0)))
                          (subst (list '= q0 0))
                          (ass)))
        (subst (list '= i0 1))
        (fact 'nth-cons-1 h m0)
        (ass))
      (lambda ()                                     ; q0 = succ r, so 1 <= q0
        (let* ((ex2 (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)))
                             "the predecessor of q0"))
               (r0  (dk-skolem! ex2)))
          (fact 'nn-one-le-succ r0)
          (have! (list '<= 1 q0)
                 (lambda () (subst (list '= q0 (list 'succ r0))) (ass)))
          (have! (list '<= q0 (list 'LENGTH m0))
                 (lambda () (subst (list '= (list 'LENGTH m0) nv)) (ass)))
          (tb-and! (tb-guard q0 (list 'LENGTH m0)))
          (fact 'nth-cons-succ q0 h m0)
          (tb-and! (tb-guard q0 nv))
          (dk-apply! entu q0)
          (fact 'nn-add-succ k0 q0)
          (fact 'tab-succ-add k0 q0)
          (fact 'eq-sym (list '+ (list 'succ k0) q0) (list 'succ (list '+ k0 q0)))
          (subst (list '= i0 (list 'succ q0)))
          (subst (list '= (list 'NTH (list 'succ q0) (list 'CONS h m0))
                        (list 'NTH q0 m0)))
          (subst (list '= (list '+ k0 (list 'succ q0)) (list 'succ (list '+ k0 q0))))
          (subst (list '= (list 'succ (list '+ k0 q0)) (list '+ (list 'succ k0) q0)))
          (ass))))))

(define (tb-step!)
  (let* ((p    (tb-goal-parts))
         (aa   (cadr p)) (nt (caddr p)) (iv (cadddr p)) (e (car (cddddr p)))
         (nv   (cadr nt))
         (plus (tb-plus e iv))
         (k0   (cadr plus))
         (sk   (list 'succ k0))
         (ep   (tb-rep e plus (list '+ sk iv)))
         (h    (tb-rep e iv 1))
         (args (reverse (cdr (reverse e))))
         (ih   (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (pair? (tb-final f))
                                         (eq? (car (tb-final f)) 'FORSOME)))
                        "the induction hypothesis"))
         (hyp  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (let ((c (tb-final f)))
                                           (and (pair? c) (eq? (car c) 'IN)
                                                (equal? (caddr c) aa)))))
                        "the entry-membership hypothesis")))
    (fact 'nn-succ-closed k0)
    (have! (tb-hyp iv nv ep aa) (lambda () (tb-shift-hyp! hyp k0 nv)))
    (let* ((ihres (apply dk-apply! ih (append (list aa) args (list sk))))
           (m0    (dk-skolem! ihres))
           (entu  (dk-pick (lambda (f)
                             (and (pair? f) (eq? (car f) 'FORALL)
                                  (let ((c (tb-final f)))
                                    (and (pair? c) (eq? (car c) '=)
                                         (pair? (cadr c)) (eq? (car (cadr c)) 'NTH)
                                         (equal? (caddr (cadr c)) m0)))))
                           "the tail entry law")))
      (fact 'nn-one-in)
      (fact 'nn-le-refl 1)
      (fact 'nn-one-le-succ nv)
      (tb-and! (tb-guard 1 (list 'succ nv)))
      (dk-apply! hyp 1)
      (tb-and! (list 'AND (list 'IN h aa) (list 'IN m0 (list 'TUPLES aa))))
      (fact 'cons-in-tuples aa h m0)
      (fact 'length-cons h m0)
      (fact 'eq-sym (list 'LENGTH m0) nv)
      (ew (list 'CONS h m0))
      (dk-conj-close!
       (lambda ()
         (let ((g (dk-goal)))
           (cond ((eq? (car g) 'FORALL) (tb-entries! h m0 nv k0 entu))
                 ((eq? (car g) '=)
                  (subst (list '= nv (list 'LENGTH m0))) (ass))
                 (#t (ass)))))))))


;;; ---------------------------------------------------------------------
;;; tab-succ-add -- succ(a) + b = succ(a + b).
;;;
;;; Proved here in four rewrites from `nn-add-succ' and `nn-add-comm'.  It is
;;; proved here rather than cited from nn-pairing because that file loads BELOW
;;; matof-in-mat, and the window this file wants is right ABOVE matof-in-mat --
;;; citing nn-pairing would push the whole tabulation block past its only
;;; consumer.  nn-pairing carried the same statement as `nn-succ-add' until
;;; 2026-09-20 (batch 11); that duplicate is gone and nn-pairing cites this.

(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ NN)
   (FORALL b_ (IMPLIES (IN b_ NN)
     (= (+ (succ a_) b_) (succ (+ a_ b_)))))))))
(dk-peel!)
(fact 'nn-succ-closed 'a_)
(tb-and! '(AND (IN (succ a_) NN) (IN b_ NN)))
(fact 'nn-add-comm '(succ a_) 'b_)
(fact 'nn-add-succ 'b_ 'a_)
(tb-and! '(AND (IN b_ NN) (IN a_ NN)))
(fact 'nn-add-comm 'b_ 'a_)
(tb-and! '(AND (IN a_ NN) (IN b_ NN)))
(fact 'nn-add-closed 'a_ 'b_)
(fact 'nn-succ-closed '(+ a_ b_))
(subst '(= (+ (succ a_) b_) (+ b_ (succ a_))))
(subst '(= (+ b_ (succ a_)) (succ (+ b_ a_))))
(subst '(= (+ b_ a_) (+ a_ b_)))
(rfl)
(qed 'tab-succ-add)
(topic! 'tab-succ-add 'plumbing)

;;; ---- the theorem ------------------------------------------------------

(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL A (FORALL f (FORALL k (IMPLIES (IN k NN)
      (IMPLIES (FORALL i_ (IMPLIES (AND (IN i_ NN) (AND (<= 1 i_) (<= i_ n)))
                                   (IN (f (+ k i_)) A)))
        (FORSOME L (AND (IN L (TUPLES A))
                   (AND (= (LENGTH L) n)
                        (FORALL i_ (IMPLIES (AND (IN i_ NN) (AND (<= 1 i_) (<= i_ n)))
                                            (= (NTH i_ L) (f (+ k i_)))))))))))))))))
(for-each
 (lambda (lf)
   (dk-focus! lf)
   (dk-peel!)
   (if (equal? (caddr (tb-goal-parts)) 0) (tb-base!) (tb-step!)))
 (dk-opened (lambda () (ni))))
(qed 'tuple-tabulation-offset)
(topic! 'tuple-tabulation-offset 'combinatorial)

;;; ---- the same driver, two indices -------------------------------------

(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL A (FORALL g (FORALL c_ (FORALL k (IMPLIES (IN k NN)
      (IMPLIES (FORALL j_ (IMPLIES (AND (IN j_ NN) (AND (<= 1 j_) (<= j_ n)))
                                   (IN (g c_ (+ k j_)) A)))
        (FORSOME L (AND (IN L (TUPLES A))
                   (AND (= (LENGTH L) n)
                        (FORALL j_ (IMPLIES (AND (IN j_ NN) (AND (<= 1 j_) (<= j_ n)))
                                            (= (NTH j_ L) (g c_ (+ k j_))))))))))))))))))
(for-each
 (lambda (lf)
   (dk-focus! lf)
   (dk-peel!)
   (if (equal? (caddr (tb-goal-parts)) 0) (tb-base!) (tb-step!)))
 (dk-opened (lambda () (ni))))
(qed 'row-tabulation-offset)
(topic! 'row-tabulation-offset 'combinatorial)

;;; ---- dropping the offset ----------------------------------------------

(define (tb-drop-offset! name)
  (dk-peel!)
  (let* ((p    (tb-goal-parts))
         (aa   (cadr p)) (nt (caddr p)) (iv (cadddr p)) (e (car (cddddr p)))
         (e0   (tb-rep e iv (list '+ 0 iv)))
         (args (reverse (cdr (reverse e))))
         (hyp  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (let ((c (tb-final f)))
                                           (and (pair? c) (eq? (car c) 'IN)
                                                (equal? (caddr c) aa)))))
                        "the entry-membership hypothesis")))
    (fact 'nn-zero-in)
    (have! (tb-hyp iv nt e0 aa)
      (lambda ()
        (let* ((landed (dk-split-all! (dk-peel!)))
               (j      (tb-typed-var landed)))
          (tb-zero-add! j)
          (tb-and! (tb-guard j nt))
          (dk-apply! hyp j)
          (subst (list '= (list '+ 0 j) j))
          (ass))))
    (let* ((thm   (apply dk-fact! name (append (list nt aa) args (list 0))))
           (l0    (dk-skolem! thm))
           (entu  (dk-pick (lambda (f)
                             (and (pair? f) (eq? (car f) 'FORALL)
                                  (let ((c (tb-final f)))
                                    (and (pair? c) (eq? (car c) '=)
                                         (pair? (cadr c)) (eq? (car (cadr c)) 'NTH)
                                         (equal? (caddr (cadr c)) l0)))))
                           "the entry law of the offset tabulation")))
      (ew l0)
      (dk-conj-close!
       (lambda ()
         (let ((g (dk-goal)))
           (if (eq? (car g) 'FORALL)
               (let* ((landed (dk-split-all! (dk-peel!)))
                      (j      (tb-typed-var landed))
                      (e0j    (tb-rep e iv (list '+ 0 j))))
                 (tb-zero-add! j)
                 (tb-and! (tb-guard j nt))
                 (dk-apply! entu j)
                 (dk-apply! hyp j)
                 (subst (list '= (list 'NTH j l0) e0j))
                 (subst (list '= (list '+ 0 j) j))
                 (rfl))
               (ass))))))))

;; (= (+ 0 j) j)  and its converse, in context.
(define (tb-zero-add! j)
  (tb-and! (list 'AND (list 'IN 0 'NN) (list 'IN j 'NN)))
  (fact 'nn-add-comm 0 j)
  (fact 'nn-add-zero j)
  (have! (list '= (list '+ 0 j) j)
    (lambda () (subst (list '= (list '+ 0 j) (list '+ j 0))) (ass)))
  (fact 'eq-sym (list '+ 0 j) j))

(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL A (FORALL f
      (IMPLIES (FORALL i_ (IMPLIES (AND (IN i_ NN) (AND (<= 1 i_) (<= i_ n)))
                                   (IN (f i_) A)))
        (FORSOME L (AND (IN L (TUPLES A))
                   (AND (= (LENGTH L) n)
                        (FORALL i_ (IMPLIES (AND (IN i_ NN) (AND (<= 1 i_) (<= i_ n)))
                                            (= (NTH i_ L) (f i_))))))))))))))
(tb-drop-offset! 'tuple-tabulation-offset)
(qed 'tuple-tabulation)

(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL A (FORALL g (FORALL c_
      (IMPLIES (FORALL j_ (IMPLIES (AND (IN j_ NN) (AND (<= 1 j_) (<= j_ n)))
                                   (IN (g c_ j_) A)))
        (FORSOME L (AND (IN L (TUPLES A))
                   (AND (= (LENGTH L) n)
                        (FORALL j_ (IMPLIES (AND (IN j_ NN) (AND (<= 1 j_) (<= j_ n)))
                                            (= (NTH j_ L) (g c_ j_)))))))))))))))
(tb-drop-offset! 'row-tabulation-offset)
(qed 'row-tabulation)


(define (mtb-final f)
  (if (and (pair? f) (memq (car f) '(FORALL IMPLIES))) (mtb-final (caddr f)) f))

(define (mtb-and! f) (have! f (lambda () (dk-conj-close! (lambda () (ass))))))
(define (mtb-guard v hi)
  (list 'AND (list 'IN v 'NN) (list 'AND (list '<= 1 v) (list '<= v hi))))

(define (mtb-zero-var landed)
  (let ((f (find-first (lambda (f) (and (pair? f) (eq? (car f) '<=) (equal? (caddr f) 0)))
                       landed)))
    (if (not f) (error "mtb-zero-var: no (<= v 0) among" landed))
    (cadr f)))

;; the FORSOME goal, taken apart: (P A M N G K IV JV ROWLEN ENT)
(define (mtb-parts)
  (let ((g (dk-goal)))
    (if (not (eq? (car g) 'FORSOME)) (error "mtb-parts: not a FORSOME" g))
    (let* ((pv    (cadr g))
           (body  (caddr g))
           (aa    (cadr (cadr (caddr (cadr body)))))
           (rest  (caddr body))
           (mt    (caddr (cadr rest)))
           (rest2 (caddr rest))
           (rowln (cadr rest2))
           (ent   (caddr rest2))
           (nt    (caddr (caddr (caddr rowln))))
           (rhs   (caddr (caddr (caddr (caddr (caddr ent))))))
           (gg    (car rhs))
           (plus  (cadr rhs))
           (k0    (cadr plus))
           (iv    (caddr plus))
           (jv    (caddr rhs)))
      (list pv aa mt nt gg k0 iv jv rowln ent))))

;; i in [1, succ mv]: either i = 1 (BODY-ONE) or i = succ q with 1 <= q <= mv
;; (BODY-SUCC q).  The goal has i rewritten to 1 / to (succ q) before the body
;; runs.  I0 is read off the GOAL by the caller: `di' is greedy, so a two-binder
;; universal peels both indices at once and the landed typings do not say which
;; is which.
(define (mtb-cases! i0 mv body-one body-succ)
  (let* ((ex (dk-fact! 'nn-pos-is-succ i0))
         (q0 (dk-skolem! ex)))
    (have! (list '<= q0 mv) (lambda () (tb-q-le! i0 q0 mv)))
    (use-cases (dk-fact! 'nn-zero-or-succ q0)
      (lambda ()
        (fact 'nn-one-is-succ-zero)
        (fact 'eq-sym 1 '(succ 0))
        (have! (list '= i0 1)
               (lambda () (subst (list '= i0 (list 'succ q0)))
                          (subst (list '= q0 0))
                          (ass)))
        (subst (list '= i0 1))
        (body-one))
      (lambda ()
        (let* ((ex2 (dk-pick (dk-head? 'FORSOME) "the predecessor of q0"))
               (r0  (dk-skolem! ex2)))
          (fact 'nn-one-le-succ r0)
          (have! (list '<= 1 q0)
                 (lambda () (subst (list '= q0 (list 'succ r0))) (ass)))
          (subst (list '= i0 (list 'succ q0)))
          (body-succ q0))))))

;; NTH(succ q, CONS r m) -> NTH(q, m) in the goal; leaves 1 <= q <= LENGTH(m).
(define (mtb-shift-row! q0 r0 m0 mv)
  (have! (list '<= q0 (list 'LENGTH m0))
         (lambda () (subst (list '= (list 'LENGTH m0) mv)) (ass)))
  (mtb-and! (mtb-guard q0 (list 'LENGTH m0)))
  (fact 'nth-cons-succ q0 r0 m0)
  (subst (list '= (list 'NTH (list 'succ q0) (list 'CONS r0 m0)) (list 'NTH q0 m0))))

(define (mtb-base!)
  (let ((aa (cadr (mtb-parts))))
    (fact 'empty-in-tuples (list 'TUPLES aa))
    (fact 'length-of-empty)
    (ew '(LIST))
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (if (eq? (car g) 'FORALL)
             (let* ((landed (dk-split-all! (dk-peel!)))
                    (v      (mtb-zero-var landed)))
               (fact 'nn-not-le-zero-pos v)
               (ai (list 'NOT (list '<= v 0))))
             (ass)))))))

(define (mtb-step!)
  (let* ((p    (mtb-parts))
         (aa   (list-ref p 1)) (mt (list-ref p 2)) (nt (list-ref p 3))
         (gg   (list-ref p 4)) (k0 (list-ref p 5)) (iv (list-ref p 6))
         (jv   (list-ref p 7)) (rowln (list-ref p 8)) (entt (list-ref p 9))
         (mv   (cadr mt))
         (sk   (list 'succ k0))
         (hyp  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (let ((c (mtb-final f)))
                                           (and (pair? c) (eq? (car c) 'IN)
                                                (equal? (caddr c) aa)))))
                        "the entry-membership hypothesis"))
         (ih   (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (pair? (mtb-final f))
                                         (eq? (car (mtb-final f)) 'FORSOME)))
                        "the induction hypothesis"))
         ;; the shifted hypothesis, offset succ k, over [1, mv]
         (hyp2 (list 'FORALL iv
                 (list 'IMPLIES (mtb-guard iv mv)
                   (list 'FORALL jv
                     (list 'IMPLIES (mtb-guard jv nt)
                       (list 'IN (list gg (list '+ sk iv) jv) aa)))))))
    (fact 'nn-succ-closed k0)
    (have! hyp2
      (lambda ()
        (dk-split-all! (dk-peel!))
        (let* ((g1 (dk-goal))                       ; (IN (gg (+ sk i) j) aa)
               (en (cadr g1))
               (i  (caddr (cadr en)))
               (j  (caddr en)))
          (fact 'nn-succ-closed i)
          (fact 'nn-one-le-succ i)
          (fact 'nn-succ-mono i mv)
          (mtb-and! (mtb-guard (list 'succ i) (list 'succ mv)))
          (let ((inner (dk-apply! hyp (list 'succ i))))
            (mtb-and! (mtb-guard j nt))
            (dk-apply! inner j))
          (fact 'tab-succ-add k0 i)
          (fact 'nn-add-succ k0 i)
          (fact 'eq-sym (list '+ k0 (list 'succ i)) (list 'succ (list '+ k0 i)))
          (subst (list '= (list '+ sk i) (list 'succ (list '+ k0 i))))
          (subst (list '= (list 'succ (list '+ k0 i)) (list '+ k0 (list 'succ i))))
          (ass))))
    ;; the tail of the matrix, from the induction hypothesis
    (let* ((ihres  (dk-apply! ih aa gg nt sk))
           (m0     (dk-skolem! ihres))
           (rowlen (dk-pick (lambda (f)
                              (and (pair? f) (eq? (car f) 'FORALL)
                                   (let ((c (mtb-final f)))
                                     (and (pair? c) (eq? (car c) '=)
                                          (pair? (cadr c)) (eq? (car (cadr c)) 'LENGTH)
                                          (pair? (cadr (cadr c)))
                                          (equal? (caddr (cadr (cadr c))) m0)))))
                            "the row-length law of the tail"))
           (ment   (dk-pick (lambda (f)
                              (and (pair? f) (eq? (car f) 'FORALL)
                                   (let ((c (mtb-final f)))
                                     (and (pair? c) (eq? (car c) '=)
                                          (pair? (cadr c)) (eq? (car (cadr c)) 'NTH)
                                          (pair? (caddr (cadr c)))
                                          (equal? (caddr (caddr (cadr c))) m0)))))
                            "the entry law of the tail")))
      ;; the first row, from row-tabulation
      (fact 'nn-one-in)
      (fact 'nn-le-refl 1)
      (fact 'nn-one-le-succ mv)
      (mtb-and! (mtb-guard 1 (list 'succ mv)))
      (dk-apply! hyp 1)
      (let* ((rex  (dk-fact! 'row-tabulation nt aa gg (list '+ k0 1)))
             (r0   (dk-skolem! rex))
             (rent (dk-pick (lambda (f)
                              (and (pair? f) (eq? (car f) 'FORALL)
                                   (let ((c (mtb-final f)))
                                     (and (pair? c) (eq? (car c) '=)
                                          (pair? (cadr c)) (eq? (car (cadr c)) 'NTH)
                                          (equal? (caddr (cadr c)) r0)))))
                            "the entry law of the first row")))
        (mtb-and! (list 'AND (list 'IN r0 (list 'TUPLES aa))
                        (list 'IN m0 (list 'TUPLES (list 'TUPLES aa)))))
        (fact 'cons-in-tuples (list 'TUPLES aa) r0 m0)
        (fact 'length-cons r0 m0)
        (fact 'eq-sym (list 'LENGTH m0) mv)
        (ew (list 'CONS r0 m0))
        (dk-conj-close!
         (lambda ()
           (let ((g (dk-goal)))
             (cond
               ((eq? (car g) 'IN) (ass))
               ((eq? (car g) '=)
                (subst (list '= mv (list 'LENGTH m0))) (ass))
               ((and (eq? (car g) 'FORALL)
                     (eq? (car (cadr (mtb-final g))) 'LENGTH))
                ;; every row of CONS(r0, m0) has length nt
                (dk-split-all! (dk-peel!))
                (let* ((g1 (dk-goal))
                       (i0 (cadr (cadr (cadr g1)))))
                  (mtb-cases! i0 mv
                    (lambda ()
                      (fact 'nth-cons-1 r0 m0)
                      (subst (list '= (list 'NTH 1 (list 'CONS r0 m0)) r0))
                      (ass))
                    (lambda (q0)
                      (mtb-shift-row! q0 r0 m0 mv)
                      (mtb-and! (mtb-guard q0 mv))
                      (dk-apply! rowlen q0)
                      (ass)))))
               (#t
                ;; the entries
                (dk-split-all! (dk-peel!))
                (let* ((g1  (dk-goal))
                       (lhs (cadr g1))
                       (j0  (cadr lhs))
                       (i0  (cadr (caddr lhs))))
                  (mtb-cases! i0 mv
                    (lambda ()
                      (fact 'nth-cons-1 r0 m0)
                      (subst (list '= (list 'NTH 1 (list 'CONS r0 m0)) r0))
                      (mtb-and! (mtb-guard j0 nt))
                      (dk-apply! rent j0)
                      (ass))
                    (lambda (q0)
                      (mtb-shift-row! q0 r0 m0 mv)
                      (mtb-and! (mtb-guard q0 mv))
                      (let ((inner (dk-apply! ment q0)))
                        (mtb-and! (mtb-guard j0 nt))
                        (dk-apply! inner j0))
                      (fact 'nn-add-succ k0 q0)
                      (fact 'tab-succ-add k0 q0)
                      (fact 'eq-sym (list '+ sk q0) (list 'succ (list '+ k0 q0)))
                      (subst (list '= (list '+ k0 (list 'succ q0))
                                    (list 'succ (list '+ k0 q0))))
                      (subst (list '= (list 'succ (list '+ k0 q0)) (list '+ sk q0)))
                      (ass)))))))))))))

(sp (make-wff
 '(FORALL m (IMPLIES (IN m NN) (FORALL A (FORALL g (FORALL n (FORALL k (IMPLIES (IN k NN) (IMPLIES (IN n NN) (IMPLIES (FORALL i_ (IMPLIES (AND (IN i_ NN) (AND (<= 1 i_) (<= i_ m))) (FORALL j_ (IMPLIES (AND (IN j_ NN) (AND (<= 1 j_) (<= j_ n))) (IN (g (+ k i_) j_) A))))) (FORSOME P (AND (IN P (TUPLES (TUPLES A))) (AND (= (LENGTH P) m) (AND (FORALL i_ (IMPLIES (AND (IN i_ NN) (AND (<= 1 i_) (<= i_ m))) (= (LENGTH (NTH i_ P)) n))) (FORALL i_ (IMPLIES (AND (IN i_ NN) (AND (<= 1 i_) (<= i_ m))) (FORALL j_ (IMPLIES (AND (IN j_ NN) (AND (<= 1 j_) (<= j_ n))) (= (NTH j_ (NTH i_ P)) (g (+ k i_) j_)))))))))))))))))))))
(for-each
 (lambda (lf)
   (dk-focus! lf)
   (dk-peel!)
   (if (equal? (caddr (mtb-parts)) 0) (mtb-base!) (mtb-step!)))
 (dk-opened (lambda () (ni))))
(qed 'matrix-tabulation)
(topic! 'matrix-tabulation 'combinatorial)


(define (mte-in-interval! i lo hi)
  (have! (list 'IN i (list 'INTERVAL lo hi))
    (lambda ()
      (mac 'INTERVAL)
      (for-each (lambda (l) (dk-focus! l) (dk-conj-close!))
                (dk-opened (lambda () (sep-mi)))))))

(define (mte-nn-of! i lo hi)
  (mac-h 'interval-membership (list 'IN i (list 'INTERVAL lo hi)))
  (dk-split-all!))

(sp (make-wff
 '(FORALL m (FORALL n (FORALL X (FORALL g (IMPLIES (IN m NN) (IMPLIES (IN n NN) (IMPLIES (<= 1 m) (IMPLIES (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m)) (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n)) (IN (g i_ j_) X))))) (FORSOME P (AND (IN P (MAT m n X)) (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m)) (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n)) (= (ENTRY P i_ j_) (g i_ j_))))))))))))))))))
(dk-peel!)
(let* ((g0  (dk-goal))
       (bod (caddr g0))
       (mat (caddr (cadr bod)))
       (mv  (cadr mat)) (nv (caddr mat)) (xx (cadddr mat))
       (ent (caddr bod))
       (gg  (car (caddr (caddr (caddr (caddr (caddr ent))))))) ; head of (g i_ j_)
       (hyp (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                      (let ((c (mtb-final f)))
                                        (and (pair? c) (eq? (car c) 'IN)
                                             (equal? (caddr c) xx)))))
                     "the entry-membership hypothesis")))
  (fact 'nn-zero-in)
  (fact 'nn-one-in)
  (fact 'nn-le-refl 1)
  ;; the hypothesis matrix-tabulation wants: NN-guarded, offset 0
  (have! (list 'FORALL 'i_
           (list 'IMPLIES (mtb-guard 'i_ mv)
             (list 'FORALL 'j_
               (list 'IMPLIES (mtb-guard 'j_ nv)
                 (list 'IN (list gg (list '+ 0 'i_) 'j_) xx)))))
    (lambda ()
      (dk-split-all! (dk-peel!))
      (let* ((g1 (dk-goal))
             (en (cadr g1))
             (i0 (caddr (cadr en)))
             (j0 (caddr en)))
        (mte-in-interval! i0 1 mv)
        (mte-in-interval! j0 1 nv)
        (let ((inner (dk-apply! hyp i0)))
          (dk-apply! inner j0))
        (tb-zero-add! i0)
        (subst (list '= (list '+ 0 i0) i0))
        (ass))))
  (let* ((mex    (dk-fact! 'matrix-tabulation mv xx gg nv 0))
         (p0     (dk-skolem! mex))
         (rowlen (dk-pick (lambda (f)
                            (and (pair? f) (eq? (car f) 'FORALL)
                                 (let ((c (mtb-final f)))
                                   (and (pair? c) (eq? (car c) '=)
                                        (pair? (cadr c)) (eq? (car (cadr c)) 'LENGTH)
                                        (pair? (cadr (cadr c)))
                                        (equal? (caddr (cadr (cadr c))) p0)))))
                          "the row-length law"))
         (ment   (dk-pick (lambda (f)
                            (and (pair? f) (eq? (car f) 'FORALL)
                                 (let ((c (mtb-final f)))
                                   (and (pair? c) (eq? (car c) '=)
                                        (pair? (cadr c)) (eq? (car (cadr c)) 'NTH)
                                        (pair? (caddr (cadr c)))
                                        (equal? (caddr (caddr (cadr c))) p0)))))
                          "the entry law")))
    (fact 'eq-sym (list 'LENGTH p0) mv)
    ;; P is a matrix over X
    (have! (list 'IN p0 (list 'MATRIX xx))
      (lambda ()
        (mac 'matrix-membership)
        (dk-conj-close!
         (lambda ()
           (let ((g1 (dk-goal)))
             (if (eq? (car g1) 'IN)
                 (ass)
                 (begin
                   (dk-split-all! (dk-peel!))
                   (let* ((g2 (dk-goal))
                          (i0 (cadr (cadr (cadr g2))))
                          (j0 (cadr (cadr (caddr g2)))))
                     (have! (list '<= i0 mv)
                            (lambda () (subst (list '= mv (list 'LENGTH p0))) (ass)))
                     (have! (list '<= j0 mv)
                            (lambda () (subst (list '= mv (list 'LENGTH p0))) (ass)))
                     (mtb-and! (mtb-guard i0 mv))
                     (dk-apply! rowlen i0)
                     (mtb-and! (mtb-guard j0 mv))
                     (dk-apply! rowlen j0)
                     (fact 'eq-sym (list 'LENGTH (list 'NTH j0 p0)) nv)
                     (fact 'eq-trans (list 'LENGTH (list 'NTH i0 p0)) nv
                                     (list 'LENGTH (list 'NTH j0 p0)))
                     (ass)))))))))
    ;; P in MAT(m, n, X) by mat-intro -- this is where 1 <= m is used: the
    ;; column count is the length of row 1
    (mtb-and! (mtb-guard 1 mv))
    (dk-apply! rowlen 1)
    (fact 'mat-intro mv nv xx p0)
    (ew p0)
    (dk-conj-close!
     (lambda ()
       (let ((g1 (dk-goal)))
         (if (eq? (car g1) 'IN)
             (ass)
             (begin
               (dk-peel!)
               (let* ((g2 (dk-goal))
                      (i0 (caddr (cadr g2)))
                      (j0 (cadddr (cadr g2))))
                 (let ((inner (dk-apply! hyp i0)))
                   (dk-apply! inner j0))
                 (mte-nn-of! i0 1 mv)
                 (mte-nn-of! j0 1 nv)
                 (mtb-and! (mtb-guard i0 mv))
                 (let ((inner2 (dk-apply! ment i0)))
                   (mtb-and! (mtb-guard j0 nv))
                   (dk-apply! inner2 j0))
                 (fact 'entry-unfold p0 i0 j0)
                 (subst (list '== (list 'ENTRY p0 i0 j0) (list 'NTH j0 (list 'NTH i0 p0))))
                 (subst (list '= (list 'NTH j0 (list 'NTH i0 p0))
                              (list gg (list '+ 0 i0) j0)))
                 (tb-zero-add! i0)
                 (subst (list '= (list '+ 0 i0) i0))
                 (rfl))))))))) 
(qed 'mat-tabulation-exists)
(topic! 'mat-tabulation-exists 'combinatorial)

(sp (make-wff
 '(FORALL m (FORALL n (FORALL g (IMPLIES (IN m NN) (IMPLIES (IN n NN) (IMPLIES (<= 1 m) (IMPLIES (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m)) (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n)) (IN (g i_ j_) SET))))) (FORSOME P (AND (IN P (MAT m n (IMAGE g (CARTESIAN (INTERVAL 1 m) (INTERVAL 1 n))))) (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m)) (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n)) (= (ENTRY P i_ j_) (g i_ j_)))))))))))))))))
(dk-peel!)
(let* ((g0  (dk-goal))
       (bod (caddr g0))
       (mat (caddr (cadr bod)))
       (mv  (cadr mat)) (nv (caddr mat)) (img (cadddr mat))
       (gg  (cadr img))
       (dhyp (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                       (let ((c (mtb-final f)))
                                         (and (pair? c) (eq? (car c) 'IN)
                                              (eq? (caddr c) 'SET)))))
                      "the definedness hypothesis")))
  (have! (list 'FORALL 'i_
           (list 'IMPLIES (list 'IN 'i_ (list 'INTERVAL 1 mv))
             (list 'FORALL 'j_
               (list 'IMPLIES (list 'IN 'j_ (list 'INTERVAL 1 nv))
                 (list 'IN (list gg 'i_ 'j_) img)))))
    (lambda ()
      (dk-peel!)
      (let* ((g1 (dk-goal))
             (en (cadr g1))
             (i0 (cadr en))
             (j0 (caddr en)))
        (let ((inner (dk-apply! dhyp i0))) (dk-apply! inner j0))
        (dk-image-goal!)
        (ew (list 'LIST i0 j0))
        (dk-conj-close!
         (lambda ()
           (let ((g2 (dk-goal)))
             (if (eq? (car g2) 'IN)
                 (begin (fact 'pair-in-cartesian (list 'INTERVAL 1 mv) (list 'INTERVAL 1 nv) i0 j0)
                        (ass))
                 (begin (fact 'apply-tupling-2 gg i0 j0)
                        (subst (list '== (list gg (list 'LIST i0 j0)) (list gg i0 j0)))
                        (rfl)))))))))
  (fact 'mat-tabulation-exists mv nv img gg)
  (ass))
(qed 'matof-exists-image)
(topic! 'matof-exists-image 'combinatorial)


(define (eom-entry-law t)
  (dk-pick (lambda (f)
             (and (pair? f) (eq? (car f) 'FORALL)
                  (let ((c (mtb-final f)))
                    (and (pair? c) (eq? (car c) '=)
                         (pair? (cadr c)) (eq? (car (cadr c)) 'ENTRY)
                         (equal? (cadr (cadr c)) t)))))
           "the entry law"))

(define (eom-unique! mv nv gg img p0)
  (dk-peel!)
  (dk-split-all!)
  (let* ((g (dk-goal))
         (y (caddr g))
         (e0 (eom-entry-law p0))
         (ey (eom-entry-law y)))
    (have! (list 'FORALL 'i_
             (list 'IMPLIES (list 'IN 'i_ (list 'INTERVAL 1 mv))
               (list 'FORALL 'j_
                 (list 'IMPLIES (list 'IN 'j_ (list 'INTERVAL 1 nv))
                   (list '= (list 'ENTRY p0 'i_ 'j_) (list 'ENTRY y 'i_ 'j_))))))
      (lambda ()
        (dk-peel!)
        (let* ((g2 (dk-goal))
               (i0 (caddr (cadr g2)))
               (j0 (cadddr (cadr g2))))
          (let ((in0 (dk-apply! e0 i0))) (dk-apply! in0 j0))
          (let ((iny (dk-apply! ey i0))) (dk-apply! iny j0))
          (fact 'eq-sym (list 'ENTRY y i0 j0) (list gg i0 j0))
          (fact 'eq-trans (list 'ENTRY p0 i0 j0) (list gg i0 j0) (list 'ENTRY y i0 j0))
          (ass))))
    (fact 'matrix-entry-extensionality mv nv img p0 y)
    (ass)))

(define (eom-ex-uniq! mv nv gg img)
  (let* ((ex (dk-fact! 'matof-exists-image mv nv gg))
         (p0 (dk-skolem! ex)))
    (ew p0)
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (car (dk-goal)) 'FORALL)
           (eom-unique! mv nv gg img p0)
           (dk-conj-close!)))
     (dk-opened (lambda () (di))))))

(sp (make-wff
 '(FORALL m (FORALL n (FORALL g (IMPLIES (IN m NN) (IMPLIES (IN n NN) (IMPLIES (<= 1 m) (IMPLIES (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m)) (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n)) (IN (g i_ j_) SET))))) (FORALL u_ (IMPLIES (IN u_ (INTERVAL 1 m)) (FORALL v_ (IMPLIES (IN v_ (INTERVAL 1 n)) (= (ENTRY (MATOF m n g) u_ v_) (g u_ v_)))))))))))))))
(dk-peel!)
(let* ((g0 (dk-goal))
       (mf (cadr (cadr g0)))
       (mv (cadr mf)) (nv (caddr mf)) (gg (cadddr mf))
       (i0 (caddr (cadr g0))) (j0 (cadddr (cadr g0)))
       (box (list 'CARTESIAN (list 'INTERVAL 1 mv) (list 'INTERVAL 1 nv)))
       (img (list 'IMAGE gg box)))
  (mac 'MATOF)
  (let ((io (cadr (cadr (dk-goal)))))
    (if (not (and (pair? io) (eq? (car io) 'IOTA)))
        (error "entry-of-matof: MATOF did not unfold to an IOTA" io))
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (car (dk-goal)) 'FORSOME)
           (eom-ex-uniq! mv nv gg img)
           (let ((dp (dk-pick (lambda (f)
                                (and (pair? f) (eq? (car f) 'AND)
                                     (equal? (cadr f) (list 'IN io (list 'MAT mv nv img)))))
                              "the defining property of the description")))
             (dk-split! dp)
             (let* ((law (eom-entry-law io))
                    (inner (dk-apply! law i0)))
               (dk-apply! inner j0))
             (ass))))
     (dk-opened (lambda () (iota-d io))))))
(qed 'entry-of-matof-guarded)
(topic! 'entry-of-matof-guarded 'combinatorial)


;;; ---------------------------------------------------------------------
;;; THE CANONICAL NAMES, GUARDED (2026-09-15 soundness repair; installed
;;; 2026-09-16, after the SIZE/MAT change in matrix.scm)
;;;
;;; `matof-exists' and `entry-of-matof' were asserted SUPPORTS in
;;; structure-library/matrix.scm with UNGUARDED dimensions, and the first of
;;; them proved FALSITY (this file's header).  They are retired there and
;;; installed here as THEOREMS under the same names.  The outer binder list and
;;; its ORDER are kept, so a citer gains premises and never a rename.
;;;
;;; The guards, at the head of the premise chain in both:
;;;
;;;   (IN m NN), (IN n NN)     the dimensions.
;;;   the definedness hypothesis  (IN (g i_ j_) SET) on the index box.
;;;
;;; NOT `1 <= m'.  The twins above carry it because they build the matrix row by
;;; row and read the column count off row 1.  Since 2026-09-16 the matrix with
;;; no rows is in MAT(0, n, X) for every natural n (`nil-in-mat',
;;; mat-basics.scm), so the canonical statements cover m = 0 by a case split:
;;; for m = 0 the witness is [] and the entry clause is vacuous; for m /= 0,
;;; m is a successor, hence 1 <= m, and the twin applies.  This is what lets
;;; `spans-fg-base' exhibit MATOF(0, 1, ...).
;;;
;;; Inner binders: the definedness hypothesis uses `i_' `j_' throughout, because
;;; `entry-of-matof''s OUTER index binders are spelled `i' `j' (as in the retired
;;; support) and MATOF's own IOTA binders are `i' `j' as well.
;;; ---------------------------------------------------------------------


(sp (make-wff
 '(FORALL m (FORALL n (FORALL g
    (IMPLIES (IN m NN)
    (IMPLIES (IN n NN)
    (IMPLIES (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m))
               (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
                 (IN (g i_ j_) SET)))))
      (FORSOME P
        (AND (IN P (MAT m n (IMAGE g (CARTESIAN (INTERVAL 1 m) (INTERVAL 1 n)))))
             (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
               (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
                 (= (ENTRY P i j) (g i j))))))))))))))))
(dk-peel!)
(let* ((g0  (dk-goal))
       (mat (caddr (cadr (caddr g0))))
       (mv  (cadr mat)) (nv (caddr mat)) (img (cadddr mat)) (gg (cadr img)))
  (use-em (list '= mv 0)
    (lambda ()                                           ; no rows: P := []
      (ew '(LIST))
      (dk-conj-close!
       (lambda ()
         (let ((g1 (dk-goal)))
           (if (eq? (car g1) 'IN)
               (begin
                 ;; m := 0 rewrites the m inside IMAGE(g, [1,m] x [1,n]) too
                 (fact 'nil-in-mat nv (subst-free mv 0 img))
                 (subst (list '= mv 0))
                 (ass))
               (begin                                    ; i in [1, 0]: absurd
                 (dk-peel!)
                 (let* ((iv (cadr (dk-pick (lambda (f)
                                             (and (pair? f) (eq? (car f) 'IN)
                                                  (equal? (caddr f) (list 'INTERVAL 1 mv))))
                                           "the row index"))))
                   (fact 'interval-elt-in-nn 1 mv iv)
                   (fact 'interval-lo 1 mv iv)
                   (fact 'interval-hi 1 mv iv)
                   (fact 'nn-not-le-zero-pos iv)         ; not(i <= 0)
                   (have! (list '<= iv 0)
                     (lambda () (subst (list '= 0 mv)) (ass)))
                   (let ((l (find-first (lambda (l) (member (list '<= iv 0) (dk-asms-of l)))
                                        (proof-leaves))))
                     (if (not l) (error "matof-exists: no leaf holds i <= 0"))
                     (dk-focus! l))
                   (pbc)                                 ; goal FALSITY
                   (ai (list 'NOT (list '<= iv 0))))))))))
    (lambda ()                                           ; rows: the twin
      (dk-one-le! mv)
      (fact 'matof-exists-image mv nv gg)
      (ass))))
(qed 'matof-exists)
(topic! 'matof-exists 'combinatorial)

(sp (make-wff
 '(FORALL m (FORALL n (FORALL g (FORALL i (FORALL j
    (IMPLIES (IN m NN)
    (IMPLIES (IN n NN)
    (IMPLIES (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m))
               (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
                 (IN (g i_ j_) SET)))))
    (IMPLIES (IN i (INTERVAL 1 m))
    (IMPLIES (IN j (INTERVAL 1 n))
      (= (ENTRY (MATOF m n g) i j) (g i j))))))))))))))
(dk-peel!)
(let* ((g0 (dk-goal))
       (e  (cadr g0))
       (mf (cadr e))
       (mv (cadr mf)) (nv (caddr mf)) (gg (cadddr mf))
       (iv (caddr e)) (jv (cadddr e)))
  ;; 1 <= m, from the row index: 1 <= i <= m
  (fact 'interval-elt-in-nn 1 mv iv)
  (fact 'interval-lo 1 mv iv)
  (fact 'interval-hi 1 mv iv)
  (fact 'nn-one-in)
  (fact 'nn-le-trans-guarded 1 iv mv)
  (fact 'entry-of-matof-guarded mv nv gg iv jv)
  (ass))
(qed 'entry-of-matof)
(topic! 'entry-of-matof 'combinatorial)
