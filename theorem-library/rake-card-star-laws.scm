;;; rake-card-star-laws.scm -- rake batch 5c, assignment 5c-X (2026-09-18).
;;; ---------------------------------------------------------------------------
;;; NOTE, 2026-09-20 (batch 9-B).  This file was written while cardinality was
;;; AXIOMATISED under the name CARD and the defined constant was its companion
;;; CARD-STAR.  On 2026-09-20 the user made the swap: CARD is the DEFINED
;;; cardinal (structure-library/cardinality.scm), the eight `primitive' axioms
;;; about it are gone, and every proof below now speaks of CARD.  The prose in
;;; this header that contrasts "the axiomatised CARD" with "the defined
;;; cardinal" is HISTORY; the surgery is docs/card-defined-2026-09-20.md.
;;; ---------------------------------------------------------------------------
;;;
;;; The finite laws that the rename CARD := CARD-STAR still owed, proved for the
;;; DEFINED cardinal (theorem-library/card-defined.scm: the least ordinal whose
;;; segment the set bijects onto; card-finite.scm; rake-ord-pigeonhole.scm).
;;; NO primitive card-* axiom about the AXIOMATISED CARD is cited anywhere in
;;; this file (checked by grep): the point of the exercise is that CARD
;;; earns these by proof rather than inheriting them by stipulation.
;;;
;;; THE AUGUST "BLOCKED ON EXTEND-BY" NOTE IS STALE.  theorem-library/
;;; card-inequalities.scm:22 and structure-notes/card-basics-worklist.md:76-78
;;; say card-insert-curried and card-union-disjoint-curried are blocked on EXTEND-BY,
;;; "the unbuilt second member of the finite-surgery kit (a bijection A -> S(n)
;;; has to be extended to A + {x} -> S(succ n))".  EXTEND-BY WAS BUILT on
;;; 2026-09-17, under another name and for another purpose:
;;; `enum-append-is-bijection' (theorem-library/finsum-insert.scm:178) is
;;; exactly that extension, in the OS(n) -> S direction, and with it
;;; card-insert-curried is a dozen citations and no new mathematics.  Both
;;; comments should be struck.
;;;
;;; WHAT IS PROVEN HERE (fourteen theorems, every one `modulo 0')
;;;
;;;   card-insert-curried          A in SET, CARD A in NN, x in SET, x not in A
;;;                             => CARD(A u {x}) = succ_ORD(CARD A)
;;;                             [card-insert, cardinality.scm:53, with the
;;;                             finiteness guard a DEFINED cardinal must have]
;;;   card-union-disjoint-curried  finite additivity  [card-union-disjoint, :87]
;;;   finite-set-induction                [finite-set-induction, :108]
;;;   card-image-injection-curried an injection preserves the cardinal on its image
;;;                             [card-image-injection, injection.scm:162]
;;; and, under them, the PEEL the finite CARD layer was missing -- "a set of
;;; cardinal succ n is a set of cardinal n plus one fresh point":
;;;   seg-restrict-is-bijection   an enumeration restricted to the shorter segment
;;;                               is a bijection onto its image
;;;   card-seg-image         ... and that image has cardinal n
;;;   seg-image-subset            ... and lies inside the set
;;;   seg-image-omits-top         ... and does not contain the top value
;;;   seg-image-insert            ... and the set IS that image plus the top value
;;;   card-zero-is-empty     cardinal 0 means empty
;;;   card-union-disjoint-ind / card-finite-induction-aux
;;;                               the NN-induction forms (induction variable
;;;                               OUTERMOST, so `ni' fires)
;;;   injection-image-is-bijection an injection restricted to its domain is a
;;;                               bijection onto its image
;;;   intersection-empty-transfer  disjointness passes to a subclass
;;;
;;; WHICH INDUCTION, AND THE CIRCULARITY QUESTION THE BRIEF ASKS.
;;; `finite-set-induction' (structure-library/cardinality.scm:108) is PRIMITIVE
;;; and stated with the AXIOMATISED CARD, so using it to prove a CARD law
;;; would prove the defined cardinal's facts from the axiomatised one's -- the
;;; dependency this file exists to remove.  What is available without any
;;; circularity is ORDINARY NN INDUCTION (nn-induction, number-systems.scm,
;;; through `ni' / `use-induction') on the CARDINAL of the set being consumed,
;;; and what makes its step go through is the PEEL above.  The same peel proves
;;; the CARD form of finite-set-induction itself, so after this file the
;;; set-induction principle is a THEOREM of the defined cardinal and no longer
;;; needs to be assumed.
;;;
;;; CITATIONS and their load positions (0-based over the quoted file names of
;;; *vnb-files*, load.scm:81):
;;;   theory (11, primitive): class-extensionality, membership-implies-sethood,
;;;     pairing, pairing-membership, union-set-closure, union-membership,
;;;     intersection-membership, intersection-set-closure, empty-set-is-set,
;;;     empty-set-has-no-members
;;;   number-systems (34, primitive): nn-succ-closed, nn-add-closed, nn-add-zero
;;;   structure-library/nn-arith (35, definitional): nn-add-succ
;;;   structure-library/ordinals (77, primitive): nn-subset-ord, ord-succ-nn,
;;;     ord-segment-is-set
;;;   structure-library/bijection (81, definitional): bijection-membership-iff
;;;   structure-library/injection (83): injection-membership-iff and
;;;     image-membership-iff (both definitional), image-set (primitive)
;;;   theorem-library/equality-basics (146): eq-sym, eq-trans
;;;   theorem-library/ord-segment-nn-succ-proof (151): ord-segment-nn-succ
;;;   theorem-library/ord-segment-nn-subset-proof (152): ord-segment-zero-no-members
;;;   theorem-library/fun-apply-type-proof (160): fun-apply-type-c
;;;   theorem-library/rake-analysis2 (191): bijection-compose
;;;   theorem-library/rake-inverse-bij (192): inverse-bij-is-bijection, ord-segment-self
;;;   theorem-library/finsum-insert (233): enum-append-is-bijection   [EXTEND-BY]
;;;   theorem-library/fin-subsets (264): union-empty-right, union-assoc
;;;   theorem-library/card-finite (274): card-bij
;;;   theorem-library/rake-ord-pigeonhole (NOT YET IN load.scm; 5c-U asks for it
;;;     at 305, after theorem-library/rake-zermelo): well-ordering-principle
;;;     -- the LATEST citation, and what sets lo.
;;;
;;; LOAD WINDOW [306, end):  wire this file immediately AFTER
;;; theorem-library/rake-ord-pigeonhole.  Nothing cites these fourteen names, so
;;; no citer forces hi.  Nothing is retired by this file (see the closing block:
;;; the axioms these replace are about a DIFFERENT constant until the rename).
;;;
;;; Helper prefix: r7x-.

;;; ---- driver helpers ---------------------------------------------------

(define (r7x-head? f h) (and (pair? f) (eq? (car f) h)))
(define (r7x-body f)
  (cond ((r7x-head? f 'FORALL)  (r7x-body (caddr f)))
        ((r7x-head? f 'IMPLIES) (r7x-body (caddr f)))
        (#t f)))
(define (r7x-asm-find f) (find-first (lambda (a) (alpha-equiv? a f)) (dk-asms)))

(define (r7x-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "r7x-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "r7x-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

;;; `mac-h' with its side conditions discharged from the context; focus is left
;;; on the main branch.
(define (r7x-mac-h! name hyp)
  (let* ((g0    (dk-goal))
         (new   (dk-opened (lambda () (mac-h name hyp))))
         (sides (filter (lambda (l) (not (alpha-equiv? (dk-goal-of l) g0))) new))
         (mains (filter (lambda (l) (alpha-equiv? (dk-goal-of l) g0)) new)))
    (for-each (lambda (s) (dk-focus! s) (ass)) sides)
    (if (null? mains) (error "r7x-mac-h!: no main branch after" name))
    (dk-focus! (car mains))))

;;; instantiate-and-detach that tolerates a step whose result is already in the
;;; context (dk-apply! goes through dk-deepest, which errors on an empty landing).
(define (r7x-step! thunk target what)
  (if (not (r7x-asm-find target)) (dk-landed* thunk))
  (or (r7x-asm-find target)
      (error (string-append "r7x-apply!: " what " landed nothing for")
             (expression->string target))))
(define (r7x-apply! f . terms)
  (let loop ((f f) (ts terms))
    (cond ((r7x-head? f 'IMPLIES)
           (loop (r7x-step! (lambda () (detach! f)) (caddr f) "detach!") ts))
          ((null? ts) f)
          ((r7x-head? f 'FORALL)
           (loop (r7x-step! (lambda () (inst+ f (car ts)))
                            (subst-free (cadr f) (car ts) (caddr f)) "inst+")
                 (cdr ts)))
          (#t (error "r7x-apply!: not a universal" (expression->string f))))))

;;; the three projections of a BIJECTION membership, in context order
;;; (FUN typing, injectivity, surjectivity).  `mac-h' REPLACES what it unfolds.
(define (r7x-open-bijection! f)
  (dk-split-all! (dk-landed* (lambda () (mac-h 'bijection-membership-iff f))))
  (list (dk-pick (lambda (a) (and (r7x-head? a 'IN) (r7x-head? (caddr a) 'FUN)))
                 "the FUN typing")
        (dk-pick (lambda (a) (and (r7x-head? a 'FORALL) (r7x-head? (r7x-body a) '=)))
                 "injectivity")
        (dk-pick (lambda (a) (and (r7x-head? a 'FORALL) (r7x-head? (r7x-body a) 'FORSOME)))
                 "surjectivity")))

;;; reduce every VNB-LAMBDA redex standing in an equational hypothesis
(define (r7x-beta-h!)
  (let loop ()
    (let ((eq (find-first (lambda (f) (and (r7x-head? f '=) (dk-contains? f 'VNB-LAMBDA)))
                          (dk-asms))))
      (if eq (begin (lam-b-h eq) (loop))))))

(define (r7x-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** rake-card-star-laws: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l)))
                    (newline))
                  (proof-leaves))
        (error "rake-card-star-laws: unfinished" name))))

;;; (IN (PAIR t t) SET) and then (IN (UNION S (PAIR t t)) SET); both axioms
;;; carry AND antecedents, which `fact' will not split, so each conjunction is
;;; landed first.
(define (r7x-insert-set! S t)
  (have! (list 'AND (list 'IN t 'SET) (list 'IN t 'SET)))
  (dk-fact! 'pairing t t)
  (have! (list 'AND (list 'IN S 'SET) (list 'IN (list 'PAIR t t) 'SET)))
  (dk-fact! 'union-set-closure S (list 'PAIR t t)))

;;; =====================================================================
;;; card-insert-curried -- adding one fresh element to a FINITE set raises the
;;; defined cardinal by one.
;;;
;;;   a_ in SET,  CARD(a_) in NN,  x_ in SET,  x_ not in a_
;;;     =>  CARD(a_ u {x_}) = succ_ORD(CARD a_)
;;;
;;; This is `card-insert' (structure-library/cardinality.scm:53) with the
;;; finiteness guard that a DEFINED cardinal needs -- unguarded the statement is
;;; FALSE (omega u {x} bijects with omega, so its least ordinal is omega and not
;;; succ omega; 5c-U's report, and the user's repair decision of the same day).
;;;
;;; THE ROUTE, and it needs no new mathematics:
;;;   well-ordering-principle  (rake-ord-pigeonhole)  enumerates a_ by its own
;;;                            cardinal:  enm in BIJECTION(OS(CARD a_), a_)
;;;   enum-append-is-bijection (finsum-insert)        extends that enumeration by
;;;                            one point: psi in BIJECTION(OS(succ N), a_ u {x_})
;;;   inverse-bij-is-bijection (rake-inverse-bij)     flips it
;;;   card-bij            (card-finite)          reads the cardinal off the
;;;                            two directions -- existence from one, LEASTNESS
;;;                            (via pigeonhole-segments-gen, inside card-bij)
;;;                            from the other.
;;; The hypothesis CARD(a_) in NN is what makes succ N a NATURAL, which is
;;; what card-bij demands and what pigeonhole under it needs.
;;; =====================================================================

(define r7x-insert-stmt
  '(FORALL a_ (IMPLIES (IN a_ SET)
     (IMPLIES (IN (CARD a_) NN)
       (FORALL x_ (IMPLIES (IN x_ SET)
         (IMPLIES (NOT (IN x_ a_))
           (= (CARD (UNION a_ (PAIR x_ x_)))
              (succ_ORD (CARD a_))))))))))

(sp (make-wff r7x-insert-stmt))
(dk-peel!)

;; every name is read off the GOAL, never off the context: both hypotheses
;; (IN a_ SET) and (IN x_ SET) have the same shape.
(define r7x-i-goal (dk-goal))
(define r7x-i-uni  (cadr (cadr r7x-i-goal)))        ; (UNION a_ (PAIR x_ x_))
(define r7x-i-a    (cadr r7x-i-uni))
(define r7x-i-x    (cadr (caddr r7x-i-uni)))
(define r7x-i-n    (cadr (caddr r7x-i-goal)))       ; (CARD a_)
(define r7x-i-segs (list 'ORD-SEGMENT (list 'succ r7x-i-n)))

(dk-fact! 'nn-succ-closed r7x-i-n)                  ; (IN (succ N) NN)
(r7x-insert-set! r7x-i-a r7x-i-x)                   ; (IN (a_ u {x_}) SET)

;; enumerate a_ by its own cardinal, then extend the enumeration by x_
(define r7x-i-enm (dk-skolem! (dk-fact! 'well-ordering-principle r7x-i-a)))
(define r7x-i-psi
  (cadr (dk-fact! 'enum-append-is-bijection r7x-i-n r7x-i-a r7x-i-x r7x-i-enm)))

;; ... and flip it, so card-bij has both directions
(dk-fact! 'inverse-bij-is-bijection r7x-i-segs r7x-i-uni r7x-i-psi)
(define r7x-i-inv (list 'INVERSE-BIJ r7x-i-psi r7x-i-segs r7x-i-uni))

(have! (list 'AND (list 'IN r7x-i-inv (list 'BIJECTION r7x-i-uni r7x-i-segs))
                  (list 'IN r7x-i-psi (list 'BIJECTION r7x-i-segs r7x-i-uni))))
(dk-fact! 'card-bij (list 'succ r7x-i-n) r7x-i-uni r7x-i-inv r7x-i-psi)

;; the statement's successor is the ORDINAL one; on NN the two agree
(dk-fact! 'ord-succ-nn r7x-i-n)
(subst (list '= (list 'succ_ORD r7x-i-n) (list 'succ r7x-i-n)))
(ass)

(r7x-check! 'card-insert-curried)
(qed 'card-insert-curried)
(topic! 'card-insert-curried 'combinatorial)

;;; =====================================================================
;;; seg-restrict-is-bijection -- an enumeration of a set restricted to the
;;; SHORTER segment is a bijection onto its image.
;;;
;;;   n_ in NN,  g_ in BIJECTION(OS(succ n_), b_)
;;;     =>  (VNB-LAMBDA i_ OS(n_). g_(i_))  in  BIJECTION(OS(n_), IMAGE(g_, OS(n_)))
;;;
;;; This is the PEEL that the disjoint-union induction needs and that the finite
;;; CARD layer did not have: card-finite.scm computes a cardinal from a
;;; bijection it is handed, and nothing produced a bijection for the set with one
;;; point removed.  Taking the image rather than a set difference is what keeps it
;;; short: surjectivity onto IMAGE is image-membership-iff read backwards, and no
;;; `difference-membership' (which the tree lacks) is needed anywhere.
;;; =====================================================================

(define r7x-restr-stmt
  '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL b_ (FORALL g_ (IMPLIES (IN g_ (BIJECTION (ORD-SEGMENT (succ n_)) b_))
       (IN (VNB-LAMBDA i_ (ORD-SEGMENT n_) (g_ i_))
           (BIJECTION (ORD-SEGMENT n_) (IMAGE g_ (ORD-SEGMENT n_))))))))))

(sp (make-wff r7x-restr-stmt))
(dk-peel!)

(define r7x-r-n (cadr (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                                (eq? (caddr f) 'NN)))
                               "n in NN")))
(define r7x-r-bij (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                            (r7x-head? (caddr f) 'BIJECTION)))
                           "g in BIJECTION"))
(define r7x-r-g    (cadr r7x-r-bij))
(define r7x-r-b    (caddr (caddr r7x-r-bij)))
(define r7x-r-segn (list 'ORD-SEGMENT r7x-r-n))
(define r7x-r-segs (list 'ORD-SEGMENT (list 'succ r7x-r-n)))

(define r7x-r-parts (r7x-open-bijection! r7x-r-bij))
(define r7x-r-fun  (car   r7x-r-parts))
(define r7x-r-inj  (cadr  r7x-r-parts))
(define r7x-r-surj (caddr r7x-r-parts))

(dk-fact! 'nn-succ-closed r7x-r-n)
(dk-fact! 'nn-subset-ord r7x-r-n)
(dk-fact! 'ord-segment-is-set r7x-r-n)

;; an index of OS(n) is an index of OS(succ n), and g sends it into b_
(define (r7x-r-lift! v)
  (have! (list 'IN v r7x-r-segs)
         (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
  (dk-fact! 'fun-apply-type-c r7x-r-g r7x-r-segs r7x-r-b v))

(mac 'bijection-membership-iff)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ;; (IN lam (FUN OS(n) IMAGE))
       ((r7x-head? g 'IN)
        (let* ((ls   (dk-opened (lambda () (lam-t))))
               (st?  (lambda (q) (and (r7x-head? q 'IN) (eq? (caddr q) 'SET))))
               (setl (r7x-leaf ls st? "sethood of OS(n)"))
               (ptw  (r7x-leaf ls (lambda (q) (not (st? q))) "pointwise typing")))
          (dk-focus! setl)
          (ass)
          (dk-focus! ptw)
          (dk-peel!)
          (let ((iv (cadr (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                                    (equal? (caddr f) r7x-r-segn)))
                                   "the peeled index"))))
            (r7x-r-lift! iv)
            (dk-image-goal!)
            (ew iv)
            (dk-conj-close! (lambda () (if (r7x-head? (dk-goal) 'IN) (ass) (rfl)))))))
       ;; injectivity
       ((r7x-head? (caddr (caddr g)) 'FORALL)
        (dk-peel!)
        (let* ((gl (dk-goal)) (av (cadr gl)) (bv (caddr gl)))
          (r7x-r-lift! av)
          (r7x-r-lift! bv)
          (r7x-beta-h!)
          (r7x-apply! r7x-r-inj av bv)
          (ass)))
       ;; surjectivity
       (#t
        (let* ((mem (car (dk-peel!)))
               (wv  (cadr mem)))
          (dk-image-hyp! mem)
          (let ((z (dk-skolem! (dk-pick (lambda (f) (and (r7x-head? f 'FORSOME)
                                                         (dk-contains? f wv)))
                                        "the image witness"))))
            (ew z)
            (dk-conj-close!
             (lambda () (if (r7x-head? (dk-goal) 'IN) (ass) (begin (lam-b) (ass))))))))))))

(r7x-check! 'seg-restrict-is-bijection)
(qed 'seg-restrict-is-bijection)
(topic! 'seg-restrict-is-bijection 'combinatorial)

;;; =====================================================================
;;; card-seg-image -- the image of the SHORTER segment has cardinal n_.
;;;
;;;   n_ in NN,  g_ in BIJECTION(OS(succ n_), b_)
;;;     =>  CARD(IMAGE(g_, OS(n_))) = n_
;;;
;;; The restriction above, flipped by inverse-bij-is-bijection and read by
;;; card-bij.  With seg-image-insert below this is the PEEL of a finite
;;; set: b_ is IMAGE(g_, OS n_) with one further point, and the image half has
;;; cardinal exactly one less.
;;; =====================================================================

(define r7x-simg-stmt
  '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL b_ (FORALL g_ (IMPLIES (IN g_ (BIJECTION (ORD-SEGMENT (succ n_)) b_))
       (= (CARD (IMAGE g_ (ORD-SEGMENT n_))) n_)))))))

(sp (make-wff r7x-simg-stmt))
(dk-peel!)
(define r7x-s-goal (dk-goal))                       ; (= (CARD (IMAGE g (OS n))) n)
(define r7x-s-im   (cadr (cadr r7x-s-goal)))
(define r7x-s-g    (cadr r7x-s-im))
(define r7x-s-segn (caddr r7x-s-im))
(define r7x-s-n    (caddr r7x-s-goal))
(define r7x-s-b    (caddr (caddr (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                                           (r7x-head? (caddr f) 'BIJECTION)))
                                          "g in BIJECTION"))))

(dk-fact! 'nn-subset-ord r7x-s-n)
(dk-fact! 'ord-segment-is-set r7x-s-n)
(dk-fact! 'image-set r7x-s-g r7x-s-segn)            ; (IN IM SET)
(define r7x-s-lam
  (cadr (dk-fact! 'seg-restrict-is-bijection r7x-s-n r7x-s-b r7x-s-g)))
(dk-fact! 'inverse-bij-is-bijection r7x-s-segn r7x-s-im r7x-s-lam)
(define r7x-s-inv (list 'INVERSE-BIJ r7x-s-lam r7x-s-segn r7x-s-im))
(have! (list 'AND (list 'IN r7x-s-inv (list 'BIJECTION r7x-s-im r7x-s-segn))
                  (list 'IN r7x-s-lam (list 'BIJECTION r7x-s-segn r7x-s-im))))
(dk-fact! 'card-bij r7x-s-n r7x-s-im r7x-s-inv r7x-s-lam)
(ass)

(r7x-check! 'card-seg-image)
(qed 'card-seg-image)
(topic! 'card-seg-image 'combinatorial)

;;; =====================================================================
;;; seg-image-subset -- the image of the shorter segment lies in b_.
;;; (image-subset-codomain, structure-library/injection.scm:152, is stated for
;;; the FUN domain itself and is an UNWARRANTED axiom besides; this is the
;;; sub-domain form and it is three citations.)
;;; =====================================================================

(define r7x-sub-stmt
  '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL b_ (FORALL g_ (IMPLIES (IN g_ (BIJECTION (ORD-SEGMENT (succ n_)) b_))
       (FORALL w_ (IMPLIES (IN w_ (IMAGE g_ (ORD-SEGMENT n_))) (IN w_ b_)))))))))

(sp (make-wff r7x-sub-stmt))
(dk-peel!)
(define r7x-u-goal (dk-goal))                       ; (IN w b)
(define r7x-u-w    (cadr r7x-u-goal))
(define r7x-u-b    (caddr r7x-u-goal))
(define r7x-u-bij  (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                             (r7x-head? (caddr f) 'BIJECTION)))
                            "g in BIJECTION"))
(define r7x-u-g    (cadr r7x-u-bij))
(define r7x-u-segs (cadr (caddr r7x-u-bij)))
(define r7x-u-n    (cadr (cadr r7x-u-segs)))
(define r7x-u-segn (list 'ORD-SEGMENT r7x-u-n))
(define r7x-u-parts (r7x-open-bijection! r7x-u-bij))

(dk-image-hyp! (list 'IN r7x-u-w (list 'IMAGE r7x-u-g r7x-u-segn)))
(define r7x-u-z
  (dk-skolem! (dk-pick (lambda (f) (and (r7x-head? f 'FORSOME) (dk-contains? f r7x-u-w)))
                       "the image witness")))
(have! (list 'IN r7x-u-z r7x-u-segs)
       (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
(dk-fact! 'fun-apply-type-c r7x-u-g r7x-u-segs r7x-u-b r7x-u-z)
(dk-fact! 'eq-sym (list r7x-u-g r7x-u-z) r7x-u-w)
(subst (list '= r7x-u-w (list r7x-u-g r7x-u-z)))
(ass)

(r7x-check! 'seg-image-subset)
(qed 'seg-image-subset)
(topic! 'seg-image-subset 'combinatorial)

;;; =====================================================================
;;; seg-image-omits-top -- the top value g_(n_) is NOT in the image of the
;;; shorter segment.  Injectivity, and "n is not below itself".
;;; =====================================================================

(define r7x-omit-stmt
  '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL b_ (FORALL g_ (IMPLIES (IN g_ (BIJECTION (ORD-SEGMENT (succ n_)) b_))
       (NOT (IN (g_ n_) (IMAGE g_ (ORD-SEGMENT n_))))))))))

(sp (make-wff r7x-omit-stmt))
(dk-peel!)
(define r7x-o-bij  (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                             (r7x-head? (caddr f) 'BIJECTION)))
                            "g in BIJECTION"))
(define r7x-o-g    (cadr r7x-o-bij))
(define r7x-o-segs (cadr (caddr r7x-o-bij)))
(define r7x-o-n    (cadr (cadr r7x-o-segs)))
(define r7x-o-segn (list 'ORD-SEGMENT r7x-o-n))
(define r7x-o-pt   (list r7x-o-g r7x-o-n))
(define r7x-o-parts (r7x-open-bijection! r7x-o-bij))
(define r7x-o-inj  (cadr r7x-o-parts))

(dk-fact! 'ord-segment-self r7x-o-n)                ; (NOT (IN n (OS n)))
(have! (list 'IN r7x-o-n r7x-o-segs)
       (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
(di)                                                ; assume the membership, goal FALSITY
(dk-image-hyp! (list 'IN r7x-o-pt (list 'IMAGE r7x-o-g r7x-o-segn)))
(define r7x-o-z
  (dk-skolem! (dk-pick (lambda (f) (and (r7x-head? f 'FORSOME) (dk-contains? f r7x-o-pt)))
                       "the image witness")))
(have! (list 'IN r7x-o-z r7x-o-segs)
       (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
(r7x-apply! r7x-o-inj r7x-o-z r7x-o-n)              ; (= z n)
(have! (list 'NOT (list 'IN r7x-o-z r7x-o-segn))
       (lambda () (subst (list '= r7x-o-z r7x-o-n)) (ass)))
(ai (list 'NOT (list 'IN r7x-o-z r7x-o-segn)))

(r7x-check! 'seg-image-omits-top)
(qed 'seg-image-omits-top)
(topic! 'seg-image-omits-top 'combinatorial)

;;; =====================================================================
;;; seg-image-insert -- a finite set IS its shorter-segment image plus the top
;;; value:   b_ = IMAGE(g_, OS(n_)) u {g_(n_)}.
;;;
;;; Class-extensionality over the surjectivity of g_ and the segment successor
;;; iff.  With card-seg-image and seg-image-omits-top this is the PEEL:
;;; every finite set of cardinal succ n_ is an INSERT of a set of cardinal n_,
;;; which is what an induction on the cardinal needs and what the CARD
;;; layer lacked.
;;; =====================================================================

(define r7x-ins-stmt
  '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL b_ (FORALL g_ (IMPLIES (IN g_ (BIJECTION (ORD-SEGMENT (succ n_)) b_))
       (= b_ (UNION (IMAGE g_ (ORD-SEGMENT n_)) (PAIR (g_ n_) (g_ n_))))))))))

(sp (make-wff r7x-ins-stmt))
(dk-peel!)
(define r7x-n-goal (dk-goal))                    ; (= b (UNION IM (PAIR pt pt)))
(define r7x-n-b    (cadr r7x-n-goal))
(define r7x-n-uni  (caddr r7x-n-goal))
(define r7x-n-im   (cadr r7x-n-uni))
(define r7x-n-g    (cadr r7x-n-im))
(define r7x-n-segn (caddr r7x-n-im))
(define r7x-n-n    (cadr r7x-n-segn))
(define r7x-n-segs (list 'ORD-SEGMENT (list 'succ r7x-n-n)))
(define r7x-n-pt   (cadr (caddr r7x-n-uni)))
(define r7x-n-bij  (list 'IN r7x-n-g (list 'BIJECTION r7x-n-segs r7x-n-b)))

(dk-fact! 'nn-subset-ord r7x-n-n)
(dk-fact! 'ord-segment-is-set r7x-n-n)
(dk-fact! 'image-set r7x-n-g r7x-n-segn)
(have! (list 'IN r7x-n-n r7x-n-segs)
       (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
;; the two projections in HAVE! LANES: `mac-h' REPLACES the membership it
;; unfolds, and (IN g_ (BIJECTION ...)) is what seg-image-subset detaches
;; against three lines further down.
(have! (list 'IN r7x-n-g (list 'FUN r7x-n-segs r7x-n-b))
       (lambda () (r7x-open-bijection! r7x-n-bij) (ass)))
(define r7x-n-surj
  (let ((st (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r7x-n-b)
              (list 'FORSOME 'z_ (list 'AND (list 'IN 'z_ r7x-n-segs)
                                       (list '= (list r7x-n-g 'z_) 'w_)))))))
    (have! st (lambda () (r7x-open-bijection! r7x-n-bij) (ass)))
    st))
(dk-fact! 'fun-apply-type-c r7x-n-g r7x-n-segs r7x-n-b r7x-n-n)    ; (IN pt b)
(dk-fact! 'membership-implies-sethood r7x-n-pt r7x-n-b)            ; (IN pt SET)
(r7x-insert-set! r7x-n-im r7x-n-pt)                                ; (IN (IM u {pt}) SET)

(have! (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ r7x-n-b) (list 'IN 'y_ r7x-n-uni)))
  (lambda ()
    (let ((yv (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (for-each
       (lambda (l)
         (dk-focus! l)
         (if (equal? (caddr (dk-goal)) r7x-n-b)
             ;; (IN y IM u {pt})  |-  (IN y b)
             (begin
               (have! (list 'IMPLIES (list 'IN yv r7x-n-im) (list 'IN yv r7x-n-b))
                      (lambda ()
                        (di)
                        (dk-fact! 'seg-image-subset r7x-n-n r7x-n-b r7x-n-g yv)
                        (ass)))
               (have! (list 'IMPLIES (list 'IN yv (list 'PAIR r7x-n-pt r7x-n-pt))
                            (list 'IN yv r7x-n-b))
                      (lambda ()
                        (di)
                        (dk-fact! 'pairing-membership r7x-n-pt r7x-n-pt yv)
                        (have! (list '= yv r7x-n-pt) (lambda () (prop)))
                        (subst (list '= yv r7x-n-pt))
                        (ass)))
               (r7x-mac-h! 'union-membership (list 'IN yv r7x-n-uni))
               (prop))
             ;; (IN y b)  |-  (IN y IM u {pt})
             (let ((z (dk-skolem! (r7x-apply! r7x-n-surj yv))))
               (mac 'union-membership)
               (use-em (list 'IN z r7x-n-segn)
                 (lambda ()
                   (oi-l)
                   (dk-image-goal!)
                   (ew z)
                   (dk-conj-close! (lambda () (ass))))
                 (lambda ()
                   (r7x-mac-h! 'ord-segment-nn-succ (list 'IN z r7x-n-segs))
                   (have! (list '= z r7x-n-n) (lambda () (prop)))
                   (have! (list '= (list r7x-n-g z) r7x-n-pt)
                          (lambda () (subst (list '= z r7x-n-n)) (rfl)))
                   (dk-fact! 'eq-sym (list r7x-n-g z) yv)
                   (dk-fact! 'eq-trans yv (list r7x-n-g z) r7x-n-pt)
                   (oi-r)
                   (dk-fact! 'pairing-membership r7x-n-pt r7x-n-pt yv)
                   (prop))))))
       (dk-opened (lambda () (di)))))))

(dk-fact! 'class-extensionality r7x-n-b r7x-n-uni)
(ass)

(r7x-check! 'seg-image-insert)
(qed 'seg-image-insert)
(topic! 'seg-image-insert 'combinatorial)

;;; =====================================================================
;;; Two set-theoretic bricks the induction below needs and the tree lacks.
;;;   card-zero-is-empty   CARD(b_) = 0  =>  b_ = EMPTY-SET
;;;   intersection-empty-transfer  disjointness passes to a subclass
;;; (union-empty-right and union-assoc are already PROVEN in
;;; theorem-library/fin-subsets.scm; union-assoc is stated the other way round,
;;; so the induction below flips its instance with eq-sym.)
;;; =====================================================================

(sp (make-wff '(FORALL b_ (IMPLIES (IN b_ SET)
                 (IMPLIES (= (CARD b_) 0) (= b_ EMPTY-SET))))))
(dk-peel!)
(define r7x-z-b (cadr (dk-goal)))
(define r7x-z-cs (list 'CARD r7x-z-b))
(fact 'empty-set-is-set)
(define r7x-z-phi (dk-skolem! (dk-fact! 'well-ordering-principle r7x-z-b)))
(define r7x-z-seg (list 'ORD-SEGMENT r7x-z-cs))
(define r7x-z-surj
  (let ((st (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ r7x-z-b)
              (list 'FORSOME 'z_ (list 'AND (list 'IN 'z_ r7x-z-seg)
                                       (list '= (list r7x-z-phi 'z_) 'w_)))))))
    (have! st (lambda () (r7x-open-bijection! (list 'IN r7x-z-phi
                                                    (list 'BIJECTION r7x-z-seg r7x-z-b)))
                         (ass)))
    st))
(dk-fact! 'eq-sym r7x-z-cs 0)                      ; (= 0 (CARD b))
(have! (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ r7x-z-b) '(IN y_ EMPTY-SET)))
  (lambda ()
    (let ((yv (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (for-each
       (lambda (l)
         (dk-focus! l)
         (if (equal? (caddr (dk-goal)) r7x-z-b)
             (begin (fact 'empty-set-has-no-members yv)
                    (ai (list 'NOT (list 'IN yv 'EMPTY-SET))))
             (let ((z (dk-skolem! (r7x-apply! r7x-z-surj yv))))
               (have! (list 'IN z '(ORD-SEGMENT 0))
                      (lambda () (subst (list '= 0 r7x-z-cs)) (ass)))
               (fact 'ord-segment-zero-no-members z)
               (ai (list 'NOT (list 'IN z '(ORD-SEGMENT 0)))))))
       (dk-opened (lambda () (di)))))))
(dk-fact! 'class-extensionality r7x-z-b 'EMPTY-SET)
(ass)
(r7x-check! 'card-zero-is-empty)
(qed 'card-zero-is-empty)
(gloss! 'card-zero-is-empty
  "A set whose cardinal is 0 is EMPTY-SET.  The converse of card-empty.  Proven here
   rather than by finite-set-induction (as theorem-library/rake-combinatorics.scm did
   until 2026-09-20), because finite-set-induction is now itself a theorem PROVEN FROM
   this one.")
(topic! 'card-zero-is-empty 'combinatorial)

(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ SET)
     (FORALL b_ (FORALL c_
       (IMPLIES (= (INTERSECTION a_ b_) EMPTY-SET)
         (IMPLIES (FORALL w_ (IMPLIES (IN w_ c_) (IN w_ b_)))
           (= (INTERSECTION a_ c_) EMPTY-SET)))))))))
(dk-peel!)
(define r7x-t-goal (dk-goal))
(define r7x-t-ac (cadr r7x-t-goal))                 ; (INTERSECTION a c)
(define r7x-t-a  (cadr r7x-t-ac))
(define r7x-t-c  (caddr r7x-t-ac))
(define r7x-t-sub (dk-pick (lambda (f) (and (r7x-head? f 'FORALL)
                                            (r7x-head? (r7x-body f) 'IN)))
                           "the subclass hypothesis"))
(define r7x-t-b (caddr (r7x-body r7x-t-sub)))
(define r7x-t-ab (list 'INTERSECTION r7x-t-a r7x-t-b))
(fact 'empty-set-is-set)
(have! (list 'OR (list 'IN r7x-t-a 'SET) (list 'IN r7x-t-c 'SET)) (lambda () (oi-l) (ass)))
(dk-fact! 'intersection-set-closure r7x-t-a r7x-t-c)
(dk-fact! 'eq-sym r7x-t-ab 'EMPTY-SET)              ; (= EMPTY-SET (INTERSECTION a b))
(have! (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ r7x-t-ac) '(IN y_ EMPTY-SET)))
  (lambda ()
    (let ((yv (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (for-each
       (lambda (l)
         (dk-focus! l)
         (if (equal? (caddr (dk-goal)) r7x-t-ac)
             (begin (fact 'empty-set-has-no-members yv)
                    (ai (list 'NOT (list 'IN yv 'EMPTY-SET))))
             (begin
               (r7x-mac-h! 'intersection-membership (list 'IN yv r7x-t-ac))
               (dk-split! (list 'AND (list 'IN yv r7x-t-a) (list 'IN yv r7x-t-c)))
               (r7x-apply! r7x-t-sub yv)
               (have! (list 'IN yv r7x-t-ab)
                      (lambda () (mac 'intersection-membership) (prop)))
               (subst (list '= 'EMPTY-SET r7x-t-ab))
               (ass))))
       (dk-opened (lambda () (di)))))))
(dk-fact! 'class-extensionality r7x-t-ac 'EMPTY-SET)
(ass)
(r7x-check! 'intersection-empty-transfer)
(qed 'intersection-empty-transfer)
(topic! 'intersection-empty-transfer 'plumbing)

;;; =====================================================================
;;; card-union-disjoint-curried -- finite additivity of the DEFINED cardinal.
;;;
;;;   a_, b_ in SET,  CARD(a_), CARD(b_) in NN,  a_ n b_ = {}
;;;     =>  CARD(a_ u b_) = CARD(a_) + CARD(b_)
;;;
;;; WHICH INDUCTION, AND WHY NOT `finite-set-induction'.  The brief asks what
;;; form of induction is available without circularity.  `finite-set-induction'
;;; (structure-library/cardinality.scm:108) is PRIMITIVE and stated with the
;;; AXIOMATISED CARD, so using it here would prove a CARD law from a CARD
;;; axiom -- exactly the dependency this file exists to remove.  What is
;;; available is ORDINARY NN INDUCTION on the cardinal of the second set, and
;;; the step needs a PEEL: a set of cardinal succ n_ written as a set of cardinal
;;; n_ plus one fresh point.  That peel is what seg-restrict-is-bijection /
;;; card-seg-image / seg-image-insert / seg-image-omits-top supply, off the
;;; enumeration well-ordering-principle produces.  The base case is
;;; card-zero-is-empty.
;;;
;;; (The same four bricks give a CARD `finite-set-induction' directly: the
;;; class C is carried from CARD(S) = n_ to CARD(S) = succ n_ by
;;; exactly this step.  Stated in the closing block; not proved here.)
;;; =====================================================================

(define r7x-uni-ind-stmt
  '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL a_ (IMPLIES (IN a_ SET)
       (IMPLIES (IN (CARD a_) NN)
         (FORALL b_ (IMPLIES (IN b_ SET)
           (IMPLIES (= (CARD b_) n_)
             (IMPLIES (= (INTERSECTION a_ b_) EMPTY-SET)
               (= (CARD (UNION a_ b_)) (+ (CARD a_) n_))))))))))))

(sp (make-wff r7x-uni-ind-stmt))

(define (r7x-do-base!)
  (dk-peel!)
  (let* ((gl (dk-goal))
         (uni (cadr (cadr gl)))
         (av (cadr uni))
         (bv (caddr uni)))
    (dk-fact! 'card-zero-is-empty bv)              ; (= b EMPTY-SET)
    (subst (list '= bv 'EMPTY-SET))
    (dk-fact! 'union-empty-right av)
    (subst (list '= (list 'UNION av 'EMPTY-SET) av))
    (dk-fact! 'nn-add-zero (list 'CARD av))
    (subst (list '= (list '+ (list 'CARD av) 0) (list 'CARD av)))
    (rfl)))

(define (r7x-do-step!)
  (dk-peel!)
  (let* ((gl   (dk-goal))                 ; (= (CARD (UNION a b)) (+ (CARD a) (succ n)))
         (uni  (cadr (cadr gl)))
         (av   (cadr uni))
         (bv   (caddr uni))
         (nv   (cadr (caddr (caddr gl))))
         (cs-a (list 'CARD av))
         (segs (list 'ORD-SEGMENT (list 'succ nv)))
         (segn (list 'ORD-SEGMENT nv))
         (ih   (dk-pick (lambda (f) (and (r7x-head? f 'FORALL)
                                         (dk-contains? f 'CARD)))
                        "the induction hypothesis")))
    (dk-fact! 'nn-succ-closed nv)
    (dk-fact! 'nn-subset-ord nv)
    (dk-fact! 'ord-segment-is-set nv)
    (fact 'empty-set-is-set)
    ;; enumerate b_ by its cardinal succ n_
    (let* ((gv   (dk-skolem! (dk-fact! 'well-ordering-principle bv)))
           (bij  (list 'IN gv (list 'BIJECTION segs bv)))
           (im   (list 'IMAGE gv segn))
           (pt   (list gv nv))
           (uai  (list 'UNION av im)))
      (dk-fact! 'eq-sym (list 'CARD bv) (list 'succ nv))
      (have! bij (lambda () (subst (list '= (list 'succ nv) (list 'CARD bv))) (ass)))
      (have! (list 'IN gv (list 'FUN segs bv))
             (lambda () (r7x-open-bijection! bij) (ass)))
      (have! (list 'IN nv segs) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
      (dk-fact! 'fun-apply-type-c gv segs bv nv)            ; (IN pt b)
      (dk-fact! 'membership-implies-sethood pt bv)          ; (IN pt SET)
      (dk-fact! 'image-set gv segn)                         ; (IN IM SET)
      (dk-fact! 'card-seg-image nv bv gv)              ; (= (CARD IM) n)
      (have! (list 'IN (list 'CARD im) 'NN)
             (lambda () (subst (list '= (list 'CARD im) nv)) (ass)))
      (define r7x-w-ins (dk-fact! 'seg-image-insert nv bv gv))   ; (= b (IM u {pt}))
      (dk-fact! 'seg-image-omits-top nv bv gv)              ; (NOT (IN pt IM))
      (dk-fact! 'seg-image-subset nv bv gv)                 ; IM subclass of b
      (dk-fact! 'intersection-empty-transfer av bv im)      ; (= (INTERSECTION a IM) {})
      ;; the induction hypothesis at (a_, IM)
      (define r7x-w-ih (r7x-apply! ih av im))               ; (= (CARD (a u IM)) (CS a + n))
      (have! (list 'AND (list 'IN av 'SET) (list 'IN im 'SET)))
      (dk-fact! 'union-set-closure av im)                   ; (IN (a u IM) SET)
      ;; (IN (+ (CARD a) n) NN) is landed in the MAIN branch, not inside the
      ;; lane below: ord-succ-nn is cited at that very term twelve lines on, and a
      ;; typing that lands only on a have!'s side branch leaves the citation
      ;; undetached -- `fact' then lands the IMPLICATION and the following `subst'
      ;; reports "equality not in context", blaming the rewrite.
      (have! (list 'AND (list 'IN cs-a 'NN) (list 'IN nv 'NN)))
      (dk-fact! 'nn-add-closed cs-a nv)
      (have! (list 'IN (list 'CARD uai) 'NN)
             (lambda () (subst r7x-w-ih) (ass)))
      ;; pt is fresh for a_ u IM
      (have! (list 'NOT (list 'IN pt av))
             (lambda ()
               (di)
               (have! (list 'IN pt (list 'INTERSECTION av bv))
                      (lambda () (mac 'intersection-membership) (prop)))
               (dk-fact! 'eq-sym (list 'INTERSECTION av bv) 'EMPTY-SET)
               (have! (list 'IN pt 'EMPTY-SET)
                      (lambda () (subst (list '= 'EMPTY-SET (list 'INTERSECTION av bv))) (ass)))
               (fact 'empty-set-has-no-members pt)
               (ai (list 'NOT (list 'IN pt 'EMPTY-SET)))))
      ;; `prop' has an atom cap and this context is ~25 formulas deep, so the
      ;; three that matter are isolated first (CLAUDE.md: a `prop' that declines
      ;; with an empty countermodel did not look at the right atoms).
      (have! (list 'NOT (list 'IN pt uai))
             (lambda ()
               (di)
               (r7x-mac-h! 'union-membership (list 'IN pt uai))
               (dk-only! (list 'OR (list 'IN pt av) (list 'IN pt im))
                         (list 'NOT (list 'IN pt av))
                         (list 'NOT (list 'IN pt im)))
               (prop)))
      ;; ... so card-insert-curried applies, and the rest is rewriting
      (define r7x-w-cin (dk-fact! 'card-insert-curried uai pt))
      (subst r7x-w-ins)
      (dk-fact! 'union-assoc av im (list 'PAIR pt pt))
      (dk-fact! 'eq-sym (list 'UNION uai (list 'PAIR pt pt))
                        (list 'UNION av (list 'UNION im (list 'PAIR pt pt))))
      (subst (list '= (list 'UNION av (list 'UNION im (list 'PAIR pt pt)))
                      (list 'UNION uai (list 'PAIR pt pt))))
      (subst r7x-w-cin)
      (subst r7x-w-ih)
      (dk-fact! 'ord-succ-nn (list '+ cs-a nv))
      (subst (list '= (list 'succ_ORD (list '+ cs-a nv)) (list 'succ (list '+ cs-a nv))))
      (dk-fact! 'nn-add-succ cs-a nv)
      (subst (list '= (list '+ cs-a (list 'succ nv)) (list 'succ (list '+ cs-a nv))))
      (rfl))))

(let* ((br   (use-induction))
       (base (cdr (assq 'base br)))
       (step (cdr (assq 'step br))))
  (dk-focus! base)
  (r7x-do-base!)
  (dk-focus! step)
  (r7x-do-step!))

(r7x-check! 'card-union-disjoint-ind)
(qed 'card-union-disjoint-ind)
(topic! 'card-union-disjoint-ind 'combinatorial)

(define r7x-uni-stmt
  '(FORALL a_ (IMPLIES (IN a_ SET)
     (IMPLIES (IN (CARD a_) NN)
       (FORALL b_ (IMPLIES (IN b_ SET)
         (IMPLIES (IN (CARD b_) NN)
           (IMPLIES (= (INTERSECTION a_ b_) EMPTY-SET)
             (= (CARD (UNION a_ b_))
                (+ (CARD a_) (CARD b_)))))))))))

(sp (make-wff r7x-uni-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))
       (uni (cadr (cadr gl)))
       (av  (cadr uni))
       (bv  (caddr uni)))
  (have! (list '= (list 'CARD bv) (list 'CARD bv)) (lambda () (rfl)))
  (dk-fact! 'card-union-disjoint-ind (list 'CARD bv) av bv)
  (ass))

(r7x-check! 'card-union-disjoint-curried)
(qed 'card-union-disjoint-curried)
(topic! 'card-union-disjoint-curried 'combinatorial)

;;; =====================================================================
;;; finite-set-induction -- `finite-set-induction'
;;; (structure-library/cardinality.scm:108, PRIMITIVE) character for character
;;; with CARD in place of CARD.
;;;
;;; The axiom's own comment calls it "derivable from nn-induction via
;;; card-finite-bij + card-insert"; that is exactly this proof, with
;;; well-ordering-principle for the first and the four peel lemmas above for the
;;; second.  It is stated with the AND antecedents the axiom has, so that the
;;; rename can substitute one for the other without touching a citer.
;;;
;;; The auxiliary carries the induction variable OUTERMOST -- `ni' tests the
;;; goal's SHAPE -- and the class c_ is a bound variable of it, so no `cut'
;;; generalization is needed.
;;; =====================================================================

(define r7x-fsi-step
  '(FORALL s_ (IMPLIES (AND (IN s_ SET) (AND (IN (CARD s_) NN) (IN s_ c_)))
     (FORALL x_ (IMPLIES (AND (IN x_ SET) (NOT (IN x_ s_)))
       (IN (UNION s_ (PAIR x_ x_)) c_))))))

(sp (make-wff
     (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
       (list 'FORALL 'c_ (list 'IMPLIES '(IN EMPTY-SET c_)
         (list 'IMPLIES r7x-fsi-step
           '(FORALL s_ (IMPLIES (IN s_ SET)
              (IMPLIES (= (CARD s_) n_) (IN s_ c_)))))))))))

(define (r7x-fsi-base!)
  (dk-peel!)
  (let* ((gl (dk-goal))                               ; (IN s c)
         (sv (cadr gl)))
    (dk-fact! 'card-zero-is-empty sv)
    (subst (list '= sv 'EMPTY-SET))
    (ass)))

(define (r7x-fsi-step!)
  (dk-peel!)
  (let* ((gl   (dk-goal))                             ; (IN s c)
         (sv   (cadr gl))
         (cv   (caddr gl))
         (nv   (cadr (caddr (dk-pick (lambda (f) (and (r7x-head? f '=)
                                                      (equal? (cadr f) (list 'CARD sv))))
                                     "CARD(s) = succ n"))))
         (segs (list 'ORD-SEGMENT (list 'succ nv)))
         (segn (list 'ORD-SEGMENT nv))
         ;; the IH is the whole BODY at n_, class variable and all -- `ni' peels
         ;; only the NN binder -- so it still quantifies c_ and is instantiated at
         ;; the peeled class below.  It is the FORALL that mentions EMPTY-SET;
         ;; the insert-closure hypothesis is the one that does not.
         (ih   (dk-pick (lambda (f) (and (r7x-head? f 'FORALL)
                                         (dk-contains? f 'EMPTY-SET)))
                        "the induction hypothesis"))
         (stp  (dk-pick (lambda (f) (and (r7x-head? f 'FORALL)
                                         (dk-contains? f 'UNION)
                                         (not (dk-contains? f 'EMPTY-SET))))
                        "the insert-closure hypothesis")))
    (dk-fact! 'nn-succ-closed nv)
    (dk-fact! 'nn-subset-ord nv)
    (dk-fact! 'ord-segment-is-set nv)
    (let* ((gv  (dk-skolem! (dk-fact! 'well-ordering-principle sv)))
           (bij (list 'IN gv (list 'BIJECTION segs sv)))
           (im  (list 'IMAGE gv segn))
           (pt  (list gv nv)))
      (dk-fact! 'eq-sym (list 'CARD sv) (list 'succ nv))
      (have! bij (lambda () (subst (list '= (list 'succ nv) (list 'CARD sv))) (ass)))
      (have! (list 'IN gv (list 'FUN segs sv))
             (lambda () (r7x-open-bijection! bij) (ass)))
      (have! (list 'IN nv segs) (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
      (dk-fact! 'fun-apply-type-c gv segs sv nv)
      (dk-fact! 'membership-implies-sethood pt sv)
      (dk-fact! 'image-set gv segn)
      (dk-fact! 'card-seg-image nv sv gv)
      (have! (list 'IN (list 'CARD im) 'NN)
             (lambda () (subst (list '= (list 'CARD im) nv)) (ass)))
      (dk-fact! 'seg-image-insert nv sv gv)
      (dk-fact! 'seg-image-omits-top nv sv gv)
      (r7x-apply! ih cv im)                           ; (IN IM c)
      (have! (list 'AND (list 'IN im 'SET)
                   (list 'AND (list 'IN (list 'CARD im) 'NN) (list 'IN im cv))))
      (have! (list 'AND (list 'IN pt 'SET) (list 'NOT (list 'IN pt im))))
      (r7x-apply! stp im pt)                          ; (IN (IM u {pt}) c)
      (subst (list '= sv (list 'UNION im (list 'PAIR pt pt))))
      (ass))))

(let* ((br   (use-induction))
       (base (cdr (assq 'base br)))
       (step (cdr (assq 'step br))))
  (dk-focus! base)
  (r7x-fsi-base!)
  (dk-focus! step)
  (r7x-fsi-step!))

(r7x-check! 'card-finite-induction-aux)
(qed 'card-finite-induction-aux)
(topic! 'card-finite-induction-aux 'combinatorial)

(sp (make-wff
     (list 'FORALL 'c_
       (list 'IMPLIES (list 'AND '(IN EMPTY-SET c_) r7x-fsi-step)
         '(FORALL s_ (IMPLIES (AND (IN s_ SET) (IN (CARD s_) NN)) (IN s_ c_)))))))
(dk-peel!)
(let* ((gl (dk-goal))
       (sv (cadr gl))
       (cv (caddr gl)))
  (dk-split-all! (list (dk-pick (lambda (f) (and (r7x-head? f 'AND)
                                                 (equal? (cadr f) '(IN EMPTY-SET c_))))
                                "the two hypotheses")
                       (dk-pick (lambda (f) (and (r7x-head? f 'AND)
                                                 (equal? (cadr f) (list 'IN sv 'SET))))
                                "s in SET and finite")))
  (have! (list '= (list 'CARD sv) (list 'CARD sv)) (lambda () (rfl)))
  (dk-fact! 'card-finite-induction-aux (list 'CARD sv) cv sv)
  (ass))

(r7x-check! 'finite-set-induction)
(qed 'finite-set-induction)
(topic! 'finite-set-induction 'combinatorial)

;;; =====================================================================
;;; injection-image-is-bijection / card-image-injection-curried --
;;; `card-image-injection' (structure-library/injection.scm:162, PRIMITIVE) for
;;; the DEFINED cardinal.
;;;
;;; The axiom's own comment is the proof ("phi restricted to dm is a bijection
;;; dm -> IMAGE(phi, dm)"), and it was never run.  The restriction lemma is
;;; seg-restrict-is-bijection with the segment replaced by an arbitrary SET and
;;; BIJECTION by INJECTION; the cardinal then comes from composing it with the
;;; enumeration well-ordering-principle produces.
;;; =====================================================================

(define r7x-iim-stmt
  '(FORALL dm_ (IMPLIES (IN dm_ SET)
     (FORALL cod_ (FORALL ph_ (IMPLIES (IN ph_ (INJECTION dm_ cod_))
       (IN (VNB-LAMBDA z_ dm_ (ph_ z_)) (BIJECTION dm_ (IMAGE ph_ dm_)))))))))

(sp (make-wff r7x-iim-stmt))
(dk-peel!)
(define r7x-j-goal (dk-goal))
(define r7x-j-bij (caddr r7x-j-goal))               ; (BIJECTION dm (IMAGE ph dm))
(define r7x-j-dm  (cadr r7x-j-bij))
(define r7x-j-ph  (cadr (caddr r7x-j-bij)))
(define r7x-j-cod (caddr (caddr (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                                          (r7x-head? (caddr f) 'INJECTION)))
                                         "ph in INJECTION"))))
(define r7x-j-inj
  (let ((st (list 'FORALL 'a_ (list 'IMPLIES (list 'IN 'a_ r7x-j-dm)
              (list 'FORALL 'b_ (list 'IMPLIES (list 'IN 'b_ r7x-j-dm)
                (list 'IMPLIES (list '= (list r7x-j-ph 'a_) (list r7x-j-ph 'b_))
                      '(= a_ b_))))))))
    (have! st (lambda ()
                (r7x-mac-h! 'injection-membership-iff
                            (list 'IN r7x-j-ph (list 'INJECTION r7x-j-dm r7x-j-cod)))
                (dk-split! (dk-pick (dk-head? 'AND) "the unfolded injection"))
                (ass)))
    st))
(have! (list 'IN r7x-j-ph (list 'FUN r7x-j-dm r7x-j-cod))
       (lambda ()
         (r7x-mac-h! 'injection-membership-iff
                     (list 'IN r7x-j-ph (list 'INJECTION r7x-j-dm r7x-j-cod)))
         (dk-split! (dk-pick (dk-head? 'AND) "the unfolded injection"))
         (ass)))

(mac 'bijection-membership-iff)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((r7x-head? g 'IN)
        (let* ((ls   (dk-opened (lambda () (lam-t))))
               (st?  (lambda (q) (and (r7x-head? q 'IN) (eq? (caddr q) 'SET))))
               (setl (r7x-leaf ls st? "sethood of the domain"))
               (ptw  (r7x-leaf ls (lambda (q) (not (st? q))) "pointwise typing")))
          (dk-focus! setl)
          (ass)
          (dk-focus! ptw)
          (dk-peel!)
          (let ((zv (cadr (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                                    (equal? (caddr f) r7x-j-dm)))
                                   "the peeled point"))))
            (dk-fact! 'fun-apply-type-c r7x-j-ph r7x-j-dm r7x-j-cod zv)
            (dk-image-goal!)
            (ew zv)
            (dk-conj-close! (lambda () (if (r7x-head? (dk-goal) 'IN) (ass) (rfl)))))))
       ((r7x-head? (caddr (caddr g)) 'FORALL)
        (dk-peel!)
        (let* ((gl (dk-goal)) (av (cadr gl)) (bv (caddr gl)))
          (r7x-beta-h!)
          (r7x-apply! r7x-j-inj av bv)
          (ass)))
       (#t
        (let* ((mem (car (dk-peel!)))
               (wv  (cadr mem)))
          (dk-image-hyp! mem)
          (let ((z (dk-skolem! (dk-pick (lambda (f) (and (r7x-head? f 'FORSOME)
                                                         (dk-contains? f wv)))
                                        "the image witness"))))
            (ew z)
            (dk-conj-close!
             (lambda () (if (r7x-head? (dk-goal) 'IN) (ass) (begin (lam-b) (ass))))))))))))

(r7x-check! 'injection-image-is-bijection)
(qed 'injection-image-is-bijection)
(topic! 'injection-image-is-bijection 'combinatorial)

(define r7x-cim-stmt
  '(FORALL dm_ (IMPLIES (IN dm_ SET)
     (IMPLIES (IN (CARD dm_) NN)
       (FORALL cod_ (FORALL ph_ (IMPLIES (IN ph_ (INJECTION dm_ cod_))
         (= (CARD (IMAGE ph_ dm_)) (CARD dm_)))))))))

(sp (make-wff r7x-cim-stmt))
(dk-peel!)
(let* ((gl  (dk-goal))                               ; (= (CARD (IMAGE ph dm)) (CARD dm))
       (im  (cadr (cadr gl)))
       (phv (cadr im))
       (dmv (caddr im))
       (kv  (list 'CARD dmv))
       (seg (list 'ORD-SEGMENT kv))
       (codv (caddr (caddr (dk-pick (lambda (f) (and (r7x-head? f 'IN) (symbol? (cadr f))
                                                     (r7x-head? (caddr f) 'INJECTION)))
                                    "ph in INJECTION"))))
       (enm (dk-skolem! (dk-fact! 'well-ordering-principle dmv)))
       (lam (cadr (dk-fact! 'injection-image-is-bijection dmv codv phv))))
  (dk-fact! 'image-set phv dmv)
  (have! (list 'AND (list 'IN enm (list 'BIJECTION seg dmv))
                    (list 'IN lam (list 'BIJECTION dmv im))))
  (let ((comp (cadr (dk-fact! 'bijection-compose seg dmv im enm lam))))
    (dk-fact! 'inverse-bij-is-bijection seg im comp)
    (have! (list 'AND (list 'IN (list 'INVERSE-BIJ comp seg im) (list 'BIJECTION im seg))
                      (list 'IN comp (list 'BIJECTION seg im))))
    (dk-fact! 'card-bij kv im (list 'INVERSE-BIJ comp seg im) comp)
    (ass)))

(r7x-check! 'card-image-injection-curried)
(qed 'card-image-injection-curried)
(topic! 'card-image-injection-curried 'combinatorial)

;;; =====================================================================
;;; CLOSING REPORT (5c-X)
;;;
;;; 1.  THE EXTEND-BY NOTE.  Struck, see the header.  `enum-append-is-bijection'
;;;     (finsum-insert.scm:178, proven 2026-09-17) IS the one-point extension
;;;     that card-inequalities.scm:22 and card-basics-worklist.md:76-78 call
;;;     unbuilt.  The blocker was real when it was written and was removed by a
;;;     file with an unrelated name six weeks later; nothing connected the two.
;;;     card-inequalities.scm's further claim -- "when the CARD migration
;;;     reaches card-union-disjoint-curried, both proofs below transcribe unchanged"
;;;     -- is now testable: card-union-disjoint-curried above has the SAME statement
;;;     shape as the axiom, so card-subset-mono and card-union-bound transcribe
;;;     with CARD for CARD and one further leaf, card-subset-nn, which is
;;;     still asserted for either cardinal.
;;;
;;; 2.  WHAT THE RENAME CARD := CARD-STAR STILL OWED (all of it landed).  5c-U's report lists four:
;;;     card-insert, card-union-disjoint, finite-set-induction, card-image-injection.
;;;     All four are PROVEN above for CARD, three of them with the finiteness
;;;     guard their CARD versions already carry and card-insert with the guard the
;;;     user decided to add on 2026-09-18 (5c-W).  Together with 5c-U's
;;;     card-in-ord / card-finite-bij / well-ordering-principle and card-finite's
;;;     card-empty / card-segment, EVERY axiom on the primitive CARD
;;;     shelf now has a proven CARD counterpart:
;;;
;;;       card-in-ord           card-zermelo, conjunct 1   (rake-ord-pigeonhole)
;;;       card-empty            card-empty                 (card-finite)
;;;       card-segment          card-segment               (card-defined)
;;;       card-finite-bij       well-ordering-principle, UNGUARDED  (rake-ord-pigeonhole)
;;;       card-insert           card-insert-curried                HERE
;;;       card-union-disjoint   card-union-disjoint-curried        HERE
;;;       finite-set-induction  finite-set-induction  HERE
;;;       card-image-injection  card-image-injection-curried       HERE
;;;       well-ordering-principle  well-ordering-principle      (rake-ord-pigeonhole)
;;;
;;;     The statements are character for character the axioms' with CARD for
;;;     CARD, EXCEPT card-insert, which needs `(IN (CARD A) NN)': unguarded it
;;;     is FALSE of a defined cardinal (5c-U; omega u {x} bijects with omega).  The
;;;     other seven needed no change, which is itself the finding -- the axioms were
;;;     stated for a finite cardinal throughout and only card-insert forgot to say so.
;;;
;;; 3.  WHAT IS *NOT* DISCHARGED, and it is not a cardinal fact.
;;;     card-subset-nn ("a subset of a finite set is finite"), card-power-nn,
;;;     card-singleton and interval-card remain asserted supports about CARD.
;;;     card-singleton and interval-card are now ONE card-bij citation each
;;;     (the bijections are explicit lambdas: x |-> 0 and j |-> PRED(j)).
;;;     card-subset-nn for CARD is finite-set-induction above with
;;;     the class C = {S : every subset of S is finite}, whose step needs the
;;;     surgery (S u {x}) \ {y} -- the set-difference the tree still cannot form
;;;     (CLAUDE.md, "Two things the tree does NOT have"); that is the same wall
;;;     rake-analysis2 and 5c-M hit, and it is a SET-DIFFERENCE gap, not a
;;;     cardinality one.
;;;
;;; 4.  THE SHAPE OF THE RENAME, for the integrator.  Nothing here retires
;;;     anything: CARD and CARD are two constants, and a proof about one says
;;;     nothing about the other (5c-U's point -- the bridge `forall A in SET.
;;;     CARD A = CARD A' is not derivable and asserting it would assert what
;;;     it is meant to discharge).  The rename is: give CARD's def-functoid
;;;     the name CARD, delete the nine axioms above, and re-point every citation
;;;     at the theorem of the same-but-for-the-prefix name.  The ONE call-site
;;;     cost is card-insert's new guard -- 16 sites in ~10 files, which 5c-W is
;;;     repairing today for the AXIOMATISED CARD, so that work is not duplicated.
;;;
;;; 5.  MACHINERY GAPS MET HERE.
;;;     * `image-subset-codomain' (structure-library/injection.scm:152) is an
;;;       UNWARRANTED axiom (`trust: none' to any citer) and is stated only for the
;;;       FUN domain itself, so a sub-domain image needs a separate lemma;
;;;       seg-image-subset above is that lemma for a segment, and the general form
;;;       ("IMAGE(f, E) subset cod for E subset dm") is three citations and would
;;;       retire the axiom.
;;;     * `union-empty-right' and `union-assoc' exist (fin-subsets.scm) but
;;;       union-assoc is stated left-to-right only, so a driver that needs the
;;;       other orientation pays an eq-sym; and `union-empty-left' / -right are in
;;;       two different files.
;;;     * A typing landed inside a `have!' LANE does not reach the main branch, so
;;;       a later `fact' at that term lands the IMPLICATION and the following
;;;       `subst' blames itself ("equality not in context").  Cost one probe.
;;;     * `prop' declined a three-atom disjunction elimination in a 25-formula
;;;       context; `dk-only!' on the three formulas fixed it, as CLAUDE.md says.
;;; =====================================================================
