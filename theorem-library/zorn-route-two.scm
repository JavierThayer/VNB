;;; zorn-route-two.scm -- ZORN'S LEMMA, PROVED.
;;;
;;; ROUTE TWO (the user's, 2026-07-27).  Route one (theorem-library/zorn-proof.scm)
;;; walks a well-ordering of the ground set and keeps whatever dominates
;;; everything kept so far; its rung 3 -- "the kept set is a chain" -- is proven
;;; there, and its rung 4 stalls, because "anything strictly above the bound would
;;; have been kept" needs the enumeration to be SURJECTIVE onto grd, and the
;;; general-ordinal enumeration supports for that do not exist.
;;;
;;; This route never enumerates grd.  Assume the order is inductive and has NO
;;; maximal element, and build a STRICTLY INCREASING tower ZUP : ORD -> grd by
;;; transfinite recursion:
;;;
;;;     ZUP(0)        = some element of grd                     (grd is nonempty)
;;;     ZUP(succ a)   = some element strictly above ZUP(a)      (a is not maximal)
;;;     ZUP(lim)      = an upper bound of { ZUP(b) : b < lim }   (INDUCTIVITY)
;;;
;;; Inductivity is used at the LIMIT stages only, and there it is enough on its
;;; own: an upper bound u of a strictly increasing family is AUTOMATICALLY
;;; strictly above every member, because if u failed to be strictly above ZUP(b)
;;; then ZUP(succ b) would be above ZUP(b), below u, and below ZUP(b) at once.
;;; Strictly increasing gives injective, and ord-no-injection-into-set
;;; (theorem-library/ord-no-injection.scm) turns an injective class function
;;; ORD -> a set into a contradiction, by replacement and Burali-Forti.
;;;
;;; WHAT IT COSTS.  Every lemma below is unconditional (`modulo 0'); the final
;;; bill is `modulo {image-set}' and nothing else.  image-set is replacement
;;; (structure-library/injection.scm:99) and is inherited whole from
;;; ord-no-injection-into-set -- this file asserts nothing of its own.  The
;;; ordinal axioms cost nothing: they are `primitive' (structure-library/
;;; ordinals.scm).
;;;
;;; The four order predicates and their English readings live in
;;; theorem-library/order-zorn.scm, which used to carry zorn-lemma as an asserted
;;; support warranted to Yosida.

(register-constant! 'ZUP 'defined-fn)

;;; x is strictly below y under porel: x <= y and NOT y <= x.  This is exactly
;;; the negation of the IS-MAXIMAL clause, which is why "no maximal element"
;;; hands us a strictly-larger witness with no extra work.
(def-predicate 'IS-STRICTLY-BELOW '(porel x y)
  '(AND (IN (LIST x y) porel) (NOT (IN (LIST y x) porel))))
(notation! 'IS-STRICTLY-BELOW 'kind 'predicate 'arity 3
           'english "$2 is strictly below $3 under $1")

;;; ZUP(grd,porel,alpha).  Both step sets are SEPs over grd, so CHOICE lands in
;;; grd as soon as the SEP is shown inhabited -- which is the ONE obligation each
;;; case of the induction below discharges.
(def-by-ord-recursion 'ZUP '(grd porel)
  '(CHOICE grd)
  '(alpha val)
  '(CHOICE (SEP y_ grd (IS-STRICTLY-BELOW porel val y_)))
  '(lam)
  '(CHOICE (SEP y_ grd
             (FORALL c_ (IMPLIES (<_ORD c_ lam)
                                 (IN (LIST (ZUP grd porel c_) y_) porel))))))

;;; The four standing hypotheses: a partial order, nonempty, every chain bounded,
;;; nothing maximal.
(define (z2-hyp)
  (conjuncts->and
   (list '(IS-PARTIAL-ORDER grd porel)
         '(FORSOME w_ (IN w_ grd))
         '(FORALL ch_ (IMPLIES (IS-CHAIN grd porel ch_)
                               (FORSOME u_ (IS-UPPER-BOUND grd porel ch_ u_))))
         '(FORALL x_ (IMPLIES (IN x_ grd)
                              (FORSOME y_ (AND (IN y_ grd)
                                               (IS-STRICTLY-BELOW porel x_ y_))))))))

;;; The induction predicate.  The "(IN (ZUP b) grd)" inside the second conjunct
;;; is NOT redundant: strictly-below-transitive needs all three elements typed in
;;; grd, and the successor case has to apply it at a stage b < a about which
;;; P(a) would otherwise say nothing.
(define (z2-P a)
  `(FORALL grd (FORALL porel
     (IMPLIES ,(z2-hyp)
        (AND (IN (ZUP grd porel ,a) grd)
             (FORALL b_ (IMPLIES (<_ORD b_ ,a)
                (AND (IN (ZUP grd porel b_) grd)
                     (IS-STRICTLY-BELOW porel
                        (ZUP grd porel b_) (ZUP grd porel ,a))))))))))

;;; --- selector kit ---------------------------------------------------------
;;; Assumptions are picked out by CONTENT, never by position in a split and
;;; never by a reconstructed eigenvariable name.

(define (z2-mentions? sym f)
  (cond ((eq? f sym) #t)
        ((pair? f) (or (z2-mentions? sym (car f)) (z2-mentions? sym (cdr f))))
        (else #f)))

(define (z2-find lst pred)
  (or (any-pred (lambda (f) (and (pred f) f)) lst)
      (error "z2-find: nothing matched" lst)))

(define (z2-head? h) (lambda (f) (and (pair? f) (eq? (car f) h))))

;; count the FORALL binders anywhere in F: the IS-PARTIAL-ORDER conjuncts are
;; distinguished by exactly that (reflexive 1, antisymmetric 2, transitive 3),
;; and nothing else about their shape separates them.
(define (z2-count-forall f)
  (cond ((not (pair? f)) 0)
        ((eq? (car f) 'FORALL) (+ 1 (z2-count-forall (caddr f))))
        (else (apply + (map z2-count-forall (cdr f))))))

(define (z2-po-parts)
  (dk-split! (dk-landed-1
    (lambda () (mac-h 'is-partial-order '(IS-PARTIAL-ORDER grd porel))))))

(define (z2-pick parts n)
  (or (any-pred (lambda (f) (and (= (z2-count-forall f) n) f)) parts)
      (error "z2-pick: no conjunct with binder count" n parts)))

;; the open leaf whose goal has head HD; errors rather than returning #f.
(define (z2-focus! hd)
  (let loop ((ls (proof-leaves)))
    (cond ((null? ls) (error "z2-focus!: no open leaf with goal head" hd))
          ((and (pair? (dk-goal-of (car ls))) (eq? (car (dk-goal-of (car ls))) hd))
           (dk-focus! (car ls)))
          (else (loop (cdr ls))))))

;; peel the FORALL/IMPLIES prefix and STOP -- `di' is greedy (one call takes all
;; leading binders, and another would take a NOT or split an AND), so counting
;; `di's is not a way to land on a chosen goal.  Guard on progress.
(define (z2-peel!)
  (let loop ((fuel 24))
    (let ((before (dk-goal)))
      (if (and (> fuel 0) (memq (car before) '(FORALL IMPLIES)))
          (begin (di)
                 (if (equal? (dk-goal) before)
                     (error "z2-peel!: no progress on" before)
                     (loop (- fuel 1))))))))

;; peel, and return everything the peel landed in the context.
(define (z2-peel-landed!) (dk-landed (lambda () (z2-peel!))))

;; split an IS-STRICTLY-BELOW assumption into its two halves.
(define (z2-sb-parts x y)
  (dk-split! (dk-landed-1
    (lambda () (mac-h 'is-strictly-below `(IS-STRICTLY-BELOW porel ,x ,y))))))

;; split the four-conjunct hypothesis block sitting in context.
(define (z2-split-hyp!) (dk-split! (z2-hyp)))

(define (z2-hyp-po    hs) (z2-find hs (z2-head? 'IS-PARTIAL-ORDER)))
(define (z2-hyp-ne    hs) (z2-find hs (z2-head? 'FORSOME)))
(define (z2-hyp-chain hs) (z2-find hs (lambda (f) (z2-mentions? 'IS-UPPER-BOUND f))))
(define (z2-hyp-nomax hs) (z2-find hs (lambda (f) (z2-mentions? 'IS-STRICTLY-BELOW f))))

;; restore the conjunction after splitting it: the induction hypotheses are
;; guarded on the WHOLE hypothesis block, and `ai' removes what it splits.
(define (z2-hyp-parts!)
  (let ((hs (z2-split-hyp!))) (have! (z2-hyp)) hs))

;; from (NOT (= p q)) in context, land (NOT (= q p)).  `subst' rewrites every
;; occurrence, so the symmetric form has to be cut, not rewritten into place.
(define (z2-neq-sym! p q)
  (have! `(NOT (= ,q ,p))
    (lambda ()
      (di)
      (have! `(= ,p ,q) (lambda () (subst `(= ,q ,p)) (rfl)))
      (ai `(NOT (= ,p ,q))))))

(sp (make-wff '(FORALL porel (FORALL x_ (NOT (IS-STRICTLY-BELOW porel x_ x_))))))
(z2-peel!)
(di)                                    ; NOT: assume it, goal falsity
(z2-sb-parts 'x_ 'x_)
;; `ai' on a NOT whose positive is in context is NOT-ELIM: it CLOSES the goal.
;; A following `ass' would find nothing to do and warn.
(ai '(NOT (IN (LIST x_ x_) porel)))
(qed 'strictly-below-irreflexive)

;;; --- (2) strict is transitive --------------------------------------------
;;; x < y < z gives (x,z) by transitivity of porel; and (z,x) would give (z,y),
;;; against y < z.  Note the transitivity conjunct's antecedent is a CONJUNCTION,
;;; which `inst+' will not split for us -- so the AND is put in context first.
(sp (make-wff (forall-guarded '(grd porel x_ y_ z_)
                '((IS-PARTIAL-ORDER grd porel) (IN x_ grd) (IN y_ grd) (IN z_ grd)
                  (IS-STRICTLY-BELOW porel x_ y_) (IS-STRICTLY-BELOW porel y_ z_))
                '(IS-STRICTLY-BELOW porel x_ z_))))
(z2-peel!)
(define z2-tr (z2-pick (z2-po-parts) 3))
(z2-sb-parts 'x_ 'y_)
(z2-sb-parts 'y_ 'z_)
(mac 'is-strictly-below)
(both!
  (lambda ()                                    ; (x,z) in porel
    (have! '(AND (IN (LIST x_ y_) porel) (IN (LIST y_ z_) porel)))
    (inst*! z2-tr 'x_ 'y_ 'z_)
    (ass))
  (lambda ()                                    ; NOT (z,x) in porel
    (di)
    (have! '(AND (IN (LIST z_ x_) porel) (IN (LIST x_ y_) porel)))
    (inst*! z2-tr 'z_ 'x_ 'y_)
    (ai '(NOT (IN (LIST z_ y_) porel)))))
(qed 'strictly-below-transitive)

;;; --- (3) equal elements are not strictly ordered -------------------------
;;; Stated with the EQUATION as the antecedent, so that one `subst' turns the
;;; goal into irreflexivity at y_.  The other orientation ("strictly below
;;; implies distinct") would need to rewrite ONE of two occurrences, and
;;; `subst' rewrites every occurrence.
(sp (make-wff '(FORALL porel (FORALL x_ (FORALL y_
      (IMPLIES (= x_ y_) (NOT (IS-STRICTLY-BELOW porel x_ y_))))))))
(z2-peel!)
(subst '(= x_ y_))
(fact 'strictly-below-irreflexive 'porel 'y_)
(ass)
(qed 'strictly-below-not-equal)

;;; --- (4) no maximal element gives a strictly larger witness --------------
;;; IS-STRICTLY-BELOW is exactly the negation of the IS-MAXIMAL clause, so this
;;; is two nested proofs by contradiction and no order axiom at all.
;;; `ai' on a NOT assumption is NOT-ELIM: it fires only when the POSITIVE is
;;; already in context.  So each contradiction is a have! of the positive
;;; followed by the ai, never an ai that "reduces the goal to" the positive.
(sp (make-wff (forall-guarded '(grd porel)
                '((NOT (FORSOME mx_ (IS-MAXIMAL grd porel mx_))))
                (forall-guarded '(x_) '((IN x_ grd))
                  '(FORSOME y_ (AND (IN y_ grd)
                                    (IS-STRICTLY-BELOW porel x_ y_)))))))
(z2-peel!)
(pbc)
(have! '(FORSOME mx_ (IS-MAXIMAL grd porel mx_))
  (lambda ()
    (ew 'x_)
    (mac 'is-maximal)
    (both!
      (lambda () (ass))
      (lambda ()
        (z2-peel!)
        ;; goal is now (IN (LIST y x_) porel) for the engine's own eigenvariable;
        ;; read the name off the goal rather than guessing it.
        (let ((y (cadr (cadr (dk-goal)))))
          (pbc)
          (have! `(FORSOME y_ (AND (IN y_ grd) (IS-STRICTLY-BELOW porel x_ y_)))
            (lambda ()
              (ew y)
              (both! (lambda () (ass))
                     (lambda () (mac 'is-strictly-below) (from-context!)))))
          (ai '(NOT (FORSOME y_ (AND (IN y_ grd)
                                     (IS-STRICTLY-BELOW porel x_ y_))))))))))
(ai '(NOT (FORSOME mx_ (IS-MAXIMAL grd porel mx_))))
(qed 'no-maximal-strictly-above)

;;; --- (5) and (6) the two partial-order laws, as citable facts ------------
;;; Stated so that no later proof has to `mac-h' IS-PARTIAL-ORDER -- which
;;; REPLACES the hypothesis every other citation is guarded on.
(sp (make-wff (forall-guarded '(grd porel x_)
                '((IS-PARTIAL-ORDER grd porel) (IN x_ grd))
                '(IN (LIST x_ x_) porel))))
(z2-peel!)
(inst*! (z2-pick (z2-po-parts) 1) 'x_)
(ass)
(qed 'po-reflexive)

(sp (make-wff (forall-guarded '(grd porel x_ y_ z_)
                '((IS-PARTIAL-ORDER grd porel) (IN x_ grd) (IN y_ grd) (IN z_ grd)
                  (IN (LIST x_ y_) porel) (IN (LIST y_ z_) porel))
                '(IN (LIST x_ z_) porel))))
(z2-peel!)
(have! '(AND (IN (LIST x_ y_) porel) (IN (LIST y_ z_) porel)))
(inst*! (z2-pick (z2-po-parts) 3) 'x_ 'y_ 'z_)
(ass)
(qed 'po-transitive)

(sp (make-wff (forall-guarded '(a_ b_)
                '((IN a_ ORD) (IN b_ ORD) (<_ORD b_ (succ_ORD a_)))
                '(OR (<_ORD b_ a_) (= b_ a_)))))
(z2-peel!)
(fact 'ord-succ-in 'a_)
(have! '(IN b_ (ORD-SEGMENT (succ_ORD a_)))
       (lambda () (mac 'ord-segment-membership) (ass)))
(mac-h 'ord-segment-succ '(IN b_ (ORD-SEGMENT (succ_ORD a_))))
(use-cases (list '(IN b_ (ORD-SEGMENT a_)) '(= b_ a_))
  (lambda ()
    (mac-h 'ord-segment-membership '(IN b_ (ORD-SEGMENT a_)))
    (oi-l) (ass))
  (lambda () (oi-r) (ass)))
(qed 'ord-lt-succ-cases)

;;; --- (2) below a limit, the successor is still below ---------------------
;;; b < lam with lam a limit: ord-segment-limit interposes some beta with
;;; b < beta < lam, ord-succ-immediate pushes succ b under beta, and succ b
;;; cannot BE lam because a limit is not a successor.
(sp (make-wff (forall-guarded '(lam b_)
                '((LIMIT-ORD lam) (IN b_ ORD) (<_ORD b_ lam))
                '(<_ORD (succ_ORD b_) lam))))
(z2-peel!)
;; Do the ord-segment-limit citation BEFORE unfolding LIMIT-ORD: mac-h REPLACES
;; the assumption it unfolds, and this citation is guarded on it.
(define z2b-ex (dk-fact! 'ord-segment-limit 'lam 'b_))
(define z2b-parts (dk-split! (dk-landed-1 (lambda () (ai z2b-ex)))))
(define z2b-beta
  (caddr (z2-find z2b-parts
           (lambda (f) (and (pair? f) (eq? (car f) '<_ORD) (eq? (cadr f) 'b_))))))
(define z2b-lim (dk-split! (dk-landed-1
                  (lambda () (mac-h 'limit-ord-iff '(LIMIT-ORD lam))))))
(define z2b-nosucc (z2-find z2b-lim (lambda (f) (and (pair? f) (eq? (car f) 'NOT)
                                                     (z2-mentions? 'succ_ORD f)))))
;; beta is an ordinal, and beta <= lam
(dk-split! (dk-landed-1 (lambda () (mac-h 'ord-lt-iff `(<_ORD ,z2b-beta lam)))))
(dk-split! (dk-fact! 'ord-le-closure z2b-beta 'lam))
;; succ b <= beta <= lam
(have! `(AND (IN b_ ORD) (AND (IN ,z2b-beta ORD) (<_ORD b_ ,z2b-beta))))
(dk-fact! 'ord-succ-immediate 'b_ z2b-beta)
(have! `(AND (<=_ORD (succ_ORD b_) ,z2b-beta) (<=_ORD ,z2b-beta lam)))
(dk-fact! 'ord-le-trans `(succ_ORD b_) z2b-beta 'lam)
;; ... and succ b /= lam, else lam is a successor
(mac 'ord-lt-iff)
(both!
  (lambda () (ass))
  (lambda ()
    (di)                                  ; assume (= (succ_ORD b_) lam)
    (have! (cadr z2b-nosucc)              ; the FORSOME under the NOT, verbatim
           (lambda ()
             (ew 'b_)
             (both! (lambda () (ass))
                    (lambda () (subst '(= (succ_ORD b_) lam)) (rfl)))))
    (ai z2b-nosucc)))
(qed 'ord-succ-lt-limit)

(sp (make-wff `(FORALL a_ (IMPLIES (IN a_ ORD) ,(z2-P 'a_)))))
(define z2-cases (dk-opened (lambda () (tfi3))))

;;; ====================================================================
;;; BASE: ZUP(...,0) = CHOICE(grd), and nothing precedes stage 0.
;;; ====================================================================
(dk-focus! (car z2-cases))
(z2-peel!)
(define z2z-hs (z2-hyp-parts!))
(mac 'zup-zero)
(both!
  (lambda ()
    (let ((w (cadr (dk-landed-1 (lambda () (ai (z2-hyp-ne z2z-hs)))))))
      (choose! 'grd w (lambda () (ass)))
      (ass)))
  (lambda ()
    (z2-peel!)
    (pbc)
    (dk-split! (dk-landed-1 (lambda () (mac-h 'ord-lt-iff '(<_ORD b_ 0)))))
    (dk-split! (dk-fact! 'ord-le-closure 'b_ 0))
    (fact 'ord-zero-least 'b_)
    (have! '(AND (<=_ORD b_ 0) (<=_ORD 0 b_)))
    (dk-fact! 'ord-le-antisymm 'b_ 0)
    (ai '(NOT (= b_ 0)))))

;;; ====================================================================
;;; SUCCESSOR: nothing is maximal, so the SEP of things strictly above ZUP(a)
;;; is inhabited.  Everything below succ a is either below a -- and then the
;;; induction hypothesis plus transitivity of the strict order does it -- or is
;;; a itself, and then it is the choice's own defining property.
;;; ====================================================================
(dk-focus! (cadr z2-cases))
(define z2s-landed (z2-peel-landed!))
(define z2s-pair
  (z2-find z2s-landed
    (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                     (pair? (cadr f)) (eq? (car (cadr f)) 'IN)
                     (eq? (caddr (cadr f)) 'ORD)))))
(define z2s-pp   (dk-split! z2s-pair))
(define z2s-aord (z2-find z2s-pp (z2-head? 'IN)))
(define z2s-a    (cadr z2s-aord))
(define z2s-ih   (z2-find z2s-pp (z2-head? 'FORALL)))
(define z2s-za   `(ZUP grd porel ,z2s-a))
;; instantiate the induction hypothesis BEFORE splitting the hypothesis block:
;; it is guarded on the whole conjunction.
(define z2s-ihres  (dk-split! (inst*! z2s-ih 'grd 'porel)))
(define z2s-ztyp   (z2-find z2s-ihres (z2-head? 'IN)))
(define z2s-ibelow (z2-find z2s-ihres (z2-head? 'FORALL)))
(define z2s-hs     (z2-hyp-parts!))
;; something strictly above ZUP(a)
;; the instantiation must happen OUTSIDE the dk-landed-1: `inst+' lands its
;; whole peeling chain, and dk-landed-1 insists on exactly one new assumption.
(define z2s-ex (inst*! (z2-hyp-nomax z2s-hs) z2s-za))
(define z2s-ab (dk-split! (dk-landed-1 (lambda () (ai z2s-ex)))))
(define z2s-y   (cadr (z2-find z2s-ab (z2-head? 'IN))))
(define z2s-sep `(SEP y_ grd (IS-STRICTLY-BELOW porel ,z2s-za y_)))
(define z2s-c   `(CHOICE ,z2s-sep))
(mac 'zup-succ)
(choose! z2s-sep z2s-y (lambda () (in-sep! (lambda () (ass)) (lambda () (ass)))))
(both!
  (lambda () (ass))
  (lambda ()
    (z2-peel!)
    ;; (IN b_ ORD): unfold the strict order in a SIDE branch, so the main branch
    ;; keeps (<_ORD b_ (succ a)) for ord-lt-succ-cases.  mac-h REPLACES.
    (have! '(IN b_ ORD)
      (lambda ()
        (dk-split! (dk-landed-1
          (lambda () (mac-h 'ord-lt-iff `(<_ORD b_ (succ_ORD ,z2s-a))))))
        (dk-split! (dk-fact! 'ord-le-closure 'b_ `(succ_ORD ,z2s-a)))
        (ass)))
    (fact 'ord-lt-succ-cases z2s-a 'b_)
    (use-cases (list `(<_ORD b_ ,z2s-a) `(= b_ ,z2s-a))
      (lambda ()
        (dk-split! (inst*! z2s-ibelow 'b_))
        (both! (lambda () (ass))
               (lambda ()
                 (fact 'strictly-below-transitive 'grd 'porel
                       '(ZUP grd porel b_) z2s-za z2s-c)
                 (ass))))
      (lambda ()
        (subst `(= b_ ,z2s-a))
        (from-context!)))))

;;; ====================================================================
;;; LIMIT.
;;; ====================================================================
(dk-focus! (caddr z2-cases))
(define z2l-landed (z2-peel-landed!))
(define z2l-pair
  (z2-find z2l-landed
    (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                     (pair? (cadr f)) (eq? (car (cadr f)) 'LIMIT-ORD)))))
(define z2l-pp  (dk-split! z2l-pair))
(define z2l-lim (z2-find z2l-pp (z2-head? 'LIMIT-ORD)))
(define z2l-a   (cadr z2l-lim))
(define z2l-ih  (z2-find z2l-pp (z2-head? 'FORALL)))
(define z2l-hs  (z2-hyp-parts!))
(have! `(IN ,z2l-a ORD)
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'limit-ord-iff z2l-lim))))
    (ass)))

;; the tower's image below lam.  The equation is oriented y_ = ZUP(c_) so that a
;; single `subst' pushes a member INTO tower form; the other orientation would
;; need the symmetric equation, which `subst' cannot produce.
(define z2l-img
  ;; binder d_, NOT c_: ZUP's own limit clause binds c_, so the eigenvariable the
  ;; peel below introduces is called c_, and reusing it here makes one name both
  ;; bound and free in the same formula (make-wff warns, and it is the capture
  ;; hazard the case-fold convention exists to avoid).
  `(SEP y_ grd (FORSOME d_ (AND (<_ORD d_ ,z2l-a) (= y_ (ZUP grd porel d_))))))

;; the induction hypothesis at a stage below lam, as (typing below-clause)
(define (z2l-ih-at b)
  (let ((parts (dk-split! (inst*! z2l-ih b 'grd 'porel))))
    (list (z2-find parts (z2-head? 'IN)) (z2-find parts (z2-head? 'FORALL)))))

;; open (IN v z2l-img); returns the stage it came from, leaving (IN v grd),
;; (<_ORD stage lam) and (= v (ZUP stage)) in context.
;; `sep-me' lands BOTH halves of a SEP membership, so dk-landed, not dk-landed-1.
(define (z2l-sep-open! v)
  (dk-landed (lambda () (sep-me `(IN ,v ,z2l-img)))))

(define (z2l-open! v)
  (let* ((parts (z2l-sep-open! v))
         (ex    (z2-find parts (z2-head? 'FORSOME)))
         (inner (dk-split! (dk-landed-1 (lambda () (ai ex))))))
    (cadr (z2-find inner (z2-head? '<_ORD)))))

;; (IN b ORD) from (<_ORD b lam), unfolding in a side branch so the main branch
;; keeps the strict inequality the induction hypothesis is guarded on.
(define (z2l-typ! b)
  (have! `(IN ,b ORD)
    (lambda ()
      (dk-split! (dk-landed-1 (lambda () (mac-h 'ord-lt-iff `(<_ORD ,b ,z2l-a)))))
      (dk-split! (dk-fact! 'ord-le-closure b z2l-a))
      (ass))))

;;; (A) the image is a chain: two members come from stages b1, b2; the ordinals
;;; are comparable, and the induction hypothesis at the larger one orders them.
(have! `(IS-CHAIN grd porel ,z2l-img)
  (lambda ()
    (mac 'is-chain)
    (both!
      (lambda ()
        (let ((x (subset-by-element!)))
          (z2l-sep-open! x)
          (ass)))
      (lambda ()
        (z2-peel!)
        (let* ((pr (cadr (cadr (dk-goal))))       ; the (LIST x y) of the left disjunct
               (x  (cadr pr))
               (y  (caddr pr))
               (b1 (z2l-open! x))
               (b2 (z2l-open! y)))
          (z2l-typ! b1)
          (z2l-typ! b2)
          (subst `(= ,x (ZUP grd porel ,b1)))
          (subst `(= ,y (ZUP grd porel ,b2)))
          (use-em `(= ,b1 ,b2)
            (lambda ()
              (z2l-ih-at b2)
              (subst `(= ,b1 ,b2))
              (fact 'po-reflexive 'grd 'porel `(ZUP grd porel ,b2))
              (oi-l) (ass))
            (lambda ()
              ;; ord-le-total's antecedent is a CONJUNCTION, and `fact' will not
              ;; split one -- without this cut it lands the implication and the
              ;; disjunction never reaches the context.
              (have! `(AND (IN ,b1 ORD) (IN ,b2 ORD)))
              (fact 'ord-le-total b1 b2)
              (use-cases (list `(<=_ORD ,b1 ,b2) `(<=_ORD ,b2 ,b1))
                (lambda ()
                  (have! `(<_ORD ,b1 ,b2)
                    (lambda () (mac 'ord-lt-iff)
                               (both! (lambda () (ass)) (lambda () (ass)))))
                  (dk-split! (inst*! (cadr (z2l-ih-at b2)) b1))
                  (z2-sb-parts `(ZUP grd porel ,b1) `(ZUP grd porel ,b2))
                  (oi-l) (ass))
                (lambda ()
                  (z2-neq-sym! b1 b2)
                  (have! `(<_ORD ,b2 ,b1)
                    (lambda () (mac 'ord-lt-iff)
                               (both! (lambda () (ass)) (lambda () (ass)))))
                  (dk-split! (inst*! (cadr (z2l-ih-at b1)) b2))
                  (z2-sb-parts `(ZUP grd porel ,b2) `(ZUP grd porel ,b1))
                  (oi-r) (ass))))))))))

;;; (B) so the chain has an upper bound, and that bound sits in the SEP the
;;; limit clause of ZUP chooses from.
(define z2l-ubfs (inst*! (z2-hyp-chain z2l-hs) z2l-img))
;; what `ai' lands here is an ATOM, so it is not dk-split!'s business: dk-split!
;; starts by ai-ing what it is given, and ai has nothing to do to an atom.
(define z2l-ubmem (dk-landed-1 (lambda () (ai z2l-ubfs))))
(define z2l-u (list-ref z2l-ubmem 4))
(define z2l-ubp
  (dk-split! (dk-landed-1
    (lambda () (mac-h 'is-upper-bound `(IS-UPPER-BOUND grd porel ,z2l-img ,z2l-u))))))
(define z2l-dom (z2-find z2l-ubp (z2-head? 'FORALL)))

(define z2l-set
  `(SEP y_ grd (FORALL c_ (IMPLIES (<_ORD c_ ,z2l-a)
                                   (IN (LIST (ZUP grd porel c_) y_) porel)))))
(define z2l-c `(CHOICE ,z2l-set))

(mac 'zup-limit)
(define z2l-ch
  (choose! z2l-set z2l-u
    (lambda ()
      (in-sep!
        (lambda () (ass))
        (lambda ()
          (z2-peel!)
          ;; the stage's value is in the image, so the upper bound dominates it
          (dk-split! (inst*! z2l-ih 'c_ 'grd 'porel))
          (have! `(IN (ZUP grd porel c_) ,z2l-img)
            (lambda ()
              (in-sep! (lambda () (ass))
                       (lambda () (witness! 'c_
                                    (lambda () (both! (lambda () (ass))
                                                      (lambda () (rfl)))))))))
          (inst*! z2l-dom '(ZUP grd porel c_))
          (ass))))))
(define z2l-prop (z2-find z2l-ch (z2-head? 'FORALL)))

;;; (C) the chosen bound is STRICTLY above every earlier stage.
(both!
  (lambda () (ass))
  (lambda ()
    (z2-peel!)
    (dk-split! (inst*! z2l-ih 'b_ 'grd 'porel))
    (both!
      (lambda () (ass))
      (lambda ()
        (mac 'is-strictly-below)
        (both!
          (lambda ()
            (inst*! z2l-prop 'b_)
            (ass))
          (lambda ()
            (di)
            (z2l-typ! 'b_)
            (fact 'ord-succ-lt-limit z2l-a 'b_)
            (fact 'ord-succ-above 'b_)
            (let ((blw (cadr (z2l-ih-at '(succ_ORD b_)))))
              (dk-split! (inst*! blw 'b_))
              (z2-sb-parts '(ZUP grd porel b_) '(ZUP grd porel (succ_ORD b_)))
              (inst*! z2l-prop '(succ_ORD b_))
              (fact 'po-transitive 'grd 'porel
                    '(ZUP grd porel (succ_ORD b_)) z2l-c '(ZUP grd porel b_))
              (ai '(NOT (IN (LIST (ZUP grd porel (succ_ORD b_))
                                  (ZUP grd porel b_)) porel))))))))))

(qed 'zup-tower)

(define (z2i-tower-at b)
  (let ((parts (dk-split! (inst*! (dk-fact! 'zup-tower b) 'grd 'porel))))
    (list (z2-find parts (z2-head? 'IN)) (z2-find parts (z2-head? 'FORALL)))))

;;; --- injectivity ---------------------------------------------------------
(sp (make-wff
      `(FORALL grd (FORALL porel
         (IMPLIES ,(z2-hyp)
           ,(forall-guarded '(a1_ a2_) '((IN a1_ ORD) (IN a2_ ORD))
              '(IMPLIES (= (ZUP grd porel a1_) (ZUP grd porel a2_))
                        (= a1_ a2_))))))))
(z2-peel!)
(pbc)
;; ord-le-total's antecedent is a CONJUNCTION; `fact' will not split one.
(have! '(AND (IN a1_ ORD) (IN a2_ ORD)))
(fact 'ord-le-total 'a1_ 'a2_)
;; lo < hi, so ZUP(lo) is strictly below ZUP(hi) -- and they are equal.
(define (z2i-close! lo hi eqn)
  (have! `(<_ORD ,lo ,hi)
    (lambda () (mac 'ord-lt-iff) (both! (lambda () (ass)) (lambda () (ass)))))
  (dk-split! (inst*! (cadr (z2i-tower-at hi)) lo))
  (fact 'strictly-below-not-equal 'porel `(ZUP grd porel ,lo) `(ZUP grd porel ,hi))
  (ai `(NOT (IS-STRICTLY-BELOW porel (ZUP grd porel ,lo) (ZUP grd porel ,hi)))))
(use-cases (list '(<=_ORD a1_ a2_) '(<=_ORD a2_ a1_))
  (lambda () (z2i-close! 'a1_ 'a2_ '(= (ZUP grd porel a1_) (ZUP grd porel a2_))))
  (lambda ()
    ;; the other direction needs both the inequality and the equation reversed;
    ;; `subst' rewrites every occurrence, so each reversal is a cut.
    (z2-neq-sym! 'a1_ 'a2_)
    (have! '(= (ZUP grd porel a2_) (ZUP grd porel a1_))
      (lambda ()
        (subst '(= (ZUP grd porel a1_) (ZUP grd porel a2_)))
        (z2i-tower-at 'a2_)
        (rfl)))
    (z2i-close! 'a2_ 'a1_ '(= (ZUP grd porel a2_) (ZUP grd porel a1_)))))
(qed 'zup-injective)

;;; --- Zorn's lemma --------------------------------------------------------
(define z2f-phi '(VNB-LAMBDA a_ ORD (ZUP grd porel a_)))

(sp (make-wff (forall-guarded '(grd porel)
    (list '(IS-PARTIAL-ORDER grd porel)
          '(FORSOME w_ (IN w_ grd))
          '(FORALL ch_ (IMPLIES (IS-CHAIN grd porel ch_)
                                (FORSOME u_ (IS-UPPER-BOUND grd porel ch_ u_)))))
    '(FORSOME mx_ (IS-MAXIMAL grd porel mx_)))))
(z2-peel!)
(pbc)
;; "nothing is maximal" is now a hypothesis; that is the fourth standing one.
(fact 'no-maximal-strictly-above 'grd 'porel)
(have! (z2-hyp))
(have! '(IN grd SET)
  (lambda ()
    (dk-split! (dk-landed-1
      (lambda () (mac-h 'is-partial-order '(IS-PARTIAL-ORDER grd porel)))))
    (ass)))
;; the tower, packaged as a class function ORD -> grd
(have! `(FORALL alpha (IMPLIES (IN alpha ORD) (IN (,z2f-phi alpha) grd)))
  (lambda ()
    (z2-peel!)
    (lam-b)
    (car (z2i-tower-at 'alpha))
    (ass)))
(have! (forall-guarded '(a1_) '((IN a1_ ORD))
         (forall-guarded '(a2_) '((IN a2_ ORD))
           `(IMPLIES (= (,z2f-phi a1_) (,z2f-phi a2_)) (= a1_ a2_))))
  (lambda ()
    (z2-peel!)
    (lam-b-h `(= (,z2f-phi a1_) (,z2f-phi a2_)))
    (fact 'zup-injective 'grd 'porel 'a1_ 'a2_)
    (ass)))
(fact 'ord-no-injection-into-set 'grd z2f-phi)
(ass)
(qed 'zorn-lemma)
(gloss! 'zorn-lemma
  "Zorn's lemma: if (grd, porel) is a partially ordered set that is nonempty and in
   which every chain (totally ordered subset) has an upper bound in grd, then grd has
   a maximal element.  Proved here from the transfinite tower ZUP rather than from the
   well-ordering principle: the tower is strictly increasing, hence injective on ORD,
   and no set receives an injection from ORD.")
(category! 'zorn-lemma 'set-quotient)
