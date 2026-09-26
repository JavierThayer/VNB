;;; rake-esum-finite.scm -- ESUM: the finiteness dichotomy.
;;;
;;; esum-bounded-implies-finite and esum-finite-iff-bounded, proven 2026-09-18 (rake batch
;;; 5c) at the end of rake-extended-order.scm and moved here VERBATIM on 2026-09-19.
;;; WHY: ESUM is DEFINED since that day (theorem-library/extended-sum.scm) and esum-in,
;;; esum-upper, esum-least are theorems of rake-esum-defined.scm, whose load window opens
;;; after rake-extended-order (it needs the order laws on RR-POS-STAR) and after
;;; rake-finsum-cm-ptwise.  This block cites the three, so it loads after them.
;;; It uses none of rake-extended-order's r6h- helpers.
;;; LOAD WINDOW: [rake-esum-defined, end).  The original is
;;; archive/rake-extended-order.scm.pre-esum-split-2026-09-19.

;;; =======================================================================
;;; ESUM: the finiteness dichotomy.
;;;
;;; `esum-finite-iff-bounded' (theorem-library/extended-sum.scm:79) is the
;;; support this file was asked to close.  Its (=>) half was proved on
;;; 2026-09-17 as `esum-finite-implies-bounded' (rake-series.scm) and is
;;; re-proved INLINE below rather than cited, so that this file's window stays
;;; at [247, end) instead of [547, end): it is three steps.
;;;
;;; The (<=) half is the one that needed `pos-inf-above-reals'.  Its route --
;;; esum-least at b := M, then ESUM(f) <= M with M real forces ESUM(f) real --
;;; wants M in RR-POS-STAR, i.e. 0 <= M, which the hypothesis does NOT say.
;;; The warrant's suggestion, b := max(M, 0), does not work: transporting the
;;; bound from M to max(M,0) needs transitivity at the partial sums, and a
;;; partial sum cannot be TYPED here -- `finsum-comm-monoid-type' wants
;;; f in FUN(S, CARR m) for the index set S, and the tree has no restriction of
;;; a function to a subset (CLAUDE.md, "Two things the tree does NOT have").
;;; The empty index set settles it instead: EMPTY-SET is a finite subset of
;;; DOM f, the bound applies to it, and FINSUM over it is the monoid identity
;;; 0 -- so 0 <= M holds of ANY bound M, and no case split on the sign of M
;;; is needed.  That is what `finsum-empty' (finsum-insert.scm, position 246)
;;; buys, and it is the only citation in this file above position 148.

(sp (make-wff
     '(FORALL f (IMPLIES (IN f (FUN (DOM f) RR-POS-STAR))
        (IMPLIES
          (FORSOME M (AND (IN M RR)
            (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
              (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) M)))))
          (IN (ESUM f) RR))))))
(dk-peel!)
(let* ((ex  (dk-pick (dk-head? 'FORSOME) "the bounded-partial-sums hypothesis"))
       (mv  (dk-skolem! ex))
       (bnd (dk-pick (dk-head? 'FORALL) "the partial-sum bound"))
       (fs  '(FINSUM RR-POS-STAR-ADD-MONOID f EMPTY-SET)))
  ;; (1) the empty set is a finite subset of DOM f, so the bound applies to it
  (fact 'empty-set-is-set)
  (have! '(IN (CARD EMPTY-SET) NN)
         (lambda ()
           (fact 'card-empty)
           (subst '(= (CARD EMPTY-SET) 0))
           (fact 'nn-zero-in)
           (ass)))
  (have! '(SUBSET EMPTY-SET (DOM f))
         (lambda ()
           (mac 'subset-def)
           (let ((m (dk-landed-1 (lambda () (di)))))
             (fact 'empty-set-has-no-members (cadr m))
             (prop))))
  (have! '(AND (IN EMPTY-SET SET) (AND (IN (CARD EMPTY-SET) NN) (SUBSET EMPTY-SET (DOM f)))))
  (dk-apply! bnd 'EMPTY-SET)
  ;; (2) that partial sum is the monoid identity, which is 0 -- so 0 <= M
  (fact 'rr-pos-star-add-monoid-def)
  (have! (list '= fs 0)
         (lambda ()
           (fact 'finsum-empty 'RR-POS-STAR-ADD-MONOID 'f)
           (subst (list '== fs '(IDEN RR-POS-STAR-ADD-MONOID)))
           (slot 'IDEN)
           (subst '(= RR-POS-STAR-ADD-MONOID (LIST RR-POS-STAR eplus 0)))
           (nth-r)
           (rfl)))
  (fact 'equality-symmetry fs 0)
  (have! (list '<= 0 mv)
         (lambda () (subst (list '= 0 fs)) (ass)))
  ;; (3) M is then a bound IN RR-POS-STAR, and esum-least applies
  (have! (list 'IN mv 'RR-POS-STAR)
         (lambda ()
           (let ((inst (dk-fact! 'rr-pos-star-membership mv)))
             (dk-only! inst (list 'IN mv 'RR) (list '<= 0 mv))
             (prop))))
  (have! (list 'AND (list 'IN mv 'RR-POS-STAR) bnd))
  (fact 'esum-least 'f mv)
  (fact 'esum-in 'f)
  (have! (list 'AND '(IN (ESUM f) RR-POS-STAR) (list 'IN mv 'RR)))
  (fact 'rr-pos-star-le-real-in-rr '(ESUM f) mv)
  (ass))
(qed 'esum-bounded-implies-finite)
(topic! 'esum-bounded-implies-finite 'analysis)

;;; -----------------------------------------------------------------------
;;; esum-finite-iff-bounded -- the support, statement copied literally from
;;; theorem-library/extended-sum.scm:79.

(sp (make-wff
     '(FORALL f (IMPLIES (IN f (FUN (DOM f) RR-POS-STAR))
        (IFF (IN (ESUM f) RR)
             (FORSOME M (AND (IN M RR)
               (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
                 (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) M))))))))))
(dk-peel!)
(let ((fwd '(IMPLIES (IN (ESUM f) RR)
              (FORSOME M (AND (IN M RR)
                (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
                  (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) M)))))))
      (bwd '(IMPLIES
              (FORSOME M (AND (IN M RR)
                (FORALL S (IMPLIES (AND (IN S SET) (AND (IN (CARD S) NN) (SUBSET S (DOM f))))
                  (<= (FINSUM RR-POS-STAR-ADD-MONOID f S) M)))))
              (IN (ESUM f) RR))))
  (have! fwd (lambda ()
               (di)
               (fact 'esum-upper 'f)
               (ew '(ESUM f))
               (dk-conj-close! (lambda () (ass)))))
  (have! bwd (lambda ()
               (di)
               (fact 'esum-bounded-implies-finite 'f)
               (ass)))
  (dk-only! fwd bwd)
  (prop))
(qed 'esum-finite-iff-bounded)
(topic! 'esum-finite-iff-bounded 'analysis)
