;;; nn-pred.scm -- the predecessor on NN, DEFINED by definite description.
;;;
;;;     pred(n)  ==  IOTA m. m in NN and succ(m) = n
;;;
;;; WHY IT EXISTS.  The finite-surgery kit (the collapse map that finite
;;; pigeonhole needs) has to send an index past the removed point down by one,
;;; and the tree had no predecessor on NN at all.
;;;
;;; WHY IOTA AND NOT THE MONUS.  `NN-MINUS' (finsum-additive.scm) is a truncated
;;; subtraction defined through ZZ -- (IF (<= l k) (- k l) 0) -- so NN-MINUS(n,1)
;;; is a total predecessor with NN-MINUS(0,1) = 0.  It is serviceable and it is
;;; what the matrix-border code uses, but everything said about it is asserted:
;;; `nn-minus-in-nn' is warranted hand-wave and `nn-minus-succ-1' well-known.
;;; The description costs nothing by comparison -- the two obligations `iota-def'
;;; posts are already theorems, `nn-nonzero-is-succ' (existence) and
;;; `nn-succ-inj' (uniqueness), both proven modulo 0 in nn-parity-proof -- so
;;; pred's laws below are proven rather than assumed.
;;;
;;; pred(0) IS UNDEFINED, deliberately.  No natural has successor 0, so the
;;; description is empty there and, `=' being partial in VNB, (= (pred 0)
;;; (pred 0)) is FALSE: every use of pred owes n /= 0.  That is the honest
;;; reading, and it is free where the kit needs it -- the collapse reaches
;;; pred(j) only for j strictly above the removed point, hence for j /= 0.
;;;
;;; It lives in theorem-library rather than structure-library because its laws
;;; are PROVEN, and a proof needs the tactic layer.  nn-pairing.scm's NNFST /
;;; NNSND are the same shape and the precedent.

(def-functoid 'PRED '(n_)
  '(IOTA m_ (AND (IN m_ NN) (= (succ m_) n_))))
(notation! 'PRED 'kind 'functoid 'arity 1 'english "the predecessor of $1")

;;; The IOTA term the description unfolds to, written once: `iota-d' takes the
;;; TERM, and reconstructing it at each call site is how eigenvariable guesswork
;;; gets in (CLAUDE.md, "never name an assumption by shape").
(define np-io '(IOTA m_ (AND (IN m_ NN) (= (succ m_) n_))))

(define (np-first h)
  (let ((fs (filter (dk-head? h) (dk-asms))))
    (if (null? fs) (error "np-first: no context formula with head" h) (car fs))))

;;; --------------------------------------------------------------------
;;; pred-property: the defining property, both halves at once.
;;;
;;;     n in NN, n /= 0  =>  pred(n) in NN  and  succ(pred(n)) = n
;;;
;;; `iota-d' posts the existence-and-uniqueness obligation and hands the
;;; defining property back as an assumption; after (mac 'pred) that property IS
;;; the goal, so the main branch closes by `ass'.  Existence is
;;; nn-nonzero-is-succ, uniqueness nn-succ-inj -- the two theorems this
;;; construction was designed to consume.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
                 (IMPLIES (NOT (= n_ 0))
                   (AND (IN (PRED n_) NN) (= (succ (PRED n_)) n_)))))))
(di)                                     ; n_ ; IN n_ NN
(di)                                     ; assume n_ /= 0 (di stops at the AND)
(mac 'pred)
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'FORSOME)
       ;; ---- the existence-and-uniqueness obligation --------------------
       (let* ((ex  (dk-fact! 'nn-nonzero-is-succ 'n_))
              (cs  (dk-split! ex))
              (eq0 (car (filter (dk-head? '=) cs)))
              (q0  (cadr (caddr eq0))))   ; the eigenvariable of n_ = succ(q)
         (ew q0)
         (for-each
          (lambda (m)
            (dk-focus! m)
            (if (eq? (car (dk-goal)) 'FORALL)
                (begin                    ; uniqueness: succ is injective
                  (di) (di)               ; the bound variable, then its guard
                  (dk-split! (np-first 'AND))
                  (let ((y (caddr (dk-goal))))
                    (fact 'eq-trans (list 'succ y) 'n_ (list 'succ q0))
                    (fact 'nn-succ-inj y q0)
                    (fact 'eq-sym y q0)
                    (ass)))
                (for-each                 ; the witness works
                 (lambda (k)
                   (dk-focus! k)
                   (if (eq? (car (dk-goal)) 'IN)
                       (ass)
                       (begin (fact 'eq-sym 'n_ (list 'succ q0)) (ass))))
                 (dk-opened (lambda () (di))))))
          (dk-opened (lambda () (di)))))
       ;; ---- the defining property IS the goal ---------------------------
       (ass)))
 (dk-opened (lambda () (iota-d np-io))))
(qed 'pred-property)
(category! 'pred-property 'arithmetic)

;;; --------------------------------------------------------------------
;;; The two halves separately, which is how consumers want them.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
                 (IMPLIES (NOT (= n_ 0)) (IN (PRED n_) NN))))))
(di) (di)
(dk-split! (dk-fact! 'pred-property 'n_))
(ass)
(qed 'pred-in-nn)
(category! 'pred-in-nn 'arithmetic)

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
                 (IMPLIES (NOT (= n_ 0)) (= (succ (PRED n_)) n_))))))
(di) (di)
(dk-split! (dk-fact! 'pred-property 'n_))
(ass)
(qed 'pred-succ)
(category! 'pred-succ 'arithmetic)

;;; --------------------------------------------------------------------
;;; pred(succ m) = m -- the computation rule, and the one every use of the
;;; collapse map goes through.  succ(m) is nonzero (nn-succ-nonzero), so
;;; pred-property applies to it and gives succ(pred(succ m)) = succ m; succ is
;;; injective, so pred(succ m) = m.
(sp (make-wff '(FORALL m_ (IMPLIES (IN m_ NN) (= (PRED (succ m_)) m_)))))
(di)
(fact 'nn-succ-closed 'm_)
(fact 'nn-succ-nonzero 'm_)
(dk-split! (dk-fact! 'pred-property '(succ m_)))
(fact 'nn-succ-inj '(PRED (succ m_)) 'm_)
(ass)
(qed 'pred-of-succ)
(category! 'pred-of-succ 'arithmetic)
