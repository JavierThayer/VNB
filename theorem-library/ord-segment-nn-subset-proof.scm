;;; ord-segment-nn-subset-proof.scm -- a member of ORD-SEGMENT(m), m in NN,
;;; is a natural number.  PROVEN, retiring the `informal' support of the same
;;; name (theorem-library/ord-segment-nn-subset.scm:9).
;;;
;;;     ord-segment-zero-no-members   forall k.  NOT (k in ORD-SEGMENT(0))
;;;     ord-segment-nn-subset         forall m.  m in NN  =>
;;;                                     forall k.  k in ORD-SEGMENT(m)  =>  k in NN
;;;
;;; PLAN.  `ni' on m.  Base: ORD-SEGMENT(0) is empty, so the hypothesis is
;;; refuted.  Step: ord-segment-nn-succ reads k in ORD-SEGMENT(succ m) as
;;; k in ORD-SEGMENT(m) or k = m; the first case is the IH at k, the second
;;; is m in NN, in context, after `subst'.  This is the archived script
;;; (archive/proven-theorems-archive.scm:1837) with the dk- kit in place of
;;; eigen-name / refocus!.
;;;
;;; THE WINDOW TRAP.  The base case needs ord-segment-zero-no-members, which
;;; is proven in theorem-library/pigeonhole-segments.scm (load.scm:914) -- and
;;; pigeonhole-segments.scm:160 is the EARLIEST real citer of
;;; ord-segment-nn-subset, so this file must load BEFORE the file that proves
;;; the base-case lemma.  (founder-warrants, load.scm:514, only re-warrants.)
;;; So the lemma is proven here, INLINE, under its own name, from ordinal
;;; primitives only (structure-library/ordinals.scm): the same 12 lines as
;;; pigeonhole-segments.scm:38-53, which then becomes a same-statement
;;; re-install and can be retired by the integrator.
;;;
;;; LOAD WINDOW [lo, hi):
;;;   lo = theorem-library/ord-segment-nn-succ-proof (load.scm:597), the latest
;;;        citation; everything else cited is `primitive' (ordinals.scm,
;;;        number-systems.scm: nn-zero-in, nn-subset-ord, ord-segment-membership,
;;;        ord-lt-iff, ord-le-closure, ord-zero-least, ord-le-antisymm).
;;;   hi = theorem-library/pigeonhole-segments (load.scm:914), the earliest
;;;        citer (:160) -- and the file whose copy of the base-case lemma this
;;;        one pre-empts.
;;;
;;; Helper prefix: osns-.

;;; ---------------------------------------------------------------------
;;; osns-focus! -- focus the unique open leaf whose goal contains SUBTERM.
;;; Sibling leaves after `ni' share the head FORALL/IMPLIES; the base case is
;;; the one mentioning ORD-SEGMENT(0), the step the one mentioning succ(m).
(define (osns-has? tree sub)
  (or (equal? tree sub)
      (and (pair? tree) (any-pred (lambda (t) (osns-has? t sub)) tree))))
(define (osns-focus! sub)
  (let ((hits (filter (lambda (l) (osns-has? (dk-goal-of l) sub)) (proof-leaves))))
    (cond ((null? hits)       (error "osns-focus!: no leaf mentions" sub))
          ((pair? (cdr hits)) (error "osns-focus!: ambiguous" sub))
          (#t (dk-focus! (car hits))))))

;;; ---------------------------------------------------------------------
;;; ORD-SEGMENT(0) is empty.  k in S(0) gives ORD-LT k 0 (ord-segment-
;;; membership, once 0 is typed in ORD), i.e. ORD-LE k 0 and k /= 0
;;; (ord-lt-iff); ord-zero-least gives ORD-LE 0 k; antisymmetry closes to
;;; k = 0, against k /= 0.
(sp (make-wff '(FORALL k (NOT (IN k (ORD-SEGMENT 0))))))
(di)                          ; the FORALL
(di)                          ; the NOT: assume k in S(0), prove FALSITY
(fact 'nn-zero-in)
(fact 'nn-subset-ord 0)       ; 0 in ORD, which ord-segment-membership wants
(mac-h 'ord-segment-membership '(IN k (ORD-SEGMENT 0)))
(mac-h 'ord-lt-iff '(ORD-LT k 0))
(dk-split! '(AND (ORD-LE k 0) (NOT (= k 0))))
(fact 'ord-le-closure 'k 0)
(dk-split! '(AND (IN k ORD) (IN 0 ORD)))
(fact 'ord-zero-least 'k)
(have! '(AND (ORD-LE k 0) (ORD-LE 0 k)))
(fact 'ord-le-antisymm 'k 0)
(ai '(NOT (= k 0)))
(qed 'ord-segment-zero-no-members)
(topic! 'ord-segment-zero-no-members 'set-theory)

;;; ---------------------------------------------------------------------
;;; ord-segment-nn-subset, by NN-induction on m.
(sp (make-wff '(FORALL m (IMPLIES (IN m NN)
     (FORALL k (IMPLIES (IN k (ORD-SEGMENT m)) (IN k NN)))))))
(ni)

;; base: k in ORD-SEGMENT(0) is impossible
(osns-focus! '(ORD-SEGMENT 0))
(let ((kv (dk-di-var! (lambda (g) (cadr g)))))   ; goal (IN k NN); read k off it
  (fact 'ord-segment-zero-no-members kv)
  (ai `(NOT (IN ,kv (ORD-SEGMENT 0)))))

;; step: m in NN, IH, and k in ORD-SEGMENT(succ m)
(osns-focus! '(succ m))
(let* ((mv (dk-di-var!))                          ; lands (IN m NN); returns m
       (ih (dk-landed-1 (lambda () (di))))        ; the IH, a FORALL
       (kv (dk-di-var! (lambda (g) (cadr g))))    ; lands (IN k (OS (succ m))); goal (IN k NN)
       (hyp `(IN ,kv (ORD-SEGMENT (succ ,mv)))))
  (if (not (eq? (car ih) 'FORALL)) (error "osns: IH did not land" ih))
  (mac-h 'ord-segment-nn-succ hyp)                ; -> (OR (IN k (OS m)) (= k m))
  (use-cases `(OR (IN ,kv (ORD-SEGMENT ,mv)) (= ,kv ,mv))
    (lambda ()                                    ; k in OS(m): the IH at k
      (dk-apply! ih kv)
      (ass))
    (lambda ()                                    ; k = m: m in NN is in context
      (subst `(= ,kv ,mv))
      (ass))))
(qed 'ord-segment-nn-subset)
(topic! 'ord-segment-nn-subset 'plumbing)
