;;; co-eq-lt-trans.scm -- co-eq-lt-trans and co-lt-eq-trans, PROVEN.
;;;
;;; structure-library/order-lemmas.scm:198-209 asserts, as `well-known' supports,
;;; the two mixed equality/strict-order compositions the `calc' order composer
;;; folds through (calc.scm:56,58):
;;;
;;;     co-eq-lt-trans   forall a, b, c.  a = b  =>  b < c  =>  a < c
;;;     co-lt-eq-trans   forall a, b, c.  a < b  =>  b = c  =>  a < c
;;;
;;; Neither is an order fact.  Each is one Leibniz rewrite of the goal by the
;;; equality in context -- `subst', the kernel's eq-subst rule on the partial
;;; `=' -- after which the goal IS the other hypothesis.  No order axiom, no
;;; guard, no typing: unlike their `<='/`<' siblings (co-le-trans,
;;; co-le-lt-trans), which need the order axioms and hence guards, an equality
;;; link is provable exactly as stated, unguarded.  Same species as eq-trans in
;;; equality-basics.scm, which this file sits beside.
;;;
;;; `subst' (pi-eq-subst!, primitive-inferences.scm) finds the equation in the
;;; context in EITHER orientation and rewrites left-to-right in the goal, so
;;; co-lt-eq-trans rewrites c -> b by naming (= c b) against the hypothesis
;;; (= b c); no symmetry citation is needed.
;;;
;;; The statements are the supports' statements UNCHANGED, so each `qed' below
;;; re-installs the same statement over the asserted one.
;;;
;;; LOAD WINDOW.  The proofs cite NOTHING: only di / subst / ass and the
;;; driver-kit goal accessor.  0-based over *vnb-files* (load.scm):
;;;     `<'                       order-predicates              39
;;;     the supports themselves   order-lemmas                  40
;;;     interactive / driver-kit                               139 / 143
;;;     equality-basics (its home, by the brief)               151
;;;     calc (the composer that names them)                    178
;;; so the window is [152, 178): right after equality-basics, before calc.
;;;
;;; Helper prefix: colt-.

;; Peel the leading FORALL/IMPLIES prefix, guarded on progress (zb-peel! shape).
(define (colt-peel!)
  (let loop ((fuel 12))
    (let ((before (dk-goal)))
      (if (and (> fuel 0) (memq (car before) '(FORALL IMPLIES)))
          (begin (di)
                 (if (equal? (dk-goal) before)
                     (error "colt-peel!: di made no progress on" before)
                     (loop (- fuel 1))))))))

;;; ---- co-eq-lt-trans: rewrite a -> b in the goal, then it is b < c --------
(sp (make-wff '(FORALL a (FORALL b (FORALL c
   (IMPLIES (= a b) (IMPLIES (< b c) (< a c))))))))
(colt-peel!)
(subst '(= a b))
(ass)
(qed 'co-eq-lt-trans)
(topic! 'co-eq-lt-trans 'inequalities)

;;; ---- co-lt-eq-trans: rewrite c -> b in the goal, then it is a < b --------
(sp (make-wff '(FORALL a (FORALL b (FORALL c
   (IMPLIES (< a b) (IMPLIES (= b c) (< a c))))))))
(colt-peel!)
(subst '(= c b))
(ass)
(qed 'co-lt-eq-trans)
(topic! 'co-lt-eq-trans 'inequalities)
