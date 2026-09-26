;;; fin-subsets.scm -- FIN-SUBSETS(a), the finite subsets of a, and the
;;; ---------------------------------------------------------------------------
;;; NOTE, 2026-09-20 (batch 9-B).  This file was written while cardinality was
;;; AXIOMATISED under the name CARD and the defined constant was its companion
;;; CARD-STAR.  On 2026-09-20 the user made the swap: CARD is the DEFINED
;;; cardinal (structure-library/cardinality.scm), the eight `primitive' axioms
;;; about it are gone, and every proof below now speaks of CARD.  The prose in
;;; this header that contrasts "the axiomatised CARD" with "the defined
;;; cardinal" is HISTORY; the surgery is docs/card-defined-2026-09-20.md.
;;; ---------------------------------------------------------------------------
;;; set-algebra laws that make it a commutative monoid under union.
;;;
;;;     FIN-SUBSETS(a)  ==  { t in POWER(a) : CARD(t) in NN }
;;;
;;; This is the carrier of the first of the two intended instances of the
;;; "commutative monoid with an NN-valued subadditive norm": union for the
;;; operation, EMPTY-SET for the identity, CARD for the norm.  CARD is
;;; SUBadditive and not additive here precisely because union is idempotent --
;;; A u A = A while CARD A + CARD A = 2.CARD A -- which is the whole reason the
;;; norm axioms are stated with `<=' rather than `='.
;;;
;;; -----------------------------------------------------------------------
;;; THE MEMBERSHIP LAW IS PROVEN, NOT ASSERTED, AND THAT IS THE POINT.
;;;
;;; CLAUDE.md records the standard trap: `def-functoid' installs only a rewrite
;;; MACETE, so `mac-h' CANNOT unfold a functoid in an ASSUMPTION -- it warns
;;; "unknown theorem/macete" and the driver sails on with the hypothesis
;;; untouched.  The library's answer has been to state the membership `iff'
;;; beside the definition and wrap it `definitional' (`span-membership',
;;; `principal-ideal-membership', and the five in definitional-reclass.scm).
;;;
;;; That is not necessary here, and it did not need to be necessary there.  The
;;; `iff' is provable as a GOAL: `mac' unfolds the functoid on the goal side --
;;; which is exactly the side that works -- and the SEP layer is reached by the
;;; KERNEL RULES rather than by axioms (`sep-mem-intro' / `sep-mem-elim' /
;;; `sep-sethood', primitive-inferences.scm:1092-1124, surfaced as `in-sep!' /
;;; `sep-me' / `sep-set').  Once the `iff' is a THEOREM it is citable by `fact'
;;; on either side, which is all the assumption-side unfolding anyone wanted.
;;;
;;; So `fin-subsets-membership' below bills `modulo 0' where the analogous laws
;;; elsewhere in the tree bill a `definitional' assertion.  The technique
;;; transfers to every `SEP'-bodied functoid in the library; whether it is worth
;;; retrofitting the existing five is a separate question, and the honest
;;; caveat is that those five sit in structure-library/ files that load LONG
;;; before the interactive engine exists (load.scm:265 vs 500+), so retrofitting
;;; them means moving each proof to a theorem-library/ file, not editing in
;;; place.  That is why this file is in theorem-library/ and carries its own
;;; `def-functoid' -- the same shape theorem-library/card-defined.scm:46 uses
;;; for CARD.
;;;
;;; -----------------------------------------------------------------------
;;; THE BILLS.  Everything here is `modulo 0' except the three that reach
;;; through card-union-nn to card-subset-nn:
;;;
;;;   fin-subsets-membership     modulo 0
;;;   fin-subsets-is-set         modulo 0
;;;   union-empty-right          modulo 0
;;;   union-assoc                modulo 0
;;;   fin-subsets-has-empty      modulo 0
;;;   fin-subsets-union-closed   modulo {card-subset-nn}  [trust: well-known]
;;;
;;; `union-empty-right' is proven rather than cited: the tree already has
;;; `union-empty-left' (theorem-library/union-empty-left.scm:9) but only as a
;;; `support' warranted `informal', so citing it would have put an `informal'
;;; leaf in every bill below for a fact that is four lines of extensionality.
;;; The LEFT identity is then union-comm composed with it, so the existing
;;; support is not needed here at all.
;;;
;;; Needs: theory (POWER/SEP/UNION base axioms), structure-library/cardinality
;;; (card-empty), theorem-library/card-inequalities (card-union-nn),
;;; theorem-library/makeset-card-bound (union-comm), plus interactive /
;;; proof-debt / driver-kit.

;;; --- file-local helpers (fs- prefix) ------------------------------------

;; Peel the leading FORALL/IMPLIES prefix and stop at the first other head.
;; The statements below quantify UNGUARDED and then imply, which one `di' does
;; NOT take whole (CLAUDE.md); loop on the head rather than counting calls.
(define (fs-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(forall implies)))
          (begin (di) (loop))))))

;; Drop every assumption but the ones named -- `prop' has a 12-atom cap and
;; `fact' lands its whole instantiation chain.
(define (fs-only! . keepers)
  (for-each (lambda (f) (if (not (member f keepers)) (wk f))) (dk-asms)))

;; The unfolded body of FIN-SUBSETS(A), as the SEP the functoid rewrites to.
;; Written once because three drivers below name it to `sep-me'.
(define (fs-sep a) (list 'SEP 't_ (list 'POWER a) '(IN (CARD t_) NN)))

;; Split a conjunctive goal to leaves and close each from the context.
(define (fs-conj-close!)
  (if (and (pair? (dk-goal)) (eq? (car (dk-goal)) 'and))
      (for-each (lambda (lf) (dk-focus! lf) (fs-conj-close!))
                (dk-opened (lambda () (di))))
      (ass)))

;;; -----------------------------------------------------------------------
;;; The definition.
;;;
;;; The SEP binder is `t_', NOT `s_': the element variable of the membership
;;; law below is `s_', and a SEP binder spelled the same would be captured on
;;; the unfold.  (Both the reader and MIT Scheme fold case, so this is the
;;; ordinary VNB name-collision hazard, one level in; `functoid-binder-audit'
;;; checks the parameter but not the caller's choice of element name.)

(def-functoid 'FIN-SUBSETS '(a_)
  '(SEP t_ (POWER a_) (IN (CARD t_) NN)))
(notation! 'FIN-SUBSETS 'kind 'functoid 'arity 1
           'english "the finite subsets of $1")

;;; -----------------------------------------------------------------------
;;; (1) fin-subsets-membership -- the characterisation.
;;;
;;;   s in FIN-SUBSETS(a)  iff  s in SET  and  s subset a  and  CARD(s) in NN
;;;
;;; The inclusion is spelled out elementwise rather than with SUBSET, to match
;;; `power-set-membership' (theory.scm:300) and `card-subset-nn', both of which
;;; state it that way.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL s_
        (IFF (IN s_ (FIN-SUBSETS a_))
             (AND (IN s_ SET)
                  (AND (FORALL z (IMPLIES (IN z s_) (IN z a_)))
                       (IN (CARD s_) NN))))))))
  (fs-peel!)
  (mac 'fin-subsets)
  ;; `di' on an IFF opens BOTH directions with each one's hypothesis already in
  ;; context (the subclass-of-set-is-set idiom), so there is no second `di'.
  ;; Both directions are then one membership citation and `prop': the SEP layer
  ;; contributes `s in POWER(a)' and `CARD s in NN', power-set-membership
  ;; relates the first to the two conjuncts, and the rest is propositional.
  (for-each
    (lambda (lf)
      (dk-focus! lf)
      (if (and (pair? (dk-goal)) (eq? (car (dk-goal)) 'and))
          ;; ==>  membership in the SEP gives all three conjuncts
          (begin
            (sep-me (list 'IN 's_ (fs-sep 'a_)))
            (fact 'power-set-membership 'a_ 's_)
            (prop))
          ;; <==  the three conjuncts put s back in the SEP
          (begin
            (fact 'power-set-membership 'a_ 's_)
            (in-sep! (lambda () (prop))     ; s in POWER(a)
                     (lambda () (prop)))))) ; CARD s in NN
    (dk-opened (lambda () (di))))))
(qed 'fin-subsets-membership)
(topic! 'fin-subsets-membership 'constructions)

;;; -----------------------------------------------------------------------
;;; (2) fin-subsets-is-set -- the carrier is a set when a is.
;;;
;;; POWER(a) is a set (power-set) and a SEP of a set is a set (sep-sethood).

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (IMPLIES (IN a_ SET) (IN (FIN-SUBSETS a_) SET)))))
  (fs-peel!)
  (fact 'power-set 'a_)
  (mac 'fin-subsets)
  (sep-set)
  (ass)))
(qed 'fin-subsets-is-set)
(topic! 'fin-subsets-is-set 'constructions)

;;; -----------------------------------------------------------------------
;;; union-empty-right and union-assoc were proven HERE until 2026-09-20; they are now
;;; proven in theorem-library/union-laws.scm, which loads far above this file (batch 9-B,
;;; CARD := CARD-STAR).  The blocks are in
;;; archive/2026-09-20-card-defined/fin-subsets-before-split.scm.

;;; -----------------------------------------------------------------------
;;; (5) fin-subsets-has-empty:  {} in FIN-SUBSETS(a).
;;;
;;; The inclusion conjunct is vacuous (nothing is in EMPTY-SET) and the
;;; finiteness conjunct is card-empty followed by 0 in NN.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (IN EMPTY-SET (FIN-SUBSETS a_)))))
  (fs-peel!)
  (ta 'empty-set-is-set)
  (have! '(FORALL z (IMPLIES (IN z EMPTY-SET) (IN z a_)))
         (lambda () (fs-peel!) (fact 'empty-set-has-no-members 'z) (prop)))
  (ta 'card-empty)
  (ta 'nn-zero-in)
  (have! '(IN (CARD EMPTY-SET) NN)
         (lambda () (subst '(= (CARD EMPTY-SET) 0)) (ass)))
  ;; the citation goes LAST and inside nothing: it lands a three-form
  ;; instantiation chain, and `prop' counts every one of those against its cap.
  (fact 'fin-subsets-membership 'a_ 'EMPTY-SET)
  (fs-only! '(iff (in empty-set (fin-subsets a_))
                  (and (in empty-set set)
                       (and (forall z (implies (in z empty-set) (in z a_)))
                            (in (card empty-set) nn))))
            '(in empty-set set)
            '(forall z (implies (in z empty-set) (in z a_)))
            '(in (card empty-set) nn))
  (prop)))
(qed 'fin-subsets-has-empty)
(topic! 'fin-subsets-has-empty 'constructions)

;;; -----------------------------------------------------------------------
;;; (6) fin-subsets-union-closed:  the carrier is closed under union.
;;;
;;; The one law of the three that needs the cardinality layer: sethood is
;;; union-set-closure and the inclusion is propositional, but the FINITENESS of
;;; the union is card-union-nn (theorem-library/card-inequalities.scm), which is
;;; exactly the theorem that had to be proved first.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL s_ (FORALL u_
        (IMPLIES (IN s_ (FIN-SUBSETS a_))
          (IMPLIES (IN u_ (FIN-SUBSETS a_))
                   (IN (UNION s_ u_) (FIN-SUBSETS a_)))))))))
  (fs-peel!)
  ;; Read each hypothesis out through the membership law INSIDE a `have!', so
  ;; that the citation's instantiation chain stays in the sub-proof: two of
  ;; those chains in the main context is four extra atoms, and `prop' is capped
  ;; at twelve.
  (have! '(AND (IN s_ SET)
               (AND (FORALL z (IMPLIES (IN z s_) (IN z a_))) (IN (CARD s_) NN)))
         (lambda () (fact 'fin-subsets-membership 'a_ 's_) (prop)))
  (have! '(AND (IN u_ SET)
               (AND (FORALL z (IMPLIES (IN z u_) (IN z a_))) (IN (CARD u_) NN)))
         (lambda () (fact 'fin-subsets-membership 'a_ 'u_) (prop)))
  (dk-split! '(AND (IN s_ SET)
                   (AND (FORALL z (IMPLIES (IN z s_) (IN z a_))) (IN (CARD s_) NN))))
  (dk-split! '(AND (IN u_ SET)
                   (AND (FORALL z (IMPLIES (IN z u_) (IN z a_))) (IN (CARD u_) NN))))
  ;; the three conjuncts of membership for the union
  (have! '(AND (IN s_ SET) (IN u_ SET)))
  (fact 'union-set-closure 's_ 'u_)
  (have! '(FORALL z (IMPLIES (IN z (UNION s_ u_)) (IN z a_)))
         (lambda ()
           (fs-peel!)
           (fact 'union-membership 's_ 'u_ 'z)
           (inst*! '(FORALL z (IMPLIES (IN z s_) (IN z a_))) 'z)
           (inst*! '(FORALL z (IMPLIES (IN z u_) (IN z a_))) 'z)
           (fs-only! '(iff (in z (union s_ u_)) (or (in z s_) (in z u_)))
                     '(implies (in z s_) (in z a_))
                     '(implies (in z u_) (in z a_))
                     '(in z (union s_ u_)))
           (prop)))
  (fact 'card-union-nn 's_ 'u_)
  (fact 'fin-subsets-membership 'a_ '(UNION s_ u_))
  (fs-only! '(iff (in (union s_ u_) (fin-subsets a_))
                  (and (in (union s_ u_) set)
                       (and (forall z (implies (in z (union s_ u_)) (in z a_)))
                            (in (card (union s_ u_)) nn))))
            '(in (union s_ u_) set)
            '(forall z (implies (in z (union s_ u_)) (in z a_)))
            '(in (card (union s_ u_)) nn))
  (prop)))
(qed 'fin-subsets-union-closed)
(topic! 'fin-subsets-union-closed 'constructions)
