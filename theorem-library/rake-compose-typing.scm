;;; rake-compose-typing.scm -- the seven RAN / composition typing supports of
;;; structure-library/compose-typing.scm, PROVEN modulo 0.
;;;
;;; All seven were `support' + `warrant! 'proof' -- the top warrant tier, "a
;;; machine-checked proof exists" -- and none had one.  Their warrant texts are
;;; the plans below, and all seven were right.
;;;
;;;   range-membership       a in DOM(f)                  =>  f(a) in RAN(f)
;;;   fun-range-membership   f in FUN(X), a in X          =>  f(a) in RAN(f)
;;;   ran-subset-codomain    f in FUN(X,Y)                =>  RAN(f) subset Y
;;;   compose-type-2..5      the mindless depth-n chains, each one application
;;;                          of fun-range-membership per link
;;;
;;; RAN is a def-functoid (compose-typing.scm:25): RAN(f) = IMAGE(f, DOM f).
;;; It is unfolded in the GOAL by `mac' -- never in an assumption, where a
;;; functoid name is "unknown theorem/macete" (CLAUDE.md, the mac-h trap).  The
;;; two `ran-subset-codomain' unfolds are therefore both goal-side: `mac RAN'
;;; BEFORE `mac subset-def', so the hypothesis the peel lands already reads
;;; IMAGE(f, DOM f) and `image-membership-iff' matches it.
;;;
;;; Citations, all of them base-theory axioms (`primitive', {} in every bill)
;;; except image-membership-iff, itself an axiom of injection.scm:
;;;
;;;   dom-membership       theory.scm:484    x in DOM(f) iff x in SET and f(x)=f(x)
;;;   dom-fun-membership   theory.scm:493    f in FUN(A) => (x in DOM f iff x in A)
;;;   fun-codomain-iff     theory.scm:459    f in FUN(A,B) iff f in FUN(A) and ...
;;;   subset-def           theory.scm:252
;;;   equality-symmetry    theorem-library/axioms.scm   (load position 15)
;;;   image-membership-iff structure-library/injection.scm:118  (position 83)
;;;
;;; LOAD WINDOW [141, end).  lo = 141: the latest-loading thing this file needs
;;; is not a theorem at all but `driver-kit' (position 140) and `interactive'
;;; (136); every mathematical citation is at position 83 or below.  There is no
;;; hi: nothing in the library cites any of the seven (the only occurrences
;;; outside the support site are the `topic!' lines of pss-topics.scm).
;;;
;;; Retire at structure-library/compose-typing.scm: :31-36, :42-48, :52-57,
;;; :68-75, :77-85, :87-96, :98-108.  The `def-functoid RAN' at :25 STAYS.
;;;
;;; Helper prefix: rct-.

;;; ---------------------------------------------------------------------
;;; range-membership -- f(a) lands in RAN(f) for any a in DOM(f).
;;;
;;; Unfold RAN, then image-membership-iff turns the goal into "some x in DOM(f)
;;; has f(x) = f(a)".  Witness x := a.  The second conjunct (f a) = (f a) is
;;; DEFINEDNESS, not reflexivity -- `=' is partial -- and it is the second
;;; conjunct of dom-membership applied to the hypothesis.  `mac-h' is
;;; destructive, but the two conjuncts are separate leaves by then, so the
;;; branch that still needs (IN a (DOM f)) intact has already closed.
(sp (make-wff '(FORALL f (FORALL a
     (IMPLIES (IN a (DOM f))
              (IN (f a) (RAN f)))))))
(di)
(mac 'RAN)
(mac 'image-membership-iff)
(ew 'a)
(di)                                    ; two leaves: a in DOM(f), and f(a)=f(a)
(ass-all)                               ; closes the first
(dk-focus! (car (proof-leaves)))
(dk-split! (dk-landed-1 (lambda () (mac-h 'dom-membership '(IN a (DOM f))))))
(ass)
(qed 'range-membership)

;;; ---------------------------------------------------------------------
;;; fun-range-membership -- the typed convenience.  dom-fun-membership bridges
;;; (IN a X) to (IN a (DOM f)); range-membership does the rest.
(sp (make-wff '(FORALL X (FORALL f (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN a X)
                (IN (f a) (RAN f)))))))))
(dk-peel!)
(inst+ (dk-fact! 'dom-fun-membership 'X 'f) 'a)
(dk-split! '(IFF (IN a (DOM f)) (IN a X)))
(detach! '(IMPLIES (IN a X) (IN a (DOM f))))
(fact 'range-membership 'f 'a)
(ass)
(qed 'fun-range-membership)

;;; ---------------------------------------------------------------------
;;; ran-subset-codomain -- RAN(f) sits inside any declared codomain.
;;;
;;; The one lemma here with content.  w in IMAGE(f, DOM f) gives a witness u in
;;; DOM(f) with f(u) = w; dom-fun-membership carries u into X and the codomain
;;; conjunct of fun-codomain-iff puts f(u) in Y; equality-symmetry flips
;;; f(u) = w so that `subst' can rewrite the goal (IN w Y) into (IN (f u) Y).
;;;
;;; The eigenvariables are READ OFF the goal and off dk-skolem!, never named
;;; literally: `di' and `ai' mint them from the global counter, so the names in
;;; a log are not names a later session mints.
(sp (make-wff '(FORALL X (FORALL Y (FORALL f
     (IMPLIES (IN f (FUN X Y))
              (SUBSET (RAN f) Y)))))))
(dk-peel!)
(mac 'RAN)                              ; goal: IMAGE(f, DOM f) subset Y
(mac 'subset-def)
(dk-peel!)                              ; lands (IN w (IMAGE f (DOM f)))
(define rct-w (cadr (dk-goal)))
(define rct-u
  (dk-skolem!
   (dk-landed-1
    (lambda () (mac-h 'image-membership-iff (list 'IN rct-w '(IMAGE f (DOM f))))))))
;; fun-codomain-iff is destructive here by design: nothing below needs
;; (IN f (FUN X Y)) itself, only its two conjuncts.
(define rct-parts
  (dk-split! (dk-landed-1 (lambda () (mac-h 'fun-codomain-iff '(IN f (FUN X Y)))))))
;; Pick the codomain universal out of what THIS split produced -- not out of the
;; whole context, which by now holds several look-alike FORALLs from `fact'.
(define rct-codom
  (let loop ((l rct-parts))
    (cond ((null? l) (error "rct: fun-codomain-iff landed no universal"))
          ((eq? (car (car l)) 'FORALL) (car l))
          (else (loop (cdr l))))))
(inst+ (dk-fact! 'dom-fun-membership 'X 'f) rct-u)
(dk-split! (list 'IFF (list 'IN rct-u '(DOM f)) (list 'IN rct-u 'X)))
(detach! (list 'IMPLIES (list 'IN rct-u '(DOM f)) (list 'IN rct-u 'X)))
(inst+ rct-codom rct-u)
(detach! (list 'IMPLIES (list 'IN rct-u 'X) (list 'IN (list 'f rct-u) 'Y)))
(fact 'equality-symmetry (list 'f rct-u) rct-w)
(subst (list '= rct-w (list 'f rct-u)))
(ass)
(qed 'ran-subset-codomain)

;;; ---------------------------------------------------------------------
;;; The chain lemmas.  One fun-range-membership per link, along
;;; X |-> RAN f |-> RAN g |-> ...; `fact' auto-detaches both antecedents,
;;; each of which is already in the context after the peel.
(sp (make-wff '(FORALL X (FORALL f (FORALL g (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN a X)
                  (IN (g (f a)) (RAN g)))))))))))
(dk-peel!)
(fact 'fun-range-membership 'X 'f 'a)
(fact 'fun-range-membership '(RAN f) 'g '(f a))
(ass)
(qed 'compose-type-2)

(sp (make-wff '(FORALL X (FORALL f (FORALL g (FORALL h (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN h (FUN (RAN g)))
           (IMPLIES (IN a X)
                    (IN (h (g (f a))) (RAN h)))))))))))))
(dk-peel!)
(fact 'fun-range-membership 'X 'f 'a)
(fact 'fun-range-membership '(RAN f) 'g '(f a))
(fact 'fun-range-membership '(RAN g) 'h '(g (f a)))
(ass)
(qed 'compose-type-3)

(sp (make-wff '(FORALL X (FORALL f (FORALL g (FORALL h (FORALL k (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN h (FUN (RAN g)))
           (IMPLIES (IN k (FUN (RAN h)))
             (IMPLIES (IN a X)
                      (IN (k (h (g (f a)))) (RAN k)))))))))))))))
(dk-peel!)
(fact 'fun-range-membership 'X 'f 'a)
(fact 'fun-range-membership '(RAN f) 'g '(f a))
(fact 'fun-range-membership '(RAN g) 'h '(g (f a)))
(fact 'fun-range-membership '(RAN h) 'k '(h (g (f a))))
(ass)
(qed 'compose-type-4)

(sp (make-wff '(FORALL X (FORALL f (FORALL g (FORALL h (FORALL k (FORALL m (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN h (FUN (RAN g)))
           (IMPLIES (IN k (FUN (RAN h)))
             (IMPLIES (IN m (FUN (RAN k)))
               (IMPLIES (IN a X)
                        (IN (m (k (h (g (f a))))) (RAN m)))))))))))))))))
(dk-peel!)
(fact 'fun-range-membership 'X 'f 'a)
(fact 'fun-range-membership '(RAN f) 'g '(f a))
(fact 'fun-range-membership '(RAN g) 'h '(g (f a)))
(fact 'fun-range-membership '(RAN h) 'k '(h (g (f a))))
(fact 'fun-range-membership '(RAN k) 'm '(k (h (g (f a)))))
(ass)
(qed 'compose-type-5)
