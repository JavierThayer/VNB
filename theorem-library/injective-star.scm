;;; injective-star.scm -- the bridge from the set-function vocabulary to the
;;; class-function one.
;;;
;;;   injection-is-injective-star :  f in INJECTION(X, Y)  =>  INJECTIVE-STAR(f)
;;;
;;; INJECTIVE-STAR (structure-library/injection.scm) says injectivity about the
;;; APPLICATION (F u), so F sits in the juxtaposition slot and may be a lambdoid,
;;; a VNB-LAMBDA or a plain variable; INJECTION says it about f as an OBJECT, and
;;; so applies only to genuine set-functions.  Without this lemma the library
;;; would carry two disconnected spellings of one notion.
;;;
;;; THE PROOF IS THE PARTIAL-EQUALITY ARGUMENT, and it is the reason INJECTIVE-STAR
;;; needs no domain argument.  Suppose (f u) = (f v).  A strict `=' asserts BOTH
;;; sides DEFINED (primitive-inferences.scm:588), so f(u) is defined -- which in
;;; VNB is written (= (f u) (f u)) and is exactly what `rfl' will close from that
;;; hypothesis.  fun-domain-apply-def (theory.scm:352) states
;;;     f in FUN(A)  =>  ( (= (f x) (f x))  iff  (IN x A) ),
;;; i.e. "f's domain is exactly A", so definedness hands back MEMBERSHIP: u is in
;;; X, and likewise v.  Now INJECTION's own injectivity clause -- which IS guarded
;;; by X -- applies, and gives u = v.
;;;
;;; So the unguarded form is not a weaker approximation of the guarded one: the
;;; guard is recoverable from definedness, and the two coincide wherever both are
;;; meaningful.  Off the domain the antecedent is false and there is nothing to
;;; prove, which is what lets INJECTIVE-STAR speak about a lambdoid on ORD.

;; From (= (f w) (f _)) or (= (f _) (f w)) in the context, land (IN w X).
;; `rfl' takes its DEFINEDNESS witness from a context (= t _) / (= _ t)
;; (asm-establishes-defined?, primitive-inferences.scm:592), and `ai' on the
;; fun-domain-apply-def IFF lands both directions, of which we detach one.
(define (isb-in-domain! w)
  (have! `(= (f ,w) (f ,w)) (lambda () (rfl)))
  (let* ((iff  (dk-fact! 'fun-domain-apply-def 'X 'f w))
         (dirs (dk-landed (lambda () (ai iff))))
         (fwd  (or (any-pred (lambda (d) (and (pair? d) (eq? (car d) 'IMPLIES)
                                              (equal? (cadr d) `(= (f ,w) (f ,w)))))
                             dirs)
                   (error "isb-in-domain!: no forward direction among" dirs))))
    (detach! fwd)))

(sp (make-wff '(FORALL X (FORALL Y (FORALL f
                 (IMPLIES (IN f (INJECTION X Y)) (INJECTIVE-STAR f)))))))
(di) (di)
(mac 'injective-star)
(di) (di) (di)                          ; u_, v_, and the hypothesis (f u_) = (f v_)

;; INJECTION gives a FUN membership and the X-guarded injectivity clause.
(define isb-injx
  (car (filter (dk-head? 'FORALL)
               (dk-split! (dk-landed-1
                 (lambda () (mac-h 'injection-membership-iff
                                   '(IN f (INJECTION X Y)))))))))
;; ... and FUN(X,Y) membership gives FUN(X) membership, which is what the
;; domain-apply law is stated over.
(dk-split! (dk-landed-1 (lambda () (mac-h 'fun-codomain-iff '(IN f (FUN X Y))))))

(isb-in-domain! 'u_)
(isb-in-domain! 'v_)
(inst*! isb-injx 'u_ 'v_)
(ass)
(qed 'injection-is-injective-star)
(topic! 'injection-is-injective-star 'plumbing)
