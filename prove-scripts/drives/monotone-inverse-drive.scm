;;; mi-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-23).
;;;
;;; PACKAGING THE INVERSE AS A FUNCTION.  `monotone-ccint-inverse-exists'
;;; (theorem-library/monotone-inverse.scm) says every y in [f(a),f(b)] is f(x)
;;; for exactly ONE x in [a,b].  That is the inverse stated POINTWISE.  The
;;; obvious next move is to turn it into a term:
;;;
;;;     g  =  VNB-LAMBDA y in [f(a),f(b)].  IOTA x. x in [a,b] and f(x) = y
;;;
;;; and to type it into FUN([f(a),f(b)], [a,b]).  Nothing about continuity is
;;; involved -- this is the algebraic half, and it is the half that decides the
;;; DESIGN QUESTION at the end of monotone-inverse.scm: if g can be built and
;;; typed on the image interval, then the missing piece really is only
;;; continuity relative to a subset, and not the whole of a subspace structure.
;;;
;;; Run:   ./prover -b -i scratchpad/mi-drive.scm     (or (load "...") in a REPL)
;;;
;;; The lines below leave you just after `lam-t', which opens TWO leaves:
;;;
;;;   (A)  (IN (CCINT (f a) (f b)) SET)          -- the SETHOOD of the domain
;;;   (B)  forall y in [f(a),f(b)].  (IOTA x. x in [a,b] and f(x) = y) in [a,b]
;;;
;;; (A) IS THE FIRST FINDING, and it is small: there is NO `ccint-in-set' in the
;;; tree.  `dk-lam-t!' knows how to close a sethood leaf for NN/RR/ZZ/QQ/CC and
;;; for INTERVAL (via `interval-in-set') and for CARTESIAN -- and for nothing
;;; else, CCINT included (driver-kit.scm:877-895).  CCINT(a,b) is
;;; SEP(x in RR | a<=x and x<=b) (extreme-value.scm:15), so its sethood is
;;; separation over a set, exactly as `interval-in-set' is; the lemma simply
;;; does not exist.  Whether it belongs in ccint-basics.scm beside
;;; `ccint-membership' and in `dk-set-close!' beside INTERVAL is your call.
;;;
;;; (B) IS THE REAL ONE, and it is where the new theorem earns its keep:
;;; `iota-d' (interactive.scm) posts the existence-and-uniqueness obligation
;;; plus the goal with the defining property in hand, and
;;; `monotone-ccint-inverse-exists' is exactly that obligation, already proven.
;;; The pattern to copy is theorem-library/chain-rule.scm:293-330
;;; (`deriv-of-is-diff-at'), which does the same thing for DERIV's own IOTA.
;;;
;;; If both close, the next question is whether `IS-STRICTLY-INCREASING-ON'
;;; should keep its hoisted `(IN f (FUN RR RR))' -- with g typed into
;;; FUN([f(a),f(b)],[a,b]) it cannot be said to be increasing in the present
;;; vocabulary, and that is the fork described at the head of
;;; monotone-inverse.scm.

(load "theorem-library/monotone-inverse.scm")

(define mi-inv-lam
  '(VNB-LAMBDA y_ (CCINT (f a) (f b))
     (IOTA x_ (AND (IN x_ (CCINT a b)) (= (f x_) y_)))))

(sp (make-wff
  (forall-guarded '(f a b)
    (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR) '(<= a b)
          '(FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
          '(IS-STRICTLY-INCREASING-ON f (CCINT a b)))
    (list 'IN mi-inv-lam '(FUN (CCINT (f a) (f b)) (CCINT a b))))))
(mi-peel!)
(display "\n### goal before lam-t: ") (write (dk-goal)) (newline)
(for-each (lambda (k) (dk-focus! k)
            (display "### open leaf: ") (write (dk-goal)) (newline))
          (dk-opened (lambda () (lam-t))))
(display "### (A) is the sethood leaf, (B) the pointwise typing leaf.\n")
