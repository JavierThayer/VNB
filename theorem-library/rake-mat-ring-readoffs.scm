;;; rake-mat-ring-readoffs.scm -- the MAT-RING slot read-offs and the two
;;; curried-operation FUN typings, PROVEN (rake, 2026-09-19).
;;;
;;; WHAT IS HERE -- seven theorems, every one `proven modulo 0'.  All seven were
;;; ASSERTED supports in structure-library/matrix.scm and are the whole
;;; `mat-ring-*' half of mat-ring-is-ring's bill:
;;;
;;;   mat-ring-carr      structure-library/matrix.scm:551   RETIRE
;;;   mat-ring-add       structure-library/matrix.scm:554   RETIRE
;;;   mat-ring-mul       structure-library/matrix.scm:557   RETIRE
;;;   mat-ring-neg       structure-library/matrix.scm:560   RETIRE
;;;   mat-ring-zero      structure-library/matrix.scm:563   RETIRE
;;;   mat-ring-add-fun   structure-library/matrix.scm:567   RETIRE
;;;   mat-ring-mul-fun   structure-library/matrix.scm:572   RETIRE
;;;
;;; Every statement is COPIED LITERALLY from the support's definition site; none
;;; is restated.  (The other eight leaves of that bill -- matadd-assoc/comm/
;;; zero-left/zero-right/neg-left/neg-right, matmul-left-dist/right-dist -- are
;;; the matrix ALGEBRA, not read-offs, and are not touched here.)
;;;
;;; THE STATEMENTS WERE AUDITED FIRST, against CLAUDE.md's species of false or
;;; underdetermined support, and all seven are sound as written: the dimension n
;;; carries `(IN n NN)' and the ring carries `(IS-RING a)' in every one (both
;;; guards were added 2026-09-16 for exactly this reason), and the two FUN
;;; typings are about a VNB-LAMBDA whose DECLARED domain is literally the FUN's
;;; domain -- not a bare constant beside a strict equation, which is the shape
;;; that proved FALSITY for eplus/etimes.
;;;
;;; THE MECHANISM: ONE DRIVER, NOT SEVEN PROOFS.
;;;
;;; The five slot read-offs all go through `rmr-read-off!', which is the view
;;; read-off idiom of CLAUDE.md ("Structures and views") in one procedure:
;;;
;;;     (dk-peel!)          the binders and both guards
;;;     TYPERS              type whatever the definedness certificate refuses
;;;     (slot ACC)          the target accessor down to (NTH k _)
;;;     (mac 'MAT-RING)     the functoid unfold, to the literal 6-tuple
;;;     (nth-r)             NTH k of a LIST literal -- the slot's value
;;;     read-back           undo the accessor rewrite where it hit the RIGHT side
;;;     (rfl)
;;;
;;; THE READ-BACK IS THE ONLY SUBTLE STEP, and it is CLAUDE.md's "iterate to a
;;; fixpoint when target and source accessor are the same symbol", generalised.
;;; A macete rewrites EVERY occurrence, so `(slot 'CARR)' on
;;;
;;;     CARR(MAT-RING(a,n)) = MAT(n, n, CARR(a))
;;;
;;; takes the right-hand side's `CARR(a)' to `NTH(1, a)' along with the left, and
;;; after the NTH reduction the two sides are equal mathematically and DIFFERENT
;;; S-expressions, which `rfl' cannot close.  `rmr-read-back!' collects every
;;; residue `NTH(k, x)' left in the goal (x not a LIST literal), proves
;;; `NTH(k, x) == ACC(x)' on a side branch by the same accessor macete, and
;;; `subst's it back.  Unlike ag-view-read-offs.scm's `avr-read-off!' -- the same
;;; move, one storey shallower -- it does not assume the residue is the goal's
;;; top-level right-hand side: here the accessor is nested, inside MAT(n,n,-).
;;; For ADD / MUL / NEG / ZERO there is no residue and the step is a no-op.
;;;
;;; The two FUN typings need no new machinery at all: `dk-lam-fun!' (driver-kit)
;;; is exactly this obligation -- lam-t, the CARTESIAN sethood leaf, the peeled
;;; pointwise typing, and the matrix typing chain (matadd-type / matmul-type,
;;; the latter's `n = 0 => m = 0 or k = 0' guard discharged by `prop' because the
;;; product is square).  So matrix.scm's warrant text for them -- "lam-t types
;;; only single-binder lambdas" -- is STALE: `pi-lambda-type!' has typed a binder
;;; LIST against a CARTESIAN domain componentwise since 2026-08-14.
;;;
;;; LOAD WINDOW [after theorem-library/rake-mat-typing, before
;;;              theorem-library/mat-ring-proof).
;;;   lo -- rake-mat-typing is the LATEST citation: mat-is-set, matadd-type and
;;;         matneg-type live there.  The others are earlier: mat-typing-bundle
;;;         (matmul-type, zeromat-type), rake-algebra (ring-carr-in-set),
;;;         structure-library/matrix (the MAT-RING functoid), structure-library/
;;;         cartesian (cartesian-set-iff, fired by dk-lam-fun!'s sethood lane).
;;;   hi -- theorem-library/mat-ring-proof is the ONLY citer of all seven (it
;;;         uses the five read-offs as MACETES and `fact's the two FUN typings),
;;;         so this file must load before it once they are retired.
;;;   Suggested slot: immediately after theorem-library/rake-det-small, which
;;;   proved the sixth read-off `mat-ring-one' on 2026-09-18 by hand and is the
;;;   natural neighbour.
;;;
;;; Helper prefix: rmr-.

;;; ---- the file's own kit -----------------------------------------------

(define (rmr-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** rake-mat-ring-readoffs: ") (display name)
        (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))))
  (qed name))

;;; Does ACC occur APPLIED (to one argument) anywhere in E?
(define (rmr-applied? acc e)
  (let walk ((t e))
    (and (pair? t)
         (or (and (eq? (car t) acc) (= (length t) 2))
             (let loop ((xs (cdr t)))
               (and (pair? xs) (or (walk (car xs)) (loop (cdr xs)))))
             (and (pair? (car t)) (walk (car t)))))))

;;; Every (NTH k x) subterm of E whose x is NOT a LIST literal: the residues the
;;; accessor macete left behind, which `nth-r' cannot reduce and `rfl' will not
;;; match.  Outermost-first, deduplicated.
(define (rmr-nth-residues e)
  (let ((found '()))
    (let walk ((t e))
      (if (pair? t)
          (begin
            (if (and (eq? (car t) 'NTH) (= (length t) 3)
                     (not (and (pair? (caddr t)) (eq? (car (caddr t)) 'LIST))))
                (if (not (member t found)) (set! found (cons t found))))
            (for-each walk (cdr t))
            (if (pair? (car t)) (walk (car t))))))
    (reverse found)))

;;; Put ACC back where the opening `slot' rewrote a side the statement meant to
;;; keep.  Each residue's projection equation is proved on its own side branch by
;;; the same accessor macete (`slot-h' is NOT the door: it has no accessor
;;; fallback -- CLAUDE.md), and one `subst' undoes it in the goal.
(define (rmr-read-back! acc)
  (for-each (lambda (r)
              (let ((src (list acc (caddr r))))
                (have! (list '== r src) (lambda () (slot acc) (qrfl)))
                (subst (list '== r src))))
            (rmr-nth-residues (dk-goal))))

;;; (rmr-read-off! NAME STMT CTOR ACC TYPERS)
;;;   NAME    the theorem name
;;;   STMT    the statement, copied literally from the support's definition site
;;;   CTOR    the constructor macete that unfolds the tuple, here 'MAT-RING
;;;   ACC     the accessor being read off: CARR / ADD / MUL / NEG / ZERO
;;;   TYPERS  a thunk, run after the peel, that types the terms the definedness
;;;           certificate refuses (a MATOF is an IOTA and is never certified),
;;;           so that the closing `rfl' has its obligation in context.
(define (rmr-read-off! name stmt ctor acc typers)
  (sp (make-wff stmt))
  (dk-peel!)
  (typers)
  (if (not (rmr-applied? acc (dk-goal)))
      (error "rmr-read-off!: the accessor does not occur in the goal" name acc))
  (slot acc)
  (mac ctor)
  (nth-r)
  (rmr-read-back! acc)
  (rfl)
  (rmr-done! name))

;;; (rmr-op-fun! NAME STMT) -- a curried operation's FUN typing.  The whole proof
;;; is the peel, the two sethood citations the CARTESIAN lane needs, and
;;; dk-lam-fun!.
(define (rmr-op-fun! name stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (fact 'ring-carr-in-set 'a)
  (fact 'mat-is-set '(CARR a) 'n 'n)
  (dk-lam-fun!)
  (rmr-done! name))

;;; The sethood of the carrier MAT(n,n,CARR a): what `rfl' needs for the CARR
;;; read-off, and what dk-lam-fun!'s CARTESIAN sethood lane bottoms out in.
(define (rmr-carr-set!)
  (fact 'ring-carr-in-set 'a)
  (fact 'mat-is-set '(CARR a) 'n 'n))

;;; =====================================================================
;;; (1) mat-ring-carr -- slot 1.  The one case where target and source
;;; accessor are the same symbol, so the read-back fires.
;;; =====================================================================
(rmr-read-off! 'mat-ring-carr
  '(FORALL a (FORALL n (IMPLIES (IS-RING a) (IMPLIES (IN n NN) (= (CARR (MAT-RING a n)) (MAT n n (CARR a)))))))
  'MAT-RING 'CARR rmr-carr-set!)
(topic! 'mat-ring-carr 'plumbing)

;;; =====================================================================
;;; (2) mat-ring-add -- slot 2, the curried entrywise sum.
;;; =====================================================================
(rmr-read-off! 'mat-ring-add
  '(FORALL a (FORALL n (IMPLIES (IS-RING a) (IMPLIES (IN n NN) (= (ADD (MAT-RING a n)) (VNB-LAMBDA (LIST P Q) (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MATADD a P Q)))))))
  'MAT-RING 'ADD rmr-carr-set!)
(topic! 'mat-ring-add 'plumbing)

;;; =====================================================================
;;; (3) mat-ring-mul -- slot 3, the curried matrix product.
;;; =====================================================================
(rmr-read-off! 'mat-ring-mul
  '(FORALL a (FORALL n (IMPLIES (IS-RING a) (IMPLIES (IN n NN) (= (MUL (MAT-RING a n)) (VNB-LAMBDA (LIST P Q) (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MATMUL a P Q)))))))
  'MAT-RING 'MUL rmr-carr-set!)
(topic! 'mat-ring-mul 'plumbing)

;;; =====================================================================
;;; (4) mat-ring-neg -- slot 4, entrywise negation (single-binder lambda).
;;; =====================================================================
(rmr-read-off! 'mat-ring-neg
  '(FORALL a (FORALL n (IMPLIES (IS-RING a) (IMPLIES (IN n NN) (= (NEG (MAT-RING a n)) (VNB-LAMBDA P (MAT n n (CARR a)) (MATNEG a P)))))))
  'MAT-RING 'NEG rmr-carr-set!)
(topic! 'mat-ring-neg 'plumbing)

;;; =====================================================================
;;; (5) mat-ring-zero -- slot 5, the all-zero matrix.  ZEROMAT is a MATOF,
;;; i.e. an IOTA, which the definedness certificate NEVER accepts, so the
;;; typing must be in context before `rfl' (CLAUDE.md, the LUTINS rule).
;;; =====================================================================
(rmr-read-off! 'mat-ring-zero
  '(FORALL a (FORALL n (IMPLIES (IS-RING a) (IMPLIES (IN n NN) (= (ZERO (MAT-RING a n)) (ZEROMAT a n n))))))
  'MAT-RING 'ZERO
  (lambda () (rmr-carr-set!) (fact 'zeromat-type 'a 'n 'n)))
(topic! 'mat-ring-zero 'plumbing)

;;; =====================================================================
;;; (6) mat-ring-add-fun -- the curried sum is a function MAT x MAT -> MAT.
;;; =====================================================================
(rmr-op-fun! 'mat-ring-add-fun
  '(FORALL a (IMPLIES (IS-RING a) (FORALL n (IMPLIES (IN n NN)
     (IN (VNB-LAMBDA (LIST P Q) (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MATADD a P Q))
         (FUN (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MAT n n (CARR a)))))))))
(topic! 'mat-ring-add-fun 'plumbing)

;;; =====================================================================
;;; (7) mat-ring-mul-fun -- the curried product is a function MAT x MAT -> MAT.
;;; The product is square, so matmul-type's guard is a propositional tautology
;;; and dk-typ--product-guard! lands it by `prop' without being asked.
;;; =====================================================================
(rmr-op-fun! 'mat-ring-mul-fun
  '(FORALL a (IMPLIES (IS-RING a) (FORALL n (IMPLIES (IN n NN)
     (IN (VNB-LAMBDA (LIST P Q) (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MATMUL a P Q))
         (FUN (CARTESIAN (MAT n n (CARR a)) (MAT n n (CARR a))) (MAT n n (CARR a)))))))))
(topic! 'mat-ring-mul-fun 'plumbing)
