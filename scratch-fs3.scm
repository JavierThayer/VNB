;;; scratch-fs3.scm -- dev: insert-last-is-bijection, finsum-insert

(define (last-node) (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (refocus! n) (set-proof-state-focus! *ps* n))
(define (cur-goal)
  (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (probe tag)
  (display ";; --- ") (display tag) (display " ---") (newline)
  (display "GOAL: ") (display (cur-goal)) (newline)
  (display "OPEN: ")
  (display (length (dg-ungrounded-nodes (proof-state-dg *ps*))))
  (newline))

;;; ===================================================================
;;; ord-segment-succ-split: i in os(succ n) => i in os n or i = n.
(sp (make-wff
     '(FORALL n (IMPLIES (IN n NN)
        (FORALL i (IMPLIES (IN i (ORD-SEGMENT (succ n)))
          (OR (IN i (ORD-SEGMENT n)) (= i n))))))))
(define oss-n (eigen-name 'n *fresh-counter*))
(define oss-i (eigen-name 'i (+ *fresh-counter* 1)))
(di) (di)
(cut `(IMPLIES (IN ,oss-i (ORD-SEGMENT (succ ,oss-n)))
               (OR (IN ,oss-i (ORD-SEGMENT ,oss-n)) (= ,oss-i ,oss-n))))
(define u-oss (last-node))
  (mac 'ord-segment-nn-succ)
  (di) (ass)
(refocus! u-oss)
(bc `(IMPLIES (IN ,oss-i (ORD-SEGMENT (succ ,oss-n)))
              (OR (IN ,oss-i (ORD-SEGMENT ,oss-n)) (= ,oss-i ,oss-n))))
(ass)
(display (if (proof-done? *ps*)
             ";; ord-segment-succ-split OK\n"
             ";; ord-segment-succ-split OPEN\n"))
(qed 'ord-segment-succ-split)

;;; ===================================================================
;;; insert-last-is-bijection
(define ilb-goal
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL S (IMPLIES (IN S SET)
       (FORALL x (IMPLIES (AND (IN x SET) (NOT (IN x S)))
         (FORALL phi (IMPLIES (IN phi (BIJECTION (ORD-SEGMENT n) S))
           (IN (INSERT-LAST phi x n)
               (BIJECTION (ORD-SEGMENT (succ n)) (UNION S (PAIR x x)))))))))))))
(sp (make-wff ilb-goal))
(define c0 *fresh-counter*)
(define nv   (eigen-name 'n   c0))
(define Sv   (eigen-name 'S   (+ c0 1)))
(define xv   (eigen-name 'x   (+ c0 2)))
(define phiv (eigen-name 'phi (+ c0 3)))
(di) (di) (di) (di)
(ai `(AND (IN ,xv SET) (NOT (IN ,xv ,Sv))))
(mac 'bijection-membership-iff)
(probe "after bijection-membership-iff")
(di)
(define u-rest (last-node))   ; the (AND inj surj) goal

;;; ---- Part A: psi in FUN(os(succ nv), UNION Sv {xv}) ----
(mac 'INSERT-LAST)
(lam-t)
(di)
(define iev (cadr (cadr (cadr (cur-goal)))))
(probe "FUN part per-i goal")
(define IFt `(IF (IN ,iev (ORD-SEGMENT ,nv)) (,phiv ,iev) ,xv))

(cut `(OR (IN ,iev (ORD-SEGMENT ,nv)) (= ,iev ,nv)))
(define u-fc (last-node))
  (bc* 'ord-segment-succ-split () (ass) (ass))
(refocus! u-fc)
(ai `(OR (IN ,iev (ORD-SEGMENT ,nv)) (= ,iev ,nv)))
(define u-fR (last-node))   ; branch-R (iev = nv)

;; branch-L : iev in os nv
(if-true IFt)
(define u-itL (last-node))
  (ass)
(refocus! u-itL)
(subst `(= ,IFt (,phiv ,iev)))
(mac 'union-membership)
(oi-l)
(cut `(IN ,phiv (FUN (ORD-SEGMENT ,nv) ,Sv)))
(define u-pf (last-node))
  (bc* 'bijection-in-fun () (ass))
(refocus! u-pf)
(bc* 'fun-apply-type ((A `(ORD-SEGMENT ,nv))) (begin (di) (ass-all)))

;; branch-R : iev = nv
(refocus! u-fR)
(if-false IFt)
(define u-ifR (last-node))
  (subst `(= ,iev ,nv))
  (bc* 'ord-segment-self () (ass))
(refocus! u-ifR)
(subst `(= ,IFt ,xv))
(mac 'union-membership)
(oi-r)
(mac 'pairing-membership)
(oi-l) (rfl)

(probe "after FUN part")
(display ";; (stopping after FUN-part)\n")
