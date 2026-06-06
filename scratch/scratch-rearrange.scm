;;; scratch-rearrange.scm -- developing ag-mul-rearrange.
;;;
;;;   IS-ABELIAN-GROUP(ag) =>
;;;     forall a,b,c in A(ag).  (a*b)*c = (a*c)*b
;;;
;;; group-assoc reassociates each side; abelian-group-mul-comm swaps b,c.
;;; group-assoc CANNOT be used as a macete -- its source ((MUL s)(..)..) has
;;; a compound head, which match-expr cannot match -- so it is applied the
;;; long way: ta + inst + a cut-chain + subst.
(load "load.scm")

(define rearrange-goal
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL a (IMPLIES (IN a (A ag))
       (FORALL b (IMPLIES (IN b (A ag))
         (FORALL c (IMPLIES (IN c (A ag))
           (= ((MUL ag) ((MUL ag) a b) c)
              ((MUL ag) ((MUL ag) a c) b)))))))))))

(sp (make-wff rearrange-goal))
(define rc *fresh-counter*)
(define ragv (eigen-name 'ag rc))
(define rav  (eigen-name 'a (+ rc 1)))
(define rbv  (eigen-name 'b (+ rc 2)))
(define rcv  (eigen-name 'c (+ rc 3)))
(di) (di) (di) (di) (di)        ; peel ag/IS-AG, a/inA, b/inB, c/inC
(display "--- after di-peeling ---\n") (show)

;;; IS-GROUP(ag)
(cut `(IS-GROUP ,ragv))
(define u-isg (last-node))
  (ta 'abelian-group-is-group)
  (inst '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s) (IS-GROUP s))) ragv)
  (bc `(IMPLIES (IS-ABELIAN-GROUP ,ragv) (IS-GROUP ,ragv)))
  (ass)
(refocus! u-isg)
(display "--- IS-GROUP established ---\n") (show)

;;; ---- formula abbreviations ------------------------------------------
(define ga
  '(FORALL s (IMPLIES (IS-GROUP s)
     (FORALL a (IMPLIES (IN a (A s))
       (FORALL b (IMPLIES (IN b (A s))
         (FORALL c (IMPLIES (IN c (A s))
           (= ((MUL s) ((MUL s) a b) c)
              ((MUL s) a ((MUL s) b c))))))))))))
(define ga-Fa
  `(FORALL a (IMPLIES (IN a (A ,ragv))
     (FORALL b (IMPLIES (IN b (A ,ragv))
       (FORALL c (IMPLIES (IN c (A ,ragv))
         (= ((MUL ,ragv) ((MUL ,ragv) a b) c)
            ((MUL ,ragv) a ((MUL ,ragv) b c))))))))))
(define ga-imp `(IMPLIES (IS-GROUP ,ragv) ,ga-Fa))
(define ga-Fb1
  `(FORALL b (IMPLIES (IN b (A ,ragv))
     (FORALL c (IMPLIES (IN c (A ,ragv))
       (= ((MUL ,ragv) ((MUL ,ragv) ,rav b) c)
          ((MUL ,ragv) ,rav ((MUL ,ragv) b c))))))))
(define ga-Fc1
  `(FORALL c (IMPLIES (IN c (A ,ragv))
     (= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rbv) c)
        ((MUL ,ragv) ,rav ((MUL ,ragv) ,rbv c))))))
(define eq1
  `(= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rbv) ,rcv)
      ((MUL ,ragv) ,rav ((MUL ,ragv) ,rbv ,rcv))))
(define ga-Fc2
  `(FORALL c (IMPLIES (IN c (A ,ragv))
     (= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rcv) c)
        ((MUL ,ragv) ,rav ((MUL ,ragv) ,rcv c))))))
(define eq2
  `(= ((MUL ,ragv) ((MUL ,ragv) ,rav ,rcv) ,rbv)
      ((MUL ,ragv) ,rav ((MUL ,ragv) ,rcv ,rbv))))
(define agc
  '(FORALL s (IMPLIES (IS-ABELIAN-GROUP s)
     (FORALL a (IMPLIES (IN a (A s))
       (FORALL b (IMPLIES (IN b (A s))
         (= ((MUL s) a b) ((MUL s) b a)))))))))
(define agc-Fa
  `(FORALL a (IMPLIES (IN a (A ,ragv))
     (FORALL b (IMPLIES (IN b (A ,ragv))
       (= ((MUL ,ragv) a b) ((MUL ,ragv) b a)))))))
(define agc-Fb
  `(FORALL b (IMPLIES (IN b (A ,ragv))
     (= ((MUL ,ragv) ,rbv b) ((MUL ,ragv) b ,rbv)))))
(define eqc
  `(= ((MUL ,ragv) ,rbv ,rcv) ((MUL ,ragv) ,rcv ,rbv)))

;;; ---- assoc1:  (a*b)*c = a*(b*c) -------------------------------------
(ta 'group-assoc)
(inst ga ragv)
(cut ga-Fa) (define u1 (last-node)) (bc ga-imp) (ass) (refocus! u1)
(inst ga-Fa rav)
(cut ga-Fb1) (define u2 (last-node))
  (bc `(IMPLIES (IN ,rav (A ,ragv)) ,ga-Fb1)) (ass) (refocus! u2)
(inst ga-Fb1 rbv)
(cut ga-Fc1) (define u3 (last-node))
  (bc `(IMPLIES (IN ,rbv (A ,ragv)) ,ga-Fc1)) (ass) (refocus! u3)
(inst ga-Fc1 rcv)
(cut eq1) (define u4 (last-node))
  (bc `(IMPLIES (IN ,rcv (A ,ragv)) ,eq1)) (ass) (refocus! u4)
(display "--- assoc1 (eq1) established ---\n") (show)

;;; ---- assoc2:  (a*c)*b = a*(c*b)  (reuse ga-Fa, ga-Fb1) --------------
(inst ga-Fb1 rcv)
(cut ga-Fc2) (define u5 (last-node))
  (bc `(IMPLIES (IN ,rcv (A ,ragv)) ,ga-Fc2)) (ass) (refocus! u5)
(inst ga-Fc2 rbv)
(cut eq2) (define u6 (last-node))
  (bc `(IMPLIES (IN ,rbv (A ,ragv)) ,eq2)) (ass) (refocus! u6)
(display "--- assoc2 (eq2) established ---\n") (show)

;;; ---- comm:  b*c = c*b -----------------------------------------------
(ta 'abelian-group-mul-comm)
(inst agc ragv)
(cut agc-Fa) (define u7 (last-node))
  (bc `(IMPLIES (IS-ABELIAN-GROUP ,ragv) ,agc-Fa)) (ass) (refocus! u7)
(inst agc-Fa rbv)
(cut agc-Fb) (define u8 (last-node))
  (bc `(IMPLIES (IN ,rbv (A ,ragv)) ,agc-Fb)) (ass) (refocus! u8)
(inst agc-Fb rcv)
(cut eqc) (define u9 (last-node))
  (bc `(IMPLIES (IN ,rcv (A ,ragv)) ,eqc)) (ass) (refocus! u9)
(display "--- comm (eqc) established ---\n") (show)

;;; ---- finish ---------------------------------------------------------
(subst eq1)              ; goal LHS  (a*b)*c -> a*(b*c)
(subst eq2)              ; goal RHS  (a*c)*b -> a*(c*b)
(subst eqc)              ; a*(b*c) -> a*(c*b)
(rfl)
(display "--- DONE ---\n") (show)
