;;; infinite-products-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch6/ch6-prod.scm (vocab).
;;; Library: complex-analysis.
;;; Proof-free: the definitions (with their notation! lines) moved here from the proof file(s) named above.

(def-by-nn-recursion 'PPROD '(ppf_) 1 '(ppn_ ppv_) '(* ppv_ (ppf_ ppn_)))
(notation! 'PPROD 'kind 'functoid 'arity 2 'english "the partial product of the first $2 terms of $1")
(def-predicate 'PROD-CONVERGES-TO '(pcf_ pcl_)
  '(AND (IN pcf_ (FUN NN CC))
    (FORSOME pcm_ (AND (IN pcm_ NN)
      (AND (FORALL pck_ (IMPLIES (IN pck_ NN) (IMPLIES (<= pcm_ pck_) (NOT (= (pcf_ pck_) 0)))))
        (FORSOME pcz_ (AND (IN pcz_ CC) (AND (NOT (= pcz_ 0))
          (AND (CONVERGES-TO CC-MS (VNB-LAMBDA pcn_ NN (PPROD (VNB-LAMBDA pcj_ NN (pcf_ (+ pcm_ pcj_))) pcn_)) pcz_)
               (= pcl_ (* (PPROD pcf_ pcm_) pcz_)))))))))))
(notation! 'PROD-CONVERGES-TO 'kind 'predicate 'arity 2 'english "the infinite product of $1 converges to $2")
(def-predicate 'PROD-CONVERGES '(pdf_) '(FORSOME pdl_ (PROD-CONVERGES-TO pdf_ pdl_)))
(notation! 'PROD-CONVERGES 'kind 'predicate 'arity 1 'english "the infinite product of $1 converges")
(def-predicate 'PROD-ABS-CONVERGES '(paa_)
  '(AND (IN paa_ (FUN NN CC)) (SERIES-CONVERGES (VNB-LAMBDA pak_ NN (magnitude (paa_ pak_))))))
(notation! 'PROD-ABS-CONVERGES 'kind 'predicate 'arity 1
           'english "the product of the factors 1 + $1(k) is absolutely convergent")
(def-predicate 'PROD-NORMAL-ON-COMPACTA '(pnu_ pnf_)
  '(FORALL pnn_ (IMPLIES (IN pnn_ NN) (IS-NORMALLY-CONVERGENT pnf_ (CC-EXHAUST pnu_ pnn_)))))
(notation! 'PROD-NORMAL-ON-COMPACTA 'kind 'predicate 'arity 2
           'english "the product of the functions 1 + $2(k) is normally convergent on the compact subsets of $1")
(def-functoid 'PROD-VALUE '(pvh_) '(IOTA pvl_ (AND (IN pvl_ CC) (PROD-CONVERGES-TO pvh_ pvl_))))
(notation! 'PROD-VALUE 'kind 'functoid 'arity 1 'english "the value of the infinite product of $1")
(def-functoid 'PROD-FUN '(pfu_ pff_) '(VNB-LAMBDA pfx_ pfu_ (PROD-VALUE (VNB-LAMBDA pfk_ NN (+ 1 ((pff_ pfk_) pfx_))))))
(notation! 'PROD-FUN 'kind 'functoid 'arity 2 'english "the function x |-> prod_k (1 + $2(k)(x)) on $1")
