;;; gal-ch-vocab.scm -- vocabulary for the general Cayley-Hamilton theorem (GALOIS B6, 2026-10-26).
;;; DEFINITIONS ONLY.  Destination: structure-library/gal-ch-vocab.scm, library linear-algebra.
;;; Load window: after gal-op-vocab.scm and the matrix files (MATOF, ENTRY, MAT).

;;; The image of an m x n matrix under a map h, entrywise.
(def-functoid 'MAT-MAP '(gmm-h_ gmm-m_ gmm-n_ gmm-a_)
  '(MATOF gmm-m_ gmm-n_ (VNB-LAMBDA (LIST gmmi_ gmmj_) (CARTESIAN (INTERVAL 1 gmm-m_) (INTERVAL 1 gmm-n_))
                          (gmm-h_ (ENTRY gmm-a_ gmmi_ gmmj_)))))
(notation! 'MAT-MAP 'arity 4 'english "the matrix $4 with $1 applied to every entry")

;;; F[T]: the operators p(T), p in F[x], under pointwise addition and composition.
(def-functoid 'OP-OF '(gof-md_ gof-t_ gof-p_)
  '(VNB-LAMBDA gofw_ (VEC gof-md_) (POLY-OP gof-md_ gof-t_ gof-p_ gofw_)))
(notation! 'OP-OF 'arity 3 'english "the operator $3($2)")
(def-functoid 'OPS '(gos-md_ gos-t_)
  '(SEP gosf_ (FUN (VEC gos-md_) (VEC gos-md_))
     (FORSOME gosp_ (AND (IN gosp_ (CARR (POLY (SCAL gos-md_)))) (= gosf_ (OP-OF gos-md_ gos-t_ gosp_))))))
(notation! 'OPS 'arity 2 'english "the operators p($2), p a polynomial")
(def-functoid 'OP-ADD '(goa-md_ goa-t_)
  '(VNB-LAMBDA (LIST goaf_ goag_) (CARTESIAN (OPS goa-md_ goa-t_) (OPS goa-md_ goa-t_))
     (VNB-LAMBDA goaw_ (VEC goa-md_) ((VADD goa-md_) (goaf_ goaw_) (goag_ goaw_)))))
(def-functoid 'OP-MUL '(gom-md_ gom-t_)
  '(VNB-LAMBDA (LIST gomf_ gomg_) (CARTESIAN (OPS gom-md_ gom-t_) (OPS gom-md_ gom-t_))
     (VNB-LAMBDA gomw_ (VEC gom-md_) (gomf_ (gomg_ gomw_)))))
(def-functoid 'OP-NEG '(gon-md_ gon-t_)
  '(VNB-LAMBDA gonf_ (OPS gon-md_ gon-t_) (VNB-LAMBDA gonw_ (VEC gon-md_) ((VNEG gon-md_) (gonf_ gonw_)))))
(def-functoid 'OP-ZERO '(goz-md_) '(VNB-LAMBDA gozw_ (VEC goz-md_) (VZERO goz-md_)))
(def-functoid 'OP-ONE '(goo-md_) '(VNB-LAMBDA goow_ (VEC goo-md_) goow_))
(def-functoid 'OP-ALG '(gal-md_ gal-t_)
  '(LIST (OPS gal-md_ gal-t_) (OP-ADD gal-md_ gal-t_) (OP-MUL gal-md_ gal-t_) (OP-NEG gal-md_ gal-t_)
         (OP-ZERO gal-md_) (OP-ONE gal-md_)))
(notation! 'OP-ALG 'arity 2 'english "the ring F[$2] of the operators p($2)")
(def-functoid 'EV-OP '(gev-md_ gev-t_)
  '(VNB-LAMBDA gevp_ (CARR (POLY (SCAL gev-md_))) (OP-OF gev-md_ gev-t_ gevp_)))
(notation! 'EV-OP 'arity 2 'english "the evaluation p |-> p($2)")

;;; An n x n matrix P of maps VEC -> VEC acting on a column u of n vectors: (P u)_i = sum_k P_ik(u_k).
(def-functoid 'MAT-ACT '(gma-md_ gma-n_ gma-p_ gma-u_)
  '(MATOF gma-n_ 1 (VNB-LAMBDA (LIST gmai_ gmaj_) (CARTESIAN (INTERVAL 1 gma-n_) (INTERVAL 1 1))
     (FINSUM (MODULE-VECTOR-AG gma-md_)
             (VNB-LAMBDA gmak_ (INTERVAL 1 gma-n_) ((ENTRY gma-p_ gmai_ gmak_) (ENTRY gma-u_ gmak_ 1)))
             (INTERVAL 1 gma-n_)))))
(notation! 'MAT-ACT 'arity 4 'english "the matrix $3 of maps applied to the column $4")
