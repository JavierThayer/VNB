;;; cx-vocab.scm -- THE BUNDLE OF SECTION 7.3.3 (Figure 9) OF ~/docs/jcs_strand_spaces.pdf: a concrete
;;; Otway-Rees strand space and bundle in which the initiator and the responder complete their strands and
;;; agree on A, B and M but not on the session key.  DEFINITIONS ONLY (four declare-instance! constants);
;;; the laws are in theorem-library/or-missing-guarantee.scm.  Agent SB-5, 2026-10-26.
;;; Destination: structure-library/or-missing-guarantee-instance.scm.  Library: strand.  Load window: after
;;; structure-library/otway-rees (SK-SPACE) and list-recursion (nn-not-a-list).
;;;
;;; TOKENS are the naturals (every subset of NN is a token set: nn-not-a-list, the user's decision of
;;; 2026-10-26).  Names A = 10, B = 11; texts Na = 20, Nb = 21, M = 22; keys KEYS = [30, 33]:
;;; K_AS = 30, K_BS = 31 (LTKEY(x) = x + 20 on the names [10, 11]), the session keys K = 32 and K' = 33.
;;; Every key is symmetric (KINV the identity).  The adversary knows no token (ADV-TOKENS = EMPTY-SET).
;;;
;;; THE EIGHT STRANDS (identifiers 1..8; 5..8 are the adversary's):
;;;   1 initiator A          < +M1, -M4' >
;;;   2 responder B          < -M1, +M2, -M3, +M4 >
;;;   3 server, key K        < -M2, +M3 >
;;;   4 server, key K'       < -M2, +M3' >
;;;   5 tee of M2            < -M2, +M2, +M2 >
;;;   6 flush of M4          < -M4 >
;;;   7 separation of M3'    < -M3', +M, +{Na K'}_KAS, +{Nb K'}_KBS >
;;;   8 concatenation        < -M, -{Na K'}_KAS, +M4' >
;;; with X_A = {Na M A B}_KAS, X_B = {Nb M A B}_KBS, M1 = M A B X_A, M2 = M A B X_A X_B,
;;; M3 = M {Na K}_KAS {Nb K}_KBS, M3' = the same with K', M4 = M {Na K}_KAS, M4' = M {Na K'}_KAS.
;;; THE TEN EDGES (node = [index, identifier]): [1,1]->[1,2] (M1), [2,2]->[1,5] (M2), [2,5]->[1,3],
;;; [3,5]->[1,4], [2,3]->[3,2] (M3), [4,2]->[1,6] (M4), [2,4]->[1,7] (M3'), [2,7]->[1,8] (M),
;;; [3,7]->[2,8] ({Na K'}_KAS), [3,8]->[2,1] (M4').  21 nodes, all in the bundle.
;;; Binders cx*_.

(define (cxv-lst . xs) `(LST (LIST ,@xs)))
(define (cxv-enc m k) `(ENCR ,m ,k))
(define cxv-xa (cxv-enc (cxv-lst 20 22 10 11) 30))
(define cxv-xb (cxv-enc (cxv-lst 21 22 10 11) 31))
(define cxv-m1 (cxv-lst 22 10 11 cxv-xa))
(define cxv-m2 (cxv-lst 22 10 11 cxv-xa cxv-xb))
(define (cxv-ya k) (cxv-enc (cxv-lst 20 k) 30))
(define (cxv-yb k) (cxv-enc (cxv-lst 21 k) 31))
(define (cxv-m3 k) (cxv-lst 22 (cxv-ya k) (cxv-yb k)))
(define cxv-m4 (cxv-lst 22 (cxv-ya 32)))
(define cxv-m4p (cxv-lst 22 (cxv-ya 33)))
(define (cxv-s m) `(LIST SENT ,m))
(define (cxv-r m) `(LIST RECEIVED ,m))
(define cxv-strands
  (list `(LIST ,(cxv-s cxv-m1) ,(cxv-r cxv-m4p))
        `(LIST ,(cxv-r cxv-m1) ,(cxv-s cxv-m2) ,(cxv-r (cxv-m3 32)) ,(cxv-s cxv-m4))
        `(LIST ,(cxv-r cxv-m2) ,(cxv-s (cxv-m3 32)))
        `(LIST ,(cxv-r cxv-m2) ,(cxv-s (cxv-m3 33)))
        `(LIST ,(cxv-r cxv-m2) ,(cxv-s cxv-m2) ,(cxv-s cxv-m2))
        `(LIST ,(cxv-r cxv-m4))
        `(LIST ,(cxv-r (cxv-m3 33)) ,(cxv-s 22) ,(cxv-s (cxv-ya 33)) ,(cxv-s (cxv-yb 33)))
        `(LIST ,(cxv-r 22) ,(cxv-r (cxv-ya 33)) ,(cxv-s cxv-m4p))))
(define cxv-edges
  '(((1 1) (1 2)) ((2 2) (1 5)) ((2 5) (1 3)) ((3 5) (1 4)) ((2 3) (3 2))
    ((4 2) (1 6)) ((2 4) (1 7)) ((2 7) (1 8)) ((3 7) (2 8)) ((3 8) (2 1))))
(define (cxv-node kv) `(LIST ,(car kv) ,(cadr kv)))
(define (cxv-or fs) (if (null? (cdr fs)) (car fs) `(OR ,(car fs) ,(cxv-or (cdr fs)))))

(declare-instance! 'CX-SP 'STRAND-SPACE 'cx-sp-def
  `(NN (INTERVAL 1 8) (INTERVAL 30 33)
       (VNB-LAMBDA cxi_ (INTERVAL 1 8) (NTH cxi_ (LIST ,@cxv-strands)))
       (VNB-LAMBDA cxk_ (INTERVAL 30 33) cxk_)))

(declare-instance! 'CX-ISP 'INFILTRATED-SPACE 'cx-isp-def
  '(CX-SP (INTERVAL 5 8) EMPTY-SET))

(declare-instance! 'CX-ORP 'SK-SPACE 'cx-orp-def
  '(CX-ISP (INTERVAL 10 11) (VNB-LAMBDA cxn_ (INTERVAL 10 11) (+ cxn_ 20))))

(declare-instance! 'CX-C 'BUNDLE 'cx-c-def
  `(CX-SP (NODES CX-SP)
          (SEP cxe_ (CARTESIAN (NODES CX-SP) (NODES CX-SP))
               ,(cxv-or (map (lambda (e) `(= cxe_ (LIST ,(cxv-node (car e)) ,(cxv-node (cadr e))))) cxv-edges)))))
