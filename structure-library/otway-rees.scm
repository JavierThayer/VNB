;;; otway-rees.scm -- THE OTWAY-REES PROTOCOL ON THE USER'S STRAND MODEL (Thayer, Herzog, Guttman,
;;; ~/docs/jcs_strand_spaces.pdf, section 7.1, Definitions 7.1 and 7.3).
;;; DEFINITIONS ONLY; the laws are in theorem-library/otway-rees-laws.scm.  Agent SB-3, wave MAP-1026,
;;; 2026-10-26.  Destination: structure-library/otway-rees.scm.  Library: strand.  Load window: after
;;; structure-library/strand-adversary (INFILTRATED-SPACE) and structure-library/strand-ideals.
;;;
;;; THE SHARED-KEY SPACE (the paper's refinement of A for section 7): a declare-structure SK-SPACE with
;;;     substructure SK-INF    an infiltrated strand space
;;;     carrier     SK-NAMES   the principals' names (the paper's T_name)
;;;     op          LTKEY      SK-NAMES -> KEYS, the paper's K(A) = K_AS, the key A shares with the server
;;;     laws        names are tokens, names are not keys, LTKEY injective, and every K_AS SYMMETRIC:
;;;                 KINV(K_AS) = K_AS (the paper: "K_AS = K_AS^-1").
;;; (Accessors SK-NAMES, LTKEY, SK-INF: NAMES / PUBKEY / PK-INF are the NSL space's, and an accessor names
;;; one slot everywhere.)
;;;
;;; TEXTS.  The paper's variables N, M range over "T minus T_name", T its texts: on this model the tokens that
;;; are neither names nor keys (IS-OR-TEXT).
;;;
;;; THE THREE ROLES (Definition 7.1), on the n-ary model: the paper's concatenation "M A B X" is the list
;;; message LST([M, A, B, X]); {X}_K is ENCR(X, K); K_XS is LTKEY(X).
;;;   IS-OR-INIT(p, s, A, B, N, M, K)          s = < +M A B {N M A B}_KAS,  -M {N K}_KAS >
;;;   IS-OR-RESP(p, s, A, B, N, M, K, H, H2)   s = < -M A B H, +M A B H {N M A B}_KBS, -M H2 {N K}_KBS, +M H2 >,
;;;                                             defined when N is not a subterm of H and N /= M (the paper:
;;;                                             "N originates on each strand in Resp", which needs both)
;;;   IS-OR-SERV(p, s, A, B, Na, Nb, M, K)     s = < -M A B {Na M A B}_KAS {Nb M A B}_KBS,
;;;                                                  +M {Na K}_KAS {Nb K}_KBS >,
;;;                                             defined when K is not known to the adversary, is no K_XS,
;;;                                             and K = K^-1
;;; In Init the key K is any key (the paper's "variables K range over K").  H, H2 are messages.
;;; IS-OR-SPACE(p) (Definition 7.3): every strand is the adversary's, an initiator's, a responder's or a
;;; server's.  The server identity S0 of the paper plays no role in any proof and is not modelled.
;;; Binders or*_.

(declare-structure SK-SPACE
  (instance-var s)
  (substructure SK-INF INFILTRATED-SPACE)
  (carriers SK-NAMES)
  (op LTKEY SK-NAMES (KEYS (ISPACE SK-INF)))
  (law (FORALL orx_ (IMPLIES (IN orx_ (SK-NAMES s)) (IN orx_ (TOKENS (ISPACE (SK-INF s)))))))
  (law (FORALL orx_ (IMPLIES (IN orx_ (SK-NAMES s)) (NOT (IN orx_ (KEYS (ISPACE (SK-INF s))))))))
  (law (FORALL orx_ (FORALL ory_ (IMPLIES (IN orx_ (SK-NAMES s)) (IMPLIES (IN ory_ (SK-NAMES s))
         (IMPLIES (= ((LTKEY s) orx_) ((LTKEY s) ory_)) (= orx_ ory_)))))))
  (law (FORALL orx_ (IMPLIES (IN orx_ (SK-NAMES s))
         (= ((KINV (ISPACE (SK-INF s))) ((LTKEY s) orx_)) ((LTKEY s) orx_))))))
(notation! 'IS-SK-SPACE 'noun "shared-key strand space" 'article "a")
(notation! 'IS-HOM-SK-SPACE 'kind 'predicate 'arity 3
           'english "$3 is a morphism of shared-key strand spaces from $1 to $2")

(def-predicate 'IS-OR-TEXT '(ortp_ ortx_)
  '(AND (IN ortx_ (TOKENS (ISPACE (SK-INF ortp_))))
   (AND (NOT (IN ortx_ (SK-NAMES ortp_)))
        (NOT (IN ortx_ (KEYS (ISPACE (SK-INF ortp_))))))))
(notation! 'IS-OR-TEXT 'kind 'predicate 'arity 2 'english "$2 is a text (neither a name nor a key) of $1")

(def-predicate 'IS-OR-INIT '(orip_ oris_ oria_ orib_ orin_ orim_ orik_)
  '(AND (IN oria_ (SK-NAMES orip_))
   (AND (IN orib_ (SK-NAMES orip_))
   (AND (IS-OR-TEXT orip_ orin_)
   (AND (IS-OR-TEXT orip_ orim_)
   (AND (IN orik_ (KEYS (ISPACE (SK-INF orip_))))
        (= oris_ (LIST (LIST SENT (LST (LIST orim_ oria_ orib_ (ENCR (LST (LIST orin_ orim_ oria_ orib_)) ((LTKEY orip_) oria_)))))
                       (LIST RECEIVED (LST (LIST orim_ (ENCR (LST (LIST orin_ orik_)) ((LTKEY orip_) oria_)))))))))))))
(notation! 'IS-OR-INIT 'kind 'predicate 'arity 7
           'english "$2 is an Otway-Rees initiator's strand of $1 for $3, $4, $5, $6, $7")

(def-predicate 'IS-OR-RESP '(orrp_ orrs_ orra_ orrb_ orrn_ orrm_ orrk_ orrh_ orrg_)
  '(AND (IN orra_ (SK-NAMES orrp_))
   (AND (IN orrb_ (SK-NAMES orrp_))
   (AND (IS-OR-TEXT orrp_ orrn_)
   (AND (IS-OR-TEXT orrp_ orrm_)
   (AND (IN orrk_ (KEYS (ISPACE (SK-INF orrp_))))
   (AND (IN orrh_ (MSG-SET (TOKENS (ISPACE (SK-INF orrp_))) (KEYS (ISPACE (SK-INF orrp_)))))
   (AND (IN orrg_ (MSG-SET (TOKENS (ISPACE (SK-INF orrp_))) (KEYS (ISPACE (SK-INF orrp_)))))
   (AND (NOT (= orrn_ orrm_))
   (AND (NOT (IS-SUBTERM (TOKENS (ISPACE (SK-INF orrp_))) (KEYS (ISPACE (SK-INF orrp_))) orrn_ orrh_))
        (= orrs_ (LIST (LIST RECEIVED (LST (LIST orrm_ orra_ orrb_ orrh_)))
                       (LIST SENT (LST (LIST orrm_ orra_ orrb_ orrh_ (ENCR (LST (LIST orrn_ orrm_ orra_ orrb_)) ((LTKEY orrp_) orrb_)))))
                       (LIST RECEIVED (LST (LIST orrm_ orrg_ (ENCR (LST (LIST orrn_ orrk_)) ((LTKEY orrp_) orrb_)))))
                       (LIST SENT (LST (LIST orrm_ orrg_)))))))))))))))
(notation! 'IS-OR-RESP 'kind 'predicate 'arity 9
           'english "$2 is an Otway-Rees responder's strand of $1 for $3, $4, $5, $6, $7, $8, $9")

(def-predicate 'IS-OR-SERV '(orsp_ orss_ orsa_ orsb_ orsn_ orso_ orsm_ orsk_)
  '(AND (IN orsa_ (SK-NAMES orsp_))
   (AND (IN orsb_ (SK-NAMES orsp_))
   (AND (IS-OR-TEXT orsp_ orsn_)
   (AND (IS-OR-TEXT orsp_ orso_)
   (AND (IS-OR-TEXT orsp_ orsm_)
   (AND (IN orsk_ (KEYS (ISPACE (SK-INF orsp_))))
   (AND (NOT (IN orsk_ (ADV-TOKENS (SK-INF orsp_))))
   (AND (FORALL orsx_ (IMPLIES (IN orsx_ (SK-NAMES orsp_)) (NOT (= orsk_ ((LTKEY orsp_) orsx_)))))
   (AND (= ((KINV (ISPACE (SK-INF orsp_))) orsk_) orsk_)
        (= orss_ (LIST (LIST RECEIVED (LST (LIST orsm_ orsa_ orsb_
                                                 (ENCR (LST (LIST orsn_ orsm_ orsa_ orsb_)) ((LTKEY orsp_) orsa_))
                                                 (ENCR (LST (LIST orso_ orsm_ orsa_ orsb_)) ((LTKEY orsp_) orsb_)))))
                       (LIST SENT (LST (LIST orsm_ (ENCR (LST (LIST orsn_ orsk_)) ((LTKEY orsp_) orsa_))
                                                   (ENCR (LST (LIST orso_ orsk_)) ((LTKEY orsp_) orsb_)))))))))))))))))
(notation! 'IS-OR-SERV 'kind 'predicate 'arity 8
           'english "$2 is an Otway-Rees server's strand of $1 for $3, $4, $5, $6, $7, $8")

(def-predicate 'IS-OR-SPACE '(orqp_)
  '(AND (IS-SK-SPACE orqp_)
        (FORALL orqi_ (IMPLIES (IN orqi_ (IDS (ISPACE (SK-INF orqp_))))
          (OR (IN orqi_ (ADV-IDS (SK-INF orqp_)))
          (OR (FORSOME orqa_ (FORSOME orqb_ (FORSOME orqn_ (FORSOME orqm_ (FORSOME orqk_
                (IS-OR-INIT orqp_ ((STRAND-MAP (ISPACE (SK-INF orqp_))) orqi_) orqa_ orqb_ orqn_ orqm_ orqk_))))))
          (OR (FORSOME orqa_ (FORSOME orqb_ (FORSOME orqn_ (FORSOME orqm_ (FORSOME orqk_ (FORSOME orqh_ (FORSOME orqg_
                (IS-OR-RESP orqp_ ((STRAND-MAP (ISPACE (SK-INF orqp_))) orqi_) orqa_ orqb_ orqn_ orqm_ orqk_ orqh_ orqg_))))))))
              (FORSOME orqa_ (FORSOME orqb_ (FORSOME orqn_ (FORSOME orqo_ (FORSOME orqm_ (FORSOME orqk_
                (IS-OR-SERV orqp_ ((STRAND-MAP (ISPACE (SK-INF orqp_))) orqi_) orqa_ orqb_ orqn_ orqo_ orqm_ orqk_))))))))))))))
(notation! 'IS-OR-SPACE 'kind 'predicate 'arity 1 'english "$1 is an Otway-Rees strand space")
