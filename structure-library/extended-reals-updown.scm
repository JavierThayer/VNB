;;; extinf-vocab.scm -- the two half-extended real lines and extended addition on each.
;;; DEFINITIONS ONLY.  Agent EXT-INF, 2026-10-26 (the user's decision of the same day: the
;;; semigroup properties of extended addition "clearly stated for both").
;;; DESTINATION: structure-library/extended-reals-updown.scm (new file), loaded right after
;;; structure-library/extended-reals (it needs RR-STAR's constants POS-INF / NEG-INF, the
;;; set vocabulary's SINGLETON and the arithmetic `+'; all load earlier).  Library: core.
;;;
;;;   RR-EXT-UP              (-inf, +inf] = RR u {POS-INF}
;;;   RR-EXT-DOWN            [-inf, +inf) = RR u {NEG-INF}
;;;   EPLUS-UP(x, y)         extended addition on (-inf, +inf]:
;;;                            POS-INF when either argument is POS-INF, else x + y
;;;   EPLUS-DOWN(x, y)       extended addition on [-inf, +inf):
;;;                            NEG-INF when either argument is NEG-INF, else x + y
;;;
;;; POS-INF + NEG-INF is NOT defined.  Neither operation is meant to be applied off its own
;;; line, and no theorem says anything about EPLUS-UP at NEG-INF or EPLUS-DOWN at POS-INF;
;;; every law is guarded by membership in the operation's own class.
;;;
;;; DEFINED, NOT AXIOMATISED (the EPLUS / ETIMES lesson of 2026-09-18).  Each operation is a
;;; def-functoid by cases through IF on the absorbing point; the classes are def-constants
;;; (a union with a singleton, as CC-HAT is).  Every law is a THEOREM:
;;; scratchpad/extinf/extinf-semigroups.scm (closure, associativity, commutativity, 0
;;; neutral, the infinity absorbing, real + real is the real sum, order compatibility),
;;; with the bridge `eplus-up-agrees-eplus': on [0, +inf] EPLUS-UP is the library's eplus.
;;;
;;; BINDERS: eux_ euy_ (EPLUS-UP), edx_ edy_ (EPLUS-DOWN).  None folds onto a class name, an
;;; accessor or a registered constant.

(def-constant 'RR-EXT-UP
  (list 'rr-ext-up-def
        '(== RR-EXT-UP (UNION RR (SINGLETON POS-INF)))))
(notation! 'RR-EXT-UP 'kind 'constant 'arity 0
           'english "the real line with +infinity adjoined, (-inf, +inf]")

(def-constant 'RR-EXT-DOWN
  (list 'rr-ext-down-def
        '(== RR-EXT-DOWN (UNION RR (SINGLETON NEG-INF)))))
(notation! 'RR-EXT-DOWN 'kind 'constant 'arity 0
           'english "the real line with -infinity adjoined, [-inf, +inf)")

(def-functoid 'EPLUS-UP '(eux_ euy_)
  '(IF (OR (= eux_ POS-INF) (= euy_ POS-INF))
       POS-INF
       (+ eux_ euy_)))
(notation! 'EPLUS-UP 'kind 'functoid 'arity 2
           'english "the extended sum of $1 and $2 in (-inf, +inf]")

(def-functoid 'EPLUS-DOWN '(edx_ edy_)
  '(IF (OR (= edx_ NEG-INF) (= edy_ NEG-INF))
       NEG-INF
       (+ edx_ edy_)))
(notation! 'EPLUS-DOWN 'kind 'functoid 'arity 2
           'english "the extended sum of $1 and $2 in [-inf, +inf)")
