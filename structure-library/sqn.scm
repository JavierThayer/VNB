;;; sqn.scm -- SQN(a): the sequences in a, i.e. FUN(NN, a).
;;;
;;; A NOTATION, not a construction.  `SQN(a)' unfolds to `FUN(NN, a)' and to
;;; nothing else; it exists because "sequence in a" is what the mathematics says
;;; and `f in FUN(NN, PTS(s))' is what the library writes, forty-odd times
;;; across the metric and analysis files.  The user's request, 2026-08-19:
;;; "we should have a constructor like tuples(a) calling it sequence(a).  This
;;; is non-other than FUN(nn,a)."
;;;
;;; WHY `SQN' AND NOT `SEQUENCE' OR `SEQ'.  `seq' is already a BINDER NAME in
;;; the library (`forall([seq in fun(nn, product(...))], ...)',
;;; coordinatewise-diagonal-subseq), and both the VNB reader and MIT Scheme fold
;;; symbols to lowercase -- so a constant `SEQ' and a bound variable `seq' are
;;; ONE name, which is precisely what `constant-binder-audit' exists to warn
;;; about.  `SEQUENCE' is free but collides with nothing and reads long inside a
;;; typing (`f in sequence(pts(s))').  `SQN' is the user's own second suggestion
;;; and is what this file installs.  `SUBSEQ' (an existing head) is a different
;;; word and does not fold together with it.
;;;
;;; THE UNFOLD IS NOT ENOUGH ON ITS OWN, and this is the trap CLAUDE.md records
;;; for every `def-functoid': it installs a rewrite MACETE, not a theorem, so
;;; `mac' unfolds SQN in a GOAL and `mac-h' CANNOT unfold it in an ASSUMPTION --
;;; it warns "unknown theorem/macete" and the driver continues with the
;;; hypothesis untouched.  Every use of a sequence reads `f in SQN(a)' out of
;;; the context, so the membership IFF is stated here beside the definition and
;;; wrapped `definitional': it is the functoid unfold and nothing else, i.e.
;;; exactly the IFF `def-predicate' would have generated had SQN been a
;;; predicate.  Same treatment and same reasoning as `span-membership'
;;; (mod-seq.scm) and `principal-ideal-membership' (ideal.scm).

(def-functoid 'SQN '(a) '(FUN NN a))

(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'sqn-membership
    '(FORALL a (FORALL f_ (IFF (IN f_ (SQN a)) (IN f_ (FUN NN a)))))))

;;; Sethood, from `fun-set-iff' (fun(a,b) in set iff a in set and b in set) and
;;; `nn-is-set'.  Stated rather than left to be re-derived: a sequence space is
;;; fed to SEP and to the finite-set machinery, both of which are gated on
;;; sethood.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'sqn-sethood
    '(FORALL a (IMPLIES (IN a SET) (IN (SQN a) SET)))))

;;; NOT named-only: `sqn-membership' is a LIVE macete, fired by name at 25 call
;;; sites (`(mac-h 'sqn-membership k)'), and that is what the library wants.
;;;
;;; A `declare-named-only!' call stood here from 2026-08 to 2026-09-20 and was
;;; DEAD: it came AFTER the `theory-add-axiom!' above, and the named-only list
;;; is read by `theorem->elementary-macete' while the macete is being built, so
;;; the declaration could not reach it.  The macete has therefore been live all
;;; along, with no trouble -- as the shape predicts: unlike `app-graph', whose
;;; left side `(f x)' is a bare application with a SCHEMA head and so matches
;;; every application in every goal, this one's left side is `(IN f_ (SQN a))',
;;; headed by IN with the constant SQN, so it fires only on an SQN membership.
;;; `declare-named-only!' now warns when it is called too late.

(notation! 'SQN 'kind 'functoid 'arity 1
           'english "the sequences in $1"
           'noun "sequence in $1"
           'tex "$1^{\\mathbb{N}}")
