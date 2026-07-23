# calculus/ probes stranded by the accessor rename

Archived 2026-07-23.  These thirteen scripts were written before the structure
accessors were renamed -- `A` -> `CARR`, `X` -> `CARR`/`PTS`, `D` -> `DIST`,
`ID`/`E` -> `IDEN` -- and they still use the OLD single-letter names in live
code: `(X s)`, `(A s)`, `(D S)`.  No accessor is a single letter any more (the
current set is ACT ADD CARR DIST FNRM IDEN IDL INV MUL NEG NRM ONE OPENS OPR PTS
RECIP REDUCE VADD VEC VNEG VNRM VZERO ZERO), so **none of these scripts runs as
written.**

Nothing detected this for as long as it was true: `calculus/` is outside
`load.scm` apart from `calculus/finite-ball-subcover-proof` (which is clean), so
no load, no audit and no test ever touched them.  The rename swept the loaded
tree and left this directory behind.

They are kept, not deleted, because several are cited by name in the glosses and
file comments of loaded files as the place a PSS entry was machine-proven --
`gauge-proof` for `euclidean-ring.scm`, `prop-3-15-proof` for
`metric-open-sets.scm`, `block-family-rederive` and
`cauchy-subseq-via-combinatorial` for `cauchy-subsequence.scm`.  Those pointers
now name this directory.  Note what that means: the cited evidence exists but
cannot currently be re-run, so those "MACHINE-PROVEN in ..." claims rest on a
past run, not a reproducible one.

To revive one, rewrite its accessor applications and re-run it:

    ./prover archive/calculus-pre-rename/<file>.scm

The files:

    block-family-rederive          probe-core
    cauchy-subseq-via-combinatorial probe-mach-cond
    cauchy-subseq-via-wbc          probe-rewrite
    gauge-proof                    prop-3-14-proof
    props-3-14-3-15                prop-3-15-proof
    scout-eps-cauchy-record        totally-bounded-cauchy-subseq
    uniqueness-of-limits

`stress-tests/compact-tb-stress.scm` has the same defect (one site) and was left
in place -- it is not a `calculus/` probe.
