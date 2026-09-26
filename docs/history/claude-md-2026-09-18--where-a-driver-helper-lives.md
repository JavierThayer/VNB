<!-- VERBATIM copy of a section of CLAUDE.md as it stood on 2026-09-18, moved here when
CLAUDE.md was trimmed to its operational rules.  Nothing was edited. -->

## Where a driver helper lives

**Every proof-driving Scheme procedure is either in `driver-kit.scm` -- loaded before any
proof -- or is local to the file that defines it.** There is no third place.

`load.scm` enforces the second half: once `driver-kit` has loaded, each `theorem-library/`
and `calculus/` file is loaded into a fresh `extend-top-level-environment`. A driver's
top-level `define`s stay in its own frame; its `set!` of `*ps*` still reaches the real
binding, and it still sees every tactic, every macro (`bc*`) and everything `driver-kit`
defines. So a stray `(define BC '(succ p))` now breaks only its own file.

Before this, both halves were false and nobody had said so: `proof-leaves` and `any-pred`
were defined *only* inside `theorem-library/nn-least-element.scm` -- a proof script -- and
used by `interactive.scm`, `macetes.scm` and eighteen drivers; `deriv-constant-proof.scm`
exported a thirteen-procedure `dc-` kit to nine drivers, under a comment calling it
"file-local". It worked only because Scheme resolves free variables at call time.

If exactly one file needs a helper, define it there with the file's prefix. If two do, it
belongs in `driver-kit.scm`.

