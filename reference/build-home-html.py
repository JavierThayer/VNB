#!/usr/bin/env python3
"""Build the VNB browser landing page (home.html).

A front door rendered in HTML.  Two kinds of link:
  * Reference links go to other HTML pages (reference.html, structure-graph.html)
    -- ordinary in-browser navigation.
  * Workbench links poke Emacs: each is a fire-and-forget fetch to a tiny
    localhost listener the launcher runs (http://127.0.0.1:PORT/do?fn=NAME).
    Emacs dispatches NAME through a fixed whitelist and raises its frame, so
    the actual proving (Focus workspace, REPL, scratch) happens in Emacs as
    before -- the browser is only the lobby.

Usage:  python3 build-home-html.py [PORT]      (PORT default 8973)
The launcher passes the port it actually listens on, so the two stay in sync.
"""
import os, sys, html

HERE = os.path.dirname(os.path.abspath(__file__))
OUT  = os.path.join(HERE, "home.html")
PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8973

def esc(s): return html.escape(s, quote=True)

# Reference reading -- all in the browser.  (label, href, blurb).  The #ANCHORS
# are reference.html's per-doc sections (build-reference-html.py: secid = the
# .md filename).  These cover what used to be the Emacs "Show X" home items.
REF_LINKS = [
    ("Library",           "reference.html",                  "everything cross-linked — start here"),
    ("Structures",        "reference.html#STRUCTURE-INDEX",  "every structure: slots, laws, views"),
    ("Theorems & axioms", "reference.html#THEOREMS",         "the full installed catalog"),
    ("Definitions",       "reference.html#DEFINITIONS",      "term & predicate definitions"),
    ("Proof Support Set", "reference.html#PSS",              "theorems excused from the VNB test, accepted on a warrant"),
    ("Fingerprint Index", "reference.html#FINGERPRINT-INDEX","results bucketed by conclusion skeleton"),
    ("Tactics",           "reference.html#TACTICS",          "interactive proof commands, each with a one-line gloss"),
    ("Structure Graph",   "structure-graph.html",            "refines & view-as relations, clickable"),
]
# Workbench: (heading, [(label, fn-name, blurb), ...]).  Emacs is ONLY for work
# the user actually performs -- starting/continuing proofs, scratch, building.
# Each fn-name MUST have a matching entry in vnb--home-actions (vnb-launch.el);
# keep the two in sync by hand.  No "Open Workspace": the browser IS the home
# page, so there is no separate Emacs landing page to bounce to.
WORKBENCH = [
    ("Prove", [
        ("Start Proof",    "start-proof",    "edit the goal in a buffer, then begin in the Focus workspace"),
        ("Continue Proof", "continue-proof", "return to the proof in progress (Focus workspace)"),
        ("Scratch",        "scratch",        "Lisp-interaction sheet: C-j sends a sexp/region to the prover"),
    ]),
    ("Build", [
        ("Build Formula",  "build-formula",  "parse and validate a formula"),
        ("Build Structure","build-structure","define a new structure (saved to file)"),
        ("Calculator",     "calculator",     "work out an arithmetic expression"),
    ]),
    ("Session", [
        ("Examples",     "examples",     "step through worked example proofs"),
        ("Save Session", "save-session", "this session's proofs as one re-loadable script"),
    ]),
]

# A small, self-contained illustration (no external assets, no web fonts): a
# friendly bubble-diagram echoing the real structure graph -- richer structures
# grow out of plainer ones.  Decorative; the live graph is structure-graph.html.
HERO_SVG = """
<svg class="hero-art" viewBox="0 0 640 230" xmlns="http://www.w3.org/2000/svg"
     role="img" aria-label="A graph of mathematical structures growing out of one another: set, group, ring, field, metric space, Euclidean ring.">
  <defs>
    <marker id="ar" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
      <path d="M0,0 L10,5 L0,10 z" fill="#9bb6d4"/>
    </marker>
  </defs>
  <g fill="none" stroke="#9bb6d4" stroke-width="2" marker-end="url(#ar)">
    <path d="M120,115 C175,75 195,70 235,62"/>
    <path d="M120,115 C185,150 210,165 250,178"/>
    <path d="M300,62 C345,72 360,90 388,108"/>
    <path d="M300,178 C350,168 362,150 388,122"/>
    <path d="M470,108 C510,80 520,72 548,64"/>
  </g>
  <g font-family="Georgia, serif" font-size="15" text-anchor="middle">
    <g><ellipse cx="80"  cy="115" rx="48" ry="30" fill="#eaf2fb" stroke="#7fa6cf"/><text x="80"  y="120" fill="#2a4a6a">set</text></g>
    <g><ellipse cx="268" cy="62"  rx="52" ry="30" fill="#e7f0ea" stroke="#86b08f"/><text x="268" y="67"  fill="#34603f">group</text></g>
    <g><ellipse cx="268" cy="178" rx="78" ry="31" fill="#f3ecf6" stroke="#a98cbf"/><text x="268" y="183" fill="#5a3f72">metric space</text></g>
    <g><ellipse cx="430" cy="115" rx="48" ry="30" fill="#e7f0ea" stroke="#86b08f"/><text x="430" y="120" fill="#34603f">ring</text></g>
    <g><ellipse cx="580" cy="62"  rx="50" ry="30" fill="#fbf2e6" stroke="#d59a3c"/><text x="580" y="67"  fill="#8a5a12">field</text></g>
    <g><ellipse cx="560" cy="170" rx="74" ry="31" fill="#fbf2e6" stroke="#d59a3c"/><text x="560" y="175" fill="#8a5a12">Euclidean ring</text></g>
  </g>
  <g fill="none" stroke="#9bb6d4" stroke-width="2" marker-end="url(#ar)">
    <path d="M430,145 C475,165 495,168 520,170"/>
  </g>
</svg>
"""

# What VNB is -- faithful to docs/ch-intro.tex (paraphrased, no new claims).
INTRO = """
<section class="intro">
  <p><b>Vienbi</b> (written <b>VNB</b>) is an <b>interactive proof assistant</b> &mdash;
  a program you do mathematics <em>with</em>. You state a theorem and build its proof a
  step at a time; the machine checks every step against a small, auditable logical
  kernel, so a finished proof is correct <em>by construction</em>, not by trust.</p>
  <p>Its foundation is a first-order set theory in the style of von&nbsp;Neumann&ndash;Bernays:
  one universe of <em>classes</em>, with membership&nbsp;(&isin;) the only primitive notion.
  But you rarely touch that bedrock &mdash; numbers, functions, and ordinals are built in as
  primitives governed by ordinary axioms, so a proof reads the way mathematics is actually
  written, not as a tower of encodings.</p>
  <p>It is also a small experiment: a rigorous proof system built largely by an AI, with
  mathematical direction from F.&nbsp;J.&nbsp;Thayer.</p>
</section>
"""

# How the pieces fit + a reassuring word for the Emacs-wary.
FITS = """
<h2>How it fits together</h2>
<div class="fits">
  <div class="part"><h3>The engine</h3>
    <p>An MIT&nbsp;Scheme program: the logical kernel, the library of structures and
    theorems, and the tactics you steer a proof with. The part that does the checking.</p></div>
  <div class="part"><h3>This page</h3>
    <p>Where you <em>read</em>: browse the library, the catalog of theorems, and the
    clickable structure graph. No setup &mdash; just links in your browser.</p></div>
  <div class="part"><h3>Emacs</h3>
    <p>Where you <em>work</em>: starting or continuing a proof opens an Emacs buffer. The
    launcher configures it for you; it&rsquo;s the worktable where steps get typed.</p></div>
</div>
<p class="reassure"><b>New to Emacs? You don&rsquo;t need to learn it.</b> The launcher sets
everything up, and the buttons below open the right window on their own. In practice you type
your goal and press a single chord (<code>C-c&nbsp;C-c</code>) to send it to the prover. Think
of Emacs here as the table you work at, not a thing to study &mdash; the mathematics is the point.</p>
"""

CSS = """
 body { font-family: Helvetica, Arial, sans-serif; color:#1a2a3a;
        background:#eef3f9; margin:0; padding:2.4rem 1rem 3rem; }
 main { max-width:46rem; margin:0 auto; }
 .hero { text-align:center; margin:0 auto 1.2rem; }
 .hero-art { width:100%; max-width:30rem; height:auto; display:block; margin:0 auto .3rem; }
 .wordmark { font-family:"Palatino Linotype","Book Antiqua",Palatino,"Iowan Old Style",
             "Hoefler Text",Georgia,"Times New Roman",serif;
             font-size:4.2rem; line-height:1; font-weight:600; letter-spacing:.01em;
             margin:.1rem 0 0;
             background:linear-gradient(95deg,#2a4a6a 0%,#3f7fb0 55%,#b06a00 100%);
             -webkit-background-clip:text; background-clip:text; color:transparent; }
 .tagline { color:#557; font-size:1.05rem; margin:.25rem 0 0; }
 .tagline b { color:#2a4a6a; letter-spacing:.04em; }
 h1 { color:#2a4a6a; font-size:1.6rem; margin:.2rem 0; }
 .sub { color:#667; margin:.2rem 0 2rem; }
 h2 { color:#365b7d; font-size:1.05rem; margin:1.8rem 0 .6rem;
      border-bottom:2px solid #dde6f0; padding-bottom:.2rem; }
 .intro { background:#fff; border:1px solid #dde6f0; border-radius:12px;
          padding:1rem 1.3rem; margin:1.3rem 0; line-height:1.55; color:#243446; }
 .intro p { margin:.5rem 0; }
 .fits { display:grid; grid-template-columns:repeat(auto-fit,minmax(12.5rem,1fr));
         gap:.7rem; margin:.6rem 0; }
 .fits .part { background:#fff; border:1px solid #dde6f0; border-radius:10px;
               padding:.8rem 1rem; }
 .fits .part h3 { margin:.1rem 0 .3rem; color:#2a4a6a; font-size:1rem; }
 .fits .part p { margin:0; color:#556; font-size:.92rem; line-height:1.45; }
 .reassure { background:#fdf6ec; border:1px solid #f0e0c4; border-left:4px solid #d59a3c;
             border-radius:8px; padding:.8rem 1.1rem; margin:1rem 0 1.4rem;
             color:#5a4a30; font-size:.95rem; line-height:1.5; }
 .card { display:block; background:#fff; border:1px solid #dde6f0;
         border-radius:10px; padding:.8rem 1rem; margin:.5rem 0;
         text-decoration:none; color:inherit; transition:box-shadow .12s; }
 .card:hover { box-shadow:0 2px 10px rgba(40,80,140,.15); border-color:#bcd0e8; }
 .card .t { font-weight:600; color:#2a4a6a; }
 .card .b { color:#667; font-size:.9rem; margin-top:.1rem; }
 .emacs .t::after { content:" \\2192 Emacs"; color:#b06a00; font-weight:400;
                    font-size:.82rem; }
 #flash { position:fixed; top:1rem; right:1rem; background:#2a4a6a; color:#fff;
          padding:.5rem .9rem; border-radius:6px; opacity:0; transition:opacity .2s;
          font-size:.9rem; }
 #flash.show { opacity:.95; }
 .classify { background:#fff; border:1px solid #dde6f0; border-radius:10px;
             padding:.4rem 1.1rem 1rem; margin:1.4rem 0 1rem; }
 .classify dt { font-weight:600; color:#2a4a6a; margin-top:.7rem; }
 .classify dd { margin:.15rem 0 0; color:#445; font-size:.92rem; }
 .classify .note { color:#556; font-size:.9rem; margin-top:.9rem;
                   border-top:1px solid #eef2f7; padding-top:.7rem; }
 .classify summary { cursor:pointer; color:#365b7d; font-weight:600;
                     font-size:1.05rem; padding:.6rem 0 .2rem; }
"""

JS = f"""
 const PORT = {PORT};
 function flash(msg) {{
   const f = document.getElementById('flash');
   f.textContent = msg; f.classList.add('show');
   setTimeout(() => f.classList.remove('show'), 1400);
 }}
 function poke(ev, fn, label) {{
   ev.preventDefault();
   fetch('http://127.0.0.1:' + PORT + '/do?fn=' + encodeURIComponent(fn),
         {{mode:'no-cors'}})
     .then(() => flash('\\u2192 ' + label + ' (see Emacs)'))
     .catch(() => flash('Emacs listener not reachable — start it from the launcher'));
 }}
"""

def ref_card(label, href, blurb):
    return (f'<a class="card" href="{esc(href)}">'
            f'<div class="t">{esc(label)}</div>'
            f'<div class="b">{esc(blurb)}</div></a>')

def emacs_card(label, fn, blurb):
    return (f'<a class="card emacs" href="#" '
            f'onclick="poke(event, \'{esc(fn)}\', \'{esc(label)}\')">'
            f'<div class="t">{esc(label)}</div>'
            f'<div class="b">{esc(blurb)}</div></a>')

# Documents the result taxonomy.  Provenance (why we hold it true) is ONE axis;
# whether the engine may fire it as a rewrite is a SEPARATE, orthogonal axis.
# Collapsed by default so the landing page leads with welcome, not taxonomy.
CLASSIFY = """
<details class="classify">
<summary>How results are classified</summary>
<dl>
  <dt>Axiom</dt>
  <dd>A primitive of VNB. The base we build on &mdash; small and essentially fixed.</dd>
  <dt>Definition</dt>
  <dd>True by construction (a defining equation, or an unfolding of one). <em>Not a
      theorem</em>, so it is never proved and is <em>not</em> a Proof Support Set
      member &mdash; but it still <strong>fires as a rewrite</strong> in proofs.</dd>
  <dt>Theorem</dt>
  <dd>Carries a machine proof, re-certified by the VNB test.</dd>
  <dt>Proof Support Set (PSS)</dt>
  <dd>A <em>theorem we trust on a warrant, without a machine proof</em> &mdash; excused
      from the VNB test. Each entry carries credentials: a plain statement plus why we
      accept it.</dd>
</dl>
<p class="note"><strong>Firing is a separate matter.</strong> Whether the prover may apply
a result as a rewrite is independent of this classification: axioms, definitions, theorems,
and PSS members can all be rewrite rules. A definition keeps that right even though it is
not a PSS member.</p>
</details>
"""

def build():
    refs = "".join(ref_card(*r) for r in REF_LINKS)
    work_sections = []
    n_work = 0
    for heading, items in WORKBENCH:
        cards = "".join(emacs_card(*e) for e in items)
        n_work += len(items)
        work_sections.append(
            f'<h2>{esc(heading)} <span class="sub" style="font-size:.85rem">'
            f'(opens in Emacs)</span></h2>\n{cards}')
    works = "\n".join(work_sections)
    doc = f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Vienbi — VNB Math Assistant</title>
<style>{CSS}</style></head><body>
<div id="flash"></div>
<main>
<header class="hero">
{HERO_SVG}
<div class="wordmark">Vienbi</div>
<p class="tagline"><b>VNB</b> &middot; the von Neumann&ndash;Bernays Math Assistant</p>
</header>
{INTRO}
{FITS}
<h2>Reference <span class="sub" style="font-size:.85rem">(reads in the browser)</span></h2>
{refs}
{works}
{CLASSIFY}
</main>
<script>{JS}</script>
</body></html>
"""
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(doc)
    print(f"wrote {OUT}  (port {PORT}, {len(REF_LINKS)} reference + {n_work} workbench links)")

if __name__ == "__main__":
    build()
