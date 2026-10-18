#!/usr/bin/env python3
"""Build a self-contained, clickable + FILTERABLE structure-graph.html.

The graph overlays two relations (solid = refines, dashed = view-as) over a
growing set of structures, and crowds badly at scale -- the view-as edges into
hub nodes (abelian-group) cross everything, and concrete number-system
instances pad the node count.  So this page is LAYERED:

    [x] refines   [ ] view-as   [ ] instances     focus: [______]

Each checkbox combination is rendered as its OWN `dot -Tsvg` layout at build
time (8 combos), so toggling a layer REDRAWS the graph (true re-layout) rather
than just hiding edges on a fixed layout -- the default refines-only view lays
out as a clean tree.  A focus box dims everything outside one structure's
immediate neighborhood.  No runtime graph engine: just pre-rendered SVGs + a
few lines of vanilla JS swapping which one is visible.  Pure stdlib.

Pipeline: parse structure-graph.dot into (preamble, node lines, refines edge
lines, view-as edge lines) -> for each layer combo, assemble a filtered dot and
render it -> inline all combos -> emit the toggles, the focus box, and the
per-structure reference section (slots / views out / refines).

Regenerate after a library change:
    # 1. rewrite the .dot from the prover REPL:  (structure-graph-dot-file)
    # 2. python3 reference/build-graph-html.py
Open reference/structure-graph.html in any web browser (double-click).
"""
import os, re, html, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOT  = os.path.join(HERE, "structure-graph.dot")
OUT  = os.path.join(HERE, "structure-graph.html")

# A node is a concrete INSTANCE (a number-system model, hidden by default)
# when its name starts with a number-system token: zz/qq/rr/cc/nn (incl. the
# rr-pos-star sup).  Everything else is an abstract structure.  No abstract structure
# name begins with a doubled number letter, so this is unambiguous.
INSTANCE_RE = re.compile(r'(zz|qq|rr|cc|nn)([-+]|$)')

def esc(s): return html.escape(s, quote=True)

def is_instance(name): return bool(INSTANCE_RE.match(name))

# ---- parse the .dot two ways: structured (for the reference section) and
#      line-grouped (for re-assembling filtered dots, losslessly) ----

def parse_dot(text):
    nodes = {}   # name -> slots-string
    views = []   # (src, tgt, label, fullname, mapping)
    refines = [] # (child, parent)
    bridges = [] # (src, tgt, functoid-label)
    for line in text.splitlines():
        m = re.match(r'\s*"([^"]+)"\s+\[tooltip="([^"]*)",\s*URL=', line)
        if m:
            name, tip = m.group(1), m.group(2)
            slots = tip.split("slots", 1)[1].strip() if "slots" in tip else ""
            nodes[name] = slots
            continue
        m = re.match(r'\s*"([^"]+)"\s*->\s*"([^"]+)"\s+\[style=dotted.*?label="([^"]*)"', line)
        if m:
            bridges.append((m.group(1), m.group(2), m.group(3)))
            continue
        m = re.match(r'\s*"([^"]+)"\s*->\s*"([^"]+)"\s+\[style=dashed.*?label="([^"]*)".*?tooltip="([^"]*)"', line)
        if m:
            src, tgt, label, tip = m.groups()
            full, mapping = (tip.split(":", 1) + [""])[:2]
            views.append((src, tgt, label, full.strip(), mapping.strip()))
            continue
        m = re.match(r'\s*"([^"]+)"\s*->\s*"([^"]+)"\s+\[color=.*tooltip=', line)
        if m:
            refines.append((m.group(1), m.group(2)))
    return nodes, views, refines, bridges

def group_dot_lines(text):
    """Split the .dot into (preamble, node-lines, {section: edge-lines}).
    preamble = digraph header + node/edge style defaults (kept verbatim)."""
    lines = text.splitlines()
    node_lines = []
    edges = {"ref": [], "view": [], "bridge": []}
    preamble = []
    section = "pre"
    for ln in lines:
        if ln.strip() == "}":
            continue
        if "// refines" in ln:
            section = "ref";    continue
        if "// view-as" in ln:
            section = "view";   continue
        if "// bridges" in ln:
            section = "bridge"; continue
        node_m = re.match(r'\s*"([^"]+)"\s+\[tooltip', ln)
        edge_m = re.match(r'\s*"([^"]+)"\s*->\s*"([^"]+)"', ln)
        if node_m:
            node_lines.append((node_m.group(1), ln)); section = "nodes"
        elif edge_m and section in edges:
            edges[section].append((edge_m.group(1), edge_m.group(2), ln))
        elif section == "pre":
            preamble.append(ln)
    return "\n".join(preamble), node_lines, edges

def assemble_dot(preamble, node_lines, edges, show_ref, show_view, show_bridge, show_inst):
    keep = {n for (n, _) in node_lines if show_inst or not is_instance(n)}
    out = [preamble, ""]
    for (n, ln) in node_lines:
        if n in keep: out.append(ln)
    for flag, sect in ((show_ref, "ref"), (show_view, "view"), (show_bridge, "bridge")):
        if flag:
            out.append(f"\n  // {sect}")
            for (s, t, ln) in edges[sect]:
                if s in keep and t in keep: out.append(ln)
    out.append("}")
    return "\n".join(out)

def render_svg(dot_text):
    svg = subprocess.run(["dot", "-Tsvg"], input=dot_text,
                         capture_output=True, text=True, check=True).stdout
    svg = svg[svg.index("<svg"):]                    # drop xml/doctype preamble
    svg = svg.replace("structure-graph.html#", "#")  # external link -> in-page anchor
    return svg

COMBOS = [(r, v, b, i) for r in (1, 0) for v in (0, 1) for b in (0, 1) for i in (0, 1)]
def combo_key(r, v, b, i): return f"r{r}v{v}b{b}i{i}"

def build():
    with open(DOT) as f:
        text = f.read()
    nodes, views, refines, bridges = parse_dot(text)
    preamble, node_lines, edges = group_dot_lines(text)
    parent = {c: p for c, p in refines}

    # one pre-rendered SVG per layer combination (true re-layout each)
    wraps = []
    for (r, v, b, i) in COMBOS:
        dot_text = assemble_dot(preamble, node_lines, edges, r, v, b, i)
        svg = render_svg(dot_text)
        # Default landing view = the ABSTRACT MAP: refines + view-as, bridges and
        # instances hidden.  (refines-only is too sparse -- most refines edges
        # are instance->abstract, so abstract structures relate via view-as.)
        disp = "block" if (r, v, b, i) == (1, 1, 0, 0) else "none"
        wraps.append(f'<div class="svgwrap" data-combo="{combo_key(r,v,b,i)}" '
                     f'style="display:{disp}">{svg}</div>')

    # per-structure reference section (always shows the full library)
    secs = []
    for name in sorted(nodes):
        outv = [v for v in views if v[0] == name]
        rows = "".join(
            f'<li><a href="#views"><code>{esc(lbl)}</code></a> &rarr; '
            f'<a href="#{esc(t)}">{esc(t)}</a> '
            f'<span class="map">{esc(m)}</span></li>'
            for (s, t, lbl, full, m) in outv) or "<li><em>none</em></li>"
        ref = (f'<p>refines <a href="#{esc(parent[name])}">{esc(parent[name])}</a></p>'
               if name in parent else "")
        bout = [(t, lbl) for (s, t, lbl) in bridges if s == name]
        bin_ = [(s, lbl) for (s, t, lbl) in bridges if t == name and s != name]
        brz = ""
        if bout or bin_:
            bo = "".join(f'<li><code class="bridge">{esc(lbl)}</code> &rarr; '
                         f'<a href="#{esc(t)}">{esc(t)}</a></li>' for (t, lbl) in bout)
            bi = "".join(f'<li><a href="#{esc(s)}">{esc(s)}</a> &rarr; '
                         f'<code class="bridge">{esc(lbl)}</code></li>' for (s, lbl) in bin_)
            brz = f'<p>bridges:</p><ul>{bo}{bi}</ul>'
        tag = ' <span class="inst">instance</span>' if is_instance(name) else ""
        secs.append(
            f'<section id="{esc(name)}"><h3>{esc(name)}{tag}</h3>'
            f'<p class="slots">slots {esc(nodes[name])}</p>{ref}'
            f'<p>views out:</p><ul>{rows}</ul>{brz}</section>')

    vrows = "".join(
        f'<tr id="view-{esc(full)}"><td><code>{esc(full)}</code></td>'
        f'<td><a href="#{esc(s)}">{esc(s)}</a> &rarr; <a href="#{esc(t)}">{esc(t)}</a></td>'
        f'<td class="map">{esc(m)}</td></tr>'
        for (s, t, lbl, full, m) in sorted(views, key=lambda v: v[3]))

    opts = "".join(f'<option value="{esc(n)}">' for n in sorted(nodes))

    doc = f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>VNB structure graph</title>
<style>
 body {{ font-family: Helvetica, Arial, sans-serif; margin: 2rem; color:#1a2a3a; }}
 h1 {{ font-size:1.4rem; }} h3 {{ margin:.2rem 0; color:#2a4a6a; }}
 .hint {{ color:#666; font-size:.9rem; }}
 .controls {{ margin:.8rem 0; padding:.6rem .8rem; background:#f2f6fb; border-radius:8px;
              display:flex; gap:1.2rem; align-items:center; flex-wrap:wrap; font-size:.95rem; }}
 .controls label {{ cursor:pointer; user-select:none; }}
 .controls .swatch {{ font-weight:bold; }}
 .controls .ref {{ color:#2a4a6a; }} .controls .view {{ color:#b06a00; }} .controls .bridge {{ color:#2a8a4a; }}
 code.bridge {{ color:#2a8a4a; background:#eef7f0; }}
 .controls input[type=text] {{ padding:.2rem .4rem; border:1px solid #bbcbdb; border-radius:4px; }}
 .controls button {{ padding:.2rem .5rem; cursor:pointer; }}
 .graph {{ overflow:auto; border:1px solid #ddd; border-radius:8px; padding:1rem; }}
 .svgwrap g.node, .svgwrap g.edge {{ transition: opacity .15s; }}
 svg a {{ cursor:pointer; }}
 section, tr {{ scroll-margin-top: 1rem; }}
 section:target, tr:target {{ background:#fff4e0; border-left:4px solid #b06a00; padding-left:.6rem; }}
 .slots, .map {{ font-family: ui-monospace, Menlo, Consolas, monospace; color:#555; }}
 .inst {{ font-size:.7rem; font-weight:normal; color:#888; border:1px solid #ccc;
          border-radius:3px; padding:0 .3rem; vertical-align:middle; }}
 .cols {{ display:flex; gap:2rem; flex-wrap:wrap; }}
 .cols section {{ min-width:16rem; }}
 table {{ border-collapse:collapse; margin-top:.5rem; }}
 td {{ border-top:1px solid #eee; padding:.3rem .8rem; vertical-align:top; }}
 code {{ background:#f2f6fb; padding:0 .25rem; border-radius:3px; }}
</style></head><body>
<h1>VNB structure graph</h1>
<p class="hint"><span class="swatch ref">&#9472;</span> refines (specialisation)
 &nbsp; <span class="swatch view">&#9476;</span> view-as (forgetful map)
 &nbsp; <span class="swatch bridge">&#8230;</span> bridge (constructor functoid, builds a new slot).
 Hover for full names; click a node or arrow to jump to its entry below.</p>
<div class="controls">
 <label><input type="checkbox" id="t-ref" checked> <span class="ref">refines</span></label>
 <label><input type="checkbox" id="t-view" checked> <span class="view">view-as</span></label>
 <label><input type="checkbox" id="t-bridge"> <span class="bridge">bridges</span></label>
 <label><input type="checkbox" id="t-inst"> instances</label>
 <span style="margin-left:auto"></span>
 <label>focus: <input type="text" id="focus" list="names" placeholder="structure"></label>
 <datalist id="names">{opts}</datalist>
 <button id="focus-clear" type="button">clear</button>
</div>
<div class="graph">{''.join(wraps)}</div>
<h2 id="structures">Structures</h2>
<div class="cols">{''.join(secs)}</div>
<h2 id="views">view-as functoids</h2>
<table><tr><th>functoid</th><th>map</th><th>components</th></tr>{vrows}</table>
<script>
(function(){{
  var ref=document.getElementById('t-ref'),
      view=document.getElementById('t-view'),
      bridge=document.getElementById('t-bridge'),
      inst=document.getElementById('t-inst'),
      focus=document.getElementById('focus'),
      wraps=[].slice.call(document.querySelectorAll('.svgwrap'));
  function key(){{ return 'r'+(ref.checked?1:0)+'v'+(view.checked?1:0)+'b'+(bridge.checked?1:0)+'i'+(inst.checked?1:0); }}
  function visible(){{ for(var i=0;i<wraps.length;i++) if(wraps[i].style.display!=='none') return wraps[i].querySelector('svg'); return null; }}
  function title(g){{ var t=g.querySelector('title'); return t?t.textContent.trim():''; }}
  function applyFocus(){{
    var svg=visible(); if(!svg) return;
    var f=focus.value.trim();
    var nodes=[].slice.call(svg.querySelectorAll('g.node')),
        edges=[].slice.call(svg.querySelectorAll('g.edge'));
    if(!f){{ nodes.concat(edges).forEach(function(g){{g.style.opacity=1;}}); return; }}
    var nbr={{}}; nbr[f]=1;
    edges.forEach(function(e){{ var p=title(e).split('->'); if(p[0]===f)nbr[p[1]]=1; if(p[1]===f)nbr[p[0]]=1; }});
    nodes.forEach(function(n){{ n.style.opacity=nbr[title(n)]?1:0.12; }});
    edges.forEach(function(e){{ var p=title(e).split('->'); e.style.opacity=(p[0]===f||p[1]===f)?1:0.08; }});
  }}
  function show(){{ var k=key(); wraps.forEach(function(w){{ w.style.display=(w.getAttribute('data-combo')===k)?'block':'none'; }}); applyFocus(); }}
  [ref,view,bridge,inst].forEach(function(b){{ b.addEventListener('change',show); }});
  focus.addEventListener('input',applyFocus);
  document.getElementById('focus-clear').addEventListener('click',function(){{ focus.value=''; applyFocus(); }});
  show();
}})();
</script>
</body></html>
"""
    with open(OUT, "w") as f:
        f.write(doc)
    inst_nodes = sorted(n for n in nodes if is_instance(n))
    print(f"wrote {OUT}  ({len(nodes)} structures, {len(views)} views, "
          f"{len(refines)} refines, {len(bridges)} bridges, {len(COMBOS)} layer combos)")
    print(f"  instances (default-hidden): {', '.join(inst_nodes)}")
    print(f"  bridges: " + "; ".join(f"{s}->{t} ({l})" for (s, t, l) in bridges))

if __name__ == "__main__":
    try:
        build()
    except subprocess.CalledProcessError as e:
        print("dot failed:", e.stderr, file=sys.stderr); sys.exit(1)
