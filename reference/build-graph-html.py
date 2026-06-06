#!/usr/bin/env python3
"""Build a self-contained, clickable structure-graph.html from structure-graph.dot.

Pipeline: parse the .dot (nodes carry slot tooltips, edges carry view/refines
tooltips) -> render the graph with `dot -Tsvg` -> rewrite the dead
"STRUCTURE-INDEX.md#x" links into in-page "#x" anchors -> emit one HTML file
that inlines the SVG and, below it, a reference section per structure (slots,
the views out of it, what it refines) plus an all-views section.  Click a node
or arrow in the graph and the page scrolls to that entry.

Regenerate after a library change:
    # 1. rewrite the .dot from the prover REPL:  (structure-graph-dot-file)
    # 2. python3 reference/build-graph-html.py
Open reference/structure-graph.html in any web browser (double-click).
"""
import os, re, html, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOT  = os.path.join(HERE, "structure-graph.dot")
OUT  = os.path.join(HERE, "structure-graph.html")

def esc(s): return html.escape(s, quote=True)

def parse_dot(text):
    nodes = {}   # name -> slots-string
    views = []   # (src, tgt, label, fullname, mapping)
    refines = [] # (child, parent)
    for line in text.splitlines():
        m = re.match(r'\s*"([^"]+)"\s+\[tooltip="([^"]*)",\s*URL=', line)
        if m:
            name, tip = m.group(1), m.group(2)
            slots = tip.split("slots", 1)[1].strip() if "slots" in tip else ""
            nodes[name] = slots
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
    return nodes, views, refines

def render_svg():
    svg = subprocess.run(["dot", "-Tsvg", DOT], capture_output=True, text=True, check=True).stdout
    svg = svg[svg.index("<svg"):]                       # drop xml/doctype preamble
    svg = svg.replace("structure-graph.html#", "#")      # external page link -> in-page anchor
    return svg

def build():
    with open(DOT) as f:
        nodes, views, refines = parse_dot(f.read())
    svg = render_svg()
    parent = {c: p for c, p in refines}

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
        secs.append(
            f'<section id="{esc(name)}"><h3>{esc(name)}</h3>'
            f'<p class="slots">slots {esc(nodes[name])}</p>{ref}'
            f'<p>views out:</p><ul>{rows}</ul></section>')

    vrows = "".join(
        f'<tr id="view-{esc(full)}"><td><code>{esc(full)}</code></td>'
        f'<td><a href="#{esc(s)}">{esc(s)}</a> &rarr; <a href="#{esc(t)}">{esc(t)}</a></td>'
        f'<td class="map">{esc(m)}</td></tr>'
        for (s, t, lbl, full, m) in sorted(views, key=lambda v: v[3]))

    doc = f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>VNB structure graph</title>
<style>
 body {{ font-family: Helvetica, Arial, sans-serif; margin: 2rem; color:#1a2a3a; }}
 h1 {{ font-size:1.4rem; }} h3 {{ margin:.2rem 0; color:#2a4a6a; }}
 .hint {{ color:#666; font-size:.9rem; }}
 .graph {{ overflow:auto; border:1px solid #ddd; border-radius:8px; padding:1rem; }}
 svg a {{ cursor:pointer; }}
 section, tr {{ scroll-margin-top: 1rem; }}
 section:target, tr:target {{ background:#fff4e0; border-left:4px solid #b06a00; padding-left:.6rem; }}
 .slots, .map {{ font-family: ui-monospace, Menlo, Consolas, monospace; color:#555; }}
 .cols {{ display:flex; gap:2rem; flex-wrap:wrap; }}
 .cols section {{ min-width:16rem; }}
 table {{ border-collapse:collapse; margin-top:.5rem; }}
 td {{ border-top:1px solid #eee; padding:.3rem .8rem; vertical-align:top; }}
 code {{ background:#f2f6fb; padding:0 .25rem; border-radius:3px; }}
</style></head><body>
<h1>VNB structure graph</h1>
<p class="hint">Solid = refines (specialisation). Dashed = view-as (forgetful map).
Hover for full names; click a node or arrow to jump to its entry below.</p>
<div class="graph">{svg}</div>
<h2 id="structures">Structures</h2>
<div class="cols">{''.join(secs)}</div>
<h2 id="views">view-as functoids</h2>
<table><tr><th>functoid</th><th>map</th><th>components</th></tr>{vrows}</table>
</body></html>
"""
    with open(OUT, "w") as f:
        f.write(doc)
    print(f"wrote {OUT}  ({len(nodes)} structures, {len(views)} views, {len(refines)} refines edges)")

if __name__ == "__main__":
    try:
        build()
    except subprocess.CalledProcessError as e:
        print("dot failed:", e.stderr, file=sys.stderr); sys.exit(1)
