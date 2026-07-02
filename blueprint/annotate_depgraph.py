#!/usr/bin/env -S uv run --quiet python3
"""Annotate the leanblueprint dep graph with lap/confidence estimates.

Single source of truth = the `@[goodstein_blueprint <order> <category>
"<stage>" "<laps>" <confidence> ...]` attribute sites in src/**/*.lean.
This script transports them into blueprint/web/dep_graph_document.html:

  * each matched node's label in the embedded DOT gains a second line,
    e.g.  pathBOperatorCutElimination
          ~5-10 laps | 65%
  * each matched node's click-modal gains the same one-line estimate

Matching: a tex node (\\label{...} + \\lean{...} in blueprint/src/content.tex)
is matched to an attribute site when the attribute's stage-declaration ident
equals the last component of any \\lean{} name on the node, modulo a
trailing `_stage`/`_capstone` (the ledger names some sites by capstone
where the tex binds the stage theorem).

The numbers are transported verbatim (including `0 laps | 100%` on ledger-clean
nodes) -- this script never adjudicates status, it only surfaces the ledger.

Idempotent: re-running skips nodes already annotated. A plain `leanblueprint
web` rebuild WIPES the annotations, so the one-command refresh is:

    blueprint/annotate_depgraph.py --web     # rebuild web/, then annotate
"""

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def norm(decl: str) -> str:
    """last component, modulo the _stage/_capstone naming split"""
    return re.sub(r"_(stage|capstone)$", "", decl.split(".")[-1])
TEX = REPO / "blueprint" / "src" / "content.tex"
HTML = REPO / "blueprint" / "web" / "dep_graph_document.html"

# attribute [goodstein_blueprint <order> <category> "<stage>" "<laps>" <conf> <stageDecl> ...
ATTR_RE = re.compile(
    r'attribute\s*\[goodstein_blueprint\s+(\d+)\s+(\w+)\s+"([^"]*)"\s+"([^"]*)"\s+(\d+)\s+([\w.]+)'
)

NODE_RE = re.compile(
    r'\\begin\{(definition|theorem|lemma)\}\s*\\label\{([^}]+)\}(.*?)\\end\{\1\}',
    re.S,
)


def lean_annotations() -> dict:
    """stage-decl last component -> {category, laps, confidence}"""
    out = {}
    for f in sorted((REPO / "src").rglob("*.lean")):
        for m in ATTR_RE.finditer(f.read_text()):
            _order, cat, _stage, laps, conf, decl = m.groups()
            out[norm(decl)] = {
                "category": cat,
                "laps": laps,
                "confidence": int(conf),
            }
    return out


def tex_node_decls() -> dict:
    """tex node id -> [last components of its \\lean{} names]"""
    nodes = {}
    for m in NODE_RE.finditer(TEX.read_text()):
        _env, label, body = m.groups()
        lm = re.search(r'\\lean\{([^}]*)\}', body)
        if lm:
            nodes[label] = [norm(d.strip()) for d in lm.group(1).split(",")]
    return nodes


def estimate_text(info: dict) -> str:
    prefix = "" if info["laps"] == "0" else "~"
    return f"{prefix}{info['laps']} laps | {info['confidence']}%"


def main() -> int:
    if "--web" in sys.argv:
        subprocess.run(["leanblueprint", "web"], cwd=REPO, check=True)

    ann = lean_annotations()
    if not ann:
        print("no @[goodstein_blueprint] annotations found", file=sys.stderr)
        return 1

    matched = {
        node: ann[d]
        for node, decls in tex_node_decls().items()
        for d in decls
        if d in ann
    }

    html = HTML.read_text()
    changed = 0
    for node, info in sorted(matched.items()):
        suffix = node.split(":", 1)[-1]
        est = estimate_text(info)
        # DOT label (inside a JS template literal: file needs \\n so the JS
        # string carries \n, which Graphviz renders as a centered line break)
        old = f"label={suffix},"
        new = f'label="{suffix}\\\\n{est}",'
        if old in html:
            html = html.replace(old, new, 1)
            changed += 1
        elif f'label="{suffix}\\\\n' not in html:
            print(f"warn: no DOT label found for {node}", file=sys.stderr)
        # modal: prepend the estimate line to the node's LaTeX link
        anchor_re = re.compile(r'(<a class="latex_link" href="[^"]*#' + re.escape(node) + '">)')
        if f'data-estimate="{node}"' not in html:
            html = anchor_re.sub(
                f'<p class="node-estimate" data-estimate="{node}">Ledger estimate: {est} confidence</p>\n    \\1',
                html,
                count=1,
            )
    HTML.write_text(html)
    print(f"annotated {changed} DOT labels / {len(matched)} matched nodes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
