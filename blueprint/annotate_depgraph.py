#!/usr/bin/env -S uv run --quiet python3
"""Sync blueprint statuses + annotate the dep graph, from the Lean ledger.

Single source of truth = the `@[goodstein_blueprint <order> <category>
"<stage>" "<laps>" <confidence> ...]` attribute sites in src/**/*.lean.
This script transports them into the blueprint:

  * STATUS SYNC (anti-drift): each ledger-matched node's `\\leanok`/`\\notready`
    tag in blueprint/src/content.tex is REWRITTEN from the ledger category
    (clean/trusted -> \\leanok, debt/broken -> \\notready). Hand-edited statuses
    on covered nodes get overwritten -- per the blueprint doctrine, status is
    machine-derived, never hand-kept. (Nodes without an attribute site are left
    alone: they are still hand-claims until they get a ledger entry.)
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


STATUS_FOR = {"clean": "\\leanok", "trusted": "\\leanok",
              "debt": "\\notready", "broken": "\\notready"}

# Route-A read-off nodes are BANKED per DIRECTION.md (2026-07-01 route pivot):
# grey/dashed "abandoned trail" styling so the map doesn't show two live routes
# to the summit. (The pathB capstone chain was originally kept live as "the
# someK substrate of the W0-W7 masterplan" — that framing died with the Zᵉ
# fork; see SUPERSEDED below.) This transports an operator decision, not a
# kernel fact.
#
# EDGES touching a banked node recede with it (dotted, dim, thin). Rationale:
# leanblueprint's \uses is conjunctive-only — the dep graph has NO native
# "one-of-several-paths" (OR) notation, and the summit is a disjunction of the
# two route headlines. The prose on thm:summit carries the OR; this overlay
# makes the banked alternative's edges read as deprioritized, not required.
BANKED = {"thm:routeA_headline", "thm:crux2_axiom"}
BANKED_EDGE_STYLE = 'style=dotted, color="#4a5056", penwidth=0.7, arrowsize=0.6]'

# The pathB capstone chain is SUPERSEDED-IN-SUBSTRATE (2026-07-02, Zᵉ fork):
# its capstones 2–8 are stated over the (k,d)/someK calculus that SPIKE-W4B
# kernel-killed, and its only consumer is the banked crux2_axiom. The
# decomposition SHAPE re-keys onto Zeh at the embedding phase (it will then
# feed wainer_axiom); until that restatement exists, the chain's EDGES fade
# like the banked trail. Node colors stay kernel-honest (ledger-audited) —
# only the edges transport this operator decision.
SUPERSEDED = {
    "thm:pathBGoodsteinSentenceShape", "thm:pathBPeanoMinusAxiomLeaves",
    "thm:pathBInductionAxiomShell", "thm:pathBClosedWitnessBudgets",
    "thm:pathBSomeKStructuralEmbedding", "thm:pathBOperatorCutElimination",
    "thm:pathBSubformulaProjection", "thm:pathBGoodsteinFragmentExtraction",
    "thm:pathBTerminalRouteBridge",
}
FADED = BANKED | SUPERSEDED


def sync_tex_statuses(ann: dict) -> bool:
    """Rewrite each ledger-matched node's status tag in content.tex from the
    ledger category. Returns True if the file changed."""
    text = TEX.read_text()
    changes = []

    def fix(m):
        env, label, body = m.groups()
        lm = re.search(r'\\lean\{([^}]*)\}', body)
        if not lm:
            return m.group(0)
        info = next(
            (ann[d] for d in (norm(x.strip()) for x in lm.group(1).split(",")) if d in ann),
            None,
        )
        if info is None:
            return m.group(0)
        want = STATUS_FOR[info["category"]]
        if re.search(r'(?<!textbackslash )\\leanok\b' if want == "\\leanok"
                     else r'(?<!textbackslash )\\notready\b', body) and not re.search(
                     r'(?<!textbackslash )\\notready\b' if want == "\\leanok"
                     else r'(?<!textbackslash )\\leanok\b', body):
            return m.group(0)  # already exactly right
        # strip any existing status tag lines, then insert the wanted one
        # right after the \lean{} line (prose uses \textbackslash forms, safe)
        body2 = re.sub(r'[ \t]*(?<!textbackslash )\\(leanok|notready)\b[ \t]*\n?', '', body)
        body3 = re.sub(r'(\\lean\{[^}]*\}[ \t]*\n)',
                       lambda mm: mm.group(1) + "  " + want + "\n",
                       body2, count=1)
        changes.append(f"{label}: -> {want} (ledger: {info['category']})")
        return f"\\begin{{{env}}}\\label{{{label}}}{body3}\\end{{{env}}}"

    new = NODE_RE.sub(fix, text)
    if new != text:
        TEX.write_text(new)
    for c in changes:
        print("status sync:", c)
    return bool(changes)


def main() -> int:
    ann = lean_annotations()
    if not ann:
        print("no @[goodstein_blueprint] annotations found", file=sys.stderr)
        return 1

    changed = sync_tex_statuses(ann)
    if "--web" in sys.argv:
        subprocess.run(["leanblueprint", "web"], cwd=REPO, check=True)
    elif changed:
        print("warn: content.tex statuses were re-synced from the ledger; "
              "re-run with --web to rebuild the site", file=sys.stderr)

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
    # Summit at the TOP: rank flow bottom-to-top, so dependencies climb
    # shores -> foothills -> routes -> crown (matches the mountain metaphor).
    html = html.replace(
        "graph [bgcolor=transparent];",
        "graph [bgcolor=transparent,\trankdir=BT];",
        1,
    )

    # Banked-route styling (see BANKED above).
    for node in sorted(BANKED):
        suffix = node.split(":", 1)[-1]
        pat = re.compile(
            r'("' + re.escape(node) + r'"\s*\[)color=[^,]*,(\s*)label=' + re.escape(suffix) + r','
        )
        def _grey(m, s=suffix):
            return (m.group(1) + 'color="#8a9096",' + m.group(2)
                    + 'label="' + s + '\\\\n(banked)",' + m.group(2) + 'style=dashed,')
        html = pat.sub(_grey, html, count=1)

    # Banked/superseded EDGE styling (see the BANKED/SUPERSEDED comments):
    # every edge with a faded endpoint recedes. Idempotent — already-faded
    # edges no longer match the stock `style=dashed]` tail.
    edge_pat = re.compile(r'("(?P<tail>[^"]+)" -> "(?P<head>[^"]+)"\s*\[)style=dashed\]')
    def _fade(m):
        if m.group("tail") in FADED or m.group("head") in FADED:
            return m.group(1) + BANKED_EDGE_STYLE
        return m.group(0)
    html, _ = edge_pat.subn(_fade, html)
    faded = len(re.findall(re.escape(BANKED_EDGE_STYLE), html))
    print(f"banked/superseded-edge fade: {faded} edge(s) deprioritized")

    HTML.write_text(html)
    print(f"annotated {changed} DOT labels / {len(matched)} matched nodes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
