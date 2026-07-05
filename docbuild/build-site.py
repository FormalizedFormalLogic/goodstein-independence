#!/usr/bin/env -S uv run --quiet python3
"""Build the complete goodstein-independence site (API docs + blueprint) locally.

One command, same steps CI runs:
  1. `lake build GoodsteinPA:docs` in docbuild/   (doc-gen4; first run renders the
     whole Mathlib+Foundation closure -- slow; incremental after that)
  2. trim-docs.py                                 (keep GoodsteinPA, link deps out to
     hosted mathlib4_docs / Foundation docs; in-place + idempotent)
  3. blueprint/annotate_depgraph.py --web         (leanblueprint web + ledger
     lap/confidence estimates)
  4. assemble site/ at the repo root:
        site/docs       trimmed API docs      <- the \\dochome{../docs} target
        site/blueprint  annotated blueprint
        site/index.html redirect to the dep graph

Serve it (replacing a server pointed at blueprint/web):

    python3 -m http.server 8127 -d ~/src/goodstein-independence/site

Flags:
  --ci         also run `lake exe cache get` first (CI runners need the Mathlib
               olean cache; locally this is SKIPPED so it can't clobber the
               lake-base CoW store)
  --skip-docs  rebuild only the blueprint + reassemble (fast local iteration;
               reuses the existing trimmed docs build)
"""

import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DOCBUILD = REPO / "docbuild"
DOC_OUT = DOCBUILD / ".lake" / "build" / "doc"
SITE = REPO / "site"

INDEX_HTML = """<!DOCTYPE html>
<meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=blueprint/dep_graph_document.html">
<title>goodstein-independence</title>
<p><a href="blueprint/dep_graph_document.html">Blueprint dependency graph</a> &middot;
   <a href="blueprint/index.html">Blueprint</a> &middot;
   <a href="docs/">API docs</a></p>
"""


def run(cmd, cwd):
    print(f"==> {' '.join(str(c) for c in cmd)}  (in {cwd})", flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def main() -> int:
    ci = "--ci" in sys.argv
    skip_docs = "--skip-docs" in sys.argv

    if not skip_docs:
        if ci:
            subprocess.run(["lake", "exe", "cache", "get"], cwd=DOCBUILD, check=False)
        # Two levers keep the 16 GB CI runner from OOMing on the doc build:
        #  (1) Build the library FIRST, then doc-gen separately (Foundation's own recipe:
        #      `lake build Foundation` then `:docs`). Going straight to `:docs` interleaves
        #      Lean elaboration (Foundation compiled from source) with doc-gen4 in one DAG,
        #      doubling peak RSS. Split => doc-gen runs on ready oleans, no overlap.
        #  (2) Cap doc-gen parallelism to -j2 on CI. goodstein's doc closure is BIGGER than
        #      Foundation's (it imports Foundation whole plus extra Mathlib), so at full -j
        #      the tail-end doc-gen workers still spike together and OOM where Foundation
        #      just fits. -j2 caps concurrent workers so peak fits in RAM. The compile phase
        #      is fine at full speed; only doc-gen needs throttling. (Local: full -j.)
        run(["lake", "build", "GoodsteinPA"], cwd=DOCBUILD)
        docs_cmd = ["lake", "build", "GoodsteinPA:docs"] + (["-j2"] if ci else [])
        run(docs_cmd, cwd=DOCBUILD)
        run([sys.executable, str(DOCBUILD / "trim-docs.py"), str(DOC_OUT), "GoodsteinPA"], cwd=REPO)
    elif not DOC_OUT.is_dir():
        sys.exit("--skip-docs given but no existing docs build at " + str(DOC_OUT))

    run([sys.executable, str(REPO / "blueprint" / "annotate_depgraph.py"), "--web"], cwd=REPO)

    if SITE.exists():
        shutil.rmtree(SITE)
    SITE.mkdir()
    shutil.copytree(DOC_OUT, SITE / "docs")
    shutil.copytree(REPO / "blueprint" / "web", SITE / "blueprint")
    (SITE / "index.html").write_text(INDEX_HTML)

    print("\nSite assembled at", SITE)
    print("Serve it:  python3 -m http.server 8127 -d", SITE)
    return 0


if __name__ == "__main__":
    sys.exit(main())
