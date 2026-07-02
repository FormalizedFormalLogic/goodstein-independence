# Blueprint Sub-Project — Plan & Contract

Multi-player build of the g-i blueprint layer.
**Players:** codex · CC-judge (Ren) · Trevor.
**No treadmill running** → codex + Ren work in the **same tree, in tandem** (coordinate edits; no worktree). Touch different files where possible; the one shared file is `BlueprintAttr.lean` (codex defines, Ren reads).

## State of the world (updated 2026-06-29)

- ✅ **Tooling:** `graphviz` 15.0.0 installed. **leanblueprint installed globally** via `uv tool install leanblueprint --with-executables-from plasTeX` — puts both `leanblueprint` and its `plastex` dep on PATH through uv (no symlink, no wrapper). ⚠️ The `--with-executables-from plasTeX` is essential: a plain `uv tool install leanblueprint` hides plastex, which leanblueprint shells out to by bare name. `checkdecls` is a separate `lake exe` (Lean-side), unaffected.
- ✅ **MacTeX** (`mactex-no-gui`) **installed** 2026-06-29 → **PDF path available** (`leanblueprint pdf`). It drops `/etc/paths.d/TeX`, so a *fresh* shell/session sees `pdflatex`; an existing shell needs `eval "$(/usr/libexec/path_helper)"` or a restart. (`leanblueprint web` does not need TeX.)
- 📂 codex `aad2102` (lap 167) landed the skeleton: `BlueprintCategory = clean|trusted|debt|broken` + 9 `\notready` Path B nodes (all claim `debt`) + `checkdecls` wired. **Path B stages promoted `wip/` → `src/GoodsteinPA/{PathBProbe,OperatorZinfty}.lean`, imported via the dedicated `GoodsteinPABlueprint` root** (keeps the axiom-bearing ledger out of the public `GoodsteinPA` root). The `@[goodstein_blueprint]` attribute lives in `src/GoodsteinPA/BlueprintAttr.lean`.

## Two-layer model (recap)

- **leanblueprint** = reviewer-facing proof map: LaTeX narrative, dependency graph, `\lean{...}`, `\uses{...}`, status color.
- **`@[goodstein_blueprint ...]`** = machine-local ledger: category, estimates, evidence strings, Lean-name validation.

## Design constraints (these change what gets authored)

1. **Status is machine-derived from `Lean.collectAxioms`, never hand-maintained** — anti-drift is the whole point; hand-kept status rots as work moves. Source of truth = the computed axiom footprint. The attribute's `status:=` and the blueprint's `\leanok`/`\notready` are **claims the audit verifies**.
2. **Status is typed, not binary.** Category enum:
   - `clean` → footprint ⊆ `{propext, Classical.choice, Quot.sound}` → `\leanok` *earned*
   - `trusted` → footprint ⊆ declared trusted-axiom allowlist (deliberate literature/finite axiom) → **own color, a DONE boundary** (matters for bounded_gaps; ~empty for g-i)
   - `debt` → depends on a deep axiom we mean to discharge → `\notready`
   - `broken` → axiom where the node should be unconditional, or `sorryAx` present → **CI error**

   Current Path B capstones are all `debt` → `\notready`.

## Division of labor (same tree, in tandem)

**codex:**
1. Make Path B stages importable. Minimal move: `git mv wip/PathBProbe.lean src/GoodsteinPA/PathBProbe.lean` + `import GoodsteinPA.PathBProbe` in the lib root. Keeps the planned `\lean{GoodsteinPA.PathBProbe.pathB_*_stage}` names resolvable by both `checkdecls` and the audit. (Confirm layout — you know it better.)
2. Extend the `@[goodstein_blueprint ...]` schema to carry the 4-value **category** above (in `BlueprintAttr.lean`).
3. Init `blueprint/`; author the 9 Path B nodes: `\lean{...}`, `\uses{...}` matching the dependency chain, `\notready` on every open capstone. **Do NOT hand-assert `\leanok`.**
4. `checkdecls` green; `leanblueprint web` + graph. **Skip `pdf`** until MacTeX lands.

**CC-judge (Ren): ✅ DONE 2026-06-29** (`src/BlueprintAudit.lean`, `lake exe blueprint_audit`).
- A. ✅ Built. Iterates every `@[goodstein_blueprint]`-tagged decl via `blueprintAttr.getParam?`, runs `Lean.collectAxioms` on `info.stage`, classifies into `clean|trusted|debt|broken` vs the allowlist, reconciles against the `category` claim (severity order `clean<trusted<debt<broken`), emits a Markdown report. Env-loaded `lake exe` (search-path seeded from `LEAN_PATH`, `enableInitializersExecution` + `importModules` — the checkdecls pattern, no Lake link needed).
- B. ✅ CI-wired ("Blueprint status gate" step in `.github/workflows/ci.yml`). **Hard FAIL** on: claim overstated (reality worse than claim, e.g. claimed `clean` but really `debt`), `sorryAx` leaked (`broken`), stage theorem missing, or zero nodes (vacuous gate). **WARN** (non-fatal) when reality is *better* than the claim → upgrade the `category`. All three branches verified live. ⚠️ Fix that fell out: `GoodsteinPABlueprint` added to `defaultTargets` so bare `lake build` (CI's lean-action + the local hook) actually compiles the Path B nodes — else the audit reads stale/absent oleans.
- C. ✅ Repo-agnostic: the trusted-axiom allowlist is a file param (`blueprint/trusted-axioms.txt`, empty for g-i). Two clearly-marked `EDIT-ON-TRANSPLANT` constants (attr ref + lib roots) are the only g-i-specific lines; copy the file + `BlueprintAttr.lean` to transplant to bounded_gaps / sum-product.

Current run: 9/9 nodes consistent (`debt`/`debt`), 0 warnings, exit 0. ~6s.

**Trevor:** LaTeX narrative + arbitration.

## Contract surface (where the players meet)

- **Category names:** `clean | trusted | debt | broken` — fixed here.
- **Trusted-axiom allowlist:** a plain list of fully-qualified axiom names the audit treats as deliberately trusted. Ren owns the format (proposal: `blueprint/trusted-axioms.txt`, one name per line). **For g-i it starts empty** (Path B capstones are `debt`, not `trusted`).
- **Node→decl map:** the `\lean{}` entries in `blueprint/src/*.tex`. codex keeps these names real + importable; Ren's audit consumes them.
- **Shared file:** `BlueprintAttr.lean` — codex defines the category enum, Ren reads it. Agree on the 4 names before Ren wires the audit.

## Not yet ready

- `leanblueprint pdf` — blocked on MacTeX download. Revisit when `pdflatex` is on PATH.

## Lap/confidence estimates in the dep graph (added 2026-07-01)

The `@[goodstein_blueprint]` ledger's `"<laps>"` + `<confidence>` fields are
surfaced on the dep graph by `blueprint/annotate_depgraph.py`: each matched
node's DOT label gains a second line (`~5-10 laps | 65%`) and its click-modal
gains the same "Ledger estimate" line. Transport is verbatim from the Lean
(single source of truth); the script never adjudicates status. Matching is
tex `\lean{}` name vs. attribute stage ident, modulo `_stage`/`_capstone`.

A plain `leanblueprint web` WIPES the annotations, so the one-command refresh is:

    blueprint/annotate_depgraph.py --web

Nodes without an attribute site (currently everything outside the 9 Path B
capstones, e.g. `wainer_axiom` / `crux2_axiom` / `infinitary_tower`) carry no
estimate; give them `@[goodstein_blueprint ...]` sites in the Lean and they
flow through automatically.
