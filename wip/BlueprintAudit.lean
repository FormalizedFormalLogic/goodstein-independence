/-
# `blueprint_audit` — machine-verified status gate for the blueprint ledger

Computes each blueprint node's REAL kernel axiom footprint via `Lean.collectAxioms` and reconciles
it against the `@[goodstein_blueprint ...]` *category claim*. Anti-drift is the whole point: the
status is DERIVED from the kernel, never hand-trusted. The blueprint's `\leanok`/`\notready` colors
and the attribute's `category :=` become claims this tool VERIFIES against `#print axioms` reality.

## What it checks (per the blueprint doctrine)

The category is the human-facing projection of the 🟢🟡🔴 axiom-discharge ledger:

| Category  | Computed condition (footprint F, allowlist T)                 | Meaning          |
|-----------|---------------------------------------------------------------|------------------|
| `clean`   | F ⊆ {propext, Classical.choice, Quot.sound}                   | `\leanok` earned |
| `trusted` | F's non-clean axioms ⊆ T (declared literature/finite axioms)  | DONE boundary    |
| `debt`    | depends on an axiom outside {clean} ∪ T (a deep axiom to kill) | `\notready`      |
| `broken`  | `sorryAx` in F                                                | CI error         |

Reconciliation verdict (severity order clean<trusted<debt<broken):
  * reality WORSE than claim (e.g. claimed `clean`, really `debt`)  → FAIL (claim overstated)
  * a `sorryAx` leaked (computed `broken`)                          → FAIL
  * a stage theorem is missing from the environment                → FAIL
  * no blueprint nodes found at all (vacuous gate)                  → FAIL
  * reality BETTER than claim (an axiom was discharged)            → WARN (upgrade the claim)
  * reality == claim                                              → OK
Exit 0 iff there are no FAILs.

## Repo-agnostic (transplants to bounded_gaps / sum-product)

The trusted-axiom allowlist is a PARAMETER — a file, one fully-qualified axiom name per line
(`#` comments and blank lines ignored). For g-i it is empty (the Path B capstones are `debt`, not
`trusted`); for bounded_gaps it would list the paper-cited axioms (BV/EH/…). To transplant: copy
this file + `BlueprintAttr.lean`, and edit the two `EDIT-ON-TRANSPLANT` constants below.

Run: `lake exe blueprint_audit [path/to/trusted-axioms.txt]`
Host-local equivalent of the per-headline `lean-axiom-gate`, but driven by the blueprint ledger.
-/
import Lean
import GoodsteinPA.BlueprintAttr

open Lean
open GoodsteinPA.Blueprint

namespace BlueprintAudit

-- ── EDIT-ON-TRANSPLANT ──────────────────────────────────────────────────────────────────────────
/-- Library roots to import so that (a) every `@[goodstein_blueprint]`-tagged declaration is in
scope and (b) the full transitive closure each stage theorem needs is loaded for `collectAxioms`.
`GoodsteinPABlueprint` carries the Path B nodes; `GoodsteinPA` catches any tag placed in the main
library. -/
def auditRoots : Array Import :=
  #[`GoodsteinPA, `GoodsteinPABlueprint].map ({ module := · })

/-- The project's blueprint attribute. The audit consumes `info.category` (the claim) and
`info.stage` (the theorem whose footprint is the ground truth). -/
def projectBlueprintAttr := blueprintAttr

/-- Default allowlist path, relative to the repo root (the cwd under `lake exe`). -/
def defaultAllowlistPath : System.FilePath := "blueprint/trusted-axioms.txt"
-- ──────────────────────────────────────────────────────────────────────────────────────────────

/-- The three kernel-standard axioms that count as "axiom-clean". -/
def cleanAxioms : NameSet :=
  (NameSet.empty.insert `propext).insert `Classical.choice |>.insert `Quot.sound

/-- The `sorry` axiom. Its presence in a footprint means the proof is incomplete. -/
def sorryAxiomName : Name := `sorryAx

/-- Severity ordering: a higher number is a worse (more axiom-laden) status. -/
def severity : BlueprintCategory → Nat
  | .clean => 0
  | .trusted => 1
  | .debt => 2
  | .broken => 3

/-- The non-clean axioms of a footprint (the ones that decide trusted-vs-debt). -/
def nonCleanAxioms (footprint : Array Name) : Array Name :=
  footprint.filter (fun a => !cleanAxioms.contains a)

/-- Compute the real category from a kernel axiom footprint and the trusted-axiom allowlist. -/
def categoryOfFootprint (footprint : Array Name) (allow : NameSet) : BlueprintCategory :=
  if footprint.contains sorryAxiomName then
    .broken
  else
    let extra := nonCleanAxioms footprint
    if extra.isEmpty then .clean
    else if extra.all allow.contains then .trusted
    else .debt

inductive Verdict where
  | ok
  | warn
  | fail
  deriving BEq, Inhabited

def Verdict.icon : Verdict → String
  | .ok => "✓ OK"
  | .warn => "⚠ WARN"
  | .fail => "✗ FAIL"

structure NodeResult where
  decl : Name
  stage : Name
  claimed : BlueprintCategory
  computed : BlueprintCategory
  footprint : Array Name
  missing : Bool
  verdict : Verdict
  note : String
  deriving Inhabited

/-- Reconcile a claimed category against the computed one. -/
def reconcile (claimed computed : BlueprintCategory) (missing : Bool) : Verdict × String :=
  if missing then
    (.fail, "stage theorem not found in environment (import gap or renamed decl)")
  else if computed == .broken then
    (.fail, "sorryAx in footprint — node depends on a `sorry`")
  else
    let sc := severity claimed
    let so := severity computed
    if so > sc then
      (.fail, s!"reality WORSE than claim ({claimed.toString} → {computed.toString}); claim is overstated")
    else if so < sc then
      (.warn, s!"reality BETTER than claim ({claimed.toString} → {computed.toString}); upgrade `category`")
    else
      (.ok, "claim matches reality")

/-- Walk every tagged declaration, compute its stage theorem's real footprint, classify, reconcile. -/
def runAudit (allow : NameSet) : CoreM (Array NodeResult) := do
  let env ← getEnv
  let mut entries : Array (Name × BlueprintInfo) := #[]
  for (declName, _) in env.constants do
    if let some info := projectBlueprintAttr.getParam? env declName then
      entries := entries.push (declName, info)
  let sorted := entries.qsort (fun a b => a.2.order < b.2.order)
  let mut results : Array NodeResult := #[]
  for (declName, info) in sorted do
    let missing := !env.contains info.stage
    let footprint ← if missing then pure #[] else collectAxioms info.stage
    let computed := categoryOfFootprint footprint allow
    let (verdict, note) := reconcile info.category computed missing
    results := results.push {
      decl := declName, stage := info.stage, claimed := info.category
      computed, footprint, missing, verdict, note
    }
  return results

private def csv (names : Array Name) : String :=
  if names.isEmpty then "—" else String.intercalate ", " (names.toList.map (·.toString))

/-- Deterministic Markdown report. -/
def renderReport (results : Array NodeResult) (allow : NameSet) (allowPath : System.FilePath)
    (allowExists : Bool) : String := Id.run do
  let mut out := "# Blueprint Audit — machine-verified status\n\n"
  out := out ++ s!"Trusted-axiom allowlist: `{allowPath}`"
  out := out ++ (if allowExists then s!" ({allow.size} entr{if allow.size == 1 then "y" else "ies"})\n"
                 else " (not found → empty allowlist)\n")
  out := out ++ "Clean axioms (always allowed): `propext`, `Classical.choice`, `Quot.sound`\n\n"
  out := out ++ "| # | Node (tagged decl) | Stage theorem | Claimed | Computed | Verdict |\n"
  out := out ++ "|---:|---|---|---|---|---|\n"
  let mut idx := 0
  for r in results do
    idx := idx + 1
    out := out ++ s!"| {idx} | `{r.decl}` | `{r.stage}` | {r.claimed.toString} | {r.computed.toString} | {r.verdict.icon} |\n"
  out := out ++ "\n## Per-node footprints\n\n"
  for r in results do
    out := out ++ s!"### `{r.stage}` — {r.verdict.icon}\n"
    out := out ++ s!"- claimed `{r.claimed.toString}`, computed `{r.computed.toString}` — {r.note}\n"
    out := out ++ s!"- non-clean axioms: {csv (nonCleanAxioms r.footprint)}\n"
    out := out ++ s!"- full footprint: {csv r.footprint}\n\n"
  return out

/-- Whitespace trim via the stable `List Char` API (the `String.trim`/`Slice` API is mid-deprecation). -/
private def trimWs (s : String) : String :=
  String.ofList (s.toList.dropWhile (·.isWhitespace) |>.reverse.dropWhile (·.isWhitespace) |>.reverse)

def readAllowlist (path : System.FilePath) : IO (NameSet × Bool) := do
  if ← path.pathExists then
    let mut s := NameSet.empty
    for line in ← IO.FS.lines path do
      let t := trimWs line
      if t.isEmpty || t.startsWith "#" then continue
      s := s.insert t.toName
    return (s, true)
  else
    return (NameSet.empty, false)

unsafe def main (args : List String) : IO UInt32 := do
  let allowPath : System.FilePath := match args with
    | p :: _ => p
    | [] => defaultAllowlistPath
  let (allow, allowExists) ← readAllowlist allowPath
  -- Populate the module search path. Under `lake exe`, LEAN_PATH carries every lib dir (project +
  -- Mathlib + Foundation + toolchain), but `importModules` reads `searchPathRef`, which is NOT
  -- auto-initialized from the environment — so we seed it here (sysroot first, then LEAN_PATH).
  Lean.initSearchPath (← Lean.findSysroot)
  if let some lp ← IO.getEnv "LEAN_PATH" then
    Lean.searchPathRef.modify (System.SearchPath.parse lp ++ ·)
  -- Load the environment of the built library, running imported initializers so every
  -- environment extension (incl. the blueprint attribute + Mathlib/Foundation extensions) is
  -- registered before entries are replayed. Mirrors `checkdecls`.
  enableInitializersExecution
  let env ← importModules auditRoots {}
  let (results, _) ← (runAudit allow).toIO
    { fileName := "blueprint_audit", fileMap := default } { env := env }
  IO.print (renderReport results allow allowPath allowExists)
  -- A blueprint with zero nodes is a vacuous gate — treat it as a misconfiguration, not a pass.
  if results.isEmpty then
    IO.eprintln "\n✗ blueprint_audit FAILED — no @[goodstein_blueprint] nodes found (vacuous gate?)."
    return 1
  let fails := results.filter (·.verdict == .fail)
  let warns := results.filter (·.verdict == .warn)
  if fails.isEmpty then
    IO.println s!"\n✓ blueprint_audit PASSED — {results.size} node(s) consistent, {warns.size} warning(s)."
    return 0
  else
    IO.eprintln s!"\n✗ blueprint_audit FAILED — {fails.size}/{results.size} node(s) inconsistent."
    return 1

end BlueprintAudit

/-- Executable entry point. -/
unsafe def main (args : List String) : IO UInt32 :=
  BlueprintAudit.main args
