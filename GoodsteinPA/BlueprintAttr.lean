import Lean

namespace GoodsteinPA.Blueprint

open Lean Elab

/-- The audit category claimed by blueprint metadata.

The audit tool computes the real category from the kernel axiom footprint and checks this claim. -/
inductive BlueprintCategory where
  | clean
  | trusted
  | debt
  | broken
  deriving BEq, Inhabited, Repr

namespace BlueprintCategory

def toString : BlueprintCategory → String
  | clean => "clean"
  | trusted => "trusted"
  | debt => "debt"
  | broken => "broken"

end BlueprintCategory

/-- Machine-readable blueprint metadata attached to a Lean declaration.  This is
planning/review metadata, not proof content. -/
structure BlueprintInfo where
  order : Nat
  category : BlueprintCategory
  kind : String
  laps : String
  confidence : Nat
  stage : Name
  uses : Array Name := #[]
  evidence : Array String := #[]
  summary : String
  deriving Inhabited, Repr

declare_syntax_cat blueprintNames
syntax "[" ident,* "]" : blueprintNames

declare_syntax_cat blueprintEvidence
syntax "[" str,* "]" : blueprintEvidence

declare_syntax_cat blueprintCategory
syntax "clean" : blueprintCategory
syntax "trusted" : blueprintCategory
syntax "debt" : blueprintCategory
syntax "broken" : blueprintCategory

syntax (name := goodstein_blueprint)
  "goodstein_blueprint" num blueprintCategory str str num ident blueprintNames blueprintEvidence str : attr

private def elabCategory : TSyntax `blueprintCategory → CoreM BlueprintCategory
  | `(blueprintCategory| clean) => pure .clean
  | `(blueprintCategory| trusted) => pure .trusted
  | `(blueprintCategory| debt) => pure .debt
  | `(blueprintCategory| broken) => pure .broken
  | _ => throwUnsupportedSyntax

private def elabNameArray : TSyntax `blueprintNames → CoreM (Array Name)
  | `(blueprintNames| [$[$ids:ident],*]) =>
      ids.mapM fun id => withRef id do
        realizeGlobalConstNoOverloadWithInfo id
  | _ => throwUnsupportedSyntax

private def elabEvidenceArray : TSyntax `blueprintEvidence → CoreM (Array String)
  | `(blueprintEvidence| [$[$items:str],*]) => pure <| items.map (·.getString)
  | _ => throwUnsupportedSyntax

/-- The project-local blueprint attribute.  It deliberately keeps proof metadata in
Lean, attached to the declaration it describes, while leaving all estimates outside
the kernel. -/
initialize blueprintAttr : ParametricAttribute BlueprintInfo ←
  registerParametricAttribute {
    name := `goodstein_blueprint
    descr := "GoodsteinPA blueprint metadata for milestone/report generation"
    getParam := fun _ stx => do
      match stx with
      | `(attr| goodstein_blueprint
          $order:num
          $category:blueprintCategory
          $kind:str
          $laps:str
          $confidence:num
          $stage:ident
          $uses:blueprintNames
          $evidence:blueprintEvidence
          $summary:str) =>
          let stageName ← withRef stage do
            realizeGlobalConstNoOverloadWithInfo stage
          pure {
            order := order.getNat
            category := ← elabCategory category
            kind := kind.getString
            laps := laps.getString
            confidence := confidence.getNat
            stage := stageName
            uses := ← elabNameArray uses
            evidence := ← elabEvidenceArray evidence
            summary := summary.getString
          }
      | _ => throwUnsupportedSyntax
  }

private def collectEntries (env : Environment) : Array (Name × BlueprintInfo) :=
  Id.run do
    let mut entries := #[]
    for (declName, _) in env.constants do
      if let some info := blueprintAttr.getParam? env declName then
        entries := entries.push (declName, info)
    entries.qsort fun a b => a.2.order < b.2.order

private def namesCell (names : Array Name) : String :=
  if names.isEmpty then "none" else String.intercalate "<br>" (names.toList.map (·.toString))

private def evidenceBlock (items : Array String) : String :=
  if items.isEmpty then "  - none\n" else
    String.join <| items.toList.map fun item => s!"  - {item}\n"

/-- Render a deterministic Markdown report for all non-proved blueprint entries in
the current Lean environment. -/
def renderMarkdown (title : String) : CoreM String := do
  let env ← getEnv
  let entries := (collectEntries env).filter fun e => e.2.category != .clean
  let mut out := s!"# {title}\n\n"
  out := out ++ "Generated from `@[goodstein_blueprint ...]` attributes in Lean declarations.\n\n"
  out := out ++ "| # | Declaration | Stage theorem | Category | Laps | Confidence | Uses |\n"
  out := out ++ "|---:|---|---|---:|---:|---:|---|\n"
  for (declName, info) in entries do
    out := out ++
      s!"| {info.order} | `{declName}` | `{info.stage}` | {info.category.toString} | {info.laps} | {info.confidence}% | {namesCell info.uses} |\n"
  out := out ++ "\n## Outline\n\n"
  for (declName, info) in entries do
    out := out ++ s!"### {info.order}. `{declName}`\n\n"
    out := out ++ s!"- Stage theorem: `{info.stage}`\n"
    out := out ++ s!"- Kind: `{info.kind}`\n"
    out := out ++ s!"- Category claim: `{info.category.toString}`\n"
    out := out ++ s!"- Estimate: {info.laps} laps, {info.confidence}% confidence\n"
    out := out ++ s!"- Summary: {info.summary}\n"
    out := out ++ "- Literature / evidence:\n"
    out := out ++ evidenceBlock info.evidence
    out := out ++ "\n"
  out := out ++ "## Audit\n\n"
  out := out ++ "Run the stage theorem through `#print axioms` to see the actual kernel-level open assumptions."
  pure out

end GoodsteinPA.Blueprint
