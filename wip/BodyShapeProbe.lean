import GoodsteinPA.OperatorZef2
import GoodsteinPA.WainerRoute
import GoodsteinPA.Embedding

/-! Probe: `goodsteinBodyE/[nm m]` head shape + Σ₁-ness (route-(c) root plumbing). -/

namespace GoodsteinPA.BodyShapeProbe

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

noncomputable def goodsteinBody : Semisentence ℒₒᵣ 1 :=
  “∃ N, !LO.FirstOrder.Arithmetic.igoodsteinDef 0 #1 N”

noncomputable def goodsteinBodyE : SyntacticSemiformula ℒₒᵣ 1 :=
  Rewriting.emb goodsteinBody

-- Probe 1: the instance is literally an ∃⁰ (rfl through the two rewrites)
example (m : ℕ) : ∃ χ : SyntacticSemiformula ℒₒᵣ 1,
    goodsteinBodyE/[nm m] = (∃⁰ χ) := ⟨_, rfl⟩

-- Probe 2: Σ₁-ness of the whole instance
example (m : ℕ) :
    Arithmetic.Hierarchy 𝚺 1 (goodsteinBodyE/[nm m]) := by
  apply Arithmetic.Hierarchy.rew
  apply Arithmetic.Hierarchy.rew
  simp [goodsteinBody]

end GoodsteinPA.BodyShapeProbe
