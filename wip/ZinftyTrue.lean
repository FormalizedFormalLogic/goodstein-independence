/-
# Truth-layer semantic core for `Z_∞` (toward the M5 `axTrue` surgery)

**Constructor-independent prototype** for the truth layer that M5's `Deriv` needs in order to host
the M4 embedding (see `ANALYSIS-2026-06-22-truth-layer-gap.md`). The atomic-truth axiom `axTrue` and
the false-literal removal `removeFalseLiteralAux` both pivot on a single semantic primitive: the
ℕ-truth of a closed literal, together with its classical totality and `∼`-duality. Those are proved
here against the standard model, with NO change to `Deriv` (so `src/` stays green). The surgery
(next lap) adds the constructor and threads the 9 `Deriv` recursion sites, consuming these lemmas in
the leaf / atomic-cut cases.

`lake env lean wip/ZinftyTrue.lean` — expect no errors.
-/
import GoodsteinPA.Zinfty

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder

/-- **ℕ-truth of a closed formula** (used on closed literals `rel r v` / `nrel r v`). The standard
ℒₒᵣ-model evaluation with no bound variables; for a *closed* formula the free-variable assignment is
immaterial (we fix `id`). This is the truth side condition the ω-logic atomic-truth axiom carries:
`axTrue L (h : LitTrue L) (L ∈ Γ)` will close any sequent containing a true closed literal. -/
def LitTrue (φ : Form) : Prop := Semiformula.Evalm ℕ ![] (id : ℕ → ℕ) φ

/-- **`∼`-duality.** A closed formula is true iff its negation is false. The atomic-cut truth layer
turns "cut atom `A` is true" into "`∼A` is a removable *false* literal". -/
@[simp] theorem litTrue_neg (φ : Form) : LitTrue (∼φ) ↔ ¬ LitTrue φ := by
  unfold LitTrue; simp

/-- **Totality** (classical): every closed literal is true or its negation is. This is the case
split `atomCutAux` performs on the cut atom. -/
theorem litTrue_or_neg (φ : Form) : LitTrue φ ∨ LitTrue (∼φ) := by
  rw [litTrue_neg]; exact em _

/-- **Consistency** of the truth axiom: no closed literal and its negation are both true, so
`axTrue` can never close a sequent two ways into a contradiction (soundness sanity for the surgery). -/
theorem not_litTrue_and_neg (φ : Form) : ¬ (LitTrue φ ∧ LitTrue (∼φ)) := by
  rw [litTrue_neg]; tauto

/-- `∼∼φ`-collapse at the truth level (literals come as `rel`/`nrel`, and the atomic-cut reduction
flips polarity once): `LitTrue (∼∼φ) ↔ LitTrue φ`. -/
theorem litTrue_neg_neg (φ : Form) : LitTrue (∼∼φ) ↔ LitTrue φ := by
  simp

end GoodsteinPA.ZinftyF
