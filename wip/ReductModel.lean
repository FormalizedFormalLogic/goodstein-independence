/-
# `ReductModel.lean` — the `ℒₒᵣ`-reduct of a model of `paLX` is an `𝗜𝚺₁` model (lap-31)

**Why this brick.** The lap-30 completeness redirect (`DescentSemantic.lean`) reduces the whole
headline to proving, for every model `M ⊧ paLX`, the model-internal Rathjen §3 argument — which is
carried out in `M`'s `ℒₒᵣ`-reduct using the lap-26 internal Goodstein substrate
(`igoodstein`/`ibump`), and that substrate lives over `[ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]`. So before any
of it can run, `M`'s reduct must be presented as such a model. This file does exactly that.

**The equality subtlety (lap-31 correction to the lap-30 plan).** The Tait completeness theorem
`Derivation.completeness_of_encodable` quantifies its semantic premise over models `M` whose `=`-symbol
need NOT be real Lean equality (it is merely whatever `Structure LX M` interprets it as). The internal
substrate needs *real* equality (it is plain Lean arithmetic over `V`). So the honest precondition for
the reduct-to-`𝗜𝚺₁` bridge is `[Structure.Eq LX M]` — i.e. `M` interprets `=` as real equality. This
is supplied by routing the final derivation through the equality-respecting completeness
(`EQ.provOf` over `[Structure.Eq]`-models), which is sound because `TI prec` is closed
(`freeVariables_TI = ∅`) hence a sentence. See `DESCENT-PLAN.md §6` / `PENDING_WORK.md` lap-31.

The two deliverables here are pure model theory (zero Goodstein content), reusable, `#print axioms`-clean:
- `reductORing` : the `ORingStructure M` read off `M`'s `LX`-interpretation of the ring/order symbols.
- `reduct_eq_standardModel` : `M`'s reduct `inst.lMap Φ` IS the `standardModel` of `reductORing`.
- `reduct_models_PA` / `reduct_models_isigma1` : `M ⊧ paLX ⟹ M ⊧ 𝗣𝗔 ⟹ M ⊧ 𝗜𝚺₁` in the reduct.
-/
import GoodsteinPA.DescentLift
import GoodsteinPA.Compat

namespace GoodsteinPA.ReductModel

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA GoodsteinPA.LangX GoodsteinPA.DescentLift

variable {M : Type} [inst : Structure LX M]

/-- **The `ORingStructure` on `M` read off its `LX`-reduct.** Each ring/order symbol of `ℒₒᵣ` is sent
by `Φ = ORing.embedding LX` to the corresponding `LX`-symbol, and we take its `M`-interpretation. By
construction this makes `inst.lMap Φ` agree with the canonical `standardModel` of `reductORing`
(`reduct_eq_standardModel`). -/
@[reducible]
noncomputable def reductORing : ORingStructure M where
  zero := (inst.lMap Φ).func Language.Zero.zero ![]
  one := (inst.lMap Φ).func Language.One.one ![]
  add a b := (inst.lMap Φ).func Language.Add.add ![a, b]
  mul a b := (inst.lMap Φ).func Language.Mul.mul ![a, b]
  lt a b := (inst.lMap Φ).rel Language.LT.lt ![a, b]

/-- **`M`'s reduct is the standard model of `reductORing`.** Under the honest precondition that `M`
interprets `=` as real equality (`[Structure.Eq LX M]`), the reduct `inst.lMap Φ` coincides with the
canonical `standardModel M` of the read-off `ORingStructure` — by `standardModel_unique`, since each
symbol's interpretation matches by construction. -/
theorem reduct_eq_standardModel [Nonempty M] [Structure.Eq LX M] :
    inst.lMap Φ = @standardModel M reductORing := by
  letI : ORingStructure M := reductORing
  letI sM : Structure ℒₒᵣ M := inst.lMap Φ
  haveI : Structure.Zero ℒₒᵣ M :=
    ⟨by simp [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq]; rfl⟩
  haveI : Structure.One ℒₒᵣ M :=
    ⟨by simp [Semiterm.Operator.val, Semiterm.Operator.One.term_eq]; rfl⟩
  haveI : Structure.Add ℒₒᵣ M := ⟨fun a b => by
    simp [Semiterm.Operator.val, Semiterm.Operator.Add.term_eq, Semiterm.val_func,
      Matrix.fun_eq_vec_two]; rfl⟩
  haveI : Structure.Mul ℒₒᵣ M := ⟨fun a b => by
    simp [Semiterm.Operator.val, Semiterm.Operator.Mul.term_eq, Semiterm.val_func,
      Matrix.fun_eq_vec_two]; rfl⟩
  haveI : Structure.LT ℒₒᵣ M := ⟨fun a b => by
    simp [Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, Semiformula.eval_rel,
      Matrix.fun_eq_vec_two]; rfl⟩
  haveI : Structure.Eq ℒₒᵣ M := ⟨fun a b => by
    have h := Structure.Eq.eq (L := LX) (M := M) a b
    simp only [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.eval_rel, Semiterm.val_bvar,
      Structure.lMap_rel, Function.comp_def] at h ⊢
    exact h⟩
  exact standardModel_unique (M := M) sM

/-- **`M`'s reduct models `𝗣𝗔`.** From `M ⊧ paLX ⊇ lMap Φ 𝗣𝗔` (the lap-30 `lMap_PA_subset`), the
reduct satisfies `𝗣𝗔` symbol-by-symbol (`modelsTheory_onTheory₁`), and the reduct IS the standard
model (`reduct_eq_standardModel`). -/
theorem reduct_models_PA [Nonempty M] [Structure.Eq LX M]
  (hM : M↓[LX] ⊧* (GoodsteinPA.EmbeddingX.paLX : Theory LX)) :
    letI : ORingStructure M := reductORing
    M ⊧ₘ* (𝗣𝗔 : Theory ℒₒᵣ) := by
  letI : ORingStructure M := reductORing
  -- `M ⊧ lMap Φ 𝗣𝗔`
  have hlift : M↓[LX] ⊧* (Theory.lMap Φ 𝗣𝗔 : Theory LX) := models_of_ss hM lMap_PA_subset
  -- each `σ ∈ 𝗣𝗔` holds in the reduct: `M↓[LX] ⊧ lMap Φ σ` transfers to `(inst.lMap Φ) ⊧ σ`
  -- (`models_lMap`), and the reduct IS the standard model of `reductORing` (`reduct_eq_standardModel`)
  refine ⟨fun σ hσ => ?_⟩
  have h2 : (inst.lMap Φ).toStruc ⊧ σ :=
    Semiformula.models_lMap.mp (hlift.models _ (Set.mem_image_of_mem _ hσ))
  exact (reduct_eq_standardModel (M := M)) ▸ h2

/-- **`M`'s reduct models `𝗜𝚺₁`.** Immediate from `reduct_models_PA` via `𝗜𝚺₁ ⪯ 𝗣𝗔`
(`models_of_subtheory`). This is the `[V ⊧ₘ* 𝗜𝚺₁]` instance the internal Goodstein substrate runs over. -/
theorem reduct_models_isigma1 [Nonempty M] [Structure.Eq LX M]
  (hM : M↓[LX] ⊧* (GoodsteinPA.EmbeddingX.paLX : Theory LX)) :
    letI : ORingStructure M := reductORing
    M ⊧ₘ* (𝗜𝚺₁ : Theory ℒₒᵣ) := by
  letI : ORingStructure M := reductORing
  exact models_of_subtheory (reduct_models_PA (M := M) hM)

end GoodsteinPA.ReductModel
