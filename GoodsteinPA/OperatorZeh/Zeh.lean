module

public import GoodsteinPA.OperatorZeh.Operator

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## The minimal `Zeh` core

`Zeh α e H m c Γ` is an operator-controlled deduction of `Γ`, at ordinal `α` and cut rank `c`,
carrying a numeric stage `m` and an ordinal operator `H : ONote → Prop`.  The rule skeleton and
the `exI` witness bound (`n ≤ hardy e m`) follow the restricted infinitary calculus `Z∞`; the
ordinal operator `H` and its ω-node relativization (`adjoin`, `relOp`) follow the Buchholz-style
operator-controlled derivation methodology.  In this PA/`ε₀` setting `H` turns out to carry no
information (`Zeh.change_H`): it is inert, and only the function-slot form `Zef` (below) makes
operator control load-bearing.

- [Tow20, §13, §15]
- [EW12, §4, Definition 23]
-/
inductive Zeh : ONote → ONote → (ONote → Prop) → ℕ → ℕ → Finset (ArithmeticFormula ℕ) → Prop
  | axL {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {ar : ℕ}
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zeh α e H m c Γ
  | wk {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hsub : Δ ⊆ Γ) (dd : Zeh α e H m c Δ) : Zeh α e H m c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zeh β e H m c Δ) : Zeh α e H m c Γ
  | allω {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c (insert (φ/[nm n]) Γ)) :
      Zeh α e H m c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ hardy e m)
      (dd : Zeh β e H m c (insert (φ/[nm n]) Γ)) : Zeh α e H m c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticFormula ℕ) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zeh βφ e H m c (insert φ Γ)) (d₂ : Zeh βψ e H m c (insert (∼φ) Γ)) :
      Zeh α e H m c Γ

variable {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

namespace Zeh

/-- **`mono_H`** — the replacement for `Provable.mono_k`/`Provable.mono_d`: raise the generator set and
the stage together.  The `exI` bound rides `hardy_monotone` (argument monotonicity — no
ordinal-raise, hence no gate); memberships ride `Cl_mono`. -/
theorem mono_H (dd : Zeh α e H m c Γ) {H' : ONote → Prop} {m' : ℕ}
    (hH : ∀ β, H β → H' β) (hm : m ≤ m') : Zeh α e H' m' c Γ := by
  induction dd generalizing H' m' with
  | axL r v hp hn => exact Zeh.axL r v hp hn
  | wk hsub _ ih => exact Zeh.wk hsub (ih hH hm)
  | weak hβ hβNF hαNF hβH hsub _ ih =>
      exact Zeh.weak hβ hβNF hαNF (Cl_mono hH hβH) hsub (ih hH hm)
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      refine Zeh.allω φ β hβ hβNF hαNF
        (fun n => Cl_mono (fun γ hγ => hγ.imp_left (hH γ)) (hβH n))
        (fun n => ih n (fun γ hγ => hγ.imp_left (hH γ)) (max_le_max hm (le_refl n)))
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zeh.exI φ n hβ hβNF hαNF (Cl_mono hH hβH)
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hH hm)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zeh.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (Cl_mono hH hβφH) (Cl_mono hH hβψH)
        (ih₁ hH hm) (ih₂ hH hm)

/-- Sequent weakening (height-preserving). -/
theorem weakening {Δ : Finset (ArithmeticFormula ℕ)}
    (hsub : Δ ⊆ Γ) (dd : Zeh α e H m c Δ) : Zeh α e H m c Γ :=
  Zeh.wk hsub dd

/-- **Operator irrelevance (R1 realized in-kernel):** the generator slot `H` carries NO
information — every `Cl H β` side condition in a `Zeh` derivation is at an NF ordinal, and
`Cl_of_NF` supplies membership in the closure of ANY generator set.  So a derivation at
operator `H` is a derivation at any operator `H'`, SAME `(α, e, m, c, Γ)`.  This is the
strong form of `mono_H` that `mono_H` (which needs `H ⊆ H'`) cannot express: the operator is
freely replaceable in BOTH directions.  Discharges the operator-threading bookkeeping in the
f-slot reductions — the running relativization `adjoin H n` of the inversion family and the
ambient `H` of the ∃-side are interchangeable at will (membership is bookkeeping only). -/
theorem change_H (dd : Zeh α e H m c Γ) {H' : ONote → Prop} : Zeh α e H' m c Γ := by
  induction dd generalizing H' with
  | axL r v hp hn => exact Zeh.axL r v hp hn
  | wk hsub _ ih => exact Zeh.wk hsub ih
  | weak hβ hβNF hαNF _ hsub _ ih => exact Zeh.weak hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | allω φ β hβ hβNF hαNF _ _ ih =>
      exact Zeh.allω φ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI φ n hβ hβNF hαNF _ hbound _ ih =>
      exact Zeh.exI φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      exact Zeh.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

end Zeh

/-- The `≤`-slack bookkeeping wrapper (`ProvableSlack`'s twin with the NORM clause deleted —
the simplification the fork buys — and the ordinal's `Cl H`-membership carried instead:
"the judgment carries `α ∈ H` directly"). -/
def ZehProv (α e : ONote) (H : ONote → Prop) (m c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Zeh α' e H m c Γ

namespace ZehProv

theorem of (hNF : α.NF) (hH : Cl H α) (D : Zeh α e H m c Γ) : ZehProv α e H m c Γ :=
  ⟨α, le_refl _, hNF, hH, D⟩

theorem mono {β : ONote} (hα : α ≤ β) (D : ZehProv α e H m c Γ) : ZehProv β e H m c Γ := by
  obtain ⟨α', hα', hNF, hH, D⟩ := D
  exact ⟨α', le_trans hα' hα, hNF, hH, D⟩

theorem weakening {Δ : Finset (ArithmeticFormula ℕ)} (h : Γ ⊆ Δ) (D : ZehProv α e H m c Γ) :
    ZehProv α e H m c Δ := by
  obtain ⟨α', hα', hNF, hH, D⟩ := D
  exact ⟨α', hα', hNF, hH, D.wk h⟩

end ZehProv

/-! ## Structural monotonicity infrastructure (assembly plumbing)

Cut-rank monotonicity, mirroring the `Provable` suite (`OperatorZinfty.lean`), reused by the
rank-lowering elimination pass `cutElimPass_Zf` (which relates rank-`c+1` and rank-`c`
derivations).  Structural: does not consume the f-slot statements. -/

namespace Zeh

/-- **`c`-monotonicity** (cut rank): a derivation valid at rank `c` is valid at any `c' ≥ c`.
Only the `cut` rule reads `c` (via `hcompl : φ.complexity < c`), so every other case threads. -/
theorem mono_c (dd : Zeh α e H m c Γ) {c' : ℕ} (hc : c ≤ c') : Zeh α e H m c' Γ := by
  induction dd generalizing c' with
  | axL r v hp hn => exact Zeh.axL r v hp hn
  | wk hsub _ ih => exact Zeh.wk hsub (ih hc)
  | weak hβ hβNF hαNF hβH hsub _ ih => exact Zeh.weak hβ hβNF hαNF hβH hsub (ih hc)
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      exact Zeh.allω φ β hβ hβNF hαNF hβH (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zeh.exI φ n hβ hβNF hαNF hβH hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zeh.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁ hc) (ih₂ hc)

end Zeh

/-- **`ZehProv`-level cut combinator** (assembly plumbing, not the reduction itself): package
the cut rule at the wrapper level — combine proofs of `φ` and `∼φ` (with `φ.complexity < c`)
into a proof of `Γ` at ordinal `osucc (βφ + βψ)`, same rank and control (no rank-lowering, no
control-raise — those belong to `cutElimPass_Zf`/the reduction).  A step/reduction assembly
would reuse this to introduce cuts before eliminating them. -/
theorem ZehProv.cut {βφ βψ : ONote} (φ : ArithmeticFormula ℕ)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hcompl : φ.complexity < c)
    (D₁ : ZehProv βφ e H m c (insert φ Γ)) (D₂ : ZehProv βψ e H m c (insert (∼φ) Γ)) :
    ZehProv (osucc (βφ + βψ)) e H m c Γ := by
  obtain ⟨α₁, hle₁, hNF₁, hH₁, d₁⟩ := D₁
  obtain ⟨α₂, hle₂, hNF₂, hH₂, d₂⟩ := D₂
  refine ⟨osucc (α₁ + α₂),
    osucc_le_osucc (ONote.add_nf α₁ α₂) (ONote.add_nf βφ βψ)
      (add_le_add_NF hNF₁ hβφNF hNF₂ hβψNF hle₁ hle₂),
    osucc_add_NF hNF₁ hNF₂, osucc_add_mem hH₁ hH₂,
    Zeh.cut φ hcompl
      (lt_of_le_of_lt (Provable.le_add_right_NF hNF₁ hNF₂) (Provable.lt_osucc (ONote.add_nf α₁ α₂)))
      (lt_of_le_of_lt (Provable.le_add_left_NF hNF₁ hNF₂) (Provable.lt_osucc (ONote.add_nf α₁ α₂)))
      hNF₁ hNF₂ (osucc_add_NF hNF₁ hNF₂) hH₁ hH₂ d₁ d₂⟩

/-- **`ZehProv`-level `exI` combinator** (assembly plumbing): package the `∃`-rule at the
wrapper level — the output ordinal `osucc β` is fully determined, no rank/control change.
Reused by the assembly to introduce existentials at the prov level. -/
theorem ZehProv.exI {β : ONote}
    (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβNF : β.NF) (hβH : Cl H β)
    (hbound : n ≤ hardy e m) (D : ZehProv β e H m c (insert (φ/[nm n]) Γ)) :
    ZehProv (osucc β) e H m c (insert (∃⁰ φ) Γ) := by
  obtain ⟨β', hle, hNF', hH', d⟩ := D
  exact ⟨osucc β, le_rfl, osucc_NF hβNF, Cl.osucc hβH,
    Zeh.exI φ n (lt_of_le_of_lt hle (Provable.lt_osucc hβNF)) hNF' (osucc_NF hβNF) hH' hbound d⟩

/-- **`ZehProv`-level `allω` combinator** (assembly plumbing): reassemble an ω-node at the
wrapper level.  Each branch's `≤`-slack witness is threaded through (`< α` survives since
`β' n ≤ β n < α`); the output witness is `α` itself (needs `Cl H α`).  Reused by the
assembly to rebuild ω-nodes over the branch family. -/
theorem ZehProv.allω (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
    (hβ : ∀ n, β n < α) (hαNF : α.NF) (hαH : Cl H α)
    (D : ∀ n, ZehProv (β n) e (adjoin H n) (max m n) c (insert (φ/[nm n]) Γ)) :
    ZehProv α e H m c (insert (∀⁰ φ) Γ) :=
  ⟨α, le_rfl, hαNF, hαH,
    Zeh.allω φ (fun n => (D n).choose)
      (fun n => lt_of_le_of_lt (D n).choose_spec.1 (hβ n))
      (fun n => (D n).choose_spec.2.1)
      hαNF
      (fun n => (D n).choose_spec.2.2.1)
      (fun n => (D n).choose_spec.2.2.2)⟩

end GoodsteinPA.OperatorZeh
