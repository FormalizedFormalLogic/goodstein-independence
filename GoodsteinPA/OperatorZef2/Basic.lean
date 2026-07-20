module

public import GoodsteinPA.OperatorZeh

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

variable {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-!
# `Zef2` — the `Nlog`-gated E–W controlled slot calculus

`Zef2` is `Zef` with a size gate `Nlog α ≤ f 0` carried on every node (and a cut-read gate
`φ.complexity ≤ f 0` on `cut`).  The gate controls the diagonal output slot's base-argument read
by the ordinal's constructor norm `Nlog`.

The forgetful map `Zef2.toZef` drops the gate — it is the conservativity witness, and discharges
the read-off exit by reuse of the `Zef` read-off.  The inversion suite is re-proven natively over
`Zef2` (the gate re-threads at each rebuilt node).

`Zef2` inherits `Zef`'s attribution.  The rule skeleton and the ordinal witness bound continue the
restricted infinitary calculus underlying `Zeh`/`Zef`.  The operator-controlled reading of the
derivation follows the `f, F ⊢^α_ρ Γ` judgment, whose side condition `N(α) ≤ f(0)` is the nearest
precedent for the `Nlog α ≤ f 0` gate carried here.  The per-node placement of the gate, the
concrete choice of norm (`Nlog`), and the additional cut-read gate `φ.complexity ≤ f 0` are
specific to this formalization.

- [Tow20, §13, §15]
- [EW12, Definition 23]
-/

/-- **`Zef2`** — the `Nlog`-gated function-slot cut-elimination calculus.  Identical to `Zef`
(`OperatorZeh.lean`) up to the size gate `hαN : Nlog α ≤ f 0` on every node and the cut-read gate
`hcutRead : φ.complexity ≤ f 0` on `cut`. -/
inductive Zef2 : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Finset (ArithmeticFormula ℕ) → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef2 α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2 α e H f c Δ) :
      Zef2 α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef2 β e H f c Δ) : Zef2 α e H f c Γ
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef2 (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef2 α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef2 β e H f c (insert (φ/[nm n]) Γ)) : Zef2 α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ : ArithmeticFormula ℕ) (hcompl : φ.complexity < c) (hcutRead : φ.complexity ≤ f 0)
      (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef2 βφ e H f c (insert φ Γ)) (d₂ : Zef2 βψ e H f c (insert (∼φ) Γ)) :
      Zef2 α e H f c Γ

namespace Zef2

/-- **Gate projection** — every `Zef2` constructor exposes its conclusion gate `Nlog α ≤ f 0`, so
a derivation is its own certificate for the size bound.  The uniform lever for re-threading the
gate through the reduction / inversion. -/
lemma gate (dd : Zef2 α e H f c Γ) : Nlog α ≤ f 0 := by
  cases dd <;> assumption

lemma weakening {Δ : Finset (ArithmeticFormula ℕ)}
    (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2 α e H f c Δ) :
    Zef2 α e H f c Γ :=
  Zef2.wk hαN hsub dd

/-- **Slot weakening** (`mono_f`): a larger slot is more permissive (all gates ride `f 0 ≤ f' 0`;
`exI` bound rides it too; `allω` rides `rel1_mono`). -/
lemma mono_f (dd : Zef2 α e H f c Γ) {f' : ℕ → ℕ} (hff' : ∀ x, f x ≤ f' x) : Zef2 α e H f' c Γ := by
  induction dd generalizing f' with
  | axL hαN r v hp hn =>
      exact Zef2.axL (le_trans hαN (hff' 0)) r v hp hn
  | wk hαN hsub _ ih =>
      exact Zef2.wk (le_trans hαN (hff' 0)) hsub (ih hff')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2.weak (le_trans hαN (hff' 0)) hβ hβNF hαNF hβH hsub (ih hff')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      exact Zef2.allω (le_trans hαN (hff' 0)) φ β hβ hβNF hαNF hβH
        (fun n => ih n (rel1_mono hff' n))
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zef2.exI (le_trans hαN (hff' 0)) φ n hβ hβNF hαNF hβH
        (le_trans hbound (hff' 0)) (ih hff')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef2.cut (le_trans hαN (hff' 0)) φ hcompl (le_trans hcutRead (hff' 0))
        hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hff') (ih₂ hff')

/-- **Operator irrelevance** (R1): the generator slot `H` carries no information. -/
lemma change_H (dd : Zef2 α e H f c Γ) {H' : ONote → Prop} : Zef2 α e H' f c Γ := by
  induction dd generalizing H' with
  | axL hαN r v hp hn => exact Zef2.axL hαN r v hp hn
  | wk hαN hsub _ ih => exact Zef2.wk hαN hsub ih
  | weak hαN hβ hβNF hαNF _ hsub _ ih =>
      exact Zef2.weak hαN hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | allω hαN φ β hβ hβNF hαNF _ _ ih =>
      exact Zef2.allω hαN φ β hβ hβNF hαNF
        (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI hαN φ n hβ hβNF hαNF _ hbound _ ih =>
      exact Zef2.exI hαN φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      exact Zef2.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

/-- Combined operator+slot move. -/
lemma mono_Hf (dd : Zef2 α e H f c Γ) {H' : ONote → Prop} {f' : ℕ → ℕ} (hff' : ∀ x, f x ≤ f' x) :
    Zef2 α e H' f' c Γ := (dd.change_H).mono_f hff'

/-- **`toZef`** — the forgetful map dropping the `Nlog`/cut-read gate (the mandated read-off route;
doubles as the conservativity witness `Zef2 ⤳ Zef`). -/
lemma toZef (dd : Zef2 α e H f c Γ) : Zef α e H f c Γ := by
  induction dd with
  | axL _ r v hp hn => exact Zef.axL r v hp hn
  | wk _ hsub _ ih => exact Zef.wk hsub ih
  | weak _ hβ hβNF hαNF hβH hsub _ ih => exact Zef.weak hβ hβNF hαNF hβH hsub ih
  | allω _ φ β hβ hβNF hαNF hβH _ ih => exact Zef.allω φ β hβ hβNF hαNF hβH (fun n => ih n)
  | exI _ φ n hβ hβNF hαNF hβH hbound _ ih => exact Zef.exI φ n hβ hβNF hαNF hβH hbound ih
  | cut _ φ hcompl _ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

end Zef2

/-- The `≤`-slack wrapper (slot form of `ZehProv`), carrying the `Nlog` gate on the witness. -/
def Zef2Prov (α e : ONote) (H : ONote → Prop) (f : ℕ → ℕ) (c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Nlog α' ≤ f 0 ∧ Zef2 α' e H f c Γ

namespace Zef2Prov

lemma of (hNF : α.NF) (hH : Cl H α) (hN : Nlog α ≤ f 0) (D : Zef2 α e H f c Γ) :
    Zef2Prov α e H f c Γ :=
  ⟨α, le_refl _, hNF, hH, hN, D⟩

lemma mono {β : ONote} (hα : α ≤ β) : Zef2Prov α e H f c Γ → Zef2Prov β e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, hN, D⟩

lemma weakening {Δ : Finset (ArithmeticFormula ℕ)}
    (h : Γ ⊆ Δ) : Zef2Prov α e H f c Γ → Zef2Prov α e H f c Δ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', hα', hNF, hH, hN, D.wk hN h⟩

/-- Forget the gate: `Zef2Prov ⤳ ZefProv`. -/
lemma toZefProv : Zef2Prov α e H f c Γ → ZefProv α e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, _, D⟩
  exact ⟨α', hα', hNF, hH, D.toZef⟩

end Zef2Prov

/-! ## The read-off exit, discharged by the forgetful map -/

/-- Mirrors `ReadoffShapeF` (`OperatorZeh.lean`) for `Zef2`; the witness-read-off shape follows
the restricted infinitary calculus's cut-elimination read-off.

- [Tow20, §17, Theorem 17.1]
-/
def ReadoffShapeF2 (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ReadoffShapeF φ f Γ

/-- Mirrors `ReadoffGoalF` (`OperatorZeh.lean`) for `Zef2`; the witness-read-off goal follows
the restricted infinitary calculus's cut-elimination read-off.

- [Tow20, §17, Theorem 17.1]
-/
def ReadoffGoalF2 (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ReadoffGoalF φ f Γ

/-- **`readoff_sigma1_Zef2`** — the `Nlog`-gated read-off, discharged by reuse of the `Zef` read-off
through `toZef` (zero re-proof; the gate is read-off-irrelevant). -/
lemma readoff_sigma1_Zef2 {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (dd : Zef2 α e H f c Γ) (hc : c = 0) (hshape : ReadoffShapeF2 φ f Γ) :
    ReadoffGoalF2 φ f Γ :=
  readoff_sigma1_Zef hφinst dd.toZef hc hshape

/-- **`headline_readoff_Zef2`** — the exit witness, discharged through `toZef`. -/
lemma headline_readoff_Zef2 {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (dd : Zef2 α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n]) :=
  headline_readoff_Zef hφinst dd.toZef

end GoodsteinPA.OperatorZeh
