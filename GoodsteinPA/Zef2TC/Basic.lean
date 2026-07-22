module

public import GoodsteinPA.ToMathlib.Goodstein.CichonCaicedo
public import GoodsteinPA.ToMathlib.Hardy.Gexp
public import GoodsteinPA.Encoding
public import GoodsteinPA.ToFoundation.Numeral
public import GoodsteinPA.ToFoundation.Subst
public import GoodsteinPA.ReadoffValueGate

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote Ordinal
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-! ## `Zef2TC` — the full-rule-set target calculus -/

/-- **`Zef2TC`** — `Zef2` (verbatim, `Nlog` gates) + E–W (Ax2) (`trueRel`/`trueNrel`) + the
finite connective rules `verumR`/`andI`/`orI` (`Provable` shapes; ordinal-descending premises with
the `weak`-style NF/`Cl` side conditions; slot UNCHANGED — E–W relativizes only the ω-rule). -/
inductive Zef2TC : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Finset (ArithmeticFormula ℕ) → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef2TC α e H f c Γ
  | trueRel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hmem : Semiformula.rel r v ∈ Γ) : Zef2TC α e H f c Γ
  | trueNrel {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hmem : Semiformula.nrel r v ∈ Γ) : Zef2TC α e H f c Γ
  | verumR {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0) (h : (⊤ : ArithmeticFormula ℕ) ∈ Γ) : Zef2TC α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2TC α e H f c Δ) :
      Zef2TC α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef2TC β e H f c Δ) : Zef2TC α e H f c Γ
  | andI {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ ψ : ArithmeticFormula ℕ) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (dφ : Zef2TC βφ e H f c (insert φ Γ)) (dψ : Zef2TC βψ e H f c (insert ψ Γ)) :
      Zef2TC α e H f c (insert (φ ⋏ ψ) Γ)
  | orI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ ψ : ArithmeticFormula ℕ) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (dd : Zef2TC β e H f c (insert φ (insert ψ Γ))) :
      Zef2TC α e H f c (insert (φ ⋎ ψ) Γ)
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef2TC (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef2TC α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef2TC β e H f c (insert (φ/[nm n]) Γ)) : Zef2TC α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (hαN : Nlog α ≤ f 0)
      (φ : ArithmeticFormula ℕ) (hcompl : φ.complexity < c) (hcutRead : φ.complexity ≤ f 0)
      (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef2TC βφ e H f c (insert φ Γ)) (d₂ : Zef2TC βψ e H f c (insert (∼φ) Γ)) :
      Zef2TC α e H f c Γ

namespace Zef2TC

variable {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

theorem gate (dd : Zef2TC α e H f c Γ) : Nlog α ≤ f 0 := by
  cases dd <;> assumption

/-- `Zef2 ⊆ Zef2TC`. -/
theorem ofZef2 (dd : Zef2 α e H f c Γ) : Zef2TC α e H f c Γ := by
  induction dd with
  | axL hαN r v hp hn => exact Zef2TC.axL hαN r v hp hn
  | wk hαN hsub _ ih => exact Zef2TC.wk hαN hsub ih
  | weak hαN hβ hβNF hαNF hβH hsub _ ih => exact Zef2TC.weak hαN hβ hβNF hαNF hβH hsub ih
  | allω hαN φ β hβ hβNF hαNF hβH _ ih => exact Zef2TC.allω hαN φ β hβ hβNF hαNF hβH ih
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      exact Zef2TC.exI hαN φ n hβ hβNF hαNF hβH hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef2TC.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

end Zef2TC
namespace Zef2TC

variable {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-- Slot monotonicity (port of `Zef2.mono_f` over the full rule set). -/
theorem mono_f (dd : Zef2TC α e H f c Γ) : ∀ {f' : ℕ → ℕ}, (∀ x, f x ≤ f' x) → Zef2TC α e H f' c Γ := by
  induction dd with
  | axL hαN r v hp hn =>
      intro f' hff'; exact .axL (le_trans hαN (hff' 0)) r v hp hn
  | trueRel hαN r v htrue hmem =>
      intro f' hff'; exact .trueRel (le_trans hαN (hff' 0)) r v htrue hmem
  | trueNrel hαN r v htrue hmem =>
      intro f' hff'; exact .trueNrel (le_trans hαN (hff' 0)) r v htrue hmem
  | verumR hαN h => intro f' hff'; exact .verumR (le_trans hαN (hff' 0)) h
  | wk hαN hsub _ ih => intro f' hff'; exact .wk (le_trans hαN (hff' 0)) hsub (ih hff')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro f' hff'; exact .weak (le_trans hαN (hff' 0)) hβ hβNF hαNF hβH hsub (ih hff')
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact .andI (le_trans hαN (hff' 0)) φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁ hff') (ih₂ hff')
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro f' hff'; exact .orI (le_trans hαN (hff' 0)) φ ψ hβ hβNF hαNF hβH (ih hff')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro f' hff'
      exact .allω (le_trans hαN (hff' 0)) φ β hβ hβNF hαNF hβH
        (fun n => ih n (rel1_mono hff' n))
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro f' hff'
      exact .exI (le_trans hαN (hff' 0)) φ n hβ hβNF hαNF hβH
        (le_trans hbound (hff' 0)) (ih hff')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact .cut (le_trans hαN (hff' 0)) φ hcompl (le_trans hcutRead (hff' 0))
        hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hff') (ih₂ hff')

/-- Cut-rank monotonicity (only `cut` mentions `c`). -/
theorem mono_c (dd : Zef2TC α e H f c Γ) : ∀ {c'}, c ≤ c' → Zef2TC α e H f c' Γ := by
  induction dd with
  | axL hαN r v hp hn => intro c' _; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro c' _; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro c' _; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro c' _; exact .verumR hαN h
  | wk hαN hsub _ ih => intro c' hcc; exact .wk hαN hsub (ih hcc)
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro c' hcc; exact .weak hαN hβ hβNF hαNF hβH hsub (ih hcc)
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hcc
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hcc) (ih₂ hcc)
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro c' hcc; exact .orI hαN φ ψ hβ hβNF hαNF hβH (ih hcc)
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro c' hcc; exact .allω hαN φ β hβ hβNF hαNF hβH (fun n => ih n hcc)
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro c' hcc; exact .exI hαN φ n hβ hβNF hαNF hβH hbound (ih hcc)
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hcc
      exact .cut hαN φ (lt_of_lt_of_le hcompl hcc) hcutRead hβφ hβψ hβφNF hβψNF hαNF
        hβφH hβψH (ih₁ hcc) (ih₂ hcc)

/-- Operator swap (port of `Zef2.change_H`; `Cl_of_NF` supplies every `Cl` obligation). -/
theorem change_H (dd : Zef2TC α e H f c Γ) : ∀ {H' : ONote → Prop}, Zef2TC α e H' f c Γ := by
  induction dd with
  | axL hαN r v hp hn => intro H'; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro H'; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro H'; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro H'; exact .verumR hαN h
  | wk hαN hsub _ ih => intro H'; exact .wk hαN hsub ih
  | weak hαN hβ hβNF hαNF _ hsub _ ih =>
      intro H'; exact .weak hαN hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂
  | orI hαN φ ψ hβ hβNF hαNF _ _ ih =>
      intro H'; exact .orI hαN φ ψ hβ hβNF hαNF (Cl_of_NF hβNF) ih
  | allω hαN φ β hβ hβNF hαNF _ _ ih =>
      intro H'
      exact .allω hαN φ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI hαN φ n hβ hβNF hαNF _ hbound _ ih =>
      intro H'; exact .exI hαN φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'
      exact .cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

/-- Control-ordinal swap: `e` is a phantom index of the derivation relation (no rule inspects
it), so a derivation transports to ANY control ordinal.  (The control ordinal only acquires
meaning in the cut-elimination pass, where it drives the `ewIter`/`hardy` slot arithmetic.) -/
theorem change_e (dd : Zef2TC α e H f c Γ) : ∀ (e' : ONote), Zef2TC α e' H f c Γ := by
  induction dd with
  | axL hαN r v hp hn => intro e'; exact .axL hαN r v hp hn
  | trueRel hαN r v htrue hmem => intro e'; exact .trueRel hαN r v htrue hmem
  | trueNrel hαN r v htrue hmem => intro e'; exact .trueNrel hαN r v htrue hmem
  | verumR hαN h => intro e'; exact .verumR hαN h
  | wk hαN hsub _ ih => intro e'; exact .wk hαN hsub (ih e')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro e'; exact .weak hαN hβ hβNF hαNF hβH hsub (ih e')
  | andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro e'
      exact .andI hαN φ ψ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ e') (ih₂ e')
  | orI hαN φ ψ hβ hβNF hαNF hβH _ ih =>
      intro e'; exact .orI hαN φ ψ hβ hβNF hαNF hβH (ih e')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro e'; exact .allω hαN φ β hβ hβNF hαNF hβH (fun n => ih n e')
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro e'; exact .exI hαN φ n hβ hβNF hαNF hβH hbound (ih e')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro e'
      exact .cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ e') (ih₂ e')

end Zef2TC

/-! ### `Nlog`/slot toolkit for the ordinal joins -/

/-- The `K`-relativized root slot dominates a smaller-budget one: `e₁ < e` (with
`norm e₁ ≤ B`), `B₁ ≤ B`, `K₁ ≤ K` give pointwise domination.  The `norm e₁ ≤ B`
side condition is exactly `hardy_le_of_lt`'s budget gate, absorbed into the structural `B`. -/
theorem relSlot_le {e₁ e} (he₁ : e₁.NF) (he : e.NF) (hlt : e₁ < e)
    {B₁ B K₁ K : ℕ} (hB : B₁ ≤ B) (hK : K₁ ≤ K) (hnorm : norm e₁ ≤ B) (x : ℕ) :
    rel1 (ewRootSlot e₁ B₁) K₁ x ≤ rel1 (ewRootSlot e B) K x := by
  simp only [rel1, ewRootSlot]
  have harg : max B₁ (max K₁ x) ≤ max B (max K x) :=
    max_le_max hB (max_le_max hK le_rfl)
  have h1 : hardy e₁ (max B₁ (max K₁ x)) ≤ hardy e₁ (max B (max K x)) :=
    hardy_monotone e₁ harg
  have h2 : hardy e₁ (max B (max K x)) ≤ hardy e (max B (max K x)) :=
    hardy_le_of_lt he₁ he hlt (le_trans hnorm (le_max_left _ _))
  have h3 : max K₁ x ≤ max K x := max_le_max hK le_rfl
  omega

/-- Same-`e` slot monotonicity in `(B, K)`. -/
theorem relSlot_mono {e} {B₁ B K₁ K : ℕ} (hB : B₁ ≤ B) (hK : K₁ ≤ K) (x : ℕ) :
    rel1 (ewRootSlot e B₁) K₁ x ≤ rel1 (ewRootSlot e B) K x := by
  simp only [rel1, ewRootSlot]
  have h1 : hardy e (max B₁ (max K₁ x)) ≤ hardy e (max B (max K x)) :=
    hardy_monotone e (max_le_max hB (max_le_max hK le_rfl))
  have h3 : max K₁ x ≤ max K x := max_le_max hK le_rfl
  omega

/-- One `K`-rung buys `+2` of root-gate slack (the `2·(x + …)` slot shape). -/
theorem relSlot_succ_gap (e : ONote) (B M : ℕ) :
    rel1 (ewRootSlot e B) M 0 + 2 ≤ rel1 (ewRootSlot e B) (M + 1) 0 := by
  simp only [rel1, ewRootSlot]
  have h1 : hardy e (max B (max M 0)) ≤ hardy e (max B (max (M + 1) 0)) :=
    hardy_monotone e (max_le_max le_rfl (max_le_max (Nat.le_succ M) le_rfl))
  have h2 : max M 0 + 1 ≤ max (M + 1) 0 := by omega
  omega

/-- The structural budget `B` is readable off the slot at `0`. -/
theorem le_relSlot_zero (e : ONote) (B K : ℕ) : B ≤ rel1 (ewRootSlot e B) K 0 := by
  simp only [rel1, ewRootSlot]
  have h1 := le_hardy e (max B (max K 0))
  have h2 : B ≤ max B (max K 0) := le_max_left _ _
  omega
/-- Every `Cl (⊤)` obligation is free. -/
theorem clT (β : ONote) : Cl (fun _ : ONote => True) β := Cl.base trivial
/-- The relativization index is readable off the slot at `0`. -/
theorem index_le_relSlot_zero (e : ONote) (B K : ℕ) : K ≤ rel1 (ewRootSlot e B) K 0 := by
  simp only [rel1, ewRootSlot]
  omega

end GoodsteinPA.E1EmbeddingGrind
