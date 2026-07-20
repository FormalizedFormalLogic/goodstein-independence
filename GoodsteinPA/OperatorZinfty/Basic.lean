/-
# `Provable` — a witness-bounded refinement of Towsner's `Z_∞` calculus

A witness-bounded refinement `Provable ⊢^{α,e}_{k,d,c} Γ` of Towsner's restricted infinitary
deduction `Z_∞ ⊢^{α,k}_c Γ`: derivations bounded jointly by a derivation ordinal `α` and a
numeric gate `k`, together with the PA embedding and the numerically-controlled cut-elimination
that raises `k` through the Hardy hierarchy at every cut. Base rules, ordinal/numeric bounds,
and cut rank follow the literature design.

A calculus whose `exI` witness bound is tied directly to the derivation ordinal `α` cannot absorb
the witness growth under cut-elimination: the principal `exI` cut's witness `hardy γ(·)` grows
super-linearly through commuting `ω`-rules, while cut-elimination only grows `α ↦ α + γ`. The
`d`-bump `d ↦ d + norm α` alone closes the norm-budget obstruction but not this witness-index one.

**Two formalization-specific extensions.** (i) The `k + d` budget split. (ii) A control ordinal
`e` decoupling the `exI` witness bound from the derivation ordinal `α`: the witness bound becomes
`n ≤ hardy e (k + d)` instead of `hardy α (k + d)` (the literature ties the witness bound directly
to `α`, with no separate control axis). Cut-elimination then raises `e` to dominate the
cut-formula bounds while `α` grows freely; the witness stays controlled by `hardy e`, a
`hardy`-closed quantity.

This file: the inductive `Provable` calculus, its structural layer (`mono_k`, `mono_d`, `mono_c`,
`mono_e`, `weakening`), and the ordinal/`norm` bookkeeping used throughout the cut-elimination
suite. The inversion suite lives in `GoodsteinPA.OperatorZinfty.Inversion`, and the cut
reductions in `GoodsteinPA.OperatorZinfty.Cut`.

- [Tow20, §13, §15, §18, §19]
- [EW12, Definition 23]
- [Buc03, §6]
-/
module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import GoodsteinPA.ToMathlib.Hardy
public import GoodsteinPA.Compat

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const
noncomputable def atomTrue (φ : ArithmeticFormula ℕ) : Prop :=
  GoodsteinPA.Compat.gEvalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The witness-bounded `Z_∞` refinement** `Provable ⊢^{α,e}_{k,d,c} Γ`.
Derivation ordinal `α`; **control ordinal `e`** (governs the witness bound, raised by cut-elim);
effective norm budget `k + d`; ω-premise `n` at `(max k n, d)`; **witness bound `hardy e (k+d)`**
(decoupled from `α`, and threaded inertly through every rule).

The base rules and ordinal/numeric bounds follow the `Z_∞` design; the `k + d` budget split and
the control ordinal `e` are this formalization's own refinement.

- [Tow20, §13, §15, §18]
- [EW12, Definition 23]
- [Buc03, §6]
-/
inductive Provable : ONote → ONote → ℕ → ℕ → ℕ → Finset (ArithmeticFormula ℕ) → Prop
  | axL {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Provable α e k d c Γ
  | verumR {α e k d c Γ} (h : (⊤ : ArithmeticFormula ℕ) ∈ Γ) : Provable α e k d c Γ
  | trueRel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.rel r v ∈ Γ) : Provable α e k d c Γ
  | trueNrel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.nrel r v ∈ Γ) : Provable α e k d c Γ
  | wk {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Provable α e k d c Δ) : Provable α e k d c Γ
  | weak {α β e k d c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (hsub : Δ ⊆ Γ) (dd : Provable β e k d c Δ) : Provable α e k d c Γ
  | andI {α βφ βψ e k d c Γ} (φ ψ : ArithmeticFormula ℕ) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (dφ : Provable βφ e k d c (insert φ Γ)) (dψ : Provable βψ e k d c (insert ψ Γ)) :
      Provable α e k d c (insert (φ ⋏ ψ) Γ)
  | orI {α β e k d c Γ} (φ ψ : ArithmeticFormula ℕ) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (dd : Provable β e k d c (insert φ (insert ψ Γ))) : Provable α e k d c (insert (φ ⋎ ψ) Γ)
  | allω {α e k d c Γ} (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n + d)
      (dd : ∀ n, Provable (β n) e (max k n) d c (insert (φ/[nm n]) Γ)) :
      Provable α e k d c (insert (∀⁰ φ) Γ)
  | exI {α β e k d c Γ} (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d) (hbound : n ≤ hardy e (k + d))
      (dd : Provable β e k d c (insert (φ/[nm n]) Γ)) : Provable α e k d c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e k d c Γ} (φ : ArithmeticFormula ℕ) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (d₁ : Provable βφ e k d c (insert φ Γ)) (d₂ : Provable βψ e k d c (insert (∼φ) Γ)) :
      Provable α e k d c Γ

namespace Provable

variable {α e : ONote} {k d c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-- **`k`-monotonicity** (the `max`/cofinal part; inversions raise this idempotently). The witness
bound `hardy e (k+d)` rises with `k` via `hardy_monotone`. -/
lemma mono_k (dd : Provable α e k d c Γ) {k'} (hk : k ≤ k') : Provable α e k' d c Γ := by
  induction dd generalizing k' with
  | axL r v hp hn => exact Provable.axL r v hp hn
  | verumR h => exact Provable.verumR h
  | trueRel r v htrue hτ hαNF hmem =>
      exact Provable.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      exact Provable.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | wk hsub _ ih => exact Provable.wk hsub (ih hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      exact Provable.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      exact Provable.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      exact Provable.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      exact Provable.allω φ β hβ hβNF hαNF
        (fun n => lt_of_lt_of_le (hτ n) (by have := Nat.add_le_add_right (max_le_max hk (le_refl n)) d; omega))
        (fun n => ih n (max_le_max hk (le_refl n)))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      exact Provable.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      exact Provable.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hk) (ih₂ hk)

/-- **`d`-monotonicity** (the additive cut-shift budget; the ∀/∃ commuting cut-reduction case
raises this by `norm α`, cf. [Tow20, §19.6]). The witness bound `hardy e (k+d)` rises with `d`
via `hardy_monotone`. -/
lemma mono_d (dd : Provable α e k d c Γ) {d'} (hd : d ≤ d') : Provable α e k d' c Γ := by
  induction dd generalizing d' with
  | axL r v hp hn => exact Provable.axL r v hp hn
  | verumR h => exact Provable.verumR h
  | trueRel r v htrue hτ hαNF hmem =>
      exact Provable.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      exact Provable.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | wk hsub _ ih => exact Provable.wk hsub (ih hd)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      exact Provable.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hd)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      exact Provable.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hd) (ihψ hd)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      exact Provable.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hd)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      exact Provable.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega))
        (fun n => ih n hd)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      exact Provable.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hd)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      exact Provable.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hd) (ih₂ hd)

/-- **`c`-monotonicity** (cut-rank). -/
lemma mono_c (dd : Provable α e k d c Γ) {c'} (hc : c ≤ c') : Provable α e k d c' Γ := by
  induction dd generalizing c' with
  | axL r v hp hn => exact Provable.axL r v hp hn
  | verumR h => exact Provable.verumR h
  | trueRel r v htrue hτ hαNF hmem => exact Provable.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => exact Provable.trueNrel r v htrue hτ hαNF hmem
  | wk hsub _ ih => exact Provable.wk hsub (ih hc)
  | weak hβ hβNF hαNF hτ hsub _ ih => exact Provable.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      exact Provable.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => exact Provable.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih => exact Provable.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      exact Provable.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      exact Provable.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- **`e`-monotonicity** (the NEW control axis; cut-elimination raises `e` to dominate cut-formula
bounds). Only the `exI` witness bound `hardy e (k+d)` depends on `e`, and it rises with `e` via
the index-monotonicity `hardy_le_of_lt` (with the budget side condition `norm e ≤ k+d`). -/
lemma mono_e (dd : Provable α e k d c Γ) {e'} (he : e.NF) (heN' : e'.NF) (hlt : e < e')
    (hnorm : norm e ≤ k + d) : Provable α e' k d c Γ := by
  induction dd generalizing e' with
  | axL r v hp hn => exact Provable.axL r v hp hn
  | verumR h => exact Provable.verumR h
  | trueRel r v htrue hτ hαNF hmem => exact Provable.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => exact Provable.trueNrel r v htrue hτ hαNF hmem
  | wk hsub _ ih => exact Provable.wk hsub (ih he heN' hlt hnorm)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      exact Provable.weak hβ hβNF hαNF hτ hsub (ih he heN' hlt hnorm)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      exact Provable.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ he heN' hlt hnorm) (ihψ he heN' hlt hnorm)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      exact Provable.orI φ ψ hβ hβNF hαNF hτ (ih he heN' hlt hnorm)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      refine Provable.allω φ β hβ hβNF hαNF hτ (fun n => ih n he heN' hlt ?_)
      -- premise n runs at index (max k n, d): budget `norm e ≤ max k n + d` from `norm e ≤ k + d`
      have : k ≤ max k n := le_max_left _ _
      omega
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      refine Provable.exI φ n hβ hβNF hαNF hτ ?_ (ih he heN' hlt hnorm)
      exact le_trans hbound (hardy_le_of_lt he heN' hlt hnorm)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      exact Provable.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ he heN' hlt hnorm) (ih₂ he heN' hlt hnorm)

/-- Sequent weakening (height-preserving). -/
lemma weakening {Δ} (hsub : Δ ⊆ Γ) (dd : Provable α e k d c Δ) : Provable α e k d c Γ :=
  Provable.wk hsub dd

end Provable

end GoodsteinPA.OperatorZinfty
