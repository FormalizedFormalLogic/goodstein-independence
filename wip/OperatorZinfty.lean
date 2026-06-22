/-
# `Zᵉᵏᵈ` — the control-ordinal operator witness-bounded `Z_∞` calculus (Towsner §15 + §19, lap-8)

The lap-7 ADDENDUM 4 finding: the split-index `(k,d)` calculus (`wip/SplitZinfty.lean`) closes the
§19.6 **norm-budget** obstruction (the `d`-bump `d ↦ d + norm α`) but NOT the **witness-index** one —
the principal `exI` cut's witness `hardy γ(·)` makes the witness bound grow super-linearly through
commuting ω-rules, and a witness bound tied to the *derivation* ordinal `α` cannot absorb that under
cut-elim (which grows `α ↦ α + γ`).

**The fix (lap-8 design): a control ordinal `e`.** Decouple the `exI` witness bound from the
derivation ordinal `α` onto a separate **control ordinal** `e`: the witness bound becomes
`n ≤ hardy e (k + d)` (was `hardy α (k + d)`). Cut-elimination then *raises `e`* to dominate the
cut-formula bounds while `α` grows freely; the witness stays controlled by `hardy e`, a `hardy`-closed
quantity (Buchholz operator-controlled derivations, specialized to PA, numeric-`e` form).

The Hardy infrastructure this needs is **banked** (lap 8, `src/Hardy.lean` + `src/LowerBound.lean`):
- `hardy_add_collapse` : `H_{e+α} = H_e ∘ H_α` (control-side: collapse nested control under cut-elim).
- `hardy_comp_lt_goodsteinLength` : `H_α(H_e(m)) < G(m)` eventually (lower-bound side: a nested
  control index is still Goodstein-dominated, so the witness-bounded lower bound survives).

This file: the inductive `Zekd` + structural layer (`mono_k`, `mono_d`, `mono_c`, `mono_e`, `weakening`).
The inversion suite + §19.5/§19.6 cut reductions port from `wip/SplitZinfty.lean` (mechanical: thread
the inert `e`, plus the §19.6 witness-control step using the banked Hardy lemmas).
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Hardy

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing

abbrev Form := SyntacticFormula ℒₒᵣ
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const
abbrev Seq := Finset Form
noncomputable def atomTrue (φ : Form) : Prop := Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The control-ordinal operator witness-bounded `Z_∞` calculus** `Zᵉᵏᵈ ⊢^{α,e}_{k,d,c} Γ`.
Derivation ordinal `α`; **control ordinal `e`** (governs the witness bound, raised by cut-elim);
effective norm budget `k + d`; ω-premise `n` at `(max k n, d)`; **witness bound `hardy e (k+d)`**
(decoupled from `α`). Cf. `SplitZinfty.Zkd` — identical except the `exI` bound uses `e` not `α`, and
every rule carries the inert `e`. -/
inductive Zekd : ONote → ONote → ℕ → ℕ → ℕ → Seq → Prop
  | axL {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zekd α e k d c Γ
  | verumR {α e k d c Γ} (h : (⊤ : Form) ∈ Γ) : Zekd α e k d c Γ
  | trueRel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.rel r v ∈ Γ) : Zekd α e k d c Γ
  | trueNrel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.nrel r v ∈ Γ) : Zekd α e k d c Γ
  | wk {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zekd α e k d c Δ) : Zekd α e k d c Γ
  | weak {α β e k d c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (hsub : Δ ⊆ Γ) (dd : Zekd β e k d c Δ) : Zekd α e k d c Γ
  | andI {α βφ βψ e k d c Γ} (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (dφ : Zekd βφ e k d c (insert φ Γ)) (dψ : Zekd βψ e k d c (insert ψ Γ)) :
      Zekd α e k d c (insert (φ ⋏ ψ) Γ)
  | orI {α β e k d c Γ} (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (dd : Zekd β e k d c (insert φ (insert ψ Γ))) : Zekd α e k d c (insert (φ ⋎ ψ) Γ)
  | allω {α e k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n + d)
      (dd : ∀ n, Zekd (β n) e (max k n) d c (insert (φ/[nm n]) Γ)) :
      Zekd α e k d c (insert (∀⁰ φ) Γ)
  | exI {α β e k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d) (hbound : n ≤ hardy e (k + d))
      (dd : Zekd β e k d c (insert (φ/[nm n]) Γ)) : Zekd α e k d c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e k d c Γ} (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (d₁ : Zekd βφ e k d c (insert φ Γ)) (d₂ : Zekd βψ e k d c (insert (∼φ) Γ)) :
      Zekd α e k d c Γ

namespace Zekd

/-- **`k`-monotonicity** (the `max`/cofinal part; inversions raise this idempotently). The witness
bound `hardy e (k+d)` rises with `k` via `hardy_monotone`. -/
theorem mono_k : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {k'}, k ≤ k' → Zekd α e k' d c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro k' _; exact Zekd.axL r v hp hn
  | verumR h => intro k' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem =>
      intro k' hk; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      intro k' hk; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | wk hsub _ ih => intro k' hk; exact Zekd.wk hsub (ih hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro k' hk
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro k' hk; exact Zekd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact Zekd.allω φ β hβ hβNF hαNF
        (fun n => lt_of_lt_of_le (hτ n) (by have := Nat.add_le_add_right (max_le_max hk (le_refl n)) d; omega))
        (fun n => ih n (max_le_max hk (le_refl n)))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro k' hk
      exact Zekd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro k' hk
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hk) (ih₂ hk)

/-- **`d`-monotonicity** (the additive cut-shift budget; the §19.6-commuting case raises this by
`norm α`). The witness bound `hardy e (k+d)` rises with `d` via `hardy_monotone`. -/
theorem mono_d : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {d'}, d ≤ d' → Zekd α e k d' c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro d' _; exact Zekd.axL r v hp hn
  | verumR h => intro d' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem =>
      intro d' hd; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      intro d' hd; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | wk hsub _ ih => intro d' hd; exact Zekd.wk hsub (ih hd)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro d' hd; exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hd)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro d' hd
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hd) (ihψ hd)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro d' hd; exact Zekd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hd)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro d' hd
      exact Zekd.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega))
        (fun n => ih n hd)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro d' hd
      exact Zekd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hd)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro d' hd
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hd) (ih₂ hd)

/-- **`c`-monotonicity** (cut-rank). -/
theorem mono_c : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {c'}, c ≤ c' → Zekd α e k d c' Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro c' _; exact Zekd.axL r v hp hn
  | verumR h => intro c' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem => intro c' _; exact Zekd.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => intro c' _; exact Zekd.trueNrel r v htrue hτ hαNF hmem
  | wk hsub _ ih => intro c' hc; exact Zekd.wk hsub (ih hc)
  | weak hβ hβNF hαNF hτ hsub _ ih => intro c' hc; exact Zekd.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro c' hc; exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zekd.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zekd.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro c' hc; exact Zekd.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zekd.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- **`e`-monotonicity** (the NEW control axis; cut-elimination raises `e` to dominate cut-formula
bounds). Only the `exI` witness bound `hardy e (k+d)` depends on `e`, and it rises with `e` via
the index-monotonicity `hardy_le_of_lt` (with the budget side condition `norm e ≤ k+d`). -/
theorem mono_e : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {e'}, e.NF → e'.NF → e < e' →
    norm e ≤ k + d → Zekd α e' k d c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro e' _ _ _ _; exact Zekd.axL r v hp hn
  | verumR h => intro e' _ _ _ _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem => intro e' _ _ _ _; exact Zekd.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => intro e' _ _ _ _; exact Zekd.trueNrel r v htrue hτ hαNF hmem
  | wk hsub _ ih => intro e' he heN' hlt hnorm; exact Zekd.wk hsub (ih he heN' hlt hnorm)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro e' he heN' hlt hnorm; exact Zekd.weak hβ hβNF hαNF hτ hsub (ih he heN' hlt hnorm)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro e' he heN' hlt hnorm
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ he heN' hlt hnorm) (ihψ he heN' hlt hnorm)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro e' he heN' hlt hnorm; exact Zekd.orI φ ψ hβ hβNF hαNF hτ (ih he heN' hlt hnorm)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro e' he heN' hlt hnorm
      refine Zekd.allω φ β hβ hβNF hαNF hτ (fun n => ih n he heN' hlt ?_)
      -- premise n runs at index (max k n, d): budget `norm e ≤ max k n + d` from `norm e ≤ k + d`
      have : k ≤ max k n := le_max_left _ _
      omega
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro e' he heN' hlt hnorm
      refine Zekd.exI φ n hβ hβNF hαNF hτ ?_ (ih he heN' hlt hnorm)
      exact le_trans hbound (hardy_le_of_lt he heN' hlt hnorm)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro e' he heN' hlt hnorm
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ he heN' hlt hnorm) (ih₂ he heN' hlt hnorm)

private theorem invPush (A b : Form) (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert b s).erase A)) ⊆ insert b (insert φ (insert ψ (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem invPull (A : Form) {b : Form} (h : b ≠ A) (s : Seq) {φ ψ : Form} :
    insert b (insert φ (insert ψ (s.erase A))) ⊆ insert φ (insert ψ ((insert b s).erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | rfl | hx
  · exact Or.inr (Or.inr ⟨h, Or.inl rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨hx.1, Or.inr hx.2⟩)

private theorem invPush2 (A b₁ b₂ : Form) (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert b₁ (insert b₂ s)).erase A))
      ⊆ insert b₁ (insert b₂ (insert φ (insert ψ (s.erase A)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem princOrSub {A : Form} (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert φ (insert ψ s)).erase A)) ⊆ insert φ (insert ψ (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∨-inversion.** Replace `φ ⋎ ψ` by `φ`, `ψ`, same `(α,k,d,c)`. -/
theorem orInv {φ ψ : Form} : ∀ {α e k d c Γ}, Zekd α e k d c Γ → (φ ⋎ ψ) ∈ Γ →
    Zekd α e k d c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  have hφ0 : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
  have hψ0 : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zekd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF hτ (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zekd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zekd.wk (invPush (φ ⋎ ψ) φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zekd.wk (invPush (φ ⋎ ψ) ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hd : (φ ⋎ ψ) ∈ Γ₀
        · exact Zekd.weak hβ hβNF hαNF hτ (princOrSub Γ₀)
            (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd)))
        · rw [Finset.erase_eq_of_notMem hd]
          exact Zekd.weak hβ hβNF hαNF hτ (Finset.Subset.refl _) (by assumption)
      · have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have P := Zekd.wk (invPush2 (φ ⋎ ψ) φ' ψ' Γ₀)
          (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
        exact Zekd.wk (invPull (φ ⋎ ψ) hhd Γ₀) (Zekd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zekd (β n) e (max k n) d c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zekd.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zekd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zekd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-! ### Single-insert reshuffle helpers (for ∧-inversion and the ∀-inversion). -/

private theorem inv1Push (A e b : Form) (s : Seq) :
    insert e ((insert b s).erase A) ⊆ insert b (insert e (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem inv1Pull (A e : Form) {b : Form} (h : b ≠ A) (s : Seq) :
    insert b (insert e (s.erase A)) ⊆ insert e ((insert b s).erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | hx
  · exact Or.inr ⟨h, Or.inl rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx.1, Or.inr hx.2⟩

private theorem inv1Push2 (A e b₁ b₂ : Form) (s : Seq) :
    insert e ((insert b₁ (insert b₂ s)).erase A) ⊆ insert b₁ (insert b₂ (insert e (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

private theorem princAllSub (A e : Form) (s : Seq) :
    insert e ((insert e s).erase A) ⊆ insert e (s.erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∧-inversion, left** (Towsner §19.3): replace `φ ⋏ ψ` by `φ`, same `(α,k,d,c)`. -/
theorem andInvL {φ ψ : Form} : ∀ {α e k d c Γ}, Zekd α e k d c Γ → (φ ⋏ ψ) ∈ Γ →
    Zekd α e k d c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ dφ _ ihφ ihψ =>
      intro hmem
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Zekd.weak hβφ hβφNF hαNF hτφ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihφ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zekd.weak hβφ hβφNF hαNF hτφ (Finset.Subset.refl _) dφ
      · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have Pφ := Zekd.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
        have Pψ := Zekd.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
        exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zekd (β n) e (max k n) d c (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∧-inversion, right** (Towsner §19.3): replace `φ ⋏ ψ` by `ψ`, same `(α,k,d,c)`. -/
theorem andInvR {φ ψ : Form} : ∀ {α e k d c Γ}, Zekd α e k d c Γ → (φ ⋏ ψ) ∈ Γ →
    Zekd α e k d c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue hτ hαNF (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ dψ ihφ ihψ =>
      intro hmem
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Zekd.weak hβψ hβψNF hαNF hτψ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihψ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zekd.weak hβψ hβψNF hαNF hτψ (Finset.Subset.refl _) dψ
      · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have Pφ := Zekd.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
        have Pψ := Zekd.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
        exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zekd (β n) e (max k n) d c (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zekd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∀-inversion** (Towsner §19.4) — the bound-critical one (the subformula bridge to `B` consumes it).
Result raises the **`k`-part** to `max k n₀` (`d` inert): the principal case's idempotent collapse
`max (max k n₀) n₀ = max k n₀` is exactly why the split index keeps `allInv` working. -/
theorem allInv {φ₀ : SyntacticSemiformula ℒₒᵣ 1} (n₀ : ℕ) :
    ∀ {α e k d c Γ}, Zekd α e k d c Γ → (∀⁰ φ₀) ∈ Γ →
      Zekd α e (max k n₀) d c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  have hI0 : (φ₀/[nm n₀]) ≠ (∀⁰ φ₀) := Semiformula.ne_of_ne_complexity (by simp)
  intro α e k d c Γ dd
  induction dd with
  | @axL α e k d c Γ ar r v hp hn =>
      intro _
      refine Zekd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α e k d c Γ h =>
      intro _
      exact Zekd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) hαNF
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α e k d c Γ ar r v htrue hτ hαNF hmem =>
      intro _
      exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) hαNF
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α e k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zekd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.wk ?_ (Zekd.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) ?_
          (Zekd.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' e k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Wedge.wedge, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zekd.wk (inv1Push (∀⁰ φ₀) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zekd.wk (inv1Push (∀⁰ φ₀) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zekd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF
          (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
          (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) Pφ Pψ)
  | @orI α β e k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Vee.vee, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push2 (∀⁰ φ₀) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zekd.orI φ' ψ' hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) P)
  | @allω α e k d c Γ₀ χ β hβ hβNF hαNF hτ dd ih =>
      intro hmem
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (Finset.mem_insert_of_mem hh)
          rw [max_eq_left (le_max_right k n₀)] at h
          exact Zekd.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (princAllSub (∀⁰ χ) _ Γ₀) h
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zekd.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (Finset.Subset.refl _) (dd n₀)
      · have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zekd (β n) e (max (max k n₀) n) d c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := Zekd.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
          rw [show max (max k n₀) n = max (max k n) n₀ from by omega]
          exact h
        exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zekd.allω χ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega)) key)
  | @exI α β e k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zekd.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zekd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zekd.exI χ n hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (le_trans hbound (hardy_monotone _ (Nat.add_le_add_right (le_max_left _ _) d))) P)
  | @cut α βφ' βψ' e k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zekd.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zekd.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zekd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
        (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) P₁ P₂

theorem lt_osucc {o : ONote} (h : o.NF) : o < osucc o :=
  lt_def.mpr (by rw [repr_osucc h]; exact lt_add_one _)

/-- **`osucc` strict monotonicity** (the §19.6 descent: `βᵢ < γ ⟹ osucc(α+βᵢ) < osucc(α+γ)`). -/
theorem osucc_lt_osucc {x y : ONote} (hx : x.NF) (hy : y.NF) (h : x < y) : osucc x < osucc y := by
  refine lt_def.mpr ?_
  rw [repr_osucc hx, repr_osucc hy, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_lt_succ (lt_def.mp h)

/-- `x < y ⟹ x < osucc y` (NF). -/
theorem lt_osucc_of_lt {x y : ONote} (hy : y.NF) (h : x < y) : x < osucc y :=
  lt_trans h (lt_osucc hy)

/-! #### Ordinal/`norm` bookkeeping for §19.6/§19.7 (copied from `BoundedZinfty`; all axiom-clean). -/

theorem add_lt_add_left_NF {α γ' γ : ONote} (hαNF : α.NF) (hγ'NF : γ'.NF) (hγNF : γ.NF)
    (h : γ' < γ) : α + γ' < α + γ := by
  haveI := hαNF; haveI := hγ'NF; haveI := hγNF
  exact lt_def.mpr (by rw [repr_add, repr_add]; exact (add_lt_add_iff_left _).mpr (lt_def.mp h))

theorem le_add_left_NF {α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) : γ ≤ α + γ := by
  haveI := hαNF; haveI := hγNF
  exact le_def.mpr (by rw [repr_add]; exact le_add_self)

/-- **The §19.6 descent step**, assembled: `γ' < γ ⟹ osucc (α + γ') < osucc (α + γ)`. -/
theorem add_osucc_descent {α γ' γ : ONote} (hαNF : α.NF) (hγ'NF : γ'.NF) (hγNF : γ.NF)
    (h : γ' < γ) : osucc (α + γ') < osucc (α + γ) :=
  osucc_lt_osucc (ONote.add_nf α γ') (ONote.add_nf α γ) (add_lt_add_left_NF hαNF hγ'NF hγNF h)

@[simp] theorem norm_omegaPow {α : ONote} : norm (oadd α 1 0) = max (norm α) 1 := by
  simp [norm_oadd]

theorem norm_addAux_le (e : ONote) (n : ℕ+) (r : ONote) :
    norm (addAux e n r) ≤ max (norm e) (n : ℕ) + norm r := by
  unfold addAux
  match r with
  | 0 => simp only [norm_oadd, norm_zero]; omega
  | oadd e' n' a' =>
    simp only []
    rcases ONote.cmp e e' with _ | _ | _ <;>
      simp only [norm_oadd, PNat.add_coe] <;> omega

theorem norm_add_le : ∀ {α : ONote}, α.NF → ∀ {γ : ONote}, γ.NF →
    norm (α + γ) ≤ norm α + norm γ := by
  intro α
  induction α with
  | zero => intro _ γ _; simp
  | oadd e n a ihe iha =>
    intro hα γ hγ
    have ha : a.NF := hα.snd
    haveI := ha; haveI := hγ
    have iha' : norm (a + γ) ≤ norm a + norm γ := iha ha hγ
    rw [oadd_add]
    rcases hr : a + γ with _ | ⟨e', n', a'⟩
    · simp only [addAux, norm_oadd, norm_zero]; omega
    · rw [hr] at iha'
      simp only [norm_oadd] at iha'
      simp only [addAux]
      rcases hcmp : ONote.cmp e e' with _ | _ | _
      · simp only [norm_oadd]; omega
      · have hee : e = e' := eq_of_cmp_eq hcmp
        have hge : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr (a + γ) := by
          rw [hr, hee]; exact omega0_le_oadd e' n' a'
        have hra : ONote.repr a < Ordinal.omega0 ^ ONote.repr e := hα.snd'.repr_lt
        have hgγ : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr γ := by
          by_contra hlt
          push_neg at hlt
          have : ONote.repr a + ONote.repr γ < Ordinal.omega0 ^ ONote.repr e :=
            (Ordinal.isPrincipal_add_omega0_opow (ONote.repr e)) hra hlt
          rw [repr_add] at hge
          exact absurd (lt_of_le_of_lt hge this) (lt_irrefl _)
        have habs : a + γ = γ := by
          have : ONote.repr (a + γ) = ONote.repr γ := by
            rw [repr_add]; exact Ordinal.add_of_omega0_opow_le hra hgγ
          exact repr_inj.mp this
        have hnγ : norm γ = max (norm e') (max (n':ℕ) (norm a')) := by
          rw [← habs, hr]; simp [norm_oadd]
        simp only [norm_oadd, PNat.add_coe]; omega
      · simp only [norm_oadd]; omega

/-- **∧/∨ cut reduction, conjunction case** (Towsner §19.5). -/
theorem cutReduceConj {a b : Form} {c k d : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Zekd α e k d c (insert (a ⋏ b) Γ)) (hNC : Zekd β e k d c (insert (∼a ⋎ ∼b) Γ)) :
    Zekd (osucc δ) e k d c Γ := by
  have hA : Zekd α e k d c (insert a Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvL (Finset.mem_insert_self _ _))
  have hB : Zekd α e k d c (insert b Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvR (Finset.mem_insert_self _ _))
  have hNab : Zekd β e k d c (insert (∼a) (insert (∼b) Γ)) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.orInv (Finset.mem_insert_self _ _))
  have cutA : Zekd δ e k d c (insert (∼b) Γ) :=
    Zekd.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ
      (Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hA) hNab
  exact Zekd.cut b hb (lt_trans hαδ (lt_osucc hδNF)) (lt_osucc hδNF) hαNF hδNF (osucc_NF hδNF)
    hτα hτδ hB cutA

/-- **∧/∨ cut reduction, disjunction case** (dual). -/
theorem cutReduceDisj {a b : Form} {c k d : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Zekd α e k d c (insert (a ⋎ b) Γ)) (hNC : Zekd β e k d c (insert (∼a ⋏ ∼b) Γ)) :
    Zekd (osucc δ) e k d c Γ := by
  have hAB : Zekd α e k d c (insert a (insert b Γ)) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.orInv (Finset.mem_insert_self _ _))
  have hNa : Zekd β e k d c (insert (∼a) Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvL (Finset.mem_insert_self _ _))
  have hNb : Zekd β e k d c (insert (∼b) Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvR (Finset.mem_insert_self _ _))
  have cutA : Zekd δ e k d c (insert b Γ) :=
    Zekd.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ hAB
      (Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hNa)
  exact Zekd.cut b hb (lt_osucc hδNF) (lt_trans hβδ (lt_osucc hδNF)) hδNF hβNF (osucc_NF hδNF)
    hτδ hτβ cutA hNb

/-- Sequent weakening (height-preserving). -/
theorem weakening {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zekd α e k d c Δ) : Zekd α e k d c Γ :=
  Zekd.wk hsub dd

end Zekd

/-! ### `ZekdProv` — the `Provable`-style wrapper (bound-as-upper-bound)

`Zekd` carries an *exact* derivation ordinal, so every ordinal-raise (e.g. `wk`'s
`γ ↦ osucc(α+γ)` in cut-elimination) needs `NF` of the source. The wrapper bundles an upper
bound + the source's `NF`, so the `≤`-slack absorbs the `osucc`/`+1` bookkeeping uniformly and
`NF` is always available. This is the surface §19.6 `cutReduceAll` is stated over (matching the
unbounded `Zinfty.lean Provable`). -/
def ZekdProv (α e : ONote) (k d c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Zekd α' e k d c Γ

namespace ZekdProv

/-- Monotonicity in `α` (≤), `k`, `d`, `c` (the control `e` is raised separately by `mono_e`,
which carries a budget side condition). -/
theorem mono {α β e : ONote} {k d c k' d' c' : ℕ} {Γ : Seq}
    (hα : α ≤ β) (hk : k ≤ k') (hd : d ≤ d') (hc : c ≤ c') :
    ZekdProv α e k d c Γ → ZekdProv β e k' d' c' Γ := by
  rintro ⟨α', hα', hNF, D⟩
  exact ⟨α', le_trans hα' hα, hNF, ((D.mono_k hk).mono_d hd).mono_c hc⟩

/-- Control-ordinal raising at the wrapper level. -/
theorem mono_e {α e e' : ONote} {k d c : ℕ} {Γ : Seq}
    (heNF : e.NF) (he'NF : e'.NF) (hlt : e < e') (hbudget : norm e ≤ k + d) :
    ZekdProv α e k d c Γ → ZekdProv α e' k d c Γ := by
  rintro ⟨α', hα', hNF, D⟩
  exact ⟨α', hα', hNF, D.mono_e heNF he'NF hlt hbudget⟩

/-- Sequent weakening. -/
theorem weakening {α e : ONote} {k d c : ℕ} {Γ Δ : Seq} (h : Γ ⊆ Δ) :
    ZekdProv α e k d c Γ → ZekdProv α e k d c Δ := by
  rintro ⟨α', hα', hNF, D⟩
  exact ⟨α', hα', hNF, D.wk h⟩

/-- Respect set-equality of sequents. -/
theorem cast {α e : ONote} {k d c : ℕ} {Γ Δ : Seq} (e0 : Γ = Δ) :
    ZekdProv α e k d c Γ → ZekdProv α e k d c Δ := fun h => e0 ▸ h

/-- Lift a raw `Zekd` derivation (with an NF ordinal) into the wrapper. -/
theorem of {α e : ONote} {k d c : ℕ} {Γ : Seq} (hNF : α.NF) (D : Zekd α e k d c Γ) :
    ZekdProv α e k d c Γ := ⟨α, le_refl _, hNF, D⟩

end ZekdProv

/-! ### §19.6 ∀/∃ cut reduction `cutReduceAll` — SCAFFOLD (lap-8 checkpoint)

The induction core. Port of `src/Zinfty.lean:785 cutReduceAllAux` to the control-ordinal calculus
over the `ZekdProv` wrapper. The ∃-side ordinal's `NF` is **threaded through the induction goal**
(`γ.NF →`), so each case's IH carries it (supplied from the constructors' own NF hyps; `wk` passes the
same `γ`; leaves wrap at `0`/carry `hαNF`). Conclusion ordinal `osucc(α+γ)`; `d`-bump `dd ↦ dd+norm α`;
`e` inert here (raised at the top-level cut, future `cutReduceAll`). `fam` is the ∀-inversion family,
fixed over the outer `(α,e,k,dd,Γ)`; in the ω-rule commuting case it is raised via `mono_k`/`mono_d`.

**Signature typechecks** (validated lap 8). Body is a disclosed `sorry` — next-lap focus.

⚠️ **STRUCTURAL CHALLENGE for the body (surfaced lap 8):** `Zekd` is multi-indexed by `(α e k d c Γ)`
(all are inductive indices), unlike the unbounded `Zinfty.lean Deriv` which is single-indexed by `Γ`
(with `o`/`cr` as separate *measure functions*). So `induction D` here generalizes `e k d c` too — and
the external `fam` (fixed over the outer `e,k,dd`) falls out of alignment with the per-case rebound
indices (acutely in the `allω` case, premise `k ↦ max k n`). **SHARPER resolution (the `allInv` precedent):** the inversions ALREADY induct over multi-indexed
`Zekd` with the `allω` `k ↦ max k n` variation — and succeed — *because they generalize `k` (and
`α,d,c,Γ`) in the theorem statement* (`∀ {α k d c Γ}, Zekd α k d c Γ → …`), so `induction` hands back an
IH at *every* index, incl. the premise's `max k n`. So `cutReduceAllAux` should likewise **generalize
`k` and `dd` (and `γ,Δ`) in the induction statement** — NOT fix them to `fam`'s. The external `fam`
(fixed at the outer `k₀,dd₀`) is then **raised per-case** to the case's `(k,dd)` via `mono_k`/`mono_d`
(indices only grow: `allω` premise `k = max k₀ n ≥ k₀`; `dd` rides ≥). Concretely:
  `∀ {γ : ONote} {k dd : ℕ} {Δ}, Zekd γ e k dd c Δ → γ.NF → k₀ ≤ k → dd₀ ≤ dd → (∃⁰∼φ)∈Δ →
     ZekdProv (osucc (α+γ)) e k (dd + norm α) c (Δ.erase (∃⁰∼φ) ∪ Γ)`
  with `fam : ∀ n, Zekd α e k₀ dd₀ c (insert (φ/[nm n]) Γ)` outside; use `(fam n).mono_k h.mono_d h'`
  to align before each principal cut. This needs NO calculus reformulation — it's the `allInv` pattern
  scaled to carry an external family. (A `Deriv`-style single-indexed `ZekdD` with `(ord,ctrl,nrm,cr)`
  measures is the heavier fallback if the index-generalized induction proves unwieldy.) -/
theorem cutReduceAllAux {φ : SyntacticSemiformula ℒₒᵣ 1} {c k₀ dd₀ : ℕ} {α e : ONote} {Γ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (fam : ∀ n, Zekd α e k₀ dd₀ c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {k dd : ℕ} {Δ : Seq}, Zekd γ e k dd c Δ → γ.NF → k₀ ≤ k → dd₀ ≤ dd →
      (∃⁰ ∼φ) ∈ Δ →
      ZekdProv (osucc (α + γ)) e k (dd + norm α) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro γ k dd Δ D
  induction D with
  | axL r v hp hn =>
      intro hγNF hk hdd hmem
      exact ⟨0, le_def.mpr (by simp), NF.zero, Zekd.axL r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))⟩
  | verumR h =>
      intro hγNF hk hdd hmem
      exact ⟨0, le_def.mpr (by simp), NF.zero, Zekd.verumR
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))⟩
  | trueRel r v htrue hτ hαNF' hmemA =>
      intro hγNF hk hdd hmem
      refine ⟨_, le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
        hγNF, Zekd.trueRel r v htrue (by omega) hγNF
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩
  | trueNrel r v htrue hτ hαNF' hmemA =>
      intro hγNF hk hdd hmem
      refine ⟨_, le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
        hγNF, Zekd.trueNrel r v htrue (by omega) hγNF
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩
  | @wk γ' e' k' dd' c' Δsub Δsup hsub D' ih =>
      intro hγNF hk hdd hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hk hdd hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · refine ⟨γ', le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
          hγNF, (D'.mono_d (by omega)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ' β e' k' dd' c' Δsub Δsup hβ hβNF hαNF' hτ hsub D' ih =>
      intro hγNF hk hdd hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hk hdd hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_osucc_descent hαNF hβNF hγNF hβ)) le_rfl le_rfl le_rfl
      · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))))), hβNF,
          (D'.mono_d (by omega)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @andI γ' βφ βψ e' k' dd' c' Γ₀ ψ₁ ψ₂ hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ dφ dψ ihφ ihψ =>
      intro hγNF hk hdd hmem
      sorry -- commuting ∧: reassemble Zekd.andI at osucc(α+γ); sub-results from ihφ/ihψ at osucc(α+βφ/βψ)
  | @orI γ' β e' k' dd' c' Γ₀ ψ₁ ψ₂ hβ hβNF hαNF' hτ dd' ih =>
      intro hγNF hk hdd hmem
      sorry -- commuting ∨
  | @allω γ' e' k' dd' c' Γ₀ χ β hβ hβNF hαNF' hτ dd' ih =>
      intro hγNF hk hdd hmem
      sorry -- commuting ω-rule: the witness-index obstruction's resolution (e inert, d-bump, raise fam via mono_k)
  | @exI γ' β e' k' dd' c' Γ₀ χ n hβ hβNF hαNF' hτ hbound dd' ih =>
      intro hγNF hk hdd hmem
      sorry -- principal exI (χ=∼φ): cut fam(n) at the witness; + commuting exI (χ≠∼φ)
  | @cut γ' βφ βψ e' k' dd' c' Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ d₁ d₂ ih₁ ih₂ =>
      intro hγNF hk hdd hmem
      sorry -- commuting cut

end GoodsteinPA.OperatorZinfty
