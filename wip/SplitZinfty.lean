/-
# `Zᵏᵈ` — the split-index `(k, d)` witness-bounded `Z_∞` calculus (Towsner §15 + §19, lap-7 design)

The lap-7 obstruction analysis (`ANALYSIS-2026-06-22-cutelim-k-threading.md`, ADDENDA 1–3) showed that
the single-numeric-index calculus `Zk` (`wip/BoundedZinfty.lean`) cannot complete §19.6 cut-elimination:
the ω-rule index `max k n` is good for `allInv` (idempotent) but breaks the §19.6-commuting case (the
`+norm α` bound shift overflows the `max{k,n}~n` budget for large `n`); switching to `k + n` fixes
§19.6 but breaks `allInv` (no idempotent collapse ⟹ slope-2 index ⟹ lower bound needs multiplicative
Hardy rescaling).

**The fix (ADDENDUM 3): split the index into `(k, d)`** — `k` the cofinal/`max` part (transformed by
the inversions, idempotently), `d` the additive cut-shift budget (transformed by cut-elimination,
additively). The effective norm budget of a node is `k + d`; the ω-rule's `n`-th premise sits at
`(max k n, d)`, i.e. budget `max(k,n) + d` (the `+d` OUTSIDE the `max`, shifting uniformly).

* `allInv` transforms only `k` (via `max`, leaving `d`) ⟹ idempotent, as in `Zk`.
* §19.6-commuting transforms only `d` (`d ↦ d + norm α`, leaving `k`) ⟹ absorbs the `+α` shift.
* Slope stays 1: `max(k,n) + d ≤ n + (k+d)`, so the lower bound's I∀ case is discharged by the banked
  `hardy_shift_lt_goodsteinLength` (`hardy α (max(k,n)+d) ≤ hardy α (n+(k+d)) < G n`). No rescaling.

This file: the inductive + the structural monotonicity lemmas (`mono_k`, `mono_d`, `mono_c`). The
inversion suite, cut reductions, `cutReduceAll`, `cutElimStep`, `cutElim` port from
`wip/BoundedZinfty.lean` by threading the inert `d` (inversions) / bumping `d` (the §19.6 payoff). WIP —
not in the build target.
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Hardy

namespace GoodsteinPA.SplitZinfty

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing

abbrev Form := SyntacticFormula ℒₒᵣ
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const
abbrev Seq := Finset Form
noncomputable def atomTrue (φ : Form) : Prop := Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The split-index witness-bounded `Z_∞` calculus** `Zᵏᵈ ⊢^{α}_{k,d,c} Γ`.
Effective norm budget `k + d`; ω-premise `n` at `(max k n, d)` (budget `max(k,n)+d`); witness bound
`hardy α (k+d)`. -/
inductive Zkd : ONote → ℕ → ℕ → ℕ → Seq → Prop
  | axL {α k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zkd α k d c Γ
  | verumR {α k d c Γ} (h : (⊤ : Form) ∈ Γ) : Zkd α k d c Γ
  | trueRel {α k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k + d) (hmem : Semiformula.rel r v ∈ Γ) : Zkd α k d c Γ
  | trueNrel {α k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k + d) (hmem : Semiformula.nrel r v ∈ Γ) : Zkd α k d c Γ
  | wk {α k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zkd α k d c Δ) : Zkd α k d c Γ
  | weak {α β k d c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (hsub : Δ ⊆ Γ) (dd : Zkd β k d c Δ) : Zkd α k d c Γ
  | andI {α βφ βψ k d c Γ} (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (dφ : Zkd βφ k d c (insert φ Γ)) (dψ : Zkd βψ k d c (insert ψ Γ)) :
      Zkd α k d c (insert (φ ⋏ ψ) Γ)
  | orI {α β k d c Γ} (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (dd : Zkd β k d c (insert φ (insert ψ Γ))) : Zkd α k d c (insert (φ ⋎ ψ) Γ)
  | allω {α k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n + d)
      (dd : ∀ n, Zkd (β n) (max k n) d c (insert (φ/[nm n]) Γ)) : Zkd α k d c (insert (∀⁰ φ) Γ)
  | exI {α β k d c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d) (hbound : n ≤ hardy α (k + d))
      (dd : Zkd β k d c (insert (φ/[nm n]) Γ)) : Zkd α k d c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ k d c Γ} (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (d₁ : Zkd βφ k d c (insert φ Γ)) (d₂ : Zkd βψ k d c (insert (∼φ) Γ)) : Zkd α k d c Γ

namespace Zkd

/-- **`k`-monotonicity** (the `max`/cofinal part; inversions raise this idempotently). -/
theorem mono_k : ∀ {α k d c Γ}, Zkd α k d c Γ → ∀ {k'}, k ≤ k' → Zkd α k' d c Γ := by
  intro α k d c Γ dd
  induction dd with
  | axL r v hp hn => intro k' _; exact Zkd.axL r v hp hn
  | verumR h => intro k' _; exact Zkd.verumR h
  | trueRel r v htrue hτ hmem =>
      intro k' hk; exact Zkd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | trueNrel r v htrue hτ hmem =>
      intro k' hk; exact Zkd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | wk hsub _ ih => intro k' hk; exact Zkd.wk hsub (ih hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact Zkd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro k' hk
      exact Zkd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro k' hk; exact Zkd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact Zkd.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by have := Nat.add_le_add_right (max_le_max hk (le_refl n)) d; omega))
        (fun n => ih n (max_le_max hk (le_refl n)))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro k' hk
      exact Zkd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro k' hk
      exact Zkd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hk) (ih₂ hk)

/-- **`d`-monotonicity** (the additive cut-shift budget; the §19.6-commuting case raises this). -/
theorem mono_d : ∀ {α k d c Γ}, Zkd α k d c Γ → ∀ {d'}, d ≤ d' → Zkd α k d' c Γ := by
  intro α k d c Γ dd
  induction dd with
  | axL r v hp hn => intro d' _; exact Zkd.axL r v hp hn
  | verumR h => intro d' _; exact Zkd.verumR h
  | trueRel r v htrue hτ hmem =>
      intro d' hd; exact Zkd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | trueNrel r v htrue hτ hmem =>
      intro d' hd; exact Zkd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hmem
  | wk hsub _ ih => intro d' hd; exact Zkd.wk hsub (ih hd)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro d' hd; exact Zkd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hd)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro d' hd
      exact Zkd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hd) (ihψ hd)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro d' hd; exact Zkd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hd)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro d' hd
      exact Zkd.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega))
        (fun n => ih n hd)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro d' hd
      exact Zkd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hd)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro d' hd
      exact Zkd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hd) (ih₂ hd)

/-- **`c`-monotonicity** (cut-rank). -/
theorem mono_c : ∀ {α k d c Γ}, Zkd α k d c Γ → ∀ {c'}, c ≤ c' → Zkd α k d c' Γ := by
  intro α k d c Γ dd
  induction dd with
  | axL r v hp hn => intro c' _; exact Zkd.axL r v hp hn
  | verumR h => intro c' _; exact Zkd.verumR h
  | trueRel r v htrue hτ hmem => intro c' _; exact Zkd.trueRel r v htrue hτ hmem
  | trueNrel r v htrue hτ hmem => intro c' _; exact Zkd.trueNrel r v htrue hτ hmem
  | wk hsub _ ih => intro c' hc; exact Zkd.wk hsub (ih hc)
  | weak hβ hβNF hαNF hτ hsub _ ih => intro c' hc; exact Zkd.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro c' hc; exact Zkd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zkd.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zkd.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro c' hc; exact Zkd.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zkd.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- Sequent weakening (height-preserving). -/
theorem weakening {α k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zkd α k d c Δ) : Zkd α k d c Γ := Zkd.wk hsub dd

/-! ### ∨-inversion (Towsner §19.2) — ported from `Zk` by threading the inert `d`.

The inversions preserve the index `(α,k,d,c)` (they do not grow `k` or `d`), so the port is mechanical:
`d` rides along untouched. The `max k n` in the `allω` case is the ω-rule's k-part (unchanged). -/

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
theorem orInv {φ ψ : Form} : ∀ {α k d c Γ}, Zkd α k d c Γ → (φ ⋎ ψ) ∈ Γ →
    Zkd α k d c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  have hφ0 : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
  have hψ0 : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
  intro α k d c Γ dd
  induction dd with
  | @axL α k d c Γ ar r v hp hn =>
      intro _
      refine Zkd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @verumR α k d c Γ h =>
      intro _
      exact Zkd.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)))
  | @trueRel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueRel r v htrue hτ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @trueNrel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueNrel r v htrue hτ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @wk α k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zkd.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zkd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zkd.weak hβ hβNF hαNF hτ (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zkd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI α βφ' βψ' k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zkd.wk (invPush (φ ⋎ ψ) φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zkd.wk (invPush (φ ⋎ ψ) ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zkd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hd : (φ ⋎ ψ) ∈ Γ₀
        · exact Zkd.weak hβ hβNF hαNF hτ (princOrSub Γ₀)
            (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd)))
        · rw [Finset.erase_eq_of_notMem hd]
          exact Zkd.weak hβ hβNF hαNF hτ (Finset.Subset.refl _) (by assumption)
      · have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have P := Zkd.wk (invPush2 (φ ⋎ ψ) φ' ψ' Γ₀)
          (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
        exact Zkd.wk (invPull (φ ⋎ ψ) hhd Γ₀) (Zkd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zkd (β n) (max k n) d c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zkd.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zkd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zkd.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zkd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zkd.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zkd.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zkd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

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
theorem andInvL {φ ψ : Form} : ∀ {α k d c Γ}, Zkd α k d c Γ → (φ ⋏ ψ) ∈ Γ →
    Zkd α k d c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  intro α k d c Γ dd
  induction dd with
  | @axL α k d c Γ ar r v hp hn =>
      intro _
      refine Zkd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α k d c Γ h =>
      intro _
      exact Zkd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueRel r v htrue hτ (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueNrel r v htrue hτ (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zkd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zkd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zkd.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zkd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ dφ _ ihφ ihψ =>
      intro hmem
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Zkd.weak hβφ hβφNF hαNF hτφ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihφ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zkd.weak hβφ hβφNF hαNF hτφ (Finset.Subset.refl _) dφ
      · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have Pφ := Zkd.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
        have Pψ := Zkd.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
        exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Zkd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zkd.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zkd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zkd (β n) (max k n) d c (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Zkd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zkd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zkd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zkd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zkd.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zkd.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zkd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∧-inversion, right** (Towsner §19.3): replace `φ ⋏ ψ` by `ψ`, same `(α,k,d,c)`. -/
theorem andInvR {φ ψ : Form} : ∀ {α k d c Γ}, Zkd α k d c Γ → (φ ⋏ ψ) ∈ Γ →
    Zkd α k d c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  intro α k d c Γ dd
  induction dd with
  | @axL α k d c Γ ar r v hp hn =>
      intro _
      refine Zkd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α k d c Γ h =>
      intro _
      exact Zkd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueRel r v htrue hτ (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueNrel r v htrue hτ (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zkd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zkd.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zkd.weak hβ hβNF hαNF hτ
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zkd.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ dψ ihφ ihψ =>
      intro hmem
      by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (φ ⋏ ψ) ∈ Γ₀
        · exact Zkd.weak hβψ hβψNF hαNF hτψ (princAllSub (φ ⋏ ψ) _ Γ₀)
            (ihψ (Finset.mem_insert_of_mem hh))
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zkd.weak hβψ hβψNF hαNF hτψ (Finset.Subset.refl _) dψ
      · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have Pφ := Zkd.wk (inv1Push (φ ⋏ ψ) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
        have Pψ := Zkd.wk (inv1Push (φ ⋏ ψ) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
        exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhd Γ₀)
          (Zkd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zkd.wk (inv1Push2 (φ ⋏ ψ) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zkd.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α k d c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zkd (β n) (max k n) d c (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) :=
        fun n => Zkd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zkd.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zkd.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zkd.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zkd.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zkd.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zkd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-- **∀-inversion** (Towsner §19.4) — the bound-critical one (the subformula bridge to `B` consumes it).
Result raises the **`k`-part** to `max k n₀` (`d` inert): the principal case's idempotent collapse
`max (max k n₀) n₀ = max k n₀` is exactly why the split index keeps `allInv` working. -/
theorem allInv {φ₀ : SyntacticSemiformula ℒₒᵣ 1} (n₀ : ℕ) :
    ∀ {α k d c Γ}, Zkd α k d c Γ → (∀⁰ φ₀) ∈ Γ →
      Zkd α (max k n₀) d c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  have hI0 : (φ₀/[nm n₀]) ≠ (∀⁰ φ₀) := Semiformula.ne_of_ne_complexity (by simp)
  intro α k d c Γ dd
  induction dd with
  | @axL α k d c Γ ar r v hp hn =>
      intro _
      refine Zkd.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α k d c Γ h =>
      intro _
      exact Zkd.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueRel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α k d c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zkd.trueNrel r v htrue (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
        (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α k d c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zkd.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zkd.wk ?_ (Zkd.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β k d c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zkd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zkd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) ?_
          (Zkd.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' k d c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Wedge.wedge, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zkd.wk (inv1Push (∀⁰ φ₀) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zkd.wk (inv1Push (∀⁰ φ₀) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zkd.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF
          (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
          (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) Pφ Pψ)
  | @orI α β k d c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Vee.vee, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zkd.wk (inv1Push2 (∀⁰ φ₀) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zkd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zkd.orI φ' ψ' hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d)) P)
  | @allω α k d c Γ₀ χ β hβ hβNF hαNF hτ dd ih =>
      intro hmem
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (Finset.mem_insert_of_mem hh)
          rw [max_eq_left (le_max_right k n₀)] at h
          exact Zkd.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (princAllSub (∀⁰ χ) _ Γ₀) h
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zkd.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (Finset.Subset.refl _) (dd n₀)
      · have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zkd (β n) (max (max k n₀) n) d c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := Zkd.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
          rw [show max (max k n₀) n = max (max k n) n₀ from by omega]
          exact h
        exact Zkd.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zkd.allω χ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega)) key)
  | @exI α β k d c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zkd.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zkd.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zkd.exI χ n hβ hβNF hαNF (lt_of_lt_of_le hτ (Nat.add_le_add_right (le_max_left _ _) d))
          (le_trans hbound (hardy_monotone _ (Nat.add_le_add_right (le_max_left _ _) d))) P)
  | @cut α βφ' βψ' k d c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zkd.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zkd.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zkd.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (lt_of_lt_of_le hτφ (Nat.add_le_add_right (le_max_left _ _) d))
        (lt_of_lt_of_le hτψ (Nat.add_le_add_right (le_max_left _ _) d)) P₁ P₂

end Zkd

end GoodsteinPA.SplitZinfty
