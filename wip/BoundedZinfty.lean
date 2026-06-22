/-
# `Zᵏ` — the witness-bounded `Z_∞` ω-rule calculus over real `ℒₒᵣ` syntax (step 1, Towsner §15)

The connecting spine (`ANALYSIS-2026-06-22-bounding-resolution.md` §"M4 scoping") needs ONE calculus
that the embedding (M4) lands in, cut-elimination (M5′) operates on, and whose cut-free fragment the
subformula bridge maps to the **done** lower bound `B` (`src/GoodsteinPA/LowerBound.lean`,
`lowerBound_hardy_selfcontained`).  `src/GoodsteinPA/Zinfty.lean` has the right rule shapes + a full
ε₀ cut-elimination but for the **unbounded** `(α,c)` calculus — the lap-4 finding showed that one is
off the headline path (no witness bound ⇒ the lower bound is false for it).

`Zᵏ` is that calculus, built **B-style** (`Prop`-valued, `ONote`-indexed, bound-as-parameter so there
are no `⨆`-suprema to represent in `ONote`) over Foundation's real `SyntacticFormula ℒₒᵣ`.  It adds to
`B` the two `(α,k)` side conditions Towsner §15 puts on the rules — the **truth-atom rule** (`τ α < k`)
and the **`∃`-witness bound** (`v ≤ h_α(k)`) — plus the connective/cut rules (`∧`,`∨`,`cut`) needed
because the embedding's cut formulas (PA induction instances) are arbitrary `ℒₒᵣ` formulas.

Indices: ordinal bound `α : ONote` (`< ε₀`, carried with `α.NF`), numeric Hardy index `k`, cut rank
`c`.  The ω-rule's `n`-th premise lives at the **raised** numeric index `max k n` (Towsner's `I∀`),
exactly as in `B.allI`.  This file: the inductive + the basic structural lemmas (`mono_k`, `weakening`,
`mono_c`).  Inversions, cut-reduction, and the embedding follow on later laps.  WIP — not in build target.
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.Basic.Model
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Hardy

namespace GoodsteinPA.BoundedZinfty

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing

/-- The closed formulas of `ℒₒᵣ` (full FO syntax, total de-Morgan `∼`, finite `complexity`). -/
abbrev Form := SyntacticFormula ℒₒᵣ

/-- The `n`-th numeral as a closed term, ready for substitution `φ/[nm n]`. -/
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const

/-- A sequent is a finite **set** of formulas (Towsner's `Γ`); set sequents ⇒ contraction is free. -/
abbrev Seq := Finset Form

/-- Atomic truth in the standard model `ℕ` (assignment-free once free vars are numeral-substituted —
the O2′-validated form; `=`/`<` are decidable in `ℕ`). -/
noncomputable def atomTrue (φ : Form) : Prop := Semiformula.Evalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The witness-bounded `Z_∞` calculus** `Zᵏ ⊢^{α}_{k,c} Γ` over real `ℒₒᵣ` syntax (Towsner §15).

* `axL` — clash identity axiom (`rel`/`nrel` together), no `k`-condition.
* `verumR` — `⊤` closes.
* `trueRel`/`trueNrel` — **truth axiom**: a true atom closes, side condition `τ α < k` (= `norm α < k`).
* `wk` — height-preserving sequent weakening (Towsner Lemma 19.1): enlarge `Γ`, same `(α,k,c)`.
* `weak` — combined ordinal-raise + weakening (β < α, budget `norm β < k`); raises the bound of an
  existing derivation, the move the inversions' principal cases need (cf. `B.weak`).
* `andI`/`orI` — the connective rules (premises at `β < α`).
* `allω` — the **ω-rule**: one premise per numeral `n`, the `n`-th at numeric index `max k n`.
* `exI` — **witness-bounded `∃`**: the numeral witness `n ≤ h_α(k)` (= `hardy α k`).
* `cut` — cut on a formula of `complexity < c`. -/
inductive Zk : ONote → ℕ → ℕ → Seq → Prop
  | axL {α k c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zk α k c Γ
  | verumR {α k c Γ} (h : (⊤ : Form) ∈ Γ) : Zk α k c Γ
  | trueRel {α k c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k) (hmem : Semiformula.rel r v ∈ Γ) : Zk α k c Γ
  | trueNrel {α k c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k) (hmem : Semiformula.nrel r v ∈ Γ) : Zk α k c Γ
  | wk {α k c Δ Γ} (hsub : Δ ⊆ Γ) (d : Zk α k c Δ) : Zk α k c Γ
  | weak {α β k c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k)
      (hsub : Δ ⊆ Γ) (d : Zk β k c Δ) : Zk α k c Γ
  | andI {α βφ βψ k c Γ} (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k) (hτψ : norm βψ < k)
      (dφ : Zk βφ k c (insert φ Γ)) (dψ : Zk βψ k c (insert ψ Γ)) :
      Zk α k c (insert (φ ⋏ ψ) Γ)
  | orI {α β k c Γ} (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k)
      (d : Zk β k c (insert φ (insert ψ Γ))) : Zk α k c (insert (φ ⋎ ψ) Γ)
  | allω {α k c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n)
      (d : ∀ n, Zk (β n) (max k n) c (insert (φ/[nm n]) Γ)) : Zk α k c (insert (∀⁰ φ) Γ)
  | exI {α β k c Γ} (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k) (hbound : n ≤ hardy α k)
      (d : Zk β k c (insert (φ/[nm n]) Γ)) : Zk α k c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ k c Γ} (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k) (hτψ : norm βψ < k)
      (d₁ : Zk βφ k c (insert φ Γ)) (d₂ : Zk βψ k c (insert (∼φ) Γ)) : Zk α k c Γ

namespace Zk

/-- **`k`-monotonicity** (Towsner Lemma 16.4, numeric part): raising the Hardy index relaxes every
side condition (`τ α < k` easier, witness bound `hardy α k` larger by `hardy_monotone`). -/
theorem mono_k : ∀ {α k c Γ}, Zk α k c Γ → ∀ {k'}, k ≤ k' → Zk α k' c Γ := by
  intro α k c Γ d
  induction d with
  | axL r v hp hn => intro k' _; exact Zk.axL r v hp hn
  | verumR h => intro k' _; exact Zk.verumR h
  | trueRel r v htrue hτ hmem => intro k' hk; exact Zk.trueRel r v htrue (lt_of_lt_of_le hτ hk) hmem
  | trueNrel r v htrue hτ hmem =>
      intro k' hk; exact Zk.trueNrel r v htrue (lt_of_lt_of_le hτ hk) hmem
  | wk hsub _ ih => intro k' hk; exact Zk.wk hsub (ih hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact Zk.weak hβ hβNF hαNF (lt_of_lt_of_le hτ hk) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro k' hk
      exact Zk.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ hk) (lt_of_lt_of_le hτψ hk)
        (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro k' hk; exact Zk.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ hk) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact Zk.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (max_le_max hk le_rfl))
        (fun n => ih n (max_le_max hk le_rfl))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro k' hk
      exact Zk.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ hk)
        (le_trans hbound (hardy_monotone _ hk)) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro k' hk
      exact Zk.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ hk) (lt_of_lt_of_le hτψ hk)
        (ih₁ hk) (ih₂ hk)

/-- **`c`-monotonicity**: raising the cut-rank bound preserves derivability (only `cut`'s
`complexity < c` side condition is affected). -/
theorem mono_c : ∀ {α k c Γ}, Zk α k c Γ → ∀ {c'}, c ≤ c' → Zk α k c' Γ := by
  intro α k c Γ d
  induction d with
  | axL r v hp hn => intro c' _; exact Zk.axL r v hp hn
  | verumR h => intro c' _; exact Zk.verumR h
  | trueRel r v htrue hτ hmem => intro c' _; exact Zk.trueRel r v htrue hτ hmem
  | trueNrel r v htrue hτ hmem => intro c' _; exact Zk.trueNrel r v htrue hτ hmem
  | wk hsub _ ih => intro c' hc; exact Zk.wk hsub (ih hc)
  | weak hβ hβNF hαNF hτ hsub _ ih => intro c' hc; exact Zk.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro c' hc
      exact Zk.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zk.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro c' hc; exact Zk.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro c' hc; exact Zk.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zk.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- **Height-preserving sequent weakening** (Towsner Lemma 19.1): direct `wk`. -/
theorem weakening {α k c Δ Γ} (hsub : Δ ⊆ Γ) (d : Zk α k c Δ) : Zk α k c Γ := Zk.wk hsub d

/-! ### Inversion lemmas (Towsner §19.2–19.4, parameter-style port)

The syntactic content feeding cut-elimination, and (the ∀-case) the subformula bridge to `B`.
Each is by structural induction; reshuffling uses height-preserving `wk`, and the *principal* case
raises the premise ordinal `β < α` back to the conclusion bound via `weak` (the move `B.allInv`
pioneered).  The `Finset` reshuffles are factored into standalone helpers (`invPush`/`invPull`/
`princOrSub`) so their `simp; tauto` runs in a clean context — inlining them inside the big
induction makes `DecidableEq Form` blow past the heartbeat limit. -/

/-- Pull a head formula `b` out through `insert φ (insert ψ (·.erase A))` (always valid). -/
private theorem invPush (A b : Form) (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert b s).erase A)) ⊆ insert b (insert φ (insert ψ (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Push a head formula `b ≠ A` back into the erased insert (the reverse reorder). -/
private theorem invPull (A : Form) {b : Form} (h : b ≠ A) (s : Seq) {φ ψ : Form} :
    insert b (insert φ (insert ψ (s.erase A))) ⊆ insert φ (insert ψ ((insert b s).erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | rfl | hx
  · exact Or.inr (Or.inr ⟨h, Or.inl rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨hx.1, Or.inr hx.2⟩)

/-- Pull two head formulas out through `insert φ (insert ψ (·.erase A))` (always valid). -/
private theorem invPush2 (A b₁ b₂ : Form) (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert b₁ (insert b₂ s)).erase A))
      ⊆ insert b₁ (insert b₂ (insert φ (insert ψ (s.erase A)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- The principal-`orI` reshuffle: the doubly-inserted premise collapses (idempotence). -/
private theorem princOrSub {A : Form} (s : Seq) {φ ψ : Form} :
    insert φ (insert ψ ((insert φ (insert ψ s)).erase A)) ⊆ insert φ (insert ψ (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∨-inversion.** If `φ ⋎ ψ` occurs in a `Zᵏ`-derivable sequent, replacing it by `φ` and `ψ` is
derivable at the same `(α,k,c)`.  Validates the connective machinery + `wk`. -/
theorem orInv {φ ψ : Form} : ∀ {α k c Γ}, Zk α k c Γ → (φ ⋎ ψ) ∈ Γ →
    Zk α k c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  have hφ0 : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
  have hψ0 : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
  intro α k c Γ d
  induction d with
  | @axL α k c Γ ar r v hp hn =>
      intro _
      refine Zk.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @verumR α k c Γ h =>
      intro _
      exact Zk.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)))
  | @trueRel α k c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zk.trueRel r v htrue hτ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @trueNrel α k c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zk.trueNrel r v htrue hτ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩)))
  | @wk α k c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zk.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zk.wk ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β k c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zk.weak hβ hβNF hαNF hτ (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zk.weak hβ hβNF hαNF hτ ?_ (by assumption)
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI α βφ' βψ' k c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zk.wk (invPush (φ ⋎ ψ) φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zk.wk (invPush (φ ⋎ ψ) ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zk.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zk.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ Pφ Pψ)
  | @orI α β k c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
      · obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
        rw [Finset.erase_insert_eq_erase]
        by_cases hd : (φ ⋎ ψ) ∈ Γ₀
        · -- the premise still carries `φ ⋎ ψ`; invert it there, collapse the duplicate, raise β→α
          exact Zk.weak hβ hβNF hαNF hτ (princOrSub Γ₀)
            (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd)))
        · -- `φ ⋎ ψ ∉ Γ₀`: the erase is a no-op, the premise IS the target; raise β→α
          rw [Finset.erase_eq_of_notMem hd]
          exact Zk.weak hβ hβNF hαNF hτ (Finset.Subset.refl _) (by assumption)
      · have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have P := Zk.wk (invPush2 (φ ⋎ ψ) φ' ψ' Γ₀)
          (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
        exact Zk.wk (invPull (φ ⋎ ψ) hhd Γ₀) (Zk.orI φ' ψ' hβ hβNF hαNF hτ P)
  | @allω α k c Γ₀ χ β hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zk (β n) (max k n) c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zk.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zk.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zk.allω χ β hβ hβNF hαNF hτ key)
  | @exI α β k c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zk.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zk.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zk.exI χ n hβ hβNF hαNF hτ hbound P)
  | @cut α βφ' βψ' k c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zk.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zk.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zk.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ P₁ P₂

/-! #### ∀-inversion (Towsner §19.4) — the bound-critical one

Mirrors `B.allInv` (the principal `allω` case raises `k → max k n₀` and lifts `β n₀ < α` via `weak`)
but over real `ℒₒᵣ` syntax, so it also needs the principal/non-principal split (`all_inj`) absent in
the single-`∀` `GForm` calculus.  This is the inversion the subformula bridge to `B` will consume. -/

/-- Single-insert push: pull a head `b` out through `insert e (·.erase A)` (always valid). -/
private theorem inv1Push (A e b : Form) (s : Seq) :
    insert e ((insert b s).erase A) ⊆ insert b (insert e (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Single-insert pull: push a head `b ≠ A` back into the erased insert. -/
private theorem inv1Pull (A e : Form) {b : Form} (h : b ≠ A) (s : Seq) :
    insert b (insert e (s.erase A)) ⊆ insert e ((insert b s).erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | hx
  · exact Or.inr ⟨h, Or.inl rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx.1, Or.inr hx.2⟩

/-- Single-insert push of two heads (for the `orI`/`andI` premises). -/
private theorem inv1Push2 (A e b₁ b₂ : Form) (s : Seq) :
    insert e ((insert b₁ (insert b₂ s)).erase A) ⊆ insert b₁ (insert b₂ (insert e (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- The principal-`allω` reshuffle: the doubly-inserted instance collapses (idempotence). -/
private theorem princAllSub (A e : Form) (s : Seq) :
    insert e ((insert e s).erase A) ⊆ insert e (s.erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **∀-inversion.** A `Zᵏ`-derivation of a sequent containing `∀⁰ φ₀` yields one of the instance
sequent `{φ₀/[nm n₀]} ∪ (Γ \ ∀⁰φ₀)` at the same ordinal `α`, raised numeric index `max k n₀`. -/
theorem allInv {φ₀ : SyntacticSemiformula ℒₒᵣ 1} (n₀ : ℕ) :
    ∀ {α k c Γ}, Zk α k c Γ → (∀⁰ φ₀) ∈ Γ →
      Zk α (max k n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  have hI0 : (φ₀/[nm n₀]) ≠ (∀⁰ φ₀) := Semiformula.ne_of_ne_complexity (by simp)
  intro α k c Γ d
  induction d with
  | @axL α k c Γ ar r v hp hn =>
      intro _
      refine Zk.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @verumR α k c Γ h =>
      intro _
      exact Zk.verumR (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))
  | @trueRel α k c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zk.trueRel r v htrue (lt_of_lt_of_le hτ (le_max_left _ _)) (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @trueNrel α k c Γ ar r v htrue hτ hmem =>
      intro _
      exact Zk.trueNrel r v htrue (lt_of_lt_of_le hτ (le_max_left _ _)) (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmem⟩))
  | @wk α k c Δ Γ hsub _ ih =>
      intro hmem
      by_cases hd : (∀⁰ φ₀) ∈ Δ
      · exact Zk.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hd)
      · refine Zk.wk ?_ (Zk.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @weak α β k c Δ Γ hβ hβNF hαNF hτ hsub _ ih =>
      intro hmem
      by_cases hd : (∀⁰ φ₀) ∈ Δ
      · exact Zk.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (le_max_left _ _))
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hd)
      · refine Zk.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (le_max_left _ _)) ?_
          (Zk.mono_k (by assumption) (le_max_left _ _))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI α βφ' βψ' k c Γ₀ φ' ψ' hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro hmem
      have hhead : (φ' ⋏ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Wedge.wedge, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have Pφ := Zk.wk (inv1Push (∀⁰ φ₀) _ φ' Γ₀) (ihφ (Finset.mem_insert_of_mem hmem0))
      have Pψ := Zk.wk (inv1Push (∀⁰ φ₀) _ ψ' Γ₀) (ihψ (Finset.mem_insert_of_mem hmem0))
      exact Zk.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zk.andI φ' ψ' hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (le_max_left _ _))
          (lt_of_lt_of_le hτψ (le_max_left _ _)) Pφ Pψ)
  | @orI α β k c Γ₀ φ' ψ' hβ hβNF hαNF hτ _ ih =>
      intro hmem
      have hhead : (φ' ⋎ ψ') ≠ (∀⁰ φ₀) := by intro h; simp [Vee.vee, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zk.wk (inv1Push2 (∀⁰ φ₀) _ φ' ψ' Γ₀)
        (ih (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0)))
      exact Zk.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zk.orI φ' ψ' hβ hβNF hαNF (lt_of_lt_of_le hτ (le_max_left _ _)) P)
  | @allω α k c Γ₀ χ β hβ hβNF hαNF hτ dd ih =>
      intro hmem
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · -- principal: `χ = φ₀`; use the `n₀`-th premise, erase any lingering `∀⁰φ₀`, raise β n₀ → α
        obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hd : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (Finset.mem_insert_of_mem hd)
          rw [max_eq_left (le_max_right k n₀)] at h
          exact Zk.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (princAllSub (∀⁰ χ) _ Γ₀) h
        · rw [Finset.erase_eq_of_notMem hd]
          exact Zk.weak (hβ n₀) (hβNF n₀) hαNF (hτ n₀) (Finset.Subset.refl _) (dd n₀)
      · -- side: `∀⁰χ ≠ ∀⁰φ₀`; invert inside every premise, re-apply the ω-rule
        have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zk (β n) (max (max k n₀) n) c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := Zk.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
          rw [show max (max k n₀) n = max (max k n) n₀ from by omega]
          exact h
        exact Zk.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zk.allω χ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega)) key)
  | @exI α β k c Γ₀ χ n hβ hβNF hαNF hτ hbound _ ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zk.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zk.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zk.exI χ n hβ hβNF hαNF (lt_of_lt_of_le hτ (le_max_left _ _))
          (le_trans hbound (hardy_monotone _ (le_max_left _ _))) P)
  | @cut α βφ' βψ' k c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zk.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zk.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zk.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (le_max_left _ _))
        (lt_of_lt_of_le hτψ (le_max_left _ _)) P₁ P₂

end Zk

end GoodsteinPA.BoundedZinfty
