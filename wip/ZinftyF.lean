/-
# Phase 2 crux — the `Z_∞` ω-rule calculus over Foundation's real PA syntax  [WIP]

Per HANDOFF-2026-06-22 ⭐ KEY FINDING: build `Z_∞` directly on Foundation's
`SyntacticFormula ℒₒᵣ` (full FO with total de-Morgan negation `∼`, finite `complexity : … → ℕ`,
genuine term substitution `φ/[t]`) instead of the standalone abstract `AForm` of
`wip/Zinfty.lean`. This **removes the `ℕ∞`/`⊤` blocker** that stalled `cutElimStep`: Foundation's
`complexity` is *always finite*, so `Provable α (c : ℕ)` (every cut formula has `complexity < c`)
is a non-vacuous predicate even for quantified cut formulas — the exact thing impossible on
abstract `AForm`, where `rk (all f)` could be `⊤`.

## Structural design decision (this lap) — set-based sequents ⭐
Sequents are **`Finset (SyntacticFormula ℒₒᵣ)`**, matching Towsner (his `Γ` is a finite *set*).
Consequence: **contraction is free** (`insert` is idempotent), so there is **no `contr` rule**.
This is not cosmetic: an explicit height-preserving `contr` rule makes the inversion lemmas
(§19.2–19.4) intractable — the principal-contraction case needs to re-invert a *remaining* copy
of the principal formula, which breaks both structural and ordinal-strong induction (the second
inversion is neither a structural subterm nor at a strictly smaller ordinal). Set sequents dissolve
that case entirely: `insert φ (insert φ Γ) = insert φ Γ` definitionally.

The calculus replaces Foundation's finitary eigenvariable `all` rule with the **ω-rule** `allω`
(one premise per numeral `n`, `Ordinal` height). Ordinal bound `o` and cut rank `cr` are computed
measures (structural recursion on the infinitely-branching tree).

Status: scaffolding. Calculus + measures + predicate-level inference API typecheck. The deep
lemmas (inversions §19.2–19.4, reductions §19.5–19.7) are the open frontier. Check with
`lake env lean wip/ZinftyF.lean`. Promote to `src/` once a milestone closes.
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Data.ENat.Lattice

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder

/-- The closed formulas of `ℒₒᵣ` (full first-order syntax, with total de-Morgan negation `∼`
and finite `complexity`). -/
abbrev Form := SyntacticFormula ℒₒᵣ

/-- The `n`-th numeral of `ℒₒᵣ` as a closed term, ready for substitution `φ/[nm n]`. -/
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const

/-- A sequent is a finite **set** of closed formulas (one-sided/Tait, Towsner's `Γ`). Set
sequents make contraction free (`insert` idempotent), so the calculus needs no `contr` rule. -/
abbrev Seq := Finset Form

/-- **The `Z_∞` calculus** over real `ℒₒᵣ` syntax. The `allω` (ω-rule) constructor stores one
sub-derivation per numeral `n`: from `insert (φ/[nm n]) Γ` for every `n`, conclude
`insert (∀⁰ φ) Γ`. -/
inductive Deriv : Seq → Type
  | axL {Γ : Seq} {k} (r : (ℒₒᵣ).Rel k) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Deriv Γ
  | verumR {Γ : Seq} (h : (⊤ : Form) ∈ Γ) : Deriv Γ
  | weak {Δ Γ : Seq} (d : Deriv Δ) (h : Δ ⊆ Γ) : Deriv Γ
  | andI {Γ : Seq} (φ ψ : Form) (dφ : Deriv (insert φ Γ)) (dψ : Deriv (insert ψ Γ)) :
      Deriv (insert (φ ⋏ ψ) Γ)
  | orI {Γ : Seq} (φ ψ : Form) (d : Deriv (insert φ (insert ψ Γ))) : Deriv (insert (φ ⋎ ψ) Γ)
  | allω {Γ : Seq} (φ : SyntacticSemiformula ℒₒᵣ 1)
      (d : (n : ℕ) → Deriv (insert (φ/[nm n]) Γ)) : Deriv (insert (∀⁰ φ) Γ)
  | exI {Γ : Seq} (φ : SyntacticSemiformula ℒₒᵣ 1) (t : Semiterm ℒₒᵣ ℕ 0)
      (d : Deriv (insert (φ/[t]) Γ)) : Deriv (insert (∃⁰ φ) Γ)
  | cut {Γ : Seq} (φ : Form) (d₁ : Deriv (insert φ Γ)) (d₂ : Deriv (insert (∼φ) Γ)) : Deriv Γ

namespace Deriv

/-- **Ordinal bound** (Towsner's superscript `α`). The ω-rule node takes the supremum of its
`ℕ`-many premise bounds, then `+1`. Weakening is height-preserving. -/
noncomputable def o : {Γ : Seq} → Deriv Γ → Ordinal.{0}
  | _, axL _ _ _ _ => 0
  | _, verumR _ => 0
  | _, weak d _ => o d
  | _, andI _ _ dφ dψ => max (o dφ) (o dψ) + 1
  | _, orI _ _ d => o d + 1
  | _, allω _ d => (⨆ n, o (d n)) + 1
  | _, exI _ _ d => o d + 1
  | _, cut _ d₁ d₂ => max (o d₁) (o d₂) + 1

/-- **Cut rank** (Towsner's subscript `c`): the max over cut formulas `φ` used of
`complexity φ + 1`, in `ℕ∞` so the ω-rule supremum is well-defined. *Crucially finite per cut*:
`complexity φ : ℕ`, so `Provable α (c:ℕ)` meaningfully bounds quantified cut formulas. A cut-free
derivation has `cr = 0`. -/
noncomputable def cr : {Γ : Seq} → Deriv Γ → ℕ∞
  | _, axL _ _ _ _ => 0
  | _, verumR _ => 0
  | _, weak d _ => cr d
  | _, andI _ _ dφ dψ => max (cr dφ) (cr dψ)
  | _, orI _ _ d => cr d
  | _, allω _ d => ⨆ n, cr (d n)
  | _, exI _ _ d => cr d
  | _, cut φ d₁ d₂ => max (φ.complexity + 1 : ℕ∞) (max (cr d₁) (cr d₂))

/-- The bounded-derivability predicate `Z_∞ ⊢^{α}_c Γ`: a derivation with ordinal bound `≤ α`
and cut rank `≤ c` (every cut formula has `complexity < c`). -/
def Provable (α : Ordinal.{0}) (c : ℕ) (Γ : Seq) : Prop :=
  ∃ d : Deriv Γ, o d ≤ α ∧ cr d ≤ (c : ℕ∞)

/-- The ω-rule bound strictly dominates each premise bound. -/
theorem o_allω_gt {Γ : Seq} (φ : SyntacticSemiformula ℒₒᵣ 1)
    (d : (n : ℕ) → Deriv (insert (φ/[nm n]) Γ)) (n : ℕ) : o (d n) < o (allω φ d) := by
  have h : o (d n) ≤ ⨆ m, o (d m) := Ordinal.le_iSup (fun m => o (d m)) n
  calc o (d n) ≤ ⨆ m, o (d m) := h
    _ < (⨆ m, o (d m)) + 1 := lt_add_of_pos_right _ one_pos
    _ = o (allω φ d) := by simp only [o]

/-- **Bound monotonicity** (Towsner Lemma 16.4): relax either recorded bound. -/
theorem Provable.mono {α β : Ordinal.{0}} {c c' : ℕ} (hα : α ≤ β) (hc : c ≤ c') {Γ : Seq} :
    Provable α c Γ → Provable β c' Γ := by
  rintro ⟨d, ho, hcr⟩
  exact ⟨d, ho.trans hα, hcr.trans (by exact_mod_cast hc)⟩

/-- **Sequent weakening** (Towsner Lemma 19.1): enlarge the sequent without raising bounds. -/
theorem Provable.weakening {α : Ordinal.{0}} {c : ℕ} {Γ Δ : Seq} (h : Γ ⊆ Δ) :
    Provable α c Γ → Provable α c Δ := by
  rintro ⟨d, ho, hcr⟩
  exact ⟨Deriv.weak d h, by simpa [Deriv.o] using ho, by simpa [Deriv.cr] using hcr⟩

/-- Provability respects set equality of sequents. -/
theorem Provable.cast {α : Ordinal.{0}} {c : ℕ} {Γ Δ : Seq} (e : Γ = Δ) :
    Provable α c Γ → Provable α c Δ := fun h => e ▸ h

/-- Identity axiom: `rel r v` and `nrel r v` together close at bound `0`, cut rank `0`. -/
theorem Provable.axL {Γ : Seq} {k} (r : (ℒₒᵣ).Rel k) (v)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) : Provable 0 0 Γ :=
  ⟨Deriv.axL r v hp hn, by simp [Deriv.o], by simp [Deriv.cr]⟩

/-- `⊤` closes a sequent at bound `0`, cut rank `0`. -/
theorem Provable.verumR {Γ : Seq} (h : (⊤ : Form) ∈ Γ) : Provable 0 0 Γ :=
  ⟨Deriv.verumR h, by simp [Deriv.o], by simp [Deriv.cr]⟩

/-- Predicate-level `∧`-introduction. -/
theorem Provable.andI {α β : Ordinal.{0}} {c : ℕ} {Γ : Seq} (φ ψ : Form)
    (hφ : Provable α c (insert φ Γ)) (hψ : Provable β c (insert ψ Γ)) :
    Provable (max α β + 1) c (insert (φ ⋏ ψ) Γ) := by
  rcases hφ with ⟨dφ, hoφ, hcφ⟩
  rcases hψ with ⟨dψ, hoψ, hcψ⟩
  refine ⟨Deriv.andI φ ψ dφ dψ, ?_, ?_⟩
  · simp only [Deriv.o]; exact add_le_add (max_le_max hoφ hoψ) le_rfl
  · simp only [Deriv.cr]; exact max_le hcφ hcψ

/-- Predicate-level `∨`-introduction. -/
theorem Provable.orI {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (φ ψ : Form)
    (h : Provable α c (insert φ (insert ψ Γ))) : Provable (α + 1) c (insert (φ ⋎ ψ) Γ) := by
  rcases h with ⟨d, ho, hcr⟩
  exact ⟨Deriv.orI φ ψ d, by simpa [Deriv.o] using add_le_add_right ho 1,
    by simpa [Deriv.cr] using hcr⟩

/-- Predicate-level `∃`-introduction (witness rule). -/
theorem Provable.exI {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (φ : SyntacticSemiformula ℒₒᵣ 1)
    (t : Semiterm ℒₒᵣ ℕ 0) (h : Provable α c (insert (φ/[t]) Γ)) :
    Provable (α + 1) c (insert (∃⁰ φ) Γ) := by
  rcases h with ⟨d, ho, hcr⟩
  exact ⟨Deriv.exI φ t d, by simpa [Deriv.o] using add_le_add_right ho 1,
    by simpa [Deriv.cr] using hcr⟩

/-- **Predicate-level ω-rule.** From a uniform-cut-rank family of premises with ordinal bounds
`β n`, conclude `∀` at bound `(⨆ n, β n) + 1`. -/
theorem Provable.allω {β : ℕ → Ordinal.{0}} {c : ℕ} {Γ : Seq}
    (φ : SyntacticSemiformula ℒₒᵣ 1) (h : ∀ n, Provable (β n) c (insert (φ/[nm n]) Γ)) :
    Provable ((⨆ n, β n) + 1) c (insert (∀⁰ φ) Γ) := by
  choose d ho hcr using h
  have hsup : (⨆ n, o (d n)) ≤ ⨆ n, β n :=
    Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup β n)
  refine ⟨Deriv.allω φ d, ?_, ?_⟩
  · simp only [Deriv.o]; exact add_le_add hsup le_rfl
  · simp only [Deriv.cr]; exact iSup_le hcr

/-- **Contraction is free** (the payoff of set sequents): a duplicate insert collapses. -/
theorem Provable.contr {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (φ : Form)
    (h : Provable α c (insert φ (insert φ Γ))) : Provable α c (insert φ Γ) := by
  simpa [Finset.insert_idem] using h

/-- **Predicate-level cut.** From `insert φ Γ` and `insert (∼φ) Γ` at cut rank `≤ c` with
`complexity φ < c`, conclude `Γ` at the same cut rank. -/
theorem Provable.cut {α β : Ordinal.{0}} {c : ℕ} {Γ : Seq} (χ : Form)
    (hc : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞))
    (h₁ : Provable α c (insert χ Γ)) (h₂ : Provable β c (insert (∼χ) Γ)) :
    Provable (max α β + 1) c Γ := by
  rcases h₁ with ⟨d₁, ho₁, hcr₁⟩
  rcases h₂ with ⟨d₂, ho₂, hcr₂⟩
  refine ⟨Deriv.cut χ d₁ d₂, ?_, ?_⟩
  · simp only [Deriv.o]; exact add_le_add (max_le_max ho₁ ho₂) le_rfl
  · simp only [Deriv.cr]; exact max_le hc (max_le hcr₁ hcr₂)

/-! ### Inversion lemmas (Towsner §19.2–19.4)

The genuine syntactic content feeding `cutElimStep`. `orInv` (∨-inversion) is the template:
proved by **structural induction on the derivation** (tractable precisely because set sequents
removed the explicit `contr` rule — see the design note above). The other inversions (∧, ω/∀)
follow the same pattern and are next. -/

section Inversion

variable {φ ψ : Form}

/-- Reorder helper: inverting under an `insert a` lands inside `insert a` of the inversion. -/
private theorem invPush (a : Form) (s : Seq) :
    insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ)))
      ⊆ insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ)))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper, valid when the head `a` is not the inverted formula. -/
private theorem invPull {a : Form} (h : a ≠ (φ ⋎ ψ)) (s : Seq) :
    insert a (insert φ (insert ψ (s.erase (φ ⋎ ψ))))
      ⊆ insert φ (insert ψ ((insert a s).erase (φ ⋎ ψ))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-- **∨-inversion (Towsner §19.2 analog).** If `φ ⋎ ψ` occurs in a `Z_∞`-derivable sequent, then
replacing it by `φ` and `ψ` is derivable at the *same* ordinal bound and cut rank. Proved by
structural induction on the derivation. -/
theorem orInvAux {c : ℕ} : ∀ {Γ : Seq} (d : Deriv Γ), cr d ≤ (c : ℕ∞) → (φ ⋎ ψ) ∈ Γ →
    Provable (o d) c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  have hφ0 : φ ≠ (φ ⋎ ψ) := Semiformula.ne_or_left φ ψ
  have hψ0 : ψ ≠ (φ ⋎ ψ) := Semiformula.ne_or_right φ ψ
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by intro h; simp [Vee.vee] at h, hn⟩
    simp only [Deriv.o]
    exact (Provable.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _
    have ht : (⊤ : Form) ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact (Provable.verumR (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ht))).mono
      le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (φ ⋎ ψ) ∈ Δ
    · exact (ih hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub)))
    · have base : Provable (o d') c Δ := ⟨d', le_rfl, hcr⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋏ ψ') ≠ (φ ⋎ ψ) := by intro h; simp [Wedge.wedge, Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : cr dφ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : cr dψ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).weakening (invPush φ' Γ₀)
    have Pψ := (ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).weakening (invPush ψ' Γ₀)
    exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (φ' ⋎ ψ') = (φ ⋎ ψ)
    · -- principal: φ' ⋎ ψ' = φ ⋎ ψ
      obtain ⟨rfl, rfl⟩ := (Semiformula.or_inj _ _ _ _).mp hhd.symm
      by_cases hd : (φ ⋎ ψ) ∈ Γ₀
      · have P := ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd))
        refine (P.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : Provable (o d') c (insert φ (insert ψ Γ₀)) := ⟨d', le_rfl, hcr⟩
        refine (base.weakening ?_).mono (le_of_lt (lt_add_of_pos_right _ one_pos)) le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | rfl | hx
        · tauto
        · tauto
        · exact Or.inr (Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩)
    · -- side: head ≠ the inverted formula
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have hsub : insert φ (insert ψ ((insert φ' (insert ψ' Γ₀)).erase (φ ⋎ ψ)))
            ⊆ insert φ' (insert ψ' (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      have P := (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
      exact (Provable.orI φ' ψ' P).weakening (invPull hhd Γ₀)
  | @allω Γ₀ χ d ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (o (d n)) c (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) :=
      fun n => (ih n (le_trans (le_iSup (fun m => cr (d m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (invPush (χ/[nm n]) Γ₀)
    exact (Provable.allω χ key).weakening (invPull hhead Γ₀)
  | @exI Γ₀ χ t d ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPush (χ/[t]) Γ₀)
    exact (Provable.exI χ t P).weakening (invPull hhead Γ₀)
  | @cut Γ₀ χ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcχ : (χ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : cr d₁ ≤ (c : ℕ∞) := (le_max_left (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cr d₂ ≤ (c : ℕ∞) := (le_max_right (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).weakening (invPush χ Γ₀)
    have P₂ := (ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).weakening (invPush (∼χ) Γ₀)
    exact Provable.cut χ hcχ P₁ P₂

/-- **∨-inversion at a relaxed bound** (the form used downstream). -/
theorem Provable.orInv {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (hmem : (φ ⋎ ψ) ∈ Γ)
    (h : Provable α c Γ) : Provable α c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (orInvAux d hcr hmem).mono ho le_rfl

end Inversion

/-! ### ω-rule inversion (Towsner §19.4)

The distinctive infinitary inversion: inverting a `∀⁰ χ` yields, for *each* numeral `n`, the
instance `χ/[nm n]`. The principal case `allω` supplies exactly the right instance from its
ω-indexed premise family. Same structural-induction template as `orInvAux`. -/

section InversionAll

variable {χ : SyntacticSemiformula ℒₒᵣ 1}

/-- Reorder helper (single insert): invert under `insert a`, push it outside. -/
private theorem invPush1 (b a : Form) (e : Form) (s : Seq) :
    insert b ((insert a s).erase e) ⊆ insert a (insert b (s.erase e)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- Reverse reorder helper (single insert), valid when the head `a` is not the erased formula. -/
private theorem invPull1 (b : Form) {a e : Form} (h : a ≠ e) (s : Seq) :
    insert a (insert b (s.erase e)) ⊆ insert b ((insert a s).erase e) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

/-- **ω/∀-inversion (Towsner §19.4).** If `∀⁰ χ` occurs in a `Z_∞`-derivable sequent, then for
every numeral `n` the instance `χ/[nm n]` is derivable at the *same* ordinal bound and cut rank.
Proved by structural induction on the derivation (`n` fixed). -/
theorem allInvAux {c : ℕ} (n : ℕ) : ∀ {Γ : Seq} (d : Deriv Γ), cr d ≤ (c : ℕ∞) →
    (∀⁰ χ) ∈ Γ → Provable (o d) c (insert (χ/[nm n]) (Γ.erase (∀⁰ χ))) := by
  have hb0 : (χ/[nm n]) ≠ (∀⁰ χ) := Semiformula.ne_of_ne_complexity (by simp)
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact (Provable.axL r v (Finset.mem_insert_of_mem hr)
      (Finset.mem_insert_of_mem hn')).mono le_rfl (Nat.zero_le c)
  | @verumR Γ h =>
    intro _ _
    have ht : (⊤ : Form) ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact (Provable.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (∀⁰ χ) ∈ Δ
    · exact (ih hcr hd).weakening
        (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))
    · have base : Provable (o d') c Δ := ⟨d', le_rfl, hcr⟩
      refine base.weakening ?_
      intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋏ ψ') ≠ (∀⁰ χ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcrφ : cr dφ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : cr dψ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have Pφ := (ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ φ' _ Γ₀)
    have Pψ := (ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ ψ' _ Γ₀)
    exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull1 _ hhead Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋎ ψ') ≠ (∀⁰ χ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hsub : insert (χ/[nm n]) ((insert φ' (insert ψ' Γ₀)).erase (∀⁰ χ))
          ⊆ insert φ' (insert ψ' (insert (χ/[nm n]) (Γ₀.erase (∀⁰ χ)))) := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
    have P := (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening hsub
    exact (Provable.orI φ' ψ' P).weakening (invPull1 _ hhead Γ₀)
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (∀⁰ χ') = (∀⁰ χ)
    · -- principal: χ' = χ (obtain rfl eliminates χ, keeping χ')
      obtain rfl := (Semiformula.all_inj _ _).mp hhd
      have hcrn : cr (d' n) ≤ (c : ℕ∞) := le_trans (le_iSup (fun m => cr (d' m)) n) hcr
      have hbound : o (d' n) ≤ (⨆ m, o (d' m)) + 1 :=
        le_trans (Ordinal.le_iSup (fun m => o (d' m)) n) (le_of_lt (lt_add_of_pos_right _ one_pos))
      by_cases hd : (∀⁰ χ') ∈ Γ₀
      · have P := ih n hcrn (Finset.mem_insert_of_mem hd)
        refine (P.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      · have base : Provable (o (d' n)) c (insert (χ'/[nm n]) Γ₀) := ⟨d' n, le_rfl, hcrn⟩
        refine (base.weakening ?_).mono hbound le_rfl
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
        rcases hx with rfl | hx
        · tauto
        · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
    · -- side
      have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      have key : ∀ m, Provable (o (d' m)) c
          (insert (χ'/[nm m]) (insert (χ/[nm n]) (Γ₀.erase (∀⁰ χ)))) := fun m =>
        (ih m (le_trans (le_iSup (fun j => cr (d' j)) m) hcr)
          (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ (χ'/[nm m]) _ Γ₀)
      exact (Provable.allω χ' key).weakening (invPull1 _ hhd Γ₀)
  | @exI Γ₀ χ' t d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (∀⁰ χ) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ (χ'/[t]) _ Γ₀)
    exact (Provable.exI χ' t P).weakening (invPull1 _ hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : cr d₁ ≤ (c : ℕ∞) := (le_max_left (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cr d₂ ≤ (c : ℕ∞) := (le_max_right (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have P₁ := (ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).weakening (invPush1 _ ξ _ Γ₀)
    have P₂ := (ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).weakening (invPush1 _ (∼ξ) _ Γ₀)
    exact Provable.cut ξ hcξ P₁ P₂

/-- **ω-inversion at a relaxed bound** (the form used downstream). -/
theorem Provable.allInv {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (hmem : (∀⁰ χ) ∈ Γ) (n : ℕ)
    (h : Provable α c Γ) : Provable α c (insert (χ/[nm n]) (Γ.erase (∀⁰ χ))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (allInvAux n d hcr hmem).mono ho le_rfl

end InversionAll

/-! ### ∧-inversion (Towsner §19.3)

Inverting `φ ⋏ ψ` yields *both* conjuncts (two conclusions). Standard FO inversion; same template
as `orInvAux`, principal case `andI` supplies the two conjunct premises. We prove the conjunction
in one induction (`andInvAux`) and expose each side as a corollary. -/

section InversionAnd

variable {φ ψ : Form}

/-- **∧-inversion (Towsner §19.3).** If `φ ⋏ ψ` occurs in a `Z_∞`-derivable sequent, then both
`φ` and `ψ` (with the conjunction erased) are derivable at the same ordinal bound and cut rank. -/
theorem andInvAux {c : ℕ} : ∀ {Γ : Seq} (d : Deriv Γ), cr d ≤ (c : ℕ∞) → (φ ⋏ ψ) ∈ Γ →
    Provable (o d) c (insert φ (Γ.erase (φ ⋏ ψ))) ∧
      Provable (o d) c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  have hφ0 : φ ≠ (φ ⋏ ψ) := Semiformula.ne_of_ne_complexity (by simp)
  have hψ0 : ψ ≠ (φ ⋏ ψ) := Semiformula.ne_of_ne_complexity (by simp)
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact ⟨(Provable.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c),
      (Provable.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')).mono
        le_rfl (Nat.zero_le c)⟩
  | @verumR Γ h =>
    intro _ _
    have ht : (⊤ : Form) ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact ⟨(Provable.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c),
      (Provable.verumR (Finset.mem_insert_of_mem ht)).mono le_rfl (Nat.zero_le c)⟩
  | @weak Δ Γ d' hsub ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (φ ⋏ ψ) ∈ Δ
    · exact ⟨(ih hcr hd).1.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)),
        (ih hcr hd).2.weakening
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))⟩
    · have base : Provable (o d') c Δ := ⟨d', le_rfl, hcr⟩
      have hsub' : Δ ⊆ Δ.erase (φ ⋏ ψ) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hx⟩
      have hΔ : Δ ⊆ Γ.erase (φ ⋏ ψ) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
      exact ⟨base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx)),
        base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx))⟩
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcrφ : cr dφ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcrψ : cr dψ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have hbφ : o dφ ≤ max (o dφ) (o dψ) + 1 :=
      le_trans (le_max_left _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    have hbψ : o dψ ≤ max (o dφ) (o dψ) + 1 :=
      le_trans (le_max_right _ _) (le_of_lt (lt_add_of_pos_right _ one_pos))
    by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
    · -- principal: φ' = φ, ψ' = ψ
      obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
      have hL : Provable (max (o dφ) (o dψ) + 1) c (insert φ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihφ hcrφ (Finset.mem_insert_of_mem hd)).1.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : Provable (o dφ) c (insert φ Γ₀) := ⟨dφ, le_rfl, hcrφ⟩
          refine (base.weakening ?_).mono hbφ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      have hR : Provable (max (o dφ) (o dψ) + 1) c (insert ψ ((insert (φ ⋏ ψ) Γ₀).erase (φ ⋏ ψ))) := by
        by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihψ hcrψ (Finset.mem_insert_of_mem hd)).2.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : Provable (o dψ) c (insert ψ Γ₀) := ⟨dψ, le_rfl, hcrψ⟩
          refine (base.weakening ?_).mono hbψ le_rfl
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      exact ⟨hL, hR⟩
    · -- side
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      refine ⟨?_, ?_⟩
      · have Pφ := ((ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).1).weakening (invPush1 _ φ' _ Γ₀)
        have Pψ := ((ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).1).weakening (invPush1 _ ψ' _ Γ₀)
        exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull1 _ hhd Γ₀)
      · have Pφ := ((ihφ hcrφ (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ φ' _ Γ₀)
        have Pψ := ((ihψ hcrψ (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ ψ' _ Γ₀)
        exact (Provable.andI φ' ψ' Pφ Pψ).weakening (invPull1 _ hhd Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Form,
        Provable (o d') c (insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))) →
        Provable (o d' + 1) c (insert b ((insert (φ' ⋎ ψ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have hsub : insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))
            ⊆ insert φ' (insert ψ' (insert b (Γ₀.erase (φ ⋏ ψ)))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      exact (Provable.orI φ' ψ' (P.weakening hsub)).weakening (invPull1 _ hhead Γ₀)
    exact ⟨mk φ ((ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).1),
      mk ψ ((ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).2)⟩
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Form,
        (∀ m, Provable (o (d' m)) c (insert b ((insert (χ'/[nm m]) Γ₀).erase (φ ⋏ ψ)))) →
        Provable ((⨆ m, o (d' m)) + 1) c (insert b ((insert (∀⁰ χ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have key : ∀ m, Provable (o (d' m)) c (insert (χ'/[nm m]) (insert b (Γ₀.erase (φ ⋏ ψ)))) :=
        fun m => (P m).weakening (invPush1 _ (χ'/[nm m]) _ Γ₀)
      exact (Provable.allω χ' key).weakening (invPull1 _ hhead Γ₀)
    refine ⟨mk φ (fun m => ?_), mk ψ (fun m => ?_)⟩
    · exact (ih m (le_trans (le_iSup (fun j => cr (d' j)) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).1
    · exact (ih m (le_trans (le_iSup (fun j => cr (d' j)) m) hcr)
        (Finset.mem_insert_of_mem hmem0)).2
  | @exI Γ₀ χ' t d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    refine ⟨?_, ?_⟩
    · have P := ((ih hcr (Finset.mem_insert_of_mem hmem0)).1).weakening (invPush1 _ (χ'/[t]) _ Γ₀)
      exact (Provable.exI χ' t P).weakening (invPull1 _ hhead Γ₀)
    · have P := ((ih hcr (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ (χ'/[t]) _ Γ₀)
      exact (Provable.exI χ' t P).weakening (invPull1 _ hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ (c : ℕ∞) := (le_max_left _ _).trans hcr
    have hcr1 : cr d₁ ≤ (c : ℕ∞) := (le_max_left (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cr d₂ ≤ (c : ℕ∞) := (le_max_right (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    refine ⟨?_, ?_⟩
    · have P₁ := ((ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).1).weakening (invPush1 _ ξ _ Γ₀)
      have P₂ := ((ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).1).weakening (invPush1 _ (∼ξ) _ Γ₀)
      exact Provable.cut ξ hcξ P₁ P₂
    · have P₁ := ((ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).2).weakening (invPush1 _ ξ _ Γ₀)
      have P₂ := ((ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).2).weakening (invPush1 _ (∼ξ) _ Γ₀)
      exact Provable.cut ξ hcξ P₁ P₂

/-- **∧-inversion, left conjunct, relaxed bound.** -/
theorem Provable.andInvL {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : Provable α c Γ) : Provable α c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (andInvAux d hcr hmem).1.mono ho le_rfl

/-- **∧-inversion, right conjunct, relaxed bound.** -/
theorem Provable.andInvR {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (hmem : (φ ⋏ ψ) ∈ Γ)
    (h : Provable α c Γ) : Provable α c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  rcases h with ⟨d, ho, hcr⟩
  exact (andInvAux d hcr hmem).2.mono ho le_rfl

end InversionAnd

/-- Towsner **Def 19.8**: `ω`-tower over `α` of height `c` (`ω_c^α`), bottom-up:
`ω_0^α = α`, `ω_{c+1}^α = ω_c^(ω^α)`. The cut-elimination ordinal blow-up. -/
noncomputable def omegaTower : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, α => α
  | c + 1, α => omegaTower c (Ordinal.omega0 ^ α)

@[simp] theorem omegaTower_zero (α : Ordinal.{0}) : omegaTower 0 α = α := rfl

@[simp] theorem omegaTower_one (α : Ordinal.{0}) : omegaTower 1 α = Ordinal.omega0 ^ α := rfl

/-- **Cut-reduction lemma** (Towsner §19.5–19.6) — the narrowed open core under `cutElimStep`,
now that all three inversions (`orInv`/`andInv`/`allInv`) are proved. Combine two cut-rank-`≤ c`
derivations of `insert φ Γ` and `insert (∼φ) Γ`, where the cut formula `φ` has `complexity ≤ c`,
into a single cut-rank-`≤ c` derivation of `Γ` — i.e. *eliminate* the top cut rather than keep it.

Proof (next lap): induction on the `insert (∼φ) Γ` derivation; when `∼φ` is principal, invert the
*matching* connective in the `insert φ Γ` derivation (∨↔∧ via `orInv`/`andInv`, ∀↔∃ via `allInv` at
the ∃-witness numeral), giving cuts on the strictly smaller subformulas (`complexity < c`), then
recurse. NOTE: the honest ordinal bound is the **natural (Hessenberg) sum** `α ♯ β`
(`Ordinal.nadd`), not `α + β`; revisit once the proof shape is fixed. Also decide whether a numeric
Hardy `k` index must be threaded through `Provable` (Towsner carries `h_{ω^α}(k)` in 19.6/19.7). -/
theorem Provable.cutReduce {α β : Ordinal.{0}} {c : ℕ} {φ : Form} {Γ : Seq}
    (hc : φ.complexity ≤ c) (h₁ : Provable α c (insert φ Γ))
    (h₂ : Provable β c (insert (∼φ) Γ)) : Provable (α + β) c Γ := by
  sorry

/-- **One level of cut elimination** (Towsner Thm 19.7). Reducing the cut rank by one raises the
ordinal bound to `ω^α`. *(Open: the principal `cut`-on-rank-`c` case calls `cutReduce`; the rest is
a transfinite induction over the derivation.)* -/
theorem Provable.cutElimStep {α : Ordinal.{0}} {c : ℕ} {Γ : Seq}
    (h : Provable α (c + 1) Γ) : Provable (Ordinal.omega0 ^ α) c Γ := by
  sorry

/-- **Full cut elimination** (Towsner Thm 19.9): iterate `cutElimStep` `c` times, reaching a
cut-free derivation at ordinal `ω_c^α`. -/
theorem Provable.cutElim {α : Ordinal.{0}} {c : ℕ} {Γ : Seq}
    (h : Provable α c Γ) : Provable (omegaTower c α) 0 Γ := by
  induction c generalizing α with
  | zero => simpa [omegaTower] using h
  | succ c ih => exact ih (Provable.cutElimStep h)

end Deriv

end GoodsteinPA.ZinftyF
