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

/-- Towsner **Def 19.8**: `ω`-tower over `α` of height `c` (`ω_c^α`), bottom-up:
`ω_0^α = α`, `ω_{c+1}^α = ω_c^(ω^α)`. The cut-elimination ordinal blow-up. -/
noncomputable def omegaTower : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, α => α
  | c + 1, α => omegaTower c (Ordinal.omega0 ^ α)

@[simp] theorem omegaTower_zero (α : Ordinal.{0}) : omegaTower 0 α = α := rfl

@[simp] theorem omegaTower_one (α : Ordinal.{0}) : omegaTower 1 α = Ordinal.omega0 ^ α := rfl

/-- **One level of cut elimination** (Towsner Thm 19.7). Reducing the cut rank by one raises the
ordinal bound to `ω^α`. *(Open: §19 inversions 19.2–19.4 + reductions 19.5–19.6.)* -/
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
