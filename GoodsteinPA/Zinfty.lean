/-
# Phase 2 crux — the `Z_∞` ω-rule calculus + cut-elimination over Foundation's real PA syntax

**Status: COMPLETE and `#print axioms`-clean** (`[propext, Classical.choice, Quot.sound]`).
This file machine-checks the full Gentzen-style cut-elimination for the infinitary ω-rule
calculus `Z_∞`, the deep core (milestone **M5**) of Route B (Towsner, *Goodstein's Theorem, ε₀,
and Unprovability*, §16–§19). It does **not** yet connect to the headline `peano_not_proves_goodstein`
— that needs the embedding `PA⁺ ↪ Z_∞` (M4, §16/§18), the cut-free lower bound (M6, §17), and the
assembly (M7, §20). Contents:
  • the `Z_∞` calculus `Deriv` (ω-rule `allω`, numeral-witness `exI`) + measures `o` (ordinal
    bound) / `cr` (cut rank), and the predicate `Provable α c Γ`;
  • the predicate-level inference API + `mono`/`weakening`/`contr` (free, via set sequents);
  • inversions **§19.2–19.4** (`orInv`, `andInvL/R`, `allInv`);
  • cut reductions **§19.5** (`cutReduceConj/Disj`) and **§19.6** (`cutReduceAll`);
  • atomic + `⊥` cut elimination (`atomCut`, `removeFalsum`) — *no truth layer needed*;
  • **§19.7** `cutElimStep` (rank `c+1 → c`, bound `ω^α`) and **§19.9** `cutElim` (cut-free).

Natural (Hessenberg) sum is **absent from mathlib v4.31.0**; all reduction bounds use ordinary
ordinal `+` with a `+1` slack, kept below `ω^(·+1)` by additive principality of `ω^c`.

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

Promoted from `wip/ZinftyF.lean` once cut-elimination closed (zero sorries). The superseded
abstract-`AForm` prototype `wip/Zinfty.lean` is kept for history.
-/
import Foundation.FirstOrder.Incompleteness.Second
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Data.ENat.Lattice
import GoodsteinPA.Compat

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

/-- A **signed atomic literal**: `signedLit true r v = rel r v`, `signedLit false r v = nrel r v`. The
atomic-truth axiom `axTrue` ranges over *true closed literals* of either polarity (the ω-logic
leaf that lets `Z_∞` prove PA's equational/arithmetic axioms — see
`ANALYSIS-2026-06-22-truth-layer-gap.md`). -/
def signedLit : Bool → {k : ℕ} → (ℒₒᵣ).Rel k → (Fin k → Semiterm ℒₒᵣ ℕ 0) → Form
  | true, _, r, v => Semiformula.rel r v
  | false, _, r, v => Semiformula.nrel r v

/-- **ℕ-truth of a closed formula** (the side condition `axTrue` carries on its literal): the
standard ℒₒᵣ-model evaluation with no bound variables. For a closed literal the free-variable
assignment is immaterial (fixed to `id`). -/
def LitTrue (φ : Form) : Prop := GoodsteinPA.Compat.gEvalm ℕ ![] (id : ℕ → ℕ) φ

/-- `∼`-duality: a closed formula is true iff its negation is false. -/
@[simp] theorem litTrue_neg (φ : Form) : LitTrue (∼φ) ↔ ¬ LitTrue φ := by
  unfold LitTrue; simp

/-- Totality (classical): every closed formula is true or its negation is. -/
theorem litTrue_or_neg (φ : Form) : LitTrue φ ∨ LitTrue (∼φ) := by
  rw [litTrue_neg]; exact em _

/-- The negation of a signed literal flips its sign. -/
@[simp] theorem neg_lit (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v) :
    ∼(signedLit b r v) = signedLit (!b) r v := by cases b <;> simp [signedLit]

/-- Flipping a signed literal's polarity flips its truth value: the opposite literal is true iff the
literal is false. (The atomic-cut / false-literal-removal truth pivot.) -/
theorem litTrue_flip (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v) :
    LitTrue (signedLit (!b) r v) ↔ ¬ LitTrue (signedLit b r v) := by
  rw [← neg_lit]; exact litTrue_neg _

/-- A signed literal is never `⊤`. -/
@[simp] theorem lit_ne_verum (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v) :
    signedLit b r v ≠ (⊤ : Form) := by cases b <;> simp [signedLit]

/-- A signed literal is never `⊥`. -/
@[simp] theorem lit_ne_falsum (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v) :
    signedLit b r v ≠ (⊥ : Form) := by cases b <;> simp [signedLit]

/-- **The `Z_∞` calculus** over real `ℒₒᵣ` syntax. The `allω` (ω-rule) constructor stores one
sub-derivation per numeral `n`: from `insert (φ/[nm n]) Γ` for every `n`, conclude
`insert (∀⁰ φ) Γ`. -/
inductive Deriv : Seq → Type
  | axL {Γ : Seq} {k} (r : (ℒₒᵣ).Rel k) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Deriv Γ
  | axTrue {Γ : Seq} {k} (b : Bool) (r : (ℒₒᵣ).Rel k) (v) (htrue : LitTrue (signedLit b r v))
      (hmem : signedLit b r v ∈ Γ) : Deriv Γ
  | verumR {Γ : Seq} (h : (⊤ : Form) ∈ Γ) : Deriv Γ
  | weak {Δ Γ : Seq} (d : Deriv Δ) (h : Δ ⊆ Γ) : Deriv Γ
  | andI {Γ : Seq} (φ ψ : Form) (dφ : Deriv (insert φ Γ)) (dψ : Deriv (insert ψ Γ)) :
      Deriv (insert (φ ⋏ ψ) Γ)
  | orI {Γ : Seq} (φ ψ : Form) (d : Deriv (insert φ (insert ψ Γ))) : Deriv (insert (φ ⋎ ψ) Γ)
  | allω {Γ : Seq} (φ : SyntacticSemiformula ℒₒᵣ 1)
      (d : (n : ℕ) → Deriv (insert (φ/[nm n]) Γ)) : Deriv (insert (∀⁰ φ) Γ)
  | exI {Γ : Seq} (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ)
      (d : Deriv (insert (φ/[nm n]) Γ)) : Deriv (insert (∃⁰ φ) Γ)
  | cut {Γ : Seq} (φ : Form) (d₁ : Deriv (insert φ Γ)) (d₂ : Deriv (insert (∼φ) Γ)) : Deriv Γ

namespace Deriv

/-- **Ordinal bound** (Towsner's superscript `α`). The ω-rule node takes the supremum of its
`ℕ`-many premise bounds, then `+1`. Weakening is height-preserving. -/
noncomputable def o : {Γ : Seq} → Deriv Γ → Ordinal.{0}
  | _, axL _ _ _ _ => 0
  | _, axTrue _ _ _ _ _ => 0
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
  | _, axTrue _ _ _ _ _ => 0
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

/-- **Atomic-truth axiom** (the ω-logic leaf): a true closed literal closes any sequent containing
it, at bound `0`, cut rank `0`. -/
theorem Provable.axTrue {Γ : Seq} {k} (b : Bool) (r : (ℒₒᵣ).Rel k) (v)
    (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : Provable 0 0 Γ :=
  ⟨Deriv.axTrue b r v htrue hmem, by simp [Deriv.o], by simp [Deriv.cr]⟩

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

/-- Predicate-level `∃`-introduction (witness rule). The witness is a **numeral** `nm n`: in the
arithmetic term model every closed term denotes a numeral, and numeral witnesses are what the
ω-rule inversion (`allInv`) produces, so the ∀/∃ cut-reduction (§19.6) can match the witness
against the inverted ∀-family. (The embedding §16 supplies a numeral by evaluating PA's witness
term — deferred to M4.) -/
theorem Provable.exI {α : Ordinal.{0}} {c : ℕ} {Γ : Seq} (φ : SyntacticSemiformula ℒₒᵣ 1)
    (n : ℕ) (h : Provable α c (insert (φ/[nm n]) Γ)) :
    Provable (α + 1) c (insert (∃⁰ φ) Γ) := by
  rcases h with ⟨d, ho, hcr⟩
  exact ⟨Deriv.exI φ n d, by simpa [Deriv.o] using add_le_add_right ho 1,
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
  | @axTrue Γ k b r v htrue hmem =>
    intro _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋎ ψ) :=
      Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit, Vee.vee], hmem⟩
    simp only [Deriv.o]
    exact (Provable.axTrue b r v htrue
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hl))).mono le_rfl (Nat.zero_le c)
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
  | @exI Γ₀ χ n d ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [Vee.vee] at h
    have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPush (χ/[nm n]) Γ₀)
    exact (Provable.exI χ n P).weakening (invPull hhead Γ₀)
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
  | @axTrue Γ k b r v htrue hmem =>
    intro _ _
    have hl : signedLit b r v ∈ Γ.erase (∀⁰ χ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Deriv.o]
    exact (Provable.axTrue b r v htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)
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
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (∀⁰ χ) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
    have hmem0 : (∀⁰ χ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
    exact (Provable.exI χ' n P).weakening (invPull1 _ hhead Γ₀)
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
  | @axTrue Γ k b r v htrue hmem =>
    intro _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩
    simp only [Deriv.o]
    exact ⟨(Provable.axTrue b r v htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c),
      (Provable.axTrue b r v htrue (Finset.mem_insert_of_mem hl)).mono le_rfl (Nat.zero_le c)⟩
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
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    refine ⟨?_, ?_⟩
    · have P := ((ih hcr (Finset.mem_insert_of_mem hmem0)).1).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
      exact (Provable.exI χ' n P).weakening (invPull1 _ hhead Γ₀)
    · have P := ((ih hcr (Finset.mem_insert_of_mem hmem0)).2).weakening (invPush1 _ (χ'/[nm n]) _ Γ₀)
      exact (Provable.exI χ' n P).weakening (invPull1 _ hhead Γ₀)
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

/-- Bound bookkeeping for a binary commuting case: a rule reassembled at `max (α+a+1) (α+b+1) + 1`
fits the target `α + (max a b + 1) + 1`. -/
private theorem cutAux_bnd (α a b : Ordinal.{0}) :
    max (α + a + 1) (α + b + 1) + 1 ≤ α + (max a b + 1) + 1 := by
  refine add_le_add_left (max_le ?_ ?_) 1
  · calc α + a + 1 = α + (a + 1) := add_assoc α a 1
      _ ≤ α + (max a b + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (le_max_left a b) 1)
  · calc α + b + 1 = α + (b + 1) := add_assoc α b 1
      _ ≤ α + (max a b + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (le_max_right a b) 1)

/-- Bound bookkeeping for a unary commuting case (∨/∃): `α + a + 1 + 1 = α + (a + 1) + 1`. -/
private theorem cutAux_bnd1 (α a : Ordinal.{0}) : α + a + 1 + 1 ≤ α + (a + 1) + 1 :=
  le_of_eq (by rw [add_assoc α a 1])

/-- Frame subset: push an `insert` out of the `erase`/`∪`-framed context (`ih`-result → canonical).
Explicit (not `tauto`) to avoid `whnf` blow-ups on negated atoms. -/
private theorem frame_in (a e : Form) (s t : Seq) :
    (insert a s).erase e ∪ t ⊆ insert a (s.erase e ∪ t) := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hne, hxa | hxs⟩ | hxt
  · exact Or.inl hxa
  · exact Or.inr (Or.inl ⟨hne, hxs⟩)
  · exact Or.inr (Or.inr hxt)

/-- Frame subset: pull an `insert` back into the `erase`/`∪`-framed context (canonical → goal),
valid when the head `a` is not the erased formula. -/
private theorem frame_out {a e : Form} (hne : a ≠ e) (s t : Seq) :
    insert a (s.erase e ∪ t) ⊆ (insert a s).erase e ∪ t := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with rfl | (⟨hne', hxs⟩ | hxt)
  · exact Or.inl ⟨hne, Or.inl rfl⟩
  · exact Or.inl ⟨hne', Or.inr hxs⟩
  · exact Or.inr hxt

/-- Bound bookkeeping for the ω-rule commuting case. -/
private theorem cutAux_bnd_sup (α : Ordinal.{0}) (f : ℕ → Ordinal.{0}) :
    (⨆ n, (α + f n + 1)) + 1 ≤ α + ((⨆ n, f n) + 1) + 1 := by
  refine add_le_add_left ?_ 1
  apply Ordinal.iSup_le
  intro n
  calc α + f n + 1 = α + (f n + 1) := add_assoc α (f n) 1
    _ ≤ α + ((⨆ m, f m) + 1) := (add_le_add_iff_left α).mpr (add_le_add_left (Ordinal.le_iSup f n) 1)

/-! ### Cut reduction, ∧/∨ principal (Towsner §19.5)

⭐ **Design note (this lap).** Natural (Hessenberg) sum `α ♯ β` is **absent from mathlib v4.31.0**
(no `NaturalOps.lean`/`Ordinal.nadd`). The classic reduction-lemma bound `α ♯ β` is therefore
unavailable. But for the **∧/∨** case there is a route that needs no natural sum *and no fresh
induction at all*: both connectives are **invertible** (`andInvL/R`, `orInv`, all proved), so we
invert *both* premises and close with **two ordinary cuts** at the strictly smaller subformulas.
The resulting bound is `max α β + 1 + 1`, and `max(ω^a, ω^b) + 2 < ω^{max a b + 1}` keeps
`cutElimStep` below `ω^α` with room to spare. (The ∀/∃ case is genuinely different — `∃` is *not*
invertible — and still needs the §19.6 induction on the ∃-side; tracked as `cutReduceAll` below.) -/

/-- Reduce a cut on a **conjunction** `a ⋏ b` (its negation `∼a ⋎ ∼b` on the other side), with both
conjuncts of complexity `< c`. Invert the ∧-side (`andInvL/R`) and the ∨-side (`orInv`), then cut
`a` and `b` separately at cut-rank `≤ c`. Towsner **Thm 19.5** (∧/∨ principal reduction). -/
theorem Provable.cutReduceConj {a b : Form} {c : ℕ} {α β : Ordinal.{0}} {Γ : Seq}
    (ha : (a.complexity + 1 : ℕ∞) ≤ c) (hb : (b.complexity + 1 : ℕ∞) ≤ c)
    (hC : Provable α c (insert (a ⋏ b) Γ)) (hNC : Provable β c (insert (∼a ⋎ ∼b) Γ)) :
    Provable (max α β + 1 + 1) c Γ := by
  -- ∧-inversion of the left premise → `a, Γ` and `b, Γ` (same bound `α`).
  have hA : Provable α c (insert a Γ) :=
    (hC.andInvL (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hB : Provable α c (insert b Γ) :=
    (hC.andInvR (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- ∨-inversion of the right premise → `∼a, ∼b, Γ` (same bound `β`).
  have hNab : Provable β c (insert (∼a) (insert (∼b) Γ)) :=
    (hNC.orInv (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- cut on `a`: `(a, ∼b, Γ)` × `(∼a, ∼b, Γ)` ⟹ `(∼b, Γ)`.
  have cutA : Provable (max α β + 1) c (insert (∼b) Γ) :=
    Provable.cut a ha (hA.weakening (by
      intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)) hNab
  -- cut on `b`: `(b, Γ)` × `(∼b, Γ)` ⟹ `Γ`.
  have cutB : Provable (max α (max α β + 1) + 1) c Γ := Provable.cut b hb hB cutA
  -- `max α (max α β + 1) + 1 = max α β + 1 + 1`.
  have he : max α (max α β + 1) + 1 = max α β + 1 + 1 := by
    congr 1
    exact max_eq_right (le_trans (le_max_left α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  exact he ▸ cutB

/-- Reduce a cut on a **disjunction** `a ⋎ b` (its negation `∼a ⋏ ∼b` on the other side), with both
disjuncts of complexity `< c`. Dual to `cutReduceConj`: invert the ∨-side (`orInv`) and the ∧-side
(`andInvL/R`), then cut `a` and `b`. Towsner **Thm 19.5**. -/
theorem Provable.cutReduceDisj {a b : Form} {c : ℕ} {α β : Ordinal.{0}} {Γ : Seq}
    (ha : (a.complexity + 1 : ℕ∞) ≤ c) (hb : (b.complexity + 1 : ℕ∞) ≤ c)
    (hC : Provable α c (insert (a ⋎ b) Γ)) (hNC : Provable β c (insert (∼a ⋏ ∼b) Γ)) :
    Provable (max α β + 1 + 1) c Γ := by
  -- ∨-inversion of the left premise → `a, b, Γ`.
  have hAB : Provable α c (insert a (insert b Γ)) :=
    (hC.orInv (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- ∧-inversion of the right premise → `∼a, Γ` and `∼b, Γ`.
  have hNa : Provable β c (insert (∼a) Γ) :=
    (hNC.andInvL (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hNb : Provable β c (insert (∼b) Γ) :=
    (hNC.andInvR (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- cut on `a`: `(a, b, Γ)` × `(∼a, b, Γ)` ⟹ `(b, Γ)`.
  have cutA : Provable (max α β + 1) c (insert b Γ) :=
    Provable.cut a ha hAB (hNa.weakening (by
      intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto))
  -- cut on `b`: `(b, Γ)` × `(∼b, Γ)` ⟹ `Γ`.
  have cutB : Provable (max (max α β + 1) β + 1) c Γ := Provable.cut b hb cutA hNb
  have he : max (max α β + 1) β + 1 = max α β + 1 + 1 := by
    congr 1
    exact max_eq_left (le_trans (le_max_right α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  exact he ▸ cutB

/-! ### Cut reduction, ∀/∃ principal (Towsner §19.6)

Unlike ∧/∨, the existential is **not invertible**, so there is no double-inversion shortcut. We
invert the ∀-side once (`allInv` → the numeral-indexed family `φ/[nm n]`) and then **induct on the
∃-side derivation**, cutting at the witness numeral when `∃∼φ` is principal. To keep the inverted
family available unchanged through the induction, it is a *fixed* hypothesis (over a fixed ambient
`Γ`, weakened up at each use) and the running conclusion is framed over `Δ.erase (∃∼φ) ∪ Γ`. -/

/-- The induction core of the ∀/∃ reduction. `fam` is the ∀-inversion family; induct on the
∃-side derivation `d`. -/
theorem Provable.cutReduceAllAux {φ : SyntacticSemiformula ℒₒᵣ 1} {c : ℕ} {α : Ordinal.{0}}
    {Γ : Seq} (hφc : (φ.complexity + 1 : ℕ∞) ≤ c)
    (fam : ∀ n, Provable α c (insert (φ/[nm n]) Γ)) :
    ∀ {Δ : Seq} (d : Deriv Δ), cr d ≤ (c : ℕ∞) → (∃⁰ ∼φ) ∈ Δ →
      Provable (α + o d + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _
    simp only [Deriv.o]
    refine (Provable.axL r v ?_ ?_).mono zero_le (Nat.zero_le c)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro _ _
    simp only [Deriv.o]
    refine (Provable.axTrue b r v htrue ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩)
  | @verumR Δ h =>
    intro _ _
    simp only [Deriv.o]
    refine (Provable.verumR ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (∃⁰ ∼φ) ∈ Δ'
    · exact (ih hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show Provable (o d') c Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_ |>.mono ?_ le_rfl
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self (o d') α)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ (∃⁰ ∼φ) := by intro h; simp [Wedge.wedge, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcr0 : cr d₀ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcr1 : cr d₁ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have P0 : Provable (α + o d₀ + 1) c (insert χ₀ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      (ih₀ hcr0 (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    have P1 : Provable (α + o d₁ + 1) c (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      (ih₁ hcr1 (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.andI χ₀ χ₁ P0 P1).weakening (show
        insert (χ₀ ⋏ χ₁) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (χ₀ ⋏ χ₁) Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cutAux_bnd α (o d₀) (o d₁)) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ (∃⁰ ∼φ) := by intro h; simp [Vee.vee, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (α + o d' + 1) c (insert χ₀ (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.orI χ₀ χ₁ P).weakening (show
        insert (χ₀ ⋎ χ₁) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (χ₀ ⋎ χ₁) Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cutAux_bnd1 α (o d')) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (α + o (d' n) + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      fun n => (ih n (le_trans (le_iSup (fun m => cr (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.allω χ' key).weakening (show
        insert (∀⁰ χ') (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (∀⁰ χ') Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cutAux_bnd_sup α (fun n => o (d' n))) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hhd : (∃⁰ χ') = (∃⁰ ∼φ)
    · -- principal: χ' = ∼φ, cut at witness numeral `n`.
      have hχ : χ' = ∼φ := by
        have := hhd; simpa [ExsQuantifier.exs] using this
      subst hχ
      rw [Finset.erase_insert_eq_erase]
      have hsubcomp : (((∼φ)/[nm n]).complexity + 1 : ℕ∞) ≤ c := by simpa using hφc
      have hcutfml : (((φ/[nm n]).complexity + 1 : ℕ∞)) ≤ c := by simpa using hφc
      -- the ∃-premise gives `∼(φ/[nm n])` in the context; combine with `fam n`.
      have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
      have famn := (fam n).weakening (show insert (φ/[nm n]) Γ
          ⊆ insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) from by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
      by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
      · have Premise : Provable (α + o d' + 1) c (insert ((∼φ)/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          (ih hcr (Finset.mem_insert_of_mem hd)).weakening (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        have hctx : insert ((∼φ)/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)
            = insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) := by rw [hNeg]
        have hcut := Provable.cut (φ/[nm n]) hcutfml famn (Premise.cast hctx)
        refine hcut.mono ?_ le_rfl
        refine add_le_add_left ?_ 1
        exact max_le le_self_add (le_of_eq (add_assoc α (o d') 1))
      · have base : Provable (o d') c (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
          refine (show Provable (o d') c (insert ((∼φ)/[nm n]) Γ₀) from ⟨d', le_rfl, hcr⟩).weakening ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hxΓ₀
          · left; rw [hNeg]
          · exact Or.inr (Or.inl ⟨fun e => hd (e ▸ hxΓ₀), hxΓ₀⟩)
        have hcut := Provable.cut (φ/[nm n]) hcutfml famn base
        refine hcut.mono ?_ le_rfl
        refine add_le_add_left ?_ 1
        exact max_le le_self_add
          (le_trans (le_of_lt (lt_add_of_pos_right _ one_pos))
            (CanonicallyOrderedAdd.le_add_self (o d' + 1) α))
    · -- commuting: ∃χ' ≠ ∃∼φ.
      have hhead : (∃⁰ χ') ≠ (∃⁰ ∼φ) := hhd
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P : Provable (α + o d' + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ((Provable.exI χ' n P).weakening (show
          insert (∃⁰ χ') (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (∃⁰ χ') Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)).mono (cutAux_bnd1 α (o d')) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ c := (le_max_left _ _).trans hcr
    have hcr1 : cr d₁ ≤ (c : ℕ∞) := (le_max_left (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cr d₂ ≤ (c : ℕ∞) := (le_max_right (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have P1 := (ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).weakening (frame_in ξ (∃⁰ ∼φ) Γ₀ Γ)
    have P2 := (ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).weakening (frame_in (∼ξ) (∃⁰ ∼φ) Γ₀ Γ)
    exact (Provable.cut ξ hcξ P1 P2).mono (cutAux_bnd α (o d₁) (o d₂)) le_rfl

/-- **Cut reduction, ∀/∃ principal** (Towsner Thm 19.6). A cut on `∀⁰ φ` (complexity `≤ c`) is
eliminated by inverting the ∀-side and inducting on the ∃-side. -/
theorem Provable.cutReduceAll {φ : SyntacticSemiformula ℒₒᵣ 1} {c : ℕ} {α β : Ordinal.{0}}
    {Γ : Seq} (hφc : (φ.complexity + 1 : ℕ∞) ≤ c)
    (hC : Provable α c (insert (∀⁰ φ) Γ)) (hNC : Provable β c (insert (∃⁰ ∼φ) Γ)) :
    Provable (α + β + 1) c Γ := by
  -- ∀-inversion → the numeral family.
  have fam : ∀ n, Provable α c (insert (φ/[nm n]) Γ) := fun n =>
    (hC.allInv (Finset.mem_insert_self _ _) n).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  rcases hNC with ⟨d, ho, hcr⟩
  have haux := Provable.cutReduceAllAux hφc fam d hcr (Finset.mem_insert_self _ _)
  refine (haux.weakening (show (insert (∃⁰ ∼φ) Γ).erase (∃⁰ ∼φ) ∪ Γ ⊆ Γ from by
    intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)).mono ?_ le_rfl
  exact add_le_add_left ((add_le_add_iff_left α).mpr ho) 1

/-! ### Ordinal bound bookkeeping for cut-rank elimination

All cases keep the new bound below `ω^(·+1)`, exploiting that `ω^c` is **additively principal**
(`isPrincipal_add_omega0_opow`): finite `+`-combinations of things `< ω^c` stay `< ω^c`. -/

private theorem one_lt_opow_succ (c : Ordinal.{0}) : (1 : Ordinal) < Ordinal.omega0 ^ (c + 1) := by
  calc (1 : Ordinal) < Ordinal.omega0 := Ordinal.one_lt_omega0
    _ = Ordinal.omega0 ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
    _ ≤ Ordinal.omega0 ^ (c + 1) :=
        Ordinal.opow_le_opow_right Ordinal.omega0_pos (CanonicallyOrderedAdd.le_add_self 1 c)

private theorem opow_lt_opow_succ_of_le_max {a b x : Ordinal.{0}}
    (hx : x ≤ max (Ordinal.omega0 ^ a) (Ordinal.omega0 ^ b)) :
    x < Ordinal.omega0 ^ (max a b + 1) := by
  refine lt_of_le_of_lt hx (max_lt ?_ ?_)
  · exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (lt_of_le_of_lt (le_max_left a b) (lt_add_of_pos_right _ one_pos))
  · exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
      (lt_of_le_of_lt (le_max_right a b) (lt_add_of_pos_right _ one_pos))

private theorem max_opow_add_one_le (a b : Ordinal.{0}) :
    max (Ordinal.omega0 ^ a) (Ordinal.omega0 ^ b) + 1 ≤ Ordinal.omega0 ^ (max a b + 1) :=
  le_of_lt (Ordinal.isPrincipal_add_omega0_opow _ (opow_lt_opow_succ_of_le_max le_rfl) (one_lt_opow_succ _))

private theorem max_opow_add_two_le (a b : Ordinal.{0}) :
    max (Ordinal.omega0 ^ a) (Ordinal.omega0 ^ b) + 1 + 1 ≤ Ordinal.omega0 ^ (max a b + 1) := by
  have hP := Ordinal.isPrincipal_add_omega0_opow (max a b + 1)
  exact le_of_lt (hP (hP (opow_lt_opow_succ_of_le_max le_rfl) (one_lt_opow_succ _))
    (one_lt_opow_succ _))

private theorem opow_add_opow_add_one_le (a b : Ordinal.{0}) :
    Ordinal.omega0 ^ a + Ordinal.omega0 ^ b + 1 ≤ Ordinal.omega0 ^ (max a b + 1) := by
  have hP := Ordinal.isPrincipal_add_omega0_opow (max a b + 1)
  exact le_of_lt (hP (hP (opow_lt_opow_succ_of_le_max (le_max_left _ _))
    (opow_lt_opow_succ_of_le_max (le_max_right _ _))) (one_lt_opow_succ _))

private theorem opow_add_one_le' (a : Ordinal.{0}) :
    Ordinal.omega0 ^ a + 1 ≤ Ordinal.omega0 ^ (a + 1) := by
  have hP := Ordinal.isPrincipal_add_omega0_opow (a + 1)
  exact le_of_lt (hP ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    (lt_add_of_pos_right _ one_pos)) (one_lt_opow_succ _))

private theorem sup_opow_add_one_le (f : ℕ → Ordinal.{0}) :
    (⨆ n, Ordinal.omega0 ^ (f n)) + 1 ≤ Ordinal.omega0 ^ ((⨆ n, f n) + 1) := by
  have hsup : (⨆ n, Ordinal.omega0 ^ (f n)) ≤ Ordinal.omega0 ^ (⨆ n, f n) :=
    Ordinal.iSup_le fun n => Ordinal.opow_le_opow_right Ordinal.omega0_pos (Ordinal.le_iSup f n)
  have hlt : Ordinal.omega0 ^ (⨆ n, f n) < Ordinal.omega0 ^ ((⨆ n, f n) + 1) :=
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_of_pos_right _ one_pos)
  exact le_of_lt (Ordinal.isPrincipal_add_omega0_opow _ (lt_of_le_of_lt hsup hlt) (one_lt_opow_succ _))

/-- **Removing a FALSE closed literal** `L = signedLit b₀ r₀ v₀` (`¬ LitTrue L`) from a cut-free
derivation, bound-preserving — the *truth layer* the ω-logic atomic cut elimination needs (Schütte /
Buchholz; the generalization of `removeFalsumAux` from `⊥` to any false literal). A literal is never
principal in a logical rule, so it is incidental at every compound step; the only new content is at
the leaves: an `axL` clash on `L` exposes its (TRUE) opposite polarity `∼L`, closed by `axTrue`; an
`axTrue` leaf's true witness is `≠ L` (which is false), so it survives the erase. -/
theorem Provable.removeFalseLitAux (b₀ : Bool) {k₀} (r₀ : (ℒₒᵣ).Rel k₀) (v₀)
    (hL : ¬ LitTrue (signedLit b₀ r₀ v₀)) :
    ∀ {Δ : Seq} (d : Deriv Δ), cr d ≤ (0 : ℕ∞) →
      signedLit b₀ r₀ v₀ ∈ Δ → Provable (o d) 0 (Δ.erase (signedLit b₀ r₀ v₀)) := by
  set L : Form := signedLit b₀ r₀ v₀ with hLdef
  have hLne : ∀ (g : Form), g.complexity ≠ 0 → g ≠ L := by
    intro g hg; rw [hLdef]; exact Semiformula.ne_of_ne_complexity (by cases b₀ <;> simp [signedLit, hg])
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _; simp only [Deriv.o]
    by_cases h1 : L = Semiformula.rel r v
    · -- `L = rel r v` (false) ⟹ `nrel r v = ∼(rel r v)` is true ⟹ close by `axTrue false`.
      have htn : LitTrue (signedLit false r v) := by
        show LitTrue (Semiformula.nrel r v)
        rw [← Semiformula.neg_rel, litTrue_neg]; exact h1 ▸ hL
      exact Provable.axTrue false r v htn (Finset.mem_erase.mpr ⟨by rw [h1]; simp [signedLit], hn⟩)
    · by_cases h2 : L = Semiformula.nrel r v
      · -- `L = nrel r v` (false) ⟹ `rel r v` is true ⟹ close by `axTrue true`.
        have htr : LitTrue (signedLit true r v) := by
          show LitTrue (Semiformula.rel r v)
          by_contra hc
          exact (h2 ▸ hL) (by rw [← Semiformula.neg_rel, litTrue_neg]; exact hc)
        exact Provable.axTrue true r v htr (Finset.mem_erase.mpr ⟨by rw [h2]; simp [signedLit], hp⟩)
      · exact Provable.axL r v (Finset.mem_erase.mpr ⟨fun e => h1 e.symm, hp⟩)
          (Finset.mem_erase.mpr ⟨fun e => h2 e.symm, hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro _ _; simp only [Deriv.o]
    -- the true witness `signedLit b r v ≠ L` (false), so it survives the erase.
    have hne : signedLit b r v ≠ L := fun e => hL (e ▸ htrue)
    exact Provable.axTrue b r v htrue (Finset.mem_erase.mpr ⟨hne, hmem⟩)
  | @verumR Δ h =>
    intro _ _; simp only [Deriv.o]
    exact Provable.verumR (Finset.mem_erase.mpr ⟨by rw [hLdef]; exact (lit_ne_verum b₀ r₀ v₀).symm, h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    by_cases hd : L ∈ Δ'
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Provable (o d') 0 Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_
      intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : Provable (o d₀) 0 (insert χ₀ (Γ₀.erase L)) :=
      (ih₀ (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : Provable (o d₁) 0 (insert χ₁ (Γ₀.erase L)) :=
      (ih₁ (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.andI χ₀ χ₁ P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (o d') 0 (insert χ₀ (insert χ₁ (Γ₀.erase L))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.orI χ₀ χ₁ P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (o (d' n)) 0 (insert (χ'/[nm n]) (Γ₀.erase L)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => cr (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.allω χ' key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (o d') 0 (insert (χ'/[nm n]) (Γ₀.erase L)) :=
      (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.exI χ' n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr _; simp only [Deriv.cr] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-! ### Atomic cut elimination (Towsner Thm 19.2, the false-atomic inversion content)

The cut formula is atomic (`rel r v`), so it is **never principal in a logical rule** — it only
enters via `axL` or weakening. No truth layer is needed: set sequents dissolve the key case. If an
`axL` clashes exactly on the cut atom `(rel r v, nrel r v)`, then `nrel r v ∈ Γ`, so the *other*
premise (`⊢ nrel r v, Γ`) already proves `Γ` (set idempotence). Every other case is incidental. -/

/-- Induction core: cut a `rel r v` derivation (`d`) against a fixed `nrel r v` derivation (`hNC`). -/
theorem Provable.atomCutAux {k} (r : (ℒₒᵣ).Rel k) (v) {B : Ordinal.{0}} {Γ : Seq}
    (hNC : Provable B 0 (insert (Semiformula.nrel r v) Γ)) :
    ∀ {Δ : Seq} (d : Deriv Δ), cr d ≤ (0 : ℕ∞) → (Semiformula.rel r v) ∈ Δ →
      Provable (B + o d + 1) 0 (Δ.erase (Semiformula.rel r v) ∪ Γ) := by
  intro Δ d
  induction d with
  | @axL Δ k' r' v' hp hn =>
    intro _ _
    simp only [Deriv.o]
    have hnn : (Semiformula.nrel r' v' : Form) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by intro h; exact absurd h (by simp), hn⟩
    by_cases hrel : (Semiformula.rel r' v' : Form) = Semiformula.rel r v
    · -- the clash's positive member IS the cut atom ⇒ `nrel r v ∈ Γ`-part, use `hNC`
      have hnrv : (Semiformula.nrel r' v' : Form) = Semiformula.nrel r v := by
        rw [← Semiformula.neg_rel r' v', hrel, Semiformula.neg_rel]
      refine (hNC.weakening ?_).mono ?_ le_rfl
      · intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hxΓ
        · exact Finset.mem_union_left _ (hnrv ▸ hnn)
        · exact Finset.mem_union_right _ hxΓ
      · exact le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos))
    · -- clash avoids the cut atom ⇒ it survives the erase, close by `axL`
      have hpp : (Semiformula.rel r' v' : Form) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨hrel, hp⟩
      exact (Provable.axL r' v' (Finset.mem_union_left _ hpp)
        (Finset.mem_union_left _ hnn)).mono zero_le le_rfl
  | @axTrue Δ k' b' r' v' htrue' hmem' =>
    intro _ _
    simp only [Deriv.o]
    by_cases heq : (signedLit b' r' v' : Form) = Semiformula.rel r v
    · -- the true literal IS the cut atom ⇒ `rel r v` is TRUE ⇒ `nrel r v` is a removable false
      -- literal on the `hNC` side. The TRUTH-LAYER key case.
      have htrue_rel : LitTrue (Semiformula.rel r v) := heq ▸ htrue'
      have hfalse : ¬ LitTrue (signedLit false r v) := by
        rw [← litTrue_flip false r v]; simpa [signedLit] using htrue_rel
      obtain ⟨dN, hoN, hcrN⟩ := hNC
      have hrm := Provable.removeFalseLitAux false r v hfalse dN hcrN
        (show signedLit false r v ∈ insert (Semiformula.nrel r v) Γ by simp [signedLit])
      refine (hrm.weakening ?_).mono ?_ le_rfl
      · intro x hx
        have hxΓ : x ∈ Γ := by
          have h1 := Finset.mem_of_mem_erase hx
          have h2 := Finset.ne_of_mem_erase hx
          rcases Finset.mem_insert.mp h1 with rfl | h3
          · exact absurd (show (Semiformula.nrel r v : Form) = signedLit false r v by simp [signedLit]) h2
          · exact h3
        exact Finset.mem_union_right _ hxΓ
      · exact le_trans hoN (le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos)))
    · -- the true literal avoids the cut atom ⇒ survives the erase, close by `axTrue`
      have hll : (signedLit b' r' v' : Form) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨heq, hmem'⟩
      exact (Provable.axTrue b' r' v' htrue' (Finset.mem_union_left _ hll)).mono zero_le le_rfl
  | @verumR Δ h =>
    intro _ _
    simp only [Deriv.o]
    have ht : (⊤ : Form) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by simp, h⟩
    exact (Provable.verumR (Finset.mem_union_left _ ht)).mono zero_le le_rfl
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    by_cases hd : (Semiformula.rel r v) ∈ Δ'
    · exact (ih hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show Provable (o d') 0 Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_ |>.mono ?_ le_rfl
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self (o d') B)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ (Semiformula.rel r v) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcr0 : cr d₀ ≤ (0 : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcr1 : cr d₁ ≤ (0 : ℕ∞) := le_trans (le_max_right _ _) hcr
    have P0 : Provable (B + o d₀ + 1) 0 (insert χ₀ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₀ hcr0 (Finset.mem_insert_of_mem hmem0)).weakening (frame_in χ₀ _ Γ₀ Γ)
    have P1 : Provable (B + o d₁ + 1) 0 (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₁ hcr1 (Finset.mem_insert_of_mem hmem0)).weakening (frame_in χ₁ _ Γ₀ Γ)
    exact ((Provable.andI χ₀ χ₁ P0 P1).weakening (frame_out hhead Γ₀ Γ)).mono
      (cutAux_bnd B (o d₀) (o d₁)) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ (Semiformula.rel r v) := by intro h; simp [Vee.vee] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (B + o d' + 1) 0 (insert χ₀ (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    exact ((Provable.orI χ₀ χ₁ P).weakening (frame_out hhead Γ₀ Γ)).mono (cutAux_bnd1 B (o d')) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (Semiformula.rel r v) := by intro h; simp [UnivQuantifier.all] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (B + o (d' n) + 1) 0
        (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => cr (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((Provable.allω χ' key).weakening (frame_out hhead Γ₀ Γ)).mono
      (cutAux_bnd_sup B (fun n => o (d' n))) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Deriv.cr] at hcr
    simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (Semiformula.rel r v) := by intro h; simp [ExsQuantifier.exs] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (B + o d' + 1) 0 (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((Provable.exI χ' n P).weakening (frame_out hhead Γ₀ Γ)).mono (cutAux_bnd1 B (o d')) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr _
    simp only [Deriv.cr] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- **Atomic cut elimination** (the Thm 19.2 content for the final cut-free step). -/
theorem Provable.atomCut {k} (r : (ℒₒᵣ).Rel k) (v) {A B : Ordinal.{0}} {Γ : Seq}
    (hC : Provable A 0 (insert (Semiformula.rel r v) Γ))
    (hNC : Provable B 0 (insert (Semiformula.nrel r v) Γ)) :
    Provable (B + A + 1) 0 Γ := by
  rcases hC with ⟨d, ho, hcr⟩
  refine ((Provable.atomCutAux r v hNC d hcr (Finset.mem_insert_self _ _)).weakening
    (show (insert (Semiformula.rel r v) Γ).erase (Semiformula.rel r v) ∪ Γ ⊆ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢;
      tauto)).mono ?_ le_rfl
  exact add_le_add_left ((add_le_add_iff_left B).mpr ho) 1

/-- Removing `⊥` from a cut-free derivation, bound-preserving. `⊥` is never introduced by any rule
and is never an `axL`/`verumR` witness, so it is incidental at every step (Towsner Thm 19.2 for the
constant-`⊥` case). -/
theorem Provable.removeFalsumAux : ∀ {Δ : Seq} (d : Deriv Δ), cr d ≤ (0 : ℕ∞) →
    (⊥ : Form) ∈ Δ → Provable (o d) 0 (Δ.erase ⊥) := by
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _; simp only [Deriv.o]
    exact Provable.axL r v (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro _ _; simp only [Deriv.o]
    exact Provable.axTrue b r v htrue (Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit], hmem⟩)
  | @verumR Δ h =>
    intro _ _; simp only [Deriv.o]
    exact Provable.verumR (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    by_cases hd : (⊥ : Form) ∈ Δ'
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Provable (o d') 0 Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_
      intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋏ χ₁) ≠ (⊥ : Form) := by simp [Wedge.wedge]
    have hmem0 : (⊥ : Form) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : Provable (o d₀) 0 (insert χ₀ (Γ₀.erase ⊥)) :=
      (ih₀ (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : Provable (o d₁) 0 (insert χ₁ (Γ₀.erase ⊥)) :=
      (ih₁ (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.andI χ₀ χ₁ P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (χ₀ ⋎ χ₁) ≠ (⊥ : Form) := by simp [Vee.vee]
    have hmem0 : (⊥ : Form) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (o d') 0 (insert χ₀ (insert χ₁ (Γ₀.erase ⊥))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.orI χ₀ χ₁ P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∀⁰ χ') ≠ (⊥ : Form) := by simp [UnivQuantifier.all]
    have hmem0 : (⊥ : Form) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (o (d' n)) 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => cr (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.allω χ' key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have hhead : (∃⁰ χ') ≠ (⊥ : Form) := by simp [ExsQuantifier.exs]
    have hmem0 : (⊥ : Form) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (o d') 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) :=
      (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.exI χ' n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr _; simp only [Deriv.cr] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)


/-- Remove a `⊥` from a cut-free sequent. -/
theorem Provable.removeFalsum {B : Ordinal.{0}} {Γ : Seq}
    (h : Provable B 0 (insert (⊥ : Form) Γ)) : Provable B 0 Γ := by
  rcases h with ⟨d, ho, hcr⟩
  refine (Provable.removeFalsumAux d hcr (Finset.mem_insert_self _ _)).weakening ?_ |>.mono ho le_rfl
  intro x hx; simp only [Finset.mem_erase, Finset.mem_insert] at hx; exact (hx.2).resolve_left hx.1

/-- **Principal cut on a rank-`c` formula** — the heart of Thm 19.7. After both premises are
cut-free-at-`c` (bound `ω^A`, `ω^B`), a cut on `ξ` with `complexity ξ = c` is eliminated by the
matching reduction (∧/∨ → `cutReduceConj/Disj`; ∀/∃ → `cutReduceAll`; atomic → `atomCut`;
`⊤`/`⊥` → `removeFalsum`), staying below `ω^(max A B+1)`. -/
theorem Provable.cutElimPrincipal {c : ℕ} {ξ : Form} {A B : Ordinal.{0}} {Γ : Seq}
    (hξeq : ξ.complexity = c)
    (hC : Provable (Ordinal.omega0 ^ A) c (insert ξ Γ))
    (hNC : Provable (Ordinal.omega0 ^ B) c (insert (∼ξ) Γ)) :
    Provable (Ordinal.omega0 ^ (max A B + 1)) c Γ := by
  cases ξ with
  | verum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : Provable (Ordinal.omega0 ^ B) 0 (insert (⊥ : Form) Γ) := hNC
      refine (Provable.removeFalsum hNC').mono ?_ le_rfl
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_right A B) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | falsum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (Provable.removeFalsum hC).mono ?_ le_rfl
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_left A B) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | rel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (Provable.atomCut r v hC hNC).mono ?_ le_rfl
      rw [max_comm A B]; exact opow_add_opow_add_one_le B A
  | nrel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : Provable (Ordinal.omega0 ^ B) 0 (insert (Semiformula.rel r v) Γ) := hNC
      exact (Provable.atomCut r v hNC' hC).mono (opow_add_opow_add_one_le A B) le_rfl
  | and a b =>
      have hM : max a.complexity b.complexity + 1 = c := hξeq
      have han : a.complexity + 1 ≤ c := by have := le_max_left a.complexity b.complexity; omega
      have hbn : b.complexity + 1 ≤ c := by have := le_max_right a.complexity b.complexity; omega
      exact (Provable.cutReduceConj (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono
        (max_opow_add_two_le A B) le_rfl
  | or a b =>
      have hM : max a.complexity b.complexity + 1 = c := hξeq
      have han : a.complexity + 1 ≤ c := by have := le_max_left a.complexity b.complexity; omega
      have hbn : b.complexity + 1 ≤ c := by have := le_max_right a.complexity b.complexity; omega
      exact (Provable.cutReduceDisj (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono
        (max_opow_add_two_le A B) le_rfl
  | all φ' =>
      have hφn : φ'.complexity + 1 ≤ c := le_of_eq hξeq
      exact (Provable.cutReduceAll (by exact_mod_cast hφn) hC hNC).mono
        (opow_add_opow_add_one_le A B) le_rfl
  | exs φ' =>
      -- ξ = ∃φ', ∼ξ = ∀∼φ'.  Use `cutReduceAll` with ∀-side = hNC, ∃-side = hC.
      have hφn : (∼φ').complexity + 1 ≤ c := by
        rw [Semiformula.complexity_neg]; exact le_of_eq hξeq
      have hC' : Provable (Ordinal.omega0 ^ A) c (insert (∃⁰ ∼(∼φ')) Γ) := by
        rw [DeMorgan.neg]; exact hC
      refine ((Provable.cutReduceAll (by exact_mod_cast hφn) hNC hC').mono ?_ le_rfl)
      rw [max_comm A B]; exact opow_add_opow_add_one_le B A

/-- The transfinite induction underlying Thm 19.7: a derivation of cut rank `≤ c+1` becomes
cut-free-at-`c` at bound `ω^(o d)`. Non-principal rules are reapplied (each `ω^· + small ≤ ω^(·+1)`);
a rank-`< c` cut is kept; a rank-`= c` cut is eliminated by `cutElimPrincipal`. -/
theorem Provable.cutElimStepAux {c : ℕ} : ∀ {Γ : Seq} (d : Deriv Γ), cr d ≤ ((c + 1 : ℕ) : ℕ∞) →
    Provable (Ordinal.omega0 ^ (o d)) c Γ := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _; simp only [Deriv.o]
    exact (Provable.axL r v hp hn).mono zero_le (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro _; simp only [Deriv.o]
    exact (Provable.axTrue b r v htrue hmem).mono zero_le (Nat.zero_le c)
  | @verumR Γ h =>
    intro _; simp only [Deriv.o]
    exact (Provable.verumR h).mono zero_le (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (ih hcr).weakening hsub
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (Provable.andI χ₀ χ₁ (ih₀ ((le_max_left _ _).trans hcr))
      (ih₁ ((le_max_right _ _).trans hcr))).mono (max_opow_add_one_le (o d₀) (o d₁)) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (Provable.orI χ₀ χ₁ (ih hcr)).mono (opow_add_one_le' (o d')) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    have IH : ∀ n, Provable (Ordinal.omega0 ^ (o (d' n))) c (insert (χ'/[nm n]) Γ₀) :=
      fun n => ih n ((le_iSup (fun m => cr (d' m)) n).trans hcr)
    exact (Provable.allω χ' IH).mono (sup_opow_add_one_le (fun n => o (d' n))) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hcr; simp only [Deriv.cr] at hcr; simp only [Deriv.o]
    exact (Provable.exI χ' n (ih hcr)).mono (opow_add_one_le' (o d')) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr; simp only [Deriv.cr] at hcr
    have hcr1 : cr d₁ ≤ ((c + 1 : ℕ) : ℕ∞) :=
      (le_max_left (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cr d₂ ≤ ((c + 1 : ℕ) : ℕ∞) :=
      (le_max_right (cr d₁) (cr d₂)).trans ((le_max_right _ _).trans hcr)
    have hξc : (ξ.complexity + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := (le_max_left _ _).trans hcr
    have IH1 := ih₁ hcr1
    have IH2 := ih₂ hcr2
    simp only [Deriv.o]
    by_cases hkeep : ξ.complexity < c
    · exact (Provable.cut ξ (by exact_mod_cast Nat.succ_le_of_lt hkeep) IH1 IH2).mono
        (max_opow_add_one_le (o d₁) (o d₂)) le_rfl
    · have hξle : ξ.complexity ≤ c := Nat.le_of_succ_le_succ (by exact_mod_cast hξc)
      have hξeq : ξ.complexity = c := le_antisymm hξle (not_lt.mp hkeep)
      exact Provable.cutElimPrincipal hξeq IH1 IH2

/-- **One level of cut elimination** (Towsner Thm 19.7): reducing the cut rank by one raises the
ordinal bound to `ω^α`. -/
theorem Provable.cutElimStep {α : Ordinal.{0}} {c : ℕ} {Γ : Seq}
    (h : Provable α (c + 1) Γ) : Provable (Ordinal.omega0 ^ α) c Γ := by
  rcases h with ⟨d, ho, hcr⟩
  exact (Provable.cutElimStepAux d hcr).mono
    (Ordinal.opow_le_opow_right Ordinal.omega0_pos ho) le_rfl

/-- **Full cut elimination** (Towsner Thm 19.9): iterate `cutElimStep` `c` times, reaching a
cut-free derivation at ordinal `ω_c^α`. -/
theorem Provable.cutElim {α : Ordinal.{0}} {c : ℕ} {Γ : Seq}
    (h : Provable α c Γ) : Provable (omegaTower c α) 0 Γ := by
  induction c generalizing α with
  | zero => simpa [omegaTower] using h
  | succ c ih => exact ih (Provable.cutElimStep h)

/-! ### `ε₀`-closure of the cut-elimination ordinal

`cutElim` lands at `omegaTower c α = ω_c^α`. For the headline (M7) the cut-free bound must stay
**below `ε₀`** when the input does — this is exactly what makes Towsner's argument work (`ε₀` is the
first fixed point of `ω ↦ ω^ω`, hence closed under the `c`-fold tower). Pure ordinal facts, no
calculus dependence; recorded now so M7 can cite them. -/

open scoped Ordinal in
/-- `ε₀` is closed under `ω^·`. -/
theorem omega0_opow_lt_epsilon0 {a : Ordinal.{0}} (h : a < ε₀) : Ordinal.omega0 ^ a < ε₀ := by
  obtain ⟨n, hn⟩ := Ordinal.lt_epsilon_zero.mp h
  have hstep : Ordinal.omega0 ^ a < (fun b => Ordinal.omega0 ^ b)^[n + 1] 0 := by
    rw [Function.iterate_succ_apply']
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hn
  exact hstep.trans (Ordinal.iterate_omega0_opow_lt_epsilon_zero (n + 1))

open scoped Ordinal in
/-- The full cut-elimination ordinal `ω_c^α` stays below `ε₀` whenever `α < ε₀`. -/
theorem omegaTower_lt_epsilon0 : ∀ (c : ℕ) {α : Ordinal.{0}}, α < ε₀ → omegaTower c α < ε₀
  | 0, _, h => by simpa [omegaTower] using h
  | c + 1, _, h => by
      simpa [omegaTower] using omegaTower_lt_epsilon0 c (omega0_opow_lt_epsilon0 h)

end Deriv

end GoodsteinPA.ZinftyF
