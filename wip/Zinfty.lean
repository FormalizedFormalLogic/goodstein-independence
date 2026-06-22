/-
# Phase 2 crux prototype — the `Z_∞` ω-rule calculus, encoding (E2)  [WIP — not in build target]

Feasibility check for milestone **M3.1/M3.2** of `PHASE2-DECOMPOSITION.md`: can we encode
Towsner's infinitary `Z_∞` (the ω-rule system with an ordinal bound) in Lean 4 / mathlib at all?

This validates encoding **(E2)**: an *infinitely-branching* `inductive` for derivations (the
ω-rule constructor stores an `ℕ`-indexed family of sub-derivations — strictly positive, so Lean
accepts it), with the **ordinal bound** and **cut rank** defined afterward as *computed measures*
by structural recursion. The ordinal of an ω-rule node is `(⨆ n, o (dₙ)) + 1` — an `Ordinal`
supremum over the `ℕ`-branches, exactly Towsner's "the bound dominates every premise's bound."

Tait-style (one-sided) formulas in negation-normal form, over an *abstract* atomic layer (a
closed atomic arithmetic sentence is decidably true/false — Towsner's `True` rule fires on a true
atom). This is deliberately self-contained: it does **not** yet connect to Foundation's PA syntax
(that is milestone M4, the embedding). The goal here is only to prove the *shape* typechecks and
the ordinal/rank measures are well-defined — the genuine Phase-2 crux per the decomposition.

Status: scaffolding. The calculus and measures below typecheck; the proof-theoretic lemmas
(16.x, 19.x) are deferred (`sorry`/unstated). Promote to `src/` once a milestone closes.
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Data.ENat.Lattice

namespace GoodsteinPA.Zinfty

/-- Tait-style arithmetic formulas in negation-normal form. The atomic layer is abstracted to its
(decidable) truth value `b : Bool` for a *closed* atomic sentence — enough to state the `True`
rule and the rank/inversion lemmas. `all`/`ex` store the instantiation family `n ↦ φ[x ↦ n]`
(the ω-rule branches over it). -/
inductive AForm where
  | atom (b : Bool)
  | and (φ ψ : AForm)
  | or (φ ψ : AForm)
  | all (f : ℕ → AForm)
  | ex (f : ℕ → AForm)

namespace AForm

/-- Negation (de Morgan dual), pushing `~` to atoms — Tait calculus has no separate `¬`. -/
def neg : AForm → AForm
  | atom b => atom (!b)
  | and φ ψ => or φ.neg ψ.neg
  | or φ ψ => and φ.neg ψ.neg
  | all f => ex fun n => (f n).neg
  | ex f => all fun n => (f n).neg

@[simp] theorem neg_neg : ∀ φ : AForm, φ.neg.neg = φ
  | atom b => by simp [neg]
  | and φ ψ => by simp [neg, neg_neg φ, neg_neg ψ]
  | or φ ψ => by simp [neg, neg_neg φ, neg_neg ψ]
  | all f => by simp [neg]; funext n; exact neg_neg (f n)
  | ex f => by simp [neg]; funext n; exact neg_neg (f n)

/-- Rank (Towsner **Def 16.2**): atoms `0`; ∧/∨ are `max+1`; ∀/∃ are `+1` (over the sup of the
instances' ranks — all instances share the same rank in the intended PA encoding, but we take a
sup to stay faithful for arbitrary families). -/
noncomputable def rk : AForm → ℕ∞
  | atom _ => 0
  | and φ ψ => max φ.rk ψ.rk + 1
  | or φ ψ => max φ.rk ψ.rk + 1
  | all f => (⨆ n, (f n).rk) + 1
  | ex f => (⨆ n, (f n).rk) + 1

end AForm

open AForm

/-- A sequent is a finite multiset of formulas (one-sided/Tait). -/
abbrev Seq := Multiset AForm

/-- **The `Z_∞` calculus (Towsner §16).** An *infinitely-branching* inductive: the `allI`
(ω-rule) constructor stores one sub-derivation per `n : ℕ`. Rules: `trueR` (a true atom closes a
sequent), `weak` (weakening), `andI`, `orI`, `allI` (ω-rule), `exI`, `contr`, `cut`. Ordinal
bound and cut rank are *computed* afterward (`o`, `cr`). -/
inductive Deriv : Seq → Type
  | trueR (Γ : Seq) (h : (AForm.atom true) ∈ Γ) : Deriv Γ
  | weak {Δ Γ : Seq} (d : Deriv Δ) (h : Δ ≤ Γ) : Deriv Γ
  | andI {Γ : Seq} (φ ψ : AForm) (dφ : Deriv (φ ::ₘ Γ)) (dψ : Deriv (ψ ::ₘ Γ)) :
      Deriv (and φ ψ ::ₘ Γ)
  | orI {Γ : Seq} (φ ψ : AForm) (d : Deriv (φ ::ₘ ψ ::ₘ Γ)) : Deriv (or φ ψ ::ₘ Γ)
  | allI {Γ : Seq} (f : ℕ → AForm) (d : (n : ℕ) → Deriv (f n ::ₘ Γ)) : Deriv (all f ::ₘ Γ)
  | exI {Γ : Seq} (f : ℕ → AForm) (n : ℕ) (d : Deriv (f n ::ₘ Γ)) : Deriv (ex f ::ₘ Γ)
  | contr {Γ : Seq} (φ : AForm) (d : Deriv (φ ::ₘ φ ::ₘ Γ)) : Deriv (φ ::ₘ Γ)
  | cut {Γ : Seq} (φ : AForm) (d₁ : Deriv (φ ::ₘ Γ)) (d₂ : Deriv (φ.neg ::ₘ Γ)) : Deriv Γ

namespace Deriv

/-- **Ordinal bound** of a derivation (Towsner's superscript `α`). The ω-rule node takes the
supremum of its `ℕ`-many premises' bounds, then `+1` — the crucial "bound dominates every
premise" property is then definitional. Well-defined by structural recursion on the
(infinitely-branching) tree: each `d n` is a structural subterm. -/
noncomputable def o : {Γ : Seq} → Deriv Γ → Ordinal.{0}
  | _, trueR _ _ => 0
  | _, weak d _ => o d
  | _, andI _ _ dφ dψ => max (o dφ) (o dψ) + 1
  | _, orI _ _ d => o d + 1
  | _, allI _ d => (⨆ n, o (d n)) + 1
  | _, exI _ _ d => o d + 1
  | _, contr _ d => o d + 1
  | _, cut _ d₁ d₂ => max (o d₁) (o d₂) + 1

/-- **Cut rank** of a derivation (Towsner's subscript `c`): the sup of `rk φ + 1` over the cut
formulas `φ` actually used. A *cut-free* derivation has `cr = 0`. -/
noncomputable def cr : {Γ : Seq} → Deriv Γ → ℕ∞
  | _, trueR _ _ => 0
  | _, weak d _ => cr d
  | _, andI _ _ dφ dψ => max (cr dφ) (cr dψ)
  | _, orI _ _ d => cr d
  | _, allI _ d => ⨆ n, cr (d n)
  | _, exI _ _ d => cr d
  | _, contr _ d => cr d
  | _, cut φ d₁ d₂ => max (φ.rk + 1) (max (cr d₁) (cr d₂))

/-- The intended bounded-derivability predicate `Z_∞ ⊢^{α,_}_c Γ` (Towsner's notation, dropping
the numeric `k` bound for now): exists a derivation with ordinal `≤ α` and cut rank `≤ c`. -/
def Provable (α : Ordinal) (c : ℕ) (Γ : Seq) : Prop :=
  ∃ d : Deriv Γ, o d ≤ α ∧ cr d ≤ (c : ℕ∞)

/-- Sanity: the ω-rule bound strictly dominates each premise bound (Towsner's defining property of
the `I∀` rule — makes the cut-elimination ordinal arithmetic go through). -/
theorem o_allI_gt {Γ : Seq} (f : ℕ → AForm) (d : (n : ℕ) → Deriv (f n ::ₘ Γ)) (n : ℕ) :
    o (d n) < o (allI f d) := by
  have h : o (d n) ≤ ⨆ m, o (d m) := Ordinal.le_iSup (fun m => o (d m)) n
  calc o (d n) ≤ ⨆ m, o (d m) := h
    _ < (⨆ m, o (d m)) + 1 := lt_add_of_pos_right _ one_pos
    _ = o (allI f d) := by simp only [o]

/-- **Bound monotonicity (Towsner Lemma 16.4 analog).** Provability is monotone in both the
ordinal bound and the cut rank — you may always relax the recorded bounds. -/
theorem Provable.mono {α β : Ordinal.{0}} {c c' : ℕ} (hα : α ≤ β) (hc : c ≤ c') {Γ : Seq} :
    Provable α c Γ → Provable β c' Γ := by
  rintro ⟨d, ho, hcr⟩
  exact ⟨d, ho.trans hα, hcr.trans (by exact_mod_cast hc)⟩

/-- **Sequent weakening (Towsner Lemma 19.1 analog).** Enlarging the sequent (`Γ ≤ Δ` as
multisets) preserves provability *without raising the ordinal bound or cut rank* — the `weak`
rule is ordinal-free (`o (weak d _) = o d`), exactly as the cut-elimination ordinal arithmetic
requires. -/
theorem Provable.weakening {α : Ordinal.{0}} {c : ℕ} {Γ Δ : Seq} (h : Γ ≤ Δ) :
    Provable α c Γ → Provable α c Δ := by
  rintro ⟨d, ho, hcr⟩
  refine ⟨Deriv.weak d h, ?_, ?_⟩
  · simpa [Deriv.o] using ho
  · simpa [Deriv.cr] using hcr

end Deriv

end GoodsteinPA.Zinfty
