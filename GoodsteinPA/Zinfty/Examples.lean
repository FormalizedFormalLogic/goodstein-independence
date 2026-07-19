/-
# Examples in the `Z_∞` calculus

Basic derivable facts of `Z_∞`: the Tait law of excluded middle (`provable_em`, `Z_∞ ⊢ φ, ∼φ`),
`ω`-completeness for true closed formulas (`provable_true`), and the unbounded provability
predicate `ZProvable`.
- [Tow20, §14]
-/
module

public import GoodsteinPA.Zinfty.Provable

@[expose] public section

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder
open Derivation

variable {Γ : Finset (ArithmeticFormula ℕ)}

/-- A `Z_∞`-derivable sequent, existentially quantified over the ordinal bound and cut rank.
- [Tow20, §14] -/
def ZProvable (Γ : Finset (ArithmeticFormula ℕ)) : Prop := ∃ α c, Provable α c Γ

namespace ZProvable

theorem mono : ZProvable Γ → ZProvable Γ := id

/-- Weaken the sequent (Foundation `wk`). -/
theorem weakening (h : Γ ⊆ Δ) : ZProvable Γ → ZProvable Δ := by
  rintro ⟨α, c, hd⟩; exact ⟨α, c, hd.weakening h⟩

/-- Drop a sequent element that already occurs (`insert X Γ = Γ` when `X ∈ Γ`). -/
theorem of_insert_mem (h : X ∈ Γ) :
    ZProvable (insert X Γ) → ZProvable Γ := by
  rw [Finset.insert_eq_self.mpr h]; exact id

end ZProvable

/-- **Identity / law of excluded middle for `Z_∞`** (the `closed` case). For any `φ`, a sequent
containing both `φ` and `∼φ` is `Z_∞`-derivable cut-free. Proved by induction on a `complexity`
bound (the standard Tait `em`, cf. Foundation `Derivation.em`, `Calculus.lean:164`). The atomic /
propositional cases are discharged here; the **∀/∃ cases** use the numeral ω-family (`allω` over
all `nm n`, each premise closed by `exI` + the inductive hypothesis at the substitution instance `φ/[nm n]`,
whose `complexity` equals `φ`'s).
- [Tow20, §14] -/
theorem provable_em (φ) (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    ∃ a, Provable a 0 Γ := by
  have key : ∀ (k : ℕ) (φ : ArithmeticFormula ℕ), φ.complexity ≤ k →
      ∀ {Γ : Finset (ArithmeticFormula ℕ)}, φ ∈ Γ → ∼φ ∈ Γ → ∃ a, Provable a 0 Γ := by
    intro k
    induction k with
    | zero =>
      intro φ hk Γ hp hn
      cases φ using Semiformula.cases' with
      | hverum => exact ⟨0, Provable.verumR hp⟩
      | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
      | hrel r v => exact ⟨0, Provable.axL r v hp (by simpa using hn)⟩
      | hnrel r v => exact ⟨0, Provable.axL r v (by simpa using hn) hp⟩
      | hand φ ψ => simp at hk
      | hor φ ψ => simp at hk
      | hall φ => simp at hk
      | hexs φ => simp at hk
    | succ k ih =>
      intro φ hk Γ hp hn
      cases φ using Semiformula.cases' with
      | hverum => exact ⟨0, Provable.verumR hp⟩
      | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
      | hrel r v => exact ⟨0, Provable.axL r v hp (by simpa using hn)⟩
      | hnrel r v => exact ⟨0, Provable.axL r v (by simpa using hn) hp⟩
      | hand φ ψ =>
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
        obtain ⟨a1, h1⟩ := ih φ hφk (Γ := insert φ (insert (∼φ) (insert (∼ψ) Γ)))
          (by simp) (by simp)
        obtain ⟨a2, h2⟩ := ih ψ hψk (Γ := insert ψ (insert (∼φ) (insert (∼ψ) Γ)))
          (by simp) (by simp)
        have hand := Provable.andI φ ψ h1 h2
        rw [Finset.insert_eq_self.mpr
          (show (φ ⋏ ψ) ∈ insert (∼φ) (insert (∼ψ) Γ) by simp [hp])] at hand
        have hor := Provable.orI (∼φ) (∼ψ) hand
        rw [Finset.insert_eq_self.mpr (show (∼φ ⋎ ∼ψ) ∈ Γ by simpa using hn)] at hor
        exact ⟨_, hor⟩
      | hor φ ψ =>
        have hn' : (∼φ ⋏ ∼ψ) ∈ Γ := by simpa using hn
        have hφk : φ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
        obtain ⟨a1, h1⟩ := ih φ hφk (Γ := insert (∼φ) (insert φ (insert ψ Γ)))
          (by simp) (by simp)
        obtain ⟨a2, h2⟩ := ih ψ hψk (Γ := insert (∼ψ) (insert φ (insert ψ Γ)))
          (by simp) (by simp)
        have hand := Provable.andI (∼φ) (∼ψ) h1 h2
        rw [Finset.insert_eq_self.mpr
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))] at hand
        have hor := Provable.orI φ ψ hand
        rw [Finset.insert_eq_self.mpr (show (φ ⋎ ψ) ∈ Γ by simp [hp])] at hor
        exact ⟨_, hor⟩
      | hall ψ =>
        -- φ = ∀⁰ψ, ∼φ = ∃⁰∼ψ. Introduce ∀⁰ψ by the ω-rule; each premise closed by `exI (∼ψ) n`
        -- over the IH at `ψ/[nm n]` (same complexity as ψ < (∀⁰ψ)'s).
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
        have hex : (∃⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, ∃ a, Provable a 0 (insert (ψ/[nm n]) Γ) := by
          intro n
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
            rw [he]; exact hψk
          obtain ⟨a, ha⟩ := ih (ψ/[nm n]) hcomp
            (Γ := insert (∼(ψ/[nm n])) (insert (ψ/[nm n]) Γ)) (by simp) (by simp)
          have hexI := Provable.exI (∼ψ) n (Γ := insert (ψ/[nm n]) Γ)
            (by have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
                rw [heq]; exact ha)
          rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hex)] at hexI
          exact ⟨a + 1, hexI⟩
        choose β hβ using fam
        have hall := Provable.allω ψ (Γ := Γ) hβ
        rw [Finset.insert_eq_self.mpr hp] at hall
        exact ⟨_, hall⟩
      | hexs ψ =>
        -- φ = ∃⁰ψ, ∼φ = ∀⁰∼ψ. Dual: introduce ∀⁰∼ψ by the ω-rule; each premise closed by `exI ψ n`.
        have hψk : ψ.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
        have hall' : (∀⁰ ∼ψ) ∈ Γ := by simpa using hn
        have fam : ∀ n, ∃ a, Provable a 0 (insert ((∼ψ)/[nm n]) Γ) := by
          intro n
          have hcomp : (ψ/[nm n]).complexity ≤ k := by
            have he : (ψ/[nm n]).complexity = ψ.complexity := by simp
            rw [he]; exact hψk
          obtain ⟨a, ha⟩ := ih (ψ/[nm n]) hcomp
            (Γ := insert (ψ/[nm n]) (insert (∼(ψ/[nm n])) Γ)) (by simp) (by simp)
          have hexI := Provable.exI ψ n (Γ := insert (∼(ψ/[nm n])) Γ) ha
          rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp)] at hexI
          have heq : (∼ψ)/[nm n] = ∼(ψ/[nm n]) := by simp
          rw [heq]; exact ⟨a + 1, hexI⟩
        choose β hβ using fam
        have hall := Provable.allω (∼ψ) (Γ := Γ) hβ
        rw [Finset.insert_eq_self.mpr hall'] at hall
        exact ⟨_, hall⟩
  exact key φ.complexity φ le_rfl hp hn

/-- The numeral `nm m` evaluates to `m` in the standard ℕ-model (any free assignment). -/
lemma valm_nm (m : ℕ) (f : ℕ → ℕ) : GoodsteinPA.Compat.gValm ℕ ![] f (nm m) = m := by
  simp [nm]

/-- **ω-completeness for true closed formulas.** Any closed (`ArithmeticFormula ℕ`) formula that is
TRUE in the standard model `ℕ` (`LitTrue`) is `Z∞`-derivable, cut-free. Proof by induction on
`complexity`: atomic via `axTrue`, `∀` via the ω-rule `allω`, `∃` by choosing a true witness.
- [Tow20, §14] -/
theorem provable_true (k : ℕ) (φ : ArithmeticFormula ℕ) (hk : φ.complexity ≤ k)
    (htrue : LitTrue φ) (hmem : φ ∈ Γ) : ∃ a, Provable a 0 Γ := by
  induction k generalizing φ Γ htrue hmem with
  | zero =>
    cases φ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR hmem⟩
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact ⟨0, Provable.axTrue true r v htrue hmem⟩
    | hnrel r v => exact ⟨0, Provable.axTrue false r v htrue hmem⟩
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    cases φ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR hmem⟩
    | hfalsum => simp [LitTrue] at htrue
    | hrel r v => exact ⟨0, Provable.axTrue true r v htrue hmem⟩
    | hnrel r v => exact ⟨0, Provable.axTrue false r v htrue hmem⟩
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have htab : LitTrue a ∧ LitTrue b := by simpa [LitTrue] using htrue
      obtain ⟨hta, htb⟩ := htab
      obtain ⟨a1, h1⟩ := ih a hak hta (Γ := insert a Γ) (by simp)
      obtain ⟨a2, h2⟩ := ih b hbk htb (Γ := insert b Γ) (by simp)
      have hand := Provable.andI a b h1 h2
      rw [Finset.insert_eq_self.mpr hmem] at hand
      exact ⟨_, hand⟩
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have htor : LitTrue a ∨ LitTrue b := by simpa [LitTrue] using htrue
      rcases htor with hta | htb
      · obtain ⟨a1, h1⟩ := ih a hak hta (Γ := insert a (insert b Γ)) (by simp)
        have hor := Provable.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        exact ⟨_, hor⟩
      · obtain ⟨a1, h1⟩ := ih b hbk htb (Γ := insert a (insert b Γ)) (by simp)
        have hor := Provable.orI a b h1
        rw [Finset.insert_eq_self.mpr hmem] at hor
        exact ⟨_, hor⟩
    | hall a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hfam : ∀ n, LitTrue (a/[nm n]) := by
        intro n
        have := htrue
        simp only [LitTrue, Semiformula.eval_all] at this
        simpa [LitTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton]
          using this n
      have fam : ∀ n, ∃ x, Provable x 0 (insert (a/[nm n]) Γ) := by
        intro n
        have hcomp : (a/[nm n]).complexity ≤ k := by
          have : (a/[nm n]).complexity = a.complexity := by simp
          rw [this]; exact hak
        exact ih (a/[nm n]) hcomp (hfam n) (by simp)
      choose β hβ using fam
      have hallω := Provable.allω a hβ
      rw [Finset.insert_eq_self.mpr hmem] at hallω
      exact ⟨_, hallω⟩
    | hexs a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hex : ∃ n, LitTrue (a/[nm n]) := by
        have := htrue
        simp only [LitTrue, Semiformula.eval_ex] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [LitTrue, Semiformula.eval_substs, valm_nm,
          Matrix.constant_eq_singleton] using hx⟩
      obtain ⟨n, hn⟩ := hex
      have hcomp : (a/[nm n]).complexity ≤ k := by
        have : (a/[nm n]).complexity = a.complexity := by simp
        rw [this]; exact hak
      obtain ⟨x, hx⟩ := ih (a/[nm n]) hcomp hn (Γ := insert (a/[nm n]) Γ) (by simp)
      have hexI := Provable.exI a n hx
      rw [Finset.insert_eq_self.mpr hmem] at hexI
      exact ⟨_, hexI⟩

end GoodsteinPA.ZinftyF
