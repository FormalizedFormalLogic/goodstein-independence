/-
# Cut elimination for the `Z_∞` calculus

Cut reductions (`∧`/`∨`- and `∀`/`∃`-principal), atomic and `⊥` cut removal, the rank-lowering
step `cut_elimination_step` (cut rank `c+1 → c`) and full cut elimination `cut_elimination` (cut-free).
- [Tow20, §19.5, §19.6, §19.7, §19.9]
-/
module

public import GoodsteinPA.ToMathlib.OmegaTower
public import GoodsteinPA.Zinfty.Inversion

@[expose] public section

namespace GoodsteinPA.Zinfty

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm
open Derivation

variable {Γ Δ : Finset (ArithmeticFormula ℕ)} {α β : Ordinal.{0}} {c : ℕ}
         {φ ψ : ArithmeticFormula ℕ} {φₓ : ArithmeticSemiformula ℕ 1}

/-- Frame subset: push an `insert` out of the `erase`/`∪`-framed context (`ih`-result → canonical).
Explicit (not `tauto`) to avoid `whnf` blow-ups on negated atoms. -/
private theorem frame_in (a e : ArithmeticFormula ℕ) (s t : Finset (ArithmeticFormula ℕ)) :
    (insert a s).erase e ∪ t ⊆ insert a (s.erase e ∪ t) := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hne, hxa | hxs⟩ | hxt
  · exact Or.inl hxa
  · exact Or.inr (Or.inl ⟨hne, hxs⟩)
  · exact Or.inr (Or.inr hxt)

/-- Frame subset: pull an `insert` back into the `erase`/`∪`-framed context (canonical → goal),
valid when the head `a` is not the erased formula. -/
private theorem frame_out {a e : ArithmeticFormula ℕ} (hne : a ≠ e) (s t : Finset (ArithmeticFormula ℕ)) :
    insert a (s.erase e ∪ t) ⊆ (insert a s).erase e ∪ t := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with rfl | (⟨hne', hxs⟩ | hxt)
  · exact Or.inl ⟨hne, Or.inl rfl⟩
  · exact Or.inl ⟨hne', Or.inr hxs⟩
  · exact Or.inr hxt

namespace Provable

/-! ### Cut reduction, ∧/∨ principal (Towsner §19.5)

**Design note.** Natural (Hessenberg) sum `α ♯ β` is unavailable, so the classic reduction-lemma
bound `α ♯ β` cannot be used. For the **∧/∨** case there is a route that needs no natural sum and
no fresh induction: both connectives are **invertible** (`and_inv_left/right`, `or_inv`), so we invert
*both* premises and close with **two ordinary cuts** at the strictly smaller subformulas. The
resulting bound is `max α β + 1 + 1`, and `max(ω^a, ω^b) + 2 < ω^{max a b + 1}` keeps `cut_elimination_step`
below `ω^α` with room to spare. (The ∀/∃ case is genuinely different — `∃` is *not* invertible —
and needs the §19.6 induction on the ∃-side; see `cut_reduce_all` below.) -/

/-- Reduce a cut on a **conjunction** `φ ⋏ ψ` (its negation `∼φ ⋎ ∼ψ` on the other side), with both
conjuncts of complexity `< c`.
- [Tow20, Theorem 19.5] -/
lemma cut_reduce_and (ha : (φ.complexity + 1 : ℕ∞) ≤ c) (hb : (ψ.complexity + 1 : ℕ∞) ≤ c)
    (hC : Provable α c (insert (φ ⋏ ψ) Γ)) (hNC : Provable β c (insert (∼φ ⋎ ∼ψ) Γ)) :
    Provable (max α β + 1 + 1) c Γ := by
  -- ∧-inversion of the left premise → `φ, Γ` and `ψ, Γ` (same bound `α`).
  have hA : Provable α c (insert φ Γ) :=
    (hC.and_inv_left (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hB : Provable α c (insert ψ Γ) :=
    (hC.and_inv_right (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- ∨-inversion of the right premise → `∼φ, ∼ψ, Γ` (same bound `β`).
  have hNab : Provable β c (insert (∼φ) (insert (∼ψ) Γ)) :=
    (hNC.or_inv (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- cut on `φ`: `(φ, ∼ψ, Γ)` × `(∼φ, ∼ψ, Γ)` ⟹ `(∼ψ, Γ)`.
  have cutA : Provable (max α β + 1) c (insert (∼ψ) Γ) :=
    Provable.cut φ ha (hA.weakening (by
      intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto)) hNab
  -- cut on `ψ`: `(ψ, Γ)` × `(∼ψ, Γ)` ⟹ `Γ`.
  have cutB : Provable (max α (max α β + 1) + 1) c Γ := Provable.cut ψ hb hB cutA
  -- `max α (max α β + 1) + 1 = max α β + 1 + 1`.
  have he : max α (max α β + 1) + 1 = max α β + 1 + 1 := by
    congr 1
    exact max_eq_right (le_trans (le_max_left α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  exact he ▸ cutB

/-- Reduce a cut on a **disjunction** `φ ⋎ ψ` (its negation `∼φ ⋏ ∼ψ` on the other side), with both
disjuncts of complexity `< c`. Dual to `cut_reduce_and`.
- [Tow20, Theorem 19.5] -/
lemma cut_reduce_or (ha : (φ.complexity + 1 : ℕ∞) ≤ c) (hb : (ψ.complexity + 1 : ℕ∞) ≤ c)
    (hC : Provable α c (insert (φ ⋎ ψ) Γ)) (hNC : Provable β c (insert (∼φ ⋏ ∼ψ) Γ)) :
    Provable (max α β + 1 + 1) c Γ := by
  -- ∨-inversion of the left premise → `φ, ψ, Γ`.
  have hAB : Provable α c (insert φ (insert ψ Γ)) :=
    (hC.or_inv (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- ∧-inversion of the right premise → `∼φ, Γ` and `∼ψ, Γ`.
  have hNa : Provable β c (insert (∼φ) Γ) :=
    (hNC.and_inv_left (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  have hNb : Provable β c (insert (∼ψ) Γ) :=
    (hNC.and_inv_right (Finset.mem_insert_self _ _)).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- cut on `φ`: `(φ, ψ, Γ)` × `(∼φ, ψ, Γ)` ⟹ `(ψ, Γ)`.
  have cutA : Provable (max α β + 1) c (insert ψ Γ) :=
    Provable.cut φ ha hAB (hNa.weakening (by
      intro x hx; simp only [Finset.mem_insert] at hx ⊢; tauto))
  -- cut on `ψ`: `(ψ, Γ)` × `(∼ψ, Γ)` ⟹ `Γ`.
  have cutB : Provable (max (max α β + 1) β + 1) c Γ := Provable.cut ψ hb cutA hNb
  have he : max (max α β + 1) β + 1 = max α β + 1 + 1 := by
    congr 1
    exact max_eq_left (le_trans (le_max_right α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  exact he ▸ cutB

/-! ### Cut reduction, ∀/∃ principal (Towsner §19.6)

Unlike ∧/∨, the existential is **not invertible**, so there is no double-inversion shortcut. We
invert the ∀-side once (`all_inv` → the numeral-indexed family `φ/[nm n]`) and then **induct on the
∃-side derivation**, cutting at the witness numeral when `∃∼φ` is principal. To keep the inverted
family available unchanged through the induction, it is a *fixed* hypothesis (over a fixed ambient
`Γ`, weakened up at each use) and the running conclusion is framed over `Δ.erase (∃∼φ) ∪ Γ`. -/

/-- The induction core of the ∀/∃ reduction: given the ∀-inversion family `fam` and a derivation
`D` (cut rank `≤ c`) of a sequent containing `∃⁰ ∼φₓ`, the sequent with `∃⁰ ∼φₓ` erased and `Γ`
merged in is provable.
- [Tow20, Theorem 19.6] -/
lemma cut_reduce_allAux (hφc : (φₓ.complexity + 1 : ℕ∞) ≤ c)
    (fam : ∀ n, Provable α c (insert (φₓ/[nm n]) Γ))
    (D : Derivation Δ) (hcr : D.cutRank ≤ c) (hmem : (∃⁰ ∼φₓ) ∈ Δ) :
      Provable (α + D.ordinalBound + 1) c (Δ.erase (∃⁰ ∼φₓ) ∪ Γ) := by
  -- Induct on the ∃-side derivation `D`; `fam` supplies the ∀-side instances at the witness cut.
  induction D with
  | @axL Δ k r v hp hn =>
    refine (Provable.axL r v ?_ ?_).mono zero_le (Nat.zero_le c)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩)
  | @axTrue Δ k b r v htrue hmemAx =>
    refine (Provable.axTrue b r v htrue ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmemAx⟩)
  | @verumR Δ h =>
    refine (Provable.verumR ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)
  | @weak Δ' Δ D' hsub ih =>
    by_cases hd : (∃⁰ ∼φₓ) ∈ Δ'
    · exact (ih hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show Provable D'.ordinalBound c Δ' from ⟨D', le_rfl, hcr⟩).weakening ?_ |>.mono_ordinalBound ?_
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self D'.ordinalBound α)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have hcr0 : D₀.cutRank ≤ c := le_trans (le_max_left _ _) hcr
    have hcr1 : D₁.cutRank ≤ c := le_trans (le_max_right _ _) hcr
    have P0 : Provable (α + D₀.ordinalBound + 1) c (insert χ₀ (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ)) :=
      (ih₀ hcr0 (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    have P1 : Provable (α + D₁.ordinalBound + 1) c (insert χ₁ (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ)) :=
      (ih₁ hcr1 (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.andI P0 P1).weakening (show
        insert (χ₀ ⋏ χ₁) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ) ⊆ (insert (χ₀ ⋏ χ₁) Γ₀).erase (∃⁰ ∼φₓ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨by grind, Or.inl rfl⟩
      · tauto)).mono_ordinalBound (Ordinal.max_add_add_one_add_one_le α D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₀ χ₀ χ₁ D' ih =>
    have P : Provable (α + D'.ordinalBound + 1) c (insert χ₀ (insert χ₁ (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ))) :=
      (ih hcr (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.orI P).weakening (show
        insert (χ₀ ⋎ χ₁) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ) ⊆ (insert (χ₀ ⋎ χ₁) Γ₀).erase (∃⁰ ∼φₓ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨by grind, Or.inl rfl⟩
      · tauto)).mono_ordinalBound (Ordinal.add_add_one_add_one_le α D'.ordinalBound)
  | @allω Γ₀ χ' Dₓ ih =>
    have key : ∀ n, Provable (α + (Dₓ n).ordinalBound + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ)) :=
      fun n => (ih n (le_trans (le_iSup (fun m => (Dₓ m).cutRank) n) hcr)
        (by grind)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.allω key).weakening (show
        insert (∀⁰ χ') (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ) ⊆ (insert (∀⁰ χ') Γ₀).erase (∃⁰ ∼φₓ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨by grind, Or.inl rfl⟩
      · tauto)).mono_ordinalBound (Ordinal.iSup_add_add_one_add_one_le α (fun n => (Dₓ n).ordinalBound))
  | @exI Γ₀ χ' n D' ih =>
    by_cases hhd : (∃⁰ χ') = (∃⁰ ∼φₓ)
    · -- principal: χ' = ∼φ, cut at witness numeral `n`.
      have hχ : χ' = ∼φₓ := by
        have := hhd; simpa [ExsQuantifier.exs] using this
      subst hχ
      rw [Finset.erase_insert_eq_erase]
      have hsubcomp : (((∼φₓ)/[nm n]).complexity + 1 : ℕ∞) ≤ c := by simpa using hφc
      have hcutfml : ((φₓ/[nm n]).complexity + 1 : ℕ∞) ≤ c := by simpa using hφc
      -- the ∃-premise gives `∼(φ/[nm n])` in the context; combine with `fam n`.
      have hNeg : (∼φₓ)/[nm n] = ∼(φₓ/[nm n]) := by simp
      have famn := (fam n).weakening (show insert (φₓ/[nm n]) Γ
          ⊆ insert (φₓ/[nm n]) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ) from by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
      by_cases hd : (∃⁰ ∼φₓ) ∈ Γ₀
      · have Premise : Provable (α + D'.ordinalBound + 1) c (insert ((∼φₓ)/[nm n]) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ)) :=
          (ih hcr (Finset.mem_insert_of_mem hd)).weakening (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        have hctx : insert ((∼φₓ)/[nm n]) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ)
            = insert (∼(φₓ/[nm n])) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ) := by rw [hNeg]
        have hcut := Provable.cut (φₓ/[nm n]) hcutfml famn (Premise.cast hctx)
        refine hcut.mono_ordinalBound ?_
        refine add_le_add_left ?_ 1
        exact max_le le_self_add (le_of_eq (add_assoc α D'.ordinalBound 1))
      · have base : Provable D'.ordinalBound c (insert (∼(φₓ/[nm n])) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ)) := by
          refine (show Provable D'.ordinalBound c (insert ((∼φₓ)/[nm n]) Γ₀) from ⟨D', le_rfl, hcr⟩).weakening ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hxΓ₀
          · left; rw [hNeg]
          · exact Or.inr (Or.inl ⟨fun e => hd (e ▸ hxΓ₀), hxΓ₀⟩)
        have hcut := Provable.cut (φₓ/[nm n]) hcutfml famn base
        refine hcut.mono_ordinalBound ?_
        refine add_le_add_left ?_ 1
        exact max_le le_self_add
          (le_trans (le_of_lt (lt_add_of_pos_right _ one_pos))
            (CanonicallyOrderedAdd.le_add_self (D'.ordinalBound + 1) α))
    · -- commuting: ∃χ' ≠ ∃∼φ.
      have P : Provable (α + D'.ordinalBound + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ)) :=
        (ih hcr (by grind)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ((Provable.exI n P).weakening (show
          insert (∃⁰ χ') (Γ₀.erase (∃⁰ ∼φₓ) ∪ Γ) ⊆ (insert (∃⁰ χ') Γ₀).erase (∃⁰ ∼φₓ) ∪ Γ from by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhd, Or.inl rfl⟩
        · tauto)).mono_ordinalBound (Ordinal.add_add_one_add_one_le α D'.ordinalBound)
  | @cut Γ₀ ξ D₁ D₂ ih₁ ih₂ =>
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ c := (le_max_left _ _).trans hcr
    have hcr1 : D₁.cutRank ≤ c := (le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
    have hcr2 : D₂.cutRank ≤ c := (le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
    have P1 := (ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).weakening (frame_in ξ (∃⁰ ∼φₓ) Γ₀ Γ)
    have P2 := (ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).weakening (frame_in (∼ξ) (∃⁰ ∼φₓ) Γ₀ Γ)
    exact (Provable.cut ξ hcξ P1 P2).mono_ordinalBound (Ordinal.max_add_add_one_add_one_le α D₁.ordinalBound D₂.ordinalBound)

/-- **Cut reduction, ∀/∃ principal.** A cut on `∀⁰ φ` (complexity `≤ c`), with an `∀`-side derivation
of bound `α` and an `∃`-side derivation of bound `β`, reduces to bound `α + β + 1`.
- [Tow20, Theorem 19.6] -/
lemma cut_reduce_all {φ : ArithmeticSemiformula ℕ 1}
  (hφc : (φ.complexity + 1 : ℕ∞) ≤ c)
  (hC : Provable α c (insert (∀⁰ φ) Γ)) (hNC : Provable β c (insert (∃⁰ ∼φ) Γ)) :
  Provable (α + β + 1) c Γ := by
  -- ∀-inversion → the numeral family.
  have fam : ∀ n, Provable α c (insert (φ/[nm n]) Γ) := fun n =>
    (hC.all_inv (Finset.mem_insert_self _ _) n).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
  -- induct on the ∃-side derivation `D`, cutting at the witness numeral when `∃∼φ` is principal.
  rcases hNC with ⟨D, ho, hcr⟩
  have haux := cut_reduce_allAux hφc fam D hcr (Finset.mem_insert_self _ _)
  refine (haux.weakening (show (insert (∃⁰ ∼φ) Γ).erase (∃⁰ ∼φ) ∪ Γ ⊆ Γ from by
    intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)).mono_ordinalBound ?_
  exact add_le_add_left ((add_le_add_iff_left α).mpr ho) 1

/-! ### Ordinal bound bookkeeping for cut-rank elimination

All cases keep the new bound below `ω^(·+1)`, exploiting that `ω^c` is **additively principal**
(`isPrincipal_add_omega0_opow`): finite `+`-combinations of things `< ω^c` stay `< ω^c`. -/

/-- **Removing a FALSE closed literal** `L = signedLit b₀ r₀ v₀` (`¬ LitTrue L`) from a cut-free
derivation, bound-preserving — the *truth layer* the ω-logic atomic cut elimination needs (Schütte /
Buchholz; the generalization of `remove_falsumAux` from `⊥` to any false literal).
- [Tow20, Theorem 19.2] -/
lemma remove_false_litAux (b₀ : Bool) (r₀ : (ℒₒᵣ).Rel k₀) (v₀) (hL : ¬ LitTrue (signedLit b₀ r₀ v₀))
  (D : Derivation Δ) (hcr : D.cutRank ≤ 0) (hmem : signedLit b₀ r₀ v₀ ∈ Δ) :
  Provable D.ordinalBound 0 (Δ.erase (signedLit b₀ r₀ v₀)) := by
  set L : ArithmeticFormula ℕ := signedLit b₀ r₀ v₀ with hLdef
  have hLne : ∀ g : ArithmeticFormula ℕ, g.complexity ≠ 0 → g ≠ L := by
    intro g hg; rw [hLdef]; exact Semiformula.ne_of_ne_complexity (by cases b₀ <;> simp [signedLit, hg])
  -- `L` is never principal in a logical rule, so it is incidental at every compound step; the only
  -- new content is at the leaves: an `axL` clash on `L` exposes its (TRUE) opposite polarity `∼L`,
  -- closed by `axTrue`; an `axTrue` leaf's true witness is `≠ L` (which is false), so it survives
  -- the erase.
  induction D with
  | @axL Δ k r v hp hn =>
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
  | @axTrue Δ k b r v htrue hmemAx =>
    -- the true witness `signedLit b r v ≠ L` (false), so it survives the erase.
    have hne : signedLit b r v ≠ L := fun e => hL (e ▸ htrue)
    exact Provable.axTrue b r v htrue (Finset.mem_erase.mpr ⟨hne, hmemAx⟩)
  | @verumR Δ h =>
    exact Provable.verumR (Finset.mem_erase.mpr ⟨by rw [hLdef]; exact (lit_ne_verum).symm, h⟩)
  | @weak Δ' Δ D' hsub ih =>
    by_cases hd : L ∈ Δ'
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Provable D'.ordinalBound 0 Δ' from ⟨D', le_rfl, hcr⟩).weakening ?_
      intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₀ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have P0 : Provable D₀.ordinalBound 0 (insert χ₀ (Γ₀.erase L)) :=
      (ih₀ (le_trans (le_max_left _ _) hcr) (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : Provable D₁.ordinalBound 0 (insert χ₁ (Γ₀.erase L)) :=
      (ih₁ (le_trans (le_max_right _ _) hcr) (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.andI P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨by grind, Or.inl rfl⟩
      · tauto)
  | @orI Γ₀ χ₀ χ₁ D' ih =>
    have P : Provable D'.ordinalBound 0 (insert χ₀ (insert χ₁ (Γ₀.erase L))) :=
      (ih hcr (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.orI P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨by grind, Or.inl rfl⟩
      · tauto)
  | @allω Γ₀ χ' Dₓ ih =>
    have key : ∀ n, Provable (Dₓ n).ordinalBound 0 (insert (χ'/[nm n]) (Γ₀.erase L)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => (Dₓ m).cutRank) n) hcr)
        (by grind)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.allω key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨by grind, Or.inl rfl⟩
      · tauto)
  | @exI Γ₀ χ' n D' ih =>
    have P : Provable D'.ordinalBound 0 (insert (χ'/[nm n]) (Γ₀.erase L)) :=
      (ih hcr (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.exI n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨by grind, Or.inl rfl⟩
      · tauto)
  | @cut Γ₀ ξ D₁ D₂ ih₁ ih₂ =>
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-! ### Atomic cut elimination (Towsner Thm 19.2, the false-atomic inversion content)

The cut formula is atomic (`rel r v`), so it is **never principal in a logical rule** — it only
enters via `axL` or weakening. No truth layer is needed: set sequents dissolve the key case. If an
`axL` clashes exactly on the cut atom `(rel r v, nrel r v)`, then `nrel r v ∈ Γ`, so the *other*
premise (`⊢ nrel r v, Γ`) already proves `Γ` (set idempotence). Every other case is incidental. -/

/-- Induction core: cut a `rel r v` derivation (`D`) against a fixed `nrel r v` derivation (`hNC`).
- [Tow20, Theorem 19.2] -/
lemma atom_cutAux (r : (ℒₒᵣ).Rel k) (v)
  (hNC : Provable β 0 (insert (Semiformula.nrel r v) Γ))
  (D : Derivation Δ) (hcr : D.cutRank ≤ 0) (hmem : (Semiformula.rel r v) ∈ Δ) :
  Provable (β + D.ordinalBound + 1) 0 (Δ.erase (Semiformula.rel r v) ∪ Γ) := by
  induction D with
  | @axL Δ k' r' v' hp hn =>
    have hnn : (Semiformula.nrel r' v' : ArithmeticFormula ℕ) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by intro h; exact absurd h (by simp), hn⟩
    by_cases hrel : (Semiformula.rel r' v' : ArithmeticFormula ℕ) = Semiformula.rel r v
    · -- the clash's positive member IS the cut atom ⇒ `nrel r v ∈ Γ`-part, use `hNC`
      have hnrv : (Semiformula.nrel r' v' : ArithmeticFormula ℕ) = Semiformula.nrel r v := by
        rw [← Semiformula.neg_rel r' v', hrel, Semiformula.neg_rel]
      refine (hNC.weakening ?_).mono_ordinalBound ?_
      · intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hxΓ
        · exact Finset.mem_union_left _ (hnrv ▸ hnn)
        · exact Finset.mem_union_right _ hxΓ
      · exact le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos))
    · -- clash avoids the cut atom ⇒ it survives the erase, close by `axL`
      have hpp : (Semiformula.rel r' v' : ArithmeticFormula ℕ) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨hrel, hp⟩
      exact (Provable.axL r' v' (Finset.mem_union_left _ hpp)
        (Finset.mem_union_left _ hnn)).mono_ordinalBound zero_le
  | @axTrue Δ k' b' r' v' htrue' hmem' =>
    by_cases heq : (signedLit b' r' v' : ArithmeticFormula ℕ) = Semiformula.rel r v
    · -- the true literal IS the cut atom ⇒ `rel r v` is TRUE ⇒ `nrel r v` is a removable false
      -- literal on the `hNC` side. The TRUTH-LAYER key case.
      have htrue_rel : LitTrue (Semiformula.rel r v) := heq ▸ htrue'
      have hfalse : ¬ LitTrue (signedLit false r v) := by
        rw [←litTrue_flip]; simpa [signedLit] using htrue_rel
      obtain ⟨DN, hoN, hcrN⟩ := hNC
      have hrm := remove_false_litAux false r v hfalse DN hcrN
        (show signedLit false r v ∈ insert (Semiformula.nrel r v) Γ by simp [signedLit])
      refine (hrm.weakening ?_).mono_ordinalBound ?_
      · intro x hx
        have hxΓ : x ∈ Γ := by
          have h1 := Finset.mem_of_mem_erase hx
          have h2 := Finset.ne_of_mem_erase hx
          rcases Finset.mem_insert.mp h1 with rfl | h3
          · exact absurd (show (Semiformula.nrel r v : ArithmeticFormula ℕ) = signedLit false r v by simp [signedLit]) h2
          · exact h3
        exact Finset.mem_union_right _ hxΓ
      · exact le_trans hoN (le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos)))
    · -- the true literal avoids the cut atom ⇒ survives the erase, close by `axTrue`
      have hll : (signedLit b' r' v' : ArithmeticFormula ℕ) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨heq, hmem'⟩
      exact (Provable.axTrue b' r' v' htrue' (Finset.mem_union_left _ hll)).mono_ordinalBound zero_le
  | @verumR Δ h =>
    have ht : (⊤ : ArithmeticFormula ℕ) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by simp, h⟩
    exact (Provable.verumR (Finset.mem_union_left _ ht)).mono_ordinalBound zero_le
  | @weak Δ' Δ D' hsub ih =>
    by_cases hd : (Semiformula.rel r v) ∈ Δ'
    · exact (ih hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show Provable D'.ordinalBound 0 Δ' from ⟨D', le_rfl, hcr⟩).weakening ?_ |>.mono_ordinalBound ?_
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self D'.ordinalBound β)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have hhead : (χ₀ ⋏ χ₁) ≠ (Semiformula.rel r v) := by grind
    have hcr0 : D₀.cutRank ≤ 0 := le_trans (le_max_left _ _) hcr
    have hcr1 : D₁.cutRank ≤ 0 := le_trans (le_max_right _ _) hcr
    have P0 : Provable (β + D₀.ordinalBound + 1) 0 (insert χ₀ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₀ hcr0 (by grind)).weakening (frame_in χ₀ _ Γ₀ Γ)
    have P1 : Provable (β + D₁.ordinalBound + 1) 0 (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₁ hcr1 (by grind)).weakening (frame_in χ₁ _ Γ₀ Γ)
    exact ((Provable.andI P0 P1).weakening (frame_out hhead Γ₀ Γ)).mono_ordinalBound
      (Ordinal.max_add_add_one_add_one_le β D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₀ χ₀ χ₁ D' ih =>
    have hhead : (χ₀ ⋎ χ₁) ≠ (Semiformula.rel r v) := by grind
    have P : Provable (β + D'.ordinalBound + 1) 0 (insert χ₀ (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ))) :=
      (ih hcr (by grind)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    exact ((Provable.orI P).weakening (frame_out hhead Γ₀ Γ)).mono_ordinalBound (Ordinal.add_add_one_add_one_le β D'.ordinalBound)
  | @allω Γ₀ χ' Dₓ ih =>
    have hhead : (∀⁰ χ') ≠ (Semiformula.rel r v) := by grind
    have key : ∀ n, Provable (β + (Dₓ n).ordinalBound + 1) 0
        (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => (Dₓ m).cutRank) n) hcr)
        (by grind)).weakening (frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((Provable.allω key).weakening (frame_out hhead Γ₀ Γ)).mono_ordinalBound
      (Ordinal.iSup_add_add_one_add_one_le β (fun n => (Dₓ n).ordinalBound))
  | @exI Γ₀ χ' n D' ih =>
    have hhead : (∃⁰ χ') ≠ (Semiformula.rel r v) := by simp
    have P : Provable (β + D'.ordinalBound + 1) 0 (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih hcr (by grind)).weakening (frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((Provable.exI n P).weakening (frame_out hhead Γ₀ Γ)).mono_ordinalBound (Ordinal.add_add_one_add_one_le β D'.ordinalBound)
  | @cut Γ₀ ξ D₁ D₂ ih₁ ih₂ =>
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- **Atomic cut elimination**: eliminate a cut whose cut formula is atomic, at cut rank `0`.
- [Tow20, Theorem 19.2] -/
lemma atom_cut (r : (ℒₒᵣ).Rel k) (v)
  (hC : Provable α 0 (insert (Semiformula.rel r v) Γ))
  (hNC : Provable β 0 (insert (Semiformula.nrel r v) Γ)) :
  Provable (β + α + 1) 0 Γ := by
  obtain ⟨D, ho, hcr⟩ := hC;
  refine ((atom_cutAux r v hNC D hcr (Finset.mem_insert_self _ _)).weakening
    (show (insert (Semiformula.rel r v) Γ).erase (Semiformula.rel r v) ∪ Γ ⊆ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢;
      tauto)).mono_ordinalBound ?_
  exact add_le_add_left ((add_le_add_iff_left β).mpr ho) 1

/-- Removing `⊥` from a cut-free derivation, bound-preserving.
- [Tow20, Theorem 19.2] -/
lemma remove_falsumAux (D : Derivation Γ) (hcr : D.cutRank ≤ 0) (hmem : ⊥ ∈ Γ) : Provable D.ordinalBound 0 (Γ.erase ⊥) := by
  -- `⊥` is never introduced by any rule and is never an `axL`/`verumR` witness, so it is
  -- incidental at every step.
  induction D with
  | @axL Γ k r v hp hn =>
    exact Provable.axL r v (Finset.mem_erase.mpr ⟨by simp, hp⟩) (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | @axTrue Γ k b r v htrue hmem =>
    exact Provable.axTrue b r v htrue (Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit], ‹_›⟩)
  | @verumR Δ h =>
    exact Provable.verumR (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | @weak Δ Γ D hsub ih =>
    by_cases hd : ⊥ ∈ Δ;
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Provable D.ordinalBound 0 Δ from ⟨D, le_rfl, hcr⟩).weakening ?_;
      . intro x;
        simp only [Finset.mem_erase];
        grind;
  | @andI Γ₀ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    have hhead : (χ₀ ⋏ χ₁) ≠ (⊥ : ArithmeticFormula ℕ) := by simp [Wedge.wedge]
    have hmem0 : ⊥ ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : Provable D₀.ordinalBound 0 (insert χ₀ (Γ₀.erase ⊥)) :=
      (ih₀ (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening $ by
        intro x hx;
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢;
        tauto
    have P1 : Provable D₁.ordinalBound 0 (insert χ₁ (Γ₀.erase ⊥)) :=
      (ih₁ (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening $ by
        intro x hx;
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢;
        tauto;
    exact (Provable.andI P0 P1).weakening $ by
      intro x;
      simp only [Finset.mem_insert, Finset.mem_erase];
      rintro (rfl | hx);
      · tauto;
      · tauto;
  | @orI Γ₀ χ₀ χ₁ D ih =>
    have hmem0 : ⊥ ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left $ by tauto
    have P : Provable D.ordinalBound 0 (insert χ₀ (insert χ₁ (Γ₀.erase ⊥))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening $ by
      intro x hx;
      simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢;
      tauto;
    exact (Provable.orI P).weakening $ by
      intro x;
      simp only [Finset.mem_insert, Finset.mem_erase];
      rintro (rfl | hx);
      · tauto;
      · tauto;
  | @allω Γ₀ χ' Dₓ ih =>
    have hmem0 : ⊥ ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => by tauto;
    have Pₓ : ∀ n, Provable (Dₓ n).ordinalBound 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) := by
      intro n;
      exact (ih n (le_trans (le_iSup (fun m => (Dₓ m).cutRank) n) hcr) (Finset.mem_insert_of_mem hmem0)).weakening $ by
        intro x hx;
        simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢;
        tauto;
    exact (Provable.allω Pₓ).weakening $ by
      intro x;
      simp only [Finset.mem_insert, Finset.mem_erase];
      rintro (rfl | hx);
      · tauto;
      · tauto;
  | @exI Γ₀ χ' n D ih =>
    have hmem0 : ⊥ ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => by tauto;
    have P : Provable D.ordinalBound 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) := (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening $ by
      intro x;
      simp only [Finset.mem_insert, Finset.mem_erase];
      tauto
    exact (Provable.exI n P).weakening $ by
      intro x;
      simp only [Finset.mem_insert, Finset.mem_erase];
      rintro (rfl | hx)
      · tauto;
      · tauto;
  | @cut Γ₀ ξ D₁ D₂ ih₁ ih₂ =>
    have := (le_max_left _ _).trans hcr;
    contradiction;

local notation "ω₀" => Ordinal.omega0

/-- Remove a `⊥` from a cut-free sequent.
- [Tow20, Theorem 19.2] -/
lemma remove_falsum (h : Provable α 0 (insert ⊥ Γ)) : Provable α 0 Γ := by
  obtain ⟨D, ho, hcr⟩ := h;
  refine (Provable.remove_falsumAux D hcr (Finset.mem_insert_self _ _)).weakening ?_ |>.mono_ordinalBound ho
  . intro x hx;
    simp only [Finset.mem_erase, Finset.mem_insert] at hx;
    exact (hx.2).resolve_left hx.1

/-- **Principal cut on a rank-`c` formula.** After both premises are
cut-free-at-`c` (bound `ω^α`, `ω^β`), a cut on `ξ` with `complexity ξ = c` is eliminated,
staying below `ω^(max α β + 1)`.
- [Tow20, Theorem 19.7] -/
lemma cut_elim_principal {ξ : ArithmeticFormula ℕ}
  (hξeq : ξ.complexity = c)
  (hC : Provable (ω₀ ^ α) c (insert ξ Γ))
  (hNC : Provable (ω₀ ^ β) c (insert (∼ξ) Γ)) :
  Provable (ω₀ ^ (max α β + 1)) c Γ := by
  -- dispatch on the shape of `ξ`: ∧/∨ → `cut_reduce_and/or`; ∀/∃ → `cut_reduce_all`;
  -- atomic → `atom_cut`; ⊤/⊥ → `remove_falsum`.
  cases ξ with
  | verum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : Provable (ω₀ ^ β) 0 (insert (⊥ : ArithmeticFormula ℕ) Γ) := hNC
      refine (remove_falsum hNC').mono_ordinalBound ?_
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_right α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | falsum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (remove_falsum hC).mono_ordinalBound ?_
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_left α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | rel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (atom_cut r v hC hNC).mono_ordinalBound ?_
      rw [max_comm α β]; exact Ordinal.opow_add_opow_add_one_le β α
  | nrel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : Provable (ω₀ ^ β) 0 (insert (Semiformula.rel r v) Γ) := hNC
      exact (atom_cut r v hNC' hC).mono_ordinalBound (Ordinal.opow_add_opow_add_one_le α β)
  | and φ' ψ' =>
      have hM : max φ'.complexity ψ'.complexity + 1 = c := hξeq
      have han : φ'.complexity + 1 ≤ c := by have := le_max_left φ'.complexity ψ'.complexity; omega
      have hbn : ψ'.complexity + 1 ≤ c := by have := le_max_right φ'.complexity ψ'.complexity; omega
      exact (Provable.cut_reduce_and (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono_ordinalBound
        (Ordinal.max_opow_add_two_le α β)
  | or φ' ψ' =>
      have hM : max φ'.complexity ψ'.complexity + 1 = c := hξeq
      have han : φ'.complexity + 1 ≤ c := by have := le_max_left φ'.complexity ψ'.complexity; omega
      have hbn : ψ'.complexity + 1 ≤ c := by have := le_max_right φ'.complexity ψ'.complexity; omega
      exact (Provable.cut_reduce_or (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono_ordinalBound
        (Ordinal.max_opow_add_two_le α β)
  | all φ' =>
      have hφn : φ'.complexity + 1 ≤ c := le_of_eq hξeq
      exact (Provable.cut_reduce_all (by exact_mod_cast hφn) hC hNC).mono_ordinalBound
        (Ordinal.opow_add_opow_add_one_le α β)
  | exs φ' =>
      -- ξ = ∃φ', ∼ξ = ∀∼φ'.  Use `cut_reduce_all` with ∀-side = hNC, ∃-side = hC.
      have hφn : (∼φ').complexity + 1 ≤ c := by
        rw [Semiformula.complexity_neg]; exact le_of_eq hξeq
      have hC' : Provable (ω₀ ^ α) c (insert (∃⁰ ∼(∼φ')) Γ) := by
        rw [DeMorgan.neg]; exact hC
      refine ((Provable.cut_reduce_all (by exact_mod_cast hφn) hNC hC').mono_ordinalBound ?_)
      rw [max_comm α β]; exact Ordinal.opow_add_opow_add_one_le β α

/-- The transfinite induction underlying the rank-lowering step: a derivation of cut rank `≤ c+1`
becomes cut-free-at-`c` at bound `ω^D.ordinalBound`.
- [Tow20, Theorem 19.7] -/
lemma cut_elimination_stepAux (D : Derivation Γ) (hcr : D.cutRank ≤ (c + 1)) : Provable (ω₀ ^ D.ordinalBound) c Γ := by
  induction D with
  | @axL Γ k r v hp hn =>
    exact (Provable.axL r v hp hn).mono zero_le (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    exact (Provable.axTrue b r v htrue hmem).mono zero_le (Nat.zero_le c)
  | @verumR Γ h =>
    exact (Provable.verumR h).mono zero_le (Nat.zero_le c)
  | @weak Δ Γ D' hsub ih =>
    exact (ih hcr).weakening hsub
  | @andI Γ₀ χ₀ χ₁ D₀ D₁ ih₀ ih₁ =>
    -- non-principal: reapply `andI`, each `ω^· + small ≤ ω^(·+1)`.
    exact (Provable.andI (ih₀ ((le_max_left _ _).trans hcr))
      (ih₁ ((le_max_right _ _).trans hcr))).mono_ordinalBound (Ordinal.max_opow_add_one_le D₀.ordinalBound D₁.ordinalBound)
  | @orI Γ₀ χ₀ χ₁ D' ih =>
    exact (Provable.orI (ih hcr)).mono_ordinalBound (Ordinal.opow_add_one_le' D'.ordinalBound)
  | @allω Γ₀ χ' Dₓ ih =>
    have IH : ∀ n, Provable (ω₀ ^ (Dₓ n).ordinalBound) c (insert (χ'/[nm n]) Γ₀) :=
      fun n => ih n ((le_iSup (fun m => (Dₓ m).cutRank) n).trans hcr)
    exact (Provable.allω IH).mono_ordinalBound (Ordinal.sup_opow_add_one_le (fun n => (Dₓ n).ordinalBound))
  | @exI Γ₀ χ' n D' ih =>
    exact (Provable.exI n (ih hcr)).mono_ordinalBound (Ordinal.opow_add_one_le' D'.ordinalBound)
  | @cut Γ₀ ξ D₁ D₂ ih₁ ih₂ =>
    have hcr1 : D₁.cutRank ≤ (c + 1 : ℕ∞) :=
      (le_max_left D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
    have hcr2 : D₂.cutRank ≤ (c + 1 : ℕ∞) :=
      (le_max_right D₁.cutRank D₂.cutRank).trans ((le_max_right _ _).trans hcr)
    have hξc : (ξ.complexity + 1 : ℕ∞) ≤ (c + 1 : ℕ∞) := (le_max_left _ _).trans hcr
    have IH1 := ih₁ hcr1
    have IH2 := ih₂ hcr2
    -- a rank-`< c` cut is kept; a rank-`= c` cut is eliminated by `cut_elim_principal`.
    by_cases hkeep : ξ.complexity < c
    · exact (Provable.cut ξ (by exact_mod_cast Nat.succ_le_of_lt hkeep) IH1 IH2).mono_ordinalBound
        (Ordinal.max_opow_add_one_le D₁.ordinalBound D₂.ordinalBound)
    · have hξle : ξ.complexity ≤ c := Nat.le_of_succ_le_succ (by exact_mod_cast hξc)
      have hξeq : ξ.complexity = c := le_antisymm hξle (not_lt.mp hkeep)
      exact Provable.cut_elim_principal hξeq IH1 IH2

/-- **One level of cut elimination**: reducing the cut rank by one raises the
ordinal bound to `ω^α`.
- [Tow20, Theorem 19.7] -/
lemma cut_elimination_step (h : Provable α (c + 1) Γ) : Provable (ω₀ ^ α) c Γ := by
  obtain ⟨D, ho, hcr⟩ := h;
  exact (cut_elimination_stepAux D hcr).mono_ordinalBound (Ordinal.opow_le_opow_right Ordinal.omega0_pos ho);

/-- **Full cut elimination**: a sequent derivable at cut rank `c` (bound `α`) is derivable
cut-free at the `c`-fold iterated ω-power `ω_c^α`.
- [Tow20, Theorem 19.9] -/
theorem cut_elimination (h : Provable α c Γ) : Provable (Ordinal.omegaTower c α) 0 Γ := by
  -- iterate `cut_elimination_step` `c` times.
  induction c generalizing α with
  | zero => simpa [Ordinal.omegaTower] using h;
  | succ c ih => exact ih (cut_elimination_step h);

end Provable

end GoodsteinPA.Zinfty
