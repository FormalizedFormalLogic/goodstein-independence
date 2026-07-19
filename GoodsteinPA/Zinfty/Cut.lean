/-
# Cut elimination for the `Z_∞` calculus

Cut reductions (`∧`/`∨`- and `∀`/`∃`-principal), atomic and `⊥` cut removal, the rank-lowering
step `cutElimStep` (cut rank `c+1 → c`) and full cut elimination `cutElim` (cut-free), together
with the `ε₀`-closure of the resulting ordinal bound.
- [Tow20, §19.5, §19.6, §19.7, §19.9]
-/
module

public import GoodsteinPA.Zinfty.Inversion

@[expose] public section

namespace GoodsteinPA.ZinftyF

open LO LO.FirstOrder
open Derivation

variable {Γ : Finset (ArithmeticFormula ℕ)} {α β : Ordinal.{0}} {c : ℕ}

/-- Towsner **Def 19.8**: `ω`-tower over `α` of height `c` (`ω_c^α`), bottom-up:
`ω_0^α = α`, `ω_{c+1}^α = ω_c^(ω^α)`. The cut-elimination ordinal blow-up. -/
@[grind =]
noncomputable def omegaTower : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, α => α
  | c + 1, α => omegaTower c (Ordinal.omega0 ^ α)

@[simp, grind =] lemma omegaTower_zero (α : Ordinal.{0}) : omegaTower 0 α = α := rfl

@[simp, grind =] lemma omegaTower_one (α : Ordinal.{0}) : omegaTower 1 α = Ordinal.omega0 ^ α := rfl

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
private theorem frame_in (a e : (ArithmeticFormula ℕ)) (s t : Finset (ArithmeticFormula ℕ)) :
    (insert a s).erase e ∪ t ⊆ insert a (s.erase e ∪ t) := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with ⟨hne, hxa | hxs⟩ | hxt
  · exact Or.inl hxa
  · exact Or.inr (Or.inl ⟨hne, hxs⟩)
  · exact Or.inr (Or.inr hxt)

/-- Frame subset: pull an `insert` back into the `erase`/`∪`-framed context (canonical → goal),
valid when the head `a` is not the erased formula. -/
private theorem frame_out {a e : (ArithmeticFormula ℕ)} (hne : a ≠ e) (s t : Finset (ArithmeticFormula ℕ)) :
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

**Design note.** Natural (Hessenberg) sum `α ♯ β` is unavailable, so the classic reduction-lemma
bound `α ♯ β` cannot be used. For the **∧/∨** case there is a route that needs no natural sum and
no fresh induction: both connectives are **invertible** (`andInvL/R`, `orInv`), so we invert
*both* premises and close with **two ordinary cuts** at the strictly smaller subformulas. The
resulting bound is `max α β + 1 + 1`, and `max(ω^a, ω^b) + 2 < ω^{max a b + 1}` keeps `cutElimStep`
below `ω^α` with room to spare. (The ∀/∃ case is genuinely different — `∃` is *not* invertible —
and needs the §19.6 induction on the ∃-side; see `cutReduceAll` below.) -/

/-- Reduce a cut on a **conjunction** `a ⋏ b` (its negation `∼a ⋎ ∼b` on the other side), with both
conjuncts of complexity `< c`. Invert the ∧-side (`andInvL/R`) and the ∨-side (`orInv`), then cut
`a` and `b` separately at cut-rank `≤ c`. Towsner **Thm 19.5** (∧/∨ principal reduction). -/
lemma Provable.cutReduceConj {a b : (ArithmeticFormula ℕ)}
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
lemma Provable.cutReduceDisj {a b : (ArithmeticFormula ℕ)}
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
lemma Provable.cutReduceAllAux {φ : ArithmeticSemiformula ℕ 1}
    (hφc : (φ.complexity + 1 : ℕ∞) ≤ c)
    (fam : ∀ n, Provable α c (insert (φ/[nm n]) Γ)) :
    ∀ {Δ : Finset (ArithmeticFormula ℕ)} (d : Derivation Δ), cutRank d ≤ (c : ℕ∞) → (∃⁰ ∼φ) ∈ Δ →
      Provable (α + ordinalBound d + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _
    simp only [Derivation.ordinalBound]
    refine (Provable.axL r v ?_ ?_).mono zero_le (Nat.zero_le c)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro _ _
    simp only [Derivation.ordinalBound]
    refine (Provable.axTrue b r v htrue ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem⟩)
  | @verumR Δ h =>
    intro _ _
    simp only [Derivation.ordinalBound]
    refine (Provable.verumR ?_).mono zero_le (Nat.zero_le c)
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hd : (∃⁰ ∼φ) ∈ Δ'
    · exact (ih hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show Provable (ordinalBound d') c Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_ |>.mono ?_ le_rfl
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self (ordinalBound d') α)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋏ χ₁) ≠ (∃⁰ ∼φ) := by intro h; simp [Wedge.wedge, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcr0 : cutRank d₀ ≤ (c : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcr1 : cutRank d₁ ≤ (c : ℕ∞) := le_trans (le_max_right _ _) hcr
    have P0 : Provable (α + ordinalBound d₀ + 1) c (insert χ₀ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      (ih₀ hcr0 (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    have P1 : Provable (α + ordinalBound d₁ + 1) c (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      (ih₁ hcr1 (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.andI χ₀ χ₁ P0 P1).weakening (show
        insert (χ₀ ⋏ χ₁) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (χ₀ ⋏ χ₁) Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cutAux_bnd α (ordinalBound d₀) (ordinalBound d₁)) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋎ χ₁) ≠ (∃⁰ ∼φ) := by intro h; simp [Vee.vee, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (α + ordinalBound d' + 1) c (insert χ₀ (insert χ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.orI χ₀ χ₁ P).weakening (show
        insert (χ₀ ⋎ χ₁) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (χ₀ ⋎ χ₁) Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cutAux_bnd1 α (ordinalBound d')) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∀⁰ χ') ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
    have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (α + ordinalBound (d' n) + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      fun n => (ih n (le_trans (le_iSup (fun m => cutRank (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    refine ((Provable.allω χ' key).weakening (show
        insert (∀⁰ χ') (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (∀⁰ χ') Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto)).mono (cutAux_bnd_sup α (fun n => ordinalBound (d' n))) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
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
      · have Premise : Provable (α + ordinalBound d' + 1) c (insert ((∼φ)/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          (ih hcr (Finset.mem_insert_of_mem hd)).weakening (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        have hctx : insert ((∼φ)/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)
            = insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) := by rw [hNeg]
        have hcut := Provable.cut (φ/[nm n]) hcutfml famn (Premise.cast hctx)
        refine hcut.mono ?_ le_rfl
        refine add_le_add_left ?_ 1
        exact max_le le_self_add (le_of_eq (add_assoc α (ordinalBound d') 1))
      · have base : Provable (ordinalBound d') c (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
          refine (show Provable (ordinalBound d') c (insert ((∼φ)/[nm n]) Γ₀) from ⟨d', le_rfl, hcr⟩).weakening ?_
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
            (CanonicallyOrderedAdd.le_add_self (ordinalBound d' + 1) α))
    · -- commuting: ∃χ' ≠ ∃∼φ.
      have hhead : (∃⁰ χ') ≠ (∃⁰ ∼φ) := hhd
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P : Provable (α + ordinalBound d' + 1) c (insert (χ'/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ((Provable.exI χ' n P).weakening (show
          insert (∃⁰ χ') (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) ⊆ (insert (∃⁰ χ') Γ₀).erase (∃⁰ ∼φ) ∪ Γ from by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)).mono (cutAux_bnd1 α (ordinalBound d')) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hcξ : (ξ.complexity + 1 : ℕ∞) ≤ c := (le_max_left _ _).trans hcr
    have hcr1 : cutRank d₁ ≤ (c : ℕ∞) := (le_max_left (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cutRank d₂ ≤ (c : ℕ∞) := (le_max_right (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have P1 := (ih₁ hcr1 (Finset.mem_insert_of_mem hmem)).weakening (frame_in ξ (∃⁰ ∼φ) Γ₀ Γ)
    have P2 := (ih₂ hcr2 (Finset.mem_insert_of_mem hmem)).weakening (frame_in (∼ξ) (∃⁰ ∼φ) Γ₀ Γ)
    exact (Provable.cut ξ hcξ P1 P2).mono (cutAux_bnd α (ordinalBound d₁) (ordinalBound d₂)) le_rfl

/-- **Cut reduction, ∀/∃ principal** (Towsner Thm 19.6). A cut on `∀⁰ φ` (complexity `≤ c`) is
eliminated by inverting the ∀-side and inducting on the ∃-side. -/
lemma Provable.cutReduceAll {φ : ArithmeticSemiformula ℕ 1}
    (hφc : (φ.complexity + 1 : ℕ∞) ≤ c)
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
lemma Provable.removeFalseLitAux (b₀ : Bool) {k₀} (r₀ : (ℒₒᵣ).Rel k₀) (v₀)
    (hL : ¬ LitTrue (signedLit b₀ r₀ v₀)) :
    ∀ {Δ : Finset (ArithmeticFormula ℕ)} (d : Derivation Δ), cutRank d ≤ (0 : ℕ∞) →
      signedLit b₀ r₀ v₀ ∈ Δ → Provable (ordinalBound d) 0 (Δ.erase (signedLit b₀ r₀ v₀)) := by
  set L : (ArithmeticFormula ℕ) := signedLit b₀ r₀ v₀ with hLdef
  have hLne : ∀ (g : (ArithmeticFormula ℕ)), g.complexity ≠ 0 → g ≠ L := by
    intro g hg; rw [hLdef]; exact Semiformula.ne_of_ne_complexity (by cases b₀ <;> simp [signedLit, hg])
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _; simp only [Derivation.ordinalBound]
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
    intro _ _; simp only [Derivation.ordinalBound]
    -- the true witness `signedLit b r v ≠ L` (false), so it survives the erase.
    have hne : signedLit b r v ≠ L := fun e => hL (e ▸ htrue)
    exact Provable.axTrue b r v htrue (Finset.mem_erase.mpr ⟨hne, hmem⟩)
  | @verumR Δ h =>
    intro _ _; simp only [Derivation.ordinalBound]
    exact Provable.verumR (Finset.mem_erase.mpr ⟨by rw [hLdef]; exact (lit_ne_verum b₀ r₀ v₀).symm, h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    by_cases hd : L ∈ Δ'
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Provable (ordinalBound d') 0 Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_
      intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋏ χ₁) ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : Provable (ordinalBound d₀) 0 (insert χ₀ (Γ₀.erase L)) :=
      (ih₀ (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : Provable (ordinalBound d₁) 0 (insert χ₁ (Γ₀.erase L)) :=
      (ih₁ (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.andI χ₀ χ₁ P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋎ χ₁) ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (ordinalBound d') 0 (insert χ₀ (insert χ₁ (Γ₀.erase L))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.orI χ₀ χ₁ P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (∀⁰ χ') ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (ordinalBound (d' n)) 0 (insert (χ'/[nm n]) (Γ₀.erase L)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => cutRank (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.allω χ' key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (∃⁰ χ') ≠ L := hLne _ (by simp)
    have hmem0 : L ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (ordinalBound d') 0 (insert (χ'/[nm n]) (Γ₀.erase L)) :=
      (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.exI χ' n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr _; simp only [Derivation.cutRank] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-! ### Atomic cut elimination (Towsner Thm 19.2, the false-atomic inversion content)

The cut formula is atomic (`rel r v`), so it is **never principal in a logical rule** — it only
enters via `axL` or weakening. No truth layer is needed: set sequents dissolve the key case. If an
`axL` clashes exactly on the cut atom `(rel r v, nrel r v)`, then `nrel r v ∈ Γ`, so the *other*
premise (`⊢ nrel r v, Γ`) already proves `Γ` (set idempotence). Every other case is incidental. -/

/-- Induction core: cut a `rel r v` derivation (`d`) against a fixed `nrel r v` derivation (`hNC`). -/
lemma Provable.atomCutAux {k} (r : (ℒₒᵣ).Rel k) (v)
    (hNC : Provable β 0 (insert (Semiformula.nrel r v) Γ)) :
    ∀ {Δ : Finset (ArithmeticFormula ℕ)} (d : Derivation Δ), cutRank d ≤ (0 : ℕ∞) → (Semiformula.rel r v) ∈ Δ →
      Provable (β + ordinalBound d + 1) 0 (Δ.erase (Semiformula.rel r v) ∪ Γ) := by
  intro Δ d
  induction d with
  | @axL Δ k' r' v' hp hn =>
    intro _ _
    simp only [Derivation.ordinalBound]
    have hnn : (Semiformula.nrel r' v' : (ArithmeticFormula ℕ)) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by intro h; exact absurd h (by simp), hn⟩
    by_cases hrel : (Semiformula.rel r' v' : (ArithmeticFormula ℕ)) = Semiformula.rel r v
    · -- the clash's positive member IS the cut atom ⇒ `nrel r v ∈ Γ`-part, use `hNC`
      have hnrv : (Semiformula.nrel r' v' : (ArithmeticFormula ℕ)) = Semiformula.nrel r v := by
        rw [← Semiformula.neg_rel r' v', hrel, Semiformula.neg_rel]
      refine (hNC.weakening ?_).mono ?_ le_rfl
      · intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hxΓ
        · exact Finset.mem_union_left _ (hnrv ▸ hnn)
        · exact Finset.mem_union_right _ hxΓ
      · exact le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos))
    · -- clash avoids the cut atom ⇒ it survives the erase, close by `axL`
      have hpp : (Semiformula.rel r' v' : (ArithmeticFormula ℕ)) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨hrel, hp⟩
      exact (Provable.axL r' v' (Finset.mem_union_left _ hpp)
        (Finset.mem_union_left _ hnn)).mono zero_le le_rfl
  | @axTrue Δ k' b' r' v' htrue' hmem' =>
    intro _ _
    simp only [Derivation.ordinalBound]
    by_cases heq : (signedLit b' r' v' : (ArithmeticFormula ℕ)) = Semiformula.rel r v
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
          · exact absurd (show (Semiformula.nrel r v : (ArithmeticFormula ℕ)) = signedLit false r v by simp [signedLit]) h2
          · exact h3
        exact Finset.mem_union_right _ hxΓ
      · exact le_trans hoN (le_trans le_self_add (le_of_lt (lt_add_of_pos_right _ one_pos)))
    · -- the true literal avoids the cut atom ⇒ survives the erase, close by `axTrue`
      have hll : (signedLit b' r' v' : (ArithmeticFormula ℕ)) ∈ Δ.erase (Semiformula.rel r v) :=
        Finset.mem_erase.mpr ⟨heq, hmem'⟩
      exact (Provable.axTrue b' r' v' htrue' (Finset.mem_union_left _ hll)).mono zero_le le_rfl
  | @verumR Δ h =>
    intro _ _
    simp only [Derivation.ordinalBound]
    have ht : (⊤ : (ArithmeticFormula ℕ)) ∈ Δ.erase (Semiformula.rel r v) :=
      Finset.mem_erase.mpr ⟨by simp, h⟩
    exact (Provable.verumR (Finset.mem_union_left _ ht)).mono zero_le le_rfl
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    by_cases hd : (Semiformula.rel r v) ∈ Δ'
    · exact (ih hcr hd).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxΔ'⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxΔ'⟩
        · exact Or.inr hxΓ)
    · refine (show Provable (ordinalBound d') 0 Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_ |>.mono ?_ le_rfl
      · intro x hx
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩)
      · exact le_trans (CanonicallyOrderedAdd.le_add_self (ordinalBound d') β)
          (le_of_lt (lt_add_of_pos_right _ one_pos))
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋏ χ₁) ≠ (Semiformula.rel r v) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcr0 : cutRank d₀ ≤ (0 : ℕ∞) := le_trans (le_max_left _ _) hcr
    have hcr1 : cutRank d₁ ≤ (0 : ℕ∞) := le_trans (le_max_right _ _) hcr
    have P0 : Provable (β + ordinalBound d₀ + 1) 0 (insert χ₀ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₀ hcr0 (Finset.mem_insert_of_mem hmem0)).weakening (frame_in χ₀ _ Γ₀ Γ)
    have P1 : Provable (β + ordinalBound d₁ + 1) 0 (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih₁ hcr1 (Finset.mem_insert_of_mem hmem0)).weakening (frame_in χ₁ _ Γ₀ Γ)
    exact ((Provable.andI χ₀ χ₁ P0 P1).weakening (frame_out hhead Γ₀ Γ)).mono
      (cutAux_bnd β (ordinalBound d₀) (ordinalBound d₁)) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋎ χ₁) ≠ (Semiformula.rel r v) := by intro h; simp [Vee.vee] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (β + ordinalBound d' + 1) 0 (insert χ₀ (insert χ₁ (Γ₀.erase (Semiformula.rel r v) ∪ Γ))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    exact ((Provable.orI χ₀ χ₁ P).weakening (frame_out hhead Γ₀ Γ)).mono (cutAux_bnd1 β (ordinalBound d')) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∀⁰ χ') ≠ (Semiformula.rel r v) := by intro h; simp [UnivQuantifier.all] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (β + ordinalBound (d' n) + 1) 0
        (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => cutRank (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((Provable.allω χ' key).weakening (frame_out hhead Γ₀ Γ)).mono
      (cutAux_bnd_sup β (fun n => ordinalBound (d' n))) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem
    simp only [Derivation.cutRank] at hcr
    simp only [Derivation.ordinalBound]
    have hhead : (∃⁰ χ') ≠ (Semiformula.rel r v) := by intro h; simp [ExsQuantifier.exs] at h
    have hmem0 : (Semiformula.rel r v) ∈ Γ₀ :=
      (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (β + ordinalBound d' + 1) 0 (insert (χ'/[nm n]) (Γ₀.erase (Semiformula.rel r v) ∪ Γ)) :=
      (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (frame_in (χ'/[nm n]) _ Γ₀ Γ)
    exact ((Provable.exI χ' n P).weakening (frame_out hhead Γ₀ Γ)).mono (cutAux_bnd1 β (ordinalBound d')) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr _
    simp only [Derivation.cutRank] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)

/-- **Atomic cut elimination** (the Thm 19.2 content for the final cut-free step). -/
lemma Provable.atomCut {k} (r : (ℒₒᵣ).Rel k) (v)
    (hC : Provable α 0 (insert (Semiformula.rel r v) Γ))
    (hNC : Provable β 0 (insert (Semiformula.nrel r v) Γ)) :
    Provable (β + α + 1) 0 Γ := by
  rcases hC with ⟨d, ho, hcr⟩
  refine ((Provable.atomCutAux r v hNC d hcr (Finset.mem_insert_self _ _)).weakening
    (show (insert (Semiformula.rel r v) Γ).erase (Semiformula.rel r v) ∪ Γ ⊆ Γ from by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢;
      tauto)).mono ?_ le_rfl
  exact add_le_add_left ((add_le_add_iff_left β).mpr ho) 1

/-- Removing `⊥` from a cut-free derivation, bound-preserving. `⊥` is never introduced by any rule
and is never an `axL`/`verumR` witness, so it is incidental at every step (Towsner Thm 19.2 for the
constant-`⊥` case). -/
lemma Provable.removeFalsumAux : ∀ {Δ : Finset (ArithmeticFormula ℕ)} (d : Derivation Δ), cutRank d ≤ (0 : ℕ∞) →
    (⊥ : (ArithmeticFormula ℕ)) ∈ Δ → Provable (ordinalBound d) 0 (Δ.erase ⊥) := by
  intro Δ d
  induction d with
  | @axL Δ k r v hp hn =>
    intro _ _; simp only [Derivation.ordinalBound]
    exact Provable.axL r v (Finset.mem_erase.mpr ⟨by simp, hp⟩)
      (Finset.mem_erase.mpr ⟨by simp, hn⟩)
  | @axTrue Δ k b r v htrue hmem =>
    intro _ _; simp only [Derivation.ordinalBound]
    exact Provable.axTrue b r v htrue (Finset.mem_erase.mpr ⟨by cases b <;> simp [signedLit], hmem⟩)
  | @verumR Δ h =>
    intro _ _; simp only [Derivation.ordinalBound]
    exact Provable.verumR (Finset.mem_erase.mpr ⟨by simp, h⟩)
  | @weak Δ' Δ d' hsub ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    by_cases hd : (⊥ : (ArithmeticFormula ℕ)) ∈ Δ'
    · exact (ih hcr hd).weakening (Finset.erase_subset_erase _ hsub)
    · refine (show Provable (ordinalBound d') 0 Δ' from ⟨d', le_rfl, hcr⟩).weakening ?_
      intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋏ χ₁) ≠ (⊥ : (ArithmeticFormula ℕ)) := by simp [Wedge.wedge]
    have hmem0 : (⊥ : (ArithmeticFormula ℕ)) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P0 : Provable (ordinalBound d₀) 0 (insert χ₀ (Γ₀.erase ⊥)) :=
      (ih₀ (le_trans (le_max_left _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    have P1 : Provable (ordinalBound d₁) 0 (insert χ₁ (Γ₀.erase ⊥)) :=
      (ih₁ (le_trans (le_max_right _ _) hcr) (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.andI χ₀ χ₁ P0 P1).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (χ₀ ⋎ χ₁) ≠ (⊥ : (ArithmeticFormula ℕ)) := by simp [Vee.vee]
    have hmem0 : (⊥ : (ArithmeticFormula ℕ)) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (ordinalBound d') 0 (insert χ₀ (insert χ₁ (Γ₀.erase ⊥))) :=
      (ih hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.orI χ₀ χ₁ P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @allω Γ₀ χ' d' ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (∀⁰ χ') ≠ (⊥ : (ArithmeticFormula ℕ)) := by simp [UnivQuantifier.all]
    have hmem0 : (⊥ : (ArithmeticFormula ℕ)) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have key : ∀ n, Provable (ordinalBound (d' n)) 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) := fun n =>
      (ih n (le_trans (le_iSup (fun m => cutRank (d' m)) n) hcr)
        (Finset.mem_insert_of_mem hmem0)).weakening (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.allω χ' key).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @exI Γ₀ χ' n d' ih =>
    intro hcr hmem; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have hhead : (∃⁰ χ') ≠ (⊥ : (ArithmeticFormula ℕ)) := by simp [ExsQuantifier.exs]
    have hmem0 : (⊥ : (ArithmeticFormula ℕ)) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have P : Provable (ordinalBound d') 0 (insert (χ'/[nm n]) (Γ₀.erase ⊥)) :=
      (ih hcr (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    exact (Provable.exI χ' n P).weakening (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
      rcases hx with rfl | hx
      · exact ⟨hhead, Or.inl rfl⟩
      · tauto)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr _; simp only [Derivation.cutRank] at hcr
    exact absurd ((le_max_left _ _).trans hcr) (by simp)


/-- Remove a `⊥` from a cut-free sequent. -/
lemma Provable.removeFalsum
    (h : Provable β 0 (insert (⊥ : (ArithmeticFormula ℕ)) Γ)) : Provable β 0 Γ := by
  rcases h with ⟨d, ho, hcr⟩
  refine (Provable.removeFalsumAux d hcr (Finset.mem_insert_self _ _)).weakening ?_ |>.mono ho le_rfl
  intro x hx; simp only [Finset.mem_erase, Finset.mem_insert] at hx; exact (hx.2).resolve_left hx.1

/-- **Principal cut on a rank-`c` formula** — the heart of Thm 19.7. After both premises are
cut-free-at-`c` (bound `ω^α`, `ω^β`), a cut on `ξ` with `complexity ξ = c` is eliminated by the
matching reduction (∧/∨ → `cutReduceConj/Disj`; ∀/∃ → `cutReduceAll`; atomic → `atomCut`;
`⊤`/`⊥` → `removeFalsum`), staying below `ω^(max α β+1)`. -/
lemma Provable.cutElimPrincipal {ξ : (ArithmeticFormula ℕ)}
    (hξeq : ξ.complexity = c)
    (hC : Provable (Ordinal.omega0 ^ α) c (insert ξ Γ))
    (hNC : Provable (Ordinal.omega0 ^ β) c (insert (∼ξ) Γ)) :
    Provable (Ordinal.omega0 ^ (max α β + 1)) c Γ := by
  cases ξ with
  | verum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : Provable (Ordinal.omega0 ^ β) 0 (insert (⊥ : (ArithmeticFormula ℕ)) Γ) := hNC
      refine (Provable.removeFalsum hNC').mono ?_ le_rfl
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_right α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | falsum =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (Provable.removeFalsum hC).mono ?_ le_rfl
      exact Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (le_trans (le_max_left α β) (le_of_lt (lt_add_of_pos_right _ one_pos)))
  | rel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      refine (Provable.atomCut r v hC hNC).mono ?_ le_rfl
      rw [max_comm α β]; exact opow_add_opow_add_one_le β α
  | nrel r v =>
      have hc0 : c = 0 := hξeq.symm
      subst hc0
      have hNC' : Provable (Ordinal.omega0 ^ β) 0 (insert (Semiformula.rel r v) Γ) := hNC
      exact (Provable.atomCut r v hNC' hC).mono (opow_add_opow_add_one_le α β) le_rfl
  | and a b =>
      have hM : max a.complexity b.complexity + 1 = c := hξeq
      have han : a.complexity + 1 ≤ c := by have := le_max_left a.complexity b.complexity; omega
      have hbn : b.complexity + 1 ≤ c := by have := le_max_right a.complexity b.complexity; omega
      exact (Provable.cutReduceConj (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono
        (max_opow_add_two_le α β) le_rfl
  | or a b =>
      have hM : max a.complexity b.complexity + 1 = c := hξeq
      have han : a.complexity + 1 ≤ c := by have := le_max_left a.complexity b.complexity; omega
      have hbn : b.complexity + 1 ≤ c := by have := le_max_right a.complexity b.complexity; omega
      exact (Provable.cutReduceDisj (by exact_mod_cast han) (by exact_mod_cast hbn) hC hNC).mono
        (max_opow_add_two_le α β) le_rfl
  | all φ' =>
      have hφn : φ'.complexity + 1 ≤ c := le_of_eq hξeq
      exact (Provable.cutReduceAll (by exact_mod_cast hφn) hC hNC).mono
        (opow_add_opow_add_one_le α β) le_rfl
  | exs φ' =>
      -- ξ = ∃φ', ∼ξ = ∀∼φ'.  Use `cutReduceAll` with ∀-side = hNC, ∃-side = hC.
      have hφn : (∼φ').complexity + 1 ≤ c := by
        rw [Semiformula.complexity_neg]; exact le_of_eq hξeq
      have hC' : Provable (Ordinal.omega0 ^ α) c (insert (∃⁰ ∼(∼φ')) Γ) := by
        rw [DeMorgan.neg]; exact hC
      refine ((Provable.cutReduceAll (by exact_mod_cast hφn) hNC hC').mono ?_ le_rfl)
      rw [max_comm α β]; exact opow_add_opow_add_one_le β α

/-- The transfinite induction underlying Thm 19.7: a derivation of cut rank `≤ c+1` becomes
cut-free-at-`c` at bound `ω^(ordinalBound d)`. Non-principal rules are reapplied (each `ω^· + small ≤ ω^(·+1)`);
a rank-`< c` cut is kept; a rank-`= c` cut is eliminated by `cutElimPrincipal`. -/
lemma Provable.cutElimStepAux : ∀ {Γ : Finset (ArithmeticFormula ℕ)} (d : Derivation Γ), cutRank d ≤ ((c + 1 : ℕ) : ℕ∞) →
    Provable (Ordinal.omega0 ^ (ordinalBound d)) c Γ := by
  intro Γ d
  induction d with
  | @axL Γ k r v hp hn =>
    intro _; simp only [Derivation.ordinalBound]
    exact (Provable.axL r v hp hn).mono zero_le (Nat.zero_le c)
  | @axTrue Γ k b r v htrue hmem =>
    intro _; simp only [Derivation.ordinalBound]
    exact (Provable.axTrue b r v htrue hmem).mono zero_le (Nat.zero_le c)
  | @verumR Γ h =>
    intro _; simp only [Derivation.ordinalBound]
    exact (Provable.verumR h).mono zero_le (Nat.zero_le c)
  | @weak Δ Γ d' hsub ih =>
    intro hcr; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    exact (ih hcr).weakening hsub
  | @andI Γ₀ χ₀ χ₁ d₀ d₁ ih₀ ih₁ =>
    intro hcr; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    exact (Provable.andI χ₀ χ₁ (ih₀ ((le_max_left _ _).trans hcr))
      (ih₁ ((le_max_right _ _).trans hcr))).mono (max_opow_add_one_le (ordinalBound d₀) (ordinalBound d₁)) le_rfl
  | @orI Γ₀ χ₀ χ₁ d' ih =>
    intro hcr; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    exact (Provable.orI χ₀ χ₁ (ih hcr)).mono (opow_add_one_le' (ordinalBound d')) le_rfl
  | @allω Γ₀ χ' d' ih =>
    intro hcr; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    have IH : ∀ n, Provable (Ordinal.omega0 ^ (ordinalBound (d' n))) c (insert (χ'/[nm n]) Γ₀) :=
      fun n => ih n ((le_iSup (fun m => cutRank (d' m)) n).trans hcr)
    exact (Provable.allω χ' IH).mono (sup_opow_add_one_le (fun n => ordinalBound (d' n))) le_rfl
  | @exI Γ₀ χ' n d' ih =>
    intro hcr; simp only [Derivation.cutRank] at hcr; simp only [Derivation.ordinalBound]
    exact (Provable.exI χ' n (ih hcr)).mono (opow_add_one_le' (ordinalBound d')) le_rfl
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro hcr; simp only [Derivation.cutRank] at hcr
    have hcr1 : cutRank d₁ ≤ ((c + 1 : ℕ) : ℕ∞) :=
      (le_max_left (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have hcr2 : cutRank d₂ ≤ ((c + 1 : ℕ) : ℕ∞) :=
      (le_max_right (cutRank d₁) (cutRank d₂)).trans ((le_max_right _ _).trans hcr)
    have hξc : (ξ.complexity + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := (le_max_left _ _).trans hcr
    have IH1 := ih₁ hcr1
    have IH2 := ih₂ hcr2
    simp only [Derivation.ordinalBound]
    by_cases hkeep : ξ.complexity < c
    · exact (Provable.cut ξ (by exact_mod_cast Nat.succ_le_of_lt hkeep) IH1 IH2).mono
        (max_opow_add_one_le (ordinalBound d₁) (ordinalBound d₂)) le_rfl
    · have hξle : ξ.complexity ≤ c := Nat.le_of_succ_le_succ (by exact_mod_cast hξc)
      have hξeq : ξ.complexity = c := le_antisymm hξle (not_lt.mp hkeep)
      exact Provable.cutElimPrincipal hξeq IH1 IH2

/-- **One level of cut elimination** (Towsner Thm 19.7): reducing the cut rank by one raises the
ordinal bound to `ω^α`. -/
theorem Provable.cutElimStep
    (h : Provable α (c + 1) Γ) : Provable (Ordinal.omega0 ^ α) c Γ := by
  rcases h with ⟨d, ho, hcr⟩
  exact (Provable.cutElimStepAux d hcr).mono
    (Ordinal.opow_le_opow_right Ordinal.omega0_pos ho) le_rfl

/-- **Full cut elimination** (Towsner Thm 19.9): iterate `cutElimStep` `c` times, reaching a
cut-free derivation at ordinal `ω_c^α`. -/
theorem Provable.cutElim
    (h : Provable α c Γ) : Provable (omegaTower c α) 0 Γ := by
  induction c generalizing α with
  | zero => simpa [omegaTower] using h
  | succ c ih => exact ih (Provable.cutElimStep h)

/-! ### `ε₀`-closure of the cut-elimination ordinal

`cutElim` lands at `omegaTower c α = ω_c^α`. The cut-free bound must stay **below `ε₀`** when the
input does — this is exactly what makes Towsner's argument work (`ε₀` is the first fixed point of
`ω ↦ ω^ω`, hence closed under the `c`-fold tower). Pure ordinal facts, no calculus dependence. -/

open scoped Ordinal in
/-- `ε₀` is closed under `ω^·`. -/
@[grind →]
lemma omega0_opow_lt_epsilon0 {a : Ordinal.{0}} (h : a < ε₀) : Ordinal.omega0 ^ a < ε₀ := by
  obtain ⟨n, hn⟩ := Ordinal.lt_epsilon_zero.mp h
  have hstep : Ordinal.omega0 ^ a < (fun b => Ordinal.omega0 ^ b)^[n + 1] 0 := by
    rw [Function.iterate_succ_apply']
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hn
  exact hstep.trans (Ordinal.iterate_omega0_opow_lt_epsilon_zero (n + 1))

open scoped Ordinal in
/-- The full cut-elimination ordinal `ω_c^α` stays below `ε₀` whenever `α < ε₀`. -/
lemma omegaTower_lt_epsilon0 : ∀ (c : ℕ) {α : Ordinal.{0}}, α < ε₀ → omegaTower c α < ε₀
  | 0, _, h => by simpa [omegaTower] using h
  | c + 1, _, h => by
      simpa [omegaTower] using omegaTower_lt_epsilon0 c (omega0_opow_lt_epsilon0 h)

end GoodsteinPA.ZinftyF
