module

public import GoodsteinPA.OperatorZeh.Zef
public import GoodsteinPA.BlueprintAttr

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

variable {α e : ONote} {H : ONote → Prop} {m c : ℕ} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-! ## The bounding read-off — the exit

The witness read-off exit follows the restricted-cut deduction of [Tow20, §17, Theorem 17.1];
the predicate shapes below (`ReadoffShape`/`ReadoffGoal` and their slot-form counterparts) are
specific to this formalization. -/

/-- Sequent shape for the read-off: every member is the target `∃⁰ φ`, an already-bounded
instance of `φ`, or a literal (∀-free). -/
def ReadoffShape (φ : ArithmeticSemiformula ℕ 1) (e : ONote) (m : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ (∃ n ≤ hardy e m, ψ = φ/[nm n]) ∨
    (∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- Read-off conclusion: a bounded true instance of the target, or a true literal
somewhere in the sequent. -/
def ReadoffGoal (φ : ArithmeticSemiformula ℕ 1) (e : ONote) (m : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  (∃ n ≤ hardy e m, atomTrue (φ/[nm n])) ∨
    (∃ ψ ∈ Γ, atomTrue ψ ∧
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- **The bounding read-off.**
From a rank-0 (cut-free) `Zeh` derivation of a `ReadoffShape` sequent whose target matrix
has atomic instances: a witness `n ≤ hardy e m` with `φ/[nm n]` true, or a true literal in
the sequent.  The bound consumes ONLY the judgment's control `e` and stage `m`.

- [Tow20, §17, Theorem 17.1]
-/
theorem readoff_sigma1 {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (dd : Zeh α e H m c Γ) (hc : c = 0) (hshape : ReadoffShape φ e m Γ) : ReadoffGoal φ e m Γ := by
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact Or.inr ⟨_, hp, htrue, ar, r, v, Or.inl rfl⟩
      · refine Or.inr ⟨_, hn, ?_, ar, r, v, Or.inr rfl⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H m c Δ Γ hsub _ ih =>
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub _ ih =>
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @allω α e H m c Γ χ β hβ hβNF hαNF hβH _ _ =>
      rcases hshape (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n, _, h⟩ | ⟨ar, r, v, h | h⟩
      · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
      · obtain ⟨ar, r, v, hrel⟩ := hφinst n
        rw [hrel] at h
        exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | @exI α β e H m c Γ χ n hβ hβNF hαNF hβH hbound _ ih =>
      have hχφ : χ = φ := by
        rcases hshape (∃⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n', _, h⟩ | ⟨ar, r, v, h | h⟩
        · simpa [ExsQuantifier.exs] using h
        · obtain ⟨ar, r, v, hrel⟩ := hφinst n'
          rw [hrel] at h
          exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
      have hφχ : φ = χ := hχφ.symm
      subst hφχ
      have hshape' : ReadoffShape φ e m (insert (φ/[nm n]) Γ) := by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inr (Or.inl ⟨n, hbound, rfl⟩)
        · exact hshape ψ (Finset.mem_insert_of_mem hψΓ)
      rcases ih hc hshape' with h | ⟨ψ, hψ, htrue, hlit⟩
      · exact Or.inl h
      · rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inl ⟨n, hbound, htrue⟩
        · exact Or.inr ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue, hlit⟩
  | @cut α βφ βψ e H m c Γ χ hcompl _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd hcompl (by omega)

/-- **The headline-instantiation read-off**: a rank-0 `Zeh` root deriving the single
per-instance Σ₁ sequent `{∃⁰ φ}` (atomic matrix) yields a numeric witness `≤ hardy e m`. -/
theorem headline_readoff {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (dd : Zeh α e H m 0 {(∃⁰ φ)}) :
    ∃ n ≤ hardy e m, atomTrue (φ/[nm n]) := by
  have hshape : ReadoffShape φ e m {(∃⁰ φ)} := by
    intro ψ hψ
    rw [Finset.mem_singleton] at hψ
    exact Or.inl hψ
  rcases readoff_sigma1 hφinst dd rfl hshape with h | ⟨ψ, hψ, _, ⟨ar, r, v, hlit⟩⟩
  · exact h
  · rw [Finset.mem_singleton] at hψ
    subst hψ
    rcases hlit with h | h <;> exact absurd h (by simp [ExsQuantifier.exs])

attribute [goodstein_blueprint 11 clean "zeh_readoff_exit" "0" 100 headline_readoff
  []
  ["Δ₀ read-off / ∀-free positive Σ₁ witness shape; [Tow20, §17, Theorem 17.1]",
   "witnessing bound f 0; [EW12, Definition 23]",
   "Proven per-instance: no evaluator, no truth predicate, no H-data (Σ₁-definability-of-H risk dissolved)"]
  "The read-off exit: a rank-0 Zeh derivation of the Σ₁ headline shape yields a witness ≤ hardy e m."]
  headline_readoff

/-! ## The read-off exit in the slot calculus (witness ≤ `f 0`)

The slot calculus reaches the same read-off exit as `Zeh`, and — because the slot is the
witness budget — the read-off bound is `f 0` (vs the `Zeh` version's `hardy e m`, the
canonical slot at 0).  Independent of cut-elimination (operates on any rank-0 derivation).

- [Tow20, §17, Theorem 17.1]
-/

/-- Slot-form read-off sequent shape (`hardy e m ⤳ f 0`). -/
def ReadoffShapeF (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ (∃ n ≤ f 0, ψ = φ/[nm n]) ∨
    (∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- Slot-form read-off conclusion. -/
def ReadoffGoalF (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  (∃ n ≤ f 0, atomTrue (φ/[nm n])) ∨
    (∃ ψ ∈ Γ, atomTrue ψ ∧
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- **`readoff_sigma1_Zef`** — the bounding read-off in the slot calculus (port of
`readoff_sigma1`, `hardy e m ⤳ f 0`).  From a rank-0 `Zef` derivation of a `ReadoffShapeF`
sequent: a witness `n ≤ f 0` with `φ/[nm n]` true, or a true literal.  The bound is EXACTLY the
slot at 0. -/
theorem readoff_sigma1_Zef {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (dd : Zef α e H f c Γ) (hc : c = 0) (hshape : ReadoffShapeF φ f Γ) : ReadoffGoalF φ f Γ := by
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact Or.inr ⟨_, hp, htrue, ar, r, v, Or.inl rfl⟩
      · refine Or.inr ⟨_, hn, ?_, ar, r, v, Or.inr rfl⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H f c Δ Γ hsub _ ih =>
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub _ ih =>
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @allω α e H f c Γ χ β hβ hβNF hαNF hβH _ _ =>
      rcases hshape (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n, _, h⟩ | ⟨ar, r, v, h | h⟩
      · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
      · obtain ⟨ar, r, v, hrel⟩ := hφinst n
        rw [hrel] at h
        exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | @exI α β e H f c Γ χ n hβ hβNF hαNF hβH hbound _ ih =>
      have hχφ : χ = φ := by
        rcases hshape (∃⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n', _, h⟩ | ⟨ar, r, v, h | h⟩
        · simpa [ExsQuantifier.exs] using h
        · obtain ⟨ar, r, v, hrel⟩ := hφinst n'
          rw [hrel] at h
          exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
      have hφχ : φ = χ := hχφ.symm
      subst hφχ
      have hshape' : ReadoffShapeF φ f (insert (φ/[nm n]) Γ) := by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inr (Or.inl ⟨n, hbound, rfl⟩)
        · exact hshape ψ (Finset.mem_insert_of_mem hψΓ)
      rcases ih hc hshape' with h | ⟨ψ, hψ, htrue, hlit⟩
      · exact Or.inl h
      · rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inl ⟨n, hbound, htrue⟩
        · exact Or.inr ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue, hlit⟩
  | @cut α βφ βψ e H f c Γ χ hcompl _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd hcompl (by omega)

/-- **`headline_readoff_Zef`** — the slot-calculus exit: a rank-0 `Zef` root deriving `{∃⁰ φ}`
yields a numeric witness `≤ f 0`.  The slot-form of `headline_readoff`; the numeric content of
the whole derivation is carried in `f 0`. -/
theorem headline_readoff_Zef {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (dd : Zef α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n]) := by
  have hshape : ReadoffShapeF φ f {(∃⁰ φ)} := by
    intro ψ hψ
    rw [Finset.mem_singleton] at hψ
    exact Or.inl hψ
  rcases readoff_sigma1_Zef hφinst dd rfl hshape with h | ⟨ψ, hψ, _, ⟨ar, r, v, hlit⟩⟩
  · exact h
  · rw [Finset.mem_singleton] at hψ
    subst hψ
    rcases hlit with h | h <;> exact absurd h (by simp [ExsQuantifier.exs])

end GoodsteinPA.OperatorZeh
