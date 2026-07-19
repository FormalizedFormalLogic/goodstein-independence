module

public import GoodsteinPA.OperatorZeh.Zef
public import GoodsteinPA.BlueprintAttr

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## §3 The bounding read-off — the exit (LOCK §4/§1 verbatim, PROVEN). -/

/-- Sequent shape for the read-off: every member is the target `∃⁰ φ`, an already-bounded
instance of `φ`, or a literal.  (BW87's "positive Σ₁(N)" restriction: ∀-free.) -/
def ReadoffShape (φ : ArithmeticSemiformula ℕ 1) (e : ONote) (m : ℕ) (Γ : Seq) : Prop :=
  ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ (∃ n ≤ hardy e m, ψ = φ/[nm n]) ∨
    (∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- Read-off conclusion: a bounded true instance of the target, or a true literal
somewhere in the sequent (the escape BW87's Bounding Lemma also carries). -/
def ReadoffGoal (φ : ArithmeticSemiformula ℕ 1) (e : ONote) (m : ℕ) (Γ : Seq) : Prop :=
  (∃ n ≤ hardy e m, atomTrue (φ/[nm n])) ∨
    (∃ ψ ∈ Γ, atomTrue ψ ∧
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- **The bounding read-off (Q2), PROVEN — the Buchholz–Wainer Bounding-Lemma analog.**
From a rank-0 (cut-free) `Zeh` derivation of a `ReadoffShape` sequent whose target matrix
has atomic instances: a witness `n ≤ hardy e m` with `φ/[nm n]` true, or a true literal in
the sequent.  The bound consumes ONLY the judgment's control `e` and stage `m`. -/
theorem readoff_sigma1 {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v) :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq},
      Zeh α e H m c Γ → c = 0 → ReadoffShape φ e m Γ → ReadoffGoal φ e m Γ := by
  intro α e H m c Γ dd
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      intro _ _
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact Or.inr ⟨_, hp, htrue, ar, r, v, Or.inl rfl⟩
      · refine Or.inr ⟨_, hn, ?_, ar, r, v, Or.inr rfl⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H m c Δ Γ hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @allω α e H m c Γ χ β hβ hβNF hαNF hβH _ _ =>
      intro _ hshape
      rcases hshape (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n, _, h⟩ | ⟨ar, r, v, h | h⟩
      · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
      · obtain ⟨ar, r, v, hrel⟩ := hφinst n
        rw [hrel] at h
        exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | @exI α β e H m c Γ χ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc hshape
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
      intro hc _
      exact absurd hcompl (by omega)

/-- **The headline-instantiation read-off** — the W5/M2-exit shape: a rank-0 `Zeh` root
deriving the single per-instance Σ₁ sequent `{∃⁰ φ}` (atomic matrix) yields a numeric
witness `≤ hardy e m`. -/
theorem headline_readoff {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    {α e : ONote} {H : ONote → Prop} {m : ℕ}
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
  ["Buchholz–Wainer 1987, Bounding Lemma (∀-free positive Σ₁ shape)",
   "Eguchi–Weiermann arXiv:1205.2879, Lemma 31 (witnessing bound f 0)",
   "SPIKE-Z1-VERDICT.md Q2: proven per-instance, no evaluator, no truth predicate, no H-data (Σ₁-definability-of-H risk dissolved)"]
  "The M2-exit read-off: a rank-0 Zeh derivation of the Σ₁ headline shape yields a witness ≤ hardy e m — the fixed exit every rebuild statement must compose toward (Δ₀-matrix extension is the scheduled laps-8–10 node)."]
  headline_readoff

/-! ## The read-off EXIT in the slot calculus (E–W Lemma 31 EXACTLY: witness ≤ `f 0`)

Closing the end-to-end viability loop: the slot calculus reaches the §3 exit, and — because the
slot IS the witness budget — the read-off bound is `f 0`, matching E–W's Witnessing Lemma (Lemma
31, `max{m_j} ≤ f(0)`) verbatim (vs the `Zeh` version's `hardy e m`, the canonical slot at 0).
Independent of cut-elimination (operates on any rank-0 derivation). -/

/-- Slot-form read-off sequent shape (`hardy e m ⤳ f 0`). -/
def ReadoffShapeF (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Seq) : Prop :=
  ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ (∃ n ≤ f 0, ψ = φ/[nm n]) ∨
    (∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- Slot-form read-off conclusion. -/
def ReadoffGoalF (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Seq) : Prop :=
  (∃ n ≤ f 0, atomTrue (φ/[nm n])) ∨
    (∃ ψ ∈ Γ, atomTrue ψ ∧
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- **`readoff_sigma1_Zef`** — the bounding read-off in the slot calculus (port of
`readoff_sigma1`, `hardy e m ⤳ f 0`).  From a rank-0 `Zef` derivation of a `ReadoffShapeF`
sequent: a witness `n ≤ f 0` with `φ/[nm n]` true, or a true literal.  The bound is EXACTLY the
slot at 0 — E–W Lemma 31. -/
theorem readoff_sigma1_Zef {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef α e H f c Γ → c = 0 → ReadoffShapeF φ f Γ → ReadoffGoalF φ f Γ := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      intro _ _
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact Or.inr ⟨_, hp, htrue, ar, r, v, Or.inl rfl⟩
      · refine Or.inr ⟨_, hn, ?_, ar, r, v, Or.inr rfl⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H f c Δ Γ hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @allω α e H f c Γ χ β hβ hβNF hαNF hβH _ _ =>
      intro _ hshape
      rcases hshape (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n, _, h⟩ | ⟨ar, r, v, h | h⟩
      · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
      · obtain ⟨ar, r, v, hrel⟩ := hφinst n
        rw [hrel] at h
        exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | @exI α β e H f c Γ χ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc hshape
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
      intro hc _
      exact absurd hcompl (by omega)

/-- **`headline_readoff_Zef`** — the slot-calculus exit: a rank-0 `Zef` root deriving `{∃⁰ φ}`
yields a numeric witness `≤ f 0`.  The slot-form of `headline_readoff`; the numeric content of
the whole derivation is carried in `f 0` (E–W). -/
theorem headline_readoff_Zef {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
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
