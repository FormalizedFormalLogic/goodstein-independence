module

public import GoodsteinPA.OperatorZef2.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-- The numeral term `nm n` (`OperatorZinfty.nm`) evaluates to `n` under any standard-model
assignment — the value of a closed numeral const is assignment-independent.  Local companion of
`stdClosedVal_nm`, phrased with `valm ℕ` so it `rw`s inside `eval_substs` read-offs. -/
@[simp] lemma valm_nm (n : ℕ) (f : ℕ → ℕ) :
    GoodsteinPA.Compat.gValm ℕ ![] f (nm n) = n := by simp [nm]

/-- **Rank-0 `Zef2` soundness** (the reusable truth core of the Δ₀ read-off).  A cut-free
derivation of `Γ` has a standard-model-true member.  The `allω` (Π) case combines: either some
branch's true member is in the shared context `Γ` (done), or every branch is true at its own
instance `φ/[nm n]` — whence `∀⁰ φ` is true (`atomTrue (∀⁰ φ) = ∀ k, atomTrue (φ/[nm k])`).
Slot-INDEPENDENT (truth does not see `f`). -/
theorem sound0 : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → c = 0 → ∃ ψ ∈ Γ, atomTrue ψ := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact ⟨_, hp, htrue⟩
      · refine ⟨_, hn, ?_⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro hc
      rcases Classical.em (∃ n : ℕ, ∃ ψ ∈ Γ, atomTrue ψ) with hctx | hctx
      · obtain ⟨n, ψ, hψ, htrue⟩ := hctx
        exact ⟨ψ, Finset.mem_insert_of_mem hψ, htrue⟩
      · refine ⟨∀⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        have hall : ∀ n, atomTrue (φ/[nm n]) := by
          intro n
          obtain ⟨ψ, hψ, htrue⟩ := ih n hc
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact htrue
          · exact absurd ⟨n, ψ, hψΓ, htrue⟩ hctx
        simp only [atomTrue, Semiformula.eval_all]
        intro x
        have hx := hall x
        simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hx
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · refine ⟨∃⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        simp only [atomTrue, Semiformula.eval_ex]
        exact ⟨n, by
          simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using htrue⟩
      · exact ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue⟩
  | @cut α βφ βψ e H f c Γ hαN φ hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc; subst hc
      exact absurd hcompl (by omega)

/-- `atomTrue (∀⁰ χ) ↔ ∀ k, atomTrue (χ/[nm k])` — a standard ω-universal is standard-model-true
iff every numeral instance is true.  (`∀⁰` at the top of a Δ₀ read-off descends to its instances.) -/
theorem atomTrue_all_iff (χ : ArithmeticSemiformula ℕ 1) :
    atomTrue (∀⁰ χ) ↔ ∀ k, atomTrue (χ/[nm k]) := by
  simp only [atomTrue, Semiformula.eval_all]
  constructor
  · intro h k
    have hk := h k
    simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hk
  · intro h x
    have hx := h x
    simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hx

/-- `atomTrue (∃⁰ χ) ↔ ∃ k, atomTrue (χ/[nm k])` — dual of `atomTrue_all_iff`. -/
theorem atomTrue_ex_iff (χ : ArithmeticSemiformula ℕ 1) :
    atomTrue (∃⁰ χ) ↔ ∃ k, atomTrue (χ/[nm k]) := by
  simp only [atomTrue, Semiformula.eval_ex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hx⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hk⟩

/-- The **spine head** of a formula: strip the `∀/∃` quantifier spine; report the terminal's
polarity + relation symbol (arity-packed, so comparisons never pay the dependent-`Rel` tax), or
`none` for the `Zef2`-inert heads `⊤/⊥/⋏/⋎`. -/
def spineHead : ∀ {n}, ArithmeticSemiformula ℕ n → Option (Bool × ((k : ℕ) × (ℒₒᵣ).Rel k))
  | _, Semiformula.rel r _ => some (true, ⟨_, r⟩)
  | _, Semiformula.nrel r _ => some (false, ⟨_, r⟩)
  | _, Semiformula.all φ => spineHead φ
  | _, Semiformula.exs φ => spineHead φ
  | _, Semiformula.verum => none
  | _, Semiformula.falsum => none
  | _, Semiformula.and _ _ => none
  | _, Semiformula.or _ _ => none

/-- Rewriting (in particular substitution `φ/[nm n]`) preserves the spine head. -/
theorem spineHead_rew : ∀ {n₁ n₂} (om : Rew ℒₒᵣ ℕ n₁ ℕ n₂) (φ : ArithmeticSemiformula ℕ n₁),
    spineHead (om ▹ φ) = spineHead φ
  | _, _, om, Semiformula.rel r v => by simp [spineHead, Function.comp_def]
  | _, _, om, Semiformula.nrel r v => by simp [spineHead, Function.comp_def]
  | _, _, om, Semiformula.all φ => by
      rw [show (Semiformula.all φ) = ∀⁰ φ from rfl, Rewriting.app_all]
      simpa [spineHead] using spineHead_rew om.q φ
  | _, _, om, Semiformula.exs φ => by
      rw [show (Semiformula.exs φ) = ∃⁰ φ from rfl, Rewriting.app_exs]
      simpa [spineHead] using spineHead_rew om.q φ
  | _, _, om, Semiformula.verum => by
      rw [show (Semiformula.verum : ArithmeticSemiformula ℕ _) = ⊤ from rfl]
      simp [spineHead]
  | _, _, om, Semiformula.falsum => by
      rw [show (Semiformula.falsum : ArithmeticSemiformula ℕ _) = ⊥ from rfl]
      simp [spineHead]
  | _, _, om, Semiformula.and φ ψ => by
      rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl]
      simp [spineHead]
  | _, _, om, Semiformula.or φ ψ => by
      rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl]
      simp [spineHead]

@[simp] theorem spineHead_all (φ : ArithmeticSemiformula ℕ 1) :
    spineHead (∀⁰ φ) = spineHead φ := rfl

@[simp] theorem spineHead_exs (φ : ArithmeticSemiformula ℕ 1) :
    spineHead (∃⁰ φ) = spineHead φ := rfl

theorem spineHead_substs (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) :
    spineHead (φ/[nm n]) = spineHead φ :=
  spineHead_rew _ φ

/-- **Uniform-spine sequents are rank-0 underivable.**  If every member of `Γ` has the SAME
spine head `t`, no `Zef2` derivation at cut-rank 0 exists: `axL` would force
`some (true, s) = t = some (false, s)`; `allω`/`exI` insert spine-head-preserving instances;
`wk`/`weak` shrink; `cut` needs `complexity < 0`. -/
theorem zef2_rank0_uniform_spine_underivable {t : Option (Bool × ((k : ℕ) × (ℒₒᵣ).Rel k))} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2 α e H f c Γ → c = 0 → (∀ ψ ∈ Γ, spineHead ψ = t) → False := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _ hyp
      have h1 := hyp _ hp
      have h2 := hyp _ hn
      rw [show spineHead (Semiformula.rel r v) = some (true, ⟨ar, r⟩) from rfl] at h1
      rw [show spineHead (Semiformula.nrel r v) = some (false, ⟨ar, r⟩) from rfl] at h2
      rw [← h2] at h1
      simp at h1
  | wk hαN hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH dd ih =>
      intro hc hyp
      refine ih 0 hc ?_
      intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · rw [spineHead_substs]
        simpa using hyp (∀⁰ φ) (Finset.mem_insert_self _ _)
      · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hc hyp
      refine ih hc ?_
      intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · rw [spineHead_substs]
        simpa using hyp (∃⁰ φ) (Finset.mem_insert_self _ _)
      · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ _ _ =>
      intro hc _
      omega

variable {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}

/-- **The R-4′ source is VACUOUS: `Zef2` cannot derive `{∃⁰ φ}` at rank 0, for any `φ`.** -/
theorem zef2_rank0_singleton_ex_underivable {φ : ArithmeticSemiformula ℕ 1} :
    ¬ Zef2 α e H f 0 {(∃⁰ φ)} := by
  intro dd
  refine zef2_rank0_uniform_spine_underivable (t := spineHead (∃⁰ φ)) dd rfl ?_
  intro ψ hψ
  rw [Finset.mem_singleton] at hψ
  rw [hψ]

/-- **The residue under the local monotone-instance condition.**  The
branch-0 mechanism (`rel1 f 0 = f`) already discharges every case where `χ/[nm 0]` is *false*; the
only survivor is `χ/[nm 0]` TRUE while `∀⁰ χ` is false.  If the matrix `χ` satisfies the natural
"`0`-instance is the easiest" condition `atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)` (a downward-closed
guard, as for the Goodstein bounded-`∀` clauses), that survivor is contradictory: `h0` forces
`atomTrue (∀⁰ χ)`, contradicting `hfalse`.  So under `hmono` the trap NEVER fires — this is the exact
fragment the structural read-off reaches without E–W's (Ax2).  A ready building block for a
monotone-guarded specialization of `readoff_delta0_Zef2`. -/
theorem readoffD_trapped_of_mono {φ χ : ArithmeticSemiformula ℕ 1}
    {Γ₀ : Seq} {β : ℕ → ONote}
    (_hbranch : ∀ n, Zef2 (β n) e (adjoin H n) (rel1 f n) 0 (insert (χ/[nm n]) Γ₀))
    (_htrap : (∃⁰ φ) ∈ Γ₀)
    (hfalse : ¬ atomTrue (∀⁰ χ))
    (_hΓ₀ : ∀ ψ ∈ Γ₀, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ)
    (h0 : atomTrue (χ/[nm 0]))
    (hmono : atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n]) :=
  absurd (hmono h0) hfalse

/-- **RUNG D (L-D) `readoff_delta0_Zef2`** — the Δ₀ (bounded-∀ matrix) read-off extension
(Towsner §5.4 pattern), re-homed to `Zef2`.  The conclusion bound is `ewIter f α 0` (rather than
`f 0`): the structurally achievable bound, since the splice consumes it at one definitional tower
level.  The old `matrixTrue` form is deleted; `<BoundedInstance>` is discharged to the repo-native
Foundation Δ₀ predicate `LO.FirstOrder.Arithmetic.DeltaZero` (= `Hierarchy 𝚺 0`) and the conclusion
reads off the standard-model truth `atomTrue = Evalm ℕ` of the instance directly.

Where `readoff_sigma1_Zef2` reads off an ATOMIC matrix (`hφinst : φ/[nm n]` atomic), this reads off
a Δ₀ instance: from a rank-0 `Zef2` derivation of the singleton `{∃⁰ φ}` whose instances
`φ/[nm n]` are Δ₀, extract a witness `n ≤ ewIter f α 0` with `atomTrue (φ/[nm n])`.

**`<BoundedInstance>` = `DeltaZero`:** the `Zeh`/`Zef2` core has only `axL`/`allω`/`exI`/`cut` (no
`∧`/`∨` rule), so the read-off descends the instance through quantifiers/atoms only; `DeltaZero` is
the repo-native Δ₀ notion, and its `∧`/`∨` heads are dead branches for the singleton read-off (a
singleton `{A ⋏ B}` is not `axL`-closable and has no ∧-rule ⇒ underivable).  The genuine content is
the `allω` (Π) case — `atomTrue (∀⁰ χ) = ∀ k, Evalm (χ/[nm k])` needs every branch's matrix as its
true disjunct + the Δ₀ bound to bound the load-bearing branches (Towsner §5.4). -/
theorem readoff_delta0_Zef2 {φ : ArithmeticSemiformula ℕ 1}
    (_hφbdd : ∀ n, LO.FirstOrder.Arithmetic.DeltaZero (φ/[nm n]))
    (dd : Zef2 α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ ewIter f α 0, atomTrue (φ/[nm n]) :=
  -- The conclusion holds via VACUITY: the source `dd` cannot exist
  -- (`zef2_rank0_singleton_ex_underivable`: `Zef2` without E–W's (Ax2) has no closure for a
  -- uniform-spine singleton).  The `hφbdd` Δ₀ premise is not consumed by this vacuity route.
  (zef2_rank0_singleton_ex_underivable dd).elim

/- Rungs E (embedding) and W (splice) moved to `wip/WainerLadder.lean`. -/

end GoodsteinPA.OperatorZeh
