import GoodsteinPA.OperatorZef2
import GoodsteinPA.Compat

/-!
# Route-(c) value gate — the hereditary `Gated` predicate (lap 206, step (2))

Mandated by the DIRECTION lap-206 block, step (2), after the step-(1) gadget probe PASSED
(`wip/ReadoffValueGadgetProbe.lean`).  Design (PENDING_WORK lap-206 top): instead of threading a
SYNTACTIC subformula-closure through the read-off's derivation induction, the invariant tracks a
SEMANTIC hereditary predicate `Gated P V ψ` —

* at a false `∀⁰ χ` member the trap descent needs a **value-gated false branch**
  `∃ k ≤ P V, ¬ atomTrue (χ/[nm k])` (E–W's rule-side branch gate, reconstructed semantically);
* every quantifier instance stays `Gated` at the bumped budget `max V k` (so the invariant
  survives `allω`/vacuous-`exI` insertions), and connective constituents stay `Gated` at the
  same budget (`andI`/`orI` insertions).

The syntactic work (φ's `Hierarchy 𝚺` ball-shapes + the subterm value bound `P_φ`) then
discharges `Gated` ONCE, at the pipeline root, for the concrete `goodsteinBodyE` instances —
NOT inside the derivation induction.  This file defines `Gated` and banks its two derivation-side
laws: budget monotonicity (`Gated_mono`) and the accessor lemmas the induction's cases consume.

Wip-only ruling input; `Gated` is internal proof machinery (no ratified-statement contact).
-/

namespace GoodsteinPA.ReadoffValueGate

open LO LO.FirstOrder
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty

/-- **The hereditary value gate.**  `Gated P V ψ` says: along any refutation descent through
`ψ`'s quantifier/connective structure, false `∀⁰`-heads admit a false branch of index `≤ P` of
the running budget, where the budget starts at `V` and absorbs every instantiation index.
Atoms/⊤/⊥ are vacuously gated (the read-off's leaf cases never descend). -/
def Gated (P : ℕ → ℕ) : ℕ → Form → Prop
  | _, Semiformula.rel _ _ => True
  | _, Semiformula.nrel _ _ => True
  | _, Semiformula.verum => True
  | _, Semiformula.falsum => True
  | V, Semiformula.and χ₁ χ₂ => Gated P V χ₁ ∧ Gated P V χ₂
  | V, Semiformula.or χ₁ χ₂ => Gated P V χ₁ ∧ Gated P V χ₂
  | V, Semiformula.all χ =>
      (¬ atomTrue (Semiformula.all χ) → ∃ k, k ≤ P V ∧ ¬ atomTrue (χ/[nm k])) ∧
      ∀ k, Gated P (max V k) (χ/[nm k])
  | V, Semiformula.exs χ => ∀ n, Gated P (max V n) (χ/[nm n])
termination_by _ φ => φ.complexity
decreasing_by
  all_goals simp [Semiformula.complexity_rew]

/-! ## Accessors — the shapes the read-off induction's cases consume -/

theorem Gated_and_iff {P : ℕ → ℕ} {V : ℕ} {χ₁ χ₂ : Form} :
    Gated P V (χ₁ ⋏ χ₂) ↔ Gated P V χ₁ ∧ Gated P V χ₂ := by
  rw [show (χ₁ ⋏ χ₂) = Semiformula.and χ₁ χ₂ from rfl, Gated]

theorem Gated_or_iff {P : ℕ → ℕ} {V : ℕ} {χ₁ χ₂ : Form} :
    Gated P V (χ₁ ⋎ χ₂) ↔ Gated P V χ₁ ∧ Gated P V χ₂ := by
  rw [show (χ₁ ⋎ χ₂) = Semiformula.or χ₁ χ₂ from rfl, Gated]

theorem Gated_all_iff {P : ℕ → ℕ} {V : ℕ} {χ : SyntacticSemiformula ℒₒᵣ 1} :
    Gated P V (∀⁰ χ) ↔
      ((¬ atomTrue (∀⁰ χ) → ∃ k, k ≤ P V ∧ ¬ atomTrue (χ/[nm k])) ∧
        ∀ k, Gated P (max V k) (χ/[nm k])) := by
  rw [show (∀⁰ χ) = Semiformula.all χ from rfl, Gated]

theorem Gated_exs_iff {P : ℕ → ℕ} {V : ℕ} {χ : SyntacticSemiformula ℒₒᵣ 1} :
    Gated P V (∃⁰ χ) ↔ ∀ n, Gated P (max V n) (χ/[nm n]) := by
  rw [show (∃⁰ χ) = Semiformula.exs χ from rfl, Gated]

/-! ## Budget monotonicity — old members stay gated when the budget bumps -/

theorem Gated_mono {P : ℕ → ℕ} (hP : Monotone P) :
    ∀ (φ : Form) (V V' : ℕ), V ≤ V' → Gated P V φ → Gated P V' φ
  | Semiformula.rel _ _, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.nrel _ _, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.verum, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.falsum, _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.and χ₁ χ₂, V, V', h, hg => by
      rw [Gated] at hg ⊢
      exact ⟨Gated_mono hP χ₁ V V' h hg.1, Gated_mono hP χ₂ V V' h hg.2⟩
  | Semiformula.or χ₁ χ₂, V, V', h, hg => by
      rw [Gated] at hg ⊢
      exact ⟨Gated_mono hP χ₁ V V' h hg.1, Gated_mono hP χ₂ V V' h hg.2⟩
  | Semiformula.all χ, V, V', h, hg => by
      rw [Gated] at hg ⊢
      refine ⟨fun hf => ?_, fun k => ?_⟩
      · obtain ⟨k, hk, hkf⟩ := hg.1 hf
        exact ⟨k, le_trans hk (hP h), hkf⟩
      · exact Gated_mono hP (χ/[nm k]) (max V k) (max V' k)
          (max_le_max h le_rfl) (hg.2 k)
  | Semiformula.exs χ, V, V', h, hg => by
      rw [Gated] at hg ⊢
      intro n
      exact Gated_mono hP (χ/[nm n]) (max V n) (max V' n)
        (max_le_max h le_rfl) (hg n)
termination_by φ _ _ _ _ => φ.complexity
decreasing_by
  all_goals simp [Semiformula.complexity_rew]

/-! ## The term-value frame `tvB` — standard-model values with all variables at `B`

The root discharge's `P_φ` is built from `tvB` over φ's guard terms.  `tvB t B` dominates the
value of every numeral instance of `t` whose numerals are `≤ B` (monotonicity + `val_rew`). -/

/-- Standard-model `ℒₒᵣ` term values are monotone in both environments (0/1/+/· are monotone). -/
theorem valm_mono : ∀ {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) {e e' : Fin m → ℕ} {ε ε' : ℕ → ℕ},
    (∀ i, e i ≤ e' i) → (∀ x, ε x ≤ ε' x) →
    GoodsteinPA.Compat.gValm ℕ e ε t ≤ GoodsteinPA.Compat.gValm ℕ e' ε' t := by
  intro m t
  induction t with
  | bvar x => intro e e' ε ε' he _; simpa using he x
  | fvar x => intro e e' ε ε' _ hε; simpa using hε x
  | func f v ih =>
      intro e e' ε ε' he hε
      cases f with
      | zero =>
          show GoodsteinPA.Compat.gValm ℕ e ε (Semiterm.func Language.Zero.zero v)
            ≤ GoodsteinPA.Compat.gValm ℕ e' ε' (Semiterm.func Language.Zero.zero v)
          simp
      | one =>
          show GoodsteinPA.Compat.gValm ℕ e ε (Semiterm.func Language.One.one v)
            ≤ GoodsteinPA.Compat.gValm ℕ e' ε' (Semiterm.func Language.One.one v)
          simp
      | add =>
          show GoodsteinPA.Compat.gValm ℕ e ε (Semiterm.func Language.Add.add v)
            ≤ GoodsteinPA.Compat.gValm ℕ e' ε' (Semiterm.func Language.Add.add v)
          simp only [Semiterm.val_func, Structure.add_eq_of_lang]
          have h0 := ih 0 he hε
          have h1 := ih 1 he hε
          exact Nat.add_le_add h0 h1
      | mul =>
          show GoodsteinPA.Compat.gValm ℕ e ε (Semiterm.func Language.Mul.mul v)
            ≤ GoodsteinPA.Compat.gValm ℕ e' ε' (Semiterm.func Language.Mul.mul v)
          simp only [Semiterm.val_func, Structure.mul_eq_of_lang]
          have h0 := ih 0 he hε
          have h1 := ih 1 he hε
          exact Nat.mul_le_mul h0 h1

/-- `tvB t B` — the value of `t` with every bounded variable at `B` and every free name at `0`. -/
noncomputable def tvB {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) (B : ℕ) : ℕ :=
  GoodsteinPA.Compat.gValm ℕ (fun _ => B) (fun _ => 0) t

theorem tvB_mono {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) : Monotone (tvB t) :=
  fun _ _ h => valm_mono t (fun _ => h) (fun _ => le_rfl)

/-- `bShift` does not change `tvB` (the constant environment absorbs the shift). -/
theorem tvB_bShift {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) (B : ℕ) :
    tvB (Rew.bShift t) B = tvB t B := by
  simp [tvB, Semiterm.val_bShift']

/-! ## The guard-value bound `gvb` — the root discharge's `P_φ` shape

`gvb ψ B` = the max standard-model value of any argument term of any atomic subformula of `ψ`,
with every bounded variable at `B` (names at `0`).  Ball guards `x < t` are atoms, so `gvb`
dominates every guard value; it is monotone in `B` and contracts under numeral substitution
(`gvb (χ/[nm k]) B ≤ gvb χ (max B k)`), which is exactly what the master induction threads. -/

noncomputable def gvb : ∀ {m : ℕ}, SyntacticSemiformula ℒₒᵣ m → ℕ → ℕ
  | _, Semiformula.rel _ v, B => Finset.univ.sup fun i => tvB (v i) B
  | _, Semiformula.nrel _ v, B => Finset.univ.sup fun i => tvB (v i) B
  | _, Semiformula.verum, _ => 0
  | _, Semiformula.falsum, _ => 0
  | _, Semiformula.and χ₁ χ₂, B => max (gvb χ₁ B) (gvb χ₂ B)
  | _, Semiformula.or χ₁ χ₂, B => max (gvb χ₁ B) (gvb χ₂ B)
  | _, Semiformula.all χ, B => gvb χ B
  | _, Semiformula.exs χ, B => gvb χ B

theorem gvb_mono : ∀ {m : ℕ} (ψ : SyntacticSemiformula ℒₒᵣ m), Monotone (gvb ψ) := by
  intro m ψ
  induction ψ with
  | rel r v => exact fun B B' h => Finset.sup_mono_fun fun i _ => tvB_mono (v i) h
  | nrel r v => exact fun B B' h => Finset.sup_mono_fun fun i _ => tvB_mono (v i) h
  | verum => exact fun _ _ _ => le_rfl
  | falsum => exact fun _ _ _ => le_rfl
  | and χ₁ χ₂ ih₁ ih₂ => exact fun B B' h => max_le_max (ih₁ h) (ih₂ h)
  | or χ₁ χ₂ ih₁ ih₂ => exact fun B B' h => max_le_max (ih₁ h) (ih₂ h)
  | all χ ih => exact ih
  | exs χ ih => exact ih

/-- Terms contract under a numeral-or-variable rewrite: if `ω` maps every bounded variable to a
term of frame value `≤ max B K` and fixes names, then `tvB (ω t) B ≤ tvB t (max B K)`. -/
theorem tvB_rew_le {K : ℕ} {n₁ n₂ : ℕ} (t : Semiterm ℒₒᵣ ℕ n₁) (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (hb : ∀ i B, tvB (ω #i) B ≤ max B K) (hf : ∀ x, ω &x = &x) (B : ℕ) :
    tvB (ω t) B ≤ tvB t (max B K) := by
  have h1 : tvB (ω t) B
      = GoodsteinPA.Compat.gValm ℕ (fun i => tvB (ω #i) B) (fun x => tvB (ω &x) B) t :=
    Semiterm.val_rew ω t
  rw [h1]
  apply valm_mono t
  · intro i
    exact hb i B
  · intro x
    rw [hf x]
    simp [tvB]

/-- The rewrite class is stable under the binder lift `ω.q`. -/
theorem q_class {K : ℕ} {n₁ n₂ : ℕ} (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂)
    (hb : ∀ i B, tvB (ω #i) B ≤ max B K) (hf : ∀ x, ω &x = &x) :
    (∀ i B, tvB (ω.q #i) B ≤ max B K) ∧ (∀ x, ω.q &x = &x) := by
  constructor
  · intro i B
    cases i using Fin.cases with
    | zero => simp [tvB]
    | succ j => rw [Rew.q_bvar_succ, tvB_bShift]; exact hb j B
  · intro x
    rw [Rew.q_fvar, hf x]
    rfl

/-- **The substitution law**: `gvb` contracts under a numeral-or-variable rewrite. -/
theorem gvb_rew_le {K : ℕ} :
    ∀ {n₁ : ℕ} (χ : SyntacticSemiformula ℒₒᵣ n₁) {n₂ : ℕ} (ω : Rew ℒₒᵣ ℕ n₁ ℕ n₂),
      (∀ i B, tvB (ω #i) B ≤ max B K) → (∀ x, ω &x = &x) →
      ∀ B, gvb (ω ▹ χ) B ≤ gvb χ (max B K) := by
  intro n₁ χ
  induction χ with
  | rel r v =>
      intro n₂ ω hb hf B
      rw [Semiformula.rew_rel]
      simp only [gvb]
      exact Finset.sup_le fun i _ =>
        le_trans (tvB_rew_le (v i) ω hb hf B)
          (Finset.le_sup (f := fun i => tvB (v i) (max B K)) (Finset.mem_univ i))
  | nrel r v =>
      intro n₂ ω hb hf B
      rw [Semiformula.rew_nrel]
      simp only [gvb]
      exact Finset.sup_le fun i _ =>
        le_trans (tvB_rew_le (v i) ω hb hf B)
          (Finset.le_sup (f := fun i => tvB (v i) (max B K)) (Finset.mem_univ i))
  | verum =>
      intro n₂ ω _ _ B
      rw [show (ω ▹ (Semiformula.verum : SyntacticSemiformula ℒₒᵣ _))
        = Semiformula.verum from rfl]
      simp [gvb]
  | falsum =>
      intro n₂ ω _ _ B
      rw [show (ω ▹ (Semiformula.falsum : SyntacticSemiformula ℒₒᵣ _))
        = Semiformula.falsum from rfl]
      simp [gvb]
  | and χ₁ χ₂ ih₁ ih₂ =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.and χ₁ χ₂)
        = Semiformula.and (ω ▹ χ₁) (ω ▹ χ₂) from rfl]
      simp only [gvb]
      exact max_le_max (ih₁ ω hb hf B) (ih₂ ω hb hf B)
  | or χ₁ χ₂ ih₁ ih₂ =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.or χ₁ χ₂)
        = Semiformula.or (ω ▹ χ₁) (ω ▹ χ₂) from rfl]
      simp only [gvb]
      exact max_le_max (ih₁ ω hb hf B) (ih₂ ω hb hf B)
  | all χ ih =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.all χ) = Semiformula.all (ω.q ▹ χ) from rfl]
      simp only [gvb]
      obtain ⟨hb', hf'⟩ := q_class ω hb hf
      exact ih ω.q hb' hf' B
  | exs χ ih =>
      intro n₂ ω hb hf B
      rw [show (ω ▹ Semiformula.exs χ) = Semiformula.exs (ω.q ▹ χ) from rfl]
      simp only [gvb]
      obtain ⟨hb', hf'⟩ := q_class ω hb hf
      exact ih ω.q hb' hf' B

/-- Numerals sit inside the frame: `tvB (nm k) B = k`. -/
theorem tvB_nm (k B : ℕ) : tvB (nm k) B = k := by
  have he : (fun _ => B : Fin 0 → ℕ) = ![] := by funext i; exact i.elim0
  simp only [tvB, he]
  exact valm_nm k (fun _ => 0)

/-- **The numeral-instance law** — the exact shape the master induction threads at `allω`/`exs`
descents: instantiating the head variable by `nm k` contracts `gvb` into the `max B k` frame. -/
theorem gvb_substs_le {χ : SyntacticSemiformula ℒₒᵣ 1} (k B : ℕ) :
    gvb (χ/[nm k]) B ≤ gvb χ (max B k) := by
  have hb : ∀ (i : Fin 1) B', tvB ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #i) B' ≤ max B' k := by
    intro i B'
    have h0 : (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #i = nm k := by
      simp
    rw [h0, tvB_nm]
    exact le_max_right _ _
  have hf : ∀ x, (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) &x = &x := by
    intro x; simp
  exact gvb_rew_le (K := k) χ (Rew.subst ![nm k]) hb hf B

/-- **The one-binder numeral-instance law** (lap 208, 2b item (b)) — the `.q`-lifted form:
substituting `nm k` for the OUTER variable under one residual binder still contracts `gvb`
into the `max B k` frame.  This is what contracts the pipeline's per-`m` value budget
`P_m = gvb (goodsteinBodyE/[nm m])` into ONE fixed `P* = gvb goodsteinBodyE` with a `max m`
argument shift — the m-uniformization of the read-off bound. -/
theorem gvb_substs_q_le {χ : SyntacticSemiformula ℒₒᵣ 2} (k B : ℕ) :
    gvb ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]).q ▹ χ) B ≤ gvb χ (max B k) := by
  have hb : ∀ (i : Fin 1) B', tvB ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #i) B' ≤ max B' k := by
    intro i B'
    have h0 : (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #i = nm k := by
      simp
    rw [h0, tvB_nm]
    exact le_max_right _ _
  have hf : ∀ x, (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) &x = &x := by
    intro x; simp
  obtain ⟨hb', hf'⟩ := q_class (K := k) (Rew.subst ![nm k]) hb hf
  exact gvb_rew_le (K := k) χ (Rew.subst ![nm k]).q hb' hf' B

/-! ## The root discharge `gated_of_sigma1` (lap 207, DIRECTION lap-206 block item 1)

`Hierarchy 𝚺 1 ψ` supplies the ball shape at every `∀`-head (the Foundation `Hierarchy`
constructors `all`/`pi`/`dummy_sigma` are polarity/level-blocked at `𝚺 1`), and the coupled
value hypothesis `∀ B, gvb ψ B ≤ P (max V B)` self-threads through numeral instantiation via
`gvb_substs_le`.  Together they discharge `Gated P V ψ` — the ONE root obligation the
V-threaded read-off invariant needs at the pipeline root. -/

/-- At arity 1, a `Positive` term has no bounded variables, so its value ignores the bounded
environment. -/
theorem valm_env_irrel_of_positive : ∀ (t : Semiterm ℒₒᵣ ℕ 1), t.Positive →
    ∀ (e e' : Fin 1 → ℕ) (ε : ℕ → ℕ),
      GoodsteinPA.Compat.gValm ℕ e ε t = GoodsteinPA.Compat.gValm ℕ e' ε t := by
  intro t
  induction t with
  | bvar x =>
      intro hpos
      rcases Fin.eq_zero x with rfl
      simp at hpos
  | fvar x => intro _ e e' ε; simp
  | func f v ih =>
      intro hpos e e' ε
      have hv : ∀ i, (v i).Positive := by simpa using hpos
      simp only [Semiterm.val_func]
      congr 1
      funext i
      exact ih i (hv i) e e' ε

/-- **The gate extraction** (probe-verified): a false numeral instance of a ball
`“x. x < !!t” 🡒 φ` pins the instance index strictly below the guard value `tvB t 0`
(env-independent by positivity) and falsifies the body instance. -/
theorem gate_extract {t : Semiterm ℒₒᵣ ℕ 1} (hpos : t.Positive)
    {φ : SyntacticSemiformula ℒₒᵣ 1} {k : ℕ}
    (h : ¬ atomTrue (((“x. x < !!t” : SyntacticSemiformula ℒₒᵣ 1) 🡒 φ)/[nm k])) :
    k < tvB t 0 ∧ ¬ atomTrue (φ/[nm k]) := by
  simp [atomTrue, Semiformula.imp_eq, Semiformula.Operator.lt_def] at h
  refine ⟨?_, by
    simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton]
      using h.2⟩
  have he : (fun _ => (0:ℕ) : Fin 0 → ℕ) = ![] := by funext i; exact i.elim0
  have h1 : Semiterm.val (fun _ => 0) (fun _ => 0)
      ((Rew.subst ![nm k]) t) = GoodsteinPA.Compat.gValm ℕ ![k] (fun _ => 0) t := by
    rw [Semiterm.val_rew]
    congr 1
    funext i
    rcases Fin.eq_zero i with rfl
    show Semiterm.val (fun _ => 0) (fun _ => 0)
      ((Rew.subst ![nm k]) #0) = k
    rw [show (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm k]) #0 = nm k by simp, he]
    exact valm_nm k _
  rw [h1, valm_env_irrel_of_positive t hpos ![k] (fun _ => 0)] at h
  exact h.1

/-- The ball body's syntactic normal form (probe-verified): the guard is a genuine `<`-relation
atom, the implication is `∼guard ⋎ φ`. -/
theorem ball_body_eq (t : Semiterm ℒₒᵣ ℕ 1) (φ : SyntacticSemiformula ℒₒᵣ 1) :
    ((“x. x < !!t” : SyntacticSemiformula ℒₒᵣ 1) 🡒 φ)
      = (Semiformula.nrel Language.LT.lt ![#0, t] ⋎ φ) := by
  simp [Semiformula.imp_eq, Semiformula.Operator.lt_def]

/-- The guard value sits inside the ball body's `gvb`. -/
theorem tvB_le_gvb_ball (t : Semiterm ℒₒᵣ ℕ 1) (φ : SyntacticSemiformula ℒₒᵣ 1) (B : ℕ) :
    tvB t B ≤ gvb ((“x. x < !!t” : SyntacticSemiformula ℒₒᵣ 1) 🡒 φ) B := by
  rw [ball_body_eq]
  refine le_trans ?_ (le_max_left _ _)
  exact Finset.le_sup (f := fun i => tvB (![#0, t] i) B) (Finset.mem_univ 1)

/-- **Σ₁ `all`-head inversion**: at `𝚺 1`, a `∀`-head can only be a ball
(`all`/`pi` are 𝚷-constructors; `dummy_sigma` needs level ≥ 2). -/
theorem sigma1_all_inv {χ : SyntacticSemiformula ℒₒᵣ 1}
    (H : Arithmetic.Hierarchy 𝚺 1 (Semiformula.all χ)) :
    ∃ (t : Semiterm ℒₒᵣ ℕ 1) (φ : SyntacticSemiformula ℒₒᵣ 1),
      t.Positive ∧ χ = ((“x. x < !!t” : SyntacticSemiformula ℒₒᵣ 1) 🡒 φ)
        ∧ Arithmetic.Hierarchy 𝚺 1 φ := by
  generalize hq : Semiformula.all χ = ψ at H
  cases H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hq
  case ball t hpos hp =>
    exact ⟨t, _, hpos, Semiformula.all.inj hq, hp⟩

/-- **THE ROOT DISCHARGE** — `Hierarchy 𝚺 1` plus the coupled guard-value bound gives `Gated`.
At the pipeline root instantiate `P := fun B => gvb φ_root (max V_root B)` (monotone by
`gvb_mono`, and the hypothesis is `gvb_mono` + max-algebra). -/
theorem gated_of_sigma1 {P : ℕ → ℕ} (hP : Monotone P) :
    ∀ (ψ : Form), Arithmetic.Hierarchy 𝚺 1 ψ →
      ∀ V : ℕ, (∀ B, gvb ψ B ≤ P (max V B)) → Gated P V ψ
  | Semiformula.rel _ _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.nrel _ _, _, _, _ => by rw [Gated]; trivial
  | Semiformula.verum, _, _, _ => by rw [Gated]; trivial
  | Semiformula.falsum, _, _, _ => by rw [Gated]; trivial
  | Semiformula.and χ₁ χ₂, H, V, hgv => by
      rw [show (Semiformula.and χ₁ χ₂) = (χ₁ ⋏ χ₂) from rfl] at H
      rw [Gated]
      have h := Arithmetic.Hierarchy.and_iff.mp H
      exact ⟨gated_of_sigma1 hP χ₁ h.1 V
          (fun B => le_trans (le_max_left _ _) (hgv B)),
        gated_of_sigma1 hP χ₂ h.2 V
          (fun B => le_trans (le_max_right _ _) (hgv B))⟩
  | Semiformula.or χ₁ χ₂, H, V, hgv => by
      rw [show (Semiformula.or χ₁ χ₂) = (χ₁ ⋎ χ₂) from rfl] at H
      rw [Gated]
      have h := Arithmetic.Hierarchy.or_iff.mp H
      exact ⟨gated_of_sigma1 hP χ₁ h.1 V
          (fun B => le_trans (le_max_left _ _) (hgv B)),
        gated_of_sigma1 hP χ₂ h.2 V
          (fun B => le_trans (le_max_right _ _) (hgv B))⟩
  | Semiformula.exs χ, H, V, hgv => by
      rw [Gated]
      intro n
      have hχ : Arithmetic.Hierarchy 𝚺 1 χ := Arithmetic.Hierarchy.sigma_of_sigma_ex H
      refine gated_of_sigma1 hP (χ/[nm n]) (hχ.rew _) (max V n) (fun B => ?_)
      calc gvb (χ/[nm n]) B ≤ gvb χ (max B n) := gvb_substs_le n B
        _ = gvb (Semiformula.exs χ) (max B n) := rfl
        _ ≤ P (max V (max B n)) := hgv (max B n)
        _ ≤ P (max (max V n) B) := hP (by omega)
  | Semiformula.all χ, H, V, hgv => by
      obtain ⟨t, φ, hpos, hχeq, hφ⟩ := sigma1_all_inv H
      rw [Gated]
      constructor
      · intro hf
        have hnall : ¬ ∀ k, atomTrue (χ/[nm k]) :=
          fun h => hf ((atomTrue_all_iff χ).mpr h)
        obtain ⟨k, hk⟩ := not_forall.mp hnall
        refine ⟨k, ?_, hk⟩
        have hlt : k < tvB t 0 := by
          rw [hχeq] at hk
          exact (gate_extract hpos hk).1
        have hle : tvB t 0 ≤ P V := by
          have h1 : tvB t 0 ≤ gvb χ 0 := hχeq ▸ tvB_le_gvb_ball t φ 0
          have h2 : gvb (Semiformula.all χ) 0 ≤ P (max V 0) := hgv 0
          calc tvB t 0 ≤ gvb χ 0 := h1
            _ = gvb (Semiformula.all χ) 0 := rfl
            _ ≤ P (max V 0) := h2
            _ = P V := by rw [Nat.max_zero]
        omega
      · intro k
        have hχH : Arithmetic.Hierarchy 𝚺 1 χ := by
          rw [hχeq]
          simpa [Arithmetic.Hierarchy.imp_iff, Semiformula.Operator.lt_def] using hφ
        refine gated_of_sigma1 hP (χ/[nm k]) (hχH.rew _) (max V k) (fun B => ?_)
        calc gvb (χ/[nm k]) B ≤ gvb χ (max B k) := gvb_substs_le k B
          _ = gvb (Semiformula.all χ) (max B k) := rfl
          _ ≤ P (max V (max B k)) := hgv (max B k)
          _ ≤ P (max (max V k) B) := hP (by omega)
termination_by ψ _ _ _ => ψ.complexity
decreasing_by
  all_goals simp [Semiformula.complexity_rew]

/-- **The certificate-exists form** — at the pipeline root the coupled hypothesis is
self-discharging with `P := fun B => gvb ψ (max V B)`. -/
theorem gated_root_of_sigma1 (ψ : Form) (h : Arithmetic.Hierarchy 𝚺 1 ψ) (V : ℕ) :
    ∃ P : ℕ → ℕ, Monotone P ∧ Gated P V ψ := by
  refine ⟨fun B => gvb ψ (max V B), fun _ _ hb => gvb_mono ψ (max_le_max le_rfl hb), ?_⟩
  refine gated_of_sigma1 (fun _ _ hb => gvb_mono ψ (max_le_max le_rfl hb)) ψ h V (fun B => ?_)
  exact gvb_mono ψ (le_trans (le_max_right V B) (le_max_right V (max V B)))

/-! ## `P*`-domination brick (lap 210, SERIES-4 S-2) — `gvb` of a FIXED formula is dominated by
finitely many iterates of ANY engine closed under successor/add/mul.  Abstract in the engine `G`
because the wip modules cannot import each other: instantiate at assembly with `Gexp = hardy ω²`
(closure facts `succ_le_Gexp`/`add_le_Gexp_max`/`mul_le_Gexp_max`, `wip/E1EmbeddingGrind.lean`),
whose iterates are padded-Hardy-dominated by `hardy_Wpow_iter_dom_pad`
(`wip/HardyMajorization.lean`). -/

section IterDom

variable {G : ℕ → ℕ}

/-- Iterates inflate, from the successor closure. -/
theorem le_iter_of_succ (hG_succ : ∀ x, x + 1 ≤ G x) : ∀ (c x : ℕ), x ≤ G^[c] x
  | 0, _ => le_rfl
  | (c + 1), x => by
      rw [Function.iterate_succ_apply']
      have h1 := le_iter_of_succ hG_succ c x
      have h2 := hG_succ (G^[c] x)
      omega

/-- Iterate-count monotonicity, from successor closure + monotonicity. -/
theorem iter_le_iter_of_succ (hG_mono : Monotone G) (hG_succ : ∀ x, x + 1 ≤ G x)
    {c c' : ℕ} (h : c ≤ c') (x : ℕ) : G^[c] x ≤ G^[c'] x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact hG_mono.iterate c (le_iter_of_succ hG_succ k x)

/-- Every ℒₒᵣ term value `tvB t` is bounded by finitely many `G`-iterates of the frame `B`
(names sit at `0`; `add`/`mul` each cost one iterate). -/
theorem tvB_le_iter (hG_mono : Monotone G) (hG_succ : ∀ x, x + 1 ≤ G x)
    (hG_add : ∀ a b, a + b ≤ G (max a b)) (hG_mul : ∀ a b, a * b ≤ G (max a b))
    {m : ℕ} (t : Semiterm ℒₒᵣ ℕ m) : ∃ c, ∀ B, tvB t B ≤ G^[c] B := by
  induction t with
  | bvar x => exact ⟨0, fun B => le_of_eq (by simp [tvB])⟩
  | fvar x => exact ⟨0, fun B => by simp [tvB]⟩
  | func f v ih =>
      match f, v with
      | LO.FirstOrder.Language.ORing.Func.zero, v =>
          refine ⟨0, fun B => ?_⟩
          have hv : tvB (Semiterm.func LO.FirstOrder.Language.ORing.Func.zero v) B = 0 := by
            simp only [tvB, GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          simp [hv]
      | LO.FirstOrder.Language.ORing.Func.one, v =>
          refine ⟨1, fun B => ?_⟩
          have hv : tvB (Semiterm.func LO.FirstOrder.Language.ORing.Func.one v) B = 1 := by
            simp only [tvB, GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          have h := hG_succ B
          simp only [Function.iterate_one]
          omega
      | LO.FirstOrder.Language.ORing.Func.add, v =>
          obtain ⟨c₀, h₀⟩ := ih 0
          obtain ⟨c₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, fun B => ?_⟩
          have hb₀ : tvB (v 0) B ≤ G^[max c₀ c₁] B :=
            le_trans (h₀ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_left c₀ c₁) B)
          have hb₁ : tvB (v 1) B ≤ G^[max c₀ c₁] B :=
            le_trans (h₁ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_right c₀ c₁) B)
          have hadd : tvB (Semiterm.func LO.FirstOrder.Language.ORing.Func.add v) B
              = tvB (v 0) B + tvB (v 1) B := by
            simp only [tvB, GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          rw [hadd, Function.iterate_succ_apply']
          exact le_trans (hG_add _ _) (hG_mono (max_le hb₀ hb₁))
      | LO.FirstOrder.Language.ORing.Func.mul, v =>
          obtain ⟨c₀, h₀⟩ := ih 0
          obtain ⟨c₁, h₁⟩ := ih 1
          refine ⟨max c₀ c₁ + 1, fun B => ?_⟩
          have hb₀ : tvB (v 0) B ≤ G^[max c₀ c₁] B :=
            le_trans (h₀ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_left c₀ c₁) B)
          have hb₁ : tvB (v 1) B ≤ G^[max c₀ c₁] B :=
            le_trans (h₁ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_right c₀ c₁) B)
          have hmul : tvB (Semiterm.func LO.FirstOrder.Language.ORing.Func.mul v) B
              = tvB (v 0) B * tvB (v 1) B := by
            simp only [tvB, GoodsteinPA.Compat.gValm, Semiterm.val_func]; rfl
          rw [hmul, Function.iterate_succ_apply']
          exact le_trans (hG_mul _ _) (hG_mono (max_le hb₀ hb₁))

/-- **`gvb` of a fixed formula is `G`-iterate-bounded** — the `P*`-domination shape:
`∃ c, ∀ B, gvb ψ B ≤ G^[c] B`. -/
theorem gvb_le_iter (hG_mono : Monotone G) (hG_succ : ∀ x, x + 1 ≤ G x)
    (hG_add : ∀ a b, a + b ≤ G (max a b)) (hG_mul : ∀ a b, a * b ≤ G (max a b))
    {m : ℕ} (ψ : SyntacticSemiformula ℒₒᵣ m) : ∃ c, ∀ B, gvb ψ B ≤ G^[c] B := by
  induction ψ with
  | rel r v =>
      choose c hc using fun i => tvB_le_iter hG_mono hG_succ hG_add hG_mul (v i)
      refine ⟨Finset.univ.sup c, fun B => ?_⟩
      rw [show gvb (Semiformula.rel r v) B = Finset.univ.sup (fun i => tvB (v i) B) from rfl]
      exact Finset.sup_le fun i _ => le_trans (hc i B)
        (iter_le_iter_of_succ hG_mono hG_succ (Finset.le_sup (Finset.mem_univ i)) B)
  | nrel r v =>
      choose c hc using fun i => tvB_le_iter hG_mono hG_succ hG_add hG_mul (v i)
      refine ⟨Finset.univ.sup c, fun B => ?_⟩
      rw [show gvb (Semiformula.nrel r v) B = Finset.univ.sup (fun i => tvB (v i) B) from rfl]
      exact Finset.sup_le fun i _ => le_trans (hc i B)
        (iter_le_iter_of_succ hG_mono hG_succ (Finset.le_sup (Finset.mem_univ i)) B)
  | verum =>
      exact ⟨0, fun B => by
        rw [show gvb (Semiformula.verum : SyntacticSemiformula ℒₒᵣ _) B = 0 from rfl]
        exact Nat.zero_le B⟩
  | falsum =>
      exact ⟨0, fun B => by
        rw [show gvb (Semiformula.falsum : SyntacticSemiformula ℒₒᵣ _) B = 0 from rfl]
        exact Nat.zero_le B⟩
  | and χ₁ χ₂ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁
      obtain ⟨c₂, h₂⟩ := ih₂
      refine ⟨max c₁ c₂, fun B => ?_⟩
      rw [show gvb (Semiformula.and χ₁ χ₂) B = max (gvb χ₁ B) (gvb χ₂ B) from rfl]
      exact max_le
        (le_trans (h₁ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_left c₁ c₂) B))
        (le_trans (h₂ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_right c₁ c₂) B))
  | or χ₁ χ₂ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁
      obtain ⟨c₂, h₂⟩ := ih₂
      refine ⟨max c₁ c₂, fun B => ?_⟩
      rw [show gvb (Semiformula.or χ₁ χ₂) B = max (gvb χ₁ B) (gvb χ₂ B) from rfl]
      exact max_le
        (le_trans (h₁ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_left c₁ c₂) B))
        (le_trans (h₂ B) (iter_le_iter_of_succ hG_mono hG_succ (le_max_right c₁ c₂) B))
  | all χ ih =>
      obtain ⟨c, h⟩ := ih
      exact ⟨c, fun B => by
        rw [show gvb (Semiformula.all χ) B = gvb χ B from rfl]; exact h B⟩
  | exs χ ih =>
      obtain ⟨c, h⟩ := ih
      exact ⟨c, fun B => by
        rw [show gvb (Semiformula.exs χ) B = gvb χ B from rfl]; exact h B⟩

/-- **The uniform root certificate** (SERIES-4 S-3): for the numeral family
`ψ_m = ∃⁰((subst ![nm m]).q ▹ body)` over a FIXED matrix `body`, ONE iterate count `k` serves
every `m`: the canonical `P := gvb ψ_m (max V ·)` is monotone, `Gated`, and `G^[k]`-bounded at
the `max (max V m)`-shifted argument (`gvb_substs_q_le` contracts the numeral out,
`gvb_le_iter` bounds the fixed matrix). -/
theorem gated_certificate_uniform {G : ℕ → ℕ} (hG_mono : Monotone G)
    (hG_succ : ∀ x, x + 1 ≤ G x)
    (hG_add : ∀ a b, a + b ≤ G (max a b)) (hG_mul : ∀ a b, a * b ≤ G (max a b))
    (body : SyntacticSemiformula ℒₒᵣ 2) :
    ∃ k : ℕ, ∀ (m V : ℕ) (χ : SyntacticSemiformula ℒₒᵣ 1),
      χ = (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹ body →
      Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) →
      ∃ P : ℕ → ℕ, Monotone P ∧ Gated P V (∃⁰ χ) ∧
        ∀ z, P z ≤ G^[k] (max (max V m) z) := by
  obtain ⟨k, hk⟩ := gvb_le_iter hG_mono hG_succ hG_add hG_mul body
  refine ⟨k, fun m V χ hχ hH => ?_⟩
  refine ⟨fun B => gvb (∃⁰ χ) (max V B),
    fun _ _ hb => gvb_mono _ (max_le_max le_rfl hb), ?_, ?_⟩
  · refine gated_of_sigma1 (fun _ _ hb => gvb_mono _ (max_le_max le_rfl hb)) _ hH V
      (fun B => ?_)
    exact gvb_mono _ (le_trans (le_max_right V B) (le_max_right V (max V B)))
  · intro z
    have h1 : gvb (∃⁰ χ) (max V z) = gvb χ (max V z) := rfl
    show gvb (∃⁰ χ) (max V z) ≤ G^[k] (max (max V m) z)
    rw [h1, hχ]
    refine le_trans (gvb_substs_q_le m (max V z)) ?_
    refine le_trans (hk (max (max V z) m)) ?_
    exact (hG_mono.iterate k) (by omega)

end IterDom

#print axioms GoodsteinPA.ReadoffValueGate.gated_certificate_uniform
#print axioms GoodsteinPA.ReadoffValueGate.gvb_le_iter
#print axioms GoodsteinPA.ReadoffValueGate.gated_root_of_sigma1
#print axioms GoodsteinPA.ReadoffValueGate.gated_of_sigma1
#print axioms GoodsteinPA.ReadoffValueGate.Gated_mono
#print axioms GoodsteinPA.ReadoffValueGate.Gated_all_iff
#print axioms GoodsteinPA.ReadoffValueGate.gvb_mono
#print axioms GoodsteinPA.ReadoffValueGate.gvb_rew_le
#print axioms GoodsteinPA.ReadoffValueGate.gvb_substs_le
#print axioms GoodsteinPA.ReadoffValueGate.gvb_substs_q_le

end GoodsteinPA.ReadoffValueGate
