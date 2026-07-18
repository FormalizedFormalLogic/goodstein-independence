/-
# M4 — the embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` (Towsner §16 / Buchholz §5.5)

**The universal bottleneck of the whole expedition — COMPLETE (lap 11).** The embedding is set up
over Foundation's **`Derivation2`** (the Finset-sequent variant, `Calculus2.lean`), which lives over
the *same* `Finset (SyntacticFormula ℒₒᵣ)` substrate as M5's `ZinftyF.Seq` — so it is a pure
rule-by-rule map with **no language translation**.

## The headline result: `embedC` (assignment-carrying form)
`embedC : Derivation2 (𝗣𝗔 : Schema) Γ → ∃ c, ∀ e : ℕ → ℕ, ∃ α, Provable α c (Γ.image (asg e ▹))`.
The numeral assignment `asg e` (`&x ↦ nm (e x)`) closes every free variable, so all sequents in the
image are CLOSED — which is what lets M5's numeral-only `exI`/ω-rule `allω` fire. Axiom-clean
(`#print axioms embedC = [propext, Classical.choice, Quot.sound]`).

## The two non-structural cases and how they close
- **`exs`** (∃-intro, open witness term `t`): `asg e ▹ t` is a closed term; `Provable.exI_closed`
  collapses it to its standard value `nm m` (via the value-congruent EM `provable_em_cong_gen` + a
  single `cut`), then numeral-`exI` fires. The cut bumps the rank to `max c (φ.complexity+1)`.
- **`axm`** (PA axiom `↑σ`, `σ ∈ 𝗣𝗔`): since `ℕ ⊧ₘ* 𝗣𝗔`, `↑σ` is a TRUE closed formula, and
  `provable_true` (**ω-completeness**: every true closed formula is `Z∞`-derivable cut-free, by
  induction on complexity — atomic via `axTrue`, `∀` via `allω`, `∃` by choosing a true witness)
  discharges it directly. The ω-rule subsumes the Buchholz §5.5 meta-induction entirely.

## Supporting results (all axiom-clean, reusable)
- `provable_em` — Z∞ law of excluded middle (atomic + ∀/∃ numeral ω-family).
- `provable_em_cong_gen` / `provable_em_cong` — value-congruent EM (closed-term congruence).
- `Provable.exI_closed` — ∃-intro with an arbitrary closed witness term.
- `provable_true` — ω-completeness for true closed formulas.

## API anchors
- `Schema ℒₒᵣ := Set (SyntacticFormula ℒₒᵣ)`; `(𝗣𝗔 : Theory) ↦ (𝗣𝗔 : Schema) = Rewriting.emb '' 𝗣𝗔`.
- `provable_def : T ⊢ σ ↔ (T : Schema) ⊢ ↑σ` (rfl) · `provable_iff_derivable2 : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ`.
  ⟹ `𝗣𝗔 ⊢ goodsteinSentence` unfolds to `Nonempty (Derivation2 (𝗣𝗔:Schema) {↑goodsteinSentence})`.
- The naive (non-assignment) `embed`/`provable_rew` of laps 9–10 were superseded by `embedC` and
  removed on promotion; see `wip/Embedding.lean` (git history) for that scaffold.
-/
import GoodsteinPA.Zinfty
import Foundation.FirstOrder.Basic.Calculus2
import Foundation.FirstOrder.Arithmetic.Schemata
import GoodsteinPA.Compat

namespace GoodsteinPA.Embedding

open LO LO.FirstOrder GoodsteinPA.ZinftyF GoodsteinPA.ZinftyF.Deriv

/-- A `Z_∞`-derivable sequent, existentially quantified over the ordinal bound and cut rank
(Towsner states the whole embedding/cut-elim chain existentially in `(α, c)` — see
`ANALYSIS-…-cutelim-k-threading.md`). -/
def ZProvable (Γ : ZinftyF.Seq) : Prop := ∃ α c, Provable α c Γ

namespace ZProvable

theorem mono {Γ : ZinftyF.Seq} : ZProvable Γ → ZProvable Γ := id

/-- Weaken the sequent (Foundation `wk`). -/
theorem weakening {Γ Δ : ZinftyF.Seq} (h : Γ ⊆ Δ) : ZProvable Γ → ZProvable Δ := by
  rintro ⟨α, c, hd⟩; exact ⟨α, c, hd.weakening h⟩

/-- Drop a sequent element that already occurs (`insert X Γ = Γ` when `X ∈ Γ`). -/
theorem of_insert_mem {Γ : ZinftyF.Seq} {X : ZinftyF.Form} (h : X ∈ Γ) :
    ZProvable (insert X Γ) → ZProvable Γ := by
  rw [Finset.insert_eq_self.mpr h]; exact id

end ZProvable

/-- **Identity / law of excluded middle for `Z_∞`** (the `closed` case). For any `φ`, a sequent
containing both `φ` and `∼φ` is `Z_∞`-derivable cut-free. Proved by induction on a `complexity`
bound (the standard Tait `em`, cf. Foundation `Derivation.em`, `Calculus.lean:164`). The atomic /
propositional cases are discharged here; the **∀/∃ cases** need M5's numeral ω-family (`allω` over
all `nm n`, each premise closed by `exI` + the IH at the substitution instance `φ/[nm n]`, whose
`complexity` equals `φ`'s) — disclosed `sorry`, the next chip. -/
theorem provable_em (φ : ZinftyF.Form) {Γ : ZinftyF.Seq} (hp : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    ∃ a, Provable a 0 Γ := by
  have key : ∀ (k : ℕ) (φ : ZinftyF.Form), φ.complexity ≤ k →
      ∀ {Γ : ZinftyF.Seq}, φ ∈ Γ → ∼φ ∈ Γ → ∃ a, Provable a 0 Γ := by
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

/-- **General substitution–rewriting commutation** (the `exs`/`axm` version of `rew_subst_nm`, for an
arbitrary witness term `t`): `ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t]`. In the assignment embedding `ω = asg e`
closes `t`, so `ω t = asg e ▹ t` is a closed term whose numeral value feeds `Provable.exI`. -/
lemma rew_subst_term (ω : Rew ℒₒᵣ ℕ 0 ℕ 0) (φ : SyntacticSemiformula ℒₒᵣ 1)
    (t : SyntacticTerm ℒₒᵣ) : ω ▹ (φ/[t]) = (ω.q ▹ φ)/[ω t] := by
  show ω ▹ (Rew.subst ![t] ▹ φ) = Rew.subst ![ω t] ▹ (ω.q ▹ φ)
  have heq : ω.comp (Rew.subst ![t]) = (Rew.subst ![ω t]).comp ω.q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ i => exact Fin.elim0 i
    · simp [Rew.comp_app]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, heq]


/-! ## Closed-term existential introduction (ported from wip/ScratchEmCong.lean, lap 11)
    The shared chip for `embedC`'s `exs`/`axm`: a value-congruent law of excluded middle
    (`provable_em_cong_gen`) ⟹ closed-term `∃`-intro `Provable.exI_closed`. -/

/-- Substitution-composition: substituting the freed (q) variable by `nm m` after a renaming
`Rew.subst w` is the same as substituting by the extended vector `nm m :> w`. -/
lemma subst_q_cons (w : Fin n → SyntacticTerm ℒₒᵣ) (m : ℕ) :
    (Rew.subst ![nm m]).comp (Rew.subst w).q = Rew.subst (nm m :> w) := by
  ext x
  · cases x using Fin.cases with
    | zero => simp [Rew.comp_app]
    | succ i => simp [Rew.comp_app]
  · simp [Rew.comp_app]

/-- Formula form: `((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ`. -/
lemma subst_q_cons_app (w : Fin n → SyntacticTerm ℒₒᵣ) (m : ℕ)
    (ψ : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    ((Rew.subst w).q ▹ ψ)/[nm m] = Rew.subst (nm m :> w) ▹ ψ := by
  show Rew.subst ![nm m] ▹ ((Rew.subst w).q ▹ ψ) = Rew.subst (nm m :> w) ▹ ψ
  rw [← TransitiveRewriting.comp_app, subst_q_cons]

/-- Value of a renamed term depends only on the values of the substituted terms. -/
lemma valm_subst_congr {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w i)
                = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w' i))
    (t : SyntacticSemiterm ℒₒᵣ n) :
    GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (Rew.subst w t)
      = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (Rew.subst w' t) := by
  simp only [GoodsteinPA.Compat.gValm, Semiterm.val_substs]
  congr 1
  funext x; exact hval x

/-- Literal-truth congruence under value-equal substitutions. -/
lemma litTrue_subst_congr {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (hval : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w i)
                = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w' i))
    (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm ℒₒᵣ n) :
    LitTrue (signedLit b r (fun i => Rew.subst w (v i)))
      ↔ LitTrue (signedLit b r (fun i => Rew.subst w' (v i))) := by
  have hv : (fun i => GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (Rew.subst w (v i)))
          = (fun i => GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (Rew.subst w' (v i))) := by
    funext i; exact valm_subst_congr w w' hval (v i)
  cases b <;>
    simp only [signedLit, LitTrue, Semiformula.eval_rel, Semiformula.eval_nrel, hv, Function.comp_def]

/-- The numeral `nm m` evaluates to `m` in the standard ℕ-model (any free assignment). -/
lemma valm_nm (m : ℕ) (f : ℕ → ℕ) : GoodsteinPA.Compat.gValm ℕ ![] f (nm m) = m := by
  simp [nm]

/-- **Value-congruent excluded middle (arity-general).** -/
theorem provable_em_cong_gen : ∀ (k : ℕ) {n : ℕ} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
    (ψ : SyntacticSemiformula ℒₒᵣ n), ψ.complexity ≤ k →
    (∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w i)
        = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w' i)) →
    ∀ {Γ : Seq}, (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ → ∃ a, Provable a 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v => exact atomic_close w w' hval r v hp hn
    | hnrel r v => exact atomic_close_neg w w' hval r v hp hn
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v => exact atomic_close w w' hval r v hp hn
    | hnrel r v => exact atomic_close_neg w w' hval r v hp hn
    | hand a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_and] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋎ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      obtain ⟨a1, h1⟩ := ih (n := n) w w' a hak hval
        (Γ := insert (Rew.subst w ▹ a)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      obtain ⟨a2, h2⟩ := ih (n := n) w w' b hbk hval
        (Γ := insert (Rew.subst w ▹ b)
          (insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ)))
        (by simp) (by simp)
      have hand := Provable.andI (Rew.subst w ▹ a) (Rew.subst w ▹ b) h1 h2
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋏ (Rew.subst w ▹ b))
        ∈ insert (∼(Rew.subst w' ▹ a)) (insert (∼(Rew.subst w' ▹ b)) Γ) by simp [hp'])] at hand
      have hor := Provable.orI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) hand
      rw [Finset.insert_eq_self.mpr hn'] at hor
      exact ⟨_, hor⟩
    | hor a b =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hbk : b.complexity ≤ k := by simp only [Semiformula.complexity_or] at hk; omega
      have hp' : ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ := by simpa using hp
      have hn' : (∼(Rew.subst w' ▹ a) ⋏ ∼(Rew.subst w' ▹ b)) ∈ Γ := by simpa using hn
      obtain ⟨a1, h1⟩ := ih (n := n) w w' a hak hval
        (Γ := insert (∼(Rew.subst w' ▹ a))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      obtain ⟨a2, h2⟩ := ih (n := n) w w' b hbk hval
        (Γ := insert (∼(Rew.subst w' ▹ b))
          (insert (Rew.subst w ▹ a) (insert (Rew.subst w ▹ b) Γ)))
        (by simp) (by simp)
      have hand := Provable.andI (∼(Rew.subst w' ▹ a)) (∼(Rew.subst w' ▹ b)) h1 h2
      rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn'))]
        at hand
      have hor := Provable.orI (Rew.subst w ▹ a) (Rew.subst w ▹ b) hand
      rw [Finset.insert_eq_self.mpr (show ((Rew.subst w ▹ a) ⋎ (Rew.subst w ▹ b)) ∈ Γ
        by simp [hp'])] at hor
      exact ⟨_, hor⟩
    | hall a =>
      -- ψ = ∀⁰a ; positive side ∀⁰((subst w).q ▹ a), negative side ∃⁰((subst w').q ▹ ∼a)
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, Provable x 0 (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        -- reconstruct ∃⁰((subst w').q ▹ ∼a) via exI with witness m
        have hexI := Provable.exI ((Rew.subst w').q ▹ ∼a) m
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)
          (by
            have heq : (((Rew.subst w').q ▹ ∼a)/[nm m])
                = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
            rw [heq, Finset.insert_comm]; exact hx)
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hn')] at hexI
        exact ⟨_, hexI⟩
      choose β hβ using fam
      have hallω := Provable.allω ((Rew.subst w).q ▹ a) hβ
      rw [Finset.insert_eq_self.mpr hp'] at hallω
      exact ⟨_, hallω⟩
    | hexs a =>
      -- ψ = ∃⁰a ; positive side ∃⁰((subst w).q ▹ a), negative side ∀⁰((subst w').q ▹ ∼a)
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, Provable x 0 (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ) := by
        intro m
        have hvalm : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) ((nm m :> w) i)
            = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) ((nm m :> w') i) := by
          intro i; cases i using Fin.cases with
          | zero => rfl
          | succ j => simpa using hval j
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak hvalm
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        -- reconstruct ∃⁰((subst w).q ▹ a) via exI with witness m
        have hexI := Provable.exI ((Rew.subst w).q ▹ a) m
          (Γ := insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ) hx
        rw [Finset.insert_eq_self.mpr (Finset.mem_insert_of_mem hp')] at hexI
        have heq : (((Rew.subst w').q ▹ ∼a)/[nm m]) = ∼(((Rew.subst w').q ▹ a)/[nm m]) := by simp
        rw [heq]; exact ⟨_, hexI⟩
      choose β hβ using fam
      have hallω := Provable.allω ((Rew.subst w').q ▹ ∼a) hβ
      rw [Finset.insert_eq_self.mpr hn'] at hallω
      exact ⟨_, hallω⟩
where
  atomic_close {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
      (hval : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w i)
                = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w' i))
      {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm ℒₒᵣ n)
      {Γ : Seq} (hp : (Rew.subst w ▹ Semiformula.rel r v) ∈ Γ)
      (hn : (∼(Rew.subst w' ▹ Semiformula.rel r v)) ∈ Γ) : ∃ a, Provable a 0 Γ := by
    have hp' : signedLit true r (fun i => Rew.subst w (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_rel, Function.comp_def] using hp
    have hn' : signedLit false r (fun i => Rew.subst w' (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_rel, Function.comp_def] using hn
    rcases litTrue_or_neg (signedLit true r (fun i => Rew.subst w (v i))) with htt | htf
    · exact ⟨0, Provable.axTrue true r _ htt hp'⟩
    · rw [neg_lit] at htf
      have htf' : LitTrue (signedLit false r (fun i => Rew.subst w' (v i))) :=
        (litTrue_subst_congr w w' hval false r v).mp htf
      exact ⟨0, Provable.axTrue false r _ htf' hn'⟩
  atomic_close_neg {n} (w w' : Fin n → SyntacticTerm ℒₒᵣ)
      (hval : ∀ i, GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w i)
                = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (w' i))
      {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm ℒₒᵣ n)
      {Γ : Seq} (hp : (Rew.subst w ▹ Semiformula.nrel r v) ∈ Γ)
      (hn : (∼(Rew.subst w' ▹ Semiformula.nrel r v)) ∈ Γ) : ∃ a, Provable a 0 Γ := by
    have hp' : signedLit false r (fun i => Rew.subst w (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_nrel, Function.comp_def] using hp
    have hn' : signedLit true r (fun i => Rew.subst w' (v i)) ∈ Γ := by
      simpa [signedLit, Semiformula.rew_nrel, Function.comp_def] using hn
    rcases litTrue_or_neg (signedLit false r (fun i => Rew.subst w (v i))) with htt | htf
    · exact ⟨0, Provable.axTrue false r _ htt hp'⟩
    · rw [neg_lit] at htf
      have htf' : LitTrue (signedLit true r (fun i => Rew.subst w' (v i))) :=
        (litTrue_subst_congr w w' hval true r v).mp htf
      exact ⟨0, Provable.axTrue true r _ htf' hn'⟩

/-- **Value-congruent excluded middle (single-term form).** For closed terms `s, s'` of equal
standard value, a sequent containing `ψ/[s]` and `∼(ψ/[s'])` is `Z∞`-derivable cut-free. -/
theorem provable_em_cong (s s' : SyntacticTerm ℒₒᵣ)
    (hval : GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) s = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) s')
    (ψ : SyntacticSemiformula ℒₒᵣ 1) {Γ : Seq}
    (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) : ∃ a, Provable a 0 Γ := by
  refine provable_em_cong_gen ψ.complexity ![s] ![s'] ψ le_rfl ?_ ?_ ?_
  · intro i; cases i using Fin.cases with
    | zero => simpa using hval
    | succ j => exact j.elim0
  · exact hp
  · exact hn

/-- **Closed-term existential introduction.** From a derivation of `insert (ψ/[s]) Γ` for ANY
(closed) witness term `s`, conclude `insert (∃⁰ψ) Γ`. The witness need not be a numeral: `s` is
collapsed to its standard value `m` via `provable_em_cong` + `cut`, then the numeral-witness rule
`Provable.exI` applies. (The cut raises the cut-rank bound to `max c (ψ.complexity + 1)`.) -/
theorem Provable.exI_closed {α : Ordinal.{0}} {c : ℕ} {Γ : Seq}
    (ψ : SyntacticSemiformula ℒₒᵣ 1) (s : SyntacticTerm ℒₒᵣ)
    (h : Provable α c (insert (ψ/[s]) Γ)) :
    ∃ β, Provable β (max c (ψ.complexity + 1)) (insert (∃⁰ ψ) Γ) := by
  set m : ℕ := GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) s with hm
  set c' : ℕ := max c (ψ.complexity + 1) with hc'
  have hsval : GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) (nm m)
             = GoodsteinPA.Compat.gValm ℕ ![] (id : ℕ → ℕ) s := by rw [valm_nm]
  -- left cut premise: ψ/[s] available (from h, weakened to add ψ/[nm m])
  have h₁ : Provable α c' (insert (ψ/[s]) (insert (ψ/[nm m]) Γ)) :=
    (h.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))).mono le_rfl
      (le_max_left _ _)
  -- right cut premise: ∼(ψ/[s]) and ψ/[nm m] — value-congruent em (nm m vs s, equal values)
  obtain ⟨b, h₂⟩ := provable_em_cong (nm m) s hsval ψ
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[nm m]) Γ)) (by simp) (by simp)
  -- cut on χ = ψ/[s]
  have hcc : (((ψ/[s]).complexity : ℕ) + 1 : ℕ∞) ≤ (c' : ℕ∞) := by
    have : (ψ/[s]).complexity = ψ.complexity := by simp
    rw [this]; exact_mod_cast le_max_right _ _
  have hcut := Provable.cut (ψ/[s]) hcc h₁ (h₂.mono le_rfl (le_max_left _ _))
  -- hcut : Provable _ c' (insert (ψ/[nm m]) Γ); introduce ∃ by exI with numeral m
  exact ⟨_, Provable.exI ψ m hcut⟩



/-- **ω-completeness for true closed formulas.** Any closed (`SyntacticFormula ℒₒᵣ`) formula that is
TRUE in the standard model `ℕ` (`LitTrue`) is `Z∞`-derivable, cut-free. Proof by induction on
`complexity`: atomic via `axTrue`, `∀` via the ω-rule `allω`, `∃` by choosing a true witness. -/
theorem provable_true : ∀ (k : ℕ) (φ : Form), φ.complexity ≤ k → LitTrue φ →
    ∀ {Γ : Seq}, φ ∈ Γ → ∃ a, Provable a 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro φ hk htrue Γ hmem
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
    intro φ hk htrue Γ hmem
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



/-! ## The assignment-carrying (all-closed) embedding `embedC` — the correct frame (lap 10)

The naive `embed` above cannot finish (`exs` with an open witness; `provable_rew` invalid for the new
`axTrue` leaf). The fix is to carry a **numeral assignment** `e : ℕ → ℕ` of the free variables, so
every sequent in the image is CLOSED. `asg e` substitutes every free variable `&x` by the numeral
`nm (e x)`. The headline consumes `embedC d (fun _ => 0)` on the closed `↑goodsteinSentence`. -/

/-- The closing substitution: free variable `&x ↦ nm (e x)`. Sends every `SyntacticFormula` to a
closed formula (sentence image). -/
noncomputable def asg (e : ℕ → ℕ) : Rew ℒₒᵣ ℕ 0 ℕ 0 := Rew.rewrite (fun x => nm (e x))

/-- **The embedding, assignment-carrying form.** Every `Derivation2` from `𝗣𝗔` embeds into `Z_∞`
*at every numeral assignment of its free variables* (all sequents closed). Structural cases done;
`all`/`exs`/`axm` are the disclosed deep obligations (the latter two now unblocked by `axTrue`). -/
theorem embedC {Γ : Finset (SyntacticFormula ℒₒᵣ)}
    (d : Derivation2 (𝗣𝗔 : Theory ℒₒᵣ) Γ) :
    ∃ c : ℕ, ∀ e : ℕ → ℕ, ∃ α, Provable α c (Γ.image (fun φ => asg e ▹ φ)) := by
  induction d with
  | closed Γ φ hp hn =>
    exact ⟨0, fun e => provable_em (asg e ▹ φ) (Finset.mem_image_of_mem _ hp)
      (by have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hn; simpa using this)⟩
  | axm φ hφ hΓ =>
    -- closed PA axiom: `φ : Sentence ℒₒᵣ`, `φ ∈ 𝗣𝗔`, and `↑φ ∈ Γ` (upstream's `Derivation2` is
    -- `Theory`-indexed, so `axm` hands back the sentence `φ` and its coercion `↑φ : Proposition`
    -- directly — no `Rewriting.emb ''` unwrap). Since `ℕ ⊧ₘ* 𝗣𝗔`, `↑φ` is a TRUE closed formula,
    -- so (even after the closing substitution `asg e`, which fixes it) `provable_true`
    -- (ω-completeness) derives it directly — no Buchholz meta-induction needed; ω-rule subsumes it.
    refine ⟨0, fun e => ?_⟩
    have htrue : LitTrue (asg e ▹ (↑φ : SyntacticFormula ℒₒᵣ)) := by
      have hmod : ℕ ⊧ₘ φ := Semantics.modelsSet_iff.mp inferInstance hφ
      simp only [LitTrue, asg, Semiformula.eval_rewrite, Semiformula.eval_emb]
      rw [models_iff] at hmod
      simpa using hmod
    exact provable_true _ _ le_rfl htrue (Finset.mem_image_of_mem _ hΓ)
  | verum hΓ =>
    exact ⟨0, fun e => ⟨0, Provable.verumR
      (by have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) hΓ; simpa using this)⟩⟩
  | @and Γ φ ψ h _dp _dq ihp ihq =>
    obtain ⟨c1, ihp⟩ := ihp; obtain ⟨c2, ihq⟩ := ihq
    refine ⟨max c1 c2, fun e => ?_⟩
    obtain ⟨a1, h1⟩ := ihp e; obtain ⟨a2, h2⟩ := ihq e
    rw [Finset.image_insert] at h1 h2
    have h1' := h1.mono (le_refl a1) (le_max_left c1 c2)
    have h2' := h2.mono (le_refl a2) (le_max_right c1 c2)
    have hand := Provable.andI (asg e ▹ φ) (asg e ▹ ψ) h1' h2'
    have hmem : (asg e ▹ φ ⋏ asg e ▹ ψ) ∈ Γ.image (fun φ => asg e ▹ φ) := by
      have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) h; simpa using this
    rw [Finset.insert_eq_self.mpr hmem] at hand
    exact ⟨_, hand⟩
  | @or Γ φ ψ h _d ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, Finset.image_insert] at hd
    have hor := Provable.orI (asg e ▹ φ) (asg e ▹ ψ) hd
    have hmem : (asg e ▹ φ ⋎ asg e ▹ ψ) ∈ Γ.image (fun φ => asg e ▹ φ) := by
      have := Finset.mem_image_of_mem (fun φ => asg e ▹ φ) h; simpa using this
    rw [Finset.insert_eq_self.mpr hmem] at hor
    exact ⟨_, hor⟩
  | @all Γ φ h _d ih =>
    -- `∀⁰φ ∈ Γ`. Introduce by `allω`: for each `n`, use `ih (n :>ₙ e)` — the freed var `&0 ↦ nm n`
    -- (A), the shifted `Γ` collapses to the `asg e` image (B). The clean ω-rule case (uniform `c`).
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    have hfam : ∀ n, ∃ a, Provable a c
        (insert (((asg e).q ▹ φ)/[nm n]) (Γ.image (fun ψ => asg e ▹ ψ))) := by
      intro n
      obtain ⟨a, hd⟩ := ih (n :>ₙ e)
      rw [Finset.image_insert] at hd
      have hA : asg (n :>ₙ e) ▹ (Rewriting.free φ) = ((asg e).q ▹ φ)/[nm n] := by
        have hRew : (asg (n :>ₙ e)).comp Rew.free = (Rew.subst ![nm n]).comp (asg e).q := by
          ext x
          · refine Fin.cases ?_ (fun i => Fin.elim0 i) x
            simp [asg, Rew.comp_app]
          · simp [asg, Rew.comp_app]
        show asg (n :>ₙ e) ▹ (Rew.free ▹ φ) = Rew.subst ![nm n] ▹ ((asg e).q ▹ φ)
        rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hRew]
      have hB : (Γ.image Rewriting.shift).image (fun ψ => asg (n :>ₙ e) ▹ ψ)
          = Γ.image (fun ψ => asg e ▹ ψ) := by
        have hcompB : (asg (n :>ₙ e)).comp Rew.shift = asg e := by
          ext x
          · exact Fin.elim0 x
          · simp [asg, Rew.comp_app]
        rw [Finset.image_image]
        refine Finset.image_congr (fun ψ _ => ?_)
        show asg (n :>ₙ e) ▹ (Rew.shift ▹ ψ) = asg e ▹ ψ
        rw [← TransitiveRewriting.comp_app, hcompB]
      rw [hA, hB] at hd
      exact ⟨a, hd⟩
    choose β hβ using hfam
    have hall := Provable.allω ((asg e).q ▹ φ) hβ
    have hmem : (asg e ▹ (∀⁰ φ)) ∈ Γ.image (fun ψ => asg e ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (asg e ▹ (∀⁰ φ)) = ∀⁰ ((asg e).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hall
    exact ⟨_, hall⟩
  | @exs Γ φ h t _d ih =>
    -- `∃⁰φ ∈ Γ`, witness `t`. `rew_subst_term` turns the IH's `asg e ▹ (φ/[t])` into
    -- `((asg e).q ▹ φ)/[asg e t]` with `asg e t` CLOSED. The remaining `sorry` is the **closed-term
    -- collapse** `Provable (insert (ψ/[s]) Γ) → Provable (insert (∃⁰ψ) Γ)` for closed `s` (value `m`):
    -- a `Provable.exI_closed` derived from `Provable.exI` + Z∞ equality-congruence (`s = nm m` via
    -- `axTrue`, then Leibniz). The term-evaluation content — next chip.
    obtain ⟨c, ih⟩ := ih
    refine ⟨max c (φ.complexity + 1), fun e => ?_⟩
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, rew_subst_term (asg e) φ t] at hd
    -- hd : Provable a c (insert (((asg e).q ▹ φ)/[asg e t]) (Γ.image (asg e ▹)))
    obtain ⟨β, hβ⟩ := Provable.exI_closed ((asg e).q ▹ φ) (asg e t) hd
    -- hβ : Provable β (max c (((asg e).q▹φ).complexity+1)) (insert (∃⁰((asg e).q▹φ)) (Γ.image (asg e▹)))
    have hcomp : (((asg e).q ▹ φ).complexity + 1) = (φ.complexity + 1) := by simp
    rw [hcomp] at hβ
    have hmem : (asg e ▹ (∃⁰ φ)) ∈ Γ.image (fun ψ => asg e ▹ ψ) := Finset.mem_image_of_mem _ h
    rw [show (asg e ▹ (∃⁰ φ)) = ∃⁰ ((asg e).q ▹ φ) by simp] at hmem
    rw [Finset.insert_eq_self.mpr hmem] at hβ
    exact ⟨_, hβ⟩
  | @wk Δ Γ _d h ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    obtain ⟨α, hα⟩ := ih e
    exact ⟨α, hα.weakening (Finset.image_subset_image h)⟩
  | @shift Γ _d ih =>
    -- re-index the assignment: `asg e ∘ Rew.shift = asg (e ∘ succ)`.
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, fun e => ?_⟩
    have hcomp : (asg e).comp Rew.shift = asg (e ∘ Nat.succ) := by
      ext x
      · exact Fin.elim0 x
      · simp [asg, Rew.comp_app]
    have key : (Γ.image Rewriting.shift).image (fun φ => asg e ▹ φ)
        = Γ.image (fun φ => asg (e ∘ Nat.succ) ▹ φ) := by
      rw [Finset.image_image]
      refine Finset.image_congr (fun ψ _ => ?_)
      show asg e ▹ (Rew.shift ▹ ψ) = asg (e ∘ Nat.succ) ▹ ψ
      rw [← TransitiveRewriting.comp_app, hcomp]
    rw [key]; exact ih (e ∘ Nat.succ)
  | @cut Γ φ _d _dn ihd ihdn =>
    obtain ⟨c1, ihd⟩ := ihd; obtain ⟨c2, ihdn⟩ := ihdn
    refine ⟨max (φ.complexity + 1) (max c1 c2), fun e => ?_⟩
    obtain ⟨a1, h1⟩ := ihd e; obtain ⟨a2, h2⟩ := ihdn e
    rw [Finset.image_insert] at h1 h2
    rw [show (asg e ▹ (∼φ)) = ∼(asg e ▹ φ) by simp] at h2
    have h1' := h1.mono (le_refl a1)
      (show c1 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_left c1 c2) (le_max_right _ _))
    have h2' := h2.mono (le_refl a2)
      (show c2 ≤ max (φ.complexity + 1) (max c1 c2) from
        le_trans (le_max_right c1 c2) (le_max_right _ _))
    have hc : (((asg e ▹ φ).complexity + 1 : ℕ) : ℕ∞)
        ≤ ((max (φ.complexity + 1) (max c1 c2) : ℕ) : ℕ∞) := by
      rw [Semiformula.complexity_rew]; exact_mod_cast Nat.le_max_left _ _
    exact ⟨_, Provable.cut (asg e ▹ φ) hc h1' h2'⟩

end GoodsteinPA.Embedding
