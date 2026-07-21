/-
The embedding `𝗣𝗔 ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` via `Derivation2` (Finset-sequent variant, with no language
translation). The main result `Provable.of_derivation2` carries a numeral assignment `asg e` that closes all
free variables, enabling the ω-rule `allω` and ω-completeness `Provable.of_true` to handle non-structural
cases (∃-intro via witness collapse, PA axioms via arithmetic truth). Axiom-clean.

- [Tow20, §16]
- [Buc03, §5.5]
-/
module

public import GoodsteinPA.Zinfty.Cut
public import GoodsteinPA.ToFoundation.Subst

@[expose] public section

namespace GoodsteinPA.Zinfty

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm

variable {Γ : Finset (ArithmeticFormula ℕ)} {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
  (hval : ∀ i, Semiterm.gValm ℕ ![] id (w i) = Semiterm.gValm ℕ ![] id (w' i))

/-! ## Closed-term existential introduction

Value-congruent excluded middle (`Provable.em_cong_gen`, `Provable.em_cong`) and closed-term `∃`-intro
(`Provable.exI_closed`). -/

/-- Literal-truth congruence under value-equal substitutions. -/
lemma litTrue_subst_congr (hval : ∀ i, Semiterm.gValm ℕ ![] id (w i) = Semiterm.gValm ℕ ![] id (w' i))
    (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ℕ n) :
    LitTrue (signedLit b r (fun i => Rew.subst w (v i)))
      ↔ LitTrue (signedLit b r (fun i => Rew.subst w' (v i))) := by
  have hv : (fun i => Semiterm.gValm ℕ ![] id (Rew.subst w (v i)))
          = (fun i => Semiterm.gValm ℕ ![] id (Rew.subst w' (v i))) := by
    funext i; exact valm_subst_congr w w' hval (v i)
  cases b <;>
    simp only [signedLit, LitTrue, Semiformula.eval_rel, Semiformula.eval_nrel, hv, Function.comp_def]

namespace Provable

/-- **Value-congruent excluded middle (arity-general).** -/
theorem em_cong_gen : ∀ (k : ℕ) {n : ℕ} (w w' : Fin n → ArithmeticTerm ℕ)
    (ψ : ArithmeticSemiformula ℕ n), ψ.complexity ≤ k →
    (∀ i, Semiterm.gValm ℕ ![] id (w i)
        = Semiterm.gValm ℕ ![] id (w' i)) →
    ∀ {Γ : Finset (ArithmeticFormula ℕ)}, (Rew.subst w ▹ ψ) ∈ Γ → (∼(Rew.subst w' ▹ ψ)) ∈ Γ → ∃ a, Provable a 0 Γ := by
  intro k
  induction k with
  | zero =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v =>
      exact atomic_close w w' hval true r v
        (by simpa [signedLit, Semiformula.rew_rel, Function.comp_def] using hp)
        (by simpa [signedLit, Semiformula.rew_rel, Function.comp_def] using hn)
    | hnrel r v =>
      exact atomic_close w w' hval false r v
        (by simpa [signedLit, Semiformula.rew_nrel, Function.comp_def] using hp)
        (by simpa [signedLit, Semiformula.rew_nrel, Function.comp_def] using hn)
    | hand φ ψ => simp at hk
    | hor φ ψ => simp at hk
    | hall φ => simp at hk
    | hexs φ => simp at hk
  | succ k ih =>
    intro n w w' ψ hk hval Γ hp hn
    cases ψ using Semiformula.cases' with
    | hverum => exact ⟨0, Provable.verumR (by simpa using hp)⟩
    | hfalsum => exact ⟨0, Provable.verumR (by simpa using hn)⟩
    | hrel r v =>
      exact atomic_close w w' hval true r v
        (by simpa [signedLit, Semiformula.rew_rel, Function.comp_def] using hp)
        (by simpa [signedLit, Semiformula.rew_rel, Function.comp_def] using hn)
    | hnrel r v =>
      exact atomic_close w w' hval false r v
        (by simpa [signedLit, Semiformula.rew_nrel, Function.comp_def] using hp)
        (by simpa [signedLit, Semiformula.rew_nrel, Function.comp_def] using hn)
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
      exact Provable.em_binaryStep hp' hn' ⟨a1, h1⟩ ⟨a2, h2⟩
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
      exact Provable.em_binaryStep hn' hp' ⟨a1, h1⟩ ⟨a2, h2⟩
    | hall a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_all] at hk; omega
      have hp' : (∀⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∃⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, Provable x 0
          (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) (insert (((Rew.subst w).q ▹ a)/[nm m]) Γ)) := by
        intro m
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak (hvalm_cons w w' hval m)
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        refine ⟨x, ?_⟩
        rw [show (((Rew.subst w').q ▹ ∼a)/[nm m]) = ∼(((Rew.subst w').q ▹ a)/[nm m]) by simp,
          Finset.insert_comm]
        exact hx
      exact Provable.em_quantStep hp' hn' fam
    | hexs a =>
      have hak : a.complexity ≤ k := by simp only [Semiformula.complexity_exs] at hk; omega
      have hp' : (∃⁰ ((Rew.subst w).q ▹ a)) ∈ Γ := by simpa using hp
      have hn' : (∀⁰ ((Rew.subst w').q ▹ ∼a)) ∈ Γ := by simpa using hn
      have fam : ∀ m, ∃ x, Provable x 0
          (insert (((Rew.subst w).q ▹ a)/[nm m]) (insert (((Rew.subst w').q ▹ ∼a)/[nm m]) Γ)) := by
        intro m
        obtain ⟨x, hx⟩ := ih (n := n + 1) (nm m :> w) (nm m :> w') a hak (hvalm_cons w w' hval m)
          (Γ := insert (((Rew.subst w).q ▹ a)/[nm m])
            (insert (∼(((Rew.subst w').q ▹ a)/[nm m])) Γ))
          (by rw [← subst_q_cons_app]; simp)
          (by rw [← subst_q_cons_app]; simp)
        refine ⟨x, ?_⟩
        rwa [show (((Rew.subst w').q ▹ ∼a)/[nm m]) = ∼(((Rew.subst w').q ▹ a)/[nm m]) by simp]
      exact Provable.em_quantStep hn' hp' fam
where
  -- extending `w`/`w'` by the shared value `nm m` at the freed variable preserves value-congruence
  hvalm_cons {n} (w w' : Fin n → ArithmeticTerm ℕ)
      (hval : ∀ i, Semiterm.gValm ℕ ![] id (w i) = Semiterm.gValm ℕ ![] id (w' i)) (m : ℕ) :
      ∀ i, Semiterm.gValm ℕ ![] id ((nm m :> w) i)
          = Semiterm.gValm ℕ ![] id ((nm m :> w') i) := by
    intro i; cases i using Fin.cases with
    | zero => rfl
    | succ j => simpa using hval j
  -- shared atomic closing step for both polarities `b : Bool` (`rel`/`nrel`)
  atomic_close {n} (w w' : Fin n → ArithmeticTerm ℕ)
      (hval : ∀ i, Semiterm.gValm ℕ ![] id (w i) = Semiterm.gValm ℕ ![] id (w' i))
      (b : Bool) {k} (r : (ℒₒᵣ).Rel k) (v : Fin k → ArithmeticSemiterm ℕ n)
      {Γ : Finset (ArithmeticFormula ℕ)} (hp : signedLit b r (fun i => Rew.subst w (v i)) ∈ Γ)
      (hn : signedLit (!b) r (fun i => Rew.subst w' (v i)) ∈ Γ) : ∃ a, Provable a 0 Γ := by
    rcases litTrue_or_neg (signedLit b r (fun i => Rew.subst w (v i))) with htt | htf
    · exact ⟨0, Provable.axTrue b r _ htt hp⟩
    · rw [neg_lit] at htf
      have htf' : LitTrue (signedLit (!b) r (fun i => Rew.subst w' (v i))) :=
        (litTrue_subst_congr w w' hval (!b) r v).mp htf
      exact ⟨0, Provable.axTrue (!b) r _ htf' hn⟩

/-- **Value-congruent excluded middle (single-term form).** For closed terms `s, s'` of equal
standard value, a sequent containing `ψ/[s]` and `∼(ψ/[s'])` is `Z∞`-derivable cut-free. -/
theorem em_cong (s s' : ArithmeticTerm ℕ)
    (hval : Semiterm.gValm ℕ ![] id s = Semiterm.gValm ℕ ![] id s')
    (ψ : ArithmeticSemiformula ℕ 1)
    (hp : (ψ/[s]) ∈ Γ) (hn : (∼(ψ/[s'])) ∈ Γ) : ∃ a, Provable a 0 Γ := by
  refine em_cong_gen ψ.complexity ![s] ![s'] ψ le_rfl ?_ hp hn
  intro i; cases i using Fin.cases with
  | zero => simpa using hval
  | succ j => exact j.elim0

/-- **Closed-term existential introduction.** From a derivation of `insert (ψ/[s]) Γ` for ANY
(closed) witness term `s` (not necessarily a numeral), conclude `insert (∃⁰ψ) Γ`, at the raised
cut-rank bound `max c (ψ.complexity + 1)`. -/
theorem exI_closed {α : Ordinal.{0}} {c : ℕ}
    (ψ : ArithmeticSemiformula ℕ 1) (s : ArithmeticTerm ℕ)
    (h : Provable α c (insert (ψ/[s]) Γ)) :
    ∃ β, Provable β (max c (ψ.complexity + 1)) (insert (∃⁰ ψ) Γ) := by
  set m := Semiterm.gValm ℕ ![] id s
  set c' := max c (ψ.complexity + 1)
  have hsval : Semiterm.gValm ℕ ![] id (nm m)
             = Semiterm.gValm ℕ ![] id s := by rw [valm_nm]
  have h₁ : Provable α c' (insert (ψ/[s]) (insert (ψ/[nm m]) Γ)) :=
    (h.weakening (Finset.insert_subset_insert _ (Finset.subset_insert _ _))).mono_cutRank
      (le_max_left _ _)
  obtain ⟨b, h₂⟩ := em_cong (nm m) s hsval ψ
    (Γ := insert (∼(ψ/[s])) (insert (ψ/[nm m]) Γ)) (by simp) (by simp)
  have hcc : ((ψ/[s]).complexity + 1 : ℕ∞) ≤ (c' : ℕ∞) := by
    rw [show (ψ/[s]).complexity = ψ.complexity by simp]; exact_mod_cast le_max_right _ _
  exact ⟨_,
    Provable.exI m $
    Provable.cut (ψ/[s]) hcc h₁ $
    h₂.mono_cutRank (by omega)
  ⟩

/-! ## The assignment-carrying embedding

The main theorem carries a numeral assignment `asg e` to close all free variables and sequents. -/

/-- **The embedding, assignment-carrying form.** Every `Derivation2` from `𝗣𝗔` embeds into `Z_∞`
*at every numeral assignment of its free variables* (all sequents closed). -/
theorem of_derivation2 (d : 𝗣𝗔 ⟹₂ Γ) : ∃ c, ∀ e : ℕ → ℕ, ∃ α, Provable α c (Γ.image (fun φ => asg e ▹ φ)) := by
  induction d with
  | closed Γ φ hp hn =>
    exact ⟨0, fun _ => Provable.lem (Finset.mem_image_of_mem _ hp) (by grind)⟩
  | axm φ hφ hΓ =>
    -- ω-completeness: ↑φ is true under 𝗣𝗔, so derivable
    refine ⟨0, ?_⟩; intro _
    refine Provable.of_true ?_ (Finset.mem_image_of_mem _ hΓ)
    have hmod : ℕ ⊧ₘ φ := Semantics.modelsSet_iff.mp inferInstance hφ
    simp_all [LitTrue, asg, Semiformula.eval_emb, models_iff]
  | verum hΓ =>
    exact ⟨0, fun _ => ⟨0, Provable.verumR (by grind)⟩⟩
  | @and Γ φ ψ h _dp _dq ihp ihq =>
    obtain ⟨c1, ihp⟩ := ihp; obtain ⟨c2, ihq⟩ := ihq
    refine ⟨max c1 c2, ?_⟩; intro e
    obtain ⟨a1, h1⟩ := ihp e; obtain ⟨a2, h2⟩ := ihq e
    rw [Finset.image_insert] at h1 h2
    have hand := Provable.andI (h1.mono_cutRank (le_max_left c1 c2))
      (h2.mono_cutRank (le_max_right c1 c2))
    exact ⟨_, hand.insert_absorb (by simpa using Finset.mem_image_of_mem (fun φ => asg e ▹ φ) h)⟩
  | @or Γ φ ψ h _d ih =>
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, ?_⟩; intro e
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, Finset.image_insert] at hd
    have hor := Provable.orI hd
    exact ⟨_, hor.insert_absorb (by simpa using Finset.mem_image_of_mem (fun φ => asg e ▹ φ) h)⟩
  | @all Γ φ h _d ih =>
    -- introduce via `allω`: for each `n`, `ih (n :>ₙ e)` frees `&0 ↦ nm n` (`hA`) and the shifted
    -- `Γ` collapses back to the `asg e` image (`hB`).
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, ?_⟩; intro e
    have hfam : ∀ n, ∃ a, Provable a c
        (insert (((asg e).q ▹ φ)/[nm n]) (Γ.image (fun ψ => asg e ▹ ψ))) := by
      intro n
      obtain ⟨a, hd⟩ := ih (n :>ₙ e)
      rw [Finset.image_insert] at hd
      have hA : asg (n :>ₙ e) ▹ (Rewriting.free φ) = ((asg e).q ▹ φ)/[nm n] := asg_cons_free n e φ
      have hB : (Γ.image Rewriting.shift).image (fun ψ => asg (n :>ₙ e) ▹ ψ)
          = Γ.image (fun ψ => asg e ▹ ψ) := by
        rw [asg_image_shift, show (n :>ₙ e) ∘ Nat.succ = e from rfl]
      rw [hA, hB] at hd
      exact ⟨a, hd⟩
    choose β hβ using hfam
    have hall := Provable.allω hβ
    exact ⟨_, hall.insert_absorb (by simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) h)⟩
  | @exs Γ φ h t _d ih =>
    -- `rew_subst_term` turns the IH's `asg e ▹ (φ/[t])` into `((asg e).q ▹ φ)/[asg e t]` with
    -- `asg e t` CLOSED, then `Provable.exI_closed` collapses the witness to a numeral.
    obtain ⟨c, ih⟩ := ih
    refine ⟨max c (φ.complexity + 1), ?_⟩; intro e
    obtain ⟨a, hd⟩ := ih e
    rw [Finset.image_insert, rew_subst_term (asg e) φ t] at hd
    obtain ⟨β, hβ⟩ := Provable.exI_closed ((asg e).q ▹ φ) (asg e t) hd
    rw [show (((asg e).q ▹ φ).complexity + 1) = (φ.complexity + 1) by simp] at hβ
    exact ⟨_, hβ.insert_absorb (by simpa using Finset.mem_image_of_mem (fun ψ => asg e ▹ ψ) h)⟩
  | wk _ h ih =>
    obtain ⟨c, ih⟩ := ih
    exact ⟨c, fun e => (ih e).imp fun _ hα => hα.weakening (Finset.image_subset_image h)⟩
  | @shift Γ _d ih =>
    -- re-index the assignment: `asg e ∘ Rew.shift = asg (e ∘ succ)`.
    obtain ⟨c, ih⟩ := ih
    refine ⟨c, ?_⟩; intro e
    rw [asg_image_shift]; exact ih (e ∘ Nat.succ)
  | @cut Γ φ _d _dn ihd ihdn =>
    obtain ⟨c1, ihd⟩ := ihd; obtain ⟨c2, ihdn⟩ := ihdn
    refine ⟨max (φ.complexity + 1) (max c1 c2), ?_⟩; intro e
    obtain ⟨a1, h1⟩ := ihd e; obtain ⟨a2, h2⟩ := ihdn e
    rw [Finset.image_insert] at h1 h2
    rw [show (asg e ▹ (∼φ)) = ∼(asg e ▹ φ) by simp] at h2
    exact ⟨_, Provable.cut (asg e ▹ φ)
      (by rw [Semiformula.complexity_rew]; exact_mod_cast Nat.le_max_left _ _)
      (h1.mono_cutRank (by omega)) (h2.mono_cutRank (by omega))⟩

/-- **Cut-free embedding.** Every `Derivation2` from `𝗣𝗔` embeds into `Z_∞` *cut-free* at every
numeral assignment of its free variables. -/
theorem of_derivation2_cutFree (d : 𝗣𝗔 ⟹₂ Γ) (e : ℕ → ℕ) :
    ∃ α, Provable α 0 (Γ.image (fun φ => asg e ▹ φ)) := by
  obtain ⟨c, h⟩ := of_derivation2 d
  obtain ⟨α, hα⟩ := h e
  exact ⟨_, cut_elimination hα⟩

end Provable

end GoodsteinPA.Zinfty
