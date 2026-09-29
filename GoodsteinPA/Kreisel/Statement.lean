/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import Foundation.FirstOrder.Incompleteness.Definability

@[expose] public section

/-!
# Kreisel's unnatural well-ordering: the statements

Kreisel's example behind the "natural well-ordering" problem.  We build a `Δ₁` (hence
primitive-recursively decidable) binary relation `kreiselLT` on the naturals which, **in the
standard model, is literally the usual `<`** — order type `ω` — and yet `𝗣𝗔` does not prove
transfinite induction along it, not even for the single formula `good`.  By contrast `𝗣𝗔` proves
transfinite induction along the *syntactic* `<` for every formula.  So the proof-theoretic strength
of "transfinite induction up to `α`" depends on the *notation*, not on the order type: exactly
Kreisel's point.

## The construction

* `prfBotΔ z` — "`z` codes a `𝗣𝗔`-proof of `⊥`", i.e. Foundation's `Δ₁` proof predicate
  `proof 𝗣𝗔` with its formula slot fixed to `⌜(⊥ : Sentence ℒₒᵣ)⌝`.
* `goodΔ x` — `∀ z ≤ x, ¬ prfBotΔ z`: no contradiction proof is coded at or below `x`.
* `kreiselLTΔ x y` — `<` restricted to the good part, then everything good before everything bad,
  then the bad part in **reverse** order.  If `𝗣𝗔` were inconsistent with least contradiction
  proof `p`, the tail from `p` on would be an infinite descending chain; since `𝗣𝗔` is in fact
  consistent, no `x` is bad and the relation collapses to `<` (headline 1).

## The four headlines

1. `kreiselLT_iff_lt` — in `ℕ`, `kreiselLT` *is* `<`.
2. `pa_not_proves_TI_kreisel` — `𝗣𝗔 ⊬ TI kreiselLT good`.
3. `pa_proves_TI_lt` — `𝗣𝗔 ⊢ TI ltRel φ` for every `φ`.
4. `kreiselLT_delta1` — `kreiselLTΔ` is `Δ₁`: its `Σ₁` and `Π₁` halves are provably equivalent
   over `𝗣𝗔` (`ProvablyProperOn`, Foundation's notion of `Δ₁`-ness), the two halves being in
   `Hierarchy 𝚺 1` / `Hierarchy 𝚷 1` by construction.

All of them are proved here, `sorry`-free and on the bare mathlib axiom triple; the two
faithfulness pins `good_iff` and `nat_models_TI_kreisel` (the sentence `𝗣𝗔` cannot prove is *true*)
come with them.
-/

namespace GoodsteinPA.Kreisel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Bounding.HierarchySymbol
open scoped FFL.FirstOrder.Bounding

/-! ## The relation -/

/-- `prfBotΔ z` : "`z` codes a `𝗣𝗔`-proof of `⊥`".  Foundation's `Δ₁` proof predicate
`proof 𝗣𝗔 d φ` with the formula slot fixed to `⌜⊥⌝`. -/
noncomputable def prfBotΔ : 𝚫ᴬ₁.Semisentence 1 :=
  (proof 𝗣𝗔).rew (Rew.subst ![#0, ⌜(⊥ : Sentence ℒₒᵣ)⌝])

/-- `prfBotΔ` as a plain formula. -/
noncomputable abbrev prfBot : Semisentence ℒₒᵣ 1 := prfBotΔ.val

/-- `goodΔ x` : `∀ z ≤ x, ¬ prfBot z` — no `𝗣𝗔`-proof of `⊥` is coded at or below `x`.
Bounded, hence still `Δ₁`. -/
noncomputable def goodΔ : 𝚫ᴬ₁.Semisentence 1 :=
  Bounding.HierarchySymbol.Semiformula.arithmetic_ball ‘x. x + 1’ (∼ prfBotΔ.rew (Rew.subst ![#0]))

/-- `goodΔ` as a plain formula; this is the `φ` of headline 2. -/
noncomputable abbrev good : Semisentence ℒₒᵣ 1 := goodΔ.val

/-- The `Δ₁` order relation `x < y` (a `Δ₀` matrix packaged as `Δ₁`). -/
noncomputable def ltΔ : 𝚫ᴬ₁.Semisentence 2 :=
  .mkDelta (.mkSigma “x y. x < y”) (.mkPi “x y. x < y”)

/-- The `Δ₁` relation `y < x`. -/
noncomputable def gtΔ : 𝚫ᴬ₁.Semisentence 2 :=
  .mkDelta (.mkSigma “x y. y < x”) (.mkPi “x y. y < x”)

/-- `goodΔ` at the first argument of a binary formula. -/
noncomputable abbrev goodΔ₀ : 𝚫ᴬ₁.Semisentence 2 := goodΔ.rew (Rew.subst ![#0])

/-- `goodΔ` at the second argument of a binary formula. -/
noncomputable abbrev goodΔ₁ : 𝚫ᴬ₁.Semisentence 2 := goodΔ.rew (Rew.subst ![#1])

/-- **Kreisel's relation.**  `x ≺ y` iff
`(good x ∧ good y ∧ x < y) ∨ (good x ∧ ¬ good y) ∨ (¬ good x ∧ ¬ good y ∧ y < x)`. -/
noncomputable def kreiselLTΔ : 𝚫ᴬ₁.Semisentence 2 :=
  (goodΔ₀ ⋏ goodΔ₁ ⋏ ltΔ) ⋎ (goodΔ₀ ⋏ ∼goodΔ₁) ⋎ (∼goodΔ₀ ⋏ ∼goodΔ₁ ⋏ gtΔ)

/-- Kreisel's relation as a plain formula. -/
noncomputable abbrev kreiselLT : Semisentence ℒₒᵣ 2 := kreiselLTΔ.val

/-- The ordinary `<`, as a binary semisentence. -/
def ltRel : Semisentence ℒₒᵣ 2 := “x y. x < y”

/-! ## Transfinite induction, internalized -/

/-- `TI r φ` : the sentence "`φ` is progressive along `r` implies `φ` holds everywhere",
i.e. `(∀ x, (∀ y, y ≺ x → φ y) → φ x) → ∀ x, φ x`. -/
def TI (r : Semisentence ℒₒᵣ 2) (φ : Semisentence ℒₒᵣ 1) : Sentence ℒₒᵣ :=
  “(∀ x, (∀ y, !r y x → !φ y) → !φ x) → ∀ x, !φ x”

/-! ## Semantics in an arbitrary model -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- "`z` codes a `𝗣𝗔`-proof of `⊥`", read in the model `V`. -/
def PrfBot (z : V) : Prop := Proof 𝗣𝗔 z (⌜(⊥ : Sentence ℒₒᵣ)⌝ : V)

/-- "no `𝗣𝗔`-proof of `⊥` is coded at or below `x`", read in the model `V`. -/
def Good (x : V) : Prop := ∀ z ≤ x, ¬ PrfBot z

/-- Kreisel's relation, read in the model `V`. -/
def KreiselLT (x y : V) : Prop :=
  (Good x ∧ Good y ∧ x < y) ∨ (Good x ∧ ¬ Good y) ∨ (¬ Good x ∧ ¬ Good y ∧ y < x)

instance prfBot.defined : 𝚫ᴬ₁-Predicate[V] PrfBot via prfBotΔ :=
  .mk ⟨by simp [prfBotΔ], by intro v; simp [prfBotΔ, PrfBot]⟩

lemma prfBotΔ_rew_properOn : ((prfBotΔ.rew (Rew.subst ![#0]) : 𝚫ᴬ₁.Semisentence 2)).ProperOn V := by
  simp

instance good.defined : 𝚫ᴬ₁-Predicate[V] Good via goodΔ :=
  .mk ⟨by
        unfold goodΔ
        exact Bounding.HierarchySymbol.Semiformula.ProperOn.ball (R := Semiformula.Operator.LT.lt) (by rfl) (t := ‘x. x + 1’)
          (prfBotΔ_rew_properOn (V := V)).neg, by
        intro v
        simp only [goodΔ, Bounding.HierarchySymbol.Semiformula.val_arithmetic_ball, Good]
        simp [(prfBotΔ_rew_properOn (V := V)).eval_neg, lt_succ_iff_le]
        ⟩

lemma goodΔ_properOn : (goodΔ : 𝚫ᴬ₁.Semisentence 1).ProperOn V :=
  Bounding.HierarchySymbol.Defined.proper (R := fun v : Fin 1 → V ↦ Good (v 0))

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma ltΔ_properOn : (ltΔ : 𝚫ᴬ₁.Semisentence 2).ProperOn V := by intro e; simp [ltΔ]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma gtΔ_properOn : (gtΔ : 𝚫ᴬ₁.Semisentence 2).ProperOn V := by intro e; simp [gtΔ]

instance kreiselLT.defined : 𝚫ᴬ₁-Relation[V] KreiselLT via kreiselLTΔ :=
  .mk ⟨by
        unfold kreiselLTΔ
        exact ((goodΔ_properOn (V := V)).rew _ |>.and
            (((goodΔ_properOn (V := V)).rew _).and (ltΔ_properOn (V := V)))).or
          ((((goodΔ_properOn (V := V)).rew _).and ((goodΔ_properOn (V := V)).rew _).neg).or
            ((((goodΔ_properOn (V := V)).rew _).neg).and
              ((((goodΔ_properOn (V := V)).rew _).neg).and (gtΔ_properOn (V := V))))), by
        intro v
        simp only [kreiselLTΔ, KreiselLT, Bounding.HierarchySymbol.Semiformula.val_or,
          Bounding.HierarchySymbol.Semiformula.val_and]
        simp [((goodΔ_properOn (V := V)).rew (Rew.subst ![#1])).eval_neg,
          ((goodΔ_properOn (V := V)).rew (Rew.subst ![#0])).eval_neg, ltΔ, gtΔ]⟩

/-- `good` is progressive along Kreisel's relation, in every model of `𝗜𝚺₁`.  This is the heart of
headline 2: if `x` is bad then `x + 1` is bad too and `x + 1 ≺ x`, so a progressive hypothesis at
`x` hands back `Good (x + 1)`, a contradiction. -/
lemma progressive_good (x : V) (h : ∀ y, KreiselLT y x → Good y) : Good x := by
  by_contra hx
  have hx1 : ¬ Good (x + 1) := fun H ↦ hx fun z hz ↦ H z (le_trans hz (by simp))
  exact hx1 (h (x + 1) (Or.inr (Or.inr ⟨hx1, hx, by simp⟩)))

/-- If every number is `Good` then no number codes a proof of `⊥`. -/
lemma consistent_of_all_good (h : ∀ x : V, Good x) : ¬ Provable 𝗣𝗔 (⌜(⊥ : Sentence ℒₒᵣ)⌝ : V) := by
  rintro ⟨d, hd⟩
  exact h d d (le_refl d) hd

/-- **The internal half of headline 2**, in every model of `𝗜𝚺₁`: transfinite induction along
Kreisel's relation for the single formula `good` implies the consistency of `𝗣𝗔`. -/
lemma models_TI_imp_consistent : V↓[ℒₒᵣ] ⊧ (TI kreiselLT good 🡒 𝗣𝗔.consistent.val) := by
  simp only [models_iff, TI]
  have H : ((∀ x : V, (∀ y : V, KreiselLT y x → Good y) → Good x) → ∀ x : V, Good x) →
      Theory.Consistent V 𝗣𝗔 := fun h ↦ consistent_of_all_good (h fun x hx ↦ progressive_good x hx)
  simpa [models_iff, TI] using H

/-- Every natural number is `Good`: `𝗣𝗔` is consistent, so nothing codes a proof of `⊥`. -/
lemma nat_good (x : ℕ) : Good x := by
  intro z _ hz
  have h : ¬ Provable 𝗣𝗔 (⌜(⊥ : Sentence ℒₒᵣ)⌝ : ℕ) :=
    (standard_consistent 𝗣𝗔).mpr inferInstance
  exact h ⟨z, hz⟩

/-- In `ℕ`, Kreisel's relation is the usual `<`. -/
lemma nat_kreiselLT_iff (x y : ℕ) : KreiselLT x y ↔ x < y := by
  simp [KreiselLT, nat_good]

/-- If `𝗣𝗔` is consistent *in the model* `V`, every element of `V` is `Good`. -/
lemma all_good_of_consistent (h : Theory.Consistent V 𝗣𝗔) : ∀ x : V, Good x :=
  fun _ z _ hz ↦ h ⟨z, hz⟩

/-- The converse of `models_TI_imp_consistent`: consistency *implies* the transfinite induction,
because it makes the conclusion `∀ x, good x` outright true.  So over `𝗣𝗔` the sentence
`TI kreiselLT good` is **equivalent** to `Con(𝗣𝗔)` — headline 2's failure is exactly a consistency
gap, no more and no less. -/
lemma models_TI_iff_consistent : V↓[ℒₒᵣ] ⊧ (TI kreiselLT good 🡘 𝗣𝗔.consistent.val) := by
  simp only [models_iff, TI]
  have H : (((∀ x : V, (∀ y : V, KreiselLT y x → Good y) → Good x) → ∀ x : V, Good x) ↔
      Theory.Consistent V 𝗣𝗔) :=
    ⟨fun h ↦ consistent_of_all_good (h fun x hx ↦ progressive_good x hx),
     fun h _ ↦ all_good_of_consistent h⟩
  simpa [models_iff, TI] using H

/-- **Ill-foundedness, the reason `𝗣𝗔` cannot see the order type.**  In any model where `𝗣𝗔` is
inconsistent — and by Gödel II `𝗣𝗔` has such models — Kreisel's relation carries an infinite
descending chain: if `d` codes a proof of `⊥` then `d, d+1, d+2, …` is `≺`-descending, because every
`d + n` is bad and on the bad part `≺` *reverses* `<`. -/
lemma descending_chain_of_inconsistent (h : ¬ Theory.Consistent V 𝗣𝗔) :
    ∃ f : ℕ → V, ∀ n : ℕ, KreiselLT (f (n + 1)) (f n) := by
  obtain ⟨d, hd⟩ : Provable 𝗣𝗔 (⌜(⊥ : Sentence ℒₒᵣ)⌝ : V) := by
    simpa [Theory.Consistent] using h
  refine ⟨fun n ↦ Nat.rec d (fun _ x ↦ x + 1) n, fun n ↦ ?_⟩
  have hge : ∀ m : ℕ, d ≤ (Nat.rec d (fun _ x ↦ x + 1) m : V) := by
    intro m
    induction m with
    | zero => exact le_def.mpr (Or.inl rfl)
    | succ m ih => exact le_trans ih (by simp)
  have hbad : ∀ m : ℕ, ¬ Good (Nat.rec d (fun _ x ↦ x + 1) m : V) := fun m H ↦ H d (hge m) hd
  exact Or.inr (Or.inr ⟨hbad (n + 1), hbad n, by simp⟩)

end Model

/-! ## Order induction for arbitrary formulas, in any model of `𝗣𝗔` -/

section PAModel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Strong (order) induction in a model of `𝗣𝗔`, for a predicate given by an *arbitrary*
first-order formula.  `𝗣𝗔` has the induction scheme for every formula, so this needs no
hierarchy hypothesis — that is what makes headline 3 work for all `φ`. -/
lemma model_order_induction (φ : Semisentence ℒₒᵣ 1)
    (ind : ∀ x : V, (∀ y < x, V ⊧/![y] φ) → V ⊧/![x] φ) : ∀ x : V, V ⊧/![x] φ := by
  haveI : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  haveI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  suffices h : ∀ x : V, ∀ y < x, V ⊧/![y] φ by
    intro x; exact h (x + 1) x (by simp)
  have hP : ∃ e : ℕ → V, ∃ ψ : ArithmeticSemiformula ℕ 1,
      (Set.univ : ArithmeticSemiformula ℕ 1 → Prop) ψ ∧
      ∀ x : V, (∀ y < x, V ⊧/![y] φ) ↔ ψ.Eval ![x] e := by
    refine ⟨fun _ ↦ 0, “x. ∀ y < x, !(Rew.emb ▹ φ) y”, trivial, ?_⟩
    intro z
    simp
  refine InductionScheme.succ_induction (C := Set.univ) hP ?_ ?_
  · simp
  · intro x IH y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH

end PAModel

/-! ## Headlines -/

/-- **Headline 1.**  In the standard model Kreisel's relation *is* the usual `<`: it has order
type `ω`.  (Uses that `𝗣𝗔` is sound, so no `z` codes a proof of `⊥`, so every `x` is `good`.) -/
theorem kreiselLT_iff_lt : ∀ x y : ℕ, (ℕ ⊧/![x, y] kreiselLT) ↔ x < y := by
  intro x y
  simpa using nat_kreiselLT_iff x y

/-- **Headline 2.**  `𝗣𝗔` does not prove transfinite induction along `kreiselLT`, already for the
single instance `φ := good`.  Sketch: inside `𝗣𝗔`, `good` is progressive along `kreiselLT`
(if `¬ good x` then `y := x + 1` satisfies `¬ good y` and `y ≺ x`), so `TI kreiselLT good` yields
`∀ x, good x`, which `𝗣𝗔` proves equivalent to `𝗣𝗔.consistent.val`; Gödel II
(`consistent_unprovable`) finishes. -/
theorem pa_not_proves_TI_kreisel : 𝗣𝗔 ⊬ ↑(TI kreiselLT good) := by
  intro h
  have key : 𝗣𝗔 ⊢ ↑(TI kreiselLT good) 🡒 𝗣𝗔.consistent.val :=
    Arithmetic.complete.{0} 𝗣𝗔 _ fun M _ _ ↦ by
      haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
      exact models_TI_imp_consistent
  exact consistent_unprovable 𝗣𝗔 (key ⨀ h)

/-- **Headline 3.**  `𝗣𝗔` proves transfinite induction along the ordinary `<` for *every* formula:
this is just strong induction, available in `𝗣𝗔`.  Same relation in `ℕ` as headline 1's, opposite
provability status. -/
theorem pa_proves_TI_lt : ∀ φ : Semisentence ℒₒᵣ 1, 𝗣𝗔 ⊢ ↑(TI ltRel φ) := fun φ ↦
  Arithmetic.complete.{0} 𝗣𝗔 _ fun M _ _ ↦ by
    have H : (∀ x : M, (∀ y < x, M ⊧/![y] φ) → M ⊧/![x] φ) → ∀ x : M, M ⊧/![x] φ :=
      model_order_induction φ
    simpa [models_iff, TI, ltRel] using H

/-- **Headline 4a.**  The two halves of `kreiselLTΔ` sit in `𝚺ᴬ₁` resp. `𝚷ᴬ₁` (by construction). -/
theorem kreiselLT_hierarchy :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 kreiselLTΔ.sigma.val ∧
      ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1 kreiselLTΔ.pi.val := ⟨by simp, by simp⟩

/-- **Headline 4b.**  `kreiselLTΔ` is `Δ₁` in Foundation's sense: `𝗣𝗔` proves its `𝚺ᴬ₁` and `𝚷ᴬ₁`
halves equivalent.  Together with `kreiselLT_hierarchy` this is the precise content of "the
relation is primitive recursive". -/
theorem kreiselLT_delta1 : kreiselLTΔ.ProvablyProperOn 𝗣𝗔 :=
  Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} 𝗣𝗔 fun M _ _ ↦ by
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    exact Bounding.HierarchySymbol.Defined.proper (R := fun v : Fin 2 → M ↦ KreiselLT (v 0) (v 1))

/-- **Sharpness of headline 2.**  Over `𝗣𝗔`, the transfinite-induction sentence for Kreisel's
relation is *equivalent* to `Con(𝗣𝗔)`.  So headline 2 is not an artefact of a weak proof: what `𝗣𝗔`
lacks is exactly its own consistency, and `TI kreiselLT good` is a natural `𝚷ᴬ₁` axiom of that
strength. -/
theorem pa_proves_TI_iff_consistent : 𝗣𝗔 ⊢ ↑(TI kreiselLT good) 🡘 𝗣𝗔.consistent.val :=
  Arithmetic.complete.{0} 𝗣𝗔 _ fun M _ _ ↦ by
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    exact models_TI_iff_consistent

/-- Corollary of sharpness: adding `Con(𝗣𝗔)` is enough to prove the induction `𝗣𝗔` cannot.
Contrast `pa_not_proves_TI_kreisel`. -/
theorem pa_con_proves_TI_kreisel : 𝗣𝗔 ∪ 𝗣𝗔.Con ⊢ ↑(TI kreiselLT good) := by
  haveI hsub : 𝗣𝗔 ⪯ 𝗣𝗔 ∪ 𝗣𝗔.Con := Entailment.WeakerThan.ofSubset Set.subset_union_left
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔 ∪ 𝗣𝗔.Con :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔) hsub
  refine Arithmetic.complete.{0} _ _ fun M _ _ ↦ ?_
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := ModelsTheory.of_add_left M 𝗣𝗔 𝗣𝗔.Con
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  have hc : Theory.Consistent M 𝗣𝗔 := by
    have h : M↓[ℒₒᵣ] ⊧ (𝗣𝗔.consistent.val : Sentence ℒₒᵣ) :=
      Theory.models (T := 𝗣𝗔 ∪ 𝗣𝗔.Con) M (by simp)
    simpa [models_iff] using h
  have : ∀ x : M, Good x := all_good_of_consistent hc
  simpa [models_iff, TI] using fun _ ↦ this

/-- **Headline 1, in its strongest form: the relation *is* `<` as a relation on `ℕ`.**  Not merely
pointwise equivalent — equal.  Everything true of `<` on `ℕ` (well-foundedness, trichotomy, order
type `ω`) therefore transfers verbatim, which is what makes the contrast with
`pa_not_proves_TI_kreisel` sharp: `𝗣𝗔` also proves transfinite induction along the *syntactic* `<`
(`pa_proves_TI_lt`), so the difference is in the notation, not the order. -/
theorem kreiselLT_eq_lt : (fun x y : ℕ ↦ ℕ ⊧/![x, y] kreiselLT) = (· < ·) := by
  funext x y
  exact propext (kreiselLT_iff_lt x y)

/-- Kreisel's relation is well-founded on `ℕ` — order type `ω`.  `𝗣𝗔` cannot prove transfinite
induction along it all the same; cf. `descending_chain_of_inconsistent`, which exhibits the infinite
descending chain that appears in any model where `𝗣𝗔` is inconsistent.  Such models exist by Gödel
II, and that is precisely why `𝗣𝗔` cannot see the order type. -/
theorem kreiselLT_wellFounded : WellFounded (fun x y : ℕ ↦ ℕ ⊧/![x, y] kreiselLT) := by
  rw [kreiselLT_eq_lt]
  exact Nat.lt_wfRel.wf

/-! ## Known-answer sanity checks -/

example : ∀ x y : ℕ, (ℕ ⊧/![x, y] ltRel) ↔ x < y := by intro x y; simp [ltRel]

example (z : ℕ) : (ℕ ⊧/![z] prfBot) ↔ Proof 𝗣𝗔 z (⌜(⊥ : Sentence ℒₒᵣ)⌝ : ℕ) := by
  simp [prfBot, prfBotΔ]

/-- Faithfulness of `good`: it really says "no `𝗣𝗔`-proof of `⊥` is coded at or below `x`".
Not free from `simp`, because the `∼` of a `𝚫ᴬ₁` formula evaluates through its `𝚷ᴬ₁` half; it needs
the properness of `prfBotΔ` (which comes from Foundation's `Proof.defined`).  Phase 2. -/
theorem good_iff (x : ℕ) :
    (ℕ ⊧/![x] good) ↔ ∀ z ≤ x, ¬ Proof 𝗣𝗔 z (⌜(⊥ : Sentence ℒₒᵣ)⌝ : ℕ) := by
  have h : (ℕ ⊧/![x] good) ↔ Good x :=
    Bounding.HierarchySymbol.Defined.iff (v := ![x]) (R := fun v : Fin 1 → ℕ ↦ Good (v 0)) (φ := goodΔ)
  rw [h]
  constructor
  · intro H z hz; exact H z (le_def.mpr (by omega))
  · intro H z hz; exact H z (by rcases le_def.mp hz with h | h <;> omega)

/-- **Anti-vacuity (ratification amendment).**  The sentence `𝗣𝗔` fails to prove is *true* in the
standard model: since `𝗣𝗔` is consistent, every `x` is `good`, so the conclusion of the induction
holds outright. -/
theorem nat_models_TI_kreisel : ℕ↓[ℒₒᵣ] ⊧ TI kreiselLT good := by
  have : ∀ x : ℕ, Good x := nat_good
  simpa [models_iff, TI] using fun _ ↦ this

end GoodsteinPA.Kreisel

end
