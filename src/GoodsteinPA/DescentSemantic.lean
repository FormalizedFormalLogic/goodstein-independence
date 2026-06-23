/-
# `DescentSemantic.lean` — the E wall via first-order COMPLETENESS (lap-30 strategic redirect)

**The lap-30 finding.** The descent wall `Thm56.DescentE`
(`𝗣𝗔 ⊢ goodsteinSentence → Nonempty (Derivation2 paLX {TI prec})`) does **not** require hand-building a
`paLX` sequent-calculus derivation of `TI_≺(X)` (the literature-gated Route-B plan, see
`ON-LINE-REQUEST.md`). Foundation's **first-order completeness theorem** delivers the derivation from a
single *semantic* premise. `Derivation.completeness_of_encodable` (`Completeness/Completeness.lean`)
produces `(paLX : Schema LX) ⟹ [TI prec]` from:

> every model `M ⊧ paLX` satisfies `TI prec` (under every assignment).

So the **entire** E wall collapses to ONE semantic obligation, `paLX_models_TI_of_PA_provable`: *under
the hypothesis `𝗣𝗔 ⊢ goodsteinSentence`*, every model `M ⊧ paLX` satisfies `TI prec`. This is Rathjen
§3 carried out **inside the model `M`** — the free set predicate `X` is `M`'s own interpretation, and the
inequality-(6) induction is justified by `M ⊧ InductionScheme LX`. Three structural wins over the
sequent-calculus plan:

1. **Resolves the free-`X` obstruction** (lap-24 correction). The earlier `sigma1_pos_succ_induction`
   route worked in `V ⊧ 𝗜𝚺₁` (no `X`) and landed an X-free `𝗣𝗔 ⊢ PRWO`, which cannot refute the free-`X`
   `TI prec`. Here we work in models of `paLX`, where `X` is present throughout, and completeness does the
   syntactic lift for free.
2. **No literature gate.** No need to pin "the precise calculus-internal `Goodstein ⟹ paLX ⊢ TI_≺(X)`
   sequent shape" — the semantic argument is standard model theory.
3. **Reuses the lap-26 substrate.** The internal Goodstein arithmetic (`igoodstein`/`ibump`, bridged
   faithful to `Defs`) lives in `M`'s `ℒₒᵣ`-reduct; `DescentCore.ineq6_step` is the route-neutral kernel.

**Non-vacuity / anti-fraud.** `paLX_models_TI_of_PA_provable` is **conditionally** true (its conclusion
`M ⊧ TI prec` is exactly what fails in the Thm-5.6 countermodel; the hypothesis `𝗣𝗔 ⊢ goodsteinSentence`
is the real meta-premise we discharge — *not* assumed false). It genuinely needs Rathjen §3 to connect
"Goodstein terminates in `M`" with "`TI prec` holds in `M`". This file proves `Thm56.DescentE` **modulo
the disclosed `sorry`** in that lemma; it does **NOT** touch `Statement.lean`'s headline `sorry`, which
stays put until the semantic lemma is real and `#print axioms` is clean (`DIRECTION.md` anti-fraud rule).
-/
import GoodsteinPA.Thm56
import GoodsteinPA.DescentLift

namespace GoodsteinPA.DescentSemantic

open LO LO.FirstOrder
open GoodsteinPA GoodsteinPA.LangX GoodsteinPA.EmbeddingX

/-! ### `LX` is an encodable language

`completeness_of_encodable` needs `[LX.Encodable]`. `LX = Language.add ℒₒᵣ Xpred` has
`Func k = ℒₒᵣ.Func k ⊕ Empty` and `Rel k = ℒₒᵣ.Rel k ⊕ XRel k`; the only missing piece is
`Encodable (XRel k)` (`XRel` is the one-constructor `X : XRel 1`). -/

/-- `XRel k` is empty for `k ≠ 1` and the singleton `{X}` for `k = 1`; encode everything to `0`. -/
instance instEncodableXRel (k : ℕ) : Encodable (XRel k) where
  encode _ := 0
  decode n := match k, n with
    | 1, 0 => some XRel.X
    | _, _ => none
  encodek := by rintro ⟨⟩; rfl

instance instEncodableLXFunc (k : ℕ) : Encodable (LX.Func k) :=
  inferInstanceAs (Encodable (Language.Func ℒₒᵣ k ⊕ Empty))

instance instEncodableLXRel (k : ℕ) : Encodable (LX.Rel k) :=
  inferInstanceAs (Encodable (Language.Rel ℒₒᵣ k ⊕ XRel k))

noncomputable instance instEncodableLX : Language.Encodable LX :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-! ### Step 1 (PROVED): import Goodstein into the model

The easy front of the semantic obligation: under `𝗣𝗔 ⊢ goodsteinSentence`, the lifted Goodstein sentence
holds in every model `M ⊧ paLX`. Pure proof-translation + soundness, no Rathjen content. -/

open GoodsteinPA.DescentLift in
/-- **`M` models the lifted Goodstein sentence.** From `𝗣𝗔 ⊢ goodsteinSentence`, E-lift
(`paLX_derivable2_lMap_of_PA_provable`) gives `paLX ⊢ lMap Φ goodsteinSentence` (as an `LX`-sentence, via
`provable_def` + `Semiformula.lMap_emb`); soundness (`models_of_provable`) then transports it into any
model `M ⊧ paLX`. -/
theorem models_lMap_goodstein (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M : Type} [Nonempty M] [Structure LX M] (hM : M ⊧ₘ* (paLX : Theory LX)) :
    M ⊧ₘ (Semiformula.lMap Φ goodsteinSentence : Sentence LX) := by
  obtain ⟨d⟩ := paLX_derivable2_lMap_of_PA_provable goodsteinSentence h
  refine models_of_provable hM ?_
  rw [provable_def, show (↑(Semiformula.lMap Φ goodsteinSentence) : SyntacticFormula LX)
        = Semiformula.lMap Φ (↑goodsteinSentence : SyntacticFormula ℒₒᵣ) from
      (Semiformula.lMap_emb goodsteinSentence).symm]
  exact provable_iff_derivable2.mpr ⟨d⟩

open GoodsteinPA.DescentLift in
/-- **The `ℒₒᵣ`-reduct of `M` models `goodsteinSentence`** (the directly-usable arithmetic form of
`models_lMap_goodstein`, via `Semiformula.models_lMap`): every internal Goodstein run terminates in `M`. -/
theorem reduct_models_goodstein (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M : Type} [Nonempty M] [inst : Structure LX M] (hM : M ⊧ₘ* (paLX : Theory LX)) :
    (inst.lMap Φ).toStruc ⊧ goodsteinSentence :=
  Semiformula.models_lMap.mp (models_lMap_goodstein h hM)

/-! ### Step 2 (PROVED): unfold `TI prec` semantics in `M` to abstract transfinite induction

`Evalfm M f (TI prec)` is exactly transfinite induction for the pair `(Mlt f, MX)` — `Mlt` is `M`'s
interpretation of the X-free order `prec` (= `≺`), `MX` is `M`'s interpretation of the set variable `X`.
This strips the Foundation-DSL wrapper, leaving a transparent goal the Rathjen §3 argument acts on. -/

/-- `M`'s interpretation of the set variable `X` (the `Xsym` relation). -/
def MX {M : Type} [Structure LX M] (a : M) : Prop := Structure.rel (L := LX) Xsym ![a]

/-- `M`'s interpretation of the order `≺` (`= Thm56.prec`, X-free), at assignment `f`: `Mlt f y x` reads
`prec` with `#0 ↦ y`, `#1 ↦ x`. -/
def Mlt {M : Type} [Structure LX M] (f : ℕ → M) (y x : M) : Prop :=
  Semiformula.Eval (L := LX) ‹_› ![y, x] f Thm56.prec

/-- **`TI prec` in `M` = abstract transfinite induction for `(Mlt, MX)`.** `Evalfm M f (TI prec)` holds
iff: progressivity of `MX` along `Mlt` implies `MX` is total. Pure unfolding (`map_imply`/`eval_all`/
`eval_rel₁`). -/
theorem evalfm_TI_unfold {M : Type} [Nonempty M] [Structure LX M] (f : ℕ → M) :
    Semiformula.Evalfm M f (Boundedness.TI Thm56.prec)
      ↔ ((∀ x : M, (∀ y : M, Mlt f y x → MX y) → MX x) → ∀ x : M, MX x) := by
  unfold MX Mlt
  simp only [Boundedness.TI, Boundedness.Prog, Boundedness.hyp, Boundedness.Xat,
    LogicalConnective.HomClass.map_imply, Semiformula.eval_all, Semiformula.eval_rel₁,
    Semiterm.val_bvar, Matrix.cons_val_zero]
  rfl

/-! ### Step 3 — the genuine remaining obligation (Rathjen §3 in `M`), as ONE named `sorry` -/

/-- **The lone remaining wall: a non-`MX`-minimal seed yields a contradiction with Goodstein-in-`M`
(DISCLOSED `sorry`).** This is Rathjen "Goodstein revisited" §3 carried out *inside `M`*: given the
"no `Mlt`-minimal non-`MX` element" fact `no_min` (so `MX`'s complement is `Mlt`-progressive-downward) and
the Goodstein-termination fact `hgood`, derive `False`. Discharge plan:

1. **M-internal `Mlt`-descent.** From `no_min` + `ha₀`, build a *definable* descending sequence
   `G : M → M`, `G 0 = a₀`, `G(k+1) =` `Mlt`-least `y` with `Mlt y (G k) ∧ ¬MX y`, via `M`'s LX
   least-number principle (`hM ⊧ InductionScheme LX Set.univ`; `Arithmetic.succInd`/`leastNumber` are
   generic over `[LX.ORing]`). **Must be M-internal** (definable + M-recursion), *not* metatheoretic
   `choice`, so the run aligns with `M`'s internal termination statement (see `PENDING_WORK.md` ⚠).
2. **`M`'s `ℒₒᵣ`-reduct as `𝗜𝚺₁`.** `hM ⊧ paLX ⊇ lMap 𝗣𝗔` ⟹ reduct `⊧ 𝗣𝗔 ⊇ 𝗜𝚺₁`; install it as the
   substrate's `[ORingStructure M] [M ⊧ₘ* 𝗜𝚺₁]`.
3. **Slow-down + inequality (6).** Slow `(G k)` ⟹ `(βₖ)` (`C(βₖ) ≤ k+1`); run the special Goodstein seq
   from `m₀ = T̂²(β₀)` (lap-26 `igoodstein` in the reduct); iterate `DescentCore.ineq6_step` by `M`'s
   LX-induction ⟹ `M ⊧ ∀k mₖ > 0`; contradict `hgood`.

The free predicate `X` (`MX`) is present throughout (a model of `paLX`, not `𝗜𝚺₁`) — the lap-24 free-`X`
obstruction does not apply. The lap-26 substrate supplies the run; this lemma is the genuine content. -/
theorem no_min_descent_absurd_of_goodstein {M : Type} [Nonempty M] [Structure LX M]
    [Structure.Eq LX M]
    (hgood : M ⊧ₘ (Semiformula.lMap GoodsteinPA.DescentLift.Φ goodsteinSentence : Sentence LX))
    (hM : M ⊧ₘ* (paLX : Theory LX)) {f : ℕ → M} {a₀ : M} (ha₀ : ¬ MX a₀)
    (no_min : ∀ x : M, ¬ MX x → ∃ y, Mlt f y x ∧ ¬ MX y) : False := by
  sorry

/-! ### The single semantic obligation, assembled (Rathjen §3, model-internal) -/

/-- **The E wall, reduced to one model-theoretic statement.** Under `𝗣𝗔 ⊢ goodsteinSentence`, *every*
model `M ⊧ paLX` satisfies `TI prec`. Steps 1–2 (`models_lMap_goodstein`, `evalfm_TI_unfold`) and the
progressivity-contrapositive are PROVED here; the genuine remaining content is the single named
`sorry` `no_min_descent_absurd_of_goodstein` (Rathjen §3 in `M`). -/
theorem paLX_models_TI_of_PA_provable (h : 𝗣𝗔 ⊢ ↑goodsteinSentence)
    {M : Type} [Nonempty M] [Structure LX M] [Structure.Eq LX M]
    (hM : M ⊧ₘ* (paLX : Theory LX)) (f : ℕ → M) :
    Semiformula.Evalfm M f (Boundedness.TI Thm56.prec) := by
  -- Step 1 (PROVED): the lifted Goodstein sentence holds in `M`.
  have hgood : M ⊧ₘ (Semiformula.lMap GoodsteinPA.DescentLift.Φ goodsteinSentence : Sentence LX) :=
    models_lMap_goodstein h hM
  -- Step 2 (PROVED): reduce to abstract transfinite induction for `(Mlt f, MX)`.
  rw [evalfm_TI_unfold]
  intro hProg
  -- Suppose `MX` is not total: `¬MX a₀` for some `a₀`.
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  -- PROVED (progressivity-contrapositive): the non-`MX` set has no `Mlt`-minimal element.
  have no_min : ∀ x : M, ¬ MX x → ∃ y, Mlt f y x ∧ ¬ MX y := fun x hx => by
    by_contra hc
    rw [not_exists] at hc
    exact hx (hProg x (fun y hy => by by_contra hny; exact hc y ⟨hy, hny⟩))
  -- Step 3 (the lone remaining obligation): the descent + Goodstein run contradiction.
  exact no_min_descent_absurd_of_goodstein hgood hM ha₀ no_min

/-! ### `DescentE` via first-order completeness -/

/-- **`Thm56.DescentE`, proved via completeness (modulo the disclosed semantic `sorry`).** From
`𝗣𝗔 ⊢ goodsteinSentence`, `completeness_of_encodable` turns the single semantic premise
`paLX_models_TI_of_PA_provable` into the derivation `paLX ⟹ [TI prec]`, then `toDerivation2` packages it
as the `Derivation2 paLX {TI prec}` that `DescentE` requires. -/
theorem descentE : Thm56.DescentE := by
  intro h
  -- The closed-sentence form of `TI prec` (it is free-variable-free: `Thm56.freeVariables_TI`).
  let tiSent : Sentence LX := (Boundedness.TI Thm56.prec).toEmpty Thm56.freeVariables_TI
  -- Semantic premise, now with genuine equality available in each model (via `𝗘𝗤 ⪯ paLX`):
  -- `consequence_iff_eq` lets us WLOG-assume `[Structure.Eq LX M]` (every model is elementarily
  -- equivalent to its `QuotEq`-quotient, and `𝗘𝗤 ⪯ paLX` preserves `paLX` under that quotient).
  have hsem : (GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊨ tiSent := by
    rw [show ((GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊨ tiSent)
          = ((GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊨[Struc.{0,0} LX] tiSent) from rfl,
        consequence_iff_eq]
    intro M _ _ _ hM
    rw [models_iff]
    exact (Semiformula.eval_toEmpty Thm56.freeVariables_TI).mp
      (paLX_models_TI_of_PA_provable h hM (fun _ => Classical.arbitrary M))
  -- Completeness (`complete : T ⊨ φ → T ⊢ φ`): the semantic premise lifts to syntactic provability.
  have hprov : (GoodsteinPA.EmbeddingX.paLX : Theory LX) ⊢ tiSent := complete hsem
  -- Repackage `paLX ⊢ tiSent` as a `Schema`-`Derivation2`, then rewrite `↑tiSent = TI prec`.
  have h2 : (GoodsteinPA.EmbeddingX.paLX : Schema LX) ⊢!₂! (↑tiSent : SyntacticFormula LX) :=
    provable_iff_derivable2.mp (provable_def.mp hprov)
  rwa [show (↑tiSent : SyntacticFormula LX) = Boundedness.TI Thm56.prec
        from Semiformula.emb_toEmpty (Boundedness.TI Thm56.prec) Thm56.freeVariables_TI] at h2

/-- **The headline, modulo the one disclosed semantic `sorry`.** Combining `descentE` with the proved
reduction `Thm56.peano_not_proves_goodstein_of_descent` yields `𝗣𝗔 ⊬ goodsteinSentence`. This carries a
`sorryAx` (from `paLX_models_TI_of_PA_provable`) and is therefore **NOT** wired into `Statement.lean`'s
headline (anti-fraud). It exists so `#print axioms` audits the *full* chain: the only non-trust-base
axioms must be `sorryAx` + the F-φ `native_decide` artifact — no `PA_delta1Definable`, no custom axiom. -/
theorem peano_not_proves_goodstein_modulo_semantic : 𝗣𝗔 ⊬ ↑goodsteinSentence :=
  Thm56.peano_not_proves_goodstein_of_descent descentE

end GoodsteinPA.DescentSemantic
