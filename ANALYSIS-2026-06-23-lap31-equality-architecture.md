# ANALYSIS (lap 31, 2026-06-23) — the equality architecture of the completeness route

## TL;DR
The lap-30 completeness redirect reduces the headline to a model-internal Rathjen §3 argument run in
`M`'s `ℒₒᵣ`-reduct via the `igoodstein` substrate. That substrate is plain Lean arithmetic over its
carrier `V`, so it needs **real Lean equality**. But the Tait calculus (`Derivation`/`Derivation2`)
used by `descentE` has **NO built-in equality rules** (constructors: `axm, axL, verum, or, and, all,
exs, wk, cut` — verified `Calculus.lean:20`), so `completeness_of_encodable` quantifies its premise
over models where the `=`-symbol is an arbitrary relation. **To get real equality you must restrict to
`[Structure.Eq]`-models, which needs `𝗘𝗤 ⪯ paLX`.** This lap's `ReductModel.lean` proves the
reduct→`𝗜𝚺₁` bridge *given* `[Structure.Eq LX M]`; the open task is to *supply* it.

## The exact gap: X-congruence only
- `𝗘𝗤(LX)` (`Eq.lean:52`) = `{refl, symm, trans} ∪ {funcExt f | f ∈ LX.Func} ∪ {relExt r | r ∈ LX.Rel}`.
- `LX.Func = ℒₒᵣ.Func ⊕ Empty`, `LX.Rel = ℒₒᵣ.Rel ⊕ XRel`.
- The ℒₒᵣ-part of `𝗘𝗤(LX)` is exactly `lMap Φ 𝗘𝗤(ℒₒᵣ)`, and `𝗘𝗤(ℒₒᵣ) ⪯ 𝗣𝗔⁻` (Foundation instance,
  verified), so `lMap Φ 𝗘𝗤(ℒₒᵣ) ⊆`-provable from `lMap Φ 𝗣𝗔⁻ ⊆ paLX`.
- **The ONLY axiom of `𝗘𝗤(LX)` not covered by paLX is `Theory.Eq.relExt Xsym`** = X-congruence
  `∀ x y, x = y → X(x) → X(y)`. (`infer_instance` for `𝗘𝗤 ⪯ paLX` fails — verified.)

## Why supplying it is real but BOUNDED work (not a new heroic wall)
To make `𝗘𝗤 ⪯ paLX` hold, augment `paLX` with X-congruence (call it `paLX'`), then re-validate the
two consumers:
1. **`descentE` (gains Eq):** route through `EQ.provOf` (`Completeness/Corollaries.lean`) over
   `[Structure.Eq]`-models → `paLX' ⊨ tiSentence` → `completeness_of_encodable` → `paLX' ⊢ tiSentence`
   → `Derivation2`. SOUND: `TI prec` is closed (`freeVariables_TI = ∅`) → coerce to a `Sentence` via
   `Semiformula.toEmpty` (`emb_toEmpty` un-coerces). Plumbing: bounded/fiddly.
2. **`peano_not_proves_TI` (must survive):** `embed_TI_bounded` runs `embedC_LX_bdd` on the derivation,
   whose `hax_paLX` discharges each paLX axiom into the `PXFc`/`XFreeAx` `Z∞` carrier. Current branches:
   X-free base axioms (`𝗣𝗔⁻` image) via `provable_true_x` (needs `XFreeForm`); X-induction via
   `metaInduction_cong`. **X-congruence is NOT X-free** (it mentions `X`), so it needs a NEW
   `hax` branch: a small bounded-ordinal `PXFc` derivation of `∀ x y, x=y → X(x) → X(y)`. This is THE
   genuinely new piece — it lives in the deep `EmbeddingBound`/`EmbeddingX` (`PXFc`) machinery, but it
   is ONE simple, true, low-complexity axiom, not a girder. The `α`/cut-rank bound argument in
   `peano_not_proves_TI` is otherwise unchanged.

## Blast radius of augmenting paLX
`paLX` is referenced in `EmbeddingX`, `EmbeddingBound`, `Thm56`, `DescentLift`, `DescentSemantic`,
`ReductModel`. Augmenting its definition risks a red build across them. SAFER: define `paLX'` (or
`paLX + 𝗘𝗤`) as a *separate* theory used only on the descent/completeness path and prove a separate
`peano_not_proves_TI'` — but a derivation over the *bigger* `paLX'` cannot reduce to one over `paLX`
(X-congruence is not paLX-provable), so `peano_not_proves_TI'` genuinely re-runs the embedding with the
extra `hax` branch. Either way, step 2's new `hax` branch is unavoidable and is the crux.

## Strategic comparison (recorded for the operator's route call)
- **Completeness route (active):** remaining = {X-congruence `hax` branch (deep, bounded) + EQ.provOf
  plumbing} ∪ {opaque-blob bridge B} ∪ {descent C} ∪ {slow-down D}. Dissolves free-`X` (lap-30 win).
- **Route B (hand-build `Derivation2 paLX {TI prec}`):** sidesteps ALL the model-theoretic
  equality/`𝗘𝗤`/quotient machinery (no models, pure syntax), but is literature-gated on the precise
  calculus-internal `Goodstein ⟹ paLX ⊢ TI_≺(X)` sequent shape (`ON-LINE-REQUEST.md`). Trades the
  equality-machinery cost for a literature/derivation-construction cost.

The completeness route's equality cost is now *fully enumerated and bounded* (above), which it was not
at lap 30. Recommendation: continue completeness; next lap START step 2 (the X-congruence `hax` branch)
since it gates `descentE`, in parallel with the opaque-blob bridge B (the other hard, route-neutral
wall). Neither is a new heroic; both are bounded ports/derivations.
