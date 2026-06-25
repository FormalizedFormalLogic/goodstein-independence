# Lap 92 — CORRECTION: the "lap-78 substitution wall" is GONE; O2 was misattributed

## What I verified in-kernel this lap

1. **`ZPhi` (the `ZDerivation` fixpoint operator, `InternalZ.lean:5008`) already uses `zKValidF`** in
   its `zK` clause: `… ∧ zKValidF s r ds` — **criticality-free** (lap-82's re-point is live).
2. **`ZDerivation_zsubst` (`Zsubst.lean:834`) is green in the build** and its conclusion is
   `ZDerivation (zsubst d a t)` for the *current* (`zKValidF`-based) `ZDerivation`. So **`zKValidF` is
   already proven preserved under (closed-term) substitution** — for the `d ≤ a` (fresh-slot) case.

## The correction

Lap-78 (`ANALYSIS-2026-06-24-lap78-…`) declared the non-vacuous generalization of `ZDerivation_zsubst`
**impossible**, via two counterexamples CE-1/CE-2. **But both counterexamples attack ONLY the
criticality conjunct** `∀ i, ¬ iperm (tp dᵢ) s` (a *formula-inequality*, broken by the non-injective
`fvSubst`). Lap-82 then proved criticality is a **separable** factor (`zKValid = zKValidF ∧ zKCritical`)
that does **not** belong in Buchholz validity, and re-pointed `ZPhi` to `zKValidF`. **⟹ CE-1/CE-2 no
longer apply to the current `ZDerivation`.** The lap-78 wall is dissolved.

Lap-91's **O2** ("eigen-subst is the lap-78 substitution wall, THE genuine next deep target") is therefore
**mislabeled**. It is *not* the lap-78 criticality wall. It is a much narrower, plausibly tractable gap:
the existing `ZDerivation_zsubst` is gated on `d ≤ a` (fresh *large* slot), and the I∀/Ind/critical
reducts need to substitute the **eigenvariable** `a` (small, occurring in `d`). Substituting a **closed
numeral never captures**, so the only obstruction is ensuring inner eigenvariables `e ≠ a` — a
**regularity** hypothesis (`aNotEigen d`), not the `d ≤ a` bound and not criticality.

## The real residual: the O1 ↔ O2 freshness/eigensubst COUPLING (intrinsic to finitary ∀)

The eigensubst lemma (O2) needs `aNotEigen d` (the substituted eigenvariable is not an inner
eigenvariable). To **establish** `aNotEigen` for the derivations route B feeds, the `ZDerivation`
predicate must **track eigenvariable regularity/freshness** — which `zIallWff`/`zIndWff` currently do
**not** (this is exactly **O1**). And that invariant must be **maintained through reduction**. So O1 and
O2 are one coupled obligation, and it is **intrinsic to the finitary eigenvariable presentation**:
finitary ∀-intro *has* eigenvariables, so it *needs* freshness tracking + capture-free instantiation.

## Consequence for the route decision (refines `REFLECTION-2026-06-25-lap92.md`)

There are now TWO honest multi-lap paths; the ω-rule case is **strengthened, not weakened**, by this
correction (it eliminates the very design that creates the O1↔O2 coupling):

- **Path X — stay finitary, fix O1+O2.** (a) Strengthen `zIallWff`/`zIndWff` with an eigenvariable-
  freshness clause and thread it through the fixpoint + reduction (O1). (b) Prove
  `ZDerivation_zsubst_eigen` (substitute the eigenvariable by a closed numeral, `aNotEigen`+regularity
  hypothesis, preserving `zKValidF`) (O2). **Lower architectural risk** (reuses everything, no rewrite);
  the lap-78 obstruction is genuinely removed, so this is no longer known-blocked. **Risk:** maintaining
  the freshness invariant through `red` may itself be fiddly, and route B's conclusion-tracking
  (`tpReduce`) still has to be carried.
- **Path C — pivot to the ω-rule.** No eigenvariables ⟹ O1 and O2 both vanish, and `tpReduce` is
  automatic (the n-th premise already concludes `Γ→F(n)`). **Higher one-time cost** (rebuild ∀/Ind over
  Buchholz §6 `Z*` notations, `iord`-recursion), **but** follows the proven `Zinfty.lean`/Bryce–Goré
  design and removes the whole coupling permanently. **Risk:** the §6 `Z*` arithmetization in IΣ₁ is new.

## NEXT — the de-risk spike now has a sharp first probe

**Probe Path X's O1 cost FIRST (cheapest decisive test):** strengthen `zIallWff` with an eigenvariable-
freshness clause in a `wip/` copy (or behind a flag) and measure the blast radius on the `ZPhi`
producers/consumers + `Δ₁`-definability. If O1 is a localized add → Path X is the cheaper unblock, drive
`ZDerivation_zsubst_eigen` next. If O1 cascades through the fixpoint/reduction → Path C (ω-rule) wins;
build the `wip/InternalZomega.lean` spike. **Either way, STOP describing O2 as "the lap-78 wall."**
