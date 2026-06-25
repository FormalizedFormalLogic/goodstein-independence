# NEXT STEPS — corrected priorities (lap 101 DEEP REFLECTION)

> Set by the lap-101 reflection. Supersedes the laps-95–100 "drive the `redZKReady` motive" plan as the
> default. Rationale: `REFLECTION-2026-06-25-lap101.md`. The destination (`𝗣𝗔 ⊬ Goodstein`, axiom-free) and
> the crux-2 target (`redSound`, internalized cut-elimination) are UNCHANGED. What changed is the sub-route
> call: the finitary-vs-ω-rule fork is reopened because lap-95's Path-X commitment skipped the de-risk
> spike lap-92 said to run first, and laps 95–100 relocated the wall rather than dissolving it.

## ▶ PRIORITY 1 — run the skipped de-risk spike (settles the fork)

**Target: `wip/InternalZomega.lean`** — a SELF-CONTAINED spike (NOT imported by `GoodsteinPA.lean`; cannot
affect the green gate). Goal: confirm in-kernel that the internal ω-rule cut-elimination is
substitution-free, so the finitary-vs-ω-rule decision is made on EVIDENCE.

Concretely (against the real `InternalZ` API):
1. **Define the internal ω-rule ∀-node** `zAllω s x h` — `s` the conclusion sequent `Γ→∀x F`, `h` a Σ₁
   CODE for the premise family. Premise-`n` := `zsubst h x (numeral n)` (reuse the axiom-clean `zsubst`;
   this is Buchholz §6 `Z*`: `h[n] = h₀(x/n)`). The validity predicate asserts `∀ n, ZDerivation
   (premise n) ∧ fstIdx (premise n) = seqSetSucc Γ F(n)` — i.e. the premise family is ASSUMED valid.
2. **Define the critical-cut reduct** on a cut `∀x F` (R-side `zAllω`) vs its L-side: the reduct SELECTS
   premise `t` (the cut term/witness) = `zsubst h x (numeral t)` = `premise t`. No NEW substitution in the
   reduction step (the `zsubst` lives in the premise-family DATA, where validity is given).
3. **State + try to prove the key lemma:** the reduct of a cut on `∀x F` is a `ZDerivation` whose
   conclusion is `tpReduce`-correct, with NO appeal to `ZDerivation_zsubst`/eigenvariable-substitution
   validity (contrast the finitary route, where O2 is the wall). Even getting this to ELABORATE (bodies
   sorried, signatures pinned against `InternalZ`) is the evidence: it shows IΣ₁ can express the ω-rule
   node + reduct.
4. **The sharp arithmetization-risk probe:** does cut-elimination recursion on `iord` work when the
   ∀-node's "size"/ordinal is a sup over the premise family? Check `iord (zAllω …)` is definable from the
   premise-family code (the repo's `iord`/ω-tower engine should supply `sup`/successor). If `iord` can't
   be assigned to the ω-node, that is the wall — and it justifies committing to Path X.

**Decision rule:** spike elaborates clean + reduct substitution-free + `iord` assignable → **PIVOT to
Path C** (rebuild the Z object theory on `zAllω`, retiring the finitary obligation list
motive/axNeg/Ind/5.1/5.2.1/ordinal-K at once; reuse the ordinal engine + `zsubst` + `Zinfty` template).
Spike walls on the Σ₁ arithmetization → **commit to Path X** with the evidence that finitary is the only
feasible internal route, and resume PRIORITY 2.

**Template to mirror:** `src/GoodsteinPA/Zinfty.lean` (the axiom-clean META ω-rule engine: `allω` rule +
the full Towsner §19 cut-elimination). The spike arithmetizes what `Zinfty` does at the meta level.

**STATUS (lap 101 — `wip/InternalZomega.lean`, 4 lemmas, all axiom-clean):**
- `zOmegaPrem_valid` — premise family uniformly valid, motive-free (freshness bound only).
- `zOmegaPrem_concl` — selected premise's conclusion computed, not threaded.
- `iord_zOmegaPrem` / `iord_zOmegaPrem_constant` — **Probe 1 RESOLVED**: premise-family ordinal is CONSTANT
  `= iord d0`, so the ω-node's `iord = iord d0 + 1` is finite — no sup-over-infinite-family primitive. The
  arithmetization-risk concern is retired.

**NET CALL: the evidence now favours the Path-C pivot.** The two ω-node hard properties (motive-free
validity, finite ordinal) are in-kernel on the EXISTING engine, and they are exactly what the finitary
route turns into the open `redZKReady` motive + `iord_descent_red` K-case. **NEXT = Probe 2 / the pivot
decision:** the ω-rule cut-elimination STEP needs the ω-node DATATYPE (new tag 7 `zAllω` in the
`zconstruction` Fixpoint) + `ZPhi`/`iord`/`tp` extension — the ~2–3k-line but TEMPLATED rebuild
(`Zinfty.lean` = meta template; the two hardest sub-questions answered above). Recommended next lap: build a
minimal `zAllω` datatype + its `red`/`iord` recursion equations as the final de-risk, then commit to the
pivot. If that minimal datatype walls (Fixpoint `StrongFinite` issues for an infinite-premise node — the
lap-92-flagged risk), THAT is the signal to commit to Path X instead.

## ▶ PRIORITY 2 — Path X fallback (ONLY if the spike walls)

Resume the laps-95–100 plan, now informed: drive the `redZKReady` motive (`Crux2Blueprint.redSoundGen`
K-case `sorry`). First sub-lemma: `redZKReady_of_emptyAnt_botSucc` (∅→⊥ special case). The open core is
the hereditary Rep-reduction `fstIdx (red dᵢ) = fstIdx dᵢ` down the selected-premise spine — **but first
settle whether it even holds**, given ∅→⊥ chain premises have growing antecedents `{A₀..A_{i-1}}→Dᵢ` (so
Cor 2.1 does not directly reapply). If it does not hold as stated, the motive must track a different
invariant — which is itself evidence for the Path-C pivot. Then: axNeg ¬-cut, `zKValidF_iIndReduct_of_zInd`
(Ind), `ZDerivation_red_zK_crit` (5.1), `ZDerivation_red_zK_splice` (5.2.1), `iord_descent_red` (ordinal K).

## ▶ PRIORITY 3 — path-independent downstream (no-regret, either route)

These are needed regardless of finitary/ω-rule and can advance in parallel once the Z object theory is
stable. They consume the SHAPE of `ZDerivation`/`ZDerivesEmpty`/`iord`, so do them AFTER the fork is
settled (a Path-C pivot reshapes `ZDerivation`):
- **M2 `foundation_bot_to_Z_empty`** (`Crux2Blueprint`) — the Bryce–Goré `Peano.v` Foundation→Z bridge
  (the PA-induction axiom maps to Z's native `Ind`). ~1k-line milestone.
- **M3 `false_of_ZDerivesEmpty`** (`Crux2Blueprint`) — internalize the descent `n ↦ iord (red^[n] z)` as
  a Σ₁ graph + apply `PRWO(ε₀)` (from crux-1). Plumbing; structure is path-independent.
- **Wire** `Crux2Blueprint` M1b∘M2∘M3 → `Reduction.goodstein_implies_consistency` → headline (only when
  `#print axioms` is clean — anti-fraud).

## Faithfulness invariant (do NOT regress)
Headline stays a bare `sorry` until `#print axioms peano_not_proves_goodstein` is trust-base only. Never
introduce an `axiom` for the ordinal-analysis girder. Keep `goodsteinSentence_faithful` axiom-clean.
