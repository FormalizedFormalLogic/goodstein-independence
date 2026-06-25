# Lap 95 (FRESH-MIND REVIEW) — the wall is a SURGICAL dispatch gate, not a 2–3k-line ω-rule pivot

> **✅ UPDATE (same lap, after the synthesis below): the gate is LANDED IN-KERNEL.** `iRK` is now gated
> on `zTag dᵢ = 4` (`InternalZ.lean`), `red_zK_splice` gains `htag`, new `red_zK_rep_nonchain`, and
> **`ZRegular_red_zK` is UNCONDITIONAL** (`hseltag` dropped, `#print axioms = [propext, choice,
> Quot.sound]`). Build 🟢 1325, headline `[propext, sorryAx, choice, Quot.sound]` unchanged. The lap-94
> regularity wall is cleared. The de-risk `wip/` spike was removed (promoted to src/). Remaining = the
> validity half (`tpReduce` conclusion-reduction) + `iord_descent_red` (steps 3–4 below).

> Build 🟢 green (`lake build GoodsteinPA`, 1325). Headline
> `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]` (0 math axioms;
> `sorryAx` traces the lone math `sorry` `goodstein_implies_consistency` = crux-2 = `redSound`).
> `peano_not_proves_consistency` fully clean. All re-verified in-kernel this lap (`lake env lean`).

## TL;DR — direction KEPT, sub-route framing CORRECTED

The destination (crux-2 = `redSound` = internalized Buchholz cut-elimination) is right and unchanged.
The **sub-route** picture in the lap-92 reflection / lap-94 handoff is **overstated as a "Path X
finitary vs Path C ω-rule, ~2–3k-line rewrite" fork.** Reading the actual kernel state this lap
dissolves that fork:

- **O2 is DONE.** `ZDerivation_zsubst` (`Zsubst.lean:1855`, axiom-clean, in the build) is exactly the
  benign, criticality-free eigenvariable-substitution lemma: `ZDerivation d → maxEigen d < a →
  ZDerivation (zsubst d a t)`. The route-B reducts `ZDerivation_zsubst_zIall_premise` /
  `_zInd_premise1` consume it. The "substitution preserves validity" wall that laps 78–91 circled is
  **already discharged** (the lap-78 obstruction was the *criticality* conjunct, which `ZPhi` dropped
  when it moved to criticality-free `zKValidF`; see the in-file note `Zsubst.lean:2010-2022`).

- **O1 is DONE except one leaf.** `ZRegular`/`zReg` freshness tracking through `red` (laps 93–94) is
  complete for the non-`zK`, replace, and critical branches. `ZRegular_red_zK` (`Zsubst.lean:1788`) is
  **fully proved modulo a single hypothesis `hseltag`** — it is *not* a `sorry`, it is a clean lemma
  waiting for one true fact.

- **The actual wall is ONE false hypothesis.** `hseltag` says the splice-branch selected premise
  `dᵢ = znth ds (permIdx (zK s r ds))` is a chain (`zTag dᵢ = 4`). It is **false under the current
  `iRK`** (proved in-kernel, `not_permIdx_lt_zKseq_zAtom`): `iRK`'s inner sub-dispatch
  (`InternalZ.lean:6108`) splices when `¬ permIdx dᵢ < lh (zKseq dᵢ)`, and for a *non-chain* `dᵢ`
  (atom/I-rule/axiom) that sentinel is `0 < 0 = false`, so the splice fires by default on non-chains.

## The fix is surgical, not architectural

`iRK`'s splice/replace sub-dispatch is wrong only in its *condition*, not its branches. Gate the splice
on the selected premise genuinely being a **critical chain**:

```
iRK d s :=
  if permIdx d < lh (zKseq d) then
    (if zTag dᵢ = 4 ∧ ¬ (permIdx dᵢ < lh (zKseq dᵢ))   -- dᵢ is a CRITICAL CHAIN
     then iRKs d s                                       -- 5.2.1 splice (genuine reduct-halves)
     else iRKr d s)                                      -- 5.2.2 replace (non-chain, or non-crit chain)
  else iRKc d s                                          -- 5.1 critical
   where dᵢ = znth (zKseq d) (permIdx d)
```

Behaviour is **identical for chain selected premises**; it changes *only* non-chain selected premises,
routing them from the (junk) splice to the replace — which is **exactly Buchholz Def 3.2 case 5.2**:
the 5.2 reduct branches on the inference SYMBOL `tp(dᵢ)` of the selected premise, and an
atom/I-rule/axiom is the replace case 5.2.2 (`d[n] := K^r_{tp(dᵢ)(Π,n)}(i/dᵢ[n])`), never the 5.2.1
splice. With this gate, the splice branch's defining condition **contains** `zTag dᵢ = 4`, so `hseltag`
becomes *derivable* (trivially true on that branch) and `ZRegular_red_zK` becomes usable by `redSound`.

### Why this is sound = the ω-rule "selection" reading (Path C, but cheaply)

The lap-92 reflection's ω-rule insight is *correct and reused* — as the JUSTIFICATION, not a rewrite.
In an ω-rule node `∀xF` is introduced from a premise family; a critical cut **selects** the witness
premise `dₙ` (already deriving `Γ→F(n)`) rather than substituting an eigenvariable. The repo's `zIall`
node already stores its premise `d0 ⊢ Γ,F(a)` as a bounded subterm; the reduct `red`'s I∀ case
SELECTS the substituted premise `zsubst d0 a n` whose validity is the now-proven O2
(`ZDerivation_zsubst`). So the finitary engine, read through the ω-rule lens, IS selection-based — no
new node, no new `Fixpoint`, no 2–3k-line `InternalZomega.lean`. (And the naive ω-node would anyway
*break* the `Fixpoint.StrongFinite` discipline — its infinite, size-unbounded premise family is not a
collection of bounded subterms; the bounded-generator design is forced, and that design is just
`zIall` + a derived benign-substitution lemma = what we already have.)

## Blast radius of the in-place `iRK` change (why it gets a `wip/` spike first)

Changing `iRK`'s splice condition touches: `iRK`/`iRKDef`/`iRK_defined` (InternalZ), `fstIdx_iRK` /
`zTag_iRK` (trivial — all branches preserve), the computation eqns `red_zK_rep` / `red_zK_splice`
(Zsubst 1654/1669 — hypotheses change), `ZRegular_red_zK` (the `hseltag` hypothesis is dropped), and
**`Crux2Blueprint.lean`** (compiled, sorry-holding: its `ZDerivation_red_zK_dispatch` calls
`red_zK_rep h1 h2` / `red_zK_splice h1 h2`). The `iord`-descent lemmas are NOT in the radius: the
per-branch descent facts are stated about `iRKs`/`iRKr`/`iRKc` in isolation, and `iord_descent_red`
is still an open `sorry` (the *assembly* is what consumes the dispatch). Per the lap-92 de-risk
doctrine and the lap-94 caveat, the `iRK` def-change gets a `wip/InternalZdispatch.lean` spike
(gated dispatch + dispatch eqns + the regularity assembly with `hseltag` derived) before the in-place
edit lands.

## After the dispatch fix — the genuinely deep residual (correctly localized)

The dispatch fix closes the **regularity (O1) half** of "red preserves valid+regular". The remaining
deep content is the **validity half**: `red` preserves `ZDerivation`, with the **conclusion reduced by
`tpReduce`** (the route-B `tp(dᵢ)(Π,n)` conclusion-tracking, `tpReduce` already Σ₁-def'd at
`InternalZ.lean:1064`). The lap-90 finding stands: a `red` that keeps `fstIdx = Π` is faithful only
for `tp = Rep`, so the conclusion-reducing replace is mandatory in the validity half. That + assembling
`iord_descent_red` (`icmp (iord (red d)) (iord d) = 0`) and wiring `Crux2Blueprint →
false_of_ZDerivesEmpty → goodstein_implies_consistency → headline` is the multi-lap road. But it is now
correctly scoped: **not blocked on a substitution wall (done) nor on an unfaithful dispatch (this fix),
but on the honest cut-elimination conclusion-tracking + ordinal descent.**

## Next actions (see PENDING_WORK.md)
1. `wip/InternalZdispatch.lean` spike: gated `iRKfix` + Σ₁-defn + invariants + dispatch eqns + the
   regularity assembly closing `hseltag` (this lap).
2. Port the gated dispatch in-place into `iRK` (InternalZ) + fix `red_zK_rep`/`red_zK_splice` +
   `ZRegular_red_zK` (drop `hseltag`) + `Crux2Blueprint` dispatch; green `lake build`.
3. Validity half: rewire the replace branch to emit `tpReduce (tp dᵢ) Π n`; prove
   `ZDerivation_red_zK_rep`/`_splice`/`_crit` (Crux2Blueprint sorries) on the reduced conclusions.
4. `iord_descent_red` + assemble `false_of_ZDerivesEmpty` → headline.
