# REFLECTION — lap 120 (DEEP, every-9th) · 2026-06-26

> Strong-model altitude lap. Job: take stock of the WHOLE project, not the next `sorry`.
> Build re-verified green (1326 jobs). Headline footprint re-verified IN-KERNEL this lap
> (`lake env lean`): `peano_not_proves_goodstein = [propext, sorryAx, Classical.choice, Quot.sound]`
> — **0 math axioms**. Statement faithfulness re-audited vs the paper — **no drift**.

---

## 0. Kernel facts re-verified this lap (not from docs)

| theorem | real `#print axioms` (lap 120, `lake env lean`) |
|---|---|
| `peano_not_proves_goodstein` (headline) | `[propext, sorryAx, Classical.choice, Quot.sound]` — 0 math axioms |
| `goodstein_implies_consistency` (lone open girder) | `[propext, sorryAx, Classical.choice, Quot.sound]` |
| `peano_not_proves_consistency` (Gödel-II hook) | `[propext, Classical.choice, Quot.sound]` — **CLEAN** |

**Statement audit (charter item 4).** `peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`;
`goodsteinSentence_faithful` (`Bridge.lean:34`) certifies `(ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N,
goodsteinSeq m N = 0` over the audited hereditary-base `goodsteinSeq`. The headline says exactly
Kirby–Paris. **No transcription drift.** (Matches the lap-111 audit.)

---

## 1. Is the DESTINATION still right? — KEEP.

`𝗣𝗔 ⊬ Goodstein` (Kirby–Paris 1982), fully axiom-free, via Route A (Rathjen 2014 Cor 3.7): inside
`𝗣𝗔`, `γ → PRWO(ε₀) → Con(𝗣𝗔)`, then Gödel II. A genuine landmark — a machine-checked, axiom-free
Kirby–Paris whose consistency strength is carried by an **IΣ₁-internalized** Gentzen ordinal
analysis (no prior fully IΣ₁-internal formalization of Gentzen's consistency proof exists to my
knowledge). crux-1 (`γ → PRWO`) is DONE + axiom-clean (lap 57). crux-2 (`PRWO → Con`, internalized
cut-elimination on V-codes) is the wall. **No new information changes the endpoint. KEEP.**

---

## 2. THE FINDING — the genuine crux is the SELECTION/STALL defect, not the inversion, and it is unresolved.

### 2a. What the last 9 laps (112–119) actually did — real progress on the inversion.
Laps 112–119 attacked the **critical-cut INVERSION** (`ZDerivation_red_zK_crit`) — the piece lap-111
named "the avoided prize, ≈0% done." That work succeeded: the inversion SOUNDNESS is now PROVEN on
**both polarities** (`ZDerivation_iRcritG_corrected` ∀ via `critReductCorr`; `ZDerivation_iRcritGNeg_corrected_neg`
¬), grounded in Buchholz §5 cases 2.1/2.2, all axiom-clean. This is the most important math advance
of the run and it is real. **KEEP it.**

### 2b. The drift (laps 117–119) — the work slid from "prove the inversion" into "perform the swap."
With the inversion proven, the focus became the **atomic engine swap** (re-key `red`'s critical value
`iRKc → iRKcCrit`). It has re-scoped three times: lap-117 "pure wiring" → lap-118 "3 downstream
consumers" → lap-119 "the O1/regularity front was entirely OMITTED; budget a whole lap for the
descent re-key." This is bounded engineering (wiring banked lemmas), but it is soaking laps on
plumbing while the genuinely-hard, genuinely-open question sits untouched (2c).

### 2c. The genuine open crux — `red` can STALL on the ⊥-orbit, so `false_of_ZDerivesEmpty` cannot close.
The endgame `false_of_ZDerivesEmpty {z} (hz : ZDerivesEmptyR z) : False` (`Crux2Blueprint:1144`) is a
**bare sorry**. Its docstring asserts it "closes either way": a `red`-fixpoint on a ⊥-orbit is a
cut-free `∅→⊥` derivation (absurd), else the orbit is an infinite ε₀-descent (PRWO forbids it). The
lap-111 §3a disjunctive reformulation (`iord_descent_red : red d = d ∨ iord ≺`) IS in place and made
that lemma green — **but only by closing the stall branches on the LEFT disjunct (`Or.inl`) and
DEFERRING the absurdity to `false_of_ZDerivesEmpty`, which has never been built.**

The repo states the defect in its own words (`RedZKDescent.lean`, above `red_zK_fixpoint_of_atom_selected`):

> "when `permIdx` selects an atom, `iord (red (zK s r ds)) = iord (zK s r ds)` — NO strict descent, the
> orbit STALLS. The `isymRep` tag conflates atoms (normal forms) with reducible Ind/chains, and `iperm
> isymRep` is unconditionally true, so an atom CAN be the first permissible premise. The fix is an
> `isPermPrem`/`permIdx` engine refinement that excludes atom premises, OR an embedding
> (`foundation_bot_to_Z_empty`) that produces atom-free chains."

So the stall is **known, real, and unresolved**. The disjunctive reformulation did not FIX it — it
RELOCATED it into the `false_of_ZDerivesEmpty` sorry. Concretely, the LEFT-disjunct endgame needs:

- **(A) fixpoint-absurdity / selection-correctness:** `red w = w ∧ ZDerivesEmptyR w ⟹ False` — a
  `red`-fixpoint on the ⊥-orbit is impossible. **0% built. Possibly the hard core.**
- **(B) no cut-free `∅→⊥`** — standard, 0% built.
- **(C) descent-internalization:** `gentzenDescentφ` as the real Σ₁ graph of `n ↦ iord(red^[n] z)`.
  Plausibly routine Σ₁-recursion in IΣ₁ (one fixed Σ₁ function `red`, internally iterable). Lower risk.

### 2d. Why this is THE crux, and why the swap does not address it.
The inversion+swap make the critical reduct SOUND. But soundness of the reduct does **not** make the
orbit TERMINATE at a contradiction: `red` can fixpoint on an atom-selected ⊥-orbit K-node (the node is
still a tag-4 cut), so the descent stalls and `false_of_ZDerivesEmpty` has no closer. **The
selection/stall defect — first diagnosed in-kernel at laps 104 and 107 ("engine `red` dispatches only
on the top `zTag`, stalls after one K-reduction; redesign `red` to find+reduce the lowest cut") — is
the SAME defect, still open 13 laps later.** Laps 108–119 addressed reduct soundness (a different
sub-problem) and the lap-111 reformulation made the descent lemma green without resolving the stall.
This is the thing the grind laps cannot see from inside the trees: **the project is polishing reduct
soundness while the load-bearing TERMINATION question — does `red`'s cut-elimination actually reach a
contradiction on `∅→⊥`? — remains unconfronted.**

---

## 3. What a sharp outside expert would say we're MISSING.

**Confront (A) directly — it is the cheapest, highest-information, highest-risk open obligation.**
The faithful Gentzen/Buchholz reduction always reduces a genuine cut (Buchholz Def 3.2: the lowest
cut), never selects a normal-form leaf as the redex. The engine's `permIdx` ("first premise with
`iperm isymRep`") is unfaithful: `iperm isymRep` is unconditionally true, so atoms qualify. There are
three candidate resolutions, in increasing cost:

1. **Vacuity (best case):** on the ⊥-orbit, an atom/`zAx1`-selected K-node is **directly absurd** by
   sequent shape — a Rep node "promotes" its selected premise's sequent to the conclusion `∅→⊥`, but an
   atom axiom's sequent (a literal/¬literal pair, or the structured `zAtom` form) cannot equal `∅→⊥`.
   If provable, (A) closes **without engine surgery**, the lap-111 fixpoint branches become vacuous
   (like axAll/axNeg already are via Cor 2.1), and the stall defect is dissolved. **Attempt this first.**
2. **Orbit invariant (option 2 in the repo's own note):** M2's embedding produces ⊥-derivations whose
   selected spine is atom-free, and `red` preserves that invariant. Principled but a real threading task.
3. **Engine refinement (option 1; the lap-104/107 plan):** refine `permIdx`/`isPermPrem` to select only
   reducible premises (a genuine cut). Most faithful to Buchholz, but an atomic engine change.

`ZDerivesEmptyR w` carries `ZRegular w` (regularity) — worth probing whether regularity already
excludes the stall (the lap-119 O1 work may be the lever).

**Why (A) over the swap, by the charter's own hardest-first rule:** hardest-first attacks the piece
whose *feasibility is in real doubt*. The swap's feasibility is NOT in doubt (it wires banked
lemmas). (A)'s feasibility IS in doubt — the repo flags it as a defect with no built resolution. So
(A) is strictly higher-value. And (A) is **decisive either way**: prove it → de-risk the whole
endgame (the engine terminates correctly) + supply the `false_of_ZDerivesEmpty` LEFT-closer; refute it
→ the single most important fact about the project (forces a selection-architecture fix BEFORE more
swap investment). The swap does not go stale; (A) gates whether the swap is even worth finishing.

**Secondary (do not lose):** M2 (`foundation_bot_to_Z_empty`) and (C) (`gentzenDescentφ` realization)
are the two ENDS that wire crux-2 to the headline; both are bare sorries at ~0% after 119 laps. They
are labelled "plumbing" in the blueprint but that label is UNVERIFIED. (C) is probably genuine Σ₁
plumbing (one fixed function's internal iteration). M2 is a real embedding. Neither should be assumed
trivial; both are downstream of (A) being resolved (an embedding that "produces atom-free chains" is
literally option-2 of (A)).

---

## 4. The call.

**KEEP:** the destination (axiom-free Kirby–Paris); the proven inversion soundness (laps 112–119); the
Σ₁ engine `red`/`iord` carrier; the disjunctive `iord_descent_red`.

**STOP:** treating the atomic engine swap as the SOLE next target and pouring whole laps into its
fragmenting fronts (O1 / descent re-key / soundness) before the endgame is de-risked. **STOP** writing
docstrings that assert `false_of_ZDerivesEmpty` "closes either way" while its LEFT-disjunct content
(A)+(B) is unbuilt and the stall it depends on is a flagged, unresolved defect.

**DO, in order:**
1. **(highest value, decisive)** Confront **(A)** `red w = w ∧ ZDerivesEmptyR w ⟹ False`. Attempt the
   vacuity resolution (§3.1) first: show an atom-/`zAx1`-selected K-node concluding `∅→⊥` is absurd by
   sequent shape, building on `red_zK_fixpoint_of_atom_selected` / `red_zK_fixpoint_of_zAx1_selected`
   and the Cor-2.1 selection invariant (`tp_selected_isymRep_of_emptyAnt_botSucc`). Probe whether
   `ZRegular` already kills it. Land it as `no_red_fixpoint_of_ZDerivesEmptyR` (or find the wall).
2. **(then)** Finish the engine swap (now de-risked / known to matter) → `redSound` → the RIGHT
   (infinite-descent) disjunct of the endgame.
3. **(then)** Build (C) the `gentzenDescentφ` Σ₁ realization + assemble `false_of_ZDerivesEmpty` from
   (A) [LEFT] + the descent+PRWO [RIGHT].

**Single highest-value next target:** **(A)** — the fixpoint-absurdity lemma. It is contained,
additive (does not disturb the green `iord_descent_red`), on the M3 critical path, independent of the
swap, and it tests the deepest unverified assumption in the entire crux-2 architecture: *does the
internalized cut-elimination actually terminate to a contradiction, or does it stall?* That question
has been deferred since lap 104. It is time to answer it.

---

## 4b. Post-synthesis scouting on (A) — kernel-grounded: the VACUITY route fails, the fix is axiom-cut elimination.

After committing the synthesis I scouted (A) in the engine. The hoped-for "vacuity" resolution (§3.1) is
**refuted by the definitions**:
- Cor 2.1 (`tp_selected_isymRep_of_emptyAnt_botSucc`, `InternalZ:7593`) forces the selected premise to be
  `tp = isymRep`; atom & `zAx1` qualify (axAll/axNeg are already vacuous since `tp = isymLk ≠ isymRep`).
- Leaf-soundness (`zTag_reducible_of_emptyAnt` / `zTag_Ind_or_K_of_ZDerivesEmpty`, `InternalZ:8377/8480`)
  excludes axiom leaves with **empty** antecedent. But the selected premise has its own sequent `sᵢ`, and
  `isChainInf` (`InternalZ:1177`) permits premise antecedents to contain CUT formulas:
  `∀ B, inAnt B (chainAnt ds i) → inAnt B (seqAnt s) ∨ ∃ i'<i, B = chainAsucc ds i'`. With `seqAnt s = ∅`,
  premise antecedents are exactly the `chainAsucc` (cut) formulas.
- Hence a selected atom `zAtom sᵢ` can be a **valid axiom `B→B`** (`seqAnt sᵢ = {B}`, `seqSucc sᵢ = B =
  chainAsucc`), satisfying atom-validity `inAnt (seqSucc sᵢ) (seqAnt sᵢ)`. Its antecedent is NOT forced
  empty. **The stall is genuinely reachable in the engine's type system; `false_of_ZDerivesEmpty` is
  unprovable as the engine stands.**

**This sharpens the finding from "possibly false" to "kernel-confirmed reachable," and identifies the
faithful fix:** a selected axiom premise `B→B` is a cut **against an axiom**, which Gentzen ELIMINATES
(the cut vanishes, leaving the matching `B`-succedent premise). The engine's Rep-reduce is the IDENTITY
there (`tpReduce_isymRep`), so it stalls. The fix is to **extend `red` to reduce axiom-cuts** — exactly the
laps-104/107 "find+reduce the lowest cut" redesign, now pinned to the precise mechanism (axiom-cut not
eliminated). Selection-refinement alone is insufficient (the B-cut must still be reduced); an M2 atom-free
orbit invariant is fragile. So the next lap is not a quick lemma but a contained engine addition (the
axiom-cut reduction), and it is the genuine remaining content of crux-2's termination.

## 5. Pacing / meta.

Laps 104/107 diagnosed the stall; laps 108–119 built around it (real inversion progress) without
resolving it; lap 111's reformulation made the descent lemma green by relocating the stall into an
unbuilt sorry. That relocation is exactly why the defect became invisible to the grind — the build is
green, the descent lemma is "done," and the open piece looks like routine M3 plumbing. It is not.
After this synthesis commits, resume the grind on target (1), not on the swap.
