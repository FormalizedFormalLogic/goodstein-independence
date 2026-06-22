# REFLECTION — 2026-06-22 (lap 9, deep-reflection lap)

A step-all-the-way-back lap. No proof mechanics until the synthesis is written. This is the
deliverable. Read with `STATUS.md` (refreshed this lap) and the rewritten `HANDOFF.md`.

---

## 1. Is the destination still right? — YES, unchanged.

**Target:** `Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence` (Kirby–Paris 1982),
axiom-clean. Verified faithful this lap: the headline negates provability of the sentence whose
standard-model meaning the `Bridge.lean` certificate pins to *exactly* `∀ m, ∃ N, goodsteinSeq m N = 0`
over the audited hereditary-base `bump`/`goodsteinSeq` (`Defs.lean`). `𝗣𝗔 = Peano` over `ℒₒᵣ`, `⊬` is
Foundation's unprovability. No transcription drift. The statement says what the paper says.

It is worth it: **net-new in Lean** (mathlib has no Goodstein at all; the Isabelle/Coq formalizations
cover *termination*, explicitly "without reference to PA"). The honest realistic endpoint, near-to-medium
term, is **not** a fully axiom-clean headline — it is *a built remainder with the headline reached modulo
a few well-isolated, clearly-cited girder sorries* (M4 embedding, the bounding bridge). That is a
legitimate, valuable endpoint and I state it plainly. The fully-clean headline is a multi-month tail.

`#print axioms` re-confirmed this lap (real output, not recalled):
- headline: `[propext, sorryAx, choice, Quot.sound]` — honest open `sorry`, **0** math axioms. ✓
- `goodsteinSentence_faithful`, `goodsteinTerminates_re`, `cutElim` (M5): trust base, clean. ✓
- `lowerBound_hardy_selfcontained` (M6): trust base + 12 🟢 `native_decide` Goodstein base-case `ax_*`. ✓
- `not_proves_of_implies_consistency` (Route A): + `PA_delta1Definable` (🟡, **Route A only**). ✓

## 2. Are we attacking the highest-value thing? — NO. Course-correct.

**The drift.** Laps 6 → 7 → 8 built *three* successive witness-bounded cut-elimination calculi —
`BoundedZinfty` (single `k`) → `SplitZinfty` (`(k,d)`) → `OperatorZinfty`/`Zekd` (control ordinal
`(e,k,d)`) — each abandoned when §19.6 `cutReduceAll`'s commuting ω-rule case resisted, each replaced by
a more elaborate index. ~3 laps, ~140 KB of `wip/`, all circling the same block.

**The verdict (two independent confirmations).** The lap-8 findings doc
(`archive/findings/…omega-rule-commuting-bound.md`) *proves* the §19.6 commuting bound **cannot close in
any single-numeric-index system** (the Hardy inequality is literally false; Towsner hand-waves the case)
and documents that the literature (Buchholz §5, Schwichtenberg–Wainer Ch.4) **never threads the witness
index through cut-elimination** — it runs two phases. The cross-lap landscape memory
(`reference/goodstein-independence-landscape.md`) independently records that for M5 "**the Hardy `k`
index was NOT needed for cut-elim**." So the entire witness-bounded-cut-elim thread was off the critical
path the whole time. M5 (witness-FREE cut-elim) has been done & axiom-clean since **lap 3**.

**The thing that actually sat untouched.** M4 — the embedding `PA ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}` — has been at
"recon done lap 6" for *eight laps*. And it is the **universal bottleneck**: it is required on Route A,
on the two-phase Route B, *and* even on the abandoned Zekd route. There is **no path to the headline that
does not go through M4.** The treadmill bagged the tractable-but-off-path cut-elim bookkeeping while the
one unavoidable deep girder went unattacked. Classic fixation + sunk cost.

## 3. What a sharp outside expert would say we're missing

**(a) The two-phase pivot is right — adopt it fully, don't half-keep the Zekd thread.** The lap-8 handoff
correctly identified the two-phase architecture but still left `Zekd cutReduceAllAux` (6/11 cases) as a
"banked alternative ~80% odds." Drop it to *reference only*. Keeping it warm invites the next grind lap to
"just finish those 5 cases" — straight back into the rabbit hole. The 80% has a *known* failure mode
(a commuting case forcing `e` to depend on `n`) and reuses *less* done work than the two-phase route.

**(b) Named architecture seam: M5 and M6 were built on incompatible substrates.** M5 (`src/Zinfty.lean`)
is over mathlib **`Ordinal.{0}`** + real **`SyntacticFormula ℒₒᵣ`**. M6 (`src/LowerBound.lean`) is over
**`ONote`** + an abstract **`GForm`** (`atom m n`/`gEx n`/`gAll`). The "bridge" therefore crosses *two*
seams at once — an ordinal-representation seam and a language seam — on top of the witness read-off. The
lap-8 framing of it as "the clean small connector" was over-optimistic. It is a real, multi-step girder.

**(c) The decomposition that shrinks the bridge.** M6 actually contains *two* separable things:
  1. `hardy_lt_goodsteinLength` / `hardy_comp_lt_goodsteinLength` — **pure ℕ-domination facts**
     (`hardy α N < G(N)` eventually). `ONote`-based but they are statements about `ℕ → ℕ` functions.
     **Directly reusable.** This is the reusable *core* of M6.
  2. `lowerBound_hardy_selfcontained : ¬ B α k {gAll}` — the bounding argument re-done over the *abstract*
     `B` calculus, built before M5's cut-free output existed in usable form.
  **Reframe the bridge:** prove the bounding lemma **directly on M5's real cut-free `Deriv`** (invert the
  ∀ via `allInv`, read the `exI` witness numeral off the cut-free structure — no `+α` growth, that *is*
  the point of cut-freeness), yielding witness `≤ hardy (toONote α) N`, then combine with fact (1). Do
  **not** transport M5's output into the abstract `B`. The `B` lower bound becomes the *template* for this
  induction — a banked reference, exactly like the witness-bounded calculi. This collapses the ordinal
  seam to a single `toONote` at the leaf (or a one-shot `∀ α<ε₀, ∃ o:ONote, o.NF ∧ o.repr=α`; check
  mathlib for `ONote.repr` surjectivity onto `[0,ε₀)` before re-deriving), and the language seam to "the
  cut-free sequent is in the g-fragment" (= M7a + subformula property).

**(d) M4 and M7a are independent and both now attackable.** M4 (the generic embedding) is generic in the
endsequent `φ`, so it does **not** need the transparent `gAllReal` — it can be attacked over the opaque
syntax today. M7a (transparent arithmetization) is needed only at assembly/bounding, is faithfulness-gated
by `Bridge.lean`, and is pure shovel-ready arithmetization (no deep proof theory). They are good parallel
threads — and M7a doubles as recon for the Foundation arithmetization API that M4 also consumes.

## 4. Faithfulness at altitude — clean.

Re-audited `Statement.lean` / `Bridge.lean` / `Encoding.lean` / `Defs.lean` against the paper claim:
no drift (§1). The one 🟡 axiom in the repo (`PA_delta1Definable`) sits strictly under the **Route-A**
`peano_not_proves_consistency`/`not_proves_of_implies_consistency`; the two-phase **Route-B** headline
path does not touch it. No 🔴 anywhere (correct — Kirby–Paris is unconditional). The `Reduction.lean`
`goodstein_implies_consistency` `sorry` is **dead weight on Route B** (it is the Route-A girder); leave it
as an honest disclosed sorry, do not invest in it.

---

## Direction call

**KEEP doing:**
- The two-phase Route B (M5 cut-elim + M6 Hardy bound, both done & clean), joined by M4 + a bounding
  bridge. This is the literature-faithful architecture and reuses the most banked work.
- Disclosed-`sorry` decomposition; commit every green; `#print axioms` the headline every review lap;
  faithfulness gating via `Bridge.lean`.
- Mining the on-disk `papers/` + the reference corpus before re-deriving (the findings + landscape memory
  are exactly why this lap could course-correct).

**STOP doing:**
- **The witness-bounded cut-elimination thread.** No more `cutReduceAllAux`, no fourth index calculus.
  `wip/{BoundedZinfty,SplitZinfty,OperatorZinfty}.lean` are reference only. Proven off-critical-path.
- Treating the bounding bridge as "a small connector" or transporting M5's output into the abstract `B`
  calculus. Prove the bounding lemma on the real `Deriv`, reuse M6's ℕ-domination fact.
- Bagging tractable-but-off-path cut-elim bookkeeping while M4 sits untouched. Hardest-first =
  unavoidable-first now.

**Single highest-value next target: M4 — the embedding `PA ⊢ φ ⟹ Z_∞ ⊢^{α}_c {φ}`.**
Reasoning: (i) it is the **only** universal bottleneck — every route to the headline needs it; (ii) its
*feasibility* is the largest remaining unknown for Route B (does Foundation's finitary `Derivation`
embed cleanly into `ZinftyF.Provable`? does PA-induction become the ω-rule via derivation-substitution —
the lap-6 "2nd deep case"?), and hardest-first says resolve the feasibility doubt before further
investment; (iii) it has been deferred for 8 laps. Concretely, the next grind lap should:
1. Read Foundation's `Derivation` definition + its recursor/induction principle.
2. Write the embedding skeleton `embed : 𝗣𝗔 ⊢ φ → ∃ α c, ZinftyF.Provable α c {φ-as-Z∞-sequent}` (or the
   right finset image) by induction on `Derivation`; get the **structural** rules green
   (init/axL, verumR, andI, orI, cut — these mirror existing `Provable.*` constructors).
3. Isolate the **finite-induction-axiom → ω-rule** case as the single disclosed `sorry` crux. That alone
   is a clean feasibility readout on the deepest unknown — a successful lap whether or not it closes.
If M4 reveals a Foundation-`Derivation` wall, pivot to **M7a** (transparent `gAllReal` + `𝗣𝗔 ⊢
goodsteinSentence ↔ gAllReal`, gated by `Bridge.lean`) — committed, low-risk, also-required progress.

This is a licensed course change: the next grind laps inherit "attack M4, not `cutReduceAll`."
