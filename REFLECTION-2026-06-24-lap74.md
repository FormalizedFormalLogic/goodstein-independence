# Reflection — 2026-06-24 (lap 74, DEEP) — direction re-validated from altitude; crux-2 unavoidability *proven*, reduct re-work flagged, second front named

> Every-9th-lap altitude pass on the stronger model. I re-read the kernel (real `#print axioms`),
> the route, the lap-62 reflection, the Bryce–Goré findings, and the *actual* crux-2 architecture
> (the lap-70 obstruction, the RedSound rung ladder, the InternalZ inversion primitives). **Verdict:
> direction KEEP — the trajectory is genuine, kernel-verified forward motion, not circling. Crux 2
> is unavoidable (I re-derive *why* below, closing a door a future lap might be tempted to reopen),
> the finitary-Buchholz-Z internalization is the right architecture, and the RedSound rung ladder is
> the correct decomposition.** Three sharpenings the grind laps cannot make from inside the trees.
> This file is the lap's primary deliverable; the STATUS/ledger refresh + the PENDING_WORK reflection
> box implement it.

## Kernel re-verified this lap (real `#print axioms`, build green **1323 jobs**)

| theorem | axioms | reading |
|---|---|---|
| `peano_not_proves_goodstein` (headline) | `propext, sorryAx, choice, Quot.sound` | honest `sorry`, **0 math axioms**, anti-fraud intact |
| `goodsteinSentence_faithful` (anchor) | `propext, choice, Quot.sound` | faithfulness anchor CLEAN |
| `peano_not_proves_consistency` (Gödel-II hook, proved) | `propext, choice, Quot.sound, PA_delta1Definable` | carries Foundation's `PA_delta1Definable` |
| `goodstein_implies_consistency` (`Reduction.lean` girder, THE open work) | `propext, sorryAx, choice, Quot.sound, PA_delta1Definable` | disclosed `sorry`; the whole headline reduces to this |

`src/` holds exactly **3 real sorries** (Statement headline [locked, anti-fraud], `Reduction.lean`
girder [the work], `DescentSemantic.lean:582` [off-path free-X, hygiene]) and **0 axiom
declarations** (all `grep axiom` hits in `src/` are docstring prose). The crux-2 engine now lives in
**`src/GoodsteinPA/InternalZ.lean`** (promoted to `src/` lap 66; 5069 lines, **0 sorry / 0 axiom** —
the real axiom-clean implementation) + `wip/GentzenCon.lean` (crux-1 assembly, **9 disclosed
axioms**). Neither crux is wired into `Reduction.lean` yet — correct (anti-fraud: the wire happens
only when `#print axioms` is clean).

## Faithfulness at altitude (review requirement #4 — re-audited, not assumed)

`peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`, where (read off source this lap):
- `goodsteinSentence := “∀ m, ∃ N, !igoodsteinDef 0 m N”` (`Encoding.lean:83`) — transparent Π₂.
- `goodsteinSentence_faithful` (`Bridge.lean:34`, CLEAN): `ℕ ⊧ goodsteinSentence ↔ ∀ m,∃N, goodsteinSeq m N = 0`.
- `goodsteinSeq` (`Defs.lean:46`): `G 0 = m`, `G(k+1) = bump(base k)(G k) − 1`, `base k = k+2`
  (hereditary base-bump from base 2, then −1) — the standard Goodstein process.
- `𝗣𝗔` = Foundation's `Peano : ArithmeticTheory` — genuine first-order Peano.

**No transcription drift. The headline statement says exactly Kirby–Paris.** `#print axioms`
certifies the *proofs*; this paragraph certifies the *statement*. Both hold.

## Trajectory: is the treadmill circling? NO — monotone, with one honest correction.

HANDOFF arc (no in-box lap log; reconstructed from HANDOFF headers + git, 575 commits over 3 days):
- 45→46 resolved the route (Goodstein⟹PRWO, **not** free-X-TI); 47 internal Thm 3.5; **57 LANDED
  crux 1 axiom-clean** (`γ→PRWO`, width-FUNCTION refactor); 58–61 built the system-Z ordinal engine.
- 66 `iR2` descends on K; 67 tag-4 descent assembled; 68 descent made unconditional (zKValid wired);
  69 reduced to ONE obligation (**RedSound**); **70 the correction — Option B refuted in-kernel,
  Option A (genuine validity-preserving reduct) forced**; 71 rung-0.5 complete (ZPhi side
  conditions); 72 `zsubst` defined; 73 `fstIdx_zsubst` + subst-commutation substrate.

This is real forward motion toward a single deep girder, not repeated failed attempts. **But lap 70
is a structural signal worth naming at altitude** (Sharpening 2 below): laps 66–69 assembled a
descent on a reduct (`iR2`) that lap 70 then proved is *not* validity-preserving. That work was not
wasted (it built the ordinal machinery and *localized* the obstruction precisely), but the genuine
Option-A reduct is effectively a fresh implementation, and the `iR2`-specific descent assembly is
being superseded. The architecture under-specified the hardest piece (genuine cut-elim) and deferred
it; laps 70+ are now confronting it properly. That is the right move — but it means the realistic
remaining distance is **the full internalized Gentzen cut-elimination**, not a finishing touch on an
almost-done engine.

---

## Sharpening 1 — crux 2 is genuinely UNAVOIDABLE (re-derived from altitude; closes a tempting door)

The single most valuable thing a strong-model lap can do here is *settle*, rigorously, whether the
deep grind (internalized cut-elimination) can be dodged — because the repo holds a complete,
axiom-clean `Thm56.peano_not_proves_TI` (Gentzen 1943, `𝗣𝗔 ⊬ TI_≺(X)`, free `X`), and "can't we
just use the monument?" is the obvious shortcut a grind lap circles back to. **I re-derived the
answer: NO. The off-path verdict is correct. Here is the proof, so no future lap re-litigates it.**

1. **Free-X TI-unprovability is the wrong *shape*.** To chain Goodstein-unprovability off
   `𝗣𝗔 ⊬ TI_≺(X)` you would need `𝗣𝗔 ⊢ γ → TI_≺(X)` for the *free* predicate `X`. Impossible: `γ` is
   a fixed first-order arithmetic sentence; it cannot imply transfinite induction for an
   *uninterpreted* `X` (a schema/2nd-order strength object). The implication that *does* hold runs the
   other way (`TI → ` arithmetic instances), i.e. the monument is an unprovability result about the
   *schema*, not about the *specific* primrec sentence crux 1 produces.
2. **The specific-instance route still needs Gentzen.** crux 1 gives `𝗣𝗔 ⊢ γ → PRWO_inst` for a
   *single* first-order sentence `PRWO_inst` ("no primrec descent of the Goodstein-derived ε₀
   sequence"). To finish *without* Con(PA) one would need `𝗣𝗔 ⊬ PRWO_inst`. But the only honest ways
   to that are: (a) `PRWO_inst → Con(PA)` (Gentzen Thm 2.8) + Gödel II — i.e. *exactly crux 2*; or
   (b) the classification of PA's provably-recursive functions (`PA`-provable totality is bounded by
   `F_α`, `α<ε₀`) — which is *itself* the ordinal analysis / infinitary cut-elimination. **Either path
   is crux 2 or harder.** There is no ε₀-strength-free proof of an ε₀-strength independence result.
3. **The banked meta-level machinery cannot be reused as-is.** `embedC`/`cutElim`/`boundedness` are
   *Lean-meta-level* theorems about the infinitary `Z∞`. crux 2 = `𝗣𝗔 ⊢ (PRWO → Con)` requires the
   *same algorithm arithmetized inside IΣ₁* (coded derivations, Σ₁ recursions, IΣ₁ inductions). The
   monument is a *blueprint* for the internal version, never a drop-in. (Confirmed: Foundation's
   `Hauptsatz.main` is a meta Lean function on the `Derivation` inductive, not a primrec PA-function.)

**Net: KEEP the monument banked (do not resurrect, do not delete), and keep grinding crux 2.** The
finitary-Buchholz-Z internalization (finite trees → codeable, `Ind` rule kept, reduction is a Σ₁
operation on codes) is the *right* architecture — strictly more tractable than internalizing the
infinitary `PA_ω` that Bryce–Goré chose, and it follows Buchholz's own "On Gentzen's first
consistency proof" (in `papers/`). Direction VALIDATED.

## Sharpening 2 — the lap-70 reduct re-work: validity AND descent both re-fit on the genuine reduct

The genuine Option-A reduct (`cut_elimination_atom/_neg/_lor`-style, shape-dispatched on the cut
formula) carries **two** obligations, and the grind must hold both in view:
- **Validity (RedSound)**: `R d` is a genuine `ZDerivation` — the rung ladder's headline target.
- **Descent**: `o(R d) ≺ o(d)` (Buchholz Thm 4.2) — *re-proven on the genuine reduct*. The lap-67
  `iord_descent_iR2_zK_of_valid` / `iord_iR2_iterate_descends` proved descent for the **wrong**
  reduct; it must be re-fitted.

**Good news (limits the waste, recorded so the grind doesn't over-rebuild):** the *ordinal
assignment* machinery (`idg`/`iõ`/`iord = iotower idg iõ`, the F1–F4 natural-sum/ω-tower order facts,
the two C3 descent **templates**) is a function of the derivation *shape/rank*, independent of the
reduct definition — so it is **reusable**. What is throwaway is specifically (i) the `iR2`/`iCritReduct`
*definition* and (ii) the `iord_iR2_iterate_descends` *assembly*. **Watch for over-investment in
`iR2` infrastructure** — every new `iR2`-shaped lemma is on the superseded path. The genuine reduct's
descent should be re-derived by feeding the *reused* C3 templates the genuine reduct's shape.

## Sharpening 3 — name the second front: `PA_delta1Definable` is a HARD REQUIREMENT, untouched, and at risk

The operator endpoint (hardened lap 62, binding) is **axiom-free or abandoned** — so
`PA_delta1Definable` is *not* an acceptable disclosed residual; it **must** be discharged for the
headline to ever be clean. This lap's findings re-confirm it is **still an `axiom`** in the pinned
*and* upstream Foundation (`Incompleteness/Examples.lean:17`, byte-identical, standing TODO since
2023) — no bump will hand it over. It is **independent of crux 2** (it rides Gödel II, not the
ordinal analysis) and **no lap has started it**.

Two honest cautions: (a) "bounded arithmetization, no deep math" (the HANDOFF's framing) is right in
kind but *understates the labor* — arithmetizing the full PA induction-scheme's Δ₁-definability has
sat open upstream for years precisely because it is large/tedious, not because it is deep. (b) It is
nonetheless the **lowest-doubt** mandatory item: its feasibility is not in question, only its volume.
**Recommendation:** keep the primary grind on RedSound (hardest-first — its feasibility *is* the open
doubt), but designate `PA_delta1Definable` the official **second front**, to be advanced whenever the
rung ladder blocks (e.g. waiting on a build, or a rung that needs a design soak). It is the single
biggest *non-cut-elimination* risk to the stated endpoint, and leaving it untouched indefinitely is
the quiet way the "axiom-free" goal silently slips.

(The **C0.5 Foundation→Z bridge** — `¬Con(PA)` ⟹ a Z ⊥-derivation — remains load-bearing and unbuilt;
Bryce–Goré's `Peano.v` 3-layer shape [real PA → ordinal-annotated PA → infinitary, by
induction-on-derivation with an explicit per-axiom ordinal table] is the blueprint, harvested in
`archive/findings/ON-LINE-FINDINGS-2026-06-24-bryce-gore-gentzen.md`. Sequence it *after* RedSound:
the engine needs to exist before it needs fuel.)

---

## The call

- **KEEP:** Route A (Rathjen Cor 3.7); crux 2 via internalized **finitary Buchholz-Z** + the Option-A
  genuine validity-preserving reduct; the RedSound rung ladder (0.5 ✅ → 1 `zsubst` → 2 Ind reduct →
  3 K/cut reduct → 4 RedSound dispatch); the reusable `iord`/ω-tower ordinal machinery; the banked
  Thm-5.6 monument (do NOT resurrect — Sharpening 1 proves it cannot chain; do NOT delete).
- **STOP:** any temptation to dodge crux 2 via the free-X monument (Sharpening 1 closes this);
  extending `iR2`/`iCritReduct` infrastructure (superseded — Sharpening 2); treating
  `PA_delta1Definable` as an acceptable disclosed residual (operator forbids; Sharpening 3).
- **HIGHEST-VALUE NEXT TARGET (unchanged from lap 73, re-endorsed):** finish **`ZDerivation_zsubst`**
  (rung-1 step 2) — the eigenvariable-substitution correctness lemma. It is the immediate prerequisite
  for the genuine Ind reduct (rung 2), which is the more tractable of the two genuine reducts and the
  next real RedSound rung. The PENDING lap-73 box has the resolved plan: (A) freshness via the `d ≤ a`
  code-bound, (B) close the well-formedness gap by adding `IsSemiformula`/`IsUFormula` side conditions
  to `zIallWff`/`zIndWff`/`zInegWff` (start `zInegWff`, the lap-71 cascade recipe is battle-tested).
- **SECOND FRONT (when the ladder blocks):** `PA_delta1Definable` (Foundation upstream; mandatory).
- **HYGIENE (non-blocking, deferred):** off-path `DescentSemantic.lean:582` free-X `sorry` +
  dependents are `wip/` candidates; not worth an invasive move on a reflection lap.

**Realistic endpoint, stated honestly:** a fully axiom-free `peano_not_proves_goodstein` is a
multi-month undertaking dominated by the internalized cut-elimination (crux 2), with
`PA_delta1Definable` + the C0.5 bridge as substantial-but-bounded side obligations. Feasibility is
settled (Bryce–Goré, Coq, Feb 2026); the path is decomposed; cadence ≈ one genuine reduct rung per
lap or two. The operator's "axiom-free or abandoned" bar is honest given that settled feasibility.
No course change — *drive the ladder*.
