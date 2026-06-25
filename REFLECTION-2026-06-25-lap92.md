# DEEP REFLECTION — lap 92 · 2026-06-25 · the ω-rule pivot (route C)

> **⭐ ADDENDUM (later same lap — read with `ANALYSIS-2026-06-25-lap92-criticality-wall-is-gone.md`).**
> Deeper in-kernel check refined this: `ZPhi` ALREADY uses criticality-free `zKValidF`, so the lap-78
> "substitution wall" (which attacked only the criticality conjunct) is **gone**, and lap-91's O2 is
> **misattributed** to it. The real residual is the **O1↔O2 freshness/eigensubst coupling** intrinsic to
> finitary ∀. This yields TWO honest paths — **Path X** (stay finitary: add freshness O1 + prove
> eigensubst O2 under `zKValidF`, no longer known-blocked, lower risk) and **Path C** (the ω-rule pivot
> below, which dissolves the coupling permanently). The de-risk spike's sharp first probe = measure Path
> X's O1 cost; localized → Path X, cascades → Path C. The ω-rule case below stands but is now ONE of two
> options, not the sole recommendation.


> Primary deliverable of the every-9th reflection lap. Build green (1325 jobs); headline
> `peano_not_proves_goodstein = [propext, sorryAx, choice, Quot.sound]` (0 math axioms),
> `peano_not_proves_consistency` clean, faithfulness anchor `goodsteinSentence_faithful` clean.
> All re-verified in-kernel this lap (`lake env lean`, outside the tree).

## The one-paragraph call

**Direction: KEEP the destination, PIVOT the sub-route.** The headline (`𝗣𝗔 ⊬ Goodstein`, axiom-free)
is right and its single remaining obligation is correctly identified: crux-2 =
`goodstein_implies_consistency` = real internalized cut-elimination (`redSound`). But the *presentation*
the arithmetized engine (`InternalZ.lean`) was built on — Buchholz's **finitary system Z with
eigenvariables** — is the wrong one, and it is the direct cause of the wall that has held laps 78–91
(~13 laps). The fix is to arithmetize the **infinitary ω-rule system** (Buchholz §6 `Z^∞` / Schütte
`PA_ω`) instead, exactly as the repo's *own meta-level engine* `Zinfty.lean` already does (axiom-clean)
and exactly as Bryce–Goré's complete Coq `Con(PA)` does. This single change dissolves all three open
route-B obstructions (O1 freshness, O2 eigen-substitution, the conclusion-tracking `tpReduce`) at once.

## 1. Is the destination still right? — YES, unchanged

`𝗣𝗔 ⊬ goodsteinSentence` via Rathjen 2014 Cor 3.7: `γ → PRWO(ε₀) → Con(𝗣𝗔)`, then Gödel II.
- **Faithfulness re-audited (reflection point 4).** `Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`
  is the genuine claim; its anti-vacuity anchor `Bridge.goodsteinSentence_faithful :
  (ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0` is **axiom-clean** and `goodsteinSeq` is
  the genuine hereditary-base process (`Defs.lean`). No transcription drift.
- **Single front confirmed.** `peano_not_proves_consistency` is axiom-clean (lap-89: `PA_delta1Definable`
  discharged upstream in Foundation). The ONLY open obligation is `goodstein_implies_consistency`
  (`Reduction.lean:68`) = crux-1 (DONE, lap 57, axiom-clean) ∘ **crux-2**.
- **Honest endpoint.** crux-2 is the irreducible ordinal-analytic content of an exact-strength
  independence result — there is no shortcut around "ordinal analysis of PA" (lap-74 proved the banked
  free-X monument is the wrong shape; lap-90 proved there is no validity-free ε₀-descent bypass).
  Feasibility is **settled**, not speculative: Bryce–Goré machine-checked `Con(PA)` in Coq (Feb 2026,
  arXiv:2603.00487), and *this repo* machine-checked the same cut-elimination at the meta level
  (`Zinfty.lean`, axiom-clean). The realistic endpoint is a fully axiom-clean Kirby–Paris; it is
  multi-month and the remaining work is engineering a known proof, not originating mathematics.

## 2. Are we attacking the highest-value thing? — the TARGET yes, the ROUTE no

crux-2 `redSound` is the only open obligation, so it is unambiguously the highest-value target — no
drift, no easy-leaf-bagging. The problem is one level down: **which cut-elimination presentation to
arithmetize.** There are now THREE attempted sub-routes inside the finitary system, and all three are
blocked by the *same* fact:

- **Route A** (repo's original `red`, keeps the conclusion `Π`): REFUTED lap-90 — faithful only when
  `tp(d) = Rep`; the recursion dives into `∅→A₀` sub-derivations where it isn't.
- **Route B** (lap-90/91 `tpReduce`, conclusion-reducing reduct): the current plan. But lap-90 itself
  (lines 127–130, 145–148) records that route B **still needs eigenvariable substitution** `d₀(a/n)`
  (I∀) and `d₁(a/0)…d₁(a/k-1)` (Ind) that *preserves validity* — and lap-90 (lines 132–143) proves
  there is **no validity-free bypass** (the critical 5.1 descent consumes `zKValidF` threading).
- **The shared wall** (O2, the lap-78 wall): the eigenvariable substitution is NOT `ZDerivation_zsubst`
  (`Zsubst.lean:834` needs a fresh *large* slot `d ≤ a`; the eigenvariable `a` is *small* and occurs in
  the premise). Laps 78→91 have circled this; lap-78 proved the original criticality formulation can't
  survive `fvSubst` (non-injective), the lap-82 `zKValidF` re-point dodged that conjunct, and O2 is the
  residue that remains.

This is the genuine "circling" signal a reflection lap exists to catch: the target is right, but the
sub-route has been re-derived three times and bounced off the same eigenvariable-substitution wall.

## 3. What a sharp outside expert would say we're missing — the ω-rule

**The eigenvariable-substitution-inside-cut-elimination wall is an artifact of the *finitary* ∀-rule.
The standard, formalization-proven fix is the ω-rule.** Three independent pieces of evidence, gathered
this lap:

1. **Bryce–Goré (the only complete formalization of `Con(PA)`, Coq, Feb 2026)** work *directly* in the
   infinitary `PA_ω` (`theories/Logic/PA_omega.v`). Their ∀-rule is `w_rule1 : (∀ c : c_term,
   PA_omega_theorem (substitution A n c) …) → PA_omega_theorem (univ n A) …` — premises indexed by all
   closed terms, **no eigenvariables**. Cut-elimination (`cut_elim.v`) is substitution-free: the
   ∀/∃ reduct *selects* the witness premise. They succeeded with this; nobody has with finitary-in-a-prover.

2. **The repo's OWN meta engine already did it.** `Zinfty.lean` (1560 lines, axiom-clean per the
   landscape note) "replaces Foundation's finitary eigenvariable `all` rule with the **ω-rule** `allω`"
   and machine-checks the full Towsner §19 cut-elimination (inversions 19.2–19.4, `cutElimStep` 19.7,
   `cutElim` 19.9). The hard cut-elimination *math* is already cracked — in the ω-rule presentation.
   The arithmetized engine (`InternalZ.lean`) inexplicably re-chose the finitary one.

3. **Buchholz embeds finitary→infinitary *precisely to do cut-elimination*.** His §6 `Z^∞` exists
   because the finitary reduction `d[n] := d₀(a/n)` (Def 3.2) is the *hard* eigenvariable-substitution
   version; cut-elimination is done in the infinitary system, where ∀ is the ω-rule and the reduct
   selects the n-th premise. His §6 "finite recursive notations `Z*`" (`h[n] = h₀(x/n)`) is the
   arithmetization-friendly encoding: a *finite* code `h` denoting an infinitary derivation, premise-n
   computed on demand — exactly what IΣ₁ can represent.

### Why the ω-rule collapses all three obstructions at once
In an ω-rule node, `∀xF` is introduced from a premise *family* `{ dₙ ⊢ Γ→F(n) }ₙ`. At a critical cut
on `∀xF`, the reduct **selects `dₙ`** — which *already* derives `Γ→F(n)`. Therefore:
- **O2 (eigen-substitution) — GONE.** Selecting a premise is not substituting. No `zsubst`, no fresh-slot
  side condition, no `fvSubst` injectivity.
- **O1 (eigenvariable freshness) — GONE.** There are no eigenvariables to keep fresh.
- **Route-B conclusion-tracking (`tpReduce`) — AUTOMATIC.** `tpReduce (R_∀xF) Π n = Γ→F(n)` is exactly
  the conclusion the selected premise `dₙ` already has. The Thm-3.4(b) invariant holds by construction.

This is the decomposition the reflection asks for: **one architectural change retires O1, O2, and the
entire route-B `tpReduce` program simultaneously**, and re-uses the cut-elimination math the repo
already proved at the meta level.

### The honest risk (this is a real pivot, not a free win)
The ω-rule has its own arithmetization cost, and intellectual honesty requires naming it:
- **The riskiest assumption:** that "premise-n as a Σ₁ recursive notation" (Buchholz §6 `Z*`) +
  "cut-elimination by recursion on the ordinal height `iord`" arithmetizes in IΣ₁ *without an equally
  bad new wall*. This is the unknown the pivot must probe FIRST.
- **Mitigants:** (a) the repo *already* arithmetizes premise-*sequences* (`zK`/`zKseq`/`iIndReductSeq`/
  `iRepeatSeq` build and index premise families); (b) recursion on `iord < ε₀` is **licensed by the
  PRWO(ε₀) hypothesis itself** — it is the natural primitive for crux-2, not an extra assumption; (c)
  the entire `iord`/`icmp`/`idg`/`iõ`/ω-tower ordinal engine (laps 58–61, axiom-clean) is **reused
  unchanged**; (d) `Zinfty.lean` is a worked meta template for every cut-reduction case.
- **What is NOT reused:** the finitary `zIall`/`zInd`-with-eigenvariable rules, `Zsubst.lean` (982 lines
  of eigenvariable substitution), the route-A/B `red`/`iRK`/`tpReduce` dispatch, and `zDerivation_induction`
  as a code-size recursion (it becomes `iord`-recursion). Call it ~2–3k lines reworked of ~7.3k.

Sunk cost is not a reason to keep a stuck route. But torching 7k lines on a hunch is also wrong. So:

## The single highest-value next target — DE-RISKED SPIKE, then pivot

**Do NOT rewrite `InternalZ.lean` yet.** Probe the riskiest assumption cheaply, in `wip/`, then decide:

1. **`wip/InternalZomega.lean` — the spike.** Define an internal ω-rule ∀-node `zAllOmega s g` where
   `g : V` codes the premise-generating Σ₁ notation (premise-n = `appPrem g n`, derives `Γ→F(n)`),
   reusing the existing seq/notation machinery. State its `ZDerivation`-clause and the **critical-cut
   reduct** for a `∀xF`-cut, and *check by elaboration* that the reduct is `appPrem g n` with **zero
   substitution obligations**. Target: confirm the I∀ and 5.1 critical cases that O2 blocks become
   substitution-free. (One bounded, self-contained lemma — good Aristotle fodder once stated.)
2. **Decision gate.** If the spike elaborates clean and the critical reduct is substitution-free →
   commit route C: port the ordinal engine, rebuild `red`/`redSound` over the ω-rule system, recursion
   on `iord`. If the spike hits a *new* equally-bad wall (e.g. Σ₁-definability of `appPrem`, or
   `iord`-recursion won't go through in IΣ₁) → that is a genuine finding; fall back to grinding route-B
   O2 with the knowledge that no cleaner route exists.
3. **Parallel:** keep route-B's *reusable* leaves (`red_zK_rep/_splice`, `tp_*`, `red_rep_of_tp_isymRep`,
   `tp_isymRep_of_emptyAnt_botSucc`) — they are not wasted; under route C the `tp`-dispatch survives, only
   the eigenvariable substitution is replaced by premise selection.

## KEEP / STOP

- **KEEP:** the destination and decomposition (γ→PRWO→Con); the axiom-clean ordinal engine
  (`iord`/`icmp`/`idg`/`iõ`/ω-tower); the Σ₁-definability scaffolding discipline; the `Zinfty.lean` meta
  ω-rule proof as the template; the `tp`-dispatch leaves.
- **STOP:** investing further in the finitary eigenvariable route — specifically the route-B `tpReduce`
  conclusion-tracking program and any new `Zsubst`/`ZDerivation_zsubst` eigenvariable-substitution
  lemmas (O1/O2). They are downstream of a presentation choice we should reverse. Do not re-derive the
  "substitution must preserve validity" wall a fourth time.

## Pointers
`Zinfty.lean` (meta ω-rule template) · `papers/buchholz-beweistheorie-lecture-notes.md` §5–6 (`Z^∞` +
`Z*` notations) · `~/src/Gentzen/theories/Logic/PA_omega.v` + `cut_elim.v` (Bryce–Goré) ·
`ANALYSIS-2026-06-25-lap90-red-faithful-only-for-rep.md` (the wall) · `HANDOFF-2026-06-25-lap91.md`
(O1/O2/O3) · `Crux2Blueprint.lean` (the assembly the spike feeds).
