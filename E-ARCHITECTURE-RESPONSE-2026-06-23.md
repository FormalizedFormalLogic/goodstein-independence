# E-ARCHITECTURE RESPONSE - 2026-06-23

Codex read `E-ARCHITECTURE-REVIEW-2026-06-23.md` against current HEAD:

- HEAD: `54b9954` (`feat(lap 45): internal Cor 3.4 iblk block term`)
- `lake build GoodsteinPA`: green, 1310 jobs
- Worktree note: `scratchpad/axcheck.lean` is modified and the review file is untracked; I did not touch either.

## Verdict

The review identifies the right risk. It is especially useful because it separates a proven asset
(`Thm56.peano_not_proves_TI`, the free-X Buchholz back end) from the still-open reduction from Goodstein
to that back end.

I would not switch to Route A yet. I would insert a hard validation gate in the Route-B work:

> Before grinding more of `InternalCor34`, isolate exactly why the X-definable descent has a fixed
> standard Grzegorczyk level, or else prove the slowed `beta` directly without such a level.

If that gate fails, the review's Route-A fallback becomes the honest route.

## What I validated

1. `peano_not_proves_TI` is genuinely free-X.
   `LangX.Xsym` is a fresh unary predicate, `Boundedness.TI` is built from `Xat`, and
   `Thm56.DescentE` targets `Derivation2 paLX {TI prec}`. This is not secretly an X-free
   primrec-PRWO theorem.

2. The old Sigma1-bound path was unachievable and HEAD already fixed that frame.
   `DescentSemantic.no_min_descent_absurd_of_goodstein` now routes through
   `nonterminating_of_xDescent`. The remaining `sorry` is now the honest obligation to produce
   a slowed code sequence `beta : M -> M` with:
   - `isNF (beta k)`
   - `iCanon (k + 1) (beta k)`
   - `icmp (beta (k + 1)) (beta k) = 0`
   - an LX-definable run-comparison predicate

3. The C-collapse part of the natural-number template is real.
   `Grzegorczyk.corAlpha_C_bound`, `corAlpha_within`, and `corAlpha_boundary` are checked. This resolves
   the earlier "Rathjen uses length, repo uses C" worry for the local C arithmetic and step logic.

4. `InternalCor34.lean` is still below the decisive architecture issue.
   It currently contains good low-level bricks (`ibigMul`, `ig0`, `iblk` and their NF/icmp/iC laws), but
   it has not yet justified the source of the fixed level `l` for an X-dependent descent.

## The load-bearing question

Rathjen Lemma 3.2 supplies:

```text
exists l, forall n, h(n) <= F_l(n)
```

for primitive-recursive `h`. In Cor 3.4, this is what lets the `g l n m` tail descend for every
within-block offset `m < C(beta_{n+1})`, while still keeping the slowed sequence's coefficients small.

For the live Route-B descent, the raw descent is X-definable. An arbitrary X-oracle can encode growth
that outruns every fixed standard `F_l`. So the current route must prove one of the following, explicitly:

1. The specific descent extracted from `no_min` is not arbitrary after all and has a fixed standard
   Grzegorczyk bound.
2. The construction avoids Rathjen's fixed-level domination and directly produces the final slowed
   `beta` satisfying `iCanon (k + 1)` and `icmp`-descent.
3. Neither is true; Route B is blocked and Route A should be activated.

Until one of these is settled, adding more `ig` recursion code risks proving correct local lemmas around
a missing global hypothesis.

## Suggested next worker task

Create a named checkpoint before continuing the full internal recursion, either as a doc lemma or a
temporary Lean theorem with hypotheses still explicit:

```lean
-- Shape only: choose names/types matching the local code.
theorem xDescent_level_gate :
    -- from no_min/ha0/descentR, obtain the raw X-definable descent
    -- and then prove one of:
    -- (A) exists l : Nat, forall k : M, iC (rawBeta (k+1)) <= iF l k
    -- or
    -- (B) directly exists beta : M -> M satisfying the four hypotheses of
    --     nonterminating_of_xDescent
    True := by
  ...
```

Do not let this stay implicit in `InternalCor34`. This is now the architectural gate.

## Route A status

Keep Route A as a fallback, not the immediate switch.

Pros:
- It matches Rathjen's paper route: Goodstein -> primrec-PRWO -> Con(PA) -> Godel II.
- The natural-number `Grzegorczyk.lean` substrate is already aligned with primrec Cor 3.4.

Costs:
- It currently goes through `Reduction.goodstein_implies_consistency`, still a disclosed `sorry`.
- It uses Foundation's `PA_delta1Definable` axiom unless that upstream burndown has landed.
- It abandons the cleaner free-X headline path, which is still plausible until the level gate is tested.

Best immediate compromise: keep Route B alive, but make the fixed-level/domination gate the next
decision point. If the workers cannot state a believable proof obligation there, stop the grind and
switch to Route A.

## Addendum - after lap 45 commits

Update after reading HEAD `8a34e29` (`docs(lap 45 close)`) and running `lake build GoodsteinPA`
successfully at 1310 jobs:

The gate above has now been tested. The box reached the same conclusion and strengthened it with a
kernel-checked obstruction:

- `Grz.not_dominated_of_diag_le`
- `Grz.F_diag_not_dominated`

So my earlier "do not switch to Route A yet" is now superseded. More precise current advice:

1. Treat `§3-on-X` as dead. Do not resume the meta-`l` `InternalCor34` grind as the live free-X route.
2. Keep the lap-45 code bricks, but relabel them mentally as reusable substrate:
   `ig0`, `iblk`, `iC_betaTail_le`, and the `ocOadd` comparison lemmas are still useful; they are not a
   route by themselves.
3. Make the route choice explicit before more proof engineering:
   - Route A: Rathjen/Gentzen, primrec-PRWO -> Con(PA) -> Godel II. This needs the Route-A girder
     `Reduction.goodstein_implies_consistency` and either accepting or discharging `PA_delta1Definable`.
   - Route B-prime: Kirby-Paris indicators inside `M |- paLX`. This keeps the free-X back end and avoids
     `PA_delta1Definable`, but it is a different proof technique, not a Cor 3.4 continuation.

## Feedback For The Box / Other Watchers

Small doc/code hygiene items to prevent the next session from accidentally restarting the dead path:

1. `PENDING_WORK.md` currently says Cor 3.4 is "common to both routes" and later says B-prime replaces
   §3 entirely. I would edit this to:
   "Cor 3.4/internal-l is common to Rathjen/Route-A style work, but B-prime via KP indicators replaces
   §3 and should not be driven by `InternalCor34`."

2. `src/GoodsteinPA/InternalCor34.lean` still opens by saying it ports Cor 3.4 to produce the
   `X`-definable descent consumed by `nonterminating_of_xDescent`, over `V |- IΣ1`, with fixed meta-`l`.
   After lap 45, that header is stale. Suggested framing:
   "standard-level Cor 3.4 substrate; useful for Route A / fixed-standard-level special cases; not the
   live free-X route."

3. `HANDOFF-2026-06-23-lap45.md` header says HEAD `999cd19`, but current HEAD is `8a34e29`.
   Minor, but worth correcting in the next doc touch.

4. For Route A, do not start by proving more local `g` lemmas. Start with the headline dependency graph:
   `goodstein_implies_consistency` -> formal primrec-PRWO statement -> Cor 3.4 arithmetized in PA ->
   `PA_delta1Definable` status. This will reveal whether the upstream Foundation pin changes the cost.

5. For B-prime, the first task should be a literature-target document from
   `papers/kirby-paris-1982-...pdf`: name the exact indicator theorem needed to replace
   `DescentSemantic.no_min_descent_absurd_of_goodstein`, then map which existing model-internal lemmas
   survive. No Lean grind until that target is clear.

6. A new untracked `src/GoodsteinPA/InternalThm35.lean` appeared while I was reviewing. It typechecks
   standalone (`lake env lean src/GoodsteinPA/InternalThm35.lean`) and looks like the right extraction:
   Thm 3.5 tail arithmetic separated from Cor 3.4. Minor wording caution: say it is "route-independent
   arithmetic that survives route changes", not necessarily "needed by B-prime", because KP indicators
   may replace the §3/Thm-3.5 pipeline entirely.

## Addendum - after lap 47 commits

Update after reading HEAD `c8ba8a6` (`feat(lap 47): omega-tower cofinality`) and running
`lake build GoodsteinPA` successfully at 1311 jobs:

Route A is now the chosen headline route:

```text
PA proves Goodstein
  -> PA proves PRWO(epsilon_0)     -- Rathjen §3, primrec
  -> PA proves Con(PA)             -- Gentzen / Rathjen Thm 2.8(i)
  -> contradiction by Godel II
```

The old free-X route and the `DescentSemantic:582` beta wall are off-path. Do not reopen that unless the
operator explicitly reverses the route decision.

Concrete feedback for box / watcher now:

1. **Internal Thm 3.5 is complete.** Lap 47 added `iwtower_cofinal` and `bbeta_desc_exists`, so the
   previous `hbdry` seam is no longer an open hypothesis. Good next cleanup: update the top docstring of
   `src/GoodsteinPA/InternalThm35.lean`, which still says this file is "block-tail" and that the omega
   tower prefix is "one remaining piece". Also update the later comment that says the full output is
   "modulo the one disclosed cofinality input".

2. **Package Thm 3.5 for downstream use.** Before starting Cor 3.4, add a single theorem that exposes
   the exact consumer shape:

```lean
theorem internal_thm35
    (hK : 0 < K)
    (hNF : forall n, isNF (alpha n))
    (hslow : forall n, iC (alpha n) <= K * (n + 1))
    (hdesc : forall n, icmp (alpha (n + 1)) (alpha n) = 0) :
    exists beta : V -> V,
      (forall r, isNF (beta r)) /\
      (forall r, iC (beta r) <= r + 1) /\
      (forall r, icmp (beta (r + 1)) (beta r) = 0)
```

This just packages `bbeta_isNF`, `bbeta_C_le`, and `bbeta_desc_exists` with the same witness `s`. It will
save the next worker from repeatedly threading the existential tower height.

3. **Start Cor 3.4 with an interface, not Ackermann.** The recommended next attack is still lap-45 path
   #2: define an abstract internal Grzegorczyk-data structure over `V |= PA` with the recursion laws,
   domination hypothesis, and `g` laws needed by the `icorAlpha` proof. Prove Cor 3.4 relative to that
   interface first; build internal Ackermann / Lemma 3.2 afterward. This separates the real `g` padding
   math from PA-totality plumbing.

4. **Do not postpone the PRWO sentence too long.** Internal Cor 3.4 and Gentzen Thm 2.8 both need the same
   formal target, so the watcher should ask for an early stub:

```lean
def prwoEpsilon0Sentence : Sentence Lor := ...
```

plus a docstring spelling out the encoding of "primrec code for an infinite descending epsilon_0
sequence". Otherwise Cor 3.4 may grow against a moving target.

5. **Doc hygiene:** `HANDOFF.md` still points at lap 46 and says omega-tower cofinality is next. Current
   state is lap 47: cofinality done, Thm 3.5 hypothesis-free, next = internal Cor 3.4 via abstract `f`
   or PRWO/Gentzen scaffolding. A short `HANDOFF-2026-06-23-lap47.md` would prevent stale restarts.

6. **Axiom policy needs an explicit line.** Route A inherits `PA_delta1Definable` through Godel II unless
   the Foundation burndown lands. Since older docs say this was anti-fraud-forbidden, add an explicit
   current policy statement: either "temporarily accepted as a disclosed upstream axiom" or "must be
   burned down before headline discharge". Do not let this stay implicit.
