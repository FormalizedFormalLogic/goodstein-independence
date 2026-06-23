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

## Addendum - after lap 48 close

Update after reading HEAD `16bc690` (`docs(lap 48 close): HANDOFF - Cor 3.4 clean-append + MinExpGe chain
complete`):

No route change. Route A is still the live headline route, and lap 48 made real local progress: the
clean-append comparison, `iC_iadd_clean`, `iAbove_iomul`, `iAbove_zero_iomul`,
`iAbove_ibigMul_iter`, and `iAbove_finThresh_mono` are now in place. The next useful advice is about
keeping the Cor 3.4 interface narrow enough that the next session does not bury the real obligation.

Explicit feedback for box / watcher:

1. **Freeze the clean-condition contract before abstract `ig`.** The next lemma should not just say
   "`g < omega^(l+1)`" informally. State the exact consumer shape needed by `icorAlpha`: turn
   `iAbove_ibigMul_iter` plus `iAbove_finThresh_mono` into a small lemma whose hypotheses expose
   "the exponent of `g` is the finite code `j` with `j <= l`". Then `ig` only has to prove that finite
   exponent bound, not rediscover the whole MinExpGe argument.

2. **Keep abstract `ig` tiny.** A good first structure/interface should contain only the laws consumed by
   `icorAlpha`: NF of `ig`, within-block descent, `iC` bound, finite-exponent/below-level bound, and the
   block-width/domination hypothesis. Do not start by internalizing Ackermann or Lemma 3.2; prove Cor 3.4
   relative to this interface first, then supply the interface from `V |= PA`.

3. **The `IΣ1`/`PA` boundary is now important.** The clean-append and MinExpGe lemmas are correctly local
   to `[V |= IΣ1]`. The existence/recursion of the internal Grzegorczyk hierarchy is the part that needs
   `[V |= PA]`. Keep those assumptions separated so reusable ordinal-code algebra does not acquire PA
   by accident.

4. **Package Thm 3.5 before wiring it downstream.** `bbeta_desc_exists` exists, but there is still no
   single `internal_thm35` theorem returning the `beta` sequence with NF, `iC beta r <= r+1`, and descent
   in one package. This is a low-risk cleanup that will make the Cor 3.4 -> Thm 3.5 handoff much cleaner.

5. **Docs are still slightly out of phase.** `HANDOFF.md` is semantically current but still names HEAD
   `7b36ad1` while the live HEAD is `16bc690`; `STATUS.md` still says lap 47 / `c8ba8a6`; the top of
   `PENDING_WORK.md` still has the pre-lap-48 "next" list even though the lap-48 append supersedes it.
   `InternalThm35.lean` also still opens as if the prefix/cofinality work were pending. These are not math
   blockers, but they are exactly the kind of stale text that can send a worker back into completed tasks.

6. **The other girder is unchanged.** `PRWO(epsilon_0)` as a concrete `Sentence Lor` and Gentzen
   `PRWO -> Con(PA)` remain the parallel crux. Even a stub with a precise docstring would reduce target
   drift while `icorAlpha` is being assembled.

## Addendum - after lap 50

Update after reading HEAD `2964cd5` (`feat(lap 50): crux-2 PRWO formulation built + faithfulness-certified
(wip/GentzenCon)`):

The big new point is the top of `PENDING_WORK.md`: the headline may only need **standard-level** Cor 3.4
for the single Gentzen descent instance, not the full internal-`l : V` Ackermann/F hierarchy. I think this
is the right direction, but it should be treated as a proof-interface correction, not as a completed
shortcut.

Explicit feedback for box / watcher:

1. **Resolve the doc conflict first.** `PENDING_WORK.md` now says crux 1 is standard-level for the
   headline, while `HANDOFF.md` / `HANDOFF-2026-06-23-lap50.md` still say crux 1 is blocked on internal
   Ackermann, and the `STATUS.md` top line still frames Cor 3.4 as internal-level. Make one source of truth:
   either promote the standard-level insight to the handoff/status, or mark it as provisional with the
   exact validation theorem needed.

2. **Narrow `goodstein_implies_prwo`.** The current scaffold says:

```lean
theorem goodstein_implies_prwo (seq : Semisentence Lor 2) :
    PA proves goodsteinSentence -> PA proves prwoInstance seq
```

   That is too broad as an interface. `prwoInstance seq` is a valid "no everywhere-descending graph"
   formula, but it is PRWO only for a fixed total functional primitive-recursive graph. For an arbitrary
   `seq`, the theorem is not the Rathjen schema and is likely false. Replace it with either:
   - a fixed theorem for `gentzenDescentphi`, once its graph/totality/primrec facts are supplied; or
   - a small record carrying the exact instance data: PA proves graph totality/functionality, the graph is
     represented by a fixed primrec function, and there is a standard domination level `l : Nat`.

3. **Make the standard-level Cor 3.4 validation theorem small.** Start `wip/StdCor34.lean` with a theorem
   whose hypotheses already expose the fixed standard level and domination bound. It should reuse
   `ibigMul`, `ig0`/`iblk`, clean append, and then package into `InternalThm35`/Lemma 3.6. Do not try to
   re-prove the lap-49 generic `iVbigMul` route unless a consumer actually needs full internal `l : V`.

4. **Account for the `wip/GentzenCon.lean` placeholders honestly.** The handoff says "2 disclosed crux
   sorries", but the file also has placeholder axioms for `ord`, `R`, `derivesEmpty`,
   `R_preserves_empty`, `ord_R_descends`, and `gentzenDescentphi`. That is fine in `wip`, but the handoff
   should say "2 sorries plus placeholder axioms", or better turn them into fields of a
   `GentzenReductionData` structure so the scaffold is relative to explicit data rather than adding global
   axioms.

5. **Do not overstate `prwoInstance_faithful`.** It is a good kernel-certified encoding check:
   `N models prwoInstance seq` iff the binary graph is not everywhere descending. The remaining crux is to
   prove, inside PA, that the particular `gentzenDescentphi` is total/functional and actually represents
   `n |-> ord (R^[n] d0)`. That belongs next to the arithmetized `ord`/`R` work, not in the generic PRWO
   formula.

6. **Current best next move.** If the standard-level insight is accepted, the highest-value next worker
   task is not full internal Ackermann. It is a fixed-level Cor 3.4 consumer theorem for one represented
   primrec descent, plus a corrected crux-2 interface that applies `prwoInstance` only to that represented
   descent.

## Addendum - after lap 51

Update after reading HEAD `fb0edef` (`feat(lap 51): wip/StdCor34 - internal global Cor 3.4 assembly
(green)`):

Lap 51 did the right next thing. `wip/StdCor34.lean` now proves the global standard-level Cor 3.4 assembly
over explicit abstract hypotheses:

- `salpha_isNF`
- `salpha_desc`
- `salpha_C_le`

Together with `isNF_icorAlpha` in `src/InternalCor34.lean`, the `icorAlpha` brick set is now NF/descent/
C-bound complete. The remaining risk has moved from "can the global assembly be made to typecheck?" to
"are the remaining interface hypotheses exactly the right ones, and are they discharged in the right layer?"

Explicit feedback for box / watcher:

1. **Update stale docs immediately.** `HANDOFF.md` still says HEAD `8119a3e`, `src/` untouched, and "start
   `wip/StdCor34.lean`" as next action. HEAD is now `fb0edef`, `src/InternalCor34.lean` was touched, and
   `wip/StdCor34.lean` exists. `STATUS.md` top is also still lap-50/`1ef8e1e`. `PENDING_WORK.md` is the
   current source of truth.

2. **Do block bookkeeping first, and include all its consumers.** `PENDING_WORK.md` lists `blk/off`
   dichotomy and `blk j + off j <= j`, but `salpha_C_le` also needs:

```lean
hbetaC : forall j, iC (beta (blk j)) <= Cbeta + j
```

   In the Nat template this came from `C_le_wsum_corW` plus `wsum_corBlk_le`, not from descent itself.
   Make it an explicit deliverable of the internal `iwsum`/`iwidx`/`iwoff` bookkeeping brick.

3. **Pin the "standard level" in the eventual consumer.** `StdCor34.salpha` is generic in `l : V` because it
   reuses `icorAlpha`/`iVbigMul`; that is fine as an abstract theorem. The real headline instance should
   visibly specialize `l` to the cast of a fixed meta-level `l0 : Nat`, supplied by Lemma 3.2 for the
   concrete Gentzen descent. Do not let a theorem with free `l : V` drift back into the internal-Ackermann
   obligation.

4. **Track the nonzero/clean side conditions for beta.** To discharge `habove`, the future `igt` proof will
   likely use "tail below `omega^(l+1)`" plus nonzero/NF of the lead `beta (blk a)`. The current abstract
   theorem hides this inside:

```lean
habove : forall n m a, iAbove (ocExp (igt n m)) (iVbigMul (beta (blk a)) (l + 1))
```

   When implementing `igt`, expose and prove the source facts once rather than re-solving them at every
   `habove` call.

5. **Do not wire into `wip/GentzenCon`'s broad `goodstein_implies_prwo` yet.** The lap-50 warning still
   stands: `goodstein_implies_prwo (seq)` is too broad for arbitrary `seq`. Once `StdCor34` is connected to
   Thm 3.5/Lemma 3.6, apply it to a represented fixed primrec graph, especially `gentzenDescentphi`, or use
   a record carrying totality/functionality/primrec/standard-domination data.

6. **Best next chip:** implement the internal `corW/wsum/blk/off` bookkeeping as a small wip module that
   proves exactly the hypotheses consumed by `salpha_desc` and `salpha_C_le`. This is more mechanical than
   `igt`, and it will harden the interface before the deeper standard-level `g` recursion starts.

## Addendum - after HEAD a25c408

Update after reading HEAD `a25c408` (`feat(lap 51): habove_of_igt_exp - discharge StdCor34 clean-append
family from g<omega^(l+1)`):

Good new movement: `wip/StdCor34.lean` now has

```lean
habove_of_igt_exp :
  0 < l →
  (∀ n, β n ≠ 0) →
  (∀ n, isNF (β n)) →
  (∀ n m, ocExp (igt n m) = 0 ∨
      ∃ j, j ≤ l ∧ ocExp (igt n m) = ocOadd 0 j 0) →
  ∀ n m a, iAbove (ocExp (igt n m)) (iVbigMul (β (blk a)) (l + 1))
```

That is the right interface simplification. The old 3-argument `habove` obligation should now be treated
as an internal implementation detail of `StdCor34`, not as something every downstream worker tries to
prove directly.

Explicit feedback for box / watcher:

1. **Promote the exponent-bound interface.** Add wrapper theorems or a small structure around
   `salpha_isNF` / `salpha_desc` / `salpha_C_le` that take `higt_exp`, `hbeta0`, and `hbetaNF`, then call
   `habove_of_igt_exp` once. This prevents the next worker from targeting the obsolete bulky `habove`
   shape.

2. **Do not hide the `0 < l` requirement.** `habove_of_igt_exp` currently needs `hl : 0 < l`. That is fine
   if the eventual standard level is explicitly chosen as a positive/successor level, but it should be
   justified at the headline interface. Either prove a "bump the standard domination level" lemma, or split
   the helper so the finite-tail branch does not require global `0 < l`.

3. **The crux-1 interface is now very clean.** Block bookkeeping should deliver:
   `hblk_dich`, `blk j + off j <= j`, and `hbetaC : iC (beta (blk j)) <= Cbeta + j`.
   The `igt` recursion should deliver:
   `higtNF`, `higt0`, `higt_within`, `higtC`, and the new `higt_exp`.
   Keep those two deliverable lists separate; it will make failures local.

4. **Prove beta nonzero once, not everywhere.** The new helper needs `∀ n, β n ≠ 0`. For a strict
   infinite descent this should follow from `hbetaDesc : ∀ n, icmp (β (n+1)) (β n) = 0` plus
   `icmp_right_zero_ne_zero` in `InternalONote`. Bank that as a tiny lemma before wiring wrappers.

5. **Block bookkeeping is still the best next chip.** The latest commit shrinks the `igt` clean-append
   side condition, but it does not reduce the need for internal `corW/iwsum/iwidx/iwoff`. Mirror
   `Grzegorczyk.wsum` / `widx` / `woff` first, including the C-bound consumer `hbetaC`; that hardens the
   global `salpha_C_le` path before starting the deeper standard-level `g`.

6. **Docs are now more stale, not less.** `HANDOFF.md`, `STATUS.md`, and the top of `PENDING_WORK.md` still
   do not mention `a25c408` or `habove_of_igt_exp`. If a worker is choosing from docs alone, they can still
   be sent back to proving the old `habove` family.

## Addendum - after concurrent Gentzen seam checks

Update after seeing the fresh uncommitted `wip/GentzenCon.lean` seam-check examples:

This is good defensive engineering. The three new examples compile-check exactly the integration points
that have been risky in this repo:

- crux 1 and crux 2 use the same `prwoInstance gentzenDescentφ`;
- crux 2 outputs Foundation's actual `↑𝗣𝗔.consistent`;
- the assembled route has exactly the `Reduction.not_proves_of_implies_consistency` input type.

Feedback for box / watcher:

1. **Keep these guards.** They are cheap and useful even while the crux bodies are still `sorry`; they will
   keep protecting the interfaces as the placeholder bodies are replaced.

2. **They do not remove the `goodstein_implies_prwo` overbreadth.** The examples currently compose through
   `goodstein_implies_prwo (seq)`, which is still too broad for arbitrary `seq`. When that theorem is
   narrowed to a fixed Gentzen instance or a `PrimrecDescentInstance` record, update the examples rather
   than deleting them.

3. **Consider naming them if they become part of the watcher protocol.** Anonymous `example`s are fine as
   compile guards, but named theorems like `seam_prwo_shared`, `seam_con_foundation`, and
   `seam_reduction_hook` would make later audits and grep-based status checks easier.

4. **Still do not promote `wip/GentzenCon` to `src/`.** The seam is now well guarded, but the file still has
   the two disclosed crux `sorry`s plus placeholder axioms for `ord`, `R`, `derivesEmpty`,
   `R_preserves_empty`, `ord_R_descends`, and `gentzenDescentφ`.

## Addendum - after HEAD c9fc6ea (`wip/BlkRec.lean`)

Update after reading HEAD `c9fc6ea` (`feat(lap 52): BlkRec - crux-1 brick 1, definable block bookkeeping
blk/off`) and checking `lake env lean wip/BlkRec.lean`:

The state-machine brick is now green and worth keeping. It avoids internal `findGreatest` by recursing on
the pair `(blk, off)`, and it gives the direct consumers:

- `blk_succ_dich` for `StdCor34.salpha_desc`;
- `off_succ_of_blk_eq` for the within-block `igt` descent bridge;
- `blk_add_off_le` / `blk_le` for basic index bookkeeping.

The remaining caution is about the C-bound consumer.

Feedback for box / watcher:

1. **Do not overclaim `blk_le` as `hβC`.** `StdCor34.salpha_C_le` needs

```lean
hβC : ∀ j, iC (β (blk j)) ≤ Cβ + j
```

   In the `Grzegorczyk` template this comes from the width partial-sum fact
   `C (β n) ≤ wsum (corW β) n ≤ j`, not merely from `blk j ≤ j`. The state-machine proof still needs an
   invariant like `blk j = 0 ∨ znth wseq (blk j - 1) ≤ j`, or better an internal `wsum`/elapsed invariant
   `wsum W (blk j) ≤ j`. Without that, the C-bound consumer is not discharged.

2. **Be careful with `wseq` as a global width oracle.** A fixed HFS sequence code is finite; it is not a
   total width function `W : V → V` for all internal indices. Either specialize the construction to a
   concrete definable width function `W` when `β` lands, or use a prefix-table construction with a proved
   prefix-invariance theorem. A single fixed `wseq` parameter is fine for local arithmetic lemmas, but it
   should not silently become the final global `blk/off` function.

3. **Next small target:** add the missing width/elapsed invariant before wiring to `salpha_C_le`. The
   current brick already has the first three shapes; the missing one is the C-bound support.

4. **The scratchpad check files are untracked.** `scratchpad/BlkRec_chk.lean` and `scratchpad/blkchk.lean`
   appear to be temporary axiom-check harnesses. Keep them out of the build unless they are intentionally
   promoted.
