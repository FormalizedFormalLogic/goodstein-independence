# HANDOFF — 2026-06-22 (lap 7)

> **NEXT LAP FIRST ACTION:** read this + `STATUS.md` + `ANALYSIS-2026-06-22-cutelim-k-threading.md`
> (the WHOLE thing — ADDENDA 1–4 are the design story; ADDENDUM 4 + the "NEXT MOVE" below are the live
> plan) + `PENDING_WORK.md` (the A–F inventory at the top). Build is **green** (`lake build GoodsteinPA`,
> 1257 jobs). Forward file: **`wip/SplitZinfty.lean`** (§19.2–19.5 on the `(k,d)` split, sorry-free;
> `lake env lean wip/SplitZinfty.lean`). Headline `peano_not_proves_goodstein` still a literal `sorry`
> (designated open target — anti-fraud, correct). **Next:** the control-ordinal operator calculus (§19.6
> needs it; `(k,d)` carries §19.2–19.5 but not §19.6's witness-index — ADDENDUM 4).

## What landed this lap (21 commits, all verified)

This was a **crux-resolution + ingredient lap**, not a new-girder-built lap. The §19.6 cut-reduction
that lap 6 pointed at turned out to have a deeper layer; this lap mapped it precisely and proved the
one ingredient that's fully tractable.

1. **RESOLVED the cut-elim `k`/`τ` crux offline** (the open lap-6 `ON-LINE-REQUEST`). Read Towsner
   §15–§20 on disk. The lap-6 "norm grows under addition ⟹ cut-elim breaks `norm<k`" worry was a
   **misframing**: (a) `k` is NOT fixed — it grows (§19.5 `k↦2k`; §19.6 `k↦h_{β#ω}(k)`; §19.7
   `k↦h_{ω^α}(k)`); (b) `lowerBound_hardy_selfcontained` is already `∀k` ⟹ growth harmless; (c) every
   `ONote` is `<ε₀` by construction ⟹ ε₀ side-condition FREE. ⟹ **state the whole cut-elim chain
   existentially in `k`** (`CutFree α Γ := ∃k, Zk α k 0 Γ`); ordinary `+` with slack (no `nadd`).
   Full write-up: `ANALYSIS-2026-06-22-cutelim-k-threading.md` (top section).

2. **Route decision: STAY ROUTE B** (the operator delegated it). Recorded in `STATUS.md` with rationale
   — the one doubtful Route-B girder (the `(α,k)` cut-elim bookkeeping) is exactly what (1) resolved;
   Route A's surface is larger. Archived the operator route-choice note, removed `OPERATOR-NOTE`.

3. **PROVED `norm_addAux_le` + `norm_add_le {α γ NF} : norm(α+γ) ≤ norm α + norm γ`** (axiom-clean,
   banked in `wip/BoundedZinfty.lean`). This is the `τ(α#β)≤τα+τβ` §19.6 budget fact. **NF is essential**
   — the NF-free version is machine-checked FALSE; the equal-exponent coefficient blow-up is killed by
   **additive-principality absorption** (`a + γ = γ` when `repr a < ω^(repr e) ≤ repr γ`, via
   `Ordinal.add_of_omega0_opow_le`). `wip/BoundedZinfty.lean` is now **sorry-free**.

4. **PROVED both Hardy ingredients option-2 (below) needs** (axiom-clean, in `src/`, build green 1257):
   - `hardy_add_ofNat {α NF} : hardy (α + ofNat c) n = hardy α (n + c)` (`src/Hardy.lean`) — finite-tail
     Hardy additivity via the successor rule.
   - `hardy_shift_lt_goodsteinLength {α NF} (c) : ∃ N, ∀ x ≥ N, hardy α (x+c) < G x` (`src/LowerBound.lean`)
     — controlled-index domination (the lower bound survives a linear ω-rule reindexing).
   **So the recommended §19.6 fix is de-risked at the Hardy layer**: a linearly-reindexed ω-rule premise
   is absorbed by a constant ordinal bump, and the lower bound's I∀ case reduces to a direct instance.
   What remains for option 2 is the *calculus refactor* (generalize `B.allI`/`Zk.allω` to a controlled
   index + re-prove `allInv` + `lowerBound_hardy_selfcontained`) — a fresh undertaking; **start it
   fresh-headed, do not half-break the clean state.**

6. **IMPLEMENTED the split-index design through §19.5** (`wip/SplitZinfty.lean`, 603 lines, sorry-free).
   See the ⭐ section below. Eliminated option 2 (numeric swap), derived the `(k,d)` split (ADDENDUM 3),
   built the calculus + `mono_k`/`mono_d`/`mono_c` + full inversion suite + §19.5 cut-reductions on it.
   `allInv`'s principal case compiling is the end-to-end validation that the design closes the
   obstruction that defeated both single-index calculi.

7. **Banked all §19.6 prerequisites** into `SplitZinfty`: ordinal/norm helpers (`add_lt_add_left_NF`,
   `le_add_left_NF`, `norm_omegaPow`, `norm_addAux_le`, `norm_add_le`) + osucc descent lemmas
   (`osucc_lt_osucc`, `add_osucc_descent`). Everything `cutReduceAll` needs except the calculus design.

8. **Found + recorded (honestly) the §19.6 SECOND obstruction (ADDENDUM 4):** the `(k,d)` split closes
   the norm-budget but NOT the witness-index growth (principal cut's `hardy γ(·)` witness ⟹ super-linear
   k-part through commuting ω-rules). ⟹ the full operator is needed. Refined the design to a concrete
   **control-ordinal `e`** (witness index `hardy e (n+k)+d`); de-risked the control side (existing
   `hardy_le_of_lt`); only the lower-bound side needs general Hardy additivity (infra B). Full
   open-obligation inventory + 3 paths each in `PENDING_WORK.md` (A–F).

5. **Mapped the real §19.6 frontier — the `allω`-commuting obstruction.** Starting `cutReduceAll`,
   found that the commuting ω-rule case (∃-side's last rule is an ω-rule) **cannot keep the ω-rule's
   `max{k,n}` norm budget after adding `α` to the bound**: `norm(α+βₙ) ~ norm α + n` exceeds `max K n ~
   n` for large `n`, for ANY fixed `K` (norm is not `<`-monotone, so `βₙ<β` does not bound `norm βₙ`;
   natural sum + `τα<k` don't save it). Towsner's "follows from IH" glosses this. This is the genuine
   remaining depth of step 1. Full derivation + 3 attack options in the ANALYSIS **ADDENDUM**;
   `ON-LINE-REQUEST` re-filed (one layer down — Buchholz operator-control / S-W bounding lemma).

## ⭐ LAP-7 LATE PROGRESS — split-index design IMPLEMENTED through §19.5 (`wip/SplitZinfty.lean`)

The option-1 design was not just recommended — it was instantiated and validated. **`wip/SplitZinfty.lean`
(603 lines, sorry-free, compiles standalone)** defines the **split-index calculus `Zkd α k d c Γ`** (the
`(k,d)` design of ADDENDUM 3: ω-premise `n` at `(max k n, d)`, budget `max(k,n)+d`) and ports the entire
§19.2–19.5 layer onto it:
- `mono_k` (idempotent `max`-part), **`mono_d`** (new — the additive cut-shift part), `mono_c`, `weakening`;
- full inversion suite `orInv`/`andInvL`/`andInvR`/`allInv` — **`allInv`'s principal case validates the
  design**: `d` rides inert, `k`-part collapses idempotently (`max (max k n₀) n₀ = max k n₀`), exactly
  the move that defeated both naive single-index swaps;
- §19.5 `cutReduceConj`/`cutReduceDisj` (+ `lt_osucc`), index `(k,d)` preserved.

This is full parity with the old single-index `wip/BoundedZinfty.lean` §19.2–19.5, on a design that
closes the §19.6 *norm-budget* obstruction (the `d`-bump). **However — see ADDENDUM 4 / the corrected
NEXT MOVE below — `(k,d)` does NOT close §19.6's *witness-index* obstruction; the full Buchholz operator
is needed.** `SplitZinfty.lean` is the correct §19.2–19.5 stepping stone the operator calculus ports
from; `wip/BoundedZinfty.lean` is the older single-index reference.

### THE NEXT MOVE — the Buchholz **operator** calculus (⚠️ `(k,d)` is NOT enough for §19.6)
⚠️ **CORRECTION (ADDENDUM 4, end of lap 7):** setting up `cutReduceAll` revealed §19.6 has **two**
obstructions; `(k,d)` closes only one:
1. **norm-budget** (`norm(α+βₙ) < budget`) — **CLOSED by the `d`-bump** (`d ↦ d + norm α`). ✓
2. **witness-index** (NEW) — the principal `exI` cut pulls the k-part up to the witness
   `w ≤ hardy γ (k'+d)`; in the **commuting `allω`** case the IH runs at `k' = max k n` (grows with `n`),
   so the cut index grows like `hardy(·)(n)` — **super-linear**. The reconstructed ω-rule needs premise
   `n` at `max k_c n` (linear), which CANNOT absorb a Hardy-growing index (`mono_k` only raises). ✗

So **`cutReduceAll` is NOT completable on `Zkd`** — `max k n` premise shape can't pass a Hardy-growing
witness index. This needs the **full Buchholz operator** `H` (a set/predicate on the witness index,
*closed under `hardy`*), so the principal cut's `hardy(·)(·)` witness stays in `H[{n}]` uniformly. Plan:
- Define `Hkd α H d c Γ` (or `H ⊢^α_{d,c}`): ω-premise `n` controlled by `H[{n}]` (closed under `hardy`/
  the ordinal functions); True/∃ side conditions by `H`; keep the additive `d` (norm budget) alongside.
- **Port §19.2–19.5 from `wip/SplitZinfty.lean`** — mechanical, `max k ·` ⤳ `H` (the inversions/§19.5
  proofs there are the template and were the point of building `SplitZinfty`).
- §19.6 `cutReduceAll`: principal cut's witness `hardy γ (·) ∈ H` (closure), commuting `allω` premise
  index in `H[{n}]` (closure) — both obstructions close. Ordinal framing `α+γ` + `osucc` (descent
  lemmas `add_osucc_descent` etc. already in `SplitZinfty`); `d`-bump for the norm budget.
- §19.7 `cutElimStep` (`ω^α`, `norm_omegaPow` banked) + §19.9 `cutElim`.
- Lower bound for the operator calculus: I∀ case via `hardy_shift_lt_goodsteinLength` (proved) — the
  controlled index stays slope-1 in `n` once `H`'s base is fixed. Then the subformula bridge ⟹ headline.

`SplitZinfty.lean` is a **correct stepping stone** (§19.2–19.5 done on the `(k,d)` split; the operator
generalizes its `max(k,·)`-part to a `hardy`-closed `H`, keeping `d`). `ON-LINE-REQUEST` (PA
operator-control spec — Buchholz §9) remains the literature ask.

<details><summary>Superseded: the abstract option-1 recommendation (now implemented above)</summary>
## (superseded) §19.6 attack **option 1** (function/operator-valued `allω` index)

The principal `exI` case of `cutReduceAll` is clean; the live frontier is the commuting `allω` case.
**Lap-7 tried option 2 (global numeric index swap) and ELIMINATED it** — see `ANALYSIS-…-cutelim-k-
threading.md` ADDENDUM 2. Summary of why no single numeric `idx(k,n)` works:
- `max k n` (current): good for `allInv` (principal case needs idempotence `max(max k n₀)n₀=max k n₀`),
  but breaks §19.6-commuting (`norm(α+βₙ)~norm α+n > max K n` for large `n`).
- `k + n`: fixes §19.6-commuting (`(k+n)+norm α=(k+norm α)+n`), but breaks `allInv` — the lingering-
  duplicate principal subcase produces index `k+2n₀` (slope 2, no idempotent collapse), forcing the
  lower bound to need `hardy α (2n) < G n` (multiplicative rescaling; the additivity lemma is slope-1).

**Revised recommendation = option 1: each `allω` carries a controlled index *function* `g : ℕ → ℕ`**
(`g n ≤ n + const`), and rules compose `g`s — idempotently for `allInv`, post-composing the `+norm α`
shift for cut-elim. This is Buchholz operator-controlled derivations specialized to PA; it's the only
design that closes BOTH obstructions, and it keeps slope 1 so the proved domination lemmas apply:
- `hardy_add_ofNat {α NF} : hardy (α + ofNat c) n = hardy α (n + c)` (`src/Hardy.lean`, axiom-clean).
- `hardy_shift_lt_goodsteinLength {α NF} (c) : ∃ N, ∀ x ≥ N, hardy α (x+c) < G x` (`src/LowerBound.lean`).
- **Plan:** (a) refactor `Zk.allω` (`wip/BoundedZinfty.lean`) + `B.allI` (`src/LowerBound.lean`) to carry
  `g` with a control predicate (`∀n, g n ≤ n + c_g` or similar); (b) re-prove the inversion suite + cut
  reductions with `g` (allInv composes `g` idempotently — should be cleaner than the numeric juggling);
  (c) re-prove `lowerBound_hardy_selfcontained` with `g` (I∀ case: `hardy α (g x) ≤ hardy α (x+c_g) < G x`
  via the two lemmas); (d) `cutReduceAll` commuting case reconstructs at `g'(n) = g(n) + norm α`.
- **Caution:** REFACTORS the (currently sorry-free) `wip/BoundedZinfty.lean` + M6 lower bound. Start
  fresh-headed; don't half-break the clean state. Reference `buchholz-beweistheorie` §9 (on disk) for the
  operator-control pattern.
- **Fallback:** Buchholz's full operator `H` (set-valued, not just a ℕ→ℕ function) if the function form
  still can't express some closure; `ON-LINE-REQUEST` re-filed for the precise PA operator-control spec.
</details>

## State of the spine (Route B, hardest-first)
- **M1, M2, Phase 0/1** — done, clean.
- **M5 (unbounded `(α,c)` cut-elim, `src/Zinfty.lean`)** — done, clean. Template for `cutReduceAll`
  (lap-3 `cutReduceAllAux` at `src/Zinfty.lean:785` — the structure to port to `Zk`).
- **M6 (Hardy lower bound, `src/LowerBound.lean`)** — done, clean (`∀k`).
- **Step 1 (`Zᵏ` cut-elim, `wip/BoundedZinfty.lean`)** — calculus + §19.2–19.5 (inversions, ∧/∨
  reductions) + `norm_add_le`/`norm_addAux_le` done. **§19.6 (`cutReduceAll`) = the live crux**
  (commuting-`allω` obstruction; option 2 above). Then §19.7 `cutElimStep` + §19.9 `cutElim`.
- **Step 2 (M4 embedding)** — independent of the §19.6 blocker; reconnaissance done lap 6 (see lap-6
  HANDOFF + `PENDING_WORK` step 2). Foundation-heavy. A viable parallel thread if §19.6 stalls.
- **Step 4 (subformula bridge), M7a (language gap), M7b (assembly)** — downstream.

## Notes
- **Aristotle:** left idle — the §19.6 work is not cleanly self-containable (needs the real Hardy/
  domination defs + the calculus). The bounded self-contained target (Hardy argument-shift) was just
  proved locally, so it's no longer a candidate.
- **`WebFetch` is dead in the box; `WebSearch` works.** The re-filed `ON-LINE-REQUEST` is for a
  networked session; meanwhile option 2 is offline-doable, so don't block on it.
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`. Headline `sorry` intact.

## File map (changes this lap)
- `ANALYSIS-2026-06-22-cutelim-k-threading.md` — **NEW**: the `k`/`τ` crux resolution + §19.6 ADDENDUM.
- `src/GoodsteinPA/Hardy.lean` — added `hardy_add_ofNat` (+ 2 private helpers); proved, build green.
- `src/GoodsteinPA/LowerBound.lean` — added `hardy_shift_lt_goodsteinLength`; proved, build green.
- `wip/BoundedZinfty.lean` — added `norm_addAux_le`, `norm_add_le` (both proved); sorry-free (single-index reference, now superseded).
- `wip/SplitZinfty.lean` — **NEW**: split-index `(k,d)` calculus `Zkd` + §19.2–19.5 layer, sorry-free (the forward path).
- `STATUS.md`, `PENDING_WORK.md` — lap-7 entries, route decision, §19.6 plan + option 2.
- `ON-LINE-REQUEST.md` — re-filed (§19.6 commuting-case bounding).
- `archive/findings/…operator-route-choice.md` — archived; `OPERATOR-NOTE…` removed.
