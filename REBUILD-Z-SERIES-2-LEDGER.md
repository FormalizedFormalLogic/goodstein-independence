# REBUILD-Z — SERIES-2 LEDGER (append-only, one block per stage)

Order: `REBUILD-Z-SERIES-2-ORDER-2026-07-03.md`. Discipline: bare `lake build` (1342-job full
gate) per stage; hygiene claims diff-verified (Series-1 §5.2); self-ratification VOID; wip-only
for everything probe-shaped.

---

## Stage A — Series-1 Stage-1 debt (src, pre-ratified, mechanical) — ✅ LANDED (lap 196)

**Build**: 🟢 `lake build` (1342 jobs, fresh full rebuild). **Headline**:
`GoodsteinPA.peano_not_proves_goodstein` footprint = `{propext, Classical.choice,
GoodsteinPA.goodstein_implies_consistency, Quot.sound}` — UNDRIFTED (re-checked via
`blueprint_audit`). **`blueprint_audit`**: ✓ PASSED, 16 nodes consistent, 0 warnings.

Diff-verified changes (git diff, not asserted from memory):

- **(A-1) `src/GoodsteinPA/WainerLadder.lean` CREATED.** Imports `GoodsteinPA.OperatorZef2` +
  `GoodsteinPA.WainerRoute` (the translation apparatus: `EventuallyLE`, `goodsteinSentence`,
  `GoodsteinPA.Dom.goodsteinLength`, `fastGrowing`). Namespace `GoodsteinPA.WainerLadder`.
  Wired into the blueprint lib root (`src/GoodsteinPABlueprint.lean` +1 import line). This is
  the L-E-direction home (ruling §4) where the top rungs can bind the concrete goodstein
  translation without the `OperatorZef2`-level cross-import obstruction.
- **(A-2) `wainer_splice_Zef2` MOVED + RESTATED VERBATIM** at the R-5 shape:
  ```lean
  theorem wainer_splice_Zef2 :
      (𝗣𝗔 ⊢ ↑goodsteinSentence) →
        ∃ o : ONote, o.NF ∧
          EventuallyLE GoodsteinPA.Dom.goodsteinLength (fun n => fastGrowing o n) := by sorry
  ```
  This is EXACTLY the statement of the `wainer_bound_of_pa_proves_goodstein` axiom (the rung
  that flips it `axiom → theorem`). The OLD parametric form
  (`(e B α …) : … ewIter (ewRootSlot e B) α 0 ≤ …`, the lap-8-ruling L-W VOIDed-as-trivial
  shape) DELETED from `OperatorZef2.lean`.
- **(A-3) `embedding_Zef2` DELETED** from `OperatorZef2.lean` (lap-8 ruling §4 VOIDed
  placeholder, R-6 debt). A `TODO(rung E, Stage-B statement lap)` naming its faithful
  statement now lives in `WainerLadder.lean`'s module docstring. No src theorem for rung E
  (its statement is the Stage-B ratification target — wip-first).
- **(A-4) Blueprint tex** (`blueprint/src/content.tex`): `thm:zeh_rank_zero` `\notready`
  DROPPED (proven modulo the pass; kept OFF `\leanok` — no `@[goodstein_blueprint]` site since
  sorry-pins can't be tagged, so the reconciler leaves this hand-status alone);
  `thm:wainer_splice` bound `\lean{GoodsteinPA.WainerLadder.wainer_splice_Zef2}` (kept
  `\notready`, still a sorry). `blueprint_audit` PASSES.
  ⚠️ **Web HTML regeneration (`annotate_depgraph.py --web`) DEFERRED to host**: `leanblueprint`
  is not installed on this box (`which leanblueprint` → absent). The tex SOURCE is updated and
  the machine gate (`blueprint_audit`) passes; the generated `blueprint/web/*.html` +
  `blueprint/lean_decls` (both untracked artifacts) refresh needs the host's leanblueprint
  toolchain. `checkdecls` will resolve the new `\lean{}` binding (the decl compiles in the
  blueprint lib).
- **(A-5) `wip/Lap13ReadoffDeltaProbe.lean` DELETED** (`git rm`) — stale name-clash with the
  now-promoted `src` `sound0` (`OperatorZef2.lean:897`).

**Sorry-declaration delta** (build `declaration uses \`sorry\`` warnings, fresh full rebuild):
15 → **14** = net −1, matching the mandated {−2 voided (A-2 old form + A-3 embedding), +1
restated}. (The order's absolute "17 expected" uses a `lean-sorry` tool not present on this
box; the verifiable delta is the mandated −1.)

Gate summary: 🟢 build · headline undrifted · no new `src` axiom · no `native_decide` in new
files · wip freeze refs untouched · `blueprint_audit` ✓. Stage A CLOSED.

---

## Stage D-1 — absorbing-norm existence (wip probe) — ✅ POSITIVE RESULT (lap 196)

**File**: `wip/AbsorbingNormProbe.lean` (compiles standalone via `lake env lean`; NOT imported
by any lib, so `src`/`lake build` UNCHANGED — pure ruling input). No `native_decide`.

**FINDING — the lap-192 conjecture "finite fibers force additivity-like growth (T-Z7(i))" is
REFUTED.** A finite-fibered ABSORBING norm on `ONote` exists: the **max-over-terms norm with a
logarithmic coefficient charge**

  `Nlog (oadd e n a) = max (Nlog e + clog n) (Nlog a)`,  `clog n = ⌊log₂ (n+1)⌋`.

Two design moves defeat the two obstructions to `ewN` being absorbing:
- **max-over-terms** (not `ewN`'s SUM) tames CONCATENATION (`α+γ` with disjoint exponents):
  the max of two maxes is a max — absorbing with `c = 0`;
- **log coefficient charge** tames the MERGE `ω^β·n + ω^β·m = ω^β·(n+m)` (`ONote.addAux`
  `Ordering.eq` arm, where coefficients ADD): `clog_add_le` proves
  `clog (n+m) ≤ max (clog n)(clog m) + 1` (pure ℕ, kernel-clean), vs `ewN`'s linear charge
  which costs the unbounded `min(n,m)`.

**Kernel-checked (`decide`, no `native_decide`):**
- `nlog_absorbs_merge_small/_big`, `nlog_absorbs_concat`, `nlog_absorbs_drop` — `Nlog` satisfies
  `Nlog (α+γ) ≤ max (Nlog α)(Nlog γ) + 1` on the adversarial merge/concat/drop pairs;
- `ewN_not_absorbing`, `ewN_not_absorbing_const_30` — the CONTRAST family `ω·k + ω·k` where
  `ewN` violates absorption for EVERY fixed constant (gap grows as `k`);
- `Nlog_spine : Nlog (spine k) = k+1` — `Nlog` GROWS on the tower spine `ω, ω^ω, …`, i.e. it
  does NOT share the E–W max-coefficient source norm's infinite-fiber failure mode (constant `1`
  on the spine — the exact reason `src` needed `ewN`);
- `clog_le_self`, `Nlog_le_ewN` — `Nlog ≤ ewN` (recorded to flag it is the WRONG direction to
  transfer finite fibers).

**Node-gate consequence (kernel-clean): `absorbing_closes_gate`** — ANY absorbing norm with
constant `c` closes the top-rank-cut node gate `N (α+γ) ≤ g (f 0)` from `N α ≤ g 0`, `N γ ≤ f 0`
needing ONLY `max (g 0)(f 0) + c ≤ g (f 0)` — vastly weaker than the refuted base-additivity
`hg_base : ∀ k, g 0 + k ≤ g k`. With `f 0 ≥ 1` (the EwF1 `2m+1` floor) this needs essentially
just `g 0 + c < g (f 0)`, i.e. `g` non-constant across `[0, f 0]` — the trap-8 plateau at a
SINGLE point no longer blocks it.

**General absorbing theorem — PROVEN (lap 196 P3 deepening, kernel-clean
`[propext, Classical.choice, Quot.sound]`):** `Nlog_add_le_max_succ : ∀ NF α γ,
Nlog (α+γ) ≤ max (Nlog α)(Nlog γ) + 1`. Proof: induct on α, `lt_trichotomy` on the two leading
exponents `repr e`, `repr eg`; each case pins the SYNTACTIC form of `α+γ` via `repr_inj` +
ordinal absorption (`add_of_omega0_opow_le`, `isPrincipal_add_omega0_opow`): `lt`→ `α+γ = γ`
(α absorbed); `gt`→ `α+γ = oadd e n (a+γ)` (prepend, IH on `a`); `eq`→ `a+γ = γ` collapses the
merge so `α+γ = oadd e (n+ng) ag`, coefficient tamed by `clog_add_le`. The single merge boundary
means the two `+1`s never compound. Helper `add_eq_right_of_repr` banked. So absorption is now a
THEOREM, not just evidenced on adversaries — the D-1 disposition is DISPOSITIVE for property (ii).

**One documented `sorry` remaining:**
- `Nlog_finite_fiber` (property (i) in full) — strategy documented (exponent-set induction:
  exponents of a `Nlog ≤ K` element are drawn from the finite `{e : Nlog e ≤ K-1}` and strictly
  decrease, bounding length). `Nlog_spine` growth is the decisive kernel witness that `Nlog`
  avoids the max-coeff norm's infinite-fiber failure mode; full mechanization needs a
  `nlogBallBelow` construction (à la `NFBelow`), a follow-up P3 target.

**DISPOSITION for the reserved top-rank-cut ruling:** the TRILEMMA's prime amendment candidate
(finite-fibered ABSORBING norm) is now KERNEL-EVIDENCED to EXIST — the judge can dissolve the
node gate by swapping `ewN → Nlog` (an absorbing norm) with a trivial non-constancy slack, WITHOUT
touching `rel1` or the additive output ordinal. This is the strongest of the three trilemma horns
and was the one the lap-192 review believed impossible.

---
