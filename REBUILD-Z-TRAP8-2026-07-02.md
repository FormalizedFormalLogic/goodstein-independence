# REBUILD-Z — candidate EIGHTH statement trap (grind lap 6, global lap 186, 2026-07-02)

> **Escalation, not a self-ratification.** Written by grind lap 6 while discharging the ratified
> laps-6–7 order (`E-2026-07-02-JUDGE-rebuild-z-lap5-validation.md` §5). Item 1 landed
> (`iterSlot_monotone`, committed `c39f08e`); attacking item 2 (the pass induction on
> `cutElimPass_Zf`) surfaced a kernel-anchored obstruction in the **locked** C2 output slot. Per
> the entrance-lock (`REBUILD-Z-LAP5-ENTRANCE-2026-07-02.md` §preamble/§5): a grind lap that
> believes a locked form is wrong **STOPS and escalates** — self-ratifying a C2 change is VOID.
> The locked statement is UNTOUCHED. This doc hands the shape question back to the architect/judge.

## 1. Claim

The lap-5-amended pin-3 output slot — the **bare** diagonalizing iterate `iterSlot f α`, keyed to
the *input* height `α` — cannot be threaded through the cut-elimination induction, because
`iterSlot f ·` is **not ordinal-monotone**: it dips at the base of a limit, so a finite `β < α`
produces a *larger* iterate than `α` at small arguments. Every induction case with a `β < α`
sub-derivation (`weak`, `exI`, `allω`, `cut`) must lift that sub-derivation's slot `iterSlot f β`
up to the parent's `iterSlot f α`, and the only slot move available (`Zef.mono_f`) raises slots —
it needs `∀ x, iterSlot f β x ≤ iterSlot f α x`, which is **kernel-false**.

This is the same evidence grade as traps 6/7: kernel-localized + structurally forced, an
*unprovable-as-stated* obstruction (not a falsity proof of a mathematical claim — the pass is true
for the RIGHT slot; the bare-`iterSlot f α` shape is what fails).

## 2. Kernel evidence (`wip/Trap8Probe.lean`, compiles clean standalone)

`f = (·+1)` (monotone + inflationary — both pin hypotheses), `β = ofNat 2`, `α = ω = oadd 1 1 0`
(both NF, `2 < ω`):

```
iterSlot f 2 0 = 3          -- f^[3] 0  (iterSlot f (ofNat 2) = f^[3])
iterSlot f ω 0 = 2          -- rides ω[0] = 1 : iterSlot f ω 0 = iterSlot f 1 0 = f^[2] 0
```

so `iterSlot f 2 0 = 3 > 2 = iterSlot f ω 0` (`trap8_dips_at_limit_base`), hence the `mono_f`
premise `∀ x, iterSlot f 2 x ≤ iterSlot f ω x` is refuted at `x = 0`
(`trap8_mono_f_lift_fails`).

**Root cause.** The diagonalizing iterate (trap-7's fix) evaluates a limit `α` at argument `x`
through `α[x]` — at `x = 0` that is `ω[0] = 1`, i.e. `iterSlot f ω 0 = f^[2] 0`, a *small* value.
A finite `β = 2` below ω has `iterSlot f 2 0 = f^[3] 0`, which is larger. trap-7 fixed the
`allω`-BRANCH unboundedness precisely by making the branch index ride a *large* argument
(`rel1 (iterSlot f α) n`, evaluated at `max n x ≥ n`). The fix bought base-argument SMALLNESS,
which now bites everywhere the slot is read near argument 0: the `weak` slot-lift, and the
`exI`/`cut` witness bound `n ≤ (slot) 0`.

## 3. Why no proof method dodges it (statement-intrinsic)

The obstruction is in the STATEMENT, not the proof. Whether the pass is proven by structural
induction on the derivation, or by well-founded recursion on the ordinal `α`, or via an auxiliary
lemma: the *output type* is `ZefProv (collapse α) e H (iterSlot f α) c Γ` with the slot **rigidly**
`iterSlot f α`. Take the minimal witness — a root `exI`:

```
D = Zef.exI φ n (hβ : β < α) … (hbound : n ≤ f 0) (dd : Zef β e H f (c+1) (insert (φ/[nm n]) Γ))
```

The output must be an `∃⁰φ`-sequent derivation at slot `iterSlot f α`. The only rule producing a
bounded-witness `∃⁰φ` sequent is `exI` (mod `wk`/`weak`), which needs a sub-derivation **at slot
`iterSlot f α`**. The eliminated `dd` is at slot `iterSlot f β` (its own height); lifting β→α via
`mono_f` requires `iterSlot f β ≤ iterSlot f α` — refuted. No choice of recursion changes the
sub-derivation's slot, which is pinned to `iterSlot f β` by the theorem's own conclusion applied
at height `β`. `ZefProv`'s existential only slackens the *height*, never the *slot*.

### 3a. The SHARP form — no fixed-argument slot works at all (`no_fixed_arg_monotone_unbounded_slot`)

This is not "the diagonalizing iterate happens to dip; pick a better one." **No** output-slot map
`S : ONote → ℕ` read at a FIXED argument can be both ordinal-monotone and unbounded along the finite
ordinals (both of which the pass requires):

- **monotone** `β < α → S β ≤ S α` — needed for the `weak`/`exI`/`cut` lift above;
- **unbounded** `n ≤ S (ofNat n)` — forced, since the exit witness bound grows with the
  derivation's ordinal (a bounded slot cannot capture cut-elimination growth).

Kernel proof (`wip/Trap8Probe.lean`, `no_fixed_arg_monotone_unbounded_slot`): `ofNat n < ω` for
every `n`, so monotonicity gives `S (ofNat n) ≤ S ω`, whence `n ≤ S ω` for all `n` — impossible for
the fixed natural `S ω`. (The well-order fact: a monotone `ONote → ℕ` cannot dominate its own values
along a limit's fundamental sequence.) So the conflict between trap-7 (needs growth) and trap-8
(needs monotonicity) is *irreducible at any fixed argument* — it forces the fix in §4 to change the
slot's *reading*, not its *shape*.

## 4. The tension the fix must reconcile (architect-owned — NOT decided here)

- **trap-7 demands DIAGONALIZATION** (branch index rides a large argument) so the `allω` node's
  ℕ-many unbounded branches are dominated. Bare fixed count `f^[norm α + 1]` fails there.
- **trap-8 demands BASE-MONOTONICITY** (`β < α ⟹ slot_β ≤ slot_α` near argument 0) so `weak`/`exI`/
  `cut` sub-derivations lift. The diagonalizing iterate fails there.

A slot form satisfying both is likely one that is **only ever read at arguments ≥ a node-budget**,
where `iterSlot` *is* ordinal-monotone. **This is now a banked theorem** — `iterSlot_le_of_lt`
(src §5b, axiom-clean): for `β < α` (NF) and budget `x ≥ norm β`, `iterSlot f β x ≤ iterSlot f α x`
(mirror of `hardy_le_of_lt`, via `reaches_of_lt` + `iterSlot_le_of_reaches` + `iterSlot_monotone`).
So a node-relative read at argument `≥ norm α` restores the `weak`/`exI`/`cut` lift the bare slot
cannot supply — the crux lemma of the fix is proven; what remains for the architect is the
statement shape that routes every slot-read through such a budget. Candidate directions for the architect (all are C2 statement changes, hence off-limits to a
grind lap):
- **Relativize the whole output slot**, not just `allω` branches: output `rel1 (iterSlot f α) K`
  (or `fun x => iterSlot f α (K + x)`) with `K` a node-budget, so the slot is read at argument
  `≥ K` where reaches-monotonicity applies. Then the exit reads `rel1 (iterSlot f α) K 0 =
  iterSlot f α K`, a large value — check the C3 anti-vacuity corollary still consumes it.
- **E–W Lemma 19 literally**: `N(α) ≤ f^{F^α(0)}(0)` bounds the witness by a plain iterate
  `f^[F^α(0)]` with `F^α(0)` a *number* (fast-growing at 0). A plain `f^[K]` IS monotone in `K`;
  the question is whether `K = F^{α}` can be made monotone in `α` (it has the same base-dip unless
  read at a positive budget). This is the count/collapse normal-form question T-Z5(iii) named.

The reconciliation is exactly the ε₀ girder that T-Z5(iii) flagged as "possibly a different
`collapse` normal form" — resolved at trap-7 for the allω-large-argument regime, re-opened here for
the base-argument regime.

## 5. What this lap banked (real forward progress, committed `c39f08e`)

Both are needed by ANY slot form (monotonicity is form-independent), so they are not wasted:
- `iterSlot_monotone` — the C5 pin, now a real sorry-free proof (mirror of `hardy_monotone`).
- `iterSlot_le_of_reaches` — base-`f` value transfer (mirror of `hardy_le_of_reaches`); this is
  precisely the reaches-monotonicity lever a relativized/positive-budget fix would ride.

## 6. Gate state / what stays frozen

- Build 🟢 1333; headline `peano_not_proves_goodstein` undrifted
  (`[propext, Classical.choice, goodstein_implies_consistency, Quot.sound]`); `blueprint_audit`
  PASSES (15 nodes); `cutElimPass_exit_root` green. Pin 3 body `cutElimPass_Zf` stays the sole src
  §5 `sorry` (the locked statement is UNTOUCHED).
- Frozen surfaces (pins 1–2 / `Zeh` core / `zeh_to_zef` / read-off) untouched. No Route-A, Δ₀,
  `(k,d)` work. No statement change made.

## 7. Recommended next (architect/judge)

Amend C2's output-slot shape (positive-budget / relativized read, per §4) so `iterSlot`'s
reaches-monotonicity is usable at every node, then re-open the pass grind against the amended
statement. Until then pin 3 is architect-gated, not grind-open — the same disposition traps 6/7
received at their catch.
