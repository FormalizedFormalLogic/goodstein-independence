# HANDOFF — 2026-06-22 (lap 8)

> **NEXT LAP FIRST ACTION:** read this + `STATUS.md` + `ANALYSIS-2026-06-22-cutelim-k-threading.md`
> **ADDENDUM 5** (the validated lap-8 design) + `PENDING_WORK.md` (A/B lap-8 update at top). Build is
> **green** (`lake build GoodsteinPA`, 1257 jobs). Forward file: **`wip/OperatorZinfty.lean`** (the
> control-ordinal operator calculus `Zekd`, sorry-free through §19.5; `lake env lean
> wip/OperatorZinfty.lean`). Headline `peano_not_proves_goodstein` still a literal `sorry` (designated
> open target — anti-fraud, correct). **Next: §19.6 `cutReduceAll` on `Zekd`** — the ONE remaining
> step-1 girder; all its infra (Hardy lemmas + `mono_e` + ordinal/norm helpers) is now banked.

## What landed this lap (11 commits, all verified green/axiom-clean)

This lap RESOLVED the Hardy-infrastructure layer of the §19.6 crux and BUILT the operator calculus
through §19.5 — turning the lap-7 "needs the operator, design open" state into "operator implemented
through §19.5, design validated, only `cutReduceAll` remains."

1. **`hardy_add_comp` / `hardy_add_collapse`** (`src/Hardy.lean`, axiom-clean) — the general
   non-absorbing Hardy additive composition law `H_{γ+δ}(x) = H_γ(H_δ(x))` (δ below γ's least
   exponent), generalizing `hardy_oadd_tail` to a full left summand. The cut-elim **control collapse**.
   Helpers: `lastExp`, `addAux_concat`, `lastExp_repr_lt`, `nfBelow_concat`, `lead`, `lead_NF`,
   `repr_lt_omega_opow_succ`.
2. **`hardy_comp_lt_goodsteinLength`** (`src/LowerBound.lean`, axiom-clean mod the documented Goodstein
   `native_decide` base-cases) — the **wrong-order** composition domination `H_α(H_e(m)) < G(m)`
   eventually, for ANY NF `α, e`. The lower-bound-side companion: a nested control index is still
   Goodstein-dominated (dominate by `ω^Q·2`, `Q = osucc(lead α + lead e)`, via index-monotonicity +
   the coefficient law `hardy_oadd_coeff`, then `hardy_lt_goodsteinLength`).
3. **`wip/OperatorZinfty.lean` — the control-ordinal operator calculus `Zekd α e k d c Γ`**, sorry-free
   through §19.5:
   - inductive (witness bound `hardy e (k+d)`, **decoupled from the derivation ordinal `α`**);
   - `mono_k` / `mono_d` / `mono_c` / **`mono_e`** (NEW — control-axis monotonicity, via the banked
     `hardy_le_of_lt`, budget side condition `norm e ≤ k+d`); `weakening`;
   - full inversion suite `orInv` / `andInvL` / `andInvR` / `allInv` (ported, `e` inert);
   - §19.5 `cutReduceConj` / `cutReduceDisj` + all §19.6/19.7 ordinal/norm helpers (`lt_osucc`,
     `osucc_lt_osucc`, `add_lt_add_left_NF`, `le_add_left_NF`, `add_osucc_descent`, `norm_omegaPow`,
     `norm_addAux_le`, `norm_add_le`).
4. **Design validated — ADDENDUM 5.** The single control ordinal `e` (numeric Buchholz form, NOT the
   set-valued `H`) closes the ADDENDUM-4 witness-index obstruction:
   - **commuting cases keep `e` inert** (no Hardy-super-linear index forced through `max k n`);
   - **`e` rises only at the top cut** via `mono_e` (combine ∀-side control `e₁`, ∃-side `e₂` → common
     `e > e₁,e₂`); the witnesses then sit under `hardy e`;
   - **lower bound survives** via `hardy_comp_lt_goodsteinLength` (nested control index dominated).
   So the full set-valued `H` is NOT needed for PA/ε₀. The `ON-LINE-REQUEST` is narrowed accordingly.

5. **NF-ified the `Zekd` leaf rules** (`trueRel`/`trueNrel` carry `hαNF` now) — the §19.6 leaf-case
   prerequisite (`norm_add_le` is NF-essential). Threaded through `mono_k/d/c/e` + inversions.
6. **Built the `ZekdProv` wrapper foundation** — `ZekdProv α e k d c Γ := ∃ α', α'≤α ∧ α'.NF ∧ Zekd α'…`
   (bound-as-upper-bound + NF, so ordinal-raises like `wk`'s `γ↦osucc(α+γ)` have NF and `≤`-slack).
   Lemmas: `mono` (α≤,k,d,c), `mono_e`, `weakening`, `cast`, `of`. This is the surface `cutReduceAll`
   is stated over (see ADDENDUM 5 cont.).

## THE NEXT MOVE — §19.6 `cutReduceAll` on `Zekd` (over `ZekdProv`)

**Foundation is DONE** (leaves NF-ified; `ZekdProv` wrapper built). Remaining for §19.6:
- **(a) `ZekdProv` rule lifts** — `axL`/`verumR` (at bound `0`, trivial), then `andI`/`orI`/`allω`/`exI`/
  `cut` at the `ZekdProv` level with the norm side conditions (mirror `Zinfty.lean` `Provable.andI` etc.,
  add the `norm β < k+d` carries). These are what the commuting cases of `cutReduceAllAux` reassemble with.
- **(b) `cutReduceAllAux`** — port `Zinfty.lean:785` over `ZekdProv`; details below.

Port `src/Zinfty.lean:785 cutReduceAllAux` (the lap-3 unbounded ∀/∃ reduction, fully proved) to `Zekd`,
adding the bounded `(α, e, k, d)` bookkeeping:
- **Structure (unchanged from lap 3):** invert ∀-side once (`allInv` → `fam : ∀n, Zekd α e k d c
  (insert (φ/[nm n]) Γ)`), then induct on the ∃-side `Zekd γ e k d c Δ` with `(∃⁰∼φ)∈Δ`. Principal
  `exI` case = cut `fam n` at the witness; commuting cases reapply the rule over `Δ.erase(∃∼φ)∪Γ`.
- **Bounds:** conclusion ordinal `osucc(α+γ)` (`add_osucc_descent` banked); `k` unchanged; `d ↦ d +
  norm α` (norm-budget `d`-bump, via `norm_add_le`); `e` raised to a common control at the **top-level**
  `cutReduceAll` (combining ∀/∃ sides) via `mono_e`.
- **⚠️ FIRST — the NF-threading subtlety (surfaced lap 8, see ADDENDUM 5):** the `Zekd` leaf rules
  (`axL`/`verumR`/`trueRel`/`trueNrel`) carry NO `hαNF` on the node ordinal, but the leaf cases of
  `cutReduceAll` need `norm(α+γ) ≤ norm α + norm γ` (`norm_add_le`, **NF-essential** — NF-free is
  machine-checked FALSE). **Fix (recommended, option (b)): NF-ify the `Zekd` leaf rules** — add `hαNF :
  α.NF` to `trueRel`/`trueNrel` (the only leaves with a norm condition; `axL`/`verumR` need no ordinal
  constraint so can be issued at `osucc(α+γ)` directly). Then re-thread `hαNF` through the
  `trueRel`/`trueNrel` cases of `mono_k/d/c/e` + the 4 inversions (~12 mechanical spots). Matches Towsner
  (every `Z_∞` node is `<ε₀` ⟹ NF).
- **Budget arithmetic tip:** for a leaf at node ordinal `γ` (norm `γ < k+d`), issue the atom at `γ` then
  `weak` up to `osucc(α+γ)` — avoids the `osucc`-`+1`-vs-strict-`<` boundary that bites if you issue
  directly at `osucc(α+γ)` (norm could hit the budget exactly).
- Then §19.7 `cutElimStep` (`ω^α`, `norm_omegaPow` banked) + §19.9 `cutElim`.
- Lower bound for the operator calculus: bridge a cut-free `{gAll}` derivation to `B` (M6), with the
  nested control index handled by `hardy_comp_lt_goodsteinLength`. Then subformula bridge ⟹ headline.

## State of the spine (Route B, hardest-first)
- **M1, M2, Phase 0/1** — done, clean.
- **M5 (unbounded `(α,c)` cut-elim, `src/Zinfty.lean`)** — done, clean. Template for `cutReduceAll`.
- **M6 (Hardy lower bound, `src/LowerBound.lean`)** — done, clean (`∀k`); + lap-8 `hardy_comp_lt_…`.
- **Step 1 (`Zekd` cut-elim, `wip/OperatorZinfty.lean`)** — calculus + §19.2–19.5 + `mono_e` + all
  §19.6 helpers DONE. **§19.6 `cutReduceAll` = the live crux** (port + bounded bookkeeping + leaf-NF).
  Then §19.7 `cutElimStep` + §19.9 `cutElim`.
- **Step 2 (M4 embedding)** — independent of §19.6; recon done lap 6. Parallel thread if §19.6 stalls.
- **Step 4 (subformula bridge), M7a (language gap), M7b (assembly)** — downstream.

## Notes
- **`SplitZinfty.lean`** is the `(k,d)`-only stepping stone (§19.2–19.5); **`OperatorZinfty.lean`** is
  its control-ordinal successor (adds `e` + `mono_e`) and the forward file. `BoundedZinfty.lean` is the
  oldest single-index reference.
- **Aristotle:** left idle — the §19.6 work needs the real `Zekd` defs + Hardy machinery (not cleanly
  self-containable). The Hardy infra it might have helped with is now proved locally.
- **`WebFetch` dead in box; `WebSearch` works.** `ON-LINE-REQUEST` narrowed (Hardy/operator layer solved
  offline; only the optional leaf-NF literature confirmation remains).
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`. Headline `sorry` intact.

## File map (changes this lap)
- `src/GoodsteinPA/Hardy.lean` — `hardy_add_comp`/`hardy_add_collapse` + helpers (`lastExp`, `lead`,
  `addAux_concat`, `repr_lt_omega_opow_succ`, …). Build green, axiom-clean.
- `src/GoodsteinPA/LowerBound.lean` — `hardy_comp_lt_goodsteinLength`. Build green, axiom-clean.
- `wip/OperatorZinfty.lean` — **NEW**: `Zekd` calculus + structural layer + inversions + §19.5. Sorry-free.
- `ANALYSIS-2026-06-22-cutelim-k-threading.md` — **ADDENDUM 5** (design validation + leaf-NF subtlety).
- `STATUS.md`, `PENDING_WORK.md`, `ON-LINE-REQUEST.md` — lap-8 updates.
- removed `wip/HardyAdd.lean` (dev scratch, fully banked into `src/`).
