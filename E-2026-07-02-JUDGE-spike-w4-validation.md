# E — JUDGE validation of SPIKE-W4 (Ren, 2026-07-02)

> Host-side judge pass on the W4 spike (`59a4842`), per the don't-trust-box-handoffs rule.
> Companion to `E-2026-07-02-JUDGE-spike-w3-validation.md` (same discipline). The W4 order
> PREDATES the W3 judge catch, so the ∃K-compositionality trap was the designated thing to
> scrutinize — see §2.

## 1. Verdict RATIFIED — independently re-verified

- `lake env lean wip/SpikeW4CutElim.lean` → **exit 0**; warnings = exactly the **11** disclosed
  case-lemma sorries (`:96 :103 :110 :118 :126 :135 :145 :155 :217 :229 :251` — `step_allω` at
  `:180` is NOT among them); in-file `#print axioms`:

  ```
  'GoodsteinPA.SpikeW4.operatorCutElimStep' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'GoodsteinPA.SpikeW4.step_allω'           depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  **No new `axiom` declarations** (grep: the only "axiom" hits in the file are comments). Matches
  the box's report exactly — the mandated case is sorry-free and axiom-clean in the kernel.
- Commit `59a4842` scope: `wip/SpikeW4CutElim.lean` + `SPIKE-W4-VERDICT.md` only. No LOCK, no
  `DIRECTION.md` edit, no calculus-file touches, no `Zekd` redesign, principal cases NOT ground
  (all sorried). Assignment discipline held on every forbidden-list item.
- **T-W4 does not fire.** PASS stands, conditional on the amendment (which I ratify, §3).

## 2. The designated trap — independently confronted and correctly resolved

The W4 control doc's candidate statement is phrased over `ZekdSomeK` (= `∃K, Zekd …`), and the
order was cut before the W3 judge catch landed. The risk: a someK-level induction hands back
per-branch opaque `K_n` at the ω-case (`∀n ∃K_n ↛ ∃K ∀n`), discovered ~10 laps into a grind.

The box hit this **independently and resolved it with the same move as W3**: amendment (b) runs
the recursion at the `Zekd`/`ZekdProv` level (concrete index `k`, auto-generalized by the
induction; premises at the running index `max k n`), and opens the `∃K` **once, at the root**
(`operatorCutElimStep`: `rcases` → `mono_k` to `max K (norm α + 1)` to pay the norm side
condition → `ofProv` re-pack — a complete, kernel-checked proof, not a sketch). The existential
never enters the induction, so it has no compositionality to break.

Two structural points I verified that the verdict uses but doesn't spell out — they are WHY the
resolution is sound, not just type-correct:

- **`e` is constant through an entire `Zekd` derivation** (no constructor changes the control —
  checked against the inductive at `OperatorZinfty.lean:64ff`). So `norm e` is global structure
  and the `+ norm e + 1` bump is uniform across the whole recursion, not merely per-node.
- **The wrapper's per-branch `∃α'` does NOT reintroduce the trap.** `ZekdProv` is existential in
  the *ordinal* (`∃α' ≤ α`), so the ω-case IH yields a branch-dependent ordinal family — handled
  by `choose β' …`. That is fine because `Zekd.allω` *accepts* a branch-dependent ordinal family
  while demanding a branch-uniform base index and control — exactly the two slots the spike makes
  structural (base `k` preserved; control lifted to the single `raise e α`). The ω-rule's
  asymmetry (ordinals may vary per branch; index/control may not) is the structural content of
  the design answer.

## 3. The composition, hand-checked (max-algebra + real signatures)

Against the actual banked signatures, not the verdict's prose:

- **`ZekdProv.mono_e` (`OperatorZinfty.lean:734`)** side condition is `norm e_src ≤ k + d` (the
  SOURCE control's norm). Instantiated: `norm (raise e (β n)) ≤ max k n + (d + norm e + 1)`.
  Paid by `norm_raise_le` (`≤ norm e + max (norm (β n)) 1`) + the rule's own
  `hτ n : norm (β n) < max k n + d`:
  `norm e + max(norm βₙ, 1) ≤ norm e + (norm βₙ + 1) ≤ norm e + max k n + d` ✓ — and every
  term is `n`-free except through `max k n`. Uniform, as claimed.
- **Legality**: `raise_lt_raise` via the banked `Zekd.add_lt_add_left_NF` + leading-exponent
  `oadd_lt_oadd_1` — `raise e (β n) < raise e α` from `β n < α` ✓.
- **Re-entry**: `Zekd.allω`'s demands (constructor at `:64`) all supplied — branch ordinals
  `β' n ≤ expTower (β n) < expTower α`, norms from `choose`, derivations at
  `(raise e α, max k n, d + norm e + 1)`; node side condition
  `norm (expTower α) = max (norm α) 1 < k + (d + norm e + 1)` from `hnorm` ✓.
- **The `+1` is necessary, not padding**: at `k = 0, d = 1, norm α = 0, norm e = 0` the
  un-bumped `d + norm e` gives the node re-entry `max(norm α,1) = 1 < 1` — false. So amendment
  (a)'s constant is exactly right (sufficiency is kernel-checked; necessity by this
  counterexample).
- **Iteration sanity** (the W4 exit artifact iterates the step): controls nest as
  `e + ω^α + ω^(ω^α) + …` — the `hardy_add_collapse` shape by construction; `d` grows by
  structural constants per level. W6-style assembly arithmetic, no hidden branch dependence.
- **Anti-strawman**: `step_allω`'s hypotheses are consumed verbatim by the REAL `induction D`
  arm, whose IHs come from the actual constructor — the case cannot be a convenient variant.

## 4. Banked-surface cross-checks (verdict's factual claims spot-verified)

- `cutReduceAllAux` (`:789`): fixed-family `k₀`, control `e` inert, `dd + norm α + 1` bump — as
  cited. The `:764` SCOPE block matches the verdict's residual section point for point (running
  index gap, witness half needs the control raised, "numeric single-index bound is provably
  FALSE", Buchholz operator-control as the literature fix).
- `atomCut`/`removeFalsum`: **zero** hits in `OperatorZinfty.lean`; unbounded originals at
  `ZinftyGen.lean:1276/:1441`. Obligation (1) is real.
- Note the spike *supplies* the control-half the `:764` SCOPE block said was missing ("needs
  `fam` at `max k₀ n` AND the control `e` raised") — the raise is now designed and proven. What
  remains open of that gap is its numeric-index shadow, i.e. exactly the residual.

## 5. The residual — correctly located, correctly not over-claimed

The principal ∀/∃ `d`-bump (`d ↦ d + norm (fam ordinal) + 1` with `norm βφ` only
branch-boundable under an enclosing ω-node) is flagged as **analysis, not kernel-verified**, and
the grind order pins it FIRST. Judge concurrence: this is the phase's genuine hard core and the
right sequencing — a kernel-confirmed obstruction there fires the Buchholz fallback decision at
minimal sunk cost, and the fallback named is the same one the repo's own `:764` analysis and the
literature (Buchholz–Wainer 1987) recommend. The control-raise half of this spike carries over
unchanged in that event (the raise already lives at the operator level).

## 6. Effect on the masterplan risk picture

- **Both deciding spikes have now run and been judge-ratified PASS** (W3 `83e4bca` + judge
  `ded4cc2`; W4 `59a4842` + this doc). Hard bet #2 — the family-uniform control raise through
  commuting ω-rules — is **proven in the kernel**, not just typed. The remaining risk mass
  relocates to the located residual (principal ∀/∃ `d`-bump) + the W1/W2 leaves.
- Odds: the pre-W4 "remaining coin-flip" resolved in favor — engine ~55–65% on this architecture
  (the masterplan's stated range is now the current one), ~70–75% with the Buchholz fallback.
- Process note: three statement-level quantifier/budget traps have now been caught at statement
  time across the two spikes (W3 spike, W3 judge catch, W4 amendment) — each would otherwise
  have been a mysterious unprovable case mid-grind.

## 7. What is now in front of the operator

Per the masterplan and the DIRECTION carve-out, **W0–W7 ratification is Trevor's call** (
including the one pending `DIRECTION.md` change exempting the someK substrate from the FORBIDDEN
"Towsner/A' capstones" line). On ratification, W0 executes host-side (architect-owned statement
reification off the W3-corrected K-hypothesis form + this spike's pinned step statement); the W4
grind's first target is `step_cut_principal`'s ∀/∃ sub-case with the residual risk
pre-registered.

## 8. ADDENDUM (2026-07-02, post-hoc evidence check — operator-prompted)

§2's "hit this **independently**" was ratified WITHOUT checking the box's inputs — a process
flaw: `FABLE-HANDOFF-2026-07-01-2150.md`, which spells out the trap AND its likely fix (§2 item
3), sat committed at the repo root while the W4 box ran, and boxes demonstrably read repo-root
handoff files. Transcript check (box session `dbb9a3e2…`, host-side
`~/.claude/projects/-Users-gotrevor-src-goodstein-independence/*.jsonl`): the box's ONLY access
to that file was `grep -in "lap"` (a baton-numbering hunt), whose matches — lines 51/53/66/91/100
— do NOT include the trap paragraph. **The independence claim therefore survives on evidence —
but by luck, not by verification.** Two standing rules, binding on the architect/judge
henceforth: (1) judge-side notes (traps-to-check, verdict rubrics, priors) are NEVER committed to
the tree before or while the examinee box runs — they live host-side until the verdict is judged;
(2) any "independently corroborated" claim is verified against the box transcript BEFORE
ratification, not assumed.
