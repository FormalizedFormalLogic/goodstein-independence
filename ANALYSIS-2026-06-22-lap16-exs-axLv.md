# ANALYSIS (lap 16) — the `exs` case of `embedC_LX` needs Buchholz's value-congruent literal axiom

## TL;DR
The lap-15 HANDOFF called the C₂ structural `embedC` port "mechanical". **Nine of its ten cases are**
(landed this lap as `embedC_LX_gen`, green). **The tenth — `exs` — is not.** Faithfully embedding
Foundation's `Derivation2.exs` (∃-introduction with an *arbitrary term* witness `t`) into our
`XFreeAx`-tracking `Z∞` requires a calculus axiom we do not have: **Buchholz's value-congruent
literal axiom** `{Xs, ¬Xt}` for `sᴺ = tᴺ` (lecture notes p.27, `AX(Z∞)`). Our `Deriv.axL` is the
*same-atom* pair `{Xs, ¬Xs}` only. This is a genuine wall, not plumbing.

## Why `exs` needs it (the precise obstruction)
`embedC`'s `exs` case (over `ℒₒᵣ`, `src/Embedding.lean:605`) collapses the closed witness `asg e ▹ t`
(value `m`) to the numeral `nm m` so the numeral-only `Deriv.exI` can fire. The collapse is a `cut`
on `((asg e).q ▹ φ)/[asg e t]` against a **value-congruent excluded middle**
`provable_em_cong (nm m) (asg e t)` proving `⊢ φ/[nm m], ∼(φ/[asg e t])`. Over `ℒₒᵣ` that EM closes
its atoms via `axTrue` (decidable literal truth) — fine, all atoms `ℒₒᵣ`, X-free.

Over `LX` the body `φ` may contain an **X-atom on the bound variable** (`∼X(#0)` etc. — and it does:
proving `TI = Prog → ∀x Xx` manipulates `∼Prog = ∃x(hyp(x) ∧ ¬X(x))`, an existential whose body
carries `¬X(x)`). The collapse then needs `⊢ X(nm m), ¬X(asg e t)` with `|nm m| = |asg e t| = m`.
This is **not** derivable in our calculus `XFreeAx`-safely:
- `axL` needs the *same* atom (`nm m ≠ asg e t` syntactically) — does not apply.
- `axTrue` on an X-literal breaks `XFreeAx` (Boundedness is false for lone X-`axTrue` leaves).
So the value-congruent X-pair is genuinely missing.

## Ground truth (Buchholz lecture notes §5, pp.26–30) — verified by reading the PDF
- **`AX(Z∞)` (p.27).** A sequent `Δ` is an axiom iff all its elements are closed literals **and**
  (`Δ ∩ TRUE₀ ≠ ∅`  **or**  `{Xs, ¬Xt} ⊆ Δ` with `sᴺ = tᴺ`). Here `TRUE₀` = true closed **ℒ₀**
  (X-free) literals. So Buchholz's axiom set is exactly: *X-free true literals* + *value-congruent
  X-pairs*. Lone true X-literals are **not** axioms — matching our `XFreeAx` intent precisely.
- **Cut closure of `AX(Z∞)` (Remark, p.27).** `Δ', Δ'' ∈ AX(Z∞) ⟹ (Δ'\{C}) ∪ (Δ''\{¬C}) ∈ AX(Z∞)`.
  Proof: the only failure would need `C = Xt`, `¬Xs ∈ Δ'\{C}`, `Xr ∈ Δ''\{¬C}` with `sᴺ=tᴺ=rᴺ` — but
  then `{Xr, ¬Xs}` is a value-congruent pair, so the union is still an axiom. This is the literal-cut
  case of cut-elimination (5.1, case 2.1) — our `atomCut` must replicate it.
- **Boundedness case 1.2 (p.29).** `last(d) = Ax_Δ` with `{Xt, ¬Xs} ⊆ Δ`: then `Xt ∈ Γ`, `¬Xs ∈ Λ`,
  and `|t|≺ = |s|≺ ≤ α < α+2^β`, giving `⊨^{α+2^β} Γ`. The value-congruent X-pair case is already in
  Buchholz's Boundedness proof — our same-atom case 1.2 is the special case `s = t`.

## The faithful fix (next lap — the C₂ crux)
**Generalise the literal axiom to value-congruent pairs.** Either generalise `Deriv.axL` to
`axL (r) (v v') (hval : ∀ i, (v i)ᴺ = (v' i)ᴺ) (hp : rel r v ∈ Γ) (hn : nrel r v' ∈ Γ)` (sound: in the
ℕ-model `rel r v ↔ rel r v'` when the value-vectors agree, for *every* relation incl. X), or add a
parallel `axLv` constructor. Generic over `L` — no `Xsym` dependency, so it lives in `ZinftyGen`.

Retrofit surface (each is a `cases`/`induction` on `Deriv`, ~leaf branch mirrors the `axL` branch):
1. **`ZinftyGen`** — `o`/`cr` (leaf `0`); `Provable.axLv` builder; inversion leaf branches
   (`orInvAux`/`andInvAux`/`allInvAux`); the literal-cut content in `removeFalseLitAux`/`atomCutAux`
   (Buchholz Remark p.27 — the genuine new math); `removeFalsumAux`/`cutElimStepAux` leaf branches.
2. **`XFreeCutElim`** — `XFreeAx` (value-congruent pair is X-free-safe: it is NOT an `axTrue`, so
   `XFreeAx` holds for it automatically); the `*_x` inversion leaf branches; thread through `cutElim`.
3. **`Boundedness`** — `XFreeAx` def leaf; the main induction's **case 1.2** generalised to the
   value-congruent X-pair (Buchholz p.29 — genuine new content, but short).
4. Then `provable_em_cong_gen_x` (value-congruent EM over `LX`, X-atoms via `axLv`, X-free atoms via
   `axTrue`, all `XFreeAx`-safe) ⟹ `PXFc.exI_closed` ⟹ the `exs` case ⟹ `embedC_LX_gen` sorry-free.

**Risk note.** This touches the flagship `PXFc.cutElim` (C₁) and `boundedness` (A), both currently
axiom-clean. It is a big-bang change (a new/changed `Deriv` constructor makes every match non-exhaustive
until all branches are added), so there is no intermediate green — best done at the *head* of a fresh
lap with full budget, grinding to a single green checkpoint. The same-atom `axL` argument that the
lap-15 C₁ relied on (X-atomic cut closes by set idempotence) generalises to the value-congruent
Remark; the truth-surgery branch stays vacuous under `XFreeAx` (still no X-`axTrue`).

## Retrofit recon (lap-16 probe — done, then reverted as uncommittable mid-big-bang)
Added the `axLv` constructor + `o`/`cr` cases + `Provable.axLv` builder, then chased the
non-exhaustive-match breaks. Findings (the map for executing this next lap):
- **8 induction sites in `ZinftyGen`** need an `axLv` branch. **5 are purely mechanical** (mirror the
  `axL` branch with `v'` on the negative literal): the three inversions `orInvAux`/`allInvAux`/
  `andInvAux`, the `removeFalsum`-union site (`atomCutAux` companion), and `cutElimStepAux`. (These
  five were written and compiled fine in the probe.)
- **`removeFalseLitAux`** (generic) needs the **full 3-case** axLv branch: if the removed false literal
  `Lit = rel r v`, close the erase by `axTrue false r v'` (true since `rel r v ↔ rel r v'` by value-cong
  + `Lit` false); symmetric if `Lit = nrel r v'`; else both survive → re-emit `axLv`. Needs a helper
  `litTrue_rel_congr : (∀ i, valm (v i) = valm (v' i)) → (LitTrue (rel r v) ↔ LitTrue (rel r v'))`.
- **`atomCutAux`** is the genuine new math = **Buchholz Remark p.27**: cutting two literal axioms
  yields a literal axiom. With `axLv` the cut of `{X r₁, ¬X v}` against `{X v', ¬X r₂}` (cut atom value
  `m`) produces `{X r₁, ¬X r₂}`, still value-congruent (`|r₁|=|r₂|=m`). This is the only hard
  ZinftyGen spot.
- **CRITICAL XFreeAx interaction (the saving grace).** In `XFreeCutElim`'s `_x` (XFreeAx-preserving)
  versions, `removeFalseLit` is **restricted to X-free removed atoms `r₀`** (lap-15 design). An `axLv`
  X-pair has relation `Xsym ≠ r₀`, so `Lit` (X-free) equals **neither** of the pair's literals ⟹ the
  axLv branch hits **only the re-emit case**, never an `axTrue` truth branch. So `axLv` does **not**
  reintroduce a lone X-`axTrue`, and `XFreeAx` is preserved — the lap-15 vacuity argument survives the
  generalisation. (`XFreeAx` itself treats `axLv` as X-free-safe automatically: it is not an `axTrue`.)
- **`Boundedness`**: `XFreeAx` def gets a trivial `axLv` leaf; the main induction gets **case 1.2
  generalised** to the value-congruent X-pair (Buchholz p.29, short: `|t|≺ = |s|≺ ≤ α`).
- The big-bang has **no intermediate green** (every match is non-exhaustive until all branches land
  across all 3 files + the `exs` discharge), so it must be driven to a single green checkpoint in one
  lap. The five mechanical ZinftyGen branches + the helper + the recon above de-risk it substantially.

## What landed this lap (green, committed)
- `provable_true_x` — ω-completeness for true **closed X-free** formulas, `XFreeAx`-safe (the X-free
  `axm` engine). Atoms close via `PXFc.axTrue` with the `XFreeForm` witness.
- `XFreeForm` + simp/rewriting-invariance lemmas (structural X-freeness predicate).
- `embedC_LX_gen` — the `axm`-abstracted structural embedding: `closed` (via `provable_em_x`) +
  all 8 structural cases, `XFreeAx`-safe. `exs` is the one disclosed `sorry` (this wall); `axm` is
  the hypothesis `hax` (discharged later by `provable_true_x` + `metaInduction`).
