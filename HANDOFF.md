# HANDOFF — 2026-06-22 (lap 16)

> **Branch** `plan` · build **green** (`lake build GoodsteinPA`, 1266 jobs) · headline
> `peano_not_proves_goodstein` = honest `sorry` (anti-fraud guard intact, untouched).
> **Lap 16 landed the C₂ structural embedding `embedC_LX_gen` (9/10 cases) + `provable_true_x`, and
> precisely MAPPED the one hard remaining case (`exs`) to a calculus retrofit the lap-15 HANDOFF had
> mis-scoped as "mechanical".** New file `src/GoodsteinPA/EmbeddingX.lean` (green, one disclosed sorry).

## ✅ Lap-16 deliverables (`src/GoodsteinPA/EmbeddingX.lean`, axiom-clean modulo the one disclosed sorry)
- **`XFreeForm`** — structural "every relation symbol is `ℒₒᵣ` (`Sum.isLeft`)" predicate over `LX`,
  with simp lemmas + rewriting-invariance (`xfreeForm_rew`).
- **`provable_true_x`** — ω-completeness for TRUE **closed X-free** formulas, `XFreeAx`-safe (atoms via
  `PXFc.axTrue` + the `XFreeForm` witness). The X-free `axm` engine.
- **`embedC_LX_gen`** — the `axm`-abstracted structural embedding
  `(hax) → Derivation2 𝓢 Γ → ∃ c, ∀ e, ∃ α, PXFc α c (Γ.image (asgX e ▹))`. Ports `Embedding.embedC`
  rule-by-rule to `LX`/`PXFc`: `closed` (via `provable_em_x`, `axL`-only) + all 8 structural cases
  (`verum/and/or/all/wk/shift/cut` + `axm`-as-hypothesis), every builder `XFreeAx`-safe. **`exs` is the
  one disclosed `sorry`** — the genuine wall (below).

## 🧱 THE WALL lap-15 mis-scoped — `exs` needs Buchholz's value-congruent literal axiom
Read `ANALYSIS-2026-06-22-lap16-exs-axLv.md` (full detail, grounded in the Buchholz lecture notes
§5 pp.26–30, **read this lap**). Summary:
- `embedC`'s `exs` collapses the closed witness `asgX e t` to a numeral via a **value-congruent EM**.
  For an **X-atom body** (and `∼TI`'s `∃x(hyp(x) ∧ ¬X(x))` HAS one) that collapse needs
  `⊢ X(nm m), ¬X(asgX e t)` with `|nm m|=|asgX e t|=m` — Buchholz's **value-congruent X-pair axiom**
  `{Xs,¬Xt}` (`sᴺ=tᴺ`, `AX(Z∞)`, p.27). Our `Deriv.axL` is **same-atom** `{Xs,¬Xs}` only; the pair is
  NOT `XFreeAx`-derivable (axL needs identical atoms; axTrue on X breaks `XFreeAx`).
- **Fix = generalise the literal axiom to value-congruent pairs** (new `Deriv.axLv (r) (v v') (hval) …`,
  generic over `L`, sound). Boundedness case 1.2 (p.29) and cut-elim's literal-cut case (Remark p.27)
  **already handle value-congruent pairs in Buchholz** — our same-atom versions are the special case.

## 🎯 Critical path to the headline (★ = real walls)
| Step | What | Status |
|---|---|---|
| **A** Boundedness Thm 5.4 | crux | ✅ DONE lap 14 |
| **B** Corollary `‖≺‖≤2^β` | invert TI + Boundedness | ✅ DONE lap 14 |
| **C₁** `XFreeAx` cutElim → cr=0 | the big §19 port | ✅ DONE lap 15 |
| **D** Thm 5.6 tail | C₁ ∘ B | ✅ DONE lap 15 (`orderType_le_of_TIprovable`) |
| **C₂-crux** X-induction meta-induction + LX-EM | faithfulness-critical | ✅ DONE lap 15 (`metaInduction`, `provable_em_x`) |
| **C₂-struct** `embedC_LX_gen` structural port | 9/10 cases | ✅ **DONE lap 16** (`exs` = the wall below) |
| **C₂-axLv ★** value-congruent literal axiom | the `exs` wall — a calculus retrofit | **NEXT** (recon done, see ANALYSIS) |
| **C₂-axm** discharge `hax` for `paLX` | X-free via `provable_true_x` + X-ind via `metaInduction` glue | not started |
| **E** Goodstein⟹TI_≺(X) bridge | Kirby–Paris; reuse Phase-0 CNF-ε₀ | not started |
| **F ★** Arithmetization seam | ℒₒᵣ-def ε₀ order, `‖≺‖=ε₀`, discharge `hprec`/`hprecXPos` | not started — 2nd hard wall |
| **G** Final assembly | chain + `#print axioms` clean | not started |

## NEXT (lap 17): execute the `axLv` retrofit — a single-lap big-bang to ONE green checkpoint
**Do this at the HEAD of a fresh lap** (it has no intermediate green — a new `Deriv` constructor makes
every match non-exhaustive until ALL branches land across 3 files + the `exs` discharge). The recon in
`ANALYSIS-2026-06-22-lap16-exs-axLv.md` de-risks it: 5 of the 8 `ZinftyGen` sites are mechanical
(mirror the `axL` branch with `v'` on the negative literal — these compiled in the lap-16 probe), and
the XFreeAx interaction is benign (`removeFalseLit_x` is X-free-restricted, so `axLv` X-pairs only hit
its re-emit case — no lone X-`axTrue`). Steps:
1. `ZinftyGen`: add `Deriv.axLv` + `o`/`cr` cases + `Provable.axLv` builder + a helper
   `litTrue_rel_congr`; the 5 mechanical inversion/`cutElimStep` branches; the **3-case
   `removeFalseLitAux`** branch; the **`atomCutAux`** value-congruent literal-cut (Buchholz Remark p.27
   — the one hard ZinftyGen spot).
2. `XFreeCutElim`: `axLv` leaf branches in the 8 `_x` inductions (mostly re-emit per the saving grace);
   confirm `cutElim` stays green + `#print axioms` clean.
3. `Boundedness`: `XFreeAx` def `axLv` leaf (X-free-safe = `True`); main induction **case 1.2**
   generalised to value-congruent X-pair (Buchholz p.29, short).
4. `EmbeddingX`: `litTrue_subst_congr` + `provable_em_cong_gen_x` (value-cong EM over `LX`: X-atoms via
   `axLv`, X-free atoms via `axTrue`, all `XFreeAx`-safe) ⟹ `PXFc.exI_closed` ⟹ discharge the `exs`
   `sorry`. `embedC_LX_gen` is then sorry-free.

## Then (after C₂-struct is sorry-free): C₂-axm + the statement `embedC_LX`
- Define `paLX : Theory LX := Theory.lMap (Language.ORing.embedding LX) 𝗣𝗔⁻ + InductionScheme LX Set.univ`
  (this RESOLVES "what is `Z ⊢ TI(X)`": `Derivation2 (↑paLX) {TI prec}`; `InductionScheme L` IS generic
  over an ORing `L` — confirmed). Then `embedC_LX := embedC_LX_gen` with `𝓢 := ↑paLX` once `hax` is
  proven: **X-free axioms** (`lMap`-image of `𝗣𝗔⁻` + X-free induction instances) via `provable_true_x`
  (need lMap⟹X-free + true-in-ℕ lemmas); **X-induction instances** via `metaInduction` (the Foundation-
  DSL glue: build `step` from `ψ` by the successor substitution, prove `hstep`, strip `univCl`+the two
  `🡒`). Deliverable `embedC_LX : (↑paLX ⊢₂ {TI prec}) → ∃ c α, PXFc α c {TI prec}` ⟹ **D fires** ⟹ Thm 5.6.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry`.
- **Aristotle:** idle. The cleanly-feedable open lemmas all need either the `axLv` retrofit (exs) or
  large `LX`/`PXFc` context (metaInduction glue), so it stayed correctly idle this lap.
- **Banked off-path (do NOT resume):** witness-bounded `wip/` calculi; `Zᵏ`/M6.
- Build: `lake build GoodsteinPA` (1266). Axiom ledger in `STATUS.md`.
