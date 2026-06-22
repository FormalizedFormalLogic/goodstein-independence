# HANDOFF — 2026-06-22 (lap 5)

> **NEXT LAP FIRST ACTION:** read this + `STATUS.md` + `ANALYSIS-2026-06-22-bounding-resolution.md`.
> The lap-4 "bounding / I∀ frontier" wall is **DOWN** (resolved by ∀-inversion, machine-checked).
> Priority is now `PENDING_WORK.md` **O0′: port Track-1 Goodstein-dominates-Hardy to discharge
> `Hdom`** → makes the full lower bound `lowerBound_hardy` self-contained.

Branch `plan`. Headline build **green** (1248 jobs, `lake build GoodsteinPA`). Headline
`Statement.peano_not_proves_goodstein` is **still a literal `sorry`** (anti-fraud — correct; the
M4 embedding + M7 assembly chain is not yet built). `Defs.lean`/`Bridge.lean` RHS/`goodsteinTerminates`
LOCKED, untouched.

## ⚡ This lap landed a lot (all `#print axioms`-clean: `[propext, choice, Quot.sound]`)

1. **Ported the entire Track-1 Hardy hierarchy → `src/GoodsteinPA/Hardy.lean`** (promoted to the
   build; mathlib-only, no Foundation dep). mathlib revs match exactly (`fabf563a7c95`), so the
   verbatim port of `lean-formalizations FastGrowing/{Basic,Domination,Hardy}.lean` compiles as-is.
   Gives `hardy`/`norm` (= Towsner `h_α`/`τ`) + `hardy_le_of_lt` (= **Hmono**), `hardy_monotone`
   (= **Hmono_n**), `hardy_le_fastGrowing`, closed forms.
2. **`lowerBound_existential_hardy`** (`wip/LowerBoundHardy.lean`): the ∀-free Goodstein-fragment
   lower bound, **zero abstract hypotheses** — `Hmono` discharged by `hardy_le_of_lt`, `HG` by
   `G_le_of_atomTrue`, over the real `goodsteinSeq`-based `G`. Re-stated the witness-bounded calculus
   `B` over **`ONote`** (Towsner's `<ε₀` = the notation system), well-founded descent via
   `ONote.lt_def`.
3. **RESOLVED the gAll/I∀ crux** — the lap-4 "accumulating existentials" wall. Key insight: in a set
   sequent the ω-rule keeps `gAll`, so a direct "all-out-of-reach" invariant is *not* preserved (you
   re-expand `gAll` at a small reachable index and `trueR`-close the whole sequent). **Fix: invert
   the universal away, don't accumulate.** Built:
   - `B.mono_k` — `k`-monotonicity (raising `k` relaxes all side conditions),
   - `B.allInv` — **∀-inversion**: `B α k Γ`, `gAll∈Γ` ⟹ `B α (max k n₀) ({gEx n₀} ∪ Γ\gAll)`
     (principal `allI` premise lifted via `weak`; others commute, k-weakened up),
   - `lowerBound_hardy` — the **full Towsner Thm 17.1** over the concrete Hardy hierarchy: no
     witness-bounded cut-free derivation of the Goodstein sentence at `(α,k)`, **modulo domination
     `Hdom : ∃ x, hardy α (max k x) < G x`**. (Invert `{gAll}` at the dominating index → gAll-free
     `{gEx x}` → apply lemma 2.)
4. **Self-answered the lap-4 `ON-LINE-REQUEST`** via WebSearch (egress works server-side this lap):
   the rigorous invariant is the Schwichtenberg–Wainer / Arai *disjunctive* boundedness lemma
   ("*some* formula of Γ witnessed below `H_α(N)`"), applied *after* ∀-inversion. Written up in
   `ANALYSIS-2026-06-22-bounding-resolution.md` (refs: SW *Proofs and Computations* Ch.4; Arai
   arXiv:2003.13207; Pakhomov arXiv:2109.06258).

## The remaining girders (hardest-first)

- **O0′ (next): discharge `Hdom`** = `∃ x, hardy α (max k x) < G x`, i.e. Goodstein length strictly
  exceeds the Hardy level at some argument. **`G n` = Track-1 `goodsteinLength n`** and the Goodstein
  defs are **byte-identical** between repos, so PORT `lean-formalizations
  Logic/Goodstein/{Domination*,TowerDomination,GrowthStatement,Length,...}` →
  `goodsteinLength_dominates_fastGrowing {o:ONote}(ho:o.NF) : ∃ N, ∀ m≥N, fastGrowing o m ≤
  goodsteinLength m + 2`. Then chain `hardy α m ≤ fastGrowing α m` (`hardy_le_fastGrowing`, m≥2) +
  identify `G = goodsteinLength`. **Watch the `+2`/strictness gap:** the Track-1 bound is `≤ +2`, but
  `Hdom` needs strict `<`; close it by using a strictly larger ordinal or arg (fastGrowing's gap over
  hardy swallows the +2 for large m) — this small strictness bridge is the one genuinely-open math
  bit, a good Aristotle target. NB Track-1 domination carries documented `native_decide` finite
  base-case axioms — they will show in `#print axioms` (acceptable; document in the ledger).
- **M4 — embedding `PA⁺ ↪ B`** (Towsner §16). The OTHER big girder. Reuse Foundation's finitary
  `Derivation`; map rules across, `∀`→ω-rule, finite induction instances ⟹ finite cut rank; produce
  the witness-bounded `(α,k)` bounds. Foundation-heavy — not Aristotle-friendly.
- **M7 — assembly**: PA⁺↔real-`ℒₒᵣ`-PA language bridge (opaque Σ₁ `goodsteinSentence` vs
  `∀x∃y g_y(x)=0`, Towsner Remark 10.3) + chain M4 ⟹ cut-elim ⟹ `lowerBound_hardy` ⟹ contradiction
  ⟹ discharge the headline `sorry`. Re-evaluate Route A (`Con(PA)`, stays in real PA) vs Route B.

## Build / file map
- `src/GoodsteinPA/{Defs,Encoding,Bridge,Statement}.lean` — Phase 0 (headline `sorry`). LOCKED bits.
- `src/GoodsteinPA/{Computability,Reduction}.lean` — M1 (axiom-clean) + M2 (Gödel II hook).
- `src/GoodsteinPA/Zinfty.lean` — `(α,c)` cut-elimination (M3+M5), axiom-clean. **Off the headline
  path** until cut-elim tracks the witness bound `k` (lap-4 finding); strategy ports.
- `src/GoodsteinPA/Hardy.lean` — **NEW lap 5**: ported Hardy/fast-growing hierarchy. Terminal asset.
- `wip/LowerBoundHardy.lean` — **NEW lap 5**: the concrete witness-bounded calculus `B` over `ONote`,
  the ∃-fragment + ∀-inversion + full lower bound `lowerBound_hardy` (mod `Hdom`). All axiom-clean.
- `wip/WitnessBound.lean` — lap-4 abstract-`h/τ` version + the gap demos (`unbounded_proves_goodstein`).
  Superseded for the lower bound by `wip/LowerBoundHardy.lean`; keep for the architectural demos.
- `wip/FastGrowing.lean`, `wip/Zinfty.lean` — earlier scaffolding (history; keep).
- `ANALYSIS-2026-06-22-bounding-resolution.md` — the invert-then-bound resolution + literature.

## Aristotle
Egress **works this lap** (`aristotle list` returns; all jobs IDLE). Left idle deliberately — the
remaining work is a deterministic Track-1 PORT (`Hdom`) + Foundation-heavy M4 (not self-containable).
The one clean future Aristotle target: the strict-domination bridge (`+2`→`<`) once the port lands.
`ON-LINE-REQUEST.md` lap-4 item is RESOLVED (self-answered); see the ANALYSIS doc.
