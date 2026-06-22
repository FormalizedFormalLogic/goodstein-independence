# HANDOFF — 2026-06-22 (lap 12)

> **Branch** `plan` · **HEAD** `605d5ba` (+ uncommitted doc updates this lap) · build **green**
> (`lake build GoodsteinPA`, 1258 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms) · `wip/OperatorZinfty.lean` green, 0 sorries.
> **Lap 12 = a REVIEW lap with two findings: (a) PROVED the §19.6 norm-budget half (`cutReduceAllAux`,
> axiom-clean); (b) PIVOTED the whole route to Buchholz's witness-FREE Boundedness analysis, which reuses
> the done M4+M5 and avoids the witness-bounded wall.** Read `ANALYSIS-2026-06-22-lap12-buchholz-pivot.md`
> FIRST, then `STATUS.md`, then `PENDING_WORK.md` (lap-12 top).

## 🎯 THE PIVOT (the headline of this lap — read the analysis doc)
Reading **Buchholz "Beweistheorie" §5** (`papers/buchholz-beweistheorie-lecture-notes.pdf` pp. 26–31)
end-to-end showed the project drifted (laps 4–11) onto Towsner's HARD witness-bounded variant. The
**standard Gentzen analysis** bounds PA's ordinal via the **witness-FREE `Z∞`** (= our M5) + a
**Boundedness** theorem on `TI_≺(X)` (Thm 5.4) — NOT a witness-bounded calculus. Its **Embedding** (Thm
5.5) and **Cut-Elimination** (Thms 5.1/5.2) are EXACTLY our **M4 `embedC`** and **M5 `cutElim`**, both
DONE & axiom-clean. So the two hardest pieces are already built; the remaining work is **Boundedness +
Goodstein⟹TI(ε₀)** — strictly less surface than Towsner, and the textbook-standard route (= DIRECTION.md's
original plan). The lap-11 "embedC is the wrong object / need witness-bounded `Zᵏ`" verdict was a
**conflation**: lap 11 killed naive *witness*-extraction (height ≠ witness bound — `G(5)` at height 1),
but Buchholz's Boundedness bounds the **order type** of `≺` via the set variable `X` + X-positive truth
semantics `⊨^α`, sidestepping witnesses. **M6 (Hardy) + the `wip/` witness-bounded calculi drop off the
critical path** (banked, not deleted).

## 🎯 NEXT LAP — execute the Buchholz route (`PENDING_WORK.md` lap-12 top has the full plan)
- **0. VERIFY-FIRST (cheap, do before deep work):** (a) M5/M4 accept a set variable `X` (extend
  `ℒₒᵣ`→`ℒₒᵣ∪{X}` or add a fixed relation symbol — `embedC.axm`/`provable_true` only need the `X`-free PA
  axioms, so should extend); (b) Goodstein⟹TI_≺(X) is provable in PA via the Phase-0 CNF-ε₀ encoding.
- **1.** Truth semantics `⊨^α Γ` (`X := {n : |n|_≺<α}`), `Prog_≺`, ≺-norm, order type `‖≺‖`, X-positivity.
- **2.** **Boundedness (Thm 5.4)** = the new theorem: induction on the cut-free `Provable β 0`-derivation
  (8 cases, Buchholz p.29). Corollary `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`.
- **3.** Goodstein ⟹ TI_≺(X) bridge (Kirby–Paris/Cichoń; reuse Phase-0 encoding).
- **4.** Assembly ⟹ discharge headline, `#print axioms` clean.

## ✅ Lap-12 (a): §19.6 norm-machinery PROVED (`wip/OperatorZinfty.lean`, axiom-clean) — banked off-path
`cutReduceAllAux` (Towsner's ∀/∃ cut-reduction on the witness-bounded `Zekd`) now compiles with 0 sorries,
`#print axioms = [propext, choice, Quot.sound]`. Cracked the **norm-budget** half of the 5-lap wall via a
self-derived **norm-carrying `ZekdProv` wrapper** (`∃ α'≤α, α'.NF ∧ norm α'<k+d ∧ Zekd α' …`) + threaded
`norm γ<k+dd` + `+1` d-bump (ADDENDUM 6). All 10 induction cases incl. the key `allω`-commuting +
`exI`-principal. **BUT** the **witness-budget** half is numeric-unclosable (ADDENDUM 7): `allInv` gives the
∀-family at `max k₀ n`, and Towsner's commuting-ω bound is false for large `n` — needs the operator `H`.
This proof is reusable norm-machinery for an operator-`H` build IF the Buchholz route ever stalls; it is
NOT on the live chain. (`le_add_right_NF` helper also added.)

## State of the spine (Buchholz route)
- **M1, M2, Phase 0/1** — done, clean. Phase-0 encoding feeds the Goodstein⟹TI bridge.
- **M4 embedding** (`src/Embedding.lean`, `embedC`) — **done, axiom-clean = Buchholz Thm 5.5.** ON path.
- **M5 ε₀ cut-elim** (`src/Zinfty.lean`, `cutElim`) — **done, axiom-clean = Buchholz Thms 5.1/5.2/5.3.** ON path.
- **Boundedness (Thm 5.4)** — the NEW theorem, lap-13 target.
- **M6 Hardy lower bound** (`src/LowerBound.lean`) — done, clean, but **OFF the critical path** (banked).
- **`wip/` witness-bounded calculi** — banked off-path; lap-12 `cutReduceAllAux` is the furthest reached.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry` intact.
- **Literature on disk:** Buchholz §5 (the route), Buss Handbook ch.II (PA proof theory), Cichoń/Kirby–Paris
  (Goodstein⟹ε₀). `Read` the PDFs directly (`pages` param). `papers/SOURCES.md` catalogs them.
- **`WebFetch` dead; `WebSearch` works.** No open `ON-LINE-REQUEST.md`.
- **Build:** `lake build GoodsteinPA` (1258); test wip via `lake env lean wip/OperatorZinfty.lean`.
- **Aristotle:** idle (no genuinely-open lemma on the live chain yet; Boundedness will furnish one).

## Lap-12 commits
- `605d5ba` §19.6 `cutReduceAllAux` PROVED on `Zekd` (norm-machinery, axiom-clean).
- (this lap, docs) ADDENDUM 6/7, the Buchholz-pivot analysis, STATUS/PENDING/HANDOFF refresh.
