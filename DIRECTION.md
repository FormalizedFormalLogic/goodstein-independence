# DIRECTION — GoodsteinPA (expedition charter)

Companion to `EXPEDITION-PLAN.md` (the math). This is the **operational charter** for an
autonomous treadmill campaign. Read both.

---

## ⚙️ CURRENT DIRECTIVE — altitude-lap-owned · binding on grind laps

> **WRITE-ACCESS: review & reflection (altitude) laps ONLY** (the operator may also set it). Grind
> laps READ this section and work strictly within it; they MUST NOT edit it. It **OUTRANKS** any
> `HANDOFF` "NEXT" pointer or in-flight campaign momentum — this is how an altitude lap's
> course-correction actually STICKS. The standing charter below changes rarely; THIS section turns
> over every few review laps. Keep it SHORT; detail lives in `PENDING_WORK.md` / `REFLECTION-*.md`.
> (Live milestone map = `E-CRUX2-ROADMAP-2026-06-24.md`; the phase list below is the standing charter.)

**Set: lap-137 (altitude review). Supersedes pre-lap-135 — the existence-form spike is DONE (lap 135,
ported to src); the open question is no longer "which form" but "close the existence form's two halves."**

- **THE objective (only this):** **M1b-term** — the crux-2 **termination** endgame, now =
  `false_of_ZDerivesEmpty` resting on its TWO sub-`sorry`s. After the lap-137 type-correction those are:
  1. **`exists_sigma1_descent_of_step`** (`Crux2Blueprint`, NEW) — build a `𝚺₁`-definable infinite
     `ε₀`-descent from the existence step. **← PRIMARY this & next laps (the literal "termination").**
  2. **`descent_step_K_majorIdx`** (`Crux2Blueprint:1613`) — the per-step cut-reduction descent
     (Ind-reduct redesign `iIndReductSeqG` underway; tag-4 chain = deep core). Secondary deep front.
- **⚠️ lap-137 STRUCTURAL FIX (do NOT undo):** the lap-135 `prwo_forbids_existence_descent`/
  `false_of_ZDerivesEmpty` concluded `False` in bare `𝗜𝚺₁` with NO PRWO hypothesis — **UNPROVABLE**
  (it ≈ `Con(𝗣𝗔)`, Gödel-barred; the per-step descent IS `𝗜𝚺₁`, so the termination half carries the
  PA-unprovable strength). Now corrected: PRWO enters via the explicit hypothesis **`InternalPRWO V`**
  (= crux-1's deliverable, "no `𝚺₁` `ε₀`-descent"), and `prwo_forbids_existence_descent` is a sorry-FREE
  composition of `exists_sigma1_descent_of_step` + `InternalPRWO`. The two halves above are what remain.
- **PRIMARY next move:** discharge `exists_sigma1_descent_of_step`. Decompose it in `src/` into the
  `𝚺₁` least-witness `redLeast` (`μ`-min over the `𝚫₁` matrix `ZDerivesEmptyR d' ∧ icmp(iord d')(iord d)=0`),
  its **internal `𝚺₁` orbit** `n ↦ redLeast^[n] z` (course-of-values recursion — internalize the
  EXTERNAL-ℕ iteration of `iord_iR2_iterate_descends`, `InternalZ:9816`), and `f n := iord(orbit n)`
  (`𝚺₁`, NF via `isNF_iotower`+`isNF_iotil_of_ZDerivation`, descends via `hstep`). This is the
  never-built M3 internalization — the load-bearing piece, neglected through laps 135-136.
- **Success metric:** *advance the crux toward discharge* — a sub-lemma CLOSED, OR honest
  DECOMPOSITION into named `src/` sub-`sorry`s (RAISES src count = PROGRESS, not regress). NOT: off-path
  lemma-banking, count-management, or hiding an active sorry in `wip/`.
- **FORBIDDEN:** re-deriving the deterministic `red`-fixpoint stall (the existence form RETIRED it);
  more `zReg`/`zFresh`/`zSeqAnt` folds as a *goal*; off-critical-path easy `sorry`s; M2 / M3 / M4 wiring.
  `descent_step_K_majorIdx` Ind-reduct work is permitted as the secondary front but the termination
  half (`exists_sigma1_descent_of_step`) is hardest-first: it VALIDATES the whole pivot end-to-end and
  was the dropped piece. If genuinely blocked, record in `PENDING_WORK.md` why + one concrete attack.
- **Why:** the lap-135 pivot was sound at the top but its termination half was MIS-TYPED (dropped PRWO)
  and the lap-136 grind sank into the *other* (legitimately-`𝗜𝚺₁`) sub-sorry's Ind-reduct redesign while
  the structural hole sat undiagnosed. Fixing the seam (lap 137) + closing the `𝚺₁`-descent is what
  actually locks the existence-form endgame.

### Directive history (newest first; append one line per altitude lap — never delete)
- **lap-137** (altitude review): existence-form spike DONE; TYPE-CORRECTED the PRWO seam (`InternalPRWO` hyp; `→ False` in bare 𝗜𝚺₁ was Gödel-barred). PRIMARY = `exists_sigma1_descent_of_step` (the 𝚺₁ ε₀-descent — neglected through laps 135-136); secondary = `descent_step_K_majorIdx`.
- **pre-lap-135** (operator + judge): focus to **M1b-term only**; existence-form spike FIRST; success = a `src/` sorry drops.

---

## The goal (not a fixture — the destination) 🦸

**Prove `Statement.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence`** — Kirby–Paris (1982),
Peano Arithmetic does not prove Goodstein's theorem. That headline `sorry` is the *target*, not
a thing to preserve. The whole campaign exists to discharge it honestly.

## You (the box) own the full decomposition

This is **formalization of a known proof**, not origination. Gentzen's ordinal analysis is ~90
years old and in textbooks (Gentzen 1936, Schütte, Takeuti). Decomposing it into mathlib-shaped
Lean lemmas is exactly treadmill work. The phases (see `EXPEDITION-PLAN.md` for the math):

- **Phase 0 — encoding.** DONE except `goodsteinTerminates_re` (below). Milestone **M1**.
- **Phase 1 — Gödel II hook.** Surface `Con(𝗣𝗔)` + `𝗣𝗔 ⊬ Con(𝗣𝗔)` from Foundation's *existing*
  Gödel II (`FirstOrder/Incompleteness/Second.lean`), and reduce the headline to the single
  implication `𝗣𝗔 ⊢ γ → 𝗣𝗔 ⊢ Con(𝗣𝗔)`. Assembly. Milestone **M2**.
- **Phase 2 — the girder.** `TI(ε₀) ⊢ Con(𝗣𝗔)`: infinitary `PA_∞` (ω-rule), ordinal assignment
  `< ε₀` to derivations, ε₀-bounded cut-elimination. The deep core. Decompose it; build on
  mathlib's ε₀ (`SetTheory/Ordinal/Veblen`, `ONote`) + Foundation's finitary Hauptsatz. Milestones **M3…**.
- **Phase 3 — `Goodstein ⟹ TI(ε₀)`.** Re-express, syntactically, the ordinal descent that the
  termination Engine (`lean-formalizations` `Logic/Goodstein`) already does model-side.
- **Phase 4 — assemble.** `γ ⟹ TI(ε₀) ⟹ Con(𝗣𝗔)`, then Gödel II ⟹ `𝗣𝗔 ⊬ γ`. Discharge the
  Statement `sorry`. `#print axioms` clean.

Decompose with **disclosed sub-`sorry`s** — a named lemma held at `sorry` is honest, checkable
progress. Bank green laps; chip the girder lemma by lemma.

## Literature — on disk + offline requests 📚

**On hand (read these FIRST):** `papers/` holds pre-downloaded proof-theory references (PDFs;
gitignored, but present on your disk via the bind-mount). `papers/SOURCES.md` is the catalog —
what each paper is and which phase it serves (Gentzen ordinal analysis, PA_∞ cut-elimination,
Kirby–Paris, Goodstein/Cichoń, fast-growing hierarchy). **Ground the girder in these, not in
memory** — infinitary proof theory is exactly where an LLM confabulates a plausible-but-wrong
argument. Quote the source; don't reconstruct it.

**For gaps:** you are network-isolated (no web, no GitHub). When you need a reference that isn't
in `papers/` — a specific lemma statement, the exact ε₀ cut-elimination bound, a notation
convention — **do not guess and do not stall.** Write an **`ON-LINE-REQUEST.md`** at the repo root
with precise questions; a host fulfiller researches it and commits `ON-LINE-FINDINGS-*.md` (and
may add a PDF to `papers/`) for you to read next lap. Getting the math right from the literature
beats inventing a decomposition.

## M1 — the immediate residual

```
Encoding.goodsteinTerminates_re : REPred goodsteinTerminates
```
`goodsteinTerminates m := ∃ N, goodsteinSeq m N = 0` is r.e. (search `N`); the only non-trivial
input is **`Computable bump`** (`Defs.lean`, well-founded recursion on `Nat.log` — mathlib won't
auto-derive it). Route: `Computable bump` → `Computable₂ goodsteinSeq` → `ComputablePred (·=0)` →
`ComputablePred.to_re` → `REPred.projection` (∃ N). See Foundation `Vorspiel/Computability`. Pure
computability: zero faithfulness risk (typechecks or it doesn't). Closing M1 makes Phase 0
axiom-clean (`#print axioms goodsteinSentence_faithful` loses its `sorryAx`).

## ANTI-FRAUD guard (the one hard rule) 🚫

A `sorry`'d headline is honest; a **fake** one is the worst outcome. You may replace
`Statement.peano_not_proves_goodstein`'s `sorry` with a real proof **only if BOTH**:
1. `#print axioms peano_not_proves_goodstein` = `[propext, Classical.choice, Quot.sound]`
   (no `sorryAx`, no custom `axiom`), AND
2. it genuinely chains through built lemmas (no `native_decide` on the headline, no
   `axiom`-smuggling, no vacuous restatement).
If you cannot do both, **leave the `sorry`** and report the gap. The host audits
`#print axioms` on the headline every review lap. Inventing an axiom to "finish" = failure.

## LOCK — faithfulness anchors (do NOT edit) 🔒

Add lemmas freely, but never change these — they are the trust base that makes the headline mean
what it says:
- `Defs.lean` — audited `goodsteinSeq` / `bump` / `base`.
- `Bridge.lean`'s theorem **RHS** `∀ m, ∃ N, goodsteinSeq m N = 0`, and the proved bridge.
- `goodsteinTerminates`'s definition in `Encoding.lean`.

## Mode + execution

- **Expedition** (`--forever`): no self-stop; this is a long campaign measured in
  accumulated axiom-clean mathlib-shaped lemmas, not a single green.
- **Offline build prerequisite**: the box must `lake build GoodsteinPA` offline from the CoW'd
  Foundation v4.31 + mathlib oleans in `.lake/packages` + the box's v4.31.0 Linux toolchain.
  Never `lake update` / fetch. (If lap 1 can't build offline, that's the host's bug to fix —
  rebuild the box image / re-CoW — not yours to route around.)
