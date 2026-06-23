# REFLECTION — 2026-06-23 (lap 36, deep/every-9th altitude pass)

> Running on the stronger reasoning model; the job this lap is **direction**, not mechanics.
> Read: STATUS.md, HANDOFF lap 34/35, DIRECTION.md, DESCENT-PLAN.md §3b/§5, papers/SOURCES.md,
> ON-LINE-REQUEST.md, Encoding.lean + Bridge.lean (the trust base), InternalGoodstein/InternalBridge,
> DescentSemantic.lean (the wall), DescentCore/DescentConstruction (the substrate). Re-ran real
> `#print axioms` on the whole headline chain.

## 1. The destination is RIGHT — and the project is ONE theorem from done

Goal: `GoodsteinPA.peano_not_proves_goodstein : 𝗣𝗔 ⊬ ↑goodsteinSentence` (Kirby–Paris) axiom-clean.

Real kernel state this lap (verified, not from the stale ledger):

| theorem | `#print axioms` |
|---|---|
| `peano_not_proves_goodstein` (headline) | `propext, sorryAx, choice, Quot.sound` — honest open `sorry`, **0 math axioms** |
| `goodsteinSentence_faithful` (bridge) | `propext, choice, Quot.sound` — **clean** (statement means Kirby–Paris) |
| `goodsteinTerminates_re` (M1) | `propext, choice, Quot.sound` — **clean** |
| `Thm56.peano_not_proves_TI` (Buchholz §5 monument, Gentzen-1943 sharpness) | `propext, choice, Quot.sound, ONoteComp…native_decide.ax_1_5` — **CLEAN** (1 🟢 finite witness) |
| `…_modulo_semantic` (the would-be headline) | `…, sorryAx` — the **single** `sorryAx`, from `no_min_descent_absurd_of_goodstein` |

So: the **entire ordinal-analysis girder is finished and axiom-clean** — embedding M4, ε₀ cut-elim M5,
Boundedness Thm 5.4, C₁/C₂/D, F (F-φ discharged lap 28). This is a landmark: a complete Lean
formalization of Gentzen's `𝗣𝗔 ⊬ TI(ε₀)`. Goodstein is **not** in mathlib (SOURCES.md), so this is net-new.

The headline is exactly **one theorem** away: `DescentSemantic.no_min_descent_absurd_of_goodstein`
(Rathjen "Goodstein revisited" §3, carried out inside a model `M ⊧ paLX`). That theorem bottoms out
at two disclosed `sorry`s (`DescentSemantic.lean:410/419`):

```
hCD : ∃ m₀ : M, ∀ k : M, 0 < InternalPow.igoodstein m₀ k     -- wall C+D: descent ⟹ run never dies
hB  : ∃ k  : M,          InternalPow.igoodstein m₀ k = 0       -- wall B : but Goodstein says it dies
exact absurd hk (hpos k).ne'                                   -- ⊥
```

The destination has **not** changed and needs no recalibration. The honest realistic endpoint is a
**fully axiom-clean** headline (no cited axiom) — it is genuinely in reach, not "one narrow axiom + a
remainder". Nothing in the literature or mathlib has shifted this.

## 2. The highest-value finding: **WALL B IS SELF-INFLICTED — dissolve it by refactoring the sentence**

This is the course-change this lap exists to find. The grind laps (and every HANDOFF/DESCENT-PLAN since
lap 24) have treated `goodsteinSentence = ∀⁰ (codeOfREPred goodsteinTerminates)` — Foundation's **opaque**
`Classical.epsilon`-over-Kleene-normal-form r.e. blob — as a **fixed, immutable** contradiction target,
and poured effort into *bridging to it*: "`𝗜𝚺₁ ⊢ codeOfREPred goodsteinTerminates(m) ↔ ∃N igoodstein m N=0`
inside an arbitrary nonstandard `M`" (wall B; the open `ON-LINE-REQUEST.md`; the "`PA_delta1Definable`-
flavoured gap" of DESCENT-PLAN §3b). That bridge is genuinely hard — you cannot reason about a code picked
by `Classical.epsilon` on nonstandard inputs — which is *why* it became the literature gate.

**But `goodsteinSentence` is not locked, and the refactor is explicitly sanctioned.** Read the trust base:

- `DIRECTION.md` LOCK list = `Defs.lean`, `Bridge.lean`'s **RHS** `∀ m, ∃ N, goodsteinSeq m N = 0`, and
  `goodsteinTerminates`'s definition. `goodsteinSentence` itself is a plain `noncomputable def` — **not** locked.
- `Encoding.lean`'s own docstring (lines 35–39, "Faithfulness note (Phase 2+ caveat)"): *"A `codeOfREPred`-
  built `γ` is faithful … but it is an opaque representability blob. The later reduction … **may want a
  more transparent, hand-built form; if so, that refactor is gated by matching this bridge's spec**, so
  faithfulness can never silently regress."* The Phase-0 author **foresaw** exactly this and built the
  bridge spec as the safety gate.

**The move.** Redefine `goodsteinSentence` as the transparent Π₂ sentence
`∀⁰ ∃' (igoodstein-graph(·,·) = 0)` built from the repo's own `igoodsteinDef : 𝚺₁.Semisentence 3`
(`InternalGoodstein.lean`), then re-prove `goodsteinSentence_faithful` (same locked RHS) via
`igoodstein_nat` (`igoodstein = goodsteinSeq` on ℕ) + `igoodstein_defined`. Faithfulness is preserved
**by the gate**; the sentence is *more* auditable, not less (a transparent run vs. an `epsilon`-chosen code).

**Why it dissolves wall B.** In `DescentSemantic.no_min_descent_absurd_of_goodstein`, `hgood :
M ⊧ lMap Φ goodsteinSentence` then says, transparently, "in `M`'s `𝗜𝚺₁`-reduct, `∀ m ∃ N igoodstein m N = 0`."
Instantiate at `m₀` ⟹ `hB` directly. The opaque-code↔run bridge (wall B) **vanishes**; what remains is a
mechanical Foundation `Defined`/eval of the *same* Σ₁ formula whose interpretation **is** `igoodstein`.

**De-risking (all verified this lap):**
- `igoodsteinDef`, `igoodstein_defined` (`𝚺₁-Function₂ … via igoodsteinDef`), `igoodstein_nat` all exist
  (`InternalGoodstein.lean:46–52`, `InternalBridge.lean:118`).
- Import DAG is clean: the whole `Internal*` chain is `Encoding`-free, so `Encoding → InternalGoodstein`
  introduces **no cycle** (only `Bridge`/`Reduction`/`Statement` import `Encoding`).
- `models_lMap_goodstein` (the front half, lap 30) is **form-independent** (it goes through the X-free
  proof translation `paLX_derivable2_lMap_of_PA_provable goodsteinSentence h`), so it survives the swap.
- Complexity unchanged: both forms are Π₂ (`∀m` of a Σ₁ body). Same statement of Kirby–Paris.

**Net effect.** Wall B → mechanical. `ON-LINE-REQUEST.md` becomes **moot** — the project's ONLY literature
gate is removed, and the entire remaining path is offline-closeable. Two walls → **one**.

## 3. The genuine remaining content after that: wall C+D (`hCD`) — Rathjen §3 internalized in `M`

`hCD : ∃ m₀, ∀ k, 0 < igoodstein m₀ k` — from a `≺`-descent (`no_min`), build a seed whose internal
Goodstein run never terminates. This is the real mathematics and it is **not** literature-gated; the
ONote-level kernel is already built and route-neutral:

- `DescentCore.lean`: `C` (the `C(β)≤k+1` slow-down measure), `Canon_iff_C_le`, `omegaStack`,
  `C_betaTail_le`, `repr_betaTail_within/boundary`, **`ineq6_step`** (Rathjen Lemma 3.6, ineq (6)),
  `lemma36_ineq6`, `lemma36_nonterminating` — the §3 math at ONote/ℕ level.
- `DescentArith.lean`: `ineq6_internal`, `nonterminating_internal` — the run side internalized in `V ⊧ 𝗜𝚺₁`.
- `DescentConstruction.lean` (lap 35, sorry-free, in `src/`): `IsDescent`, **`descent_seq_exists`** + the
  LX-definability combinators — the M-internal descent existence.

Remaining: (1) extract a coherent descent **function** `a : M → M` from `descent_seq_exists`; (2) construct
`βₖ` from `a` and **internalize the `DescentCore` ONote/`C` facts into `M`'s reduct as `LX`-definable
functions** (the hard part — moving notation arithmetic into a nonstandard model); (3) wire to the run
side ⟹ `hCD`. Several laps, fully offline. "Internalize the built kernel," not "discover the math."

## 4. Faithfulness at altitude

The audit surface is solid and the refactor *strengthens* it. `goodsteinSentence_faithful` keeps the
**identical** locked RHS `∀ m, ∃ N, goodsteinSeq m N = 0`; the headline `𝗣𝗔 ⊬ ↑goodsteinSentence` keeps
its honest `sorry` (anti-fraud) until `hCD`+`hB` are real and `#print axioms` is clean. No transcription
drift found in `Thm56`/`Statement`/`Bridge`. The one accepted artifact is the 🟢 `native_decide` F-φ
finite witness `ONoteComp.cmpStep_spec…ax_1_5` (a CNF-comparison base case) — fine indefinitely.

## 5. Direction call · KEEP · STOP · next target

**KEEP**
- The lap-30 **model-internal completeness** architecture (`descentE` via `completeness_of_encodable`/
  `consequence_iff_eq`): it dropped the §3b sequent-shape literature gate and resolved the free-`X`
  obstruction. Sound; keep it.
- The route-neutral **ONote kernel** (`DescentCore`) and the disclosed-`sorry` discipline.
- Faithfulness audit via real `#print axioms` every review lap.
- Route 1 (ordinal analysis). The monument is done; route 2 (Cichoń/Hardy) would re-need the same
  Boundedness machinery and is **not** a shortcut. Do not switch.

**STOP**
- Treating the opaque `codeOfREPred goodsteinSentence` as immutable.
- Pursuing wall B as an opaque-code↔`igoodstein` bridge inside nonstandard `M` (the `ON-LINE-REQUEST`).
  Stop trying to reason about a `Classical.epsilon` Kleene code on nonstandard inputs — refactor instead.

**Single highest-value next target (this is the new direction): refactor `goodsteinSentence` transparent.**
Order of operations for the next grind lap(s):
1. **Spike (de-risk):** in a scratch file, construct the transparent `Sentence ℒₒᵣ` from `igoodsteinDef`
   (subst result-slot `:= 0`, `∃` over the step var, `∀⁰` close) and confirm the eval lemmas
   (`igoodstein_defined` + `igoodstein_nat`) give `ℕ ⊧ it ↔ ∀ m ∃ N goodsteinSeq m N = 0`.
2. Redefine `goodsteinSentence` in `Encoding.lean` (import `InternalGoodstein`; drop
   `R0.Representation`/`codeOfREPred`). Re-prove `Bridge.goodsteinSentence_faithful` (unchanged RHS).
3. Close `hB` (`DescentSemantic.lean:419`) directly from `hgood`. Re-run `#print axioms` on the chain:
   target = `…_modulo_semantic` loses nothing and `hB`'s `sorryAx` share is gone; only `hCD` remains.
4. Retire `ON-LINE-REQUEST.md` (wall B moot) and grind **wall C+D** (`hCD`) — the lone genuine wall.

Confidence: high. The sanction is explicit, the substrate exists, the DAG is clean, and the front-half
lemma is form-independent. The one unknown is the Foundation ergonomics of building the Σ₁ sentence from
`igoodsteinDef` — hence the spike as step 1.
