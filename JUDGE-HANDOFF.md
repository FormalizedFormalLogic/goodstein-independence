# JUDGE HANDOFF — Goodstein-independence (judge / next-iteration-of-Ren baton)

> For a fresh Ren session inheriting this work. You are the **outside judge** of
> `~/src/goodstein-independence` — NOT a worker. An autonomous box + "Codex" grind the proof; your job is to
> read the **source**, catch **architecture/seam** errors they can't see from inside, calibrate **honestly**
> (confidence %, "how this could be wrong"), and relay high-value findings to Trevor, who pastes them to the
> box. **Faithfulness > fluency** — route load-bearing claims to the paper/compiler, never a summary.
> Updated 2026-06-24 (~lap 65); supersedes the lap-50 version. Re-run catch-up first — this WILL be stale.

## ⏳ DO THIS FIRST — a live A/B effort experiment stops ~06:13
Two CoW-clone arms are running a 4.5h effort probe (identical start `2beac51` + prompt; only `--effort`
differs): **`~/src/goodstein-ab-med`** (medium) and **`~/src/goodstein-ab-xhigh`** (xhigh), each
`lean-treadmill <arm> --max-duration 4.5h --effort <e> --prompt "<§8 objective>"`.
**Once both stop** (`lean-treadmill list` empty = done), pull the comparison and relay to Trevor:
```
for a in goodstein-ab-med goodstein-ab-xhigh; do echo "== $a =="; \
  grep '"event": "end"' ~/.local/state/lean-treadmill/$a.jsonl; done     # NEW per-lap metrics
git -C ~/src/goodstein-ab-med   log --oneline 2beac51..HEAD              # what med built
git -C ~/src/goodstein-ab-xhigh log --oneline 2beac51..HEAD             # what xhigh built
# THEN verify the nuts aren't vacuous: build each arm, #print axioms the case-5.1 nut
#   (iord_descent_iCritReduct / iord_descent_iCritReduct_object). "axiom-clean" is the box's claim, unverified.
```
- **Question:** does effort change the RESULT or just the PATH? Lap-1 preliminary (n=1, weak): med=breadth
  (13 commits, built the `ZDerivation`/`iR` objects), xhigh=depth (6 commits, nut end-to-end on "genuine
  reduct codes" + T4); **both ended src 3 / wip 7.** Reads as *converge to the same frontier, xhigh deeper
  per commit* — but n=1, "same sorry count" is coarse (likely different frontiers), divergence may be
  stochastic. The 4.5h run ≈ 9 laps each = the real sample.
- ⚠️ **Methodology honesty:** a single fixed-budget lap structurally rewards LOW effort (higher effort =
  more tokens/action ⟹ fewer actions/budget), so commit-count favors medium *by design*. The clean
  experiment is a **fixed-OUTCOME race** (same target → measure laps+tokens to reach it). The arms diverged
  after lap 1, so they're no longer a pristine RCT — read it as "two efforts, ~same start, who gets where."
- **Trevor is running this with genuine detachment — no stake. Report numbers straight; do NOT project
  hope/excitement onto him.** (He corrected me on exactly this.)

## Where the PROOF stands (VERIFY against HEAD)
- Headline `peano_not_proves_goodstein` = honest `sorry` (`[propext, sorryAx, choice, Quot.sound]`,
  anti-fraud intact). `goodsteinSentence_faithful` clean. `peano_not_proves_TI` clean (+1 native_decide).
- **Route RESOLVED — Route A (Rathjen Cor 3.7):** `PA⊢γ →(§3) PA⊢PRWO(ε₀) →(Gentzen Thm 2.8) PA⊢Con(PA)` → Gödel II.
- **crux-1 (γ→PRWO) is DONE + axiom-clean (lap 57).** The ONLY remaining math wall is **crux-2 (PRWO→Con)** —
  the Gentzen consistency proof arithmetized over coded derivations.
- **crux-2 is FULLY DECOMPOSED → `E-CRUX2-DECOMPOSITION-2026-06-24.md` (this session's main deliverable).**
  Key finding: the difficulty is ONE reduction case (**5.1, the cut-elim degree-drop**) gated behind TWO
  prereqs the box hadn't listed (**Lemma 3.1** critical-pair finder, **Theorem 3.4** rank bound). §8 takes
  it to leaf level: the ENTIRE genuinely-new content = **4 small leaves** — L3.1 finder; T2/T3 "replace-a-
  premise stays a valid Kʳ-chain"; T4a rank-substitution-invariance `rk(F(t))=rk(F)`; the `d{0}/d{1}` object
  construction (`iR` critical branch). Everything else is IH / ℕ-`max`-arithmetic / F1–F2 (in flight) / one
  tower lemma. **No monolith remains.** The box executes it leaf-by-leaf (commits name LH/T3.4/the-nut verbatim).
- **C0.5 Foundation→Z bridge** (seam I found; box added the milestone): turn a Foundation ⊥-proof into a
  Buchholz-Z ⊥-derivation. CHEAPER than first flagged — Z has a *native* `Ind` rule, so PA-induction maps
  directly (Bryce-Goré spent ~half their `Peano.v` unfolding induction into the ω-rule; we skip that).
  Blueprint = Bryce-Goré `Peano.v`. **Do NOT port their `cut_elim.v`** (infinitary; wrong for our primrec route).
- **Feasibility SETTLED:** Bryce-Goré (arXiv:2603.00487, Coq, Feb 2026) machine-checked Con(PA) via ordinal
  cut-elim. Finishability ~70%, multi-month but precedented + bounded. Clone: `scratchpad/Gentzen-bg/`.
- **OPERATOR DIRECTIVE (BINDING):** axiom-free (trust base only) **or ABANDON**. NO Gentzen-as-axiom on the
  headline (that cop-out is forbidden — I pitched it twice and was corrected). `PA_delta1Definable`
  (Foundation axiom under Gödel II) must ALSO be discharged. You MAY state+prove PRWO→Con as its own result;
  you may NOT rest the target on it. (See memory `feedback-formalization-no-axiom-copout`.)
- **OPERATOR DIRECTIVE (Trevor, 2026-06-25): M2 is SERIAL — do NOT parallelize.** The `E-CRUX2-ROADMAP`
  floated running M2 (Foundation→Z bridge) in a second box concurrently with M1. Trevor decided against it:
  **M2 runs serial in the one box, after M1. Do not spin a second worktree/treadmill for M2.** The roadmap's
  "parallel floor" (~75 laps) is reference-only; the serial path (~115–150 laps from lap 83) is the plan.
- **HARVEST.md** (box-built, judge-verified): reusable spin-offs with real `#print axioms` + destinations.

## Catch-up recipe (every session)
```
cd ~/src/goodstein-independence
git log --oneline -15
grep -rn "sorry" src/GoodsteinPA/Statement.lean
ls -t HANDOFF-*.md | head -1     # newest box baton → read it + STATUS.md + PENDING_WORK.md
```

## 🛠️ Tooling changed this session (committed to gotrevor/bin, NOT pushed — push is Trevor's call)
- `bin/lean-treadmill`: **`--max-duration D`** (wall-clock cap, e.g. `4.5h`; graceful between-lap stop, max
  overshoot one lap). The per-lap laplog `end` event now carries effort/kind/commits/src+wip-sorries/
  diffstat/wedged (the A/B metrics); new `_git_diffstat`. Commits `d3e52da`, `d106ce2`.
- `bin/test_lean_treadmill.py`: NEW, 24 green tests (the tool had none). Commit `9edab6a`.
- All UNPUSHED on `gotrevor/bin` main (which already held an unpushed backlog — pathspec-scope, don't sweep).

## Judge playbook (still true)
- Catch up from HEAD, not memory. `papers/` has Buchholz [6] (THE crux-2 source: §3 reduction, §4 assignment,
  Lemma 4.1/Thm 4.2 = eq 5), Rathjen 2014, Kirby-Paris, Cichoń, Arai, Buss; Bryce-Goré Coq in `scratchpad/`.
- Deliver findings the box can VALIDATE: cited claim + confidence % + validation checklist + "how this could
  be wrong," as a repo doc `E-*.md` (box reads on reflection laps) AND a tight paste for Trevor (the live
  channel). Keep status check-ins SHORT — headline, not a deep read each time.
- Converge, don't compete; credit the workers (the box adopted every finding this session). Add value the
  workers can't: source-grounded architecture/seam calls, library discoveries, faithfulness audits.

## Pointers
- THE decomposition (the prize): `E-CRUX2-DECOMPOSITION-2026-06-24.md` — §8 is the leaf-level grind-list.
- Prior finding: `E-EQ5-ROUTE-FINDING-2026-06-23.md` (eq-5 faithful; the bridge seam; feasibility/route).
- Box state: newest `HANDOFF-*.md`, `STATUS.md`, `PENDING_WORK.md`. Spin-offs: `HARVEST.md`.
- Buchholz §4: `o(d)=ω_{dg(d)}(õ(d))`; the box's `iord`/`idg`/`iõ` = this exactly (judge-verified faithful).

— start with the A/B review (time-sensitive), then the catch-up recipe + newest box HANDOFF, then ask:
"what's the next seam that has to join, and has anyone checked it joins?"
