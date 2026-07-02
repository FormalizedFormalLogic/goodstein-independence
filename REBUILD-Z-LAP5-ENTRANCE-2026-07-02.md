# REBUILD-Z — LAP-5 ENTRANCE MINI-LOCK: pin-3 restatement + laps 5–7 order (architect, 2026-07-02) 🔒

> **Binding.** Written by the judge/architect pass that ratified laps 2–4
> (`E-2026-07-02-JUDGE-rebuild-z-laps2-4-validation.md`). Companions: the LOCK (now carrying
> Addendum 2 — the `Zef` amendment) and `wip/ZefCutElim.lean` (the kernel-grounded shape
> finding this lock builds on). Grind laps work strictly within this; a lap that believes a
> locked form here is wrong STOPS and escalates — **self-ratification is a VOID offense**
> (ruling §5), no matter how good the evidence looks.

## 1. What pin 3 must become (the restatement's locked constraints)

Pin 3 (`cutElimPass_Zf`) as written is FORBIDDEN to discharge (vacuous `∃ f'`, Q2 — unchanged).
Its restatement is lap 5's statement deliverable, and it is CONSTRAINED, not free:

- **(C1) Judgment `Zef`, control untouched.** `e` is a *phantom* in `Zef` (no rule reads it —
  ruling §4). The restated pass does NOT "raise the control": there is no `raise e α` in the
  output. The ordinal collapses; the SLOT iterates. Any draft resurrecting a raised-`e`
  output is re-opening the fifth trap's corpse.
- **(C2) The output slot is a PINNED ordinal-indexed iterate — no `∃`, no plain `f^[k]`.**
  Kernel-grounded (wip/ZefCutElim finding, judge-endorsed): the `∃`-cut lane threads with
  plain iterates (`iter_comp`: counts ADD), but the `allω` node has ℕ-many branches with
  unbounded per-branch counts — a single `f^[k]` cannot dominate them (the same
  branch-unbounded demand that killed the `(k,d)` calculus). The index must read the
  ordinal: E–W Lemma 19's `N(α) ≤ f^{F^α(0)}(0)` coupling ("doubly operator-controlled").
  Target shape:

  ```
  cutElimPass_Zf : Zef α e H f (c+1) Γ → Monotone f → (∀ x, x ≤ f x) → α.NF → Cl H α →
      ZefProv (collapse α) e H (iterSlot f α) c Γ
  ```

  with `collapse : ONote → ONote` (Lemma 30's rank-lowering tower) and
  `iterSlot : (ℕ → ℕ) → ONote → (ℕ → ℕ)` (the ordinal-indexed iterate) both **explicit
  definitions** whose ONote-grounded form is lap 5's design work — with the E–W paper open
  (`papers/eguchi-weiermann-2012-operator-controlled-id1.md`), not guessed.
- **(C3) The exit must CONSUME the count.** The anti-vacuity test is composition: iterating
  the pass to rank 0 and feeding `headline_readoff_Zef` must yield a concrete bound
  `(iterSlot … ) 0` at the root instantiation `f = rel1 (hardy e) m`. A statement whose
  count the read-off never reads is severed-slot vacuity — the exact Q2 disease in new
  clothes. Lap 5 kernel-checks this composition AT STATEMENT LEVEL (bodies `sorry`,
  the composed corollary must typecheck with the bound expression visible in its statement).
- **(C4) Rails unchanged**: R1 (no numeric fact through membership — `Cl_of_NF` pays all
  memberships), R2 (existentials root-only; `ZefProv`'s ∃-ordinal is the one sanctioned
  wrapper), R5 (no new `axiom`s, sorries only as disclosed pins with named laps). Slots stay
  `Monotone` + inflationary through the pass — the carriers are `wip/ZefCutElim.lean`'s
  `iter_monotone`/`iter_infl`/`iter_normControlled`/`iter_le_of_le`/`iter_comp` (all
  sorry-free; PORT them to src as lap 5's first mechanical step).
- **(C5) Definitional obligations on `collapse`** (so the assembly can splice): NF-preserving;
  compatible with the descent bricks (`Zekd.add_osucc_descent`-class); strictly monotone in
  the sense the rank-lowering induction needs. State these as lemmas WITH the definition
  (bodies may be `sorry` pins with named laps if hard — disclosed, LOCK R5).

## 2. Lap plan (laps 5–7)

- **Lap 5 — STATEMENT LAP (no grinding; ends at a mini-verdict; STOP for the judge).**
  (a) Port the iterate bricks from `wip/ZefCutElim.lean` to src (mechanical, sorry-free).
  (b) Define `collapse` + `iterSlot` against ONote per C2/C5, with the paper open.
  (c) Restate pin 3 per C1–C2 (body `sorry`), DELETE the old vacuous form (it is dead — its
  `NormControlled`/`raise e` shape belongs to the retired stage world).
  (d) Kernel-check C3's composed exit corollary at statement level.
  (e) Write `REBUILD-Z-LAP5-VERDICT.md`; **STOP for the judge.** Statement traps have been
  caught at statement time six times running; this is the cheapest place to catch the seventh.
- **Laps 6–7 — the pass grind (judge-gated behind the lap-5 verdict).** Induction on the
  derivation: `∃`-cut lane via `stepAllω_Zf` + `iter_comp` (counts add); `allω` lane via the
  relativized ordinal-indexed count (`rel1 (iterSlot f (β n)) n`-class bookkeeping — the hard
  case, where Lemma 19/20's arithmetic lives); structural cases thread. Every lap green +
  headline undrifted + §6/§8b seam probes green; park with named blockers rather than force.

## 3. Pre-registered triggers (hitting one is a finding, not a failure)

- **T-Z5(i)**: the ordinal-count coupling cannot be STATED without an `∃` or without
  branch-indexed raise shapes (the W4B family) → escalate with the kernel probe; the shape
  question comes back to the architect. Do not improvise a judgment change.
- **T-Z5(ii)**: the composed exit corollary (C3) does not consume the count → the statement
  is wrong; back to the architect. (This is checkable at statement time — it should never
  survive into a grind lap.)
- **T-Z5(iii)**: the `allω` lane's Lemma-19 arithmetic is kernel-obstructed on ONote (the
  collapse/iterate pair cannot both satisfy C5 and dominate the branches) → verdict-style
  writeup; this is the ε₀ girder biting, and the response is architect-level (possibly a
  different `collapse` normal form), not more grinding.

## 4. FORBIDDEN (unchanged + new)

Pins 1–2, the `Zeh` core, `zeh_to_zef`, and the read-off block are **judge-owned frozen
surfaces** (hash-checked at the next judge pass). Route-A untouched. Δ₀ read-off extension
stays laps 8–10 (target `readoff_sigma1_Zef`). No self-ratification of any statement change
(VOID). No `(k,d)`-motive work. `wip/Spike*.lean` evidence artifacts read-only.

## 5. Suggested treadmill shape (operator fires; sized to the permitted scope)

- Lap 5 alone: `--max-laps 1` (statement lap + verdict, then it must STOP for the judge —
  a second lap would have nothing permitted to do).
- After the lap-5 judge pass: laps 6–7 as `--max-laps 3 --max-duration 6h`, prompt scoped to
  "discharge restated pin 3 per the ratified lap-5 verdict; FORBIDDEN list §4".

**Estimates** (calibration: grind runs 2–4× optimistic; statement/judge cadence has been
1-session-accurate): lap 5 = 1 session; the pass grind = 2–4 sessions with the `allω`/Lemma-19
lane the likely long pole; then the Δ₀ extension (laps 8–10) before the assembly audit.

---

## ADDENDUM (2026-07-02, post-lap-5 judge ruling — C2 AMENDED, now LOCKED)

Lap 5 (global lap 185) delivered a–e; the judge pass
(`E-2026-07-02-JUDGE-rebuild-z-lap5-validation.md`) caught the **seventh statement trap** in the
draft's iterate index: `iterCount α := norm α + 1` is a fixed syntactic count, and the `allω`
reassembly containment is kernel-refuted (`wip/JudgeTrap7Probe.lean`: at `α = ω`, branch
`ofNat 2`, `f = hardy ω`, parent side `11 < 23` branch side; `norm` is not monotone along `<`).
**C2 as locked now reads**: the output slot is the **diagonalizing** ordinal-indexed iterate —
`iterSlot f 0 = f`, `iterSlot f (a+1) n = iterSlot f a (f n)`, `iterSlot f λ n =
iterSlot f (λ[n]) n` (the E–W Lemma 19 `F^α(0)` transfinite form, same fundamental-sequence
recursion as `hardy`). `collapse := expTower` is ratified as drafted. Laps 6–7 are **OPEN**:
first item = discharge the disclosed C5 pin `iterSlot_monotone` (mirror `hardy_monotone` with
the f-relative reaches comparison), then the pass induction (`∃`-cut/structural lanes, then the
`allω`/reaches lane). T-Z5(iii) is resolved at statement time; its grind residue is the
reachability arithmetic, a proof burden, not a statement unknown.
