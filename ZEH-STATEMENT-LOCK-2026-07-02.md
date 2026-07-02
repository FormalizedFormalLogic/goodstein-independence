# ZEH STATEMENT-LOCK (architect-owned, 2026-07-02) 🔒

> **Binding on all `Zᵉ` rebuild laps.** This locks the judgment forms Z1 pinned and the rails
> the four spikes paid for. Grind laps work strictly within it; they MUST NOT edit this file
> or deviate from a locked form — a lap that believes a locked form is wrong STOPS and
> escalates (baton note + verdict-style writeup), it does not improvise. Provenance:
> `SPIKE-Z1-VERDICT.md` + `E-2026-07-02-JUDGE-spike-z1-validation.md` (judge-ratified PASS),
> on top of `SPIKE-W4B-VERDICT.md` (the fork pin) and the W3/W4 ratified statements.

## 1. The calculus core — LOCKED verbatim

`Zeh α e H m c Γ` exactly as pinned in `wip/SpikeZ1Seams.lean` §2 (six constructors: `axL`,
`wk`, `weak`, `allω`, `exI`, `cut`), with:

- **slots**: derivation ordinal `α` · control `e` (**constant through a derivation** — no rule
  changes it) · operator **generator** slot `H : ONote → Prop` (side conditions are
  `Cl H`-membership; `Cl` = inductive closure under `+`/`expTower`/`osucc`/`ofNat`;
  `IsOperator (Cl S)` holds for every `S`) · **stage `m : ℕ`** (amendment A1) · cut rank `c` ·
  sequent `Γ`.
- **A1 (locked)**: `exI` bounds its witness by `hardy e m` at the judgment's stage; `allω`
  premises run at `(adjoin H n, max m n)` with branch ordinals in `relOp H n = Cl (adjoin H n)`.
  No rule lowers `m`.
- **Re-anchor closure (locked, from the W4B judge)**: every rule demands its ordinals
  `∈ Cl H` (`weak`'s source, `exI`'s premise, `cut`'s both premises) — no retroactive
  absolution.
- **Structural layer**: `mono_H` (generators + stage raised together; proven in the spike) is
  the only monotonicity rule. There is **no `mono_e`** — a membership-gated control-raise rule
  is kernel-refuted (`mono_e_membership_gate_refuted`); do not add one.
- **Wrapper**: `ZehProv` (∃-slack in the ordinal only, `NF` + `Cl H`-membership carried). The
  `ZekdProv` norm clause has no twin — deleted, permanently.

Seed the rebuild module (`src/GoodsteinPA/OperatorZeh.lean`) from the spike's §0–§2 + `mono_H`
+ `ZehProv` **verbatim** (namespace change only). The read-off block (§5: `ReadoffShape`,
`ReadoffGoal`, `readoff_sigma1`, `headline_readoff`) ports verbatim too — it is proven and is
the fixed exit.

## 2. Hard rails (kernel-paid; violations are wrong by construction)

- **(R1) No numeric fact routes through `H`-membership.** K1–K3 (`Cl_of_NF`,
  `finite_part_unbounded`, `norm_ball_not_add_closed`) prove membership at `ε₀` is
  information-free: every NF notation is in every closure, and no concrete `H` can certify
  norms. Membership is ordinal bookkeeping ONLY. A statement that "pays" a bound by
  membership is a bug even if it typechecks.
- **(R2) Existentials open at the ROOT only** (three spikes' trap; W3 judge catch). Never
  inside an induction motive; `ZehProv`'s ∃-ordinal is the one sanctioned wrapper.
- **(R3) `e` is constant through a derivation; control changes happen at STATEMENT level**,
  once per elimination pass (A2). The per-branch raise-then-`mono_e`-unify mechanism of
  SPIKE-W4 does NOT exist in `Zeh` — step/reduction motives hold their IHs at ONE control.
- **(R4) Numeric budgets are function-valued** (Eguchi–Weiermann form, §3 below). Any ℕ-valued
  slot in a reduction/step motive re-opens the W4B seams and is forbidden.
- **(R5) No new `axiom` declarations, ever; `native_decide` only within the documented blessed
  base; sorries only as disclosed statement pins with a named discharging lap.**

## 3. The numeric carrier — Eguchi–Weiermann function slots (binding form, lap-1 pins the exact statements)

Per arXiv:1205.2879 (Def. 23 + Lemma 25; summary on disk at
`papers/eguchi-weiermann-2012-operator-controlled-id1.md`) and the verdict's §6, the
cut-elimination **statements** (not the judgment) carry a number-theoretic operator slot
`f : ℕ → ℕ`:

- **composition at principal cuts** (the reduction's output slot is `f ∘ g` of the premises' —
  `seam1_bump_absorbed_by_composition` is the kernel shape);
- **max-relativization at ω-nodes** (`rel1 f n = fun x => f (max n x)`; `rel1_comp` — proven,
  axiom-free — is the re-entry algebra; `seam2_function_slot_payable` is the kernel shape);
- **`hardy e` at the root instantiation** (the read-off's bound, A1's `(e, m)` axis).

The judgment `Zeh` itself stays f-free — LOCKED. The f-slots live in the elimination-lemma
statements. Flagged literature wants for the statement lap: Weiermann BSL 12(2) 2006 (the PA
case proper) + Buchholz MLQ 47 (2001) *Finitary Treatment of Operator Controlled Derivations*.

## 4. The exit — LOCKED (proven, do not restate)

```
headline_readoff : Zeh α e H m 0 {∃⁰ φ}  →  ∃ n ≤ hardy e m, atomTrue (φ/[nm n])
```

(atomic-matrix form; per-instance, no evaluator, no `H`-data). Every rebuild statement must
compose toward this exit. **Known gap, an explicit rebuild node (J3): the Δ₀ (bounded-∀)
matrix extension** — the Goodstein sentence's matrix is not atomic; the Towsner-5.4-style
extension of `readoff_sigma1` is scheduled work, not a discovered surprise.

## 5. Pre-registered risks (named at lock time; hitting one is a finding, not a failure)

- **(P1) Hardy-domination under raise** (W4B caveat (ii) + K2b): the once-per-pass control
  raise must re-establish `exI` bounds; discharge is per-instance at the headline (`e` is
  concrete there) or via f-slot carriage. If threading stays hard, the **BW87 fallback is
  pre-validated**: don't thread — eliminate cuts (ordinal may tower) and read off the
  cut-free derivation with the proven `readoff_sigma1`. Note the fallback still requires the
  cut-free output to be a LEGAL `Zeh` derivation (bounds payable at the raised control).
- **(P2) The Δ₀ read-off extension** (§4). Bounded quantifiers introduce `allω` nodes;
  extension pattern is Towsner 5.4 / the banked `prwoInstance` discipline.
- **(P3) The two Z1 pins** (`allInv_Zeh`, `cutReduceAllAuxRunning_Zeh`) are statement pins,
  and pin 2's LITERAL signature is expected to be superseded by the f-slot form in lap 1 —
  the LOCK covers §1's core, not pin 2's exact shape.

## 6. NOT locked (lap-1 statement work, judge-gated)

The f-slot reduction/step signatures (`cutReduceAllAuxRunning_Zf`-class, the common-control
step motive, the collapse iteration form `f ↦ f^{…}`). Lap 1 drafts them under §2–§3's rails
and STOPS for the judge before any grinding (see `REBUILD-Z-ORDER-2026-07-02.md`).

**Addendum (2026-07-02, post-lap-1 judge ruling — now LOCKED):** the lemma split is
Eguchi–Weiermann's own: **reduction/step statements run at FIXED control and COMPOSE the
slot (`f∘g`, Lemma 25); the elimination pass alone raises the control and ITERATES the slot
(Lemma 30).** A raised-control conjunct on a reduction statement is refutable (K2b re-tag +
`axL`-instantiation — see `E-2026-07-02-JUDGE-rebuild-z-lap1-validation.md`) and is now a
rail violation. Pin 3's iterate must be EXPLICIT (a bare `∃ f'` is kernel-checked vacuous,
`normControlled_exists_trivial`); its restatement is the lap-5 entrance statement mini-lock.
`stepAllω_Zf` stays unified (one ⋁-principal reduction; the ∀-side enters via `allInv_Zeh`).
