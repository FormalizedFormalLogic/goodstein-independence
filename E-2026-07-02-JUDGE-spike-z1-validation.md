# E — JUDGE validation of SPIKE-Z1 (Ren, 2026-07-02)

> Host-side judge pass on the Z1 spike (`3683ef2`), per the don't-trust-box-handoffs rule.
> Companion to `E-2026-07-02-JUDGE-spike-w{3,4,w4b}-validation.md`. **The verdict asymmetry
> REVERSES here**: W4B was a FAIL-that-mandates-redesign (strawman-hunt the refutation); Z1 is
> a PASS-that-green-lights-a-multi-lap-rebuild, so the designated hunt is the **fake PASS** —
> seams that "close" vacuously, an interface mismatch between the seam probes and the concrete
> `H`, a read-off that doesn't defend the pass. See §3: the box found the vacuity itself,
> kernel-proved it, and disclosed it as the verdict's lead — the hunt confirms the disclosure
> rather than catching a concealment. First spike run under the judge-privacy rules (W4 §8):
> the rubric lived host-side; nothing to leak.

## 1. Verdict RATIFIED — independently re-verified

- `lake env lean wip/SpikeZ1Seams.lean` → **exit 0**; warnings = exactly **two** sorried
  declarations (`:419` `allInv_Zeh`, `:437` `cutReduceAllAuxRunning_Zeh` — the two §3 statement
  pins; the literal `sorry` tokens sit at `:423`/`:444` as the verdict says). All **18** in-file
  `#print axioms` outputs match the verdict's table **line for line**; `sorryAx` appears ONLY on
  the two pins and on `probe_cut_all_arm_Zeh` (which consumes them — every other theorem sharing
  the same imports prints clean, so the imported bricks it uses are clean and the pins are its
  only sorry source).
- **No new `axiom` declarations, no `native_decide`, no `set_option`/`unsafe`/`macro` escape
  hatches** (grep: the only "axiom" hit is the `#print axioms` banner comment).
- Commit `3683ef2` scope: `wip/SpikeZ1Seams.lean` + `SPIKE-Z1-VERDICT.md` +
  `HANDOFF-2026-07-02-lap174.md` only. No `src/` edit, no LOCK, no `DIRECTION.md` edit, no
  re-threading of `OperatorZinfty` — every forbidden-list item held.
- Sequent/witness sanity spot-checks against banked signatures: `hardy_omega`
  (`Hardy.lean:1336`, `hardy ω n = 2n+1`) and `hardy_ofNat` (`:1326`, `= x + k`) confirm the
  K2b arithmetic (`hardy ω 0 = 1 < 5 = hardy (ofNat 5) 0`) and the concrete read-off instance
  (`hardy ω 1 = 3`); `hardy_monotone` (`:1197`) is monotone in the **stage** argument — exactly
  what `mono_H`'s `exI` case spends (no control-raise, hence no gate). `atomTrue` is the repo's
  established per-instance meta-evaluator (`OperatorZinfty.lean:40`, the same one `Zekd`'s
  `trueRel` discipline already uses) — applied here only to atomic instances/literals; no new
  truth machinery entered.
- **T-Z1 does not fire.** PASS stands, with the amendments ratified (§4) and the judge caveats
  in §5 binding on the rebuild.

## 2. The pins — statement-trap hunt (the W3-catch discipline)

A sorried pin with a trapped statement would make both Q1 probes vacuous, so the two pins got
the full quantifier/threading audit:

- **`allInv_Zeh`** mirrors the banked, PROVEN `Zekd.allInv` (`OperatorZinfty.lean:484`)
  verbatim: output at the relativization `adjoin H n₀` and raised stage `max m n₀` (was
  `max k n₀`, `d` inert — the `k`-axis returns as the stage, the `d`-axis is deleted). No
  existential anywhere, `e` constant, output shape is precisely the reduction pin's input
  shape — the handoff **type-checks in the kernel** inside `probe_cut_all_arm_Zeh` (the same
  check W4B ran on the `Zekd` side). Plausibly provable by the same induction as the banked
  original (memberships lift by `Cl_mono`; the `exI` bound rides `hardy_monotone`); grind-shaped,
  correctly deferred.
- **`cutReduceAllAuxRunning_Zeh`** carries the ratified W4/W4B skeleton unchanged (output
  ordinal class `osucc (α + γ)`, output control `raise e α`, inner recursion `∀`-quantified
  with the existential only inside the root-level `ZehProv` wrapper — the established pattern,
  no `∀∃/∃∀` inversion). The ONLY change from the refuted `Zekd` statement is the deletion of
  the `(dd + norm α + 1)` budget slot in favor of `Cl H`-membership of the output ordinal.
  Doctrine compliance: existential root-only ✓, `e` constant through the inner recursion ✓
  (`raise e α` is fixed by the outer `α`), branch dependence only via the relativization ✓.
- **Non-vacuity of the probes consuming them**: `probe_cut_all_arm_Zeh`'s conclusion demands a
  derivation of the *cut result* `Γ` (arbitrary, constrained only through the IHs) — not
  producible without actually running inversion + reduction; the probe genuinely composes
  `allInv_Zeh → fam → reduction → weakening` and its membership obligation is discharged by
  `seam1_membership_absorbed` (two `Cl` constructors, `[propext]` only). The seam-2 probe's
  hypothesis family is realizable: `two_level_config_Zeh` (sorry-free) rebuilds W4B §3's exact
  configuration — one `allω` at `ω^ω`, every branch a rank-`c` principal ∀/∃ cut at premise
  ordinals `ω·(n+1)` = the family that kernel-refuted every ℕ-slot
  (`seam2_no_uniform_slot`, `SpikeW4BBudget.lean:273`) — as a legal `Zeh` derivation.

## 3. The designated hunt: is the PASS fake? (vacuity, interface coherence, the read-off)

**The vacuity question.** The trivial-`H` strawman (`H := fun _ => True` closes every seam
vacuously) turns out not to be a strawman but a **theorem the box proved about EVERY `H`**:
`Cl_of_NF` (K1) shows every normal-form notation lies in the closure of every generator set —
at `ε₀`, membership side conditions are uniformly dischargeable and carry zero numeric
information. The box led the verdict with this ("stated up front because a judge will
(correctly) hunt for it"). Judge assessment of whether the PASS survives its own K1:

- **The seams the order asked about are genuinely dead, not hidden.** W4B's refutations were
  *statement-composition* failures of ℕ-valued slots (`seam1_uniform_slot_unpayable`,
  `seam2_no_uniform_slot` — both parametric, both kernel facts). `Zeh` deletes those slots.
  The probes verify the replacement obligations compose (arm emission = motive's demanded
  form; ω-re-entry = the rule's premise form). "Closure absorbs the seams" is true precisely
  *because* membership is information-free — and the order's PASS criterion was seam closure
  with real membership proofs, which is what was delivered.
- **The calculus is NOT vacuous.** The numeric content never left: the `exI` rule carries a
  real bound `n ≤ hardy e m`, and `readoff_sigma1` is a genuine **soundness theorem** — a
  rank-0 `Zeh` derivation of `{∃⁰ φ}` forces a TRUE instance with witness `≤ hardy e m`. A
  trivial calculus could not prove that; the read-off is itself the non-vacuity certificate.
- **Interface coherence (rubric item): HELD.** The seam proofs consume ONLY the four `Cl`
  constructors (= `IsOperator`'s conditions, verbatim: `isOperator_Cl`); the concrete `H` is
  `Cl gen` with `IsOperator (Cl S)` proven for **every** `S` — nothing smuggled into Q1 that
  Q2's `H` lacks. Relativization coherence is free by construction: `H[n] = Cl (adjoin H n)`
  is an operator by the same theorem (the generated formulation the order explicitly
  permitted; closure trivially survives adjoining `ofNat n`).
- **The rubric's original Q2 defense ("the read-off is FALSE for the trivial `H`") is
  IMPOSSIBLE — and the box proved why.** By K1 all closures are extensionally equal on NF
  notations, so no read-off can distinguish trivial from concrete `H`. The restructured
  defense is stronger: the read-off consumes NO `H`-data at all (verified: `H` does not occur
  in `readoff_sigma1`'s conclusion and the proof uses no `Cl` fact) — the bound rides the
  judgment's `(e, m)` and the `exI` rule's own side condition. This also dissolves the
  "Σ₁-definability of the concrete `H`" headline risk exactly as claimed.
- **The `exI` witness design point (rubric item): resolved, not vacuous.** A1 makes the
  designated argument a judgment-carried stage `m`, threaded `max m n` at ω-premises. `m` is
  pinned by the root judgment the embedding will produce; no rule lowers `m` (checked all six
  constructors); `mono_H` raises it only monotonically, which *weakens* the read-off bound —
  the sound direction. The pin's original "`m ∈ H ∩ ℕ`" is kernel-refuted
  (`finite_part_unbounded`) — the order demanded this design point be confronted; it was.

**Conclusion: the PASS is real, but its meaning is scoped** — the `H`-membership layer is
ordinal bookkeeping (harmless, literature-shaped, inert), and the fork's actual content is
(a) the deletion of the structurally-diseased ℕ-slots, (b) the surviving `(e, m)`/`exI`
numeric axis with its proven read-off, and (c) the Eguchi–Weiermann function-valued carrier
for the reduction statements. The verdict says exactly this; the judge concurs.

## 4. Amendments A1/A2 — ratified (both kernel-forced, in-file)

- **A1 (stage designation)**: forced by `finite_part_unbounded` (K2a). Also independently the
  literature's own form (Buchholz–Wainer Bounding Lemma; Eguchi–Weiermann's max-adjunction
  `f[n]` — `Zekd`'s `max k n` axis returning in operator dress). Ratified.
- **A2 (common-control motive)**: forced by `mono_e_membership_gate_refuted` (K2b) — the
  kernel exhibits `e < e' = raise e 1`, both NF, both in every closure, with
  `hardy e' 0 < hardy e 0` (CNF absorption: `ofNat 5 + ω = ω`). So no (NF, `<`, membership)
  rule package restores the `exI` bound after a raise; `Zekd.mono_e`'s gate was genuinely paid
  by the numeric premise-norm conditions `Zeh` deletes. **This corrects the W4B verdict's
  carries-over list on one point**: SPIKE-W4's `step_allω` per-branch raise-then-unify does
  NOT port. The probes are stated at a common control accordingly. Ratified — with the note
  that A2's *replacement mechanism* (root-parameter control with once-per-pass raise and
  per-instance hardy-domination, or witness data on the `f`-slot) is design, not yet a kernel
  probe; it is correctly the rebuild's first-lap statement work (§5-J2).

## 5. Judge findings — binding caveats for the rebuild (none verdict-changing)

- **(J1) No numeric fact may route through `H`-membership — now a hard rail.** K1–K3 make the
  membership layer inert; any rebuild statement that "pays" a bound by membership is wrong by
  construction. The verdict states this; the statement-LOCK makes it binding.
- **(J2) Pin 2's literal statement is expected to be SUPERSEDED, and the surviving risk
  concentrates there.** Re-scoping item 1 re-keys the reduction/step statements to
  Eguchi–Weiermann `f`-slots in lap 1 — so what Z1 locked is the **calculus core + A1/A2 +
  the read-off exit**, NOT pin 2's exact signature. The hardy-domination-under-raise question
  (W4B caveat (ii), sharpened by K2b) lands on those statements. The BW87 fallback
  ("don't thread; read off the cut-free derivation") is kernel-validated as an exit
  (`readoff_sigma1` proven) — a real de-risk — but note it is not free: cut-elimination must
  still emit a LEGAL `Zeh` derivation, i.e. the transformed `exI` nodes' bounds must be
  payable at the raised control. Bounded risk, not zero; pre-registered for the rebuild.
- **(J3) The proven read-off covers ATOMIC matrices; the Goodstein headline matrix is Δ₀.**
  Bounded-∀ matrices introduce `allω` nodes the ∀-free lemma excludes (disclosed in the
  verdict). The Towsner-5.4-style bounded-quantifier extension of `readoff_sigma1` must be an
  explicit, estimated node in the rebuild order — without it the exit does not connect to
  `wainer_bound_of_pa_proves_goodstein`'s actual sequent.

## 6. Evidence checks (per the W4 §8 standing rules)

- **Attribution/independence, verified against the box transcript** (session `4e49b043…`,
  397 lines): the vacuity finding appears at **line 25** — the box's own early exploration —
  long before any literature contact. The box then reached the Weiermann operator literature
  through its own `WebSearch` (line 175–176, 04:27:59Z). The operator's Eguchi–Weiermann
  summary landed as host commit `f411cf4` at 04:54Z; the box's final commit `3683ef2` is its
  child at 04:58Z, folding in the corrected attribution. So the verdict's narrative —
  kernel findings first, "mid-spike the operator landed E–W", paper supplies the carrier —
  is **evidence-true**, and no unverified "independently found" claim is being ratified
  (the box *credits* the operator's drop; its own prior web contact makes the §6 mechanics
  partially independent anyway, which only strengthens the account).
- `f411cf4` commit surface: `papers/` summary + SOURCES entry only (host-side, operator's
  session — not the box, not this judge).
- Judge-privacy: this spike's rubric was written into the host-side handoff
  (KB inbox), never committed to the tree — the first spike judged fully under the W4 §8
  rules.

## 7. Effect on the plan

- **Deciding experiment #4: PASS, judge-ratified. The `Zᵉ` fork is real.** Four spikes, four
  1-session-accurate binary answers (W3 PASS, W4 PASS, W4B FAIL→fork, Z1 PASS); the spike
  cadence continues to pay for itself — this one converted a green-light question into a
  kernel-backed re-scoping (numeric carrier = function slots, not membership) *before* any
  grind lap was spent on the wrong motive.
- Risk mass after Z1: OFF "Σ₁-definability of `H`" (dissolved), OFF "do the seams reopen in
  operator form" (kernel-closed), ONTO "witness-threading design through cut-elimination"
  (J2 — bounded by the validated BW87 fallback) + the known W1/W2-class leaves + J3's Δ₀
  read-off extension. Estimate: ~7–11 laps for the rebuild stands (envelope ~7–20 under the
  2–4× grind-optimism calibration).
- **The rebuild gate is now OPEN** (DIRECTION green-light block: grind "GATED on a
  judge-ratified Z1 PASS" — this document). Next artifacts, architect-owned per the cadence:
  `ZEH-STATEMENT-LOCK-2026-07-02.md` (the binding rule forms + rails) and
  `REBUILD-Z-ORDER-2026-07-02.md` (the lap plan the operator fires).
