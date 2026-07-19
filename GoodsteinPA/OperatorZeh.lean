/-
# `OperatorZeh` — the `Zᵉ` operator-controlled calculus (REBUILD-Z lap 1)

The `Zeh` cut-elimination substrate, promoted from the judge-ratified spike
`wip/SpikeZ1Seams.lean` into `src/` per `REBUILD-Z-ORDER-2026-07-02.md` (Scope-A) and
`ZEH-STATEMENT-LOCK-2026-07-02.md`.  The calculus core (§0–§2), the structural layer
(`mono_H`, `ZehProv`), and the read-off exit (§3) are the LOCK §1 forms VERBATIM
(namespace change only, `SpikeZ1 → OperatorZeh`).

**SUPERSEDED (lap 8, ratified in `E-2026-07-02-JUDGE-rebuild-z-lap8-validation.md`):** the
`Zef` layer (§5/§7), `iterSlot` + the §5b lemmas, and old pin 3 (`cutElimPass_Zf`) are
superseded by `OperatorZef2.lean` (`Zef2`, the ewN-gated calculus). They remain here as frozen
evidence — statement tokens untouched.

Beyond the verbatim seed this module carries the lap-1 statement work:

* **§4 — the inversion suite (A3, PROVEN).**  `allInv_Zeh` (Z1 pin 1) is discharged as a
  real proof — the six-case induction mirroring the banked `Zekd.allInv`
  (`OperatorZinfty.lean:484`) with the numeric `max k n₀`/`d`-inert bookkeeping re-keyed to
  the stage `max m n₀` and the relativization `adjoin H n₀`.  `#print axioms` clean.
* **§5/§7 — the f-slot elimination suite (A2; pins 1–2 DISCHARGED lap 184, pin 3 `sorry`).**
  The Eguchi–Weiermann function-slot forms (LOCK §3): the running-family reduction
  `cutReduceAllAuxRunning_Zf` (pin 1) and the common-control step motive `stepAllω_Zf`
  (pin 2) are **real sorry-free theorems** in the function-slot judgment `Zef` (§7) — the
  slot `f : ℕ → ℕ` composed at principal cuts (output slot `g ∘ f`), max-relativized at
  ω-nodes (`rel1`), instantiated to `hardy e` at the root.  This required amending LOCK
  §1-A1/§3: the ℕ-stage judgment `Zeh` could not carry the reduction (kernel-refuted,
  `principal_witness_exceeds_stage`), so the R4-compliant slot judgment `Zef` replaces the
  ℕ-stage with the function-slot (RATIFIED lap 184,
  `REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`).  The collapse/iteration shape
  `cutElimPass_Zf` (pin 3) stays the lap-5 entrance gate — `sorry`, discharge FORBIDDEN.
* **§6 — the two Z1 seams RE-EXPRESSED in the f-form (A2, PROVEN).**  The Z1 seam probes
  re-run against the §5 statements: seam 1 (`seam1_f_absorbed_by_composition`) and seam 2
  (`seam2_f_slot_payable`) close as REAL proofs against the function-slot reduction shape —
  no sorried membership, no sorried slot.  If either failed here it would be T-R(i) (the
  E–W carrier failing where the ℕ-slots failed); it does not.

Standing rails honored (LOCK §2): no numeric fact routes through `H`-membership (R1);
existentials open at the root only (R2); `e` is constant through a derivation, control
changes at statement level (R3); numeric budgets are function-valued (R4); no new `axiom`
declarations (R5).
-/
module

public import GoodsteinPA.OperatorZinfty
public import GoodsteinPA.BlueprintAttr
public import GoodsteinPA.ToMathlib.FastGrowing.EWIteration
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## §0 The SPIKE-W4 transforms (LOCK §1 verbatim; `wip/` copies were re-derivations). -/

@[simp] theorem norm_expTower (α : ONote) : norm (expTower α) = max (norm α) 1 :=
  Zekd.norm_omegaPow

/-- SPIKE-W4's family-uniform control raise `raise e α := e + ω^α`. -/
def raise (e α : ONote) : ONote := e + expTower α

theorem raise_NF {e α : ONote} (he : e.NF) (hα : α.NF) : (raise e α).NF := by
  haveI := he; haveI := expTower_NF hα
  exact ONote.add_nf e (expTower α)

theorem raise_lt_raise {e β α : ONote} (he : e.NF) (hβ : β.NF) (hα : α.NF) (h : β < α) :
    raise e β < raise e α :=
  Zekd.add_lt_add_left_NF he (expTower_NF hβ) (expTower_NF hα) (expTower_lt_expTower hβ h)

/-- `ω·(m+1)` as an explicit `ONote` (the W4B two-level-configuration family). -/
def wmul (m : ℕ) : ONote := oadd 1 m.succPNat 0

theorem wmul_NF (m : ℕ) : (wmul m).NF := nf_one.oadd m.succPNat NFBelow.zero

@[simp] theorem norm_one : norm (1 : ONote) = 1 := rfl

@[simp] theorem norm_wmul (m : ℕ) : norm (wmul m) = m + 1 := by
  rw [wmul, norm_oadd, norm_one, norm_zero, Nat.succPNat_coe]
  omega

/-- Equal-exponent CNF merge, parametric (kernel-computed; W4B's rail brick). -/
theorem wmul_add_wmul (a b : ℕ) :
    wmul a + wmul b = oadd 1 (a.succPNat + b.succPNat) 0 := rfl

theorem one_lt_omegaO : (1 : ONote) < ONote.omega :=
  oadd_lt_oadd_1 nf_one ONote.zero_lt_one

theorem omegaO_NF : (ONote.omega).NF := nf_one.oadd 1 NFBelow.zero

theorem wmul_lt_expTower_omega (m : ℕ) : wmul m < expTower ONote.omega :=
  oadd_lt_oadd_1 (wmul_NF m) one_lt_omegaO

/-- Any `oadd 1 K 1`-shaped notation (an `osucc` of an `ω·K` notation) sits below `ω^ω`. -/
theorem osucc_omega_coeff_lt (K : ℕ+) : osucc (oadd 1 K 0) < expTower ONote.omega := by
  have h : (osucc (oadd 1 K 0)).NF := osucc_NF (nf_one.oadd K NFBelow.zero)
  rw [show osucc (oadd 1 K 0) = oadd 1 K 1 from rfl] at h ⊢
  exact oadd_lt_oadd_1 h one_lt_omegaO

theorem osucc_wmul_lt_expTower_omega (m : ℕ) : osucc (wmul m) < expTower ONote.omega :=
  osucc_omega_coeff_lt m.succPNat

/-! ## §1 The operator layer (LOCK §1 verbatim). -/

/-- The pin's closure conditions: closed under `+`, `ω^·` (`expTower`), `osucc`, `ofNat`. -/
structure IsOperator (H : ONote → Prop) : Prop where
  ofNat_mem : ∀ n : ℕ, H (ONote.ofNat n)
  add_mem : ∀ {α β : ONote}, H α → H β → H (α + β)
  expTower_mem : ∀ {α : ONote}, H α → H (expTower α)
  osucc_mem : ∀ {α : ONote}, H α → H (osucc α)

/-- Inductive closure of a generator set under the pin's four operations.  Membership
witnesses are finite trees — the "represented, countable" operator shape. -/
inductive Cl (S : ONote → Prop) : ONote → Prop
  | base {β : ONote} : S β → Cl S β
  | ofNat (n : ℕ) : Cl S (ONote.ofNat n)
  | add {α β : ONote} : Cl S α → Cl S β → Cl S (α + β)
  | expTower {α : ONote} : Cl S α → Cl S (expTower α)
  | osucc {α : ONote} : Cl S α → Cl S (osucc α)

/-- The closure of ANY generator set is an operator (the pin's conditions, verbatim). -/
theorem isOperator_Cl (S : ONote → Prop) : IsOperator (Cl S) where
  ofNat_mem := Cl.ofNat
  add_mem := Cl.add
  expTower_mem := Cl.expTower
  osucc_mem := Cl.osucc

/-- Closure is monotone in the generators (feeds `Zeh.mono_H`). -/
theorem Cl_mono {S S' : ONote → Prop} (h : ∀ β, S β → S' β) :
    ∀ {β : ONote}, Cl S β → Cl S' β := by
  intro β hβ
  induction hβ with
  | base hb => exact Cl.base (h _ hb)
  | ofNat n => exact Cl.ofNat n
  | add _ _ ih₁ ih₂ => exact Cl.add ih₁ ih₂
  | expTower _ ih => exact Cl.expTower ih
  | osucc _ ih => exact Cl.osucc ih

/-- `Cl` is the LEAST operator over its generators: closure membership maps into any
`IsOperator` set containing the generators (the bridge between the abstract-`H` and
generated-`H` formulations of the pin). -/
theorem Cl_sub_of_isOperator {S H : ONote → Prop} (hop : IsOperator H)
    (hSH : ∀ β, S β → H β) : ∀ {β : ONote}, Cl S β → H β := by
  intro β hβ
  induction hβ with
  | base hb => exact hSH _ hb
  | ofNat n => exact hop.ofNat_mem n
  | add _ _ ih₁ ih₂ => exact hop.add_mem ih₁ ih₂
  | expTower _ ih => exact hop.expTower_mem ih
  | osucc _ ih => exact hop.osucc_mem ih

/-- The relativization generator set: adjoin the branch numeral (the work order's
"`H[n]` is generation from `gen ∪ {ofNat n}`").  `Zeh.allω` runs premise `n` over it. -/
def adjoin (H : ONote → Prop) (n : ℕ) : ONote → Prop := fun β => H β ∨ β = ONote.ofNat n

/-- The relativized operator `H[n]`. -/
def relOp (H : ONote → Prop) (n : ℕ) : ONote → Prop := Cl (adjoin H n)

/-! ### The kernel findings (K1)–(K3): what set-membership can and cannot carry at `ε₀`. -/

/-- `ω^e·n` (zero tail) is in every closure, by `n`-fold equal-exponent merge of
`expTower e` (kernel-computed merges via `repr_inj`). -/
theorem oaddZero_mem {S : ONote → Prop} {ε : ONote} (hε : ε.NF) (hεS : Cl S ε) :
    ∀ n : ℕ+, Cl S (oadd ε n 0) := by
  have key : ∀ k : ℕ, Cl S (oadd ε k.succPNat 0) := by
    intro k
    induction k with
    | zero => exact Cl.expTower hεS
    | succ k ih =>
        have hNF : (oadd ε k.succPNat 0).NF := hε.oadd _ NFBelow.zero
        have hNF' : (expTower ε).NF := expTower_NF hε
        have hNF'' : (oadd ε (k + 1).succPNat 0).NF := hε.oadd _ NFBelow.zero
        haveI := hNF; haveI := hNF'; haveI := hNF''
        have hsum : oadd ε k.succPNat 0 + expTower ε = oadd ε (k + 1).succPNat 0 := by
          refine repr_inj.mp ?_
          rw [repr_add (oadd ε k.succPNat 0) (expTower ε)]
          simp only [expTower, ONote.repr, Nat.succPNat_coe, PNat.one_coe,
            Nat.cast_one, add_zero, mul_one]
          have hc : (((k + 1).succ : ℕ) : Ordinal) = ((k.succ : ℕ) : Ordinal) + 1 := by
            push_cast
            try rfl
          rw [hc, mul_add, mul_one]
        exact hsum ▸ Cl.add ih (Cl.expTower hεS)
  intro n
  have h := key n.natPred
  rwa [PNat.succPNat_natPred] at h

/-- **(K1) VACUITY.**  Every normal-form notation is in the closure of EVERY generator set:
at the `ε₀` level, all of the notation system is hereditarily generated from numerals by
`+` and `ω^·`.  Consequence: the pinned membership side conditions are uniformly
dischargeable (good for the seams) and carry NO numeric information (fatal for any
membership-based bound). -/
theorem Cl_of_NF {S : ONote → Prop} : ∀ {β : ONote}, β.NF → Cl S β := by
  intro β
  induction β with
  | zero =>
      intro _
      exact Cl.ofNat 0
  | oadd ε n a ihε iha =>
      intro h
      have hε : ε.NF := h.fst
      have ha : a.NF := h.snd
      have hhead : (oadd ε n 0).NF := hε.oadd n NFBelow.zero
      haveI := hhead; haveI := ha; haveI := h
      have hsplit : oadd ε n 0 + a = oadd ε n a := by
        refine repr_inj.mp ?_
        rw [repr_add (oadd ε n 0) a]
        simp [ONote.repr]
      exact hsplit ▸ Cl.add (oaddZero_mem hε (ihε hε) n) (iha ha)

/-- **(K2a)** The finite part of every closure is ALL of ℕ — so the pin's original `exI`
designation "some `m ∈ H ∩ ℕ`" designates nothing (amendment A1: the stage is
judgment-carried). -/
theorem finite_part_unbounded (S : ONote → Prop) : ∀ m : ℕ, Cl S (ONote.ofNat m) :=
  Cl.ofNat

/-- The pinned additive raise genuinely ABSORBS a numeral base (kernel-computed):
`raise (ofNat 5) 1 = ofNat 5 + ω = ω`. -/
theorem raise_absorbs_base : raise (ONote.ofNat 5) 1 = ONote.omega := rfl

/-- **(K2b) The membership-gated `mono_e` is kernel-refuted.**  There are `e < e'` (indeed
`e' = raise e 1`, the pin's own raise shape), both normal-form, both in EVERY closure, with
`hardy e' m < hardy e m`: `hardy ω 0 = 1 < 5 = hardy (ofNat 5) 0`.  So no `Zeh`-rule
package of (NF, `<`, membership) facts can re-establish the `exI` bound after a raise —
`Zekd.mono_e`'s numeric gate `norm e ≤ k + d` does NOT "become `e ∈ H`"; the domination
content must come from elsewhere (amendment A2 / the verdict's re-scoping). -/
theorem mono_e_membership_gate_refuted :
    ∃ (e e' : ONote) (m : ℕ), e.NF ∧ e'.NF ∧ e < e' ∧ e' = raise e 1 ∧
      (∀ S : ONote → Prop, Cl S e ∧ Cl S e') ∧ hardy e' m < hardy e m := by
  refine ⟨ONote.ofNat 5, ONote.omega, 0, ?_, omegaO_NF, ?_, rfl, ?_, ?_⟩
  · exact ONote.nf_ofNat 5
  · rw [lt_def, repr_ofNat]
    have h : (ONote.omega).repr = Ordinal.omega0 := by simp [ONote.omega, ONote.repr]
    rw [h]
    exact Ordinal.natCast_lt_omega0 5
  · intro S
    exact ⟨Cl.ofNat 5, Cl.expTower (Cl.ofNat 1)⟩
  · rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega, hardy_ofNat]
    omega

/-- **(K3)** No norm-ball is `+`-closed (equal-exponent merges are additive in the head
coefficient — W4B's rail).  So (K1) is not a representation artifact: no concrete `H` can
satisfy the pinned closure conditions AND certify a norm bound. -/
theorem norm_ball_not_add_closed (R : ℕ) (hR : 1 ≤ R) :
    ∃ α β : ONote, norm α ≤ R ∧ norm β ≤ R ∧ R < norm (α + β) := by
  refine ⟨wmul (R - 1), wmul (R - 1), by rw [norm_wmul]; omega, by rw [norm_wmul]; omega, ?_⟩
  rw [wmul_add_wmul, norm_oadd, norm_one, norm_zero]
  have : ((R - 1).succPNat + (R - 1).succPNat : ℕ+) = (2 * R : ℕ) := by
    simp [Nat.succPNat, PNat.add_coe]
    omega
  omega

/-! ## §2 The minimal `Zeh` core (LOCK §1 verbatim, amendment A1 folded in). -/
inductive Zeh : ONote → ONote → (ONote → Prop) → ℕ → ℕ → Finset (ArithmeticFormula ℕ) → Prop
  | axL {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {ar : ℕ}
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zeh α e H m c Γ
  | wk {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hsub : Δ ⊆ Γ) (dd : Zeh α e H m c Δ) : Zeh α e H m c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zeh β e H m c Δ) : Zeh α e H m c Γ
  | allω {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c (insert (φ/[nm n]) Γ)) :
      Zeh α e H m c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ hardy e m)
      (dd : Zeh β e H m c (insert (φ/[nm n]) Γ)) : Zeh α e H m c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticFormula ℕ) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zeh βφ e H m c (insert φ Γ)) (d₂ : Zeh βψ e H m c (insert (∼φ) Γ)) :
      Zeh α e H m c Γ

namespace Zeh

/-- **`mono_H` — the pin's replacement for `mono_k`/`mono_d`** (a REAL proof): raise the
generator set and the stage together.  The `exI` bound rides `hardy_monotone` (argument
monotonicity — no ordinal-raise, hence no gate); memberships ride `Cl_mono`. -/
theorem mono_H : ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zeh α e H m c Γ → ∀ {H' : ONote → Prop} {m' : ℕ},
    (∀ β, H β → H' β) → m ≤ m' → Zeh α e H' m' c Γ := by
  intro α e H m c Γ dd
  induction dd with
  | axL r v hp hn => intro H' m' _ _; exact Zeh.axL r v hp hn
  | wk hsub _ ih => intro H' m' hH hm; exact Zeh.wk hsub (ih hH hm)
  | weak hβ hβNF hαNF hβH hsub _ ih =>
      intro H' m' hH hm
      exact Zeh.weak hβ hβNF hαNF (Cl_mono hH hβH) hsub (ih hH hm)
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      intro H' m' hH hm
      refine Zeh.allω φ β hβ hβNF hαNF
        (fun n => Cl_mono (fun γ hγ => hγ.imp_left (hH γ)) (hβH n))
        (fun n => ih n (fun γ hγ => hγ.imp_left (hH γ)) (max_le_max hm (le_refl n)))
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro H' m' hH hm
      exact Zeh.exI φ n hβ hβNF hαNF (Cl_mono hH hβH)
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hH hm)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro H' m' hH hm
      exact Zeh.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (Cl_mono hH hβφH) (Cl_mono hH hβψH)
        (ih₁ hH hm) (ih₂ hH hm)

/-- Sequent weakening (height-preserving). -/
theorem weakening {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
    (hsub : Δ ⊆ Γ) (dd : Zeh α e H m c Δ) : Zeh α e H m c Γ :=
  Zeh.wk hsub dd

/-- **Operator irrelevance (R1 realized in-kernel):** the generator slot `H` carries NO
information — every `Cl H β` side condition in a `Zeh` derivation is at an NF ordinal, and
`Cl_of_NF` supplies membership in the closure of ANY generator set.  So a derivation at
operator `H` is a derivation at any operator `H'`, SAME `(α, e, m, c, Γ)`.  This is the
strong form of `mono_H` that `mono_H` (which needs `H ⊆ H'`) cannot express: the operator is
freely replaceable in BOTH directions.  Discharges the operator-threading bookkeeping in the
§5 reductions — the running relativization `adjoin H n` of the inversion family and the ambient
`H` of the ∃-side are interchangeable at will (rail R1: membership is bookkeeping only). -/
theorem change_H : ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zeh α e H m c Γ → ∀ {H' : ONote → Prop}, Zeh α e H' m c Γ := by
  intro α e H m c Γ dd
  induction dd with
  | axL r v hp hn => intro H'; exact Zeh.axL r v hp hn
  | wk hsub _ ih => intro H'; exact Zeh.wk hsub (ih)
  | weak hβ hβNF hαNF _ hsub _ ih => intro H'; exact Zeh.weak hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | allω φ β hβ hβNF hαNF _ _ ih =>
      intro H'
      exact Zeh.allω φ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI φ n hβ hβNF hαNF _ hbound _ ih =>
      intro H'; exact Zeh.exI φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'; exact Zeh.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

end Zeh

/-- The `≤`-slack bookkeeping wrapper (`ZekdProv`'s twin with the NORM clause deleted —
the simplification the fork buys — and the ordinal's `Cl H`-membership carried instead:
"the judgment carries `α ∈ H` directly"). -/
def ZehProv (α e : ONote) (H : ONote → Prop) (m c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Zeh α' e H m c Γ

namespace ZehProv

theorem of {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hNF : α.NF) (hH : Cl H α) (D : Zeh α e H m c Γ) : ZehProv α e H m c Γ :=
  ⟨α, le_refl _, hNF, hH, D⟩

theorem mono {α β e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hα : α ≤ β) : ZehProv α e H m c Γ → ZehProv β e H m c Γ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, D⟩

theorem weakening {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ Δ : Finset (ArithmeticFormula ℕ)} (h : Γ ⊆ Δ) :
    ZehProv α e H m c Γ → ZehProv α e H m c Δ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', hα', hNF, hH, D.wk h⟩

end ZehProv

/-! ## §3 The bounding read-off — the exit (LOCK §4/§1 verbatim, PROVEN). -/

/-- Sequent shape for the read-off: every member is the target `∃⁰ φ`, an already-bounded
instance of `φ`, or a literal.  (BW87's "positive Σ₁(N)" restriction: ∀-free.) -/
def ReadoffShape (φ : ArithmeticSemiformula ℕ 1) (e : ONote) (m : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ (∃ n ≤ hardy e m, ψ = φ/[nm n]) ∨
    (∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- Read-off conclusion: a bounded true instance of the target, or a true literal
somewhere in the sequent (the escape BW87's Bounding Lemma also carries). -/
def ReadoffGoal (φ : ArithmeticSemiformula ℕ 1) (e : ONote) (m : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  (∃ n ≤ hardy e m, atomTrue (φ/[nm n])) ∨
    (∃ ψ ∈ Γ, atomTrue ψ ∧
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- **The bounding read-off (Q2), PROVEN — the Buchholz–Wainer Bounding-Lemma analog.**
From a rank-0 (cut-free) `Zeh` derivation of a `ReadoffShape` sequent whose target matrix
has atomic instances: a witness `n ≤ hardy e m` with `φ/[nm n]` true, or a true literal in
the sequent.  The bound consumes ONLY the judgment's control `e` and stage `m`. -/
theorem readoff_sigma1 {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v) :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
      Zeh α e H m c Γ → c = 0 → ReadoffShape φ e m Γ → ReadoffGoal φ e m Γ := by
  intro α e H m c Γ dd
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      intro _ _
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact Or.inr ⟨_, hp, htrue, ar, r, v, Or.inl rfl⟩
      · refine Or.inr ⟨_, hn, ?_, ar, r, v, Or.inr rfl⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H m c Δ Γ hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @allω α e H m c Γ χ β hβ hβNF hαNF hβH _ _ =>
      intro _ hshape
      rcases hshape (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n, _, h⟩ | ⟨ar, r, v, h | h⟩
      · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
      · obtain ⟨ar, r, v, hrel⟩ := hφinst n
        rw [hrel] at h
        exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | @exI α β e H m c Γ χ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc hshape
      have hχφ : χ = φ := by
        rcases hshape (∃⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n', _, h⟩ | ⟨ar, r, v, h | h⟩
        · simpa [ExsQuantifier.exs] using h
        · obtain ⟨ar, r, v, hrel⟩ := hφinst n'
          rw [hrel] at h
          exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
      have hφχ : φ = χ := hχφ.symm
      subst hφχ
      have hshape' : ReadoffShape φ e m (insert (φ/[nm n]) Γ) := by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inr (Or.inl ⟨n, hbound, rfl⟩)
        · exact hshape ψ (Finset.mem_insert_of_mem hψΓ)
      rcases ih hc hshape' with h | ⟨ψ, hψ, htrue, hlit⟩
      · exact Or.inl h
      · rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inl ⟨n, hbound, htrue⟩
        · exact Or.inr ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue, hlit⟩
  | @cut α βφ βψ e H m c Γ χ hcompl _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc _
      exact absurd hcompl (by omega)

/-- **The headline-instantiation read-off** — the W5/M2-exit shape: a rank-0 `Zeh` root
deriving the single per-instance Σ₁ sequent `{∃⁰ φ}` (atomic matrix) yields a numeric
witness `≤ hardy e m`. -/
theorem headline_readoff {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    {α e : ONote} {H : ONote → Prop} {m : ℕ}
    (dd : Zeh α e H m 0 {(∃⁰ φ)}) :
    ∃ n ≤ hardy e m, atomTrue (φ/[nm n]) := by
  have hshape : ReadoffShape φ e m {(∃⁰ φ)} := by
    intro ψ hψ
    rw [Finset.mem_singleton] at hψ
    exact Or.inl hψ
  rcases readoff_sigma1 hφinst dd rfl hshape with h | ⟨ψ, hψ, _, ⟨ar, r, v, hlit⟩⟩
  · exact h
  · rw [Finset.mem_singleton] at hψ
    subst hψ
    rcases hlit with h | h <;> exact absurd h (by simp [ExsQuantifier.exs])

/-- **Concrete kernel instance of the read-off**: a two-node derivation — `exI` at witness
`3` over an `axL` leaf — at control `ω` and stage `1`; the rule's bound is
`3 ≤ hardy ω 1 = 3`, kernel-computed exactly (`hardy_omega`). -/
theorem concrete_readoff_instance {ar : ℕ} (r : (ℒₒᵣ).Rel ar)
    (v : Fin ar → ArithmeticTerm ℕ) (φ : ArithmeticSemiformula ℕ 1)
    {H : ONote → Prop} :
    Zeh (osucc 0) ONote.omega H 1 0
      (insert (∃⁰ φ) (insert (Semiformula.rel r v) {Semiformula.nrel r v})) := by
  refine Zeh.exI φ 3 (Zekd.lt_osucc NF.zero) NF.zero (osucc_NF NF.zero)
    (Cl.ofNat 0) (by rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]) ?_
  exact Zeh.axL r v
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

/-- The concrete stage/control bound of the instance, kernel-computed: `hardy ω 1 = 3`. -/
theorem concrete_bound_computes : hardy ONote.omega 1 = 3 := by
  rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]

/-! ## §4 The inversion suite (A3 — Z1 pin 1 DISCHARGED)

`allInv_Zeh` was the first disclosed Z1 statement pin; here it is a REAL proof, the
six-case induction mirroring the banked `Zekd.allInv` (`OperatorZinfty.lean:484`) with the
numeric `max k n₀`/`d`-inert bookkeeping re-keyed to the stage axis `max m n₀` and the
relativization axis `adjoin H n₀`.  Since the minimal `Zeh` core has only the six mandated
constructors (no `andI`/`orI`/`verumR`/`trueRel`/`trueNrel`), the induction is strictly
shorter than `Zekd`'s — the only genuinely new bookkeeping is that inverting under an
`allω`/`exI` sub-derivation adjoins `n₀` on TOP of the branch relativization, which the
`adjoin` reassociation lemmas below absorb (they are the operator-side analog of `Zekd`'s
`max`-reshuffle `max (max k n₀) n = max (max k n) n₀`). -/

/-- The relativization only grows the operator (feeds every `Cl_mono`/`mono_H` re-key). -/
theorem adjoin_le (H : ONote → Prop) (n : ℕ) : ∀ γ, H γ → adjoin H n γ :=
  fun _ h => Or.inl h

/-- Adjoining a fresh numeral commutes past an inner relativization (the operator-side
analog of `max (max k a) b = max (max k b) a`; feeds the non-principal `allω` re-key). -/
theorem adjoin_swap (H : ONote → Prop) (a b : ℕ) :
    ∀ γ, adjoin (adjoin H a) b γ → adjoin (adjoin H b) a γ := by
  rintro γ ((hg | rfl) | rfl)
  · exact Or.inl (Or.inl hg)
  · exact Or.inr rfl
  · exact Or.inl (Or.inr rfl)

/-- Adjoining the SAME numeral twice collapses (the operator-side analog of
`max (max k n₀) n₀ = max k n₀`; feeds the principal `allω` re-key). -/
theorem adjoin_idem (H : ONote → Prop) (n : ℕ) :
    ∀ γ, adjoin (adjoin H n) n γ → adjoin H n γ := by
  rintro γ ((hg | rfl) | rfl)
  · exact Or.inl hg
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- Relativization is monotone in the base operator (feeds the non-principal `allω`
side-condition re-key `relOp H n → relOp (adjoin H n₀) n`). -/
theorem adjoin_base_mono {H H' : ONote → Prop} (n : ℕ) (h : ∀ γ, H γ → H' γ) :
    ∀ γ, adjoin H n γ → adjoin H' n γ := by
  rintro γ (hg | rfl)
  · exact Or.inl (h _ hg)
  · exact Or.inr rfl

/-! ### Finset push/pull helpers for the inversion (re-derivations of the `private`
`OperatorZinfty` copies — calculus-independent). -/

theorem inv1Push (A e b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert b s).erase A) ⊆ insert b (insert e (s.erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

theorem inv1Pull (A e : ArithmeticFormula ℕ) {b : ArithmeticFormula ℕ} (h : b ≠ A)
    (s : Finset (ArithmeticFormula ℕ)) :
    insert b (insert e (s.erase A)) ⊆ insert e ((insert b s).erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | hx
  · exact Or.inr ⟨h, Or.inl rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hx.1, Or.inr hx.2⟩

theorem princAllSub (A e : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ)) :
    insert e ((insert e s).erase A) ⊆ insert e (s.erase A) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

/-- **PIN 1 DISCHARGED — ∀-inversion, `Zeh` form** (was the disclosed Z1 statement pin,
now a real proof).  The extracted instance runs at the relativization `adjoin H n₀` and the
raised stage `max m n₀`. -/
theorem allInv_Zeh {φ₀ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ) :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
      Zeh α e H m c Γ → (∀⁰ φ₀) ∈ Γ →
      Zeh α e (adjoin H n₀) (max m n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  intro α e H m c Γ dd
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      intro _
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H m c Δ Γ hsub dd ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.wk ?_ (Zeh.mono_H dd (adjoin_le H n₀) (le_max_left m n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF (Cl_mono (adjoin_le H n₀) hβH)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.weak hβ hβNF hαNF (Cl_mono (adjoin_le H n₀) hβH) ?_
          (Zeh.mono_H dd (adjoin_le H n₀) (le_max_left m n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmem
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · -- PRINCIPAL: specialize branch n₀ (already at `adjoin H n₀`, `max m n₀`)
        obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · -- the tail still carries a ∀⁰χ: invert it out of branch n₀ recursively
          have h := ih n₀ (Finset.mem_insert_of_mem hh)
          have h2 : Zeh (β n₀) e (adjoin H n₀) (max m n₀) c
              (insert (χ/[nm n₀]) ((insert (χ/[nm n₀]) Γ₀).erase (∀⁰ χ))) :=
            Zeh.mono_H h (adjoin_idem H n₀) (le_of_eq (by omega))
          exact Zeh.weak (hβ n₀) (hβNF n₀) hαNF (hβH n₀) (princAllSub (∀⁰ χ) _ Γ₀) h2
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zeh.weak (hβ n₀) (hβNF n₀) hαNF (hβH n₀) (Finset.Subset.refl _) (dd n₀)
      · -- NON-PRINCIPAL: rebuild the `allω`, adjoining `n₀` on top of each branch relativization
        have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zeh (β n) e (adjoin (adjoin H n₀) n) (max (max m n₀) n) c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := ih n (Finset.mem_insert_of_mem hmem0)
          exact Zeh.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀)
            (Zeh.mono_H h (adjoin_swap H n n₀) (le_of_eq (by omega)))
        exact Zeh.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zeh.allω χ β hβ hβNF hαNF
            (fun n => Cl_mono (adjoin_base_mono n (adjoin_le H n₀)) (hβH n)) key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zeh.exI χ n hβ hβNF hαNF (Cl_mono (adjoin_le H n₀) hβH)
          (le_trans hbound (hardy_monotone _ (le_max_left m n₀))) P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zeh.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_mono (adjoin_le H n₀) hβφH) (Cl_mono (adjoin_le H n₀) hβψH) P₁ P₂

/-- `ω·(n+1)` is a member of every closure — by an `n`-sized tree of equal-exponent merges
(the seam-2 reversal brick; feeds `probe_allomega_reassembly_Zf`). -/
theorem wmul_mem (S : ONote → Prop) (n : ℕ) : Cl S (wmul n) := by
  induction n with
  | zero => exact Cl.expTower (Cl.ofNat 1)
  | succ n ih =>
      have h : wmul n + wmul 0 = wmul (n + 1) := rfl
      exact h ▸ Cl.add ih (Cl.expTower (Cl.ofNat 1))

/-! ## §5 The f-slot elimination suite (A2 — LOCK §3/§6; pins 1–2 DISCHARGED in §7, pin 3 `sorry`)

The Eguchi–Weiermann number-theoretic operator slot `f : ℕ → ℕ` (arXiv:1205.2879, Def. 23 +
Lemma 25) is what the `(k,d)` counter could never be (SPIKE-W4B: both seams are ℕ-slot
overflow failures; SPIKE-Z1 §6: the non-affine function-slot absorbs both).

**LOCK §1-A1/§3 amendment (RATIFIED lap 184, `REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`):** the
draft kept the ℕ-stage judgment `Zeh` f-free with the slot only in the elimination *statements*,
but laps 2–3 proved in-kernel that the ℕ-stage `Zeh` **cannot** carry the running-family reduction
(`principal_witness_exceeds_stage`: the `exI` witness `n ≤ hardy e m > m` cannot be lowered to the
output stage — the exact ℕ-budget failure LOCK R4 forbids).  The fix is the R4-compliant
function-slot judgment `Zef` (§7): the ℕ-stage `m` is replaced by the slot `f`.  Pins 1–2
(`cutReduceAllAuxRunning_Zf`, `stepAllω_Zf`) are DISCHARGED there as real theorems.  The f-slot
enters the elimination lemmas as:

* **composition at principal cuts** — the reduction's output slot is `f ∘ g` of the premises';
* **max-relativization at ω-nodes** — `rel1 f n = fun x => f (max n x)`;
* **`hardy e` at the root** — `NormControlled` collapses to `hardy e` when `m = 0`.

These signatures are the lap-1 draft as **JUDGE-AMENDED** (2026-07-02,
`E-2026-07-02-JUDGE-rebuild-z-lap1-validation.md`, ratifying the lap-176 finding
`REBUILD-Z-LAP1-FINDING-2026-07-02-fslot-control-raise.md` — Option A, kernel-forced):
the reduction/step statements stay at **FIXED control** with the composed slot (E–W
Lemma 25 — the raised-control conjunct of the original draft was refutable two independent
ways: the K2b re-tag failure, and an `axL`-instantiation making the conjunct falsifiable
outright).  ALL ordinal COLLAPSE and numeric ITERATION is confined to `cutElimPass_Zf`
(E–W Lemma 27/30); per the lap-5 restatement (C1) the control `e` is UNTOUCHED — the ordinal
collapses (`collapse α`) and the slot iterates (`iterSlot f α`), where the P1 domination obligation
is paid by the pinned iterate — not by composition, not by a raised control.  Pins 1–2 are
DISCHARGED (§7, slot judgment `Zef`); pin 3 `cutElimPass_Zf` stays `sorry` (lap-5 entrance gate,
discharge FORBIDDEN). -/

/-- **Norm control** (the E–W "number-theoretic operator" bound, tied to the `(e, m)` axis):
`f` dominates the Hardy witness bound at every relativization depth.  `hardy e` is the root
instantiation (`normControlled_root`); the ω-node re-entry is `normControlled_rel1`. -/
def NormControlled (f : ℕ → ℕ) (e : ONote) (m : ℕ) : Prop :=
  ∀ x, hardy e (max m x) ≤ f x

/-- **Root instantiation** (LOCK §3, third bullet): `hardy e` controls the stage-0 axis. -/
theorem normControlled_root (e : ONote) : NormControlled (fun x => hardy e x) e 0 := by
  intro x; simp

/-- **Seam 2 in controlled form — the ω-node re-entry** (real proof): a controlled slot,
relativized at branch `n` and run at the max-adjoined stage, is controlled by `rel1 f n`.
This is `rel1_comp`'s semantic payload: the branch-unbounded demand that overflowed every
`Zekd` `d`-slot re-enters through ONE function slot's relativization. -/
theorem normControlled_rel1 {f : ℕ → ℕ} {e : ONote} {m : ℕ} (h : NormControlled f e m)
    (n : ℕ) : NormControlled (rel1 f n) e (max m n) := by
  intro x
  have hx := h (max n x)
  have he : max m (max n x) = max (max m n) x := by omega
  rw [he] at hx
  simpa [rel1] using hx

/-- Norm control is monotone in the slot (assembly plumbing: a dominating slot still
controls; reused when a reduction outputs a larger-than-needed composed slot). -/
theorem NormControlled.mono {f f' : ℕ → ℕ} {e : ONote} {m : ℕ}
    (h : NormControlled f e m) (hff' : ∀ x, f x ≤ f' x) : NormControlled f' e m :=
  fun x => le_trans (h x) (hff' x)

/-- Norm control is antitone in the stage: a slot controlling stage `m` controls any
smaller stage `m' ≤ m` (the `exI` bound only shrinks).  Reused when the reduction runs a
premise at a lower stage than the conclusion. -/
theorem NormControlled.stage_antitone {f : ℕ → ℕ} {e : ONote} {m m' : ℕ}
    (h : NormControlled f e m) (hm : m' ≤ m) : NormControlled f e m' :=
  fun x => le_trans (hardy_monotone e (by omega)) (h x)

/-- **Composition preserves control at a FIXED control** (E–W Lemma 25's numeric update,
`f ↦ f∘g`, at the *same* control — the faithful reduction shape per the lap-176 finding
`REBUILD-Z-LAP1-FINDING-2026-07-02-fslot-control-raise.md`, Option A).  If `g` controls `e`
at `m` and `f` is inflationary (E–W condition `(f.1)`: `2y+1 ≤ f y ⟹ y ≤ f y`), then the
composed slot `f ∘ g` still controls `e` at `m`.  This is the banked plumbing that discharges
the reduction conjunct `NormControlled (f∘g) e m` once the raise is confined to the
elimination pass — VALIDATING the lap-176 claim that Option A's reduction discharge is
near-immediate.  Note: this is the *fixed*-control fact (K2b-benign); the *raised*-control
demand belongs to `cutElimPass_Zf`'s pinned iterate, NOT here. -/
theorem NormControlled.comp {f g : ℕ → ℕ} {e : ONote} {m : ℕ}
    (hg : NormControlled g e m) (hf : ∀ y, y ≤ f y) : NormControlled (f ∘ g) e m :=
  fun x => le_trans (hg x) (hf (g x))

/-- **The reduction's composed-slot conjunct, DISCHARGED** (the `NormControlled (f∘g) e m` half
of pins 1–2, at FIXED control — Option A).  From `g` controlled at ANY stage `m₀` and `f`
controlled at the output stage `m`, the composed slot `f ∘ g` is controlled at `m`.  Unlike
`NormControlled.comp` this needs NO separate inflationarity hypothesis on `f`: control of `g`
already forces `g` inflationary (`x ≤ max m₀ x ≤ hardy e (max m₀ x) ≤ g x`, via `le_hardy`), and
then `f (g x) ≥ hardy e (max m (g x)) ≥ hardy e (max m x)` (`hf` at `g x`, `hardy_monotone`).
This is the kernel proof behind the judge's Q1 ruling ("discharge near-immediate via the banked
`NormControlled.comp` + hardy-inflationarity") — it does NOT touch the derivation, so it splits
cleanly off the reduction pins' second conjunct. -/
theorem normControlled_comp_running {f g : ℕ → ℕ} {e : ONote} {m₀ m : ℕ}
    (hg : NormControlled g e m₀) (hf : NormControlled f e m) : NormControlled (f ∘ g) e m := by
  intro x
  have hxg : x ≤ g x :=
    le_trans (le_trans (le_max_right m₀ x) (le_hardy e (max m₀ x))) (hg x)
  exact le_trans (hardy_monotone e (max_le_max (le_refl m) hxg)) (hf (g x))

/-- **The bare `∃`-slot is VACUOUS** (kernel-backing for the lap-176 companion finding
`REBUILD-Z-LAP1-FINDING-2026-07-02-fslot-control-raise.md`, Q2; banked lap 177 as permitted
sibling infrastructure — the `NormControlled.comp` precedent: a fact about the stable
`NormControlled` def, consuming no f-slot pin, touching no gated body).  For ANY control `e`
and stage `m`, `∃ f, NormControlled f e m` holds trivially — the Hardy witness itself is a
slot.  Consequence: the retired draft's conjunct `∃ f', NormControlled f' (raise e α') m` added
NO quantitative content, so the read-off (E–W Lemma 31, `witness ≤ f(0)`) forces `f'` to be
PINNED to the E–W iterate of the input `f`, not left existential.  This is why the lap-5 pin-3
restatement (`cutElimPass_Zf`, §7b) outputs `iterSlot f α`, NOT `∃ f'`.  This LEMMA machine-checks
the vacuity the Q2 ruling rests on. -/
theorem normControlled_exists_trivial (e : ONote) (m : ℕ) :
    ∃ f : ℕ → ℕ, NormControlled f e m :=
  ⟨fun x => hardy e (max m x), fun _ => le_rfl⟩

/-- **Kernel witness for the stage-`m` reduction gap (the candidate sixth-trap root, now the
LOCK §1-A1 obstruction).**  The former stage-`m` reduction `redDeriv` (deleted lap 184) had a
principal-`exI` case where the witness satisfies only `n ≤ hardy e m`, which STRICTLY exceeds the
principal `exI` case the witness satisfies only `n ≤ hardy e m`, which STRICTLY exceeds the
stage `m` at any nontrivial control — e.g. `hardy ω m = 2m+1 > m`.  So `n ≤ hardy e m` does
NOT give `n ≤ m`, and the family member `fam n` (stage `max m₀ n`) cannot be lowered to the
output stage `m` (`Zeh` has no stage-lowering rule; LOCK §1 A1).  This is the reduction-stage
analog of the judge's fifth-trap kernel fact `hardy ω 0 = 1 > 0`. -/
theorem principal_witness_exceeds_stage (m : ℕ) : m < hardy ONote.omega m := by
  rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]; omega


/-! ## The numeric-slot ITERATE bricks (E–W Def 16 carriers; ported from `wip/ZefCutElim.lean`)

`Function.iterate` (`f^[k]`) is the `k`-fold composition; it preserves exactly the operator
conditions the reduction threads (monotone, inflationary, `NormControlled`) and composes to
iterates (`iter_comp`: counts ADD — the `∃`-cut lane).  These are the numeric carrier the pin-3
restatement's output slot (`iterSlot`, below) is built on.  All sorry-free — the ported bricks
were `#print axioms`-clean in `wip/ZefCutElim.lean`. -/

/-- The iterate is monotone if `f` is. -/
theorem iter_monotone {f : ℕ → ℕ} (hf : Monotone f) : ∀ k, Monotone f^[k]
  | 0 => monotone_id
  | k + 1 => by rw [Function.iterate_succ]; exact (iter_monotone hf k).comp hf

/-- The iterate is inflationary if `f` is. -/
theorem iter_infl {f : ℕ → ℕ} (hf : ∀ x, x ≤ f x) : ∀ k x, x ≤ f^[k] x
  | 0, x => le_rfl
  | k + 1, x => by
      rw [Function.iterate_succ']
      exact le_trans (iter_infl hf k x) (hf _)

/-- The iterate preserves `NormControlled` (for `k ≥ 1`): `f^[k+1] x ≥ f x ≥ hardy e (max m x)`,
via `f^[k]` inflationary. -/
theorem iter_normControlled {f : ℕ → ℕ} {e : ONote} {m : ℕ}
    (hf : NormControlled f e m) (hf_infl : ∀ x, x ≤ f x) (k : ℕ) :
    NormControlled f^[k + 1] e m := by
  intro x
  rw [Function.iterate_succ, Function.comp_apply]
  exact le_trans (hf x) (iter_infl hf_infl k (f x))

/-- Iterate monotone in the index count: `f^[j] ≤ f^[k]` pointwise for `j ≤ k`, `f` inflationary +
monotone.  Feeds `mono_f` when a pass outputs a longer iterate than a sibling branch needs. -/
theorem iter_le_of_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    {j k : ℕ} (hjk : j ≤ k) : ∀ x, f^[j] x ≤ f^[k] x := by
  intro x
  obtain ⟨d, rfl⟩ := Nat.le.dest hjk
  rw [Function.iterate_add_apply]
  exact iter_monotone hf_mono j (iter_infl hf_infl d x)

/-- **Iterates compose to iterates** (`f^[j] ∘ f^[k] = f^[j+k]`) — the numeric core of the
`∃`-cut lane: composing two premise iterates of the SAME base ADDS the counts, so the slot stays
`f^[·]`.  This is why pin 3's `f'` is a *pinned* iterate (Q2), not a free slot. -/
theorem iter_comp (f : ℕ → ℕ) (j k : ℕ) : f^[j] ∘ f^[k] = f^[j + k] :=
  (Function.iterate_add f j k).symm

/-! ## §5b The collapse + ordinal-indexed iterate — pin-3's restatement carriers (LOCK Addendum 2,
C2/C5; **iterate AMENDED by the lap-5 judge pass — SEVENTH statement trap**)

Pin 3 relates a rank-`c+1` derivation to a rank-`c` one by COLLAPSING the ordinal and ITERATING the
slot.  Two explicit ONote-grounded definitions:

- `collapse α := ω^α` (`expTower`) — E–W Lemma 27's Ω-free predicative shadow `φ 0 β = ω^β` for one
  rank step; iterated `c` times it is the rank-lowering tower `Ω_c(α) = Ω^{Ω_{c-1}(α)}`
  (paper §5, `arai`-style tower).  NF-preserving + strictly monotone (the descent the collapse
  induction needs) — both proven below (C5), reusing `expTower_NF`/`expTower_lt_expTower`.
- `iterSlot f α` — the **diagonalizing** ordinal-indexed iterate (E–W Def 16's `f^α`; Lemma 19's
  `F^α(0)` is a TRANSFINITE iterate, not a syntactic count).  Defined by the same
  fundamental-sequence recursion as the repo's `hardy` (which is exactly the successor's
  `iterSlot`): base `iterSlot f 0 = f`, successor `iterSlot f (a+1) n = iterSlot f a (f n)`,
  limit `iterSlot f λ n = iterSlot f (λ[n]) n`.  On finite ordinals it agrees with the retired
  count form (`iterSlot f (ofNat k) = f^[k+1]`); at limits it DIAGONALIZES — the branch index
  rides the numeric argument, which `rel1` raises (`rel1 (iterSlot f α) n` evaluates the ordinal
  index at `α[max n x]`-stages, absorbing branch-growing budgets).

**⚠️ SEVENTH STATEMENT TRAP (caught by the lap-5 judge pass; kernel evidence
`wip/JudgeTrap7Probe.lean`).**  The lap-5 draft's fixed-count form
`iterSlot f α := f^[norm α + 1]` is refuted at the `allω` reassembly: the pass's induction hands
branch `n` its output at slot `(rel1 f n)^[norm (β n) + 1]`, while the pin's conclusion forces the
parent's branch slot `rel1 (f^[norm α + 1]) n`; `Zef.mono_f` only RAISES slots, so reassembly needs
`(rel1 f n)^[norm (β n) + 1] ≤ rel1 (f^[norm α + 1]) n` pointwise.  Kernel counterexample at
`α = ω`, `β 2 = ofNat 2`, `f = hardy ω`, `x = 0`: parent side `f^[2] 2 = 11 < 23 = (rel1 f 2)^[3] 0`.
Root cause: `norm` is not monotone along `<` (`norm (ofNat n) = n` grows along ω's fundamental
sequence while `norm ω = 1`), so NO fixed ℕ-count read off the parent ordinal dominates the
branches — the diagonalization is forced.  (The box's lap-5 docstring mis-read its own statement:
it described branch slots as `rel1 (iterSlot f (β n)) n`, but the conclusion's slot parameter puts
`iterSlot f α` — the branch ordinal never enters the branch slot.) -/

/-- **`iterSlot`** — the diagonalizing ordinal-indexed numeric-slot iterate (E–W Def 16's `f^α` /
Lemma 19's `F^α(0)`): `iterSlot f 0 = f`; `iterSlot f (a+1) n = iterSlot f a (f n)`;
`iterSlot f λ n = iterSlot f (λ[n]) n` (limit, via `ONote.fundamentalSequence`).  Same well-founded
recursion as `hardy`; `hardy` is `iterSlot` of the successor, up to the base case. -/
def iterSlot (f : ℕ → ℕ) : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => f
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; exact Order.lt_succ _
      fun n => iterSlot f a (f n)
    | Sum.inr fs, h => fun n =>
      have : fs n < o := (h.2.1 n).2.1
      iterSlot f (fs n) n
  termination_by o => o

/-- Unfolding lemma for `iterSlot`, mirroring `hardy_def`. -/
theorem iterSlot_def (f : ℕ → ℕ) {o : ONote} {x} (e : fundamentalSequence o = x) :
    iterSlot f o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => f
      | Sum.inl (some a), _ => fun n => iterSlot f a (f n)
      | Sum.inr fs, _ => fun n => iterSlot f (fs n) n := by
  subst x
  rw [iterSlot]

/-- `iterSlot f o = f` when `o = 0` (the `inl none` branch). -/
theorem iterSlot_zero' (f : ℕ → ℕ) (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    iterSlot f o = f := by
  rw [iterSlot_def f h]

/-- `iterSlot f o n = iterSlot f a (f n)` when `o` is the successor of `a`. -/
theorem iterSlot_succ (f : ℕ → ℕ) (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    iterSlot f o = fun n => iterSlot f a (f n) := by
  rw [iterSlot_def f h]

/-- `iterSlot f o n = iterSlot f (o[n]) n` when `o` is a limit with fundamental sequence `fs`. -/
theorem iterSlot_limit (f : ℕ → ℕ) (o) {fs} (h : fundamentalSequence o = Sum.inr fs) :
    iterSlot f o = fun n => iterSlot f (fs n) n := by
  rw [iterSlot_def f h]

/-- **C5: `iterSlot f α` is inflationary** if `f` is (slot stays inflationary through the pass).
Mirrors `le_hardy`. -/
theorem iterSlot_infl {f : ℕ → ℕ} (hf_infl : ∀ x, x ≤ f x) (o : ONote) (n : ℕ) :
    n ≤ iterSlot f o n := by
  rcases e : fundamentalSequence o with (_ | a) | fs
  · rw [iterSlot_zero' f o e]; exact hf_infl n
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [iterSlot_succ f o e]
    exact le_trans (hf_infl n) (iterSlot_infl hf_infl a (f n))
  · have hlt : fs n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [iterSlot_limit f o e]
    exact iterSlot_infl hf_infl (fs n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Value transfer for `iterSlot`** (mirror of `hardy_le_of_reaches`, base `f`).  If `β`
structurally reaches `α` at budget `x`, and *every* notation `β` reaches has a monotone slot
iterate, then `iterSlot f α x ≤ iterSlot f β x`.  Unlike the fast-growing transfer, the successor
step `iterSlot f β x = iterSlot f γ (f x)` shifts the argument from `x` to `f x`; that shift is
absorbed by inflationarity (`x ≤ f x`, `hf_infl`) plus monotonicity of the intermediate
`iterSlot f γ` — the exact analog of `hardy_le_of_reaches`'s `Nat.le_succ` absorption. -/
theorem iterSlot_le_of_reaches {f : ℕ → ℕ} (hf_infl : ∀ x, x ≤ f x) {x : ℕ} {β α : ONote}
    (h : Reaches x β α) :
    (∀ γ, Reaches x β γ → Monotone (iterSlot f γ)) → iterSlot f α x ≤ iterSlot f β x := by
  induction h with
  | refl a => intro _; exact le_rfl
  | @succ β γ α hb _ ih =>
      intro hmono
      have hmγ : Monotone (iterSlot f γ) := hmono γ (Reaches.succ hb (Reaches.refl γ))
      have ihγ : iterSlot f α x ≤ iterSlot f γ x := ih (fun δ hδ => hmono δ (Reaches.succ hb hδ))
      have heq : iterSlot f β x = iterSlot f γ (f x) := by rw [iterSlot_succ f _ hb]
      rw [heq]; exact le_trans ihγ (hmγ (hf_infl x))
  | @limit β α g hb _ ih =>
      intro hmono
      have ihg : iterSlot f α x ≤ iterSlot f (g x) x :=
        ih (fun δ hδ => hmono δ (Reaches.limit hb hδ))
      have heq : iterSlot f β x = iterSlot f (g x) x := by rw [iterSlot_limit f _ hb]
      rw [heq]; exact ihg

/-- **C5 (discharged lap 6): `iterSlot f α` is monotone** for `f` monotone + inflationary.
Mirrors `hardy_monotone`: zero case is `hf_mono`, successor threads the IH through `f`'s
monotonicity, and the limit case combines monotonicity of `iterSlot f (α[n])` (IH) with the index
step `iterSlot f (α[n])(n+1) ≤ iterSlot f (α[n+1])(n+1)` = `iterSlot_le_of_reaches` on the
structural Bachmann reach `fastGrowing_bachmann_reach` (every intermediate is `< α`, so the IH
supplies its monotonicity). -/
theorem iterSlot_monotone {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    (α : ONote) : Monotone (iterSlot f α) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases e : fundamentalSequence α with (_ | a) | fs
  · rw [iterSlot_zero' f α e]; exact hf_mono (Nat.le_succ n)
  · have hlt : a < α := by
      have hp := fundamentalSequence_has_prop α; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [iterSlot_succ f α e]
    exact iterSlot_monotone hf_mono hf_infl a (hf_mono (Nat.le_succ n))
  · have hlt : fs n < α := by
      have hp := fundamentalSequence_has_prop α; rw [e] at hp
      exact (hp.2.1 n).2.1
    have hltn1 : fs (n + 1) < α := by
      have hp := fundamentalSequence_has_prop α; rw [e] at hp
      exact (hp.2.1 (n + 1)).2.1
    rw [iterSlot_limit f α e]
    have mono_fn : Monotone (iterSlot f (fs n)) := iterSlot_monotone hf_mono hf_infl (fs n)
    have step : iterSlot f (fs n) (n + 1) ≤ iterSlot f (fs (n + 1)) (n + 1) := by
      apply iterSlot_le_of_reaches hf_infl (fastGrowing_bachmann_reach e n)
      intro γ hγ
      have hγα : γ < α := lt_of_le_of_lt (reaches_le hγ) hltn1
      exact iterSlot_monotone hf_mono hf_infl γ
    exact le_trans (mono_fn (Nat.le_succ n)) step
termination_by α
decreasing_by
  · exact hlt
  · exact hlt
  · exact hγα

/-- **C5: `iterSlot f 0 = f`** — the α = 0 (cut-free axiom) case leaves the slot unchanged. -/
theorem iterSlot_zero (f : ℕ → ℕ) : iterSlot f 0 = f :=
  iterSlot_zero' f 0 rfl

/-- **BUDGETED ordinal-monotonicity of `iterSlot`** (mirror of `hardy_le_of_lt`): for `β < α`
(both NF) and a budget `x ≥ norm β`, `iterSlot f β x ≤ iterSlot f α x`.  Composes
`reaches_of_lt` (the general Bachmann reachability `Reaches x α β`) with `iterSlot_le_of_reaches`
(value transfer) and `iterSlot_monotone` (the per-notation monotonicity).

This is the form-independent CRUX LEMMA for the trap-8 fix (`REBUILD-Z-TRAP8-2026-07-02.md`):
`iterSlot f ·` is NOT ordinal-monotone at a FIXED small argument
(`no_fixed_arg_monotone_unbounded_slot`), but it IS monotone once the argument reaches the
`norm`-budget of the smaller ordinal.  So any pin-3 output slot whose READ is node-relative
(argument `≥ norm` of the node's ordinal — e.g. a relativized `rel1 (iterSlot f α) K` with
`K ≥ norm α`) restores the `weak`/`exI`/`cut` slot-lift that the bare `iterSlot f α` cannot
supply.  Banked here so the architect's node-relative C2 amendment can splice it directly. -/
theorem iterSlot_le_of_lt {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    {x : ℕ} {α β : ONote} (hα : α.NF) (hβ : β.NF) (hβα : β < α) (hnorm : norm β ≤ x) :
    iterSlot f β x ≤ iterSlot f α x :=
  iterSlot_le_of_reaches hf_infl (reaches_of_lt α hα β hβ hβα hnorm)
    (fun γ _ => iterSlot_monotone hf_mono hf_infl γ)

/-! ## §6 The two Z1 seams RE-EXPRESSED in the f-form (A2 — real proofs)

The Z1 seam probes re-run against the §5 f-slot statements.  If either seam failed to
compose HERE it would be trigger T-R(i) (the E–W carrier failing where the ℕ-slots failed —
no third carrier is pinned).  It does not: both close as real proofs. -/

/-- **Seam 1 absorbed by composition** (spike §6, ported; contrast
`SpikeW4B.seam1_uniform_slot_unpayable`, `¬(dd + x + 1 ≤ dd)` for every ℕ-slot): the
reduction's `+ norm α + 1`-class output bump re-enters the COMPOSED slot, which pays any
structural bump exactly. -/
theorem seam1_bump_absorbed_by_composition (x : ℕ) :
    ∃ g : ℕ → ℕ, ∀ dd : ℕ, dd + x + 1 ≤ g dd :=
  ⟨fun dd => dd + x + 1, fun _ => le_rfl⟩

/-- **Seam 2 absorbed by a function slot** (spike §6, ported; contrast
`SpikeW4B.seam2_no_uniform_slot`, which refuted every ℕ-slot `D` against exactly this
family): the two-level configuration's branch-`n` demand is paid by ONE function-valued
slot evaluated through its own relativization. -/
theorem seam2_function_slot_payable (dBase eNorm : ℕ) :
    ∃ f : ℕ → ℕ, ∀ n : ℕ, (dBase + eNorm + 1) + norm (expTower (wmul n)) + 1 ≤ rel1 f n 0 := by
  refine ⟨fun x => dBase + eNorm + x + 3, fun n => ?_⟩
  have h : norm (expTower (wmul n)) = n + 1 := by
    rw [norm_expTower, norm_wmul]; omega
  rw [h]
  simp [rel1]
  omega

/-- **Non-vacuity (W4B §3's two-level configuration, `Zeh` form; sorry-free).**  ONE `allω`
node at `ω^ω` whose EVERY branch `n` is a rank-`c` principal ∀/∃ cut with premise ordinals
`ω·(n+1)` — the branch-unbounded configuration that killed the `(k,d)` calculus, realized as
a legal `Zeh` derivation: every side condition is a membership, discharged by a REAL
per-branch closure tree.  This is the inhabitedness witness the seam-2 reversal rests on
(the reassembly probe would be vacuous without it). -/
theorem two_level_config_Zeh {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (χ ψ : ArithmeticSemiformula ℕ 1) {e : ONote} {H : ONote → Prop} {m : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    Zeh (expTower ONote.omega) e H m ((∀⁰ χ).complexity + 1) (insert (∀⁰ ψ) Γ) := by
  refine Zeh.allω ψ (fun n => osucc (wmul n))
    (fun n => osucc_wmul_lt_expTower_omega n)
    (fun n => osucc_NF (wmul_NF n))
    (expTower_NF omegaO_NF)
    (fun n => Cl.osucc (wmul_mem _ n))
    (fun n => ?_)
  refine Zeh.cut (∀⁰ χ) (Nat.lt_succ_self _)
    (Zekd.lt_osucc (wmul_NF n)) (Zekd.lt_osucc (wmul_NF n))
    (wmul_NF n) (wmul_NF n) (osucc_NF (wmul_NF n))
    (wmul_mem _ n) (wmul_mem _ n) ?_ ?_
  · exact Zeh.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))
  · exact Zeh.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))

/-- **Seam-2 reversal probe, f-form (sorry-free):** the ω-node re-assembles over the
reduction-output class, with each branch's control carried by the relativized f-slot
`rel1 f n` (`normControlled_rel1`).  Mirrors the spike's `probe_allomega_reassembly_Zeh`
membership form; here the numeric control rides the function slot the seam demands. -/
theorem probe_allomega_reassembly_Zf {e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {f : ℕ → ℕ} (hf : NormControlled f e m)
    (dd : ∀ n, Zeh (osucc (wmul n + wmul n)) e (adjoin H n) (max m n) c
      (insert (χ/[nm n]) Γ)) :
    Zeh (expTower ONote.omega) e H m c (insert (∀⁰ χ) Γ) ∧
      (∀ n, NormControlled (rel1 f n) e (max m n)) := by
  refine ⟨?_, fun n => normControlled_rel1 hf n⟩
  refine Zeh.allω χ (fun n => osucc (wmul n + wmul n))
    (fun n => ?_) (fun n => ?_) (expTower_NF omegaO_NF)
    (fun n => Cl.osucc (Cl.add (wmul_mem (adjoin H n) n) (wmul_mem (adjoin H n) n))) dd
  · rw [wmul_add_wmul]
    exact osucc_omega_coeff_lt _
  · rw [wmul_add_wmul]
    exact osucc_NF (nf_one.oadd _ NFBelow.zero)


/-! ## §7 Companion inversions (A3 — mirroring the banked `Zekd` suite)

`orInv_Zeh`, `andInvL_Zeh`, `andInvR_Zeh` — the propositional inversions the banked `Zekd`
suite carries (`OperatorZinfty.lean:221/326/404`).  They keep the SAME `(α, e, H, m, c)`
(unlike `allInv_Zeh`, which raises the stage/relativization), so no `mono_H`/`Cl_mono`
re-keying is needed — the side-condition memberships thread through unchanged.  Since the
minimal `Zeh` core has NO `andI`/`orI` introduction rule, `φ ⋏ ψ` / `φ ⋎ ψ` is never
principal: every case just threads the inversion past a passive side formula, so these ports
are strictly SHORTER than `Zekd`'s (which each carry a principal `andI`/`orI` sub-case).
They do not consume the §5 f-slot statements — safe grind, and reused by the cut-elimination
assembly (laps 5–7) for cuts on propositional formulas. -/

/-- Double-insert reshuffle helpers (∨-inversion inserts both `φ` and `ψ`; re-derivations of
the `private` `OperatorZinfty` copies). -/
theorem invPush (A b : ArithmeticFormula ℕ) (s : Finset (ArithmeticFormula ℕ))
    {φ ψ : ArithmeticFormula ℕ} :
    insert φ (insert ψ ((insert b s).erase A)) ⊆ insert b (insert φ (insert ψ (s.erase A))) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

theorem invPull (A : ArithmeticFormula ℕ) {b : ArithmeticFormula ℕ} (h : b ≠ A)
    (s : Finset (ArithmeticFormula ℕ)) {φ ψ : ArithmeticFormula ℕ} :
    insert b (insert φ (insert ψ (s.erase A))) ⊆ insert φ (insert ψ ((insert b s).erase A)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | rfl | rfl | hx
  · exact Or.inr (Or.inr ⟨h, Or.inl rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨hx.1, Or.inr hx.2⟩)

/-- **∨-inversion, `Zeh` form** (Towsner §19.3): replace `φ ⋎ ψ` by `φ, ψ`, same
`(α, e, H, m, c)`. -/
theorem orInv_Zeh {φ ψ : ArithmeticFormula ℕ} :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zeh α e H m c Γ → (φ ⋎ ψ) ∈ Γ →
    Zeh α e H m c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  intro α e H m c Γ dd
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      intro _
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @wk α e H m c Δ Γ hsub dd ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zeh.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF hβH (Finset.insert_subset_insert _
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zeh.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [UnivQuantifier.all, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zeh.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zeh.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [ExsQuantifier.exs, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zeh.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zeh.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, left, `Zeh` form** (Towsner §19.3): replace `φ ⋏ ψ` by `φ`, same
`(α, e, H, m, c)`. -/
theorem andInvL_Zeh {φ ψ : ArithmeticFormula ℕ} :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zeh α e H m c Γ → (φ ⋏ ψ) ∈ Γ →
    Zeh α e H m c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  intro α e H m c Γ dd
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      intro _
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H m c Δ Γ hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c
          (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zeh.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, right, `Zeh` form** (Towsner §19.3): replace `φ ⋏ ψ` by `ψ`, same
`(α, e, H, m, c)`. -/
theorem andInvR_Zeh {φ ψ : ArithmeticFormula ℕ} :
    ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zeh α e H m c Γ → (φ ⋏ ψ) ∈ Γ →
    Zeh α e H m c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  intro α e H m c Γ dd
  induction dd with
  | @axL α e H m c Γ ar r v hp hn =>
      intro _
      refine Zeh.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H m c Δ Γ hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H m c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zeh.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zeh.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H m c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zeh (β n) e (adjoin H n) (max m n) c
          (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H m c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zeh.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zeh.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zeh.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H m c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zeh.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zeh.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zeh.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-! ## §8 Structural monotonicity infrastructure (assembly plumbing, not judge-gated)

Cut-rank monotonicity — banked in the `Zekd` suite (`OperatorZinfty.lean:146`), reused by
the rank-lowering elimination pass (`cutElimPass_Zf`, which relates rank-`c+1` and rank-`c`
derivations).  Structural, does NOT consume the §5 f-slot statements; safe pre-ratification
infrastructure. -/

namespace Zeh

/-- **`c`-monotonicity** (cut rank): a derivation valid at rank `c` is valid at any `c' ≥ c`.
Only the `cut` rule reads `c` (via `hcompl : φ.complexity < c`), so every other case threads. -/
theorem mono_c : ∀ {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zeh α e H m c Γ → ∀ {c' : ℕ}, c ≤ c' → Zeh α e H m c' Γ := by
  intro α e H m c Γ dd
  induction dd with
  | axL r v hp hn => intro c' _; exact Zeh.axL r v hp hn
  | wk hsub _ ih => intro c' hc; exact Zeh.wk hsub (ih hc)
  | weak hβ hβNF hαNF hβH hsub _ ih => intro c' hc; exact Zeh.weak hβ hβNF hαNF hβH hsub (ih hc)
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      intro c' hc; exact Zeh.allω φ β hβ hβNF hαNF hβH (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro c' hc; exact Zeh.exI φ n hβ hβNF hαNF hβH hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zeh.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁ hc) (ih₂ hc)

end Zeh

/-! ### Ordinal-splice descent bricks (assembly plumbing, not judge-gated)

The §19.6 reduction outputs ordinal `osucc (α + γ)`; its inner descent cites these pure
`ONote` facts (no `Zeh` manipulation — reused by, but distinct from, the gated reduction).
Each composes the banked `Zekd` ordinal lemmas.  Built ahead so the discharge lap is pure
assembly. -/

/-- The reduction-output ordinal is NF whenever its components are. -/
theorem osucc_add_NF {α γ : ONote} (hα : α.NF) (hγ : γ.NF) : (osucc (α + γ)).NF :=
  osucc_NF (ONote.add_nf α γ)

/-- **Splice descent, `osucc` form:** `γ' < γ ⟹ osucc (α + γ') < osucc (α + γ)` (the branch
premise's ordinal strictly drops below the spliced output). -/
theorem osucc_add_lt_osucc_add {α γ' γ : ONote} (hα : α.NF) (hγ' : γ'.NF) (hγ : γ.NF)
    (h : γ' < γ) : osucc (α + γ') < osucc (α + γ) :=
  Zekd.osucc_lt_osucc (ONote.add_nf α γ') (ONote.add_nf α γ)
    (Zekd.add_lt_add_left_NF hα hγ' hγ h)

/-- **Splice descent, bare form:** `γ' < γ ⟹ α + γ' < osucc (α + γ)` (a premise below `γ`
lies strictly below the spliced output — the direct `weak`/`exI` descent witness). -/
theorem add_lt_osucc_add {α γ' γ : ONote} (hα : α.NF) (hγ' : γ'.NF) (hγ : γ.NF)
    (h : γ' < γ) : α + γ' < osucc (α + γ) :=
  Zekd.lt_osucc_of_lt (ONote.add_nf α γ) (Zekd.add_lt_add_left_NF hα hγ' hγ h)

/-- Membership of the reduction-output ordinal by closure (the seam-1 brick, named for the
reduction's use site: `osucc (α + γ)` is a member whenever `α`, `γ` are). -/
theorem osucc_add_mem {S : ONote → Prop} {α γ : ONote} (hα : Cl S α) (hγ : Cl S γ) :
    Cl S (osucc (α + γ)) :=
  Cl.osucc (Cl.add hα hγ)

/-- Ordinal `+` is monotone in both arguments (non-strict; the wrapper's `≤`-slack bound for
the cut combinator). -/
theorem add_le_add_NF {α₁ β₁ α₂ β₂ : ONote} (hα₁ : α₁.NF) (hβ₁ : β₁.NF)
    (hα₂ : α₂.NF) (hβ₂ : β₂.NF) (h₁ : α₁ ≤ β₁) (h₂ : α₂ ≤ β₂) : α₁ + α₂ ≤ β₁ + β₂ := by
  haveI := hα₁; haveI := hβ₁; haveI := hα₂; haveI := hβ₂
  exact le_def.mpr (by rw [repr_add, repr_add]; exact add_le_add (le_def.mp h₁) (le_def.mp h₂))

/-- `osucc` non-strict monotonicity (pairs with `Zekd.osucc_lt_osucc`). -/
theorem osucc_le_osucc {x y : ONote} (hx : x.NF) (hy : y.NF) (h : x ≤ y) : osucc x ≤ osucc y := by
  refine le_def.mpr ?_
  rw [repr_osucc hx, repr_osucc hy, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_le_succ (le_def.mp h)

/-- **`ZehProv`-level cut combinator** (assembly plumbing, NOT the gated reduction): package
the cut RULE at the wrapper level — combine proofs of `φ` and `∼φ` (with `φ.complexity < c`)
into a proof of `Γ` at ordinal `osucc (βφ + βψ)`, SAME rank and control (no rank-lowering, no
control-raise — those are the judge-gated `cutElimPass_Zf`/reduction).  The step/reduction
assembly reuses this to introduce cuts before eliminating them. -/
theorem ZehProv.cut {βφ βψ e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (φ : ArithmeticFormula ℕ) (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hcompl : φ.complexity < c)
    (D₁ : ZehProv βφ e H m c (insert φ Γ)) (D₂ : ZehProv βψ e H m c (insert (∼φ) Γ)) :
    ZehProv (osucc (βφ + βψ)) e H m c Γ := by
  obtain ⟨α₁, hle₁, hNF₁, hH₁, d₁⟩ := D₁
  obtain ⟨α₂, hle₂, hNF₂, hH₂, d₂⟩ := D₂
  refine ⟨osucc (α₁ + α₂),
    osucc_le_osucc (ONote.add_nf α₁ α₂) (ONote.add_nf βφ βψ)
      (add_le_add_NF hNF₁ hβφNF hNF₂ hβψNF hle₁ hle₂),
    osucc_add_NF hNF₁ hNF₂, osucc_add_mem hH₁ hH₂,
    Zeh.cut φ hcompl
      (lt_of_le_of_lt (Zekd.le_add_right_NF hNF₁ hNF₂) (Zekd.lt_osucc (ONote.add_nf α₁ α₂)))
      (lt_of_le_of_lt (Zekd.le_add_left_NF hNF₁ hNF₂) (Zekd.lt_osucc (ONote.add_nf α₁ α₂)))
      hNF₁ hNF₂ (osucc_add_NF hNF₁ hNF₂) hH₁ hH₂ d₁ d₂⟩

/-- **`ZehProv`-level `exI` combinator** (assembly plumbing): package the `∃`-rule at the
wrapper level — the output ordinal `osucc β` is fully determined, no rank/control change.
Reused by the assembly to introduce existentials at the prov level. -/
theorem ZehProv.exI {β e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβNF : β.NF) (hβH : Cl H β)
    (hbound : n ≤ hardy e m) (D : ZehProv β e H m c (insert (φ/[nm n]) Γ)) :
    ZehProv (osucc β) e H m c (insert (∃⁰ φ) Γ) := by
  obtain ⟨β', hle, hNF', hH', d⟩ := D
  exact ⟨osucc β, le_rfl, osucc_NF hβNF, Cl.osucc hβH,
    Zeh.exI φ n (lt_of_le_of_lt hle (Zekd.lt_osucc hβNF)) hNF' (osucc_NF hβNF) hH' hbound d⟩

/-- **`ZehProv`-level `allω` combinator** (assembly plumbing): reassemble an ω-node at the
wrapper level.  Each branch's `≤`-slack witness is threaded through (`< α` survives since
`β' n ≤ β n < α`); the output witness is `α` itself (needs `Cl H α`).  Reused by the
assembly to rebuild ω-nodes over the branch family. -/
theorem ZehProv.allω {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
    (hβ : ∀ n, β n < α) (hαNF : α.NF) (hαH : Cl H α)
    (D : ∀ n, ZehProv (β n) e (adjoin H n) (max m n) c (insert (φ/[nm n]) Γ)) :
    ZehProv α e H m c (insert (∀⁰ φ) Γ) :=
  ⟨α, le_rfl, hαNF, hαH,
    Zeh.allω φ (fun n => (D n).choose)
      (fun n => lt_of_le_of_lt (D n).choose_spec.1 (hβ n))
      (fun n => (D n).choose_spec.2.1)
      hαNF
      (fun n => (D n).choose_spec.2.2.1)
      (fun n => (D n).choose_spec.2.2.2)⟩

/-! ## Blueprint ledger coverage (machine-synced status for the proven Zᵉ nodes)

Only the PROVEN nodes carry ledger attributes.  Pins 1–2 (`cutReduceAllAuxRunning_Zf`,
`stepAllω_Zf`) are now DISCHARGED (§7 slot judgment, lap 184) and eligible for attributes; pin 3
(`cutElimPass_Zf`) is still `sorryAx`-bearing, and the audit treats a sorried footprint as
`broken` = CI FAIL by design, so it stays a `notready` TeX node until its lap-5 discharge lands. -/

attribute [goodstein_blueprint 10 clean "zeh_inversion_suite" "0" 100 allInv_Zeh
  []
  ["Towsner §19.4 ∀-inversion; mirrors the banked Zekd.allInv (OperatorZinfty.lean:484)",
   "GoodsteinPA.OperatorZeh.orInv_Zeh / andInvL_Zeh / andInvR_Zeh: complete propositional companions, axiom-clean",
   "E-2026-07-02-JUDGE-rebuild-z-lap1-validation.md §2: suite completeness verified (the minimal core admits no fifth inversion)"]
  "The Zeh inversion suite: control-preserving inversions (∀ at the relativization + running stage) feeding the fixed-control reduction and the cut-elimination assembly."]
  allInv_Zeh

attribute [goodstein_blueprint 11 clean "zeh_readoff_exit" "0" 100 headline_readoff
  []
  ["Buchholz–Wainer 1987, Bounding Lemma (∀-free positive Σ₁ shape)",
   "Eguchi–Weiermann arXiv:1205.2879, Lemma 31 (witnessing bound f 0)",
   "SPIKE-Z1-VERDICT.md Q2: proven per-instance, no evaluator, no truth predicate, no H-data (Σ₁-definability-of-H risk dissolved)"]
  "The M2-exit read-off: a rank-0 Zeh derivation of the Σ₁ headline shape yields a witness ≤ hardy e m — the fixed exit every rebuild statement must compose toward (Δ₀-matrix extension is the scheduled laps-8–10 node)."]
  headline_readoff


/-! # §7 — The function-slot judgment `Zef` (LOCK §1-A1/§3 amendment, ratified lap 184)

Ported verbatim from `wip/ZefSlotCalculus.lean` (kernel-verified sorry-free / axiom-clean).  `Zef`
= `Zeh` with the ℕ-stage `m` replaced by a function-slot `f : ℕ → ℕ` — the R4-compliant carrier the
stage judgment could not provide (the stage-`m` reduction is kernel-refuted:
`principal_witness_exceeds_stage`; see `REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`).  `exI` bound
`n ≤ f 0`, `allω` branch slot `rel1 f n`, reduction output slot **`g∘f`**.  This block discharges
pins 1–2 (`cutReduceAllAuxRunning_Zf`, `stepAllω_Zf`) and the read-off exit (`headline_readoff_Zef`) as REAL
theorems; the §5 stage pins are rewired to consume them next (port step P3). -/
/-! ## The slot calculus `Zef` (`Zeh` with stage `m` ⤳ slot `f : ℕ → ℕ`) -/

inductive Zef : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Finset (ArithmeticFormula ℕ) → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {ar : ℕ}
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hsub : Δ ⊆ Γ) (dd : Zef α e H f c Δ) : Zef α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef β e H f c Δ) : Zef α e H f c Γ
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef β e H f c (insert (φ/[nm n]) Γ)) : Zef α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
      (φ : ArithmeticFormula ℕ) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef βφ e H f c (insert φ Γ)) (d₂ : Zef βψ e H f c (insert (∼φ) Γ)) :
      Zef α e H f c Γ

namespace Zef

/-- Sequent weakening (height-preserving). -/
theorem weakening {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Finset (ArithmeticFormula ℕ)}
    (hsub : Δ ⊆ Γ) (dd : Zef α e H f c Δ) : Zef α e H f c Γ :=
  Zef.wk hsub dd

/-- **Slot weakening** (`mono_f` — the slot analog of `Zeh.mono_H`'s stage-raise): a larger slot
is more permissive.  `exI` rides `n ≤ f 0 ≤ f' 0`; `allω` rides `rel1_mono`. -/
theorem mono_f : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zef α e H f c Γ → ∀ {f' : ℕ → ℕ}, (∀ x, f x ≤ f' x) → Zef α e H f' c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL r v hp hn => intro f' _; exact Zef.axL r v hp hn
  | wk hsub _ ih => intro f' hff'; exact Zef.wk hsub (ih hff')
  | weak hβ hβNF hαNF hβH hsub _ ih =>
      intro f' hff'; exact Zef.weak hβ hβNF hαNF hβH hsub (ih hff')
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      intro f' hff'
      exact Zef.allω φ β hβ hβNF hαNF hβH (fun n => ih n (rel1_mono hff' n))
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro f' hff'
      exact Zef.exI φ n hβ hβNF hαNF hβH (le_trans hbound (hff' 0)) (ih hff')
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact Zef.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hff') (ih₂ hff')

/-- **Operator irrelevance** (R1, slot form): the generator slot `H` carries no information
(every `Cl H β` side condition is at an NF ordinal — `Cl_of_NF`), so a derivation at `H` is one
at any `H'`, same `(α, e, f, c, Γ)`.  Mirrors `Zeh.change_H`. -/
theorem change_H : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zef α e H f c Γ → ∀ {H' : ONote → Prop}, Zef α e H' f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL r v hp hn => intro H'; exact Zef.axL r v hp hn
  | wk hsub _ ih => intro H'; exact Zef.wk hsub ih
  | weak hβ hβNF hαNF _ hsub _ ih => intro H'; exact Zef.weak hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | allω φ β hβ hβNF hαNF _ _ ih =>
      intro H'; exact Zef.allω φ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI φ n hβ hβNF hαNF _ hbound _ ih =>
      intro H'; exact Zef.exI φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'; exact Zef.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

/-- Combined operator+slot move (operator free via `change_H`, slot raised via `mono_f`) — the
`mono_H` analog the inversion port needs. -/
theorem mono_Hf {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (dd : Zef α e H f c Γ) {H' : ONote → Prop} {f' : ℕ → ℕ} (hff' : ∀ x, f x ≤ f' x) :
    Zef α e H' f' c Γ := (dd.change_H).mono_f hff'

end Zef

/-- The `≤`-slack wrapper (slot form of `ZehProv`). -/
def ZefProv (α e : ONote) (H : ONote → Prop) (f : ℕ → ℕ) (c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Zef α' e H f c Γ

namespace ZefProv

theorem of {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hNF : α.NF) (hH : Cl H α) (D : Zef α e H f c Γ) : ZefProv α e H f c Γ :=
  ⟨α, le_refl _, hNF, hH, D⟩

theorem mono {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hα : α ≤ β) : ZefProv α e H f c Γ → ZefProv β e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, D⟩

theorem weakening {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Δ : Finset (ArithmeticFormula ℕ)}
    (h : Γ ⊆ Δ) : ZefProv α e H f c Γ → ZefProv α e H f c Δ := by
  rintro ⟨α', hα', hNF, hH, D⟩
  exact ⟨α', hα', hNF, hH, D.wk h⟩

end ZefProv

/-! ## The re-slot domination facts (lap-3 probe, restated for `rel1 · ·` slots) -/

/-- **The ∀-family member re-slots to `g∘f`** (lap-3 `reslot_gof_family`): for `g` monotone, `f`
monotone + inflationary, and witness `n ≤ f 0`, `rel1 g n ≤ g∘f` pointwise. -/
theorem reslot_family {f g : ℕ → ℕ} (hg_mono : Monotone g)
    (hf_infl : ∀ x, x ≤ f x) (hf_mono : Monotone f) {n : ℕ} (hn : n ≤ f 0) :
    ∀ x, rel1 g n x ≤ (g ∘ f) x := by
  intro x
  simp only [rel1, Function.comp]
  refine hg_mono ?_
  rcases le_total n x with h | h
  · rw [max_eq_right h]; exact hf_infl x
  · rw [max_eq_left h]; exact le_trans hn (hf_mono (Nat.zero_le x))

/-- **The ∃-side reduct re-slots to `g∘f`** (lap-3 `reslot_gof_exside`): `f ≤ g∘f` for `g`
inflationary. -/
theorem reslot_exside {f g : ℕ → ℕ} (hg_infl : ∀ x, x ≤ g x) :
    ∀ x, f x ≤ (g ∘ f) x := fun x => hg_infl (f x)

/-! ## The running-family reduction, SORRY-FREE (the lap-2 gap, now closed) -/

set_option maxHeartbeats 400000 in
/-- **`cutReduceAllAuxRunning_Zf`** — the full Towsner §19.6 running-family cut-reduction in the slot
calculus, output slot `g∘f`.  The lap-2 `redDeriv` port with the stage `m` replaced by the
current slot `f'` (threaded monotone + inflationary) and the two axis-critical moves:
- **principal `exI`** — both cut premises re-slot to `g∘f'` (`reslot_family` / `reslot_exside`),
  cut lands at `g∘f'` (the conclusion slot) with NO leak — the gap the fixed `hardy e m` bound
  could not cross;
- **`allω`** — each branch's IH output slot `g ∘ rel1 f' n` is `rel1 (g∘f') n` by `rel1_comp`
  (definitional), exactly the `allω` node's branch slot. -/
theorem cutReduceAllAuxRunning_Zf {φ : ArithmeticSemiformula ℕ 1} {c : ℕ} {α e : ONote}
    {Γ : Finset (ArithmeticFormula ℕ)} {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (fam : ∀ n (H' : ONote → Prop), Zef α e H' (rel1 g n) c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Finset (ArithmeticFormula ℕ)}, Zef γ e H f c Δ → γ.NF →
      Monotone f → (∀ x, x ≤ f x) → (∃⁰ ∼φ) ∈ Δ →
      ZefProv (osucc (α + γ)) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro γ H f Δ D
  induction D with
  | @axL γ e H f c Δ ar r v hp hn =>
      intro hγNF _ _ hmem
      refine ZefProv.of (osucc_NF (ONote.add_nf α γ)) (Cl_of_NF (osucc_NF (ONote.add_nf α γ))) ?_
      exact Zef.axL r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))
  | @wk γ e H f c Δsub Δsup hsub D' ih =>
      intro hγNF hmono hinfl hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hmono hinfl hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · refine ⟨γ, le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))), hγNF, Cl_of_NF hγNF,
          (D'.mono_f (reslot_exside hg_infl)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ β e H f c Δsub Δsup hβ hβNF hγNF' hβH hsub D' ih =>
      intro hγNF hmono hinfl hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hmono hinfl hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
      · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ))))), hβNF, Cl_of_NF hβNF,
          (D'.mono_f (reslot_exside hg_infl)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @allω γ e H f c Γ₀ χ β hβ hβNF hγNF' hβH dd ih =>
      intro hγNF hmono hinfl hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have ihn : ∀ n, ZefProv (osucc (α + β n)) e (adjoin H n) (g ∘ rel1 f n) c
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        exact (ih n hφc heNF fam (hβNF n) (rel1_monotone hmono n) (rel1_infl hinfl n)
          (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      have hAll : Zef (osucc (α + γ)) e H (g ∘ f) c
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        -- branch slot `g ∘ rel1 f n` is `rel1 (g∘f) n` by `rel1_comp` (definitional)
        refine Zef.allω χ (fun n => (ihn n).choose)
          (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
            (Zekd.add_osucc_descent hαNF (hβNF n) hγNF (hβ n)))
          (fun n => (ihn n).choose_spec.2.1) hsuccNF
          (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
          (fun n => (ihn n).choose_spec.2.2.2)
      exact hAll.wk (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)
  | @exI γ β e H f c Γ₀ χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      intro hγNF hmono hinfl hmem
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · -- PRINCIPAL: χ = ∼φ; cut `fam n` (re-slotted to `g∘f`) against the ∃-premise.
        have hχ : χ = ∼φ := by simpa [ExsQuantifier.exs] using hhd
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c := by simpa using hφc
        -- `fam n` re-slots `rel1 g n → g∘f` (both premises land at the conclusion slot `g∘f`)
        have famn : Zef α e H (g ∘ f) c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          ((fam n H).mono_f (reslot_family hg_mono hinfl hmono hbound)).wk (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
        have hαlt : α < osucc (α + γ) :=
          lt_of_le_of_lt (Zekd.le_add_right_NF hαNF hγNF) (Zekd.lt_osucc (ONote.add_nf α γ))
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hmono hinfl
            (Finset.mem_insert_of_mem hd)
          have Da' : Zef a e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Da.wk (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
          refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
          exact Zef.cut (φ/[nm n]) hcompl hαlt
            (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            hαNF haNF hsuccNF (Cl_of_NF hαNF) haH famn Da'
        · -- ∃-premise `dχ` re-slots `f → g∘f`
          have Dβ' : Zef β e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            (dχ.mono_f (reslot_exside hg_infl)).wk (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
          refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
          exact Zef.cut (φ/[nm n]) hcompl hαlt
            (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
              (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ)))))
            hαNF hβNF hsuccNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, haH, Da⟩ := ih hφc heNF fam hβNF hmono hinfl
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zef a e H (g ∘ f) c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Da.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
        -- non-principal `exI`: witness bound `n ≤ f 0 ≤ (g∘f) 0` (via `hg_infl` at `f 0`)
        have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
        have hExI : Zef (osucc (α + γ)) e H (g ∘ f) c
            (insert (∃⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zef.exI χ n (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            haNF hsuccNF haH hbound' Da'
        exact hExI.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhd, Or.inl rfl⟩
          · tauto)
  | @cut γ βφ βψ e H f c Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl (Finset.mem_insert_of_mem hmem)
      have hsuccNF : (osucc (α + γ)).NF := osucc_NF (ONote.add_nf α γ)
      have D₁' : Zef a₁ e H (g ∘ f) c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₁.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have D₂' : Zef a₂ e H (g ∘ f) c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₂.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine ZefProv.of hsuccNF (Cl_of_NF hsuccNF) ?_
      exact Zef.cut χ hχc
        (lt_of_le_of_lt ha₁le (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
        ha₁NF ha₂NF hsuccNF ha₁H ha₂H D₁' D₂'

/-! ## ∀-inversion in the slot calculus (feeds the reduction from a ∀-side derivation) -/

/-- `f ≤ rel1 f n₀` for monotone `f` (`f x ≤ f (max n₀ x)`). -/
private theorem f_le_rel1 {f : ℕ → ℕ} (hf : Monotone f) (n₀ : ℕ) :
    ∀ x, f x ≤ rel1 f n₀ x := fun x => hf (le_max_right n₀ x)

/-- **`allInv_Zef`** — ∀-inversion, slot form: port of `allInv_Zeh` with `max m n₀ ⤳ rel1 f n₀`.
The extracted instance runs at the relativization `adjoin H n₀` and the relativized slot
`rel1 f n₀`.  Needs `f` monotone (to raise `exI` bounds `n ≤ f 0 ≤ (rel1 f n₀) 0 = f n₀`).  The
operator threading is FREE (`mono_Hf`/`change_H`, R1). -/
theorem allInv_Zef {φ₀ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
      Zef α e H f c Γ → Monotone f → (∀⁰ φ₀) ∈ Γ →
      Zef α e (adjoin H n₀) (rel1 f n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      intro _ _
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hsub dd ih =>
      intro hmono hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef.wk ?_ (dd.mono_Hf (f_le_rel1 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmono hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF (Cl_of_NF hβNF)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef.weak hβ hβNF hαNF (Cl_of_NF hβNF) ?_ (dd.mono_Hf (f_le_rel1 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmono hmem
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (rel1_monotone hmono n₀) (Finset.mem_insert_of_mem hh)
          have h2 : Zef (β n₀) e (adjoin H n₀) (rel1 f n₀) c
              (insert (χ/[nm n₀]) ((insert (χ/[nm n₀]) Γ₀).erase (∀⁰ χ))) :=
            h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega))
          exact Zef.weak (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀)) (princAllSub (∀⁰ χ) _ Γ₀) h2
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zef.weak (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀)) (Finset.Subset.refl _) (dd n₀)
      · have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zef (β n) e (adjoin (adjoin H n₀) n) (rel1 (rel1 f n₀) n) c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := ih n (rel1_monotone hmono n) (Finset.mem_insert_of_mem hmem0)
          exact Zef.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀)
            (h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega)))
        exact Zef.wk (inv1Pull (∀⁰ φ₀) _ hhd Γ₀)
          (Zef.allω χ β hβ hβNF hαNF (fun n => Cl_of_NF (hβNF n)) key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmono hmem
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih hmono (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (∀⁰ φ₀) _ hhead Γ₀)
        (Zef.exI χ n hβ hβNF hαNF (Cl_of_NF hβNF)
          (le_trans hbound (hmono (Nat.zero_le _))) P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmono hmem
      have P₁ := Zef.wk (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ hmono (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ hmono (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) P₁ P₂

/-- **`stepAllω_Zf`** (pin-2 analog in the slot calculus): the principal ∀/∃ cut-reduction step,
IHs at ONE control `E` and stage-slots, output slot `g∘f`.  Invert the ∀-side `D₁` (slot `g`) to
the running family via `allInv_Zef`, then apply `cutReduceAllAuxRunning_Zf` against the ∃-side `D₂` (slot `f`).
Both premises are `ZefProv` wrappers; slots monotone + inflationary. -/
theorem stepAllω_Zf {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {βφ βψ : ONote} {f g : ℕ → ℕ}
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    (D₁ : ZefProv (expTower βφ) E H g c (insert (∀⁰ χ) Γ))
    (D₂ : ZefProv (expTower βψ) E H f c (insert (∃⁰ ∼χ) Γ)) :
    ∃ δ : ONote, δ.NF ∧ Cl H δ ∧ ZefProv δ E H (g ∘ f) c Γ := by
  obtain ⟨α₁, _, hNF₁, hH₁, d₁⟩ := D₁
  obtain ⟨γ₁, _, hNF₂, hH₂, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    exact ((allInv_Zef n d₁ hg_mono (Finset.mem_insert_self _ _)).weakening
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))).change_H
  have hred := cutReduceAllAuxRunning_Zf hχc hNF₁ hENF hg_mono hg_infl fam d₂ hNF₂ hf_mono hf_infl
    (Finset.mem_insert_self _ _)
  refine ⟨osucc (α₁ + γ₁), osucc_NF (ONote.add_nf α₁ γ₁),
    Cl_of_NF (osucc_NF (ONote.add_nf α₁ γ₁)), ?_⟩
  exact hred.weakening (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))

/-- **§6 seam-1 composition probe, slot form (a REAL corollary — the §5 reduction pins are now
DISCHARGED).**  The ∀/∃ arm at an ω-branch: the two premises' slots `g` (∀-family) and `f`
(∃-side) compose to `g ∘ f` on the output, at the FIXED control `E` (the raise/iteration live in
`cutElimPass_Zf` alone).  Formerly the sorry-dependent `probe_cut_all_arm_Zf`; now a direct
consequence of the discharged `stepAllω_Zf`.  Seam 1 reverses in the slot form. -/
theorem probe_cut_all_arm_Zf {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {βφ βψ : ONote} {f g : ℕ → ℕ}
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    (IH1 : ZefProv (expTower βφ) E H g c (insert (∀⁰ χ) Γ))
    (IH2 : ZefProv (expTower βψ) E H f c (insert (∃⁰ ∼χ) Γ)) :
    ∃ δ : ONote, δ.NF ∧ Cl H δ ∧ ZefProv δ E H (g ∘ f) c Γ :=
  stepAllω_Zf hENF hχc hg_mono hg_infl hf_mono hf_infl IH1 IH2

/-! ## The read-off EXIT in the slot calculus (E–W Lemma 31 EXACTLY: witness ≤ `f 0`)

Closing the end-to-end viability loop: the slot calculus reaches the §3 exit, and — because the
slot IS the witness budget — the read-off bound is `f 0`, matching E–W's Witnessing Lemma (Lemma
31, `max{m_j} ≤ f(0)`) verbatim (vs the `Zeh` version's `hardy e m`, the canonical slot at 0).
Independent of cut-elimination (operates on any rank-0 derivation). -/

/-- Slot-form read-off sequent shape (`hardy e m ⤳ f 0`). -/
def ReadoffShapeF (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∀ ψ ∈ Γ, ψ = (∃⁰ φ) ∨ (∃ n ≤ f 0, ψ = φ/[nm n]) ∨
    (∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- Slot-form read-off conclusion. -/
def ReadoffGoalF (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  (∃ n ≤ f 0, atomTrue (φ/[nm n])) ∨
    (∃ ψ ∈ Γ, atomTrue ψ ∧
      ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, ψ = Semiformula.rel r v ∨ ψ = Semiformula.nrel r v)

/-- **`readoff_sigma1_Zef`** — the bounding read-off in the slot calculus (port of
`readoff_sigma1`, `hardy e m ⤳ f 0`).  From a rank-0 `Zef` derivation of a `ReadoffShapeF`
sequent: a witness `n ≤ f 0` with `φ/[nm n]` true, or a true literal.  The bound is EXACTLY the
slot at 0 — E–W Lemma 31. -/
theorem readoff_sigma1_Zef {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
      Zef α e H f c Γ → c = 0 → ReadoffShapeF φ f Γ → ReadoffGoalF φ f Γ := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      intro _ _
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact Or.inr ⟨_, hp, htrue, ar, r, v, Or.inl rfl⟩
      · refine Or.inr ⟨_, hn, ?_, ar, r, v, Or.inr rfl⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H f c Δ Γ hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hshape
      rcases ih hc (fun ψ hψ => hshape ψ (hsub hψ)) with h | ⟨ψ, hψ, hrest⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hsub hψ, hrest⟩
  | @allω α e H f c Γ χ β hβ hβNF hαNF hβH _ _ =>
      intro _ hshape
      rcases hshape (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n, _, h⟩ | ⟨ar, r, v, h | h⟩
      · exact absurd h (by simp [UnivQuantifier.all, ExsQuantifier.exs])
      · obtain ⟨ar, r, v, hrel⟩ := hφinst n
        rw [hrel] at h
        exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
      · exact absurd h (by simp [UnivQuantifier.all])
  | @exI α β e H f c Γ χ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc hshape
      have hχφ : χ = φ := by
        rcases hshape (∃⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨n', _, h⟩ | ⟨ar, r, v, h | h⟩
        · simpa [ExsQuantifier.exs] using h
        · obtain ⟨ar, r, v, hrel⟩ := hφinst n'
          rw [hrel] at h
          exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
        · exact absurd h (by simp [ExsQuantifier.exs])
      have hφχ : φ = χ := hχφ.symm
      subst hφχ
      have hshape' : ReadoffShapeF φ f (insert (φ/[nm n]) Γ) := by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inr (Or.inl ⟨n, hbound, rfl⟩)
        · exact hshape ψ (Finset.mem_insert_of_mem hψΓ)
      rcases ih hc hshape' with h | ⟨ψ, hψ, htrue, hlit⟩
      · exact Or.inl h
      · rcases Finset.mem_insert.mp hψ with rfl | hψΓ
        · exact Or.inl ⟨n, hbound, htrue⟩
        · exact Or.inr ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue, hlit⟩
  | @cut α βφ βψ e H f c Γ χ hcompl _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc _
      exact absurd hcompl (by omega)

/-- **`headline_readoff_Zef`** — the slot-calculus exit: a rank-0 `Zef` root deriving `{∃⁰ φ}`
yields a numeric witness `≤ f 0`.  The slot-form of `headline_readoff`; the numeric content of
the whole derivation is carried in `f 0` (E–W). -/
theorem headline_readoff_Zef {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    (dd : Zef α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n]) := by
  have hshape : ReadoffShapeF φ f {(∃⁰ φ)} := by
    intro ψ hψ
    rw [Finset.mem_singleton] at hψ
    exact Or.inl hψ
  rcases readoff_sigma1_Zef hφinst dd rfl hshape with h | ⟨ψ, hψ, _, ⟨ar, r, v, hlit⟩⟩
  · exact h
  · rw [Finset.mem_singleton] at hψ
    subst hψ
    rcases hlit with h | h <;> exact absurd h (by simp [ExsQuantifier.exs])


/-! ## §8 The stage→slot embedding `Zeh → Zef` (P4 consolidation; the LOCK §1-A1/§3 amendment
made faithful — `Zef` conservatively generalizes `Zeh`)

The ℕ-stage judgment `Zeh` embeds into the function-slot judgment `Zef` at the **root slot**
`rel1 (hardy e) m` (so `f 0 = hardy e (max m 0) = hardy e m`: the read-off bound is preserved,
LOCK §4).  The `allω` branch threads by `rel1_rel1` (stage `max m n` ⤳ slot
`rel1 (rel1 (hardy e) m) n = rel1 (hardy e) (max m n)`); the `exI` bound
`n ≤ hardy e m = (rel1 (hardy e) m) 0` is definitional.  This is the kernel witness that the
lap-184 amendment is a CONSERVATIVE generalization — every stage-`m` derivation is a slot
derivation at the canonical slot — so nothing the stage calculus proved is lost. -/

/-- **Stage→slot embedding `Zeh → Zef`** at the root slot `rel1 (hardy e) m`.  Witnesses that the
LOCK §1-A1/§3 amendment (ℕ-stage ⤳ function-slot) is a conservative generalization. -/
theorem zeh_to_zef {α e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (d : Zeh α e H m c Γ) : Zef α e H (rel1 (hardy e) m) c Γ := by
  induction d with
  | axL r v hp hn => exact Zef.axL r v hp hn
  | wk hsub _ ih => exact Zef.wk hsub ih
  | weak hβ hβNF hαNF hβH hsub _ ih => exact Zef.weak hβ hβNF hαNF hβH hsub ih
  | @allω α e H m c Γ φ β hβ hβNF hαNF hβH dd ih =>
      refine Zef.allω φ β hβ hβNF hαNF hβH (fun n => ?_)
      rw [rel1_rel1]
      exact ih n
  | @exI α β e H m c Γ φ n hβ hβNF hαNF hβH hbound dd ih =>
      refine Zef.exI φ n hβ hβNF hαNF hβH ?_ ih
      simpa [rel1] using hbound
  | @cut α βφ βψ e H m c Γ φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      exact Zef.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

/-! ## §8b The two W4B seams, now in the SLOT judgment `Zef` (§6 migration complete)

The stage-form seam probes (`two_level_config_Zeh`, `probe_allomega_reassembly_Zf`) re-expressed
natively in `Zef` — the calculus the cut-elimination assembly (laps 5–7) will operate in.  In the
slot judgment the numeric control IS the slot, so the reassembly needs no separate `NormControlled`
conjunct: each ω-branch simply runs at the relativized slot `rel1 f n`. -/

/-- **Non-vacuity in the slot judgment (slot form of `two_level_config_Zeh`, sorry-free).**  ONE
`allω` node at `ω^ω` whose every branch is a rank-`c` principal ∀/∃ cut with premise ordinals
`ω·(n+1)` — the branch-unbounded configuration that killed the `(k,d)` calculus, a legal `Zef`
derivation at an arbitrary slot `f`. -/
theorem two_level_config_Zef {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (χ ψ : ArithmeticSemiformula ℕ 1) {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    Zef (expTower ONote.omega) e H f ((∀⁰ χ).complexity + 1) (insert (∀⁰ ψ) Γ) := by
  refine Zef.allω ψ (fun n => osucc (wmul n))
    (fun n => osucc_wmul_lt_expTower_omega n)
    (fun n => osucc_NF (wmul_NF n))
    (expTower_NF omegaO_NF)
    (fun n => Cl.osucc (wmul_mem _ n))
    (fun n => ?_)
  refine Zef.cut (∀⁰ χ) (Nat.lt_succ_self _)
    (Zekd.lt_osucc (wmul_NF n)) (Zekd.lt_osucc (wmul_NF n))
    (wmul_NF n) (wmul_NF n) (osucc_NF (wmul_NF n))
    (wmul_mem _ n) (wmul_mem _ n) ?_ ?_
  · exact Zef.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))
  · exact Zef.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))

/-- **Seam-2 reassembly in the slot judgment (slot form of `probe_allomega_reassembly_Zf`,
sorry-free).**  The ω-node re-assembles over the reduction-output class, each branch's control
carried by the relativized slot `rel1 f n` — the branch-unbounded demand that overflowed the
`(k,d)` counter, now paid by the function slot inside the judgment (no separate control conjunct). -/
theorem probe_allomega_reassembly_Zef {e : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {f : ℕ → ℕ}
    (dd : ∀ n, Zef (osucc (wmul n + wmul n)) e (adjoin H n) (rel1 f n) c
      (insert (χ/[nm n]) Γ)) :
    Zef (expTower ONote.omega) e H f c (insert (∀⁰ χ) Γ) := by
  refine Zef.allω χ (fun n => osucc (wmul n + wmul n))
    (fun n => ?_) (fun n => ?_) (expTower_NF omegaO_NF)
    (fun n => Cl.osucc (Cl.add (wmul_mem (adjoin H n) n) (wmul_mem (adjoin H n) n))) dd
  · rw [wmul_add_wmul]
    exact osucc_omega_coeff_lt _
  · rw [wmul_add_wmul]
    exact osucc_NF (nf_one.oadd _ NFBelow.zero)

/-! ## §8c Propositional inversions in the slot judgment `Zef` (assembly prerequisite)

Slot-form ports of `orInv_Zeh`/`andInvL_Zeh`/`andInvR_Zeh` — the propositional inversions the
cut-elimination assembly (laps 5–7) reuses for cuts on `⋏`/`⋎` formulas.  Control-preserving (same
`(α, e, H, f, c)`); since the minimal core has no `andI`/`orI` intro rule, `φ ⋏ ψ` / `φ ⋎ ψ` is
never principal, so every case threads the inversion past a passive side formula.  Completes the
`Zef` inversion suite (`allInv_Zef` + these three), mirroring the banked `Zeh` suite. -/

/-- **∨-inversion, `Zef` form** (Towsner §19.3): replace `φ ⋎ ψ` by `φ, ψ`, same
`(α, e, H, f, c)`. -/
theorem orInv_Zef {φ ψ : ArithmeticFormula ℕ} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zef α e H f c Γ → (φ ⋎ ψ) ∈ Γ →
    Zef α e H f c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      intro _
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩))
  | @wk α e H f c Δ Γ hsub dd ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.insert_subset_insert _
          (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zef.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmem
      by_cases hd : (φ ⋎ ψ) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF hβH (Finset.insert_subset_insert _
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))) (ih hd)
      · refine Zef.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩))
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [UnivQuantifier.all, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c
          (insert (χ/[nm n]) (insert φ (insert ψ (Γ₀.erase (φ ⋎ ψ))))) := fun n =>
        Zef.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zef.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋎ ψ) := by intro h; simp [ExsQuantifier.exs, Vee.vee] at h
      have hmem0 : (φ ⋎ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (invPush (φ ⋎ ψ) (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (invPull (φ ⋎ ψ) hhead Γ₀) (Zef.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zef.wk (invPush (φ ⋎ ψ) χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (invPush (φ ⋎ ψ) (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, left, `Zef` form** (Towsner §19.3): replace `φ ⋏ ψ` by `φ`, same
`(α, e, H, f, c)`. -/
theorem andInvL_Zef {φ ψ : ArithmeticFormula ℕ} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zef α e H f c Γ → (φ ⋏ ψ) ∈ Γ →
    Zef α e H f c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      intro _
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c
          (insert (χ/[nm n]) (insert φ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zef.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-- **∧-inversion, right, `Zef` form** (Towsner §19.3): replace `φ ⋏ ψ` by `ψ`, same
`(α, e, H, f, c)`. -/
theorem andInvR_Zef {φ ψ : ArithmeticFormula ℕ} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zef α e H f c Γ → (φ ⋏ ψ) ∈ Γ →
    Zef α e H f c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar r v hp hn =>
      intro _
      refine Zef.axL r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.wk (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.wk ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hβ hβNF hαNF hβH hsub dd ih =>
      intro hmem
      by_cases hh : (φ ⋏ ψ) ∈ Δ
      · exact Zef.weak hβ hβNF hαNF hβH
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hh)
      · refine Zef.weak hβ hβNF hαNF hβH ?_ dd
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ χ β hβ hβNF hαNF hβH dd ih =>
      intro hmem
      have hhead : (∀⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [UnivQuantifier.all, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have key : ∀ n, Zef (β n) e (adjoin H n) (rel1 f n) c
          (insert (χ/[nm n]) (insert ψ (Γ₀.erase (φ ⋏ ψ)))) := fun n =>
        Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih n (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.allω χ β hβ hβNF hαNF hβH key)
  | @exI α β e H f c Γ₀ χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmem
      have hhead : (∃⁰ χ) ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
      have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef.wk (inv1Push (φ ⋏ ψ) _ (χ/[nm n]) Γ₀) (ih (Finset.mem_insert_of_mem hmem0))
      exact Zef.wk (inv1Pull (φ ⋏ ψ) _ hhead Γ₀) (Zef.exI χ n hβ hβNF hαNF hβH hbound P)
  | @cut α βφ βψ e H f c Γ₀ χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmem
      have P₁ := Zef.wk (inv1Push (φ ⋏ ψ) _ χ Γ₀) (ih₁ (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef.wk (inv1Push (φ ⋏ ψ) _ (∼χ) Γ₀) (ih₂ (Finset.mem_insert_of_mem hmem))
      exact Zef.cut χ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH P₁ P₂

/-! ## §8d Assembly plumbing in the slot judgment `Zef` (safe pre-ratification infrastructure)

Slot-form ports of `Zeh.mono_c` (cut-rank monotonicity) and the `ZehProv` wrapper combinators
(`cut`/`exI`/`allω`) — the structural layer the cut-elimination assembly (laps 5–7) reuses to
introduce cuts before eliminating them and to rebuild ω-nodes.  None consumes pin 3 or raises the
control; all reuse the `Zeh`-agnostic ONote splice bricks (`osucc_add_NF`, `add_le_add_NF`, …). -/

/-- **`c`-monotonicity** (cut rank): a derivation valid at rank `c` is valid at any `c' ≥ c`.
Only the `cut` rule reads `c` (via `hcompl : φ.complexity < c`), so every other case threads. -/
theorem Zef.mono_c : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
    Zef α e H f c Γ → ∀ {c' : ℕ}, c ≤ c' → Zef α e H f c' Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL r v hp hn => intro c' _; exact Zef.axL r v hp hn
  | wk hsub _ ih => intro c' hc; exact Zef.wk hsub (ih hc)
  | weak hβ hβNF hαNF hβH hsub _ ih => intro c' hc; exact Zef.weak hβ hβNF hαNF hβH hsub (ih hc)
  | allω φ β hβ hβNF hαNF hβH _ ih =>
      intro c' hc; exact Zef.allω φ β hβ hβNF hαNF hβH (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro c' hc; exact Zef.exI φ n hβ hβNF hαNF hβH hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zef.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁ hc) (ih₂ hc)

/-- **`ZefProv`-level cut combinator** (assembly plumbing, NOT the gated reduction): package
the cut RULE at the wrapper level — combine proofs of `φ` and `∼φ` (with `φ.complexity < c`)
into a proof of `Γ` at ordinal `osucc (βφ + βψ)`, SAME rank and control (no rank-lowering, no
control-raise — those are the judge-gated `cutElimPass_Zf`/reduction).  The step/reduction
assembly reuses this to introduce cuts before eliminating them. -/
theorem ZefProv.cut {βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ}
    {Γ : Finset (ArithmeticFormula ℕ)} (φ : ArithmeticFormula ℕ)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hcompl : φ.complexity < c)
    (D₁ : ZefProv βφ e H f c (insert φ Γ)) (D₂ : ZefProv βψ e H f c (insert (∼φ) Γ)) :
    ZefProv (osucc (βφ + βψ)) e H f c Γ := by
  obtain ⟨α₁, hle₁, hNF₁, hH₁, d₁⟩ := D₁
  obtain ⟨α₂, hle₂, hNF₂, hH₂, d₂⟩ := D₂
  refine ⟨osucc (α₁ + α₂),
    osucc_le_osucc (ONote.add_nf α₁ α₂) (ONote.add_nf βφ βψ)
      (add_le_add_NF hNF₁ hβφNF hNF₂ hβψNF hle₁ hle₂),
    osucc_add_NF hNF₁ hNF₂, osucc_add_mem hH₁ hH₂,
    Zef.cut φ hcompl
      (lt_of_le_of_lt (Zekd.le_add_right_NF hNF₁ hNF₂) (Zekd.lt_osucc (ONote.add_nf α₁ α₂)))
      (lt_of_le_of_lt (Zekd.le_add_left_NF hNF₁ hNF₂) (Zekd.lt_osucc (ONote.add_nf α₁ α₂)))
      hNF₁ hNF₂ (osucc_add_NF hNF₁ hNF₂) hH₁ hH₂ d₁ d₂⟩

/-- **`ZefProv`-level `exI` combinator** (assembly plumbing): package the `∃`-rule at the
wrapper level — the output ordinal `osucc β` is fully determined, no rank/control change.
Reused by the assembly to introduce existentials at the prov level. -/
theorem ZefProv.exI {β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβNF : β.NF) (hβH : Cl H β)
    (hbound : n ≤ f 0) (D : ZefProv β e H f c (insert (φ/[nm n]) Γ)) :
    ZefProv (osucc β) e H f c (insert (∃⁰ φ) Γ) := by
  obtain ⟨β', hle, hNF', hH', d⟩ := D
  exact ⟨osucc β, le_rfl, osucc_NF hβNF, Cl.osucc hβH,
    Zef.exI φ n (lt_of_le_of_lt hle (Zekd.lt_osucc hβNF)) hNF' (osucc_NF hβNF) hH' hbound d⟩

/-- **`ZefProv`-level `allω` combinator** (assembly plumbing): reassemble an ω-node at the
wrapper level.  Each branch's `≤`-slack witness is threaded through (`< α` survives since
`β' n ≤ β n < α`); the output witness is `α` itself (needs `Cl H α`).  Reused by the
assembly to rebuild ω-nodes over the branch family. -/
theorem ZefProv.allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
    (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
    (hβ : ∀ n, β n < α) (hαNF : α.NF) (hαH : Cl H α)
    (D : ∀ n, ZefProv (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
    ZefProv α e H f c (insert (∀⁰ φ) Γ) :=
  ⟨α, le_rfl, hαNF, hαH,
    Zef.allω φ (fun n => (D n).choose)
      (fun n => lt_of_le_of_lt (D n).choose_spec.1 (hβ n))
      (fun n => (D n).choose_spec.2.1)
      hαNF
      (fun n => (D n).choose_spec.2.2.1)
      (fun n => (D n).choose_spec.2.2.2)⟩

/-! ## Blueprint ledger — the DISCHARGED reduction pins (lap 184)

Pins 1–2 are now `clean` nodes (real kernel footprint = trust base only); the audit reconciles
their claimed status against `Lean.collectAxioms`.  Pin 3 (`cutElimPass_Zf`) stays `notready`
(`sorryAx`-bearing) until its lap-5 restatement lands. -/

attribute [goodstein_blueprint 12 clean "zeh_reduction_pin1" "0" 100 cutReduceAllAuxRunning_Zf
  []
  ["Eguchi–Weiermann arXiv:1205.2879 Lemma 25 (compose the slot at a principal cut)",
   "Towsner §19.6 running-family cut-reduction; output slot g∘f at FIXED control",
   "REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md: discharged in the Zef function-slot judgment; the ℕ-stage Zeh form was kernel-refuted (principal_witness_exceeds_stage), R4-noncompliant"]
  "Pin 1: the running-family cut-reduction, function-slot form (fixed control, output slot g∘f). Discharged sorry-free lap 184."]
  cutReduceAllAuxRunning_Zf

attribute [goodstein_blueprint 13 clean "zeh_step_pin2" "0" 100 stepAllω_Zf
  []
  ["Eguchi–Weiermann arXiv:1205.2879 Lemma 25; the common-control ∀/∃ step",
   "Q3-unified (one ⋁-principal reduction; the ∀-side enters via allInv_Zef)",
   "REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md: discharged in the Zef function-slot judgment"]
  "Pin 2: the common-control ∀/∃ step motive, function-slot form. Discharged sorry-free lap 184 (feeds pin 1 via allInv_Zef inversion)."]
  stepAllω_Zf

end GoodsteinPA.OperatorZeh
