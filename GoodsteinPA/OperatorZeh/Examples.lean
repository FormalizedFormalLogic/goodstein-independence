module

public import GoodsteinPA.OperatorZeh.Slot
public import GoodsteinPA.OperatorZeh.Zef

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-- **(K2a)** The finite part of every closure is ALL of ℕ — so an `exI` designation
"some `m ∈ H ∩ ℕ`" would designate nothing (the stage is judgment-carried instead). -/
theorem finite_part_unbounded (S : ONote → Prop) : ∀ m : ℕ, Cl S (ONote.ofNat m) :=
  Cl.ofNat

/-- The additive raise genuinely absorbs a numeral base (kernel-computed):
`raise (ofNat 5) 1 = ofNat 5 + ω = ω`. -/
theorem raise_absorbs_base : raise (ONote.ofNat 5) 1 = ONote.omega := rfl

/-- **(K2b) The membership-gated `mono_e` is kernel-refuted.**  There are `e < e'` (indeed
`e' = raise e 1`), both normal-form, both in EVERY closure, with
`hardy e' m < hardy e m`: `hardy ω 0 = 1 < 5 = hardy (ofNat 5) 0`.  So no `Zeh`-rule
package of (NF, `<`, membership) facts can re-establish the `exI` bound after a raise —
`Zekd.mono_e`'s numeric gate `norm e ≤ k + d` does not "become `e ∈ H`"; the domination
content must come from elsewhere. -/
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
coefficient).  So (K1) is not a representation artifact: no concrete `H` can satisfy the
closure conditions and certify a norm bound. -/
theorem norm_ball_not_add_closed (R : ℕ) (hR : 1 ≤ R) :
    ∃ α β : ONote, norm α ≤ R ∧ norm β ≤ R ∧ R < norm (α + β) := by
  refine ⟨wmul (R - 1), wmul (R - 1), by rw [norm_wmul]; omega, by rw [norm_wmul]; omega, ?_⟩
  rw [wmul_add_wmul, norm_oadd, norm_one, norm_zero]
  have : ((R - 1).succPNat + (R - 1).succPNat : ℕ+) = (2 * R : ℕ) := by
    simp [Nat.succPNat, PNat.add_coe]
    omega
  omega

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

/-- **The bare `∃`-slot is vacuous.**  For any control `e` and stage `m`,
`∃ f, NormControlled f e m` holds trivially — the Hardy witness itself is a slot.
Consequence: a bare existential slot conjunct `∃ f', NormControlled f' (raise e α') m` adds no
quantitative content, so the read-off (E–W Lemma 31, `witness ≤ f(0)`) forces `f'` to be pinned
to the E–W iterate of the input `f`, not left existential — which is why `cutElimPass_Zf`'s
restatement is expected to output `iterSlot f α`, not `∃ f'`. -/
theorem normControlled_exists_trivial (e : ONote) (m : ℕ) :
    ∃ f : ℕ → ℕ, NormControlled f e m :=
  ⟨fun x => hardy e (max m x), fun _ => le_rfl⟩

/-! ## The two seams re-expressed in the f-form

The seam probes re-run against the f-slot statements.  If either seam failed to compose here
it would show the E–W carrier failing where the ℕ-slots failed — no third carrier pinned.  It
does not: both close as real proofs. -/

/-- **Seam 1 absorbed by composition**: a ℕ-slot `D` cannot pay `dd + x + 1 ≤ D` for every `dd`,
but the composed function slot does — the reduction's `+ norm α + 1`-class output bump re-enters
the composed slot, which pays any structural bump exactly. -/
theorem seam1_bump_absorbed_by_composition (x : ℕ) :
    ∃ g : ℕ → ℕ, ∀ dd : ℕ, dd + x + 1 ≤ g dd :=
  ⟨fun dd => dd + x + 1, fun _ => le_rfl⟩

/-- **Seam 2 absorbed by a function slot**: no ℕ-slot `D` pays this family's branch-`n` demand
uniformly, but the two-level configuration's branch-`n` demand is paid by one function-valued
slot evaluated through its own relativization. -/
theorem seam2_function_slot_payable (dBase eNorm : ℕ) :
    ∃ f : ℕ → ℕ, ∀ n : ℕ, (dBase + eNorm + 1) + norm (expTower (wmul n)) + 1 ≤ rel1 f n 0 := by
  refine ⟨fun x => dBase + eNorm + x + 3, fun n => ?_⟩
  have h : norm (expTower (wmul n)) = n + 1 := by
    rw [norm_expTower, norm_wmul]; omega
  rw [h]
  simp [rel1]
  omega

/-- **Non-vacuity (the two-level configuration, `Zeh` form; sorry-free).**  ONE `allω`
node at `ω^ω` whose EVERY branch `n` is a rank-`c` principal ∀/∃ cut with premise ordinals
`ω·(n+1)` — the branch-unbounded configuration that killed the `(k,d)` calculus, realized as
a legal `Zeh` derivation: every side condition is a membership, discharged by a REAL
per-branch closure tree.  This is the inhabitedness witness the seam-2 reversal rests on
(the reassembly probe would be vacuous without it). -/
theorem two_level_config_Zeh {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (χ ψ : ArithmeticSemiformula ℕ 1) {e : ONote} {H : ONote → Prop} {m : ℕ} {Γ : Seq}
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
`rel1 f n` (`normControlled_rel1`) — the numeric control rides the function slot the seam
demands. -/
theorem probe_allomega_reassembly_Zf {e : ONote} {H : ONote → Prop} {m c : ℕ} {Γ : Seq}
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

/-! ## The two seams, now in the slot judgment `Zef`

The stage-form seam probes (`two_level_config_Zeh`, `probe_allomega_reassembly_Zf`) re-expressed
natively in `Zef`.  In the slot judgment the numeric control is the slot, so the reassembly
needs no separate `NormControlled` conjunct: each ω-branch simply runs at the relativized slot
`rel1 f n`. -/

/-- **Non-vacuity in the slot judgment (slot form of `two_level_config_Zeh`, sorry-free).**  ONE
`allω` node at `ω^ω` whose every branch is a rank-`c` principal ∀/∃ cut with premise ordinals
`ω·(n+1)` — the branch-unbounded configuration that killed the `(k,d)` calculus, a legal `Zef`
derivation at an arbitrary slot `f`. -/
theorem two_level_config_Zef {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (χ ψ : ArithmeticSemiformula ℕ 1) {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq}
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
theorem probe_allomega_reassembly_Zef {e : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Seq}
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

end GoodsteinPA.OperatorZeh
