/-
# SPIKE W4B — the principal ∀/∃ `d`-BUDGET composition probe (operator-commissioned, 2026-07-02)

Deciding experiment #3 (`SPIKE-W4B-BUDGET.md`), resolving the residual SPIKE-W4 located
(`SPIKE-W4-VERDICT.md` §"the residual"): **does the numeric `(k, d)` budget calculus admit ANY
statement-level fix for the principal ∀/∃ cut's `d`-bump under an enclosing ω-node, or does the
overflow kernel-confirm — forcing the Buchholz operator-controlled (`Zᵉ`) redesign?**

This file is a **minimal kernel probe of ONE composition point**, NOT a proof campaign:

* §1 pins the RUNNING-family generalization of the banked `cutReduceAllAux`
  (`OperatorZinfty.lean:789`, fixed `k₀` → running `max k₀ n`, control raised per SPIKE-W4's
  `raise`), body `sorry` — only its statement-level budget shape is under test.
* §2 rail-checks that pinned output budget on concrete/parametric `ONote`s: the
  `osucc (α + γ)`-class output ordinal GENUINELY carries `norm α` (equal-exponent CNF merge is
  additive in the head coefficient), so the `+ norm α + 1` bump is not bookkeeping that a
  tighter statement could shed — this kernel-refutes dodge (a).
* §3 exhibits the two-level configuration (principal ∀/∃ cut under one `allω`) as a REAL,
  sorry-free `Zekd` derivation whose branch-`n` cut premises have norm `n + 1`:
  branch-unbounded, exactly the residual's shape.
* §4 is the composition probe: the ∀/∃ arm of `step_cut_principal` consuming §1's output is a
  REAL proof (`probe_cut_all_arm`) recording what the arm CAN emit — the slot inflated by
  `norm αf + 1` at a doubled control; the seam lemmas then kernel-check that this can NEVER meet
  the motive's demands (seam 1: uniform slot; seam 2: the ω-node's single-`d` re-assembly).
* §5 kernel-refutes the remaining candidate dodges: (b) ordinal-indexed slot (dies at TWO seams:
  `norm` is not `<`-monotone, and the ω-family premise norms are unbounded), (c) `k`-rebalance
  (dies at `Zekd.allω`'s exact-index discipline), + the control-side seams of the pinned raise
  shape (unconditional overshoot; fam-exponent escape).

**Outcome (see `SPIKE-W4B-VERDICT.md`): FAIL — T-W4B fires.** Every candidate shape's failing
inequality is reduced below to a kernel-checked counterexample or a named unsatisfiable side
condition; none of the probes is `sorry`ed except the §1 statement pin itself (disclosed).

Standing doctrine honored: no `src/` edits, no new `axiom` declarations, no someK-level
induction; budgets in a motive are functions of structure, never of a branch index — the probe
shows precisely that no such function exists for this node.
-/
import GoodsteinPA.OperatorZinfty

namespace GoodsteinPA.SpikeW4B

open LO LO.FirstOrder ONote
open GoodsteinPA.FastGrowing
open GoodsteinPA.OperatorZinfty

/-! ## §0 The SPIKE-W4 transforms (duplicated from `wip/SpikeW4CutElim.lean`, which is not an
importable module; definitions are identical). -/

/-- `ω^α` as an explicit `ONote` (`oadd α 1 0`) — SPIKE-W4's ordinal transform. -/
def expTower (α : ONote) : ONote := oadd α 1 0

theorem expTower_NF {α : ONote} (hα : α.NF) : (expTower α).NF :=
  hα.oadd 1 NFBelow.zero

theorem expTower_lt_expTower {β α : ONote} (hβ : β.NF) (h : β < α) :
    expTower β < expTower α :=
  oadd_lt_oadd_1 (expTower_NF hβ) h

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

theorem norm_raise_le {e α : ONote} (he : e.NF) (hα : α.NF) :
    norm (raise e α) ≤ norm e + max (norm α) 1 := by
  have h := Zekd.norm_add_le he (expTower_NF hα)
  simpa [raise] using h

/-! ## §1 The pinned RUNNING-family reduction statement (spike objective #1)

The banked `cutReduceAllAux` (`OperatorZinfty.lean:789`) takes the ∀-inversion family `fam` at a
FIXED index `k₀` with the control `e` inert.  The recursion's `allInv` hands the family at the
RUNNING index `max k₀ n` (`OperatorZinfty.lean:2209`), and re-deriving `fam n` at the ∃-side cut
site (index `k' ≥ k₀`, but `k'` unrelated to the witness `n`) is exactly the `:764` witness-budget
gap — the numeric single-index bound is provably false there, so the statement must RAISE the
control (per SPIKE-W4's `raise`), which is what this pin does.

**Output shape** (explicit, per the work order): ordinal `osucc (α + γ)` — the `§19.6`-class
splice ordinal; control `raise e α`; budget `dd + norm α + 1`.

**Admissibility rail** (the honesty bar): the output budget CANNOT be smaller than
`dd + norm α + 1`-class, because the output ordinal's OWN norm genuinely reaches
`norm α + norm γ` (equal-exponent CNF merge; kernel-checked in §2 below) and the wrapper
carries `norm α' < k + d_out`.  A statement shedding the `norm α` contribution would be a fake
PASS — §2 `rail_norm_genuinely_carried` / `dodge_a_norm_not_sheddable` refute it.

**Disclosed caveats** (statement-level, flagged for the verdict): (i) the body is `sorry` — the
probe tests the COMPOSITION arithmetic, not the reduction port (forbidden by the work order);
(ii) even the raised control may be witness-insufficient (`hardy (raise e α) ≥ hardy e ∘ hardy e`
is NOT implied when `ω^α < e`) — this pin is the MOST GENEROUS plausible member of its class,
and the composition below fails even so. -/
theorem cutReduceAllAuxRunning {φ : SyntacticSemiformula ℒₒᵣ 1} {c k₀ dd₀ : ℕ} {α e : ONote}
    {Γ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (fam : ∀ n, Zekd α e (max k₀ n) dd₀ c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {k dd : ℕ} {Δ : Seq}, Zekd γ e k dd c Δ → γ.NF → norm γ < k + dd →
      k₀ ≤ k → dd₀ ≤ dd → (∃⁰ ∼φ) ∈ Δ →
      ZekdProv (osucc (α + γ)) (raise e α) k (dd + norm α + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  sorry

/-! ## §2 The admissibility rail, kernel-checked (refutes dodge (a))

Concrete `ONote` family: `wmul m := ω·(m+1)` (`norm = m + 1`).  Equal-exponent CNF addition
merges head coefficients — `ω·(a+1) + ω·(b+1) = ω·(a+b+2)` — so `norm (osucc (α + γ))` reaches
`norm α + norm γ` EXACTLY: the `∀`-side family ordinal's norm is genuinely carried by the output
ordinal, not bookkeeping.  All computations are parametric `rfl`/`omega` (stronger than
single-point `decide`). -/

/-- `ω·(m+1)` as an explicit `ONote`. -/
def wmul (m : ℕ) : ONote := oadd 1 m.succPNat 0

theorem wmul_NF (m : ℕ) : (wmul m).NF := nf_one.oadd m.succPNat NFBelow.zero

@[simp] theorem norm_one : norm (1 : ONote) = 1 := rfl

@[simp] theorem norm_wmul (m : ℕ) : norm (wmul m) = m + 1 := by
  rw [wmul, norm_oadd, norm_one, norm_zero, Nat.succPNat_coe]
  omega

@[simp] theorem norm_expTower_wmul (m : ℕ) : norm (expTower (wmul m)) = m + 1 := by
  rw [norm_expTower, norm_wmul]; omega

/-- Equal-exponent CNF merge, parametric (kernel-computed). -/
theorem wmul_add_wmul (a b : ℕ) :
    wmul a + wmul b = oadd 1 (a.succPNat + b.succPNat) 0 := rfl

/-- `osucc` on an `ω·K`-notation appends `+1` (kernel-computed). -/
theorem osucc_wmul_sum (K : ℕ+) : osucc (oadd 1 K 0) = oadd 1 K 1 := rfl

/-- **THE RAIL**: the `osucc (α + γ)`-class output ordinal's own norm equals
`norm α + norm γ` on the merge family — the `norm α` contribution is genuinely carried. -/
theorem rail_norm_genuinely_carried (a b : ℕ) :
    norm (osucc (wmul a + wmul b)) = (a + 1) + (b + 1) := by
  rw [wmul_add_wmul, osucc_wmul_sum, norm_oadd, norm_one, PNat.add_coe,
    Nat.succPNat_coe, Nat.succPNat_coe]
  omega

/-- **Dodge (a) refuted, parametrically**: NO constant `C` (hence no structural functional
evaluated at a fixed configuration) lets the output-wrapper norm ride the ∃-side `γ` alone:
`norm (osucc (α + γ)) > norm γ + C` already at `α := wmul (C+1)`, `γ := wmul 0` — while `α` stays
a legitimate ∀-side family ordinal (cf. §3).  The bump `+ norm α + 1` is genuine. -/
theorem dodge_a_norm_not_sheddable (C : ℕ) :
    norm (wmul 0) + C < norm (osucc (wmul (C + 1) + wmul 0)) := by
  rw [rail_norm_genuinely_carried, norm_wmul]
  omega

/-! ## §3 The two-level configuration is REAL (non-vacuity witness)

A sorry-free `Zekd` derivation: ONE `allω` node (ordinal `ω^ω`, base index `k = 0`, `d = 3`)
whose EVERY branch `n` is a rank-`c` principal ∀/∃ cut (cut formula `∀⁰ χ`, complexity `= c`)
with premise ordinals `wmul n = ω·(n+1)` — premise norms `n + 1`, i.e. **branch-unbounded**,
legal because the branch sits at index `max 0 n` (the rule's own `hτ` is `norm < max k n + d`).
This is exactly the configuration the step recursion must traverse, with the residual's
branch-dependent quantity realized in the kernel.  Leaves are `axL` (the probe needs the SHAPE,
not deep sub-derivations). -/

theorem one_lt_omegaO : (1 : ONote) < ONote.omega :=
  oadd_lt_oadd_1 nf_one ONote.zero_lt_one

theorem omegaO_NF : (ONote.omega).NF := nf_one.oadd 1 NFBelow.zero

theorem wmul_lt_expTower_omega (m : ℕ) : wmul m < expTower ONote.omega :=
  oadd_lt_oadd_1 (wmul_NF m) one_lt_omegaO

theorem osucc_wmul_lt_expTower_omega (m : ℕ) : osucc (wmul m) < expTower ONote.omega := by
  have h : (osucc (wmul m)).NF := osucc_NF (wmul_NF m)
  rw [show osucc (wmul m) = oadd 1 m.succPNat 1 from rfl] at h ⊢
  exact oadd_lt_oadd_1 h one_lt_omegaO

/-- The two-level configuration: `allω` over branch-indexed principal ∀/∃ cuts whose premise
norms grow with the branch.  Sorry-free; any `e`, any relation pair in `Γ`. -/
theorem two_level_config {ar : ℕ} (r : (ℒₒᵣ).Rel ar) (v : Fin ar → SyntacticTerm ℒₒᵣ)
    (χ ψ : SyntacticSemiformula ℒₒᵣ 1) {e : ONote} {Γ : Seq}
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    Zekd (expTower ONote.omega) e 0 3 ((∀⁰ χ).complexity + 1) (insert (∀⁰ ψ) Γ) := by
  refine Zekd.allω ψ (fun n => osucc (wmul n))
    (fun n => osucc_wmul_lt_expTower_omega n)
    (fun n => osucc_NF (wmul_NF n))
    (expTower_NF omegaO_NF)
    (fun n => ?_) (fun n => ?_)
  · -- node-side norm budget: norm (osucc (ω·(n+1))) ≤ n + 2 < max 0 n + 3
    have h1 : norm (osucc (wmul n)) ≤ n + 2 := by
      have h := norm_osucc_le (o := wmul n)
      rw [norm_wmul] at h; omega
    have h2 : n ≤ max 0 n := le_max_right 0 n
    omega
  · -- branch n: the rank-c principal ∀/∃ cut, premise ordinals ω·(n+1) (norm n+1)
    refine Zekd.cut (∀⁰ χ) (Nat.lt_succ_self _)
      (Zekd.lt_osucc (wmul_NF n)) (Zekd.lt_osucc (wmul_NF n))
      (wmul_NF n) (wmul_NF n) (osucc_NF (wmul_NF n)) ?_ ?_ ?_ ?_
    · rw [norm_wmul]; have := le_max_right 0 n; omega
    · rw [norm_wmul]; have := le_max_right 0 n; omega
    · exact Zekd.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))
    · exact Zekd.axL r v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hn))

/-- The ω-node itself satisfies the step motive's package (`norm (ω^ω) = 1 < k + d`). -/
theorem config_node_norm : norm (expTower ONote.omega) < 0 + 3 := by
  rw [norm_expTower, show norm ONote.omega = 1 from rfl]
  omega

/-! ## §4 The composition probe (spike objective #2): both seams, kernel-checked

The ∀/∃ arm of `step_cut_principal` at an ω-branch (node ordinal `B`, branch index `max k nBr`,
IHs at SPIKE-W4's slot `d + norm e + 1`) consuming §1's output.  `probe_cut_all_arm` is a REAL
proof (its only `sorry`-dependence is the §1 pin): it kernel-checks the seam-1 max-algebra —
`mono_e` control unification budgets, `allInv`'s running-index discipline feeding §1's family
shape EXACTLY, the reduction application, the sequent cleanup — and records what the arm CAN
emit.  The seam lemmas then show the emission can never meet the motive. -/

/-- **Seam-1 record (positive half)**: the arm CAN emit — but only at the slot inflated by
`norm αf + 1` (with `norm αf` bounded ONLY branch-dependently: `< max k nBr + (d + norm e + 1)`,
the wrapper's carried clause) and at the DOUBLED control `raise (raise e B) αf`.
The motive demands slot `d + norm e + 1` and control `raise e B`. -/
theorem probe_cut_all_arm {e βφ βψ B : ONote} {k d c nBr : ℕ} {Γ : Seq}
    {χ : SyntacticSemiformula ℒₒᵣ 1}
    (heNF : e.NF) (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hBNF : B.NF)
    (hβφ : βφ < B) (hβψ : βψ < B)
    (hτφ : norm βφ < max k nBr + d) (hτψ : norm βψ < max k nBr + d)
    (hχc : χ.complexity < c)
    (IH1 : ZekdProv (expTower βφ) (raise e βφ) (max k nBr) (d + norm e + 1) c
      (insert (∀⁰ χ) Γ))
    (IH2 : ZekdProv (expTower βψ) (raise e βψ) (max k nBr) (d + norm e + 1) c
      (insert (∃⁰ ∼χ) Γ)) :
    ∃ αf γf : ONote,
      αf.NF ∧ αf ≤ expTower βφ ∧ norm αf < max k nBr + (d + norm e + 1) ∧
      ZekdProv (osucc (αf + γf)) (raise (raise e B) αf) (max k nBr)
        ((d + norm e + 1) + norm αf + 1) c Γ := by
  obtain ⟨α₁, hle₁, hNF₁, hnorm₁, D₁⟩ := IH1
  obtain ⟨γ₁, hle₂, hNF₂, hnorm₂, D₂⟩ := IH2
  have hENF : (raise e B).NF := raise_NF heNF hBNF
  -- unify both IH controls at the node-level single raise `raise e B` (mono_e; budget from
  -- norm_raise_le + the cut rule's own hτ — the same algebra step_allω kernel-checked)
  have D₁' : Zekd α₁ (raise e B) (max k nBr) (d + norm e + 1) c (insert (∀⁰ χ) Γ) := by
    refine D₁.mono_e (raise_NF heNF hβφNF) hENF (raise_lt_raise heNF hβφNF hBNF hβφ) ?_
    have h1 := norm_raise_le heNF hβφNF
    omega
  have D₂' : Zekd γ₁ (raise e B) (max k nBr) (d + norm e + 1) c (insert (∃⁰ ∼χ) Γ) := by
    refine D₂.mono_e (raise_NF heNF hβψNF) hENF (raise_lt_raise heNF hβψNF hBNF hβψ) ?_
    have h1 := norm_raise_le heNF hβψNF
    omega
  -- the RUNNING family, exactly §1's input shape: allInv hands branch m at index max (max k nBr) m
  have fam : ∀ m, Zekd α₁ (raise e B) (max (max k nBr) m) (d + norm e + 1) c
      (insert (χ/[nm m]) Γ) := by
    intro m
    exact (Zekd.allInv m D₁' (Finset.mem_insert_self _ _)).weakening
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))
  -- §1's reduction, then clean the sequent
  have hred := cutReduceAllAuxRunning hχc hNF₁ hENF fam D₂' hNF₂ hnorm₂ le_rfl le_rfl
    (Finset.mem_insert_self _ _)
  exact ⟨α₁, γ₁, hNF₁, hle₁, hnorm₁,
    hred.weakening (Finset.union_subset (Finset.erase_insert_subset _ _)
      (Finset.Subset.refl Γ))⟩

/-- **Seam 1 (negative half)**: the inflated slot can NEVER re-enter the motive's uniform slot —
for ANY value of the bump (even `0`), since `Zekd` has no `d`-lowering (`mono_d` raises only). -/
theorem seam1_uniform_slot_unpayable (ddIn x : ℕ) : ¬ (ddIn + x + 1 ≤ ddIn) := by omega

/-- **Seam 2 (the ω-node's uniform-`d` demand)**: `Zekd.allω` requires ONE `d`-slot for all
premises; on §3's configuration branch `n`'s inflated slot is
`(d + norm e + 1) + norm (expTower (wmul n)) + 1 = (d + norm e + 1) + (n + 1) + 1` — unbounded
in `n`.  NO uniform slot `D` exists, whatever structural functional produced it. -/
theorem seam2_no_uniform_slot (D dBase eNorm : ℕ) :
    ¬ (∀ n : ℕ, (dBase + eNorm + 1) + norm (expTower (wmul n)) + 1 ≤ D) := by
  intro h
  have hD := h D
  rw [norm_expTower_wmul] at hD
  omega

/-! ## §5 The remaining dodges, kernel-refuted -/

/-- **Dodge (b), seam ① (`norm` is not `<`-monotone)**: the ordinal-indexed slot
`d + norm e + norm α + 1` fails to thread ANY rule with premise norm above the node norm
(`weak`/`andI`/`orI`/`cut`/`allω` all allow it): the premise IH then sits at a STRICTLY LARGER
slot than the node's, and `Zekd` has no `d`-lowering.  Kernel witness: `ω·2 < ω^ω` with
`norm (ω·2) = 2 > 1 = norm (ω^ω)`. -/
theorem dodge_b_slot_not_monotone :
    wmul 1 < expTower ONote.omega ∧ norm (expTower ONote.omega) < norm (wmul 1) := by
  refine ⟨wmul_lt_expTower_omega 1, ?_⟩
  rw [norm_wmul, norm_expTower, show norm ONote.omega = 1 from rfl]
  omega

/-- **Dodge (b), seam ② (the sharpest single check)**: at the ω-node the ordinal-indexed premise
slots are `… + norm (β n) + …` with `β n := wmul n` a legitimate family below `ω^ω` (§3 uses
exactly it) whose norms are UNBOUNDED — `mono_d` (raising-only) + the wrapper's `≤`-slack cannot
bridge premise slots exceeding EVERY candidate node slot.  So dodge (b) dies at the `allω`
re-assembly even where seam ① happens to point the right way. -/
theorem dodge_b_allomega_unbridgeable (D : ℕ) :
    (∀ n, wmul n < expTower ONote.omega) ∧ ¬ (∀ n : ℕ, norm (wmul n) ≤ D) := by
  refine ⟨wmul_lt_expTower_omega, fun h => ?_⟩
  have hD := h D
  rw [norm_wmul] at hD
  omega

/-- **Dodge (c) (`k`-rebalance)**: push the bump `B ≥ 1` into the `k`-slot instead.
`Zekd.allω`'s premises must sit at EXACTLY `max k_node n`; a branch emitted at `max k n + B`
overshoots `max (k + B) n` as soon as `n > k + B`, and `Zekd` has no index-LOWERING — so no
node-level base `k_node` recovers the family.  (The deeper semantic form is banked at
`OperatorZinfty.lean:764`: the single-index witness bound is provably false,
`h_{βₙ#ω}(max{k,n}) ≰ max{h_{β#ω}(k), n}`.) -/
theorem dodge_c_k_rebalance_escapes (k B : ℕ) (hB : 1 ≤ B) :
    ∃ n, max (k + B) n < max k n + B :=
  ⟨k + B + 1, by omega⟩

/-- **Control seam (unconditional overshoot)**: §1's output control `raise E αf` strictly
exceeds its input control `E` for EVERY `αf`; since `mono_e` raises only, the arm — whose inputs
are already at/above the motive's single raise — can never emit at the motive's `raise e B`
under the pinned raise shape. -/
theorem control_seam_overshoot {E X : ONote} (hE : E.NF) (hX : X.NF) : E < raise E X := by
  haveI := hE
  haveI := expTower_NF hX
  rw [lt_def, raise, repr_add E (expTower X)]
  refine lt_add_of_pos_right _ ?_
  have h := oadd_pos X 1 0
  rw [lt_def, repr_zero] at h
  exact h

/-- **Control seam (fam-exponent escape)**: nor can a smarter pin re-base the raise at the
original `e` with exponent the fam ordinal `αf` — fitting `raise e X ≤ raise e B` needs
`X ≤ B`, but `αf ≤ expTower βφ` escapes `B` already at `βφ = 1 < B = 2`, `αf = ω^1 = ω > 2`. -/
theorem control_exponent_escape :
    (1 : ONote) < ofNat 2 ∧ ofNat 2 < expTower (1 : ONote) := by
  constructor
  · rw [lt_def]; simp
  · rw [lt_def, repr_ofNat]
    have h : (expTower (1 : ONote)).repr = Ordinal.omega0 := by
      simp [expTower, ONote.repr]
    rw [h]
    exact Ordinal.natCast_lt_omega0 2

end GoodsteinPA.SpikeW4B

/-! ## Real axiom footprints (work-order requirement: `sorryAx` + the 3 canonical at most;
NO new `axiom` declarations anywhere in this file). -/

-- the §1 statement pin (body sorried by design):
#print axioms GoodsteinPA.SpikeW4B.cutReduceAllAuxRunning
-- the rail + dodge (a) refutation (sorry-free):
#print axioms GoodsteinPA.SpikeW4B.rail_norm_genuinely_carried
#print axioms GoodsteinPA.SpikeW4B.dodge_a_norm_not_sheddable
-- the two-level configuration (sorry-free):
#print axioms GoodsteinPA.SpikeW4B.two_level_config
-- the composition probe (depends on the §1 pin ⟹ sorryAx, disclosed):
#print axioms GoodsteinPA.SpikeW4B.probe_cut_all_arm
-- the seams (sorry-free):
#print axioms GoodsteinPA.SpikeW4B.seam1_uniform_slot_unpayable
#print axioms GoodsteinPA.SpikeW4B.seam2_no_uniform_slot
-- the dodges (sorry-free):
#print axioms GoodsteinPA.SpikeW4B.dodge_b_slot_not_monotone
#print axioms GoodsteinPA.SpikeW4B.dodge_b_allomega_unbridgeable
#print axioms GoodsteinPA.SpikeW4B.dodge_c_k_rebalance_escapes
#print axioms GoodsteinPA.SpikeW4B.control_seam_overshoot
#print axioms GoodsteinPA.SpikeW4B.control_exponent_escape
