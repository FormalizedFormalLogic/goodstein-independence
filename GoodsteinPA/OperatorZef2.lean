module

public import GoodsteinPA.OperatorZeh
public import GoodsteinPA.ToMathlib.FastGrowing.EguchiWeiermannIteration
public import GoodsteinPA.Compat

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-!
# `Zef2` — the ewN-gated E–W controlled slot calculus (lap-8 src port)

Port of the ratified lap-7 statement layer (`wip/Zef2Calculus.lean`, freeze reference).  `Zef2`
is `Zef` with an ewN-size gate `ewN α ≤ f 0` carried on every node (and a cut-read gate
`φ.complexity ≤ f 0` on `cut`).  The gate is what the trap-8 escalation demanded: the diagonal
output slot's base-argument read is controlled by the ordinal's constructor norm.

The forgetful map `Zef2.toZef` drops the gate — it is the conservativity witness, and discharges
both read-off pins by reuse of the `Zef` read-off (§ read-off).  Pins 1–2 (§ reduction) and the
inversion suite are re-proven natively over `Zef2` (the gate re-threads at each rebuilt node).
The cut-elimination pass `cutElimPass_Zef2` stays the laps-9+ gate (`sorry`; grind FORBIDDEN).

`OperatorZeh.lean`'s old `Zef` layer, `iterSlot` + §5b lemmas, and old pin 3 are SUPERSEDED by
this module (frozen evidence; statement tokens there untouched).
-/

/-- **`Zef2`** — the ewN-gated function-slot cut-elimination calculus.  Identical to `Zef`
(`OperatorZeh.lean`) up to the size gate `hαN : ewN α ≤ f 0` on every node and the cut-read gate
`hcutRead : φ.complexity ≤ f 0` on `cut`. -/
inductive Zef2 : ONote → ONote → (ONote → Prop) → (ℕ → ℕ) → ℕ → Seq → Prop
  | axL {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} {ar : ℕ}
      (hαN : Nlog α ≤ f 0)
      (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zef2 α e H f c Γ
  | wk {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2 α e H f c Δ) :
      Zef2 α e H f c Γ
  | weak {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β)
      (hsub : Δ ⊆ Γ) (dd : Zef2 β e H f c Δ) : Zef2 α e H f c Γ
  | allω {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
      (hβH : ∀ n, relOp H n (β n))
      (dd : ∀ n, Zef2 (β n) e (adjoin H n) (rel1 f n) c (insert (φ/[nm n]) Γ)) :
      Zef2 α e H f c (insert (∀⁰ φ) Γ)
  | exI {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hβH : Cl H β) (hbound : n ≤ f 0)
      (dd : Zef2 β e H f c (insert (φ/[nm n]) Γ)) : Zef2 α e H f c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
      (hαN : Nlog α ≤ f 0)
      (φ : Form) (hcompl : φ.complexity < c) (hcutRead : φ.complexity ≤ f 0)
      (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
      (hβφH : Cl H βφ) (hβψH : Cl H βψ)
      (d₁ : Zef2 βφ e H f c (insert φ Γ)) (d₂ : Zef2 βψ e H f c (insert (∼φ) Γ)) :
      Zef2 α e H f c Γ

namespace Zef2

/-- **Gate projection** — every `Zef2` constructor exposes its conclusion gate `ewN α ≤ f 0`, so
a derivation is its own certificate for the size bound.  The uniform lever for re-threading the
gate through the reduction / inversion. -/
theorem gate {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (dd : Zef2 α e H f c Γ) : Nlog α ≤ f 0 := by
  cases dd <;> assumption

theorem weakening {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Δ Γ : Seq}
    (hαN : Nlog α ≤ f 0) (hsub : Δ ⊆ Γ) (dd : Zef2 α e H f c Δ) :
    Zef2 α e H f c Γ :=
  Zef2.wk hαN hsub dd

/-- **Slot weakening** (`mono_f`): a larger slot is more permissive (all gates ride `f 0 ≤ f' 0`;
`exI` bound rides it too; `allω` rides `rel1_mono`). -/
theorem mono_f : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → ∀ {f' : ℕ → ℕ}, (∀ x, f x ≤ f' x) → Zef2 α e H f' c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn =>
      intro f' hff'; exact Zef2.axL (le_trans hαN (hff' 0)) r v hp hn
  | wk hαN hsub _ ih =>
      intro f' hff'; exact Zef2.wk (le_trans hαN (hff' 0)) hsub (ih hff')
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro f' hff'; exact Zef2.weak (le_trans hαN (hff' 0)) hβ hβNF hαNF hβH hsub (ih hff')
  | allω hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro f' hff'
      exact Zef2.allω (le_trans hαN (hff' 0)) φ β hβ hβNF hαNF hβH
        (fun n => ih n (rel1_mono hff' n))
  | exI hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro f' hff'
      exact Zef2.exI (le_trans hαN (hff' 0)) φ n hβ hβNF hαNF hβH
        (le_trans hbound (hff' 0)) (ih hff')
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      intro f' hff'
      exact Zef2.cut (le_trans hαN (hff' 0)) φ hcompl (le_trans hcutRead (hff' 0))
        hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH (ih₁ hff') (ih₂ hff')

/-- **Operator irrelevance** (R1): the generator slot `H` carries no information. -/
theorem change_H : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → ∀ {H' : ONote → Prop}, Zef2 α e H' f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL hαN r v hp hn => intro H'; exact Zef2.axL hαN r v hp hn
  | wk hαN hsub _ ih => intro H'; exact Zef2.wk hαN hsub ih
  | weak hαN hβ hβNF hαNF _ hsub _ ih =>
      intro H'; exact Zef2.weak hαN hβ hβNF hαNF (Cl_of_NF hβNF) hsub ih
  | allω hαN φ β hβ hβNF hαNF _ _ ih =>
      intro H'; exact Zef2.allω hαN φ β hβ hβNF hαNF
        (fun n => Cl_of_NF (hβNF n)) (fun n => ih n)
  | exI hαN φ n hβ hβNF hαNF _ hbound _ ih =>
      intro H'; exact Zef2.exI hαN φ n hβ hβNF hαNF (Cl_of_NF hβNF) hbound ih
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF _ _ _ _ ih₁ ih₂ =>
      intro H'; exact Zef2.cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) ih₁ ih₂

/-- Combined operator+slot move. -/
theorem mono_Hf {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (dd : Zef2 α e H f c Γ) {H' : ONote → Prop} {f' : ℕ → ℕ} (hff' : ∀ x, f x ≤ f' x) :
    Zef2 α e H' f' c Γ := (dd.change_H).mono_f hff'

/-- **`toZef`** — the forgetful map dropping the ewN/cut-read gate (the mandated read-off route;
doubles as the conservativity witness `Zef2 ⤳ Zef`). -/
theorem toZef : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → Zef α e H f c Γ := by
  intro α e H f c Γ dd
  induction dd with
  | axL _ r v hp hn => exact Zef.axL r v hp hn
  | wk _ hsub _ ih => exact Zef.wk hsub ih
  | weak _ hβ hβNF hαNF hβH hsub _ ih => exact Zef.weak hβ hβNF hαNF hβH hsub ih
  | allω _ φ β hβ hβNF hαNF hβH _ ih => exact Zef.allω φ β hβ hβNF hαNF hβH (fun n => ih n)
  | exI _ φ n hβ hβNF hαNF hβH hbound _ ih => exact Zef.exI φ n hβ hβNF hαNF hβH hbound ih
  | cut _ φ hcompl _ hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      exact Zef.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH ih₁ ih₂

end Zef2

/-- The `≤`-slack wrapper (slot form of `ZehProv`), carrying the ewN gate on the witness. -/
def Zef2Prov (α e : ONote) (H : ONote → Prop) (f : ℕ → ℕ) (c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ Cl H α' ∧ Nlog α' ≤ f 0 ∧ Zef2 α' e H f c Γ

namespace Zef2Prov

theorem of {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hNF : α.NF) (hH : Cl H α) (hN : Nlog α ≤ f 0) (D : Zef2 α e H f c Γ) :
    Zef2Prov α e H f c Γ :=
  ⟨α, le_refl _, hNF, hH, hN, D⟩

theorem mono {α β e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (hα : α ≤ β) : Zef2Prov α e H f c Γ → Zef2Prov β e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', le_trans hα' hα, hNF, hH, hN, D⟩

theorem weakening {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ Δ : Seq}
    (h : Γ ⊆ Δ) : Zef2Prov α e H f c Γ → Zef2Prov α e H f c Δ := by
  rintro ⟨α', hα', hNF, hH, hN, D⟩
  exact ⟨α', hα', hNF, hH, hN, D.wk hN h⟩

/-- Forget the gate: `Zef2Prov ⤳ ZefProv`. -/
theorem toZefProv {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq} :
    Zef2Prov α e H f c Γ → ZefProv α e H f c Γ := by
  rintro ⟨α', hα', hNF, hH, _, D⟩
  exact ⟨α', hα', hNF, hH, D.toZef⟩

end Zef2Prov

/-! ## The read-off exit, discharged by the forgetful map (P-c) -/

def ReadoffShapeF2 (φ : SyntacticSemiformula ℒₒᵣ 1) (f : ℕ → ℕ) (Γ : Seq) : Prop :=
  ReadoffShapeF φ f Γ

def ReadoffGoalF2 (φ : SyntacticSemiformula ℒₒᵣ 1) (f : ℕ → ℕ) (Γ : Seq) : Prop :=
  ReadoffGoalF φ f Γ

/-- **`readoff_sigma1_Zef2`** — the ewN-gated read-off, discharged by reuse of the `Zef` read-off
through `toZef` (zero re-proof; the gate is read-off-irrelevant). -/
theorem readoff_sigma1_Zef2 {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq}
    (dd : Zef2 α e H f c Γ) (hc : c = 0) (hshape : ReadoffShapeF2 φ f Γ) :
    ReadoffGoalF2 φ f Γ :=
  readoff_sigma1_Zef hφinst dd.toZef hc hshape

/-- **`headline_readoff_Zef2`** — the exit witness, discharged through `toZef`. -/
theorem headline_readoff_Zef2 {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    (dd : Zef2 α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n]) :=
  headline_readoff_Zef hφinst dd.toZef

/-! ## ewN arithmetic — the size norm is sub-additive under `+` and near-additive under `osucc`

These are the size-control facts the reduction's synthesized `osucc (α + γ)` roots need: the gate
`ewN (osucc (α + γ)) ≤ ewN α + ewN γ + 1`.  Banked here (kernel-verified, unconditional for `+`,
`NF` for `osucc`) toward the P-d discharge. -/

/-- `ewN` is sub-additive over `addAux`. -/
theorem ewN_addAux_le (e : ONote) (n : ℕ+) (o : ONote) :
    ewN (addAux e n o) ≤ ewN e + (n : ℕ) + ewN o := by
  unfold addAux
  cases o with
  | zero => simp [ewN]
  | oadd e' n' a' =>
      simp only
      cases h : ONote.cmp e e' with
      | lt => simp only [ewN_oadd]; omega
      | eq =>
          have he : e = e' := eq_of_cmp_eq h
          subst he
          simp only [ewN_oadd, PNat.add_coe]; omega
      | gt => simp only [ewN_oadd]; omega

/-- `ewN` is sub-additive over ordinal addition (unconditional). -/
theorem ewN_add_le : ∀ (a o : ONote), ewN (a + o) ≤ ewN a + ewN o := by
  intro a
  induction a with
  | zero => intro o; simp [ewN]
  | oadd e n b ihe ih =>
      intro o
      rw [oadd_add]
      refine le_trans (ewN_addAux_le e n (b + o)) ?_
      have := ih o
      simp only [ewN_oadd]; omega

/-- `ewN` grows by at most one under the notation successor (for normal forms). -/
theorem ewN_osucc_le : ∀ {o : ONote}, o.NF → ewN (osucc o) ≤ ewN o + 1
  | 0, _ => by simp [osucc, ewN]
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [repr_zero, opow_zero] at hlt
        exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact Order.lt_one_iff.1 hlt)
      subst ha0
      show ewN (oadd 0 (n + 1) 0) ≤ ewN (oadd 0 n 0) + 1
      simp only [ewN_oadd, ewN_zero, PNat.add_coe, PNat.one_coe]; omega
  | oadd (oadd e' n' a') m b, h => by
      show ewN (oadd (oadd e' n' a') m (osucc b)) ≤ ewN (oadd (oadd e' n' a') m b) + 1
      have hIH := ewN_osucc_le h.snd
      simp only [ewN_oadd] at hIH ⊢; omega

/-- The composite the reduction roots need: `ewN (osucc (α + γ)) ≤ ewN α + ewN γ + 1`. -/
theorem ewN_osucc_add_le {α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) :
    ewN (osucc (α + γ)) ≤ ewN α + ewN γ + 1 := by
  refine le_trans (ewN_osucc_le (ONote.add_nf α γ)) ?_
  have := ewN_add_le α γ
  omega

/-- **The composed-slot base gate** (lap-10 SERIES-1 R-0(ii)) — the judge's `α + γ` output gate.
`ewN α ≤ g 0`, `ewN γ ≤ f 0`, and the `∀`-side per-step floor `g 0 + k ≤ g k` close the fresh
node's gate `ewN (α + γ) ≤ (g ∘ f) 0 = g (f 0)`.  Kernel-checked in `wip/Lap10SeamProbe.lean`
(`seam_ewN_add_comp`, `#print axioms` clean); this REPLACES the refuted `osucc`-`+1` composite for
Stage-2's node gates. -/
theorem ewN_add_le_comp {α γ : ONote} {f g : ℕ → ℕ}
    (hα : ewN α ≤ g 0) (hγ : ewN γ ≤ f 0) (hg_base : ∀ k, g 0 + k ≤ g k) :
    ewN (α + γ) ≤ g (f 0) :=
  le_trans (ewN_add_le α γ) (base_add_le_comp hg_base hα hγ)

/-! ## The pass's ordinal-collapse containment (Stage-3 prep) -/

/-- `repr (collapse x) = ω ^ repr x` (`collapse = expTower = oadd · 1 0`). -/
theorem repr_collapse (x : ONote) : (collapse x).repr = ω ^ x.repr := by
  simp [collapse, expTower, ONote.repr]

/-- **Ordinal-collapse containment** (lap-10 SERIES-3 pass prep) — the cut-elimination step feeds two
IH-reduced premises (at `collapse βφ`, `collapse βψ`, `βφ,βψ < α`) into the reduction pin, whose
additive output `collapse βφ + collapse βψ` must fit strictly under the single collapse
`collapse α = ω^α`.  This is the additive principality of `ω^α`.  Kernel-checked in
`wip/Lap10PassProbe.lean`. -/
theorem collapse_add_lt {βφ βψ α : ONote} (hβφ : βφ.NF) (hβψ : βψ.NF) (_hα : α.NF)
    (hφ : βφ < α) (hψ : βψ < α) : collapse βφ + collapse βψ < collapse α := by
  haveI := hβφ; haveI := hβψ; haveI := _hα
  haveI := collapse_NF hβφ; haveI := collapse_NF hβψ; haveI := collapse_NF _hα
  haveI := ONote.add_nf (collapse βφ) (collapse βψ)
  refine lt_def.mpr ?_
  rw [repr_add, repr_collapse, repr_collapse, repr_collapse]
  have hφr : (ω : Ordinal) ^ βφ.repr < ω ^ α.repr :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_def.mp hφ)
  have hψr : (ω : Ordinal) ^ βψ.repr < ω ^ α.repr :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_def.mp hψ)
  exact (Ordinal.isPrincipal_add_omega0_opow α.repr) hφr hψr

/-- `ewN (collapse α) = ewN α + 1` (`collapse α = oadd α 1 0`). -/
theorem ewN_collapse (α : ONote) : ewN (collapse α) = ewN α + 1 := by
  simp [collapse, expTower, ewN]

/-- **Per-node gate for the pass** — the rebuilt node at `collapse α` with slot `ewIter f α` needs
gate `ewN (collapse α) ≤ (ewIter f α) 0`.  From the derivation's base gate `ewN α ≤ f 0` + the
`2m+1 ≤ f m` LOWER bound (`hlow`): `ewN (collapse α) = ewN α + 1`, and `ewIter f α 0 ≥ f (f 0) ≥
2·f 0 + 1 ≥ ewN α + 1` (the `f(f 0)` floor via `ewIter_lower` at `0 < α`; `hlow` at the base for
`α = 0`).  Crucially uses only `hlow`, NOT strict monotonicity — so it survives the pass's `allω`
branches where the slot is `rel1 f n` (which preserves `hlow` via `rel1_low` but breaks
strictness).  Kernel-checked in `wip/Lap10PassProbe.lean`. -/
theorem ewN_collapse_le {f : ℕ → ℕ} (hlow : ∀ m, 2 * m + 1 ≤ f m) {α : ONote}
    (hgate : ewN α ≤ f 0) : ewN (collapse α) ≤ ewIter f α 0 := by
  rw [ewN_collapse]
  by_cases hα : α = 0
  · subst hα
    simp only [ewN_zero, ewIter_zero]
    have := hlow 0; omega
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow' := ewIter_lower (f := f) (β := 0) (α := α) (m := 0) NF.zero h0α (Nat.zero_le _)
    have hff : f (f 0) ≤ ewIter f α 0 := by simpa [ewIter_zero] using hlow'
    have hb : 2 * f 0 + 1 ≤ f (f 0) := hlow (f 0)
    exact le_trans (by omega : ewN α + 1 ≤ f (f 0)) hff

/-- `Nlog (collapse α) = Nlog α + 1` (`collapse α = oadd α 1 0`, `clog 1 = 1`) — the `Nlog`
analog of `ewN_collapse` (N-1 promotion from `wip/NlogGateProbe.lean`). -/
theorem Nlog_collapse (α : ONote) : Nlog (collapse α) = Nlog α + 1 := by
  show Nlog (oadd α 1 0) = Nlog α + 1
  have hc : clog 1 = 1 := by decide
  simp [Nlog_oadd, hc]

/-- **Per-node gate for the pass over `Nlog`** — the analog of `ewN_collapse_le`: the rebuilt
node at `collapse α` with slot `ewIter f α` closes its `Nlog` gate from the derivation's base
gate `Nlog α ≤ f 0` + the EwLow floor.  Same `f (f 0)` mechanism; only `hlow`, no strictness,
so it survives the `allω` branches' `rel1 f n` slots. -/
theorem Nlog_collapse_le {f : ℕ → ℕ} (hlow : ∀ m, 2 * m + 1 ≤ f m) {α : ONote}
    (hgate : Nlog α ≤ f 0) : Nlog (collapse α) ≤ ewIter f α 0 := by
  rw [Nlog_collapse]
  by_cases hα : α = 0
  · subst hα
    simp only [Nlog_zero, ewIter_zero]
    have := hlow 0; omega
  · have h0α : (0 : ONote) < α := by
      cases α with
      | zero => exact (hα rfl).elim
      | oadd e n a => exact oadd_pos e n a
    have hlow' := ewIter_lower (f := f) (β := 0) (α := α) (m := 0) NF.zero h0α (Nat.zero_le _)
    have hff : f (f 0) ≤ ewIter f α 0 := by simpa [ewIter_zero] using hlow'
    have hb : 2 * f 0 + 1 ≤ f (f 0) := hlow (f 0)
    omega

/-! ## Pins 1–2 over `Zef2` (P-d) — re-proven natively (disclosed sub-pins, laps-9+) -/

/-- `β < γ → α < α + γ` (NF): the fresh `α + γ` root strictly dominates the `∀`-family base `α`
whenever the `∃`-side ordinal `γ` is positive (which a strict descendant `β < γ` witnesses).  The
`α + γ` analogue of the old `α < osucc (α + γ)`.  Kernel-checked in `wip/Lap10SeamProbe.lean`. -/
private theorem lt_add_of_inner_lt {α β γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) (hβ : β < γ) :
    α < α + γ := by
  haveI := hαNF; haveI := hγNF
  refine lt_def.mpr ?_
  rw [repr_add]
  have hγpos : (0 : Ordinal) < γ.repr := lt_of_le_of_lt (by simp) (lt_def.mp hβ)
  simpa using (add_lt_add_iff_left α.repr).mpr hγpos

set_option maxHeartbeats 1000000 in
/-- **PIN (disclosed sub-pin, P-d): the running-family cut-reduction over `Zef2`.**  Port of
`cutReduceAllAuxRunning_Zf` with the ewN/cut-read gate re-threaded at every rebuilt node.

**SUPERSEDES the `osucc (α + γ)` form** per the judge ruling (§3, trap 9, E–W Lemma 25,
`E-2026-07-02-JUDGE-rebuild-z-lap8-validation.md`): the reduction's fresh root is `α + γ` (NO
successor `+1`) and the lap-9 refutation of the `osucc`-`+1` gate no longer applies.  The two
Stage-1 additions to the signature — `hg_base : ∀ k, g 0 + k ≤ g k` (a per-step growth floor on the
`∀`-side slot) and `φ.complexity ≤ f 0` (the fresh cut-read) — are exactly what the R-0 seam probe
proved close the fresh node's gates: `ewN (α + γ) ≤ g (f 0)` via `ewN_add_le_comp` and
`φ.complexity ≤ (g ∘ f) 0` via `hg_infl`.  Premises land strictly below `α + γ` by the R-0(i)
covariance seams.  Body `sorry` until Stage 2 (grind UNLOCKED). -/
theorem cutReduceAllAuxRunning_Zf2 {φ : SyntacticSemiformula ℒₒᵣ 1} {c : ℕ} {α e : ONote}
    {Γ : Seq} {g : ℕ → ℕ} (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (fam : ∀ n (H' : ONote → Prop), Zef2 α e H' (rel1 g n) c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Seq}, Zef2 γ e H f c Δ → γ.NF →
      Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      φ.complexity ≤ f 0 → (∃⁰ ∼φ) ∈ Δ →
      Zef2Prov (α + γ) e H (g ∘ f) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  have hg0 : Nlog α ≤ g 0 := by
    have h := Zef2.gate (fam 0 (fun _ => True)); simpa [rel1] using h
  intro γ H f Δ D
  induction D with
  | @axL γ e H f c Δ ar hαN r v hp hn =>
      intro hγNF _ _ hsl _ hmem
      refine Zef2Prov.of (ONote.add_nf α γ) (Cl_of_NF (ONote.add_nf α γ))
        (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2.axL (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))
  | @wk γ e H f c Δsub Δsup hαN hsub D' ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hmono hinfl hsl hφread hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · exact ⟨γ, Zekd.le_add_left_NF hαNF hγNF, hγNF, Cl_of_NF hγNF,
          le_trans hαN (reslot_exside hg_infl 0),
          (D'.mono_f (reslot_exside hg_infl)).wk (le_trans hαN (reslot_exside hg_infl 0)) (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ β e H f c Δsub Δsup hαN hβ hβNF hγNF' hβH hsub D' ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF hmono hinfl hsl hφread hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
      · exact ⟨β, le_of_lt (lt_of_lt_of_le hβ (Zekd.le_add_left_NF hαNF hγNF)), hβNF, Cl_of_NF hβNF,
          le_trans (Zef2.gate D') (reslot_exside hg_infl 0),
          (D'.mono_f (reslot_exside hg_infl)).wk (le_trans (Zef2.gate D') (reslot_exside hg_infl 0)) (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @allω γ e H f c Γ₀ hαN χ β hβ hβNF hγNF' hβH dd ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      have ihn : ∀ n, Zef2Prov (α + β n) e (adjoin H n) (g ∘ rel1 f n) c
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        have hread : φ.complexity ≤ (rel1 f n) 0 := by
          simp only [rel1]; exact le_trans hφread (hmono (Nat.zero_le _))
        exact (ih n hφc heNF fam (hβNF n) (rel1_monotone hmono n) (rel1_infl hinfl n)
          (fun k hk => hsl k (le_trans (by
            simp only [rel1]; exact hmono (Nat.zero_le _)) hk))
          hread (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hAll : Zef2 (α + γ) e H (g ∘ f) c
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        exact Zef2.allω (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ (fun n => (ihn n).choose)
          (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
            (Zekd.add_lt_add_left_NF hαNF (hβNF n) hγNF (hβ n)))
          (fun n => (ihn n).choose_spec.2.1) haddNF
          (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
          (fun n => (ihn n).choose_spec.2.2.2.2)
      exact hAll.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)
  | @exI γ β e H f c Γ₀ hαN χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      intro hγNF hmono hinfl hsl hφread hmem
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · have hχ : χ = ∼φ := by simpa [ExsQuantifier.exs] using hhd
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c := by simpa using hφc
        have hcutRead : (φ/[nm n]).complexity ≤ (g ∘ f) 0 := by
          have he : (φ/[nm n]).complexity = φ.complexity := by simp
          rw [he]; exact le_trans hφread (hg_infl (f 0))
        have hg0comp : Nlog α ≤ (g ∘ f) 0 := le_trans hg0 (hg_mono (Nat.zero_le _))
        have famn : Zef2 α e H (g ∘ f) c (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          ((fam n H).mono_f (reslot_family hg_mono hinfl hmono hbound)).wk hg0comp (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
        have hαlt : α < α + γ := lt_add_of_inner_lt hαNF hγNF hβ
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
            (Finset.mem_insert_of_mem hd)
          have Da' : Zef2 a e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Da.wk hag (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
          refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
          exact Zef2.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
            (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
            hαNF haNF haddNF (Cl_of_NF hαNF) haH famn Da'
        · have Dβ' : Zef2 β e H (g ∘ f) c
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            (dχ.mono_f (reslot_exside hg_infl)).wk
              (le_trans (Zef2.gate dχ) (reslot_exside hg_infl 0)) (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
          refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
          exact Zef2.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (φ/[nm n]) hcompl hcutRead hαlt
            (lt_of_lt_of_le hβ (Zekd.le_add_left_NF hαNF hγNF))
            hαNF hβNF haddNF (Cl_of_NF hαNF) (Cl_of_NF hβNF) famn Dβ'
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih hφc heNF fam hβNF hmono hinfl hsl hφread
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zef2 a e H (g ∘ f) c (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Da.wk hag (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
        have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
        exact Zef2.exI (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ n
          (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hαNF hβNF hγNF hβ))
          haNF haddNF haH hbound' Da'
        |>.wk (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhd, Or.inl rfl⟩
          · tauto)
  | @cut γ βφ βψ e H f c Γ₀ hαN χ hχc hcutRead' hβφ hβψ hβφNF hβψNF hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hsl hφread hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁⟩ := ih₁ hφc heNF fam hβφNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂⟩ := ih₂ hφc heNF fam hβψNF hmono hinfl hsl hφread
        (Finset.mem_insert_of_mem hmem)
      have haddNF : (α + γ).NF := ONote.add_nf α γ
      have D₁' : Zef2 a₁ e H (g ∘ f) c (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₁.wk ha₁g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have D₂' : Zef2 a₂ e H (g ∘ f) c (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₂.wk ha₂g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2Prov.of haddNF (Cl_of_NF haddNF) (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2.cut (Nlog_add_le_comp hαNF hγNF hg0 hαN (hsl _ le_rfl)) χ hχc
        (le_trans hcutRead' (hg_infl (f 0)))
        (lt_of_le_of_lt ha₁le (Zekd.add_lt_add_left_NF hαNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (Zekd.add_lt_add_left_NF hαNF hβψNF hγNF hβψ))
        ha₁NF ha₂NF haddNF ha₁H ha₂H D₁' D₂'

/-- `f x ≤ rel1 f n₀ x` for monotone `f`. -/
private theorem f_le_rel1_2 {f : ℕ → ℕ} (hf : Monotone f) (n₀ : ℕ) :
    ∀ x, f x ≤ rel1 f n₀ x := fun x => hf (le_max_right n₀ x)

/-- Transport a gate `ewN α ≤ f 0` to the relativized slot `rel1 f n₀`. -/
private theorem gate_rel1 {f : ℕ → ℕ} (hmono : Monotone f) {α : ONote} (n₀ : ℕ)
    (h : Nlog α ≤ f 0) : Nlog α ≤ rel1 f n₀ 0 := by
  refine le_trans h ?_
  simp only [rel1]
  exact hmono (Nat.zero_le _)

/-- **`allInv_Zef2`** — ∀-inversion over `Zef2` (port of `allInv_Zef`).  Ordinals are unchanged by
inversion, so every rebuilt node's gate re-threads from its input gate through the relativized
slot `rel1 f n₀` (`gate_rel1`, `f` monotone). -/
theorem allInv_Zef2 {φ₀ : SyntacticSemiformula ℒₒᵣ 1} (n₀ : ℕ) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2 α e H f c Γ → Monotone f → (∀⁰ φ₀) ∈ Γ →
      Zef2 α e (adjoin H n₀) (rel1 f n₀) c (insert (φ₀/[nm n₀]) (Γ.erase (∀⁰ φ₀))) := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro hmono _
      refine Zef2.axL (gate_rel1 hmono n₀ hαN) r v ?_ ?_ <;>
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), by assumption⟩)
  | @wk α e H f c Δ Γ hαN hsub dd ih =>
      intro hmono hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef2.wk (gate_rel1 hmono n₀ hαN)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef2.wk (gate_rel1 hmono n₀ hαN) ?_ (dd.mono_Hf (f_le_rel1_2 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub dd ih =>
      intro hmono hmem
      by_cases hh : (∀⁰ φ₀) ∈ Δ
      · exact Zef2.weak (gate_rel1 hmono n₀ hαN) hβ hβNF hαNF (Cl_of_NF hβNF)
          (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)) (ih hmono hh)
      · refine Zef2.weak (gate_rel1 hmono n₀ hαN) hβ hβNF hαNF (Cl_of_NF hβNF) ?_
          (dd.mono_Hf (f_le_rel1_2 hmono n₀))
        intro x hx
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ hx), hsub hx⟩)
  | @allω α e H f c Γ₀ hαN χ β hβ hβNF hαNF hβH dd ih =>
      intro hmono hmem
      by_cases hhd : (∀⁰ χ) = (∀⁰ φ₀)
      · obtain rfl := (Semiformula.all_inj _ _).mp hhd
        rw [Finset.erase_insert_eq_erase]
        by_cases hh : (∀⁰ χ) ∈ Γ₀
        · have h := ih n₀ (rel1_monotone hmono n₀) (Finset.mem_insert_of_mem hh)
          have h2 : Zef2 (β n₀) e (adjoin H n₀) (rel1 f n₀) c
              (insert (χ/[nm n₀]) ((insert (χ/[nm n₀]) Γ₀).erase (∀⁰ χ))) :=
            h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega))
          exact Zef2.weak (gate_rel1 hmono n₀ hαN) (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀))
            (princAllSub (∀⁰ χ) _ Γ₀) h2
        · rw [Finset.erase_eq_of_notMem hh]
          exact Zef2.weak (gate_rel1 hmono n₀ hαN) (hβ n₀) (hβNF n₀) hαNF (Cl_of_NF (hβNF n₀))
            (Finset.Subset.refl _) (dd n₀)
      · have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        have key : ∀ n, Zef2 (β n) e (adjoin (adjoin H n₀) n) (rel1 (rel1 f n₀) n) c
            (insert (χ/[nm n]) (insert (φ₀/[nm n₀]) (Γ₀.erase (∀⁰ φ₀)))) := by
          intro n
          have h := ih n (rel1_monotone hmono n) (Finset.mem_insert_of_mem hmem0)
          have hg : Nlog (β n) ≤ rel1 (rel1 f n₀) n 0 := by
            have hgn := Zef2.gate (dd n)
            simp only [rel1] at hgn ⊢
            exact le_trans hgn (hmono (le_max_right n₀ (max n 0)))
          exact Zef2.wk hg (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀)
            (h.mono_Hf (fun x => le_of_eq (by simp only [rel1]; congr 1; omega)))
        refine Zef2.wk (gate_rel1 hmono n₀ hαN) (inv1Pull (∀⁰ φ₀) _ hhd Γ₀) ?_
        exact Zef2.allω (gate_rel1 hmono n₀ hαN) χ β hβ hβNF hαNF
          (fun n => Cl_of_NF (hβNF n)) key
  | @exI α β e H f c Γ₀ hαN χ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hmono hmem
      have hhead : (∃⁰ χ) ≠ (∀⁰ φ₀) := by intro h; simp [ExsQuantifier.exs, UnivQuantifier.all] at h
      have hmem0 : (∀⁰ φ₀) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have P := Zef2.wk (Zef2.gate (ih hmono (Finset.mem_insert_of_mem hmem0)))
        (inv1Push (∀⁰ φ₀) _ (χ/[nm n]) Γ₀) (ih hmono (Finset.mem_insert_of_mem hmem0))
      refine Zef2.wk (gate_rel1 hmono n₀ hαN) (inv1Pull (∀⁰ φ₀) _ hhead Γ₀) ?_
      exact Zef2.exI (gate_rel1 hmono n₀ hαN) χ n hβ hβNF hαNF (Cl_of_NF hβNF)
        (le_trans hbound (by simp only [rel1]; exact hmono (Nat.zero_le _))) P
  | @cut α βφ βψ e H f c Γ₀ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hmono hmem
      have P₁ := Zef2.wk (Zef2.gate (ih₁ hmono (Finset.mem_insert_of_mem hmem)))
        (inv1Push (∀⁰ φ₀) _ χ Γ₀) (ih₁ hmono (Finset.mem_insert_of_mem hmem))
      have P₂ := Zef2.wk (Zef2.gate (ih₂ hmono (Finset.mem_insert_of_mem hmem)))
        (inv1Push (∀⁰ φ₀) _ (∼χ) Γ₀) (ih₂ hmono (Finset.mem_insert_of_mem hmem))
      exact Zef2.cut (gate_rel1 hmono n₀ hαN) χ hcompl (le_trans hcutRead
        (by simp only [rel1]; exact hmono (Nat.zero_le _))) hβφ hβψ hβφNF hβψNF hαNF
        (Cl_of_NF hβφNF) (Cl_of_NF hβψNF) P₁ P₂

/-- **`stepAllω_Zf2`** (pin-2 over `Zef2`): the principal ∀/∃ cut-reduction step.  Disclosed
sub-pin — invert the ∀-side via `allInv_Zef2`, feed `cutReduceAllAuxRunning_Zf2`.  Restated per the
judge ruling with the `hg_base` floor + `hχRead : χ.complexity ≤ f 0` cut-read (Stage-1 R-2). -/
theorem stepAllω_Zf2 {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Seq}
    {χ : SyntacticSemiformula ℒₒᵣ 1} {βφ βψ : ONote} {f g : ℕ → ℕ}
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hg_slack : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) (hχRead : χ.complexity ≤ f 0)
    (D₁ : Zef2Prov (expTower βφ) E H g c (insert (∀⁰ χ) Γ))
    (D₂ : Zef2Prov (expTower βψ) E H f c (insert (∃⁰ ∼χ) Γ)) :
    ∃ δ : ONote, δ.NF ∧ Cl H δ ∧ Zef2Prov δ E H (g ∘ f) c Γ := by
  obtain ⟨α₁, _, hNF₁, _, _, d₁⟩ := D₁
  obtain ⟨γ₁, _, hNF₂, _, _, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef2 α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    have hinv := allInv_Zef2 n d₁ hg_mono (Finset.mem_insert_self _ _)
    exact (hinv.wk (Zef2.gate hinv)
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))).change_H
  have hred := cutReduceAllAuxRunning_Zf2 hχc hNF₁ hENF hg_mono hg_infl fam
    d₂ hNF₂ hf_mono hf_infl hg_slack hχRead (Finset.mem_insert_self _ _)
  refine ⟨α₁ + γ₁, ONote.add_nf α₁ γ₁, Cl_of_NF (ONote.add_nf α₁ γ₁), ?_⟩
  exact hred.weakening
    (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))

/-- **`stepAllω_Zf2_bnd`** — the bound-EXPOSING variant of `stepAllω_Zf2`.  Same principal ∀/∃
cut-reduction, but the output witness ordinal is bounded by `P₁ + P₂` (the sum of the two premises'
ordinals), which the cut-elimination pass needs to place the eliminated cut strictly under
`collapse α` (via `collapse_add_lt`).  The generic `stepAllω_Zf2` hides `δ`; here we keep the two
`≤`-bounds from the `Zef2Prov` witnesses and add-monotone them (`repr_add` + `add_le_add`). -/
theorem stepAllω_Zf2_bnd {E : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Seq}
    {χ : SyntacticSemiformula ℒₒᵣ 1} {P₁ P₂ : ONote} {f g : ℕ → ℕ}
    (hP₁ : P₁.NF) (hP₂ : P₂.NF)
    (hENF : E.NF) (hχc : χ.complexity < c)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (hg_slack : ∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k)
    (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x) (hχRead : χ.complexity ≤ f 0)
    (D₁ : Zef2Prov P₁ E H g c (insert (∀⁰ χ) Γ))
    (D₂ : Zef2Prov P₂ E H f c (insert (∃⁰ ∼χ) Γ)) :
    Zef2Prov (P₁ + P₂) E H (g ∘ f) c Γ := by
  obtain ⟨α₁, hα₁le, hNF₁, _, _, d₁⟩ := D₁
  obtain ⟨γ₁, hγ₁le, hNF₂, _, _, d₂⟩ := D₂
  have fam : ∀ n (H' : ONote → Prop), Zef2 α₁ E H' (rel1 g n) c (insert (χ/[nm n]) Γ) := by
    intro n H'
    have hinv := allInv_Zef2 n d₁ hg_mono (Finset.mem_insert_self _ _)
    exact (hinv.wk (Zef2.gate hinv)
      (Finset.insert_subset_insert _ (Finset.erase_insert_subset _ _))).change_H
  have hred := cutReduceAllAuxRunning_Zf2 hχc hNF₁ hENF hg_mono hg_infl fam
    d₂ hNF₂ hf_mono hf_infl hg_slack hχRead (Finset.mem_insert_self _ _)
  have hbnd : α₁ + γ₁ ≤ P₁ + P₂ := by
    haveI := hNF₁; haveI := hNF₂; haveI := hP₁; haveI := hP₂
    rw [le_def, repr_add, repr_add]
    exact add_le_add (le_def.mp hα₁le) (le_def.mp hγ₁le)
  exact ((hred.weakening
    (Finset.union_subset (Finset.erase_insert_subset _ _) (Finset.Subset.refl Γ))).mono hbnd)

/-! ## N-2 helpers: inert-shape erasure + the atomic-cut splice

`Zef2` has NO `⊤/⊥/⋏/⋎` rules, so formulas of those shapes are never principal — they can be
erased from any context (`Zef2.erase_inert`).  This closes the top-rank cut for the four inert
cut-formula shapes.  The two atomic shapes (`rel`/`nrel`) are closed by the flagged atom-cut
lemma (`atomCutRun_Zf2`, the axL-pair surgery — a fixed-premise mirror of the running
reduction).  The two quantifier shapes are `stepAllω_Zf2_bnd`. -/

/-- A formula shape never principal in any `Zef2` rule. -/
def InertForm (A : Form) : Prop :=
  (∀ (ar : ℕ) (r : (ℒₒᵣ).Rel ar) (v : Fin ar → Semiterm ℒₒᵣ ℕ 0),
      A ≠ Semiformula.rel r v ∧ A ≠ Semiformula.nrel r v) ∧
  ∀ (χ : SyntacticSemiformula ℒₒᵣ 1), A ≠ (∀⁰ χ) ∧ A ≠ (∃⁰ χ)

theorem inertForm_verum : InertForm ⊤ :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

theorem inertForm_falsum : InertForm ⊥ :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

theorem inertForm_and (φ₁ φ₂ : Form) : InertForm (φ₁ ⋏ φ₂) :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

theorem inertForm_or (φ₁ φ₂ : Form) : InertForm (φ₁ ⋎ φ₂) :=
  ⟨fun _ _ _ => ⟨nofun, nofun⟩, fun _ => ⟨nofun, nofun⟩⟩

/-- **Inert erasure**: a formula of inert shape can be erased from any `Zef2` context (it is
never principal, so every rule commutes; instance formulas `χ/[nm n]` that happen to EQUAL the
inert formula are restored by plain `wk`).  All gates ride unchanged (same `α`, same `f`). -/
theorem Zef2.erase_inert {A : Form} (hA : InertForm A) :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2 α e H f c Γ → Zef2 α e H f c (Γ.erase A) := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      exact Zef2.axL hαN r v
        (Finset.mem_erase.mpr ⟨Ne.symm (hA.1 _ r v).1, hp⟩)
        (Finset.mem_erase.mpr ⟨Ne.symm (hA.1 _ r v).2, hn⟩)
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      exact Zef2.wk hαN (Finset.erase_subset_erase A hsub) ih
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      exact Zef2.weak hαN hβ hβNF hαNF hβH (Finset.erase_subset_erase A hsub) ih
  | @allω α e H f c Γ₀ hαN χ β hβ hβNF hαNF hβH dd ih =>
      have hne : (∀⁰ χ) ≠ A := Ne.symm (hA.2 χ).1
      have hgoal : (insert (∀⁰ χ) Γ₀).erase A = insert (∀⁰ χ) (Γ₀.erase A) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hxA, rfl | hx⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxA, hx⟩
        · rintro (rfl | ⟨hxA, hx⟩)
          · exact ⟨hne, Or.inl rfl⟩
          · exact ⟨hxA, Or.inr hx⟩
      rw [hgoal]
      refine Zef2.allω hαN χ β hβ hβNF hαNF hβH (fun n => ?_)
      exact (ih n).wk (Zef2.gate (ih n)) (by
        intro x hx
        simp only [Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  | @exI α β e H f c Γ₀ hαN χ n hβ hβNF hαNF hβH hbound _ ih =>
      have hne : (∃⁰ χ) ≠ A := Ne.symm (hA.2 χ).2
      have hgoal : (insert (∃⁰ χ) Γ₀).erase A = insert (∃⁰ χ) (Γ₀.erase A) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨hxA, rfl | hx⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hxA, hx⟩
        · rintro (rfl | ⟨hxA, hx⟩)
          · exact ⟨hne, Or.inl rfl⟩
          · exact ⟨hxA, Or.inr hx⟩
      rw [hgoal]
      refine Zef2.exI hαN χ n hβ hβNF hαNF hβH hbound ?_
      exact ih.wk (Zef2.gate ih) (by
        intro x hx
        simp only [Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  | @cut α βφ βψ e H f c Γ₀ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ ih₁ ih₂ =>
      refine Zef2.cut hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH
        (ih₁.wk (Zef2.gate ih₁) ?_) (ih₂.wk (Zef2.gate ih₂) ?_) <;>
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto

set_option maxHeartbeats 1000000 in
/-- **The atom-cut lemma (axL-pair surgery)** — the `c = 0`-shape sub-crux of the top-rank
cut, at general rank.  A fixed premise `D₂` deriving `insert (nrel rr vv) Γ` is spliced into a
derivation of a context containing `rel rr vv`: every axL leaf whose pair IS `(rr, vv)` is
replaced by `D₂` (weakened); all other nodes rebuild at the fresh root `βψ + γ` with the
absorbing gate (`Nlog_add_le_comp` + the slot-threaded slack, exactly as in the running
reduction).  Output slot `g ∘ f`. -/
theorem atomCutRun_Zf2 {ar : ℕ} {rr : (ℒₒᵣ).Rel ar} {vv : Fin ar → Semiterm ℒₒᵣ ℕ 0}
    {c : ℕ} {βψ e : ONote} {Γ : Seq} {g : ℕ → ℕ} {H₂ : ONote → Prop}
    (hβψNF : βψ.NF) (heNF : e.NF)
    (hg_mono : Monotone g) (hg_infl : ∀ x, x ≤ g x)
    (D₂ : Zef2 βψ e H₂ g c (insert (Semiformula.nrel rr vv) Γ)) :
    ∀ {γ : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Δ : Seq}, Zef2 γ e H f c Δ → γ.NF →
      Monotone f → (∀ x, x ≤ f x) → (∀ k, f 0 ≤ k → max (g 0) k + 1 ≤ g k) →
      Zef2Prov (βψ + γ) e H (g ∘ f) c (Δ.erase (Semiformula.rel rr vv) ∪ Γ) := by
  have hg0 : Nlog βψ ≤ g 0 := Zef2.gate D₂
  intro γ H f Δ D
  induction D with
  | @axL γ e H f c Δ ar' hαN r v hp hn =>
      intro hγNF hmono hinfl hsl
      by_cases hsplice : Semiformula.rel r v = Semiformula.rel rr vv
      · -- the pair IS the cut atom: splice `D₂` (its `nrel` support is in `Δ`, hence survives)
        have hnrel : Semiformula.nrel r v = Semiformula.nrel rr vv := by
          have := congrArg (∼·) hsplice
          simpa using this
        have hnmem : Semiformula.nrel rr vv ∈ Δ.erase (Semiformula.rel rr vv) ∪ Γ :=
          Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hnrel ▸ hn⟩)
        have hgate : Nlog βψ ≤ (g ∘ f) 0 := le_trans hg0 (hg_mono (Nat.zero_le _))
        refine ⟨βψ, Zekd.le_add_right_NF hβψNF hγNF, hβψNF, Cl_of_NF hβψNF, hgate, ?_⟩
        exact ((D₂.change_H (H' := H)).mono_f (fun x => hg_mono (hinfl x))).wk hgate (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxΓ
          · exact hnmem
          · exact Finset.mem_union_right _ hxΓ)
      · -- ordinary axL: the pair survives the erasure; keep the ordinal `γ` (no fresh root)
        have hgate : Nlog γ ≤ (g ∘ f) 0 := le_trans hαN (hg_infl (f 0))
        refine ⟨γ, Zekd.le_add_left_NF hβψNF hγNF, hγNF, Cl_of_NF hγNF, hgate, ?_⟩
        exact Zef2.axL hgate r v
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hsplice, hp⟩))
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hn⟩))
  | @wk γ e H f c Δsub Δsup hαN hsub D' ih =>
      intro hγNF hmono hinfl hsl
      exact (ih heNF D₂ hγNF hmono hinfl hsl).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxs⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxs⟩
        · exact Or.inr hxΓ)
  | @weak γ β e H f c Δsub Δsup hαN hβ hβNF hγNF' hβH hsub D' ih =>
      intro hγNF hmono hinfl hsl
      exact ((ih heNF D₂ hβNF hmono hinfl hsl).weakening (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
        rcases hx with ⟨hne, hxs⟩ | hxΓ
        · exact Or.inl ⟨hne, hsub hxs⟩
        · exact Or.inr hxΓ)).mono
        (le_of_lt (Zekd.add_lt_add_left_NF hβψNF hβNF hγNF hβ))
  | @allω γ e H f c Γ₀ hαN χ β hβ hβNF hγNF' hβH dd ih =>
      intro hγNF hmono hinfl hsl
      have hhead : (∀⁰ χ) ≠ Semiformula.rel rr vv := (fun h => by cases h)
      have haddNF : (βψ + γ).NF := ONote.add_nf βψ γ
      have ihn : ∀ n, Zef2Prov (βψ + β n) e (adjoin H n) (g ∘ rel1 f n) c
          (insert (χ/[nm n]) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) := by
        intro n
        refine (ih n heNF D₂ (hβNF n) (rel1_monotone hmono n)
          (rel1_infl hinfl n)
          (fun k hk => hsl k (le_trans (by
            simp only [rel1]; exact hmono (Nat.zero_le _)) hk))).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2Prov.of haddNF (Cl_of_NF haddNF)
        (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hAll : Zef2 (βψ + γ) e H (g ∘ f) c
          (insert (∀⁰ χ) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) := by
        exact Zef2.allω (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) χ
          (fun n => (ihn n).choose)
          (fun n => lt_of_le_of_lt (ihn n).choose_spec.1
            (Zekd.add_lt_add_left_NF hβψNF (hβNF n) hγNF (hβ n)))
          (fun n => (ihn n).choose_spec.2.1) haddNF
          (fun n => Cl_of_NF (ihn n).choose_spec.2.1)
          (fun n => (ihn n).choose_spec.2.2.2.2)
      exact hAll.wk (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)
  | @exI γ β e H f c Γ₀ hαN χ n hβ hβNF hγNF' hβH hbound dχ ih =>
      intro hγNF hmono hinfl hsl
      have hhead : (∃⁰ χ) ≠ Semiformula.rel rr vv := (fun h => by cases h)
      have haddNF : (βψ + γ).NF := ONote.add_nf βψ γ
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ :=
        ih heNF D₂ hβNF hmono hinfl hsl
      have Da' : Zef2 a e H (g ∘ f) c
          (insert (χ/[nm n]) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) :=
        Da.wk hag (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2Prov.of haddNF (Cl_of_NF haddNF)
        (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      have hbound' : n ≤ (g ∘ f) 0 := le_trans hbound (hg_infl (f 0))
      exact Zef2.exI (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) χ n
        (lt_of_le_of_lt hale (Zekd.add_lt_add_left_NF hβψNF hβNF hγNF hβ))
        haNF haddNF haH hbound' Da'
      |>.wk (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhead, Or.inl rfl⟩
        · tauto)
  | @cut γ βφ' βψ' e H f c Γ₀ hαN χ hχc hcutRead' hβφ hβψ' hβφNF hβψNF' hγNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hγNF hmono hinfl hsl
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, Dc₁⟩ :=
        ih₁ heNF D₂ hβφNF hmono hinfl hsl
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, Dc₂⟩ :=
        ih₂ heNF D₂ hβψNF' hmono hinfl hsl
      have haddNF : (βψ + γ).NF := ONote.add_nf βψ γ
      have Dc₁' : Zef2 a₁ e H (g ∘ f) c
          (insert χ (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) :=
        Dc₁.wk ha₁g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have Dc₂' : Zef2 a₂ e H (g ∘ f) c
          (insert (∼χ) (Γ₀.erase (Semiformula.rel rr vv) ∪ Γ)) :=
        Dc₂.wk ha₂g (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      refine Zef2Prov.of haddNF (Cl_of_NF haddNF)
        (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) ?_
      exact Zef2.cut (Nlog_add_le_comp hβψNF hγNF hg0 hαN (hsl _ le_rfl)) χ hχc
        (le_trans hcutRead' (hg_infl (f 0)))
        (lt_of_le_of_lt ha₁le (Zekd.add_lt_add_left_NF hβψNF hβφNF hγNF hβφ))
        (lt_of_le_of_lt ha₂le (Zekd.add_lt_add_left_NF hβψNF hβψNF' hγNF hβψ'))
        ha₁NF ha₂NF haddNF ha₁H ha₂H Dc₁' Dc₂'

/-! ## The cut-elimination pass (P-e) — Stage-3 grind (UNLOCKED); `passAux` is the induction -/

/-- **`passAux`** — the cut-elimination pass as a generalized induction, threading
`Monotone f ∧ (∀x,x≤f x) ∧ (∀m,2m+1≤f m)` (NOT `EwF1`: the `2m+1` bound is what `ewN_collapse_le`
needs and it, unlike strict monotonicity, is PRESERVED by the `allω`-branch relativization `rel1 f n`
via `rel1_low`).  The rank is generalized to a variable `r` (with `r = c+1`) so `induction` can fire.
Structural cases (`axL`/`wk`/`weak`) DISCHARGED via the banked pass-prep engine:
- `axL`: build at `collapse α` with node gate `ewN_collapse_le`;
- `wk`: IH + `Zef2Prov.weakening`;
- `weak`: IH at `β<α` + ordinal-lift (`collapse_strictMono`) + slot-lift (`ewIter_slot_le`).

Three cases remain as disclosed sub-`sorry`s (the crux decomposition):
- `exI`: like `weak` + rebuild the `∃` node (bound `n ≤ ewIter f α 0`);
- `allω`: the ω-branch reassembly (IH at `rel1 f n` branches, recombine via `ewIter_rel1_le`);
- `cut`: sub-rank rebuild (χ.complexity < c) OR TOP-rank eliminate (χ.complexity = c, ∀/∃ →
  `stepAllω_Zf2` + `collapse_add_lt` + `ewIter_comp_le`; the c=0 atomic case needs an atom-cut lemma).
-/
theorem passAux (c : ℕ) {e : ONote} (heNF : e.NF) :
    ∀ {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq} {r : ℕ},
      Zef2 α e H f r Γ → r = c + 1 → Monotone f → (∀ x, x ≤ f x) → (∀ m, 2 * m + 1 ≤ f m) →
      α.NF → Cl H α →
      Zef2Prov (collapse α) e H (ewIter f α) c Γ := by
  intro α H f Γ r D
  induction D with
  | @axL α e H f r Γ ar hαN rel v hp hn =>
      intro hr hmono hinfl hlow hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      exact Zef2Prov.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg
        (Zef2.axL hg rel v hp hn)
  | @wk α e H f r Δ Γ hαN hsub D' ih =>
      intro hr hmono hinfl hlow hαNF hαH
      exact (ih heNF hr hmono hinfl hlow hαNF hαH).weakening hsub
  | @weak α β e H f r Δ Γ hαN hβ hβNF hαNF' hβH hsub D' ih =>
      intro hr hmono hinfl hlow hαNF hαH
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih heNF hr hmono hinfl hlow hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2.gate D')
      exact ⟨a, le_trans hale (le_of_lt (collapse_strictMono hβNF hβ)), haNF, haH,
        le_trans hag (hslot 0), (Da.mono_f hslot).wk (le_trans hag (hslot 0)) hsub⟩
  | @allω α e H f r Γ hαN χ β hβ hβNF hαNF' hβH dd ih =>
      intro hr hmono hinfl hlow hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      have hbranch : ∀ n, Zef2Prov (collapse (β n)) e (adjoin H n)
          (ewIter (rel1 f n) (β n)) c (insert (χ/[nm n]) Γ) := fun n =>
        ih n heNF hr (rel1_monotone hmono n) (rel1_infl hinfl n) (rel1_low hmono hlow n)
          (hβNF n) (Cl_of_NF (hβNF n))
      choose a hale haNF haH hagate Da using hbranch
      have hlift : ∀ n x, ewIter (rel1 f n) (β n) x ≤ rel1 (ewIter f α) n x := by
        intro n x
        refine le_trans (ewIter_rel1_le hmono hinfl (β n) n x) ?_
        have hgate : Nlog (β n) ≤ f (Nlog α + max n x) := by
          have hgn := Zef2.gate (dd n)
          simp only [rel1] at hgn
          refine le_trans hgn (hmono ?_)
          omega
        simpa [rel1] using ewIter_le_of_lt (f := f) hinfl (hβNF n) (hβ n) hgate
      have Da' : ∀ n, Zef2 (a n) e (adjoin H n) (rel1 (ewIter f α) n) c
          (insert (χ/[nm n]) Γ) := fun n => (Da n).mono_f (hlift n)
      have haltcol : ∀ n, a n < collapse α :=
        fun n => lt_of_le_of_lt (hale n) (collapse_strictMono (hβNF n) (hβ n))
      refine Zef2Prov.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2.allω hg χ a haltcol haNF (collapse_NF hαNF)
        (fun n => Cl_of_NF (haNF n)) Da'
  | @exI α β e H f r Γ hαN χ n hβ hβNF hαNF' hβH hbound dχ ih =>
      intro hr hmono hinfl hlow hαNF hαH
      obtain ⟨a, hale, haNF, haH, hag, Da⟩ := ih heNF hr hmono hinfl hlow hβNF (Cl_of_NF hβNF)
      have hslot := ewIter_slot_le hmono hinfl hβNF hβ (Zef2.gate dχ)
      have haltcol : a < collapse α := lt_of_le_of_lt hale (collapse_strictMono hβNF hβ)
      have hg := Nlog_collapse_le hlow hαN
      have hf0 : f 0 ≤ ewIter f α 0 := by
        by_cases h0 : α = 0
        · subst h0; simp
        · have h0α : (0 : ONote) < α := by
            cases α with
            | zero => exact (h0 rfl).elim
            | oadd e n a => exact oadd_pos e n a
          have := ewIter_le_of_lt (f := f) hinfl (β := 0) (α := α) (m := 0) NF.zero h0α (Nat.zero_le _)
          simpa [ewIter_zero] using this
      have hbound' : n ≤ ewIter f α 0 := le_trans hbound hf0
      refine Zef2Prov.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
      exact Zef2.exI hg χ n haltcol haNF (collapse_NF hαNF) haH hbound'
        ((Da.mono_f hslot).wk (le_trans hag (hslot 0)) (Finset.Subset.refl _))
  | @cut α βφ βψ e H f r Γ hαN χ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF' hβφH hβψH d₁ d₂ ih₁ ih₂ =>
      intro hr hmono hinfl hlow hαNF hαH
      have hg := Nlog_collapse_le hlow hαN
      have hf0 : f 0 ≤ ewIter f α 0 := by
        by_cases h0 : α = 0
        · subst h0; simp
        · have h0α : (0 : ONote) < α := by
            cases α with
            | zero => exact (h0 rfl).elim
            | oadd e n a => exact oadd_pos e n a
          have := ewIter_le_of_lt (f := f) hinfl (β := 0) (α := α) (m := 0) NF.zero h0α (Nat.zero_le _)
          simpa [ewIter_zero] using this
      by_cases hc : χ.complexity < c
      · -- SUB-RANK cut: cut formula below the pass's max rank — keep the cut, rebuild at rank `c`
        -- with both premises IH-reduced and slot-lifted to the common `ewIter f α`.
        obtain ⟨aφ, haφle, haφNF, haφH, haφg, Dφ⟩ :=
          ih₁ heNF hr hmono hinfl hlow hβφNF (Cl_of_NF hβφNF)
        obtain ⟨aψ, haψle, haψNF, haψH, haψg, Dψ⟩ :=
          ih₂ heNF hr hmono hinfl hlow hβψNF (Cl_of_NF hβψNF)
        have hsφ := ewIter_slot_le hmono hinfl hβφNF hβφ (Zef2.gate d₁)
        have hsψ := ewIter_slot_le hmono hinfl hβψNF hβψ (Zef2.gate d₂)
        have haφcol : aφ < collapse α := lt_of_le_of_lt haφle (collapse_strictMono hβφNF hβφ)
        have haψcol : aψ < collapse α := lt_of_le_of_lt haψle (collapse_strictMono hβψNF hβψ)
        refine Zef2Prov.of (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF)) hg ?_
        exact Zef2.cut hg χ hc (le_trans hcutRead hf0) haφcol haψcol
          haφNF haψNF (collapse_NF hαNF) haφH haψH (Dφ.mono_f hsφ) (Dψ.mono_f hsψ)
      · -- TOP-RANK cut: `χ.complexity = c`.  ELIMINATE the cut (E–W Lemma 26 principal step),
        -- by the shape of `χ`: quantifier shapes → `stepAllω_Zf2_bnd` (slack = `hslack_kit_ge`)
        -- + `collapse_add_lt` + `ewIter_comp_le`; atomic shapes → `atomCutRun_Zf2` (the axL-pair
        -- surgery); inert shapes (`⊤/⊥/⋏/⋎`, never principal) → `Zef2.erase_inert`.
        have hgφ : Nlog βφ ≤ f 0 := Zef2.gate d₁
        have hgψ : Nlog βψ ≤ f 0 := Zef2.gate d₂
        have hcomp : ∀ m, ewIter f βφ (ewIter f βψ m) ≤ ewIter f α m :=
          ewIter_comp_le hmono hinfl hβφNF hβψNF hβφ hβψ hgφ hgψ
        have hcomp' : ∀ m, ewIter f βψ (ewIter f βφ m) ≤ ewIter f α m :=
          ewIter_comp_le hmono hinfl hβψNF hβφNF hβψ hβφ hgψ hgφ
        have hcollt : collapse βφ + collapse βψ < collapse α :=
          collapse_add_lt hβφNF hβψNF hαNF hβφ hβψ
        have hcollt' : collapse βψ + collapse βφ < collapse α :=
          collapse_add_lt hβψNF hβφNF hαNF hβψ hβφ
        have P₁ := ih₁ heNF hr hmono hinfl hlow hβφNF (Cl_of_NF hβφNF)
        have P₂ := ih₂ heNF hr hmono hinfl hlow hβψNF (Cl_of_NF hβψNF)
        -- the inert-shape discharge, shared by ⊤/⊥/⋏/⋎
        have inert_case : InertForm χ → Zef2Prov (collapse α) e H (ewIter f α) c Γ := by
          intro hInert
          obtain ⟨a, hale, haNF, haH, hag, Da⟩ := P₁
          have hslot := ewIter_slot_le hmono hinfl hβφNF hβφ hgφ
          have hDa2 : Zef2 a e H (ewIter f βφ) c ((insert χ Γ).erase χ) :=
            Zef2.erase_inert hInert Da
          rw [Finset.erase_insert_eq_erase] at hDa2
          have hDa3 : Zef2 a e H (ewIter f βφ) c Γ :=
            hDa2.wk hag (Finset.erase_subset _ _)
          exact ⟨a, le_trans hale (le_of_lt (collapse_strictMono hβφNF hβφ)), haNF, haH,
            le_trans hag (hslot 0), hDa3.mono_f hslot⟩
        cases χ with
        | verum => exact inert_case inertForm_verum
        | falsum => exact inert_case inertForm_falsum
        | and φ₁ φ₂ => exact inert_case (inertForm_and φ₁ φ₂)
        | or φ₁ φ₂ => exact inert_case (inertForm_or φ₁ φ₂)
        | rel r' v' =>
            -- `∼(rel r' v') = nrel r' v'`: fixed side = the ψ-premise
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂w⟩ := P₂
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁w⟩ := P₁
            have hrun := atomCutRun_Zf2 ha₂NF heNF (ewIter_monotone hmono hinfl βψ)
              (ewIter_infl hinfl βψ) D₂w D₁w ha₁NF (ewIter_monotone hmono hinfl βφ)
              (ewIter_infl hinfl βφ) (hslack_kit_ge hmono hinfl hlow βψ βφ)
            have hrun' := hrun.weakening (Δ := Γ) (by
              intro x hx
              simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx
              tauto)
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hrun'
            have hsum : a₂ + a₁ ≤ collapse βψ + collapse βφ := by
              haveI := ha₂NF; haveI := ha₁NF
              haveI := collapse_NF hβψNF; haveI := collapse_NF hβφNF
              haveI := ONote.add_nf a₂ a₁
              haveI := ONote.add_nf (collapse βψ) (collapse βφ)
              rw [le_def, repr_add, repr_add]
              exact add_le_add (le_def.mp ha₂le) (le_def.mp ha₁le)
            exact ⟨w, le_trans hwle (le_trans hsum (le_of_lt hcollt')), hwNF, hwH,
              le_trans hwg (hcomp' 0), Dw.mono_f hcomp'⟩
        | nrel r' v' =>
            -- `∼(nrel r' v') = rel r' v'`: fixed side = the φ-premise
            obtain ⟨a₁, ha₁le, ha₁NF, ha₁H, ha₁g, D₁w⟩ := P₁
            obtain ⟨a₂, ha₂le, ha₂NF, ha₂H, ha₂g, D₂w⟩ := P₂
            have hrun := atomCutRun_Zf2 ha₁NF heNF (ewIter_monotone hmono hinfl βφ)
              (ewIter_infl hinfl βφ) D₁w D₂w ha₂NF (ewIter_monotone hmono hinfl βψ)
              (ewIter_infl hinfl βψ) (hslack_kit_ge hmono hinfl hlow βφ βψ)
            have hrun' := hrun.weakening (Δ := Γ) (by
              intro x hx
              simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx
              tauto)
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hrun'
            have hsum : a₁ + a₂ ≤ collapse βφ + collapse βψ := by
              haveI := ha₁NF; haveI := ha₂NF
              haveI := collapse_NF hβφNF; haveI := collapse_NF hβψNF
              haveI := ONote.add_nf a₁ a₂
              haveI := ONote.add_nf (collapse βφ) (collapse βψ)
              rw [le_def, repr_add, repr_add]
              exact add_le_add (le_def.mp ha₁le) (le_def.mp ha₂le)
            exact ⟨w, le_trans hwle (le_trans hsum (le_of_lt hcollt)), hwNF, hwH,
              le_trans hwg (hcomp 0), Dw.mono_f hcomp⟩
        | all ψ =>
            have h : (Semiformula.all ψ : Form).complexity = ψ.complexity + 1 := rfl
            have hψc : ψ.complexity < c := by omega
            have hread : ψ.complexity ≤ ewIter f βψ 0 := by
              have h2 : ψ.complexity ≤ f 0 := by omega
              exact le_trans h2 (ewIter_base_le hinfl βψ)
            have hstep := stepAllω_Zf2_bnd (collapse_NF hβφNF) (collapse_NF hβψNF) heNF hψc
              (ewIter_monotone hmono hinfl βφ) (ewIter_infl hinfl βφ)
              (hslack_kit_ge hmono hinfl hlow βφ βψ)
              (ewIter_monotone hmono hinfl βψ) (ewIter_infl hinfl βψ) hread P₁ P₂
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hstep
            exact ⟨w, le_trans hwle (le_of_lt hcollt), hwNF, hwH,
              le_trans hwg (hcomp 0), Dw.mono_f hcomp⟩
        | exs ψ =>
            have h : (Semiformula.exs ψ : Form).complexity = ψ.complexity + 1 := rfl
            have h2 : (∼ψ).complexity = ψ.complexity := Semiformula.complexity_neg ψ
            have hψc : (∼ψ).complexity < c := by omega
            have hread : (∼ψ).complexity ≤ ewIter f βφ 0 := by
              have h3 : (∼ψ).complexity ≤ f 0 := by omega
              exact le_trans h3 (ewIter_base_le hinfl βφ)
            -- roles swap: the ψ-premise carries `∀⁰ ∼ψ` (= `∼(∃⁰ ψ)`, rfl); the φ-premise
            -- carries `∃⁰ ψ = ∃⁰ ∼∼ψ`
            have P₁' : Zef2Prov (collapse βφ) e H (ewIter f βφ) c (insert (∃⁰ ∼(∼ψ)) Γ) := by
              have hnn : (∼(∼ψ)) = ψ := by simp
              rw [hnn]
              exact P₁
            have hstep := stepAllω_Zf2_bnd (collapse_NF hβψNF) (collapse_NF hβφNF) heNF hψc
              (ewIter_monotone hmono hinfl βψ) (ewIter_infl hinfl βψ)
              (hslack_kit_ge hmono hinfl hlow βψ βφ)
              (ewIter_monotone hmono hinfl βφ) (ewIter_infl hinfl βφ) hread P₂ P₁'
            obtain ⟨w, hwle, hwNF, hwH, hwg, Dw⟩ := hstep
            exact ⟨w, le_trans hwle (le_of_lt hcollt'), hwNF, hwH,
              le_trans hwg (hcomp' 0), Dw.mono_f hcomp'⟩

/-- **PIN → THEOREM (Stage-3, in grind): one cut-ELIMINATION pass over `Zef2`.**  E–W Lemma 26/27's
single predicative rank step: the ordinal COLLAPSES (`collapse α`) and the numeric slot ITERATES
(`ewIter f α`).  Now a real derivation from `passAux` (its three remaining sub-`sorry`s are the
disclosed crux decomposition). -/
theorem cutElimPass_Zef2 {α e : ONote} {H : ONote → Prop} {c : ℕ} {Γ : Seq} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2 α e H f (c + 1) Γ) (hf1 : EwF1 f) (_hf2 : EwF2 f) :
    Zef2Prov (collapse α) e H (ewIter f α) c Γ :=
  passAux c heNF D rfl hf1.monotone hf1.infl hf1.2 hαNF hαH

/-- **§7b The C3 composed exit over `Zef2`** — the anti-vacuity test: ONE elimination pass
(`cutElimPass_Zef2`, rank `1 → 0`) composed with `headline_readoff_Zef2`, at the concrete
`ewRootSlot`.  The `ewIter (ewRootSlot e m) α 0` iterate is VISIBLE in the bound and is what the
read-off reads.  Real derivation from the pin + the read-off. -/
theorem cutElimPass_exit_root_Zef2 {α e : ONote} {H : ONote → Prop} {m : ℕ}
    {φ : SyntacticSemiformula ℒₒᵣ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2 α e H (ewRootSlot e m) (0 + 1) {(∃⁰ φ)}) :
    ∃ n ≤ ewIter (ewRootSlot e m) α 0, atomTrue (φ/[nm n]) := by
  obtain ⟨α', _, _, _, _, D'⟩ :=
    cutElimPass_Zef2 (ewRootSlot e m) heNF hαNF hαH D
      (ewRootSlot_f1 e m) (ewRootSlot_f2 e m)
  exact headline_readoff_Zef2 hφinst D'

/-! ## The wainer ladder (L-items) — the four rungs as named pins (lap-8 erection)

The rungs decompose the `wainer_bound_of_pa_proves_goodstein` monolith
(blueprint node 14, now in `Statement.lean`) into the E–W pipeline order.  All are sorry-bearing `theorem`s
(disclosed pins; raising the src sorry count IS the decomposition) — deliberately NOT
`@[goodstein_blueprint]`-tagged, because `BlueprintAudit` computes `broken` for any sorryAx
footprint (an axiom is FORBIDDEN this lap), so the rungs live on the tex dep-graph
(`thm:zeh_rank_zero`/`thm:zeh_embedding`/`thm:wainer_splice`, `\lean{}`-bound), not the machine
ledger.  Ledger metadata is carried in each docstring. -/

/-- **`rankToZeroAux`** — the EwLow-threaded rung-R induction.  Threads
`Monotone ∧ inflationary ∧ (2m+1 ≤ ·)` (NOT `EwF1`: `ewIter` does not inherit strict monotonicity,
but it DOES inherit these three via `ewIter_monotone`/`_infl`/`_low`, so the pass ITERATES).  Each
step applies one `passAux`, promotes the reduced witness UP to `collapse α` exactly (`Zef2.weak`,
gate `ewN_collapse_le`), recurses, and rewrites via the two tower-shift lemmas. -/
theorem rankToZeroAux (e : ONote) (heNF : e.NF) :
    ∀ (d : ℕ) {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Seq},
      Zef2 α e H f d Γ → Monotone f → (∀ x, x ≤ f x) → (∀ m, 2 * m + 1 ≤ f m) →
      α.NF → Cl H α →
      Zef2Prov (collapseIter d α) e H (ewIterTower f d α) 0 Γ := by
  intro d
  induction d with
  | zero =>
      intro α H f Γ D hmono hinfl hlow hαNF hαH
      exact Zef2Prov.of hαNF hαH (Zef2.gate D) D
  | succ d ih =>
      intro α H f Γ D hmono hinfl hlow hαNF hαH
      obtain ⟨β, hβle, hβNF, hβH, hβgate, Dβ⟩ :=
        passAux d heNF D rfl hmono hinfl hlow hαNF hαH
      have hg := Nlog_collapse_le hlow (Zef2.gate D)
      have Dcol : Zef2 (collapse α) e H (ewIter f α) d Γ := by
        rcases lt_or_eq_of_le (le_def.mp hβle) with hlt | heq
        · exact Zef2.weak hg (lt_def.mpr hlt) hβNF (collapse_NF hαNF) hβH
            (Finset.Subset.refl Γ) Dβ
        · have hβeq : β = collapse α := by
            haveI := hβNF; haveI := collapse_NF hαNF
            exact repr_inj.mp heq
          exact hβeq ▸ Dβ
      have hrec := ih Dcol (ewIter_monotone hmono hinfl α) (ewIter_infl hinfl α)
        (fun m => ewIter_low hinfl hlow α m) (collapse_NF hαNF) (Cl_of_NF (collapse_NF hαNF))
      rw [collapseIter_collapse α d, ewIterTower_collapse f α d] at hrec
      exact hrec

/-- **RUNG R (L-R) `rankToZero_Zef2`** — iterate `cutElimPass_Zef2` down the cut rank `d → 0`.
A plain induction over the pass (`rankToZeroAux`): `d` applications collapse the ordinal to
`collapseIter d α` and tower the slot to `ewIterTower f d α`, landing at rank 0.  Now a REAL
derivation (reuses the pass; `EwF1 → EwLow` at the top).  **Ledger: debt, "1", 90** (rung R). -/
theorem rankToZero_Zef2 {α e : ONote} {H : ONote → Prop} {d : ℕ} {Γ : Seq} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2 α e H f d Γ) (hf1 : EwF1 f) (_hf2 : EwF2 f) :
    Zef2Prov (collapseIter d α) e H (ewIterTower f d α) 0 Γ :=
  rankToZeroAux e heNF d D hf1.monotone hf1.infl hf1.2 hαNF hαH

/-- The numeral term `nm n` (`OperatorZinfty.nm`) evaluates to `n` under any standard-model
assignment — the value of a closed numeral const is assignment-independent.  Local companion of
`stdClosedVal_nm`, phrased with `valm ℕ` so it `rw`s inside `eval_substs` read-offs. -/
@[simp] lemma valm_nm (n : ℕ) (f : ℕ → ℕ) :
    GoodsteinPA.Compat.gValm ℕ ![] f (nm n) = n := by simp [nm]

/-- **Rank-0 `Zef2` soundness** (the reusable truth core of the Δ₀ read-off).  A cut-free
derivation of `Γ` has a standard-model-true member.  The `allω` (Π) case combines: either some
branch's true member is in the shared context `Γ` (done), or every branch is true at its own
instance `φ/[nm n]` — whence `∀⁰ φ` is true (`atomTrue (∀⁰ φ) = ∀ k, atomTrue (φ/[nm k])`).
Slot-INDEPENDENT (truth does not see `f`).  Ported from `wip/Lap13ReadoffDeltaProbe.lean`. -/
theorem sound0 : ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
    Zef2 α e H f c Γ → c = 0 → ∃ ψ ∈ Γ, atomTrue ψ := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _
      by_cases htrue : atomTrue (Semiformula.rel r v)
      · exact ⟨_, hp, htrue⟩
      · refine ⟨_, hn, ?_⟩
        simpa [atomTrue, Semiformula.eval_nrel, Semiformula.eval_rel, Function.comp_def] using htrue
  | @wk α e H f c Δ Γ hαN hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @weak α β e H f c Δ Γ hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      exact ⟨ψ, hsub hψ, htrue⟩
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH _ ih =>
      intro hc
      rcases Classical.em (∃ n : ℕ, ∃ ψ ∈ Γ, atomTrue ψ) with hctx | hctx
      · obtain ⟨n, ψ, hψ, htrue⟩ := hctx
        exact ⟨ψ, Finset.mem_insert_of_mem hψ, htrue⟩
      · refine ⟨∀⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        have hall : ∀ n, atomTrue (φ/[nm n]) := by
          intro n
          obtain ⟨ψ, hψ, htrue⟩ := ih n hc
          rcases Finset.mem_insert.mp hψ with rfl | hψΓ
          · exact htrue
          · exact absurd ⟨n, ψ, hψΓ, htrue⟩ hctx
        simp only [atomTrue, Semiformula.eval_all]
        intro x
        have hx := hall x
        simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hx
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound _ ih =>
      intro hc
      obtain ⟨ψ, hψ, htrue⟩ := ih hc
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · refine ⟨∃⁰ φ, Finset.mem_insert_self _ _, ?_⟩
        simp only [atomTrue, Semiformula.eval_ex]
        exact ⟨n, by
          simpa [atomTrue, Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using htrue⟩
      · exact ⟨ψ, Finset.mem_insert_of_mem hψΓ, htrue⟩
  | @cut α βφ βψ e H f c Γ hαN φ hcompl hcutRead _ _ _ _ _ _ _ _ _ _ _ =>
      intro hc; subst hc
      exact absurd hcompl (by omega)

/-- `atomTrue (∀⁰ χ) ↔ ∀ k, atomTrue (χ/[nm k])` — a standard ω-universal is standard-model-true
iff every numeral instance is true.  (`∀⁰` at the top of a Δ₀ read-off descends to its instances.) -/
theorem atomTrue_all_iff (χ : SyntacticSemiformula ℒₒᵣ 1) :
    atomTrue (∀⁰ χ) ↔ ∀ k, atomTrue (χ/[nm k]) := by
  simp only [atomTrue, Semiformula.eval_all]
  constructor
  · intro h k
    have hk := h k
    simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hk
  · intro h x
    have hx := h x
    simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hx

/-- `atomTrue (∃⁰ χ) ↔ ∃ k, atomTrue (χ/[nm k])` — dual of `atomTrue_all_iff`. -/
theorem atomTrue_ex_iff (χ : SyntacticSemiformula ℒₒᵣ 1) :
    atomTrue (∃⁰ χ) ↔ ∃ k, atomTrue (χ/[nm k]) := by
  simp only [atomTrue, Semiformula.eval_ex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hx⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa [Semiformula.eval_substs, valm_nm, Matrix.constant_eq_singleton] using hk⟩

/-- The **spine head** of a formula: strip the `∀/∃` quantifier spine; report the terminal's
polarity + relation symbol (arity-packed, so comparisons never pay the dependent-`Rel` tax), or
`none` for the `Zef2`-inert heads `⊤/⊥/⋏/⋎`. -/
def spineHead : ∀ {n}, SyntacticSemiformula ℒₒᵣ n → Option (Bool × ((k : ℕ) × (ℒₒᵣ).Rel k))
  | _, Semiformula.rel r _ => some (true, ⟨_, r⟩)
  | _, Semiformula.nrel r _ => some (false, ⟨_, r⟩)
  | _, Semiformula.all φ => spineHead φ
  | _, Semiformula.exs φ => spineHead φ
  | _, Semiformula.verum => none
  | _, Semiformula.falsum => none
  | _, Semiformula.and _ _ => none
  | _, Semiformula.or _ _ => none

/-- Rewriting (in particular substitution `φ/[nm n]`) preserves the spine head. -/
theorem spineHead_rew : ∀ {n₁ n₂} (om : Rew ℒₒᵣ ℕ n₁ ℕ n₂) (φ : SyntacticSemiformula ℒₒᵣ n₁),
    spineHead (om ▹ φ) = spineHead φ
  | _, _, om, Semiformula.rel r v => by simp [spineHead, Function.comp_def]
  | _, _, om, Semiformula.nrel r v => by simp [spineHead, Function.comp_def]
  | _, _, om, Semiformula.all φ => by
      rw [show (Semiformula.all φ) = ∀⁰ φ from rfl, Rewriting.app_all]
      simpa [spineHead] using spineHead_rew om.q φ
  | _, _, om, Semiformula.exs φ => by
      rw [show (Semiformula.exs φ) = ∃⁰ φ from rfl, Rewriting.app_exs]
      simpa [spineHead] using spineHead_rew om.q φ
  | _, _, om, Semiformula.verum => by
      rw [show (Semiformula.verum : SyntacticSemiformula ℒₒᵣ _) = ⊤ from rfl]
      simp [spineHead]
  | _, _, om, Semiformula.falsum => by
      rw [show (Semiformula.falsum : SyntacticSemiformula ℒₒᵣ _) = ⊥ from rfl]
      simp [spineHead]
  | _, _, om, Semiformula.and φ ψ => by
      rw [show (Semiformula.and φ ψ) = φ ⋏ ψ from rfl]
      simp [spineHead]
  | _, _, om, Semiformula.or φ ψ => by
      rw [show (Semiformula.or φ ψ) = φ ⋎ ψ from rfl]
      simp [spineHead]

@[simp] theorem spineHead_all (φ : SyntacticSemiformula ℒₒᵣ 1) :
    spineHead (∀⁰ φ) = spineHead φ := rfl

@[simp] theorem spineHead_exs (φ : SyntacticSemiformula ℒₒᵣ 1) :
    spineHead (∃⁰ φ) = spineHead φ := rfl

theorem spineHead_substs (φ : SyntacticSemiformula ℒₒᵣ 1) (n : ℕ) :
    spineHead (φ/[nm n]) = spineHead φ :=
  spineHead_rew _ φ

/-- **Uniform-spine sequents are rank-0 underivable.**  If every member of `Γ` has the SAME
spine head `t`, no `Zef2` derivation at cut-rank 0 exists: `axL` would force
`some (true, s) = t = some (false, s)`; `allω`/`exI` insert spine-head-preserving instances;
`wk`/`weak` shrink; `cut` needs `complexity < 0`. -/
theorem zef2_rank0_uniform_spine_underivable {t : Option (Bool × ((k : ℕ) × (ℒₒᵣ).Rel k))} :
    ∀ {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {c : ℕ} {Γ : Seq},
      Zef2 α e H f c Γ → c = 0 → (∀ ψ ∈ Γ, spineHead ψ = t) → False := by
  intro α e H f c Γ dd
  induction dd with
  | @axL α e H f c Γ ar hαN r v hp hn =>
      intro _ hyp
      have h1 := hyp _ hp
      have h2 := hyp _ hn
      rw [show spineHead (Semiformula.rel r v) = some (true, ⟨ar, r⟩) from rfl] at h1
      rw [show spineHead (Semiformula.nrel r v) = some (false, ⟨ar, r⟩) from rfl] at h2
      rw [← h2] at h1
      simp at h1
  | wk hαN hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | weak hαN hβ hβNF hαNF hβH hsub _ ih =>
      intro hc hyp
      exact ih hc (fun ψ hψ => hyp ψ (hsub hψ))
  | @allω α e H f c Γ hαN φ β hβ hβNF hαNF hβH dd ih =>
      intro hc hyp
      refine ih 0 hc ?_
      intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · rw [spineHead_substs]
        simpa using hyp (∀⁰ φ) (Finset.mem_insert_self _ _)
      · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
  | @exI α β e H f c Γ hαN φ n hβ hβNF hαNF hβH hbound dd ih =>
      intro hc hyp
      refine ih hc ?_
      intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψΓ
      · rw [spineHead_substs]
        simpa using hyp (∃⁰ φ) (Finset.mem_insert_self _ _)
      · exact hyp ψ (Finset.mem_insert_of_mem hψΓ)
  | cut hαN φ hcompl hcutRead hβφ hβψ hβφNF hβψNF hαNF hβφH hβψH _ _ _ _ =>
      intro hc _
      omega

/-- **The R-4′ source is VACUOUS: `Zef2` cannot derive `{∃⁰ φ}` at rank 0, for any `φ`.** -/
theorem zef2_rank0_singleton_ex_underivable {φ : SyntacticSemiformula ℒₒᵣ 1}
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} :
    ¬ Zef2 α e H f 0 {(∃⁰ φ)} := by
  intro dd
  refine zef2_rank0_uniform_spine_underivable (t := spineHead (∃⁰ φ)) dd rfl ?_
  intro ψ hψ
  rw [Finset.mem_singleton] at hψ
  rw [hψ]

/-- **The residue is SORRY-FREE under the local monotone-instance condition** (lap-195).  The
branch-0 mechanism (`rel1 f 0 = f`) already discharges every case where `χ/[nm 0]` is *false*; the
only survivor is `χ/[nm 0]` TRUE while `∀⁰ χ` is false.  If the matrix `χ` satisfies the natural
"`0`-instance is the easiest" condition `atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)` (a downward-closed
guard, as for the Goodstein bounded-`∀` clauses), that survivor is contradictory: `h0` forces
`atomTrue (∀⁰ χ)`, contradicting `hfalse`.  So under `hmono` the trap NEVER fires — this is the exact
fragment the structural read-off reaches without E–W's (Ax2).  A ready building block for a
monotone-guarded specialization of `readoff_delta0_Zef2`. -/
theorem readoffD_trapped_of_mono {φ χ : SyntacticSemiformula ℒₒᵣ 1}
    {e : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ₀ : Seq} {β : ℕ → ONote}
    (_hbranch : ∀ n, Zef2 (β n) e (adjoin H n) (rel1 f n) 0 (insert (χ/[nm n]) Γ₀))
    (_htrap : (∃⁰ φ) ∈ Γ₀)
    (hfalse : ¬ atomTrue (∀⁰ χ))
    (_hΓ₀ : ∀ ψ ∈ Γ₀, ψ = (∃⁰ φ) ∨ ¬ atomTrue ψ)
    (h0 : atomTrue (χ/[nm 0]))
    (hmono : atomTrue (χ/[nm 0]) → atomTrue (∀⁰ χ)) :
    ∃ n ≤ f 0, atomTrue (φ/[nm n]) :=
  absurd (hmono h0) hfalse

/-- **RUNG D (L-D) `readoff_delta0_Zef2`** — the Δ₀ (bounded-∀ matrix) read-off extension
(Towsner §5.4 pattern), re-homed to `Zef2`.  **R-4′ RESTATEMENT (Series-2 ruling (2), ratified
verbatim; executed Series-3 D-3): conclusion bound `f 0 → ewIter f α 0`** (the structurally
achievable bound; the splice consumes it at one definitional tower level, Stage C-1).  Earlier,
**R-4 RESTATEMENT (SERIES-1 order):** the old
`matrixTrue` form is deleted; `<BoundedInstance>` is discharged to the repo-native Foundation Δ₀
predicate `LO.FirstOrder.Arithmetic.DeltaZero` (= `Hierarchy 𝚺 0`) and the conclusion reads off the
standard-model truth `atomTrue = Evalm ℕ` of the instance directly.

Where `readoff_sigma1_Zef2` reads off an ATOMIC matrix (`hφinst : φ/[nm n]` atomic), this reads off
a Δ₀ instance: from a rank-0 `Zef2` derivation of the singleton `{∃⁰ φ}` whose instances
`φ/[nm n]` are Δ₀, extract a witness `n ≤ ewIter f α 0` with `atomTrue (φ/[nm n])`.

**`<BoundedInstance>` = `DeltaZero`, justified in `wip/Lap12BoundedInstanceProbe.lean` (committed,
2 candidates probed):** the `Zeh`/`Zef2` core has only `axL`/`allω`/`exI`/`cut` (no `∧`/`∨` rule), so
the read-off descends the instance through quantifiers/atoms only; `DeltaZero` is the repo-native Δ₀
notion, and its `∧`/`∨` heads are dead branches for the singleton read-off (a singleton `{A ⋏ B}` is
not `axL`-closable and has no ∧-rule ⇒ underivable).  The genuine grind is the `allω` (Π) case —
`atomTrue (∀⁰ χ) = ∀ k, Evalm (χ/[nm k])` needs every branch's matrix as its true disjunct + the Δ₀
bound to bound the load-bearing branches (Towsner §5.4).  **Ledger: debt, "2-3", 80** (rung D). -/
theorem readoff_delta0_Zef2 {φ : SyntacticSemiformula ℒₒᵣ 1}
    (_hφbdd : ∀ n, LO.FirstOrder.Arithmetic.DeltaZero (φ/[nm n]))
    {α e : ONote} {H : ONote → Prop} {f : ℕ → ℕ}
    (dd : Zef2 α e H f 0 {(∃⁰ φ)}) :
    ∃ n ≤ ewIter f α 0, atomTrue (φ/[nm n]) :=
  -- D-3 (Series-3): the R-4′-ratified conclusion, landed via VACUITY — the source `dd` cannot
  -- exist (`zef2_rank0_singleton_ex_underivable`: `Zef2` without E–W's (Ax2) has no closure for
  -- a uniform-spine singleton).  The abandoned structural route (falsity invariant
  -- `readoffD_aux` + trapped residue) is parked verbatim in `wip/ReadoffDAuxRetired.lean`; its
  -- `allω` trapped case is NOT closable even at this bound (semantic `k₀` overflows the
  -- `ewIter` budget — see the retirement note there).  The `hφbdd` Δ₀ premise is part of the
  -- ratified text; it is not consumed by the vacuity route.
  (zef2_rank0_singleton_ex_underivable dd).elim

/- **Rungs E (embedding) and W (splice) MOVED to `GoodsteinPA/WainerLadder.lean`** (Series-2
Stage A, order R-5/R-6).

- The old parametric `wainer_splice_Zef2 (e B α …) : … ewIter (ewRootSlot e B) α 0 ≤ …` was the
  lap-8-ruling L-W VOIDed-as-trivial shape; it is DELETED here and RESTATED at its ratified
  non-parametric shape (`(𝗣𝗔 ⊢ ↑goodsteinSentence) → ∃ o, …`) in `WainerLadder.lean`, which can
  public import the translation apparatus without the `OperatorZef2`-level cross-import obstruction.

- The old parametric `embedding_Zef2 (Γ_G e …)` was the lap-8-ruling §4 VOIDed placeholder (R-6
  debt); its faithful, translation-bound restatement is the Stage-B rung-E statement lap and
  stays a `wip/Ax2AdequacyProbe.lean` draft until the judge ratifies it.  A `TODO` for it lives
  in `WainerLadder.lean`. -/

end GoodsteinPA.OperatorZeh
