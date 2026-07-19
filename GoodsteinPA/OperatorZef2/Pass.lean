module

public import GoodsteinPA.OperatorZef2.GateArith
public import GoodsteinPA.OperatorZef2.CutStep

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## The cut-elimination pass (P-e); `passAux` is the induction -/

/-- **`passAux`** — the cut-elimination pass as a generalized induction, threading
`Monotone f ∧ (∀x,x≤f x) ∧ (∀m,2m+1≤f m)` (NOT `EwF1`: the `2m+1` bound is what `ewN_collapse_le`
needs and it, unlike strict monotonicity, is PRESERVED by the `allω`-branch relativization `rel1 f n`
via `rel1_low`).  The rank is generalized to a variable `r` (with `r = c+1`) so `induction` can fire.
Structural cases (`axL`/`wk`/`weak`) DISCHARGED via the banked pass-prep engine:
- `axL`: build at `collapse α` with node gate `ewN_collapse_le`;
- `wk`: IH + `Zef2Prov.weakening`;
- `weak`: IH at `β<α` + ordinal-lift (`collapse_strictMono`) + slot-lift (`ewIter_slot_le`).

The crux decomposition is in three cases:
- `exI`: like `weak` + rebuild the `∃` node (bound `n ≤ ewIter f α 0`);
- `allω`: the ω-branch reassembly (IH at `rel1 f n` branches, recombine via `ewIter_rel1_le`);
- `cut`: sub-rank rebuild (χ.complexity < c) OR TOP-rank eliminate (χ.complexity = c, ∀/∃ →
  `stepAllω_Zf2` + `collapse_add_lt` + `ewIter_comp_le`; the c=0 atomic case needs an atom-cut lemma).
-/
theorem passAux (c : ℕ) {e : ONote} (heNF : e.NF) :
    ∀ {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)} {r : ℕ},
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
            have h : (Semiformula.all ψ : ArithmeticFormula ℕ).complexity = ψ.complexity + 1 := rfl
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
            have h : (Semiformula.exs ψ : ArithmeticFormula ℕ).complexity = ψ.complexity + 1 := rfl
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

variable {α e : ONote} {H : ONote → Prop}

/-- **One cut-ELIMINATION pass over `Zef2`** (E–W Lemma 26/27): a single predicative rank step —
the ordinal COLLAPSES (`collapse α`) and the numeric slot ITERATES (`ewIter f α`). -/
theorem cutElimPass_Zef2 {c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2 α e H f (c + 1) Γ) (hf1 : EwF1 f) (_hf2 : EwF2 f) :
    Zef2Prov (collapse α) e H (ewIter f α) c Γ :=
  passAux c heNF D rfl hf1.monotone hf1.infl hf1.2 hαNF hαH

/-- **The composed exit over `Zef2`** — the anti-vacuity test: ONE elimination pass
(`cutElimPass_Zef2`, rank `1 → 0`) composed with `headline_readoff_Zef2`, at the concrete
`ewRootSlot`.  The `ewIter (ewRootSlot e m) α 0` iterate is VISIBLE in the bound and is what the
read-off reads. -/
theorem cutElimPass_exit_root_Zef2 {m : ℕ}
    {φ : ArithmeticSemiformula ℕ 1}
    (hφinst : ∀ n, ∃ ar, ∃ r : (ℒₒᵣ).Rel ar, ∃ v, φ/[nm n] = Semiformula.rel r v)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2 α e H (ewRootSlot e m) (0 + 1) {(∃⁰ φ)}) :
    ∃ n ≤ ewIter (ewRootSlot e m) α 0, atomTrue (φ/[nm n]) := by
  obtain ⟨α', _, _, _, _, D'⟩ :=
    cutElimPass_Zef2 (ewRootSlot e m) heNF hαNF hαH D
      (ewRootSlot_f1 e m) (ewRootSlot_f2 e m)
  exact headline_readoff_Zef2 hφinst D'

/-! ## The wainer ladder (L-items) — the four rungs as named pins

The rungs decompose the `wainer_bound_of_pa_proves_goodstein` monolith (now in `Statement.lean`)
into the E–W pipeline order. -/

/-- **`rankToZeroAux`** — the EwLow-threaded rung-R induction.  Threads
`Monotone ∧ inflationary ∧ (2m+1 ≤ ·)` (NOT `EwF1`: `ewIter` does not inherit strict monotonicity,
but it DOES inherit these three via `ewIter_monotone`/`_infl`/`_low`, so the pass ITERATES).  Each
step applies one `passAux`, promotes the reduced witness UP to `collapse α` exactly (`Zef2.weak`,
gate `ewN_collapse_le`), recurses, and rewrites via the two tower-shift lemmas. -/
theorem rankToZeroAux (e : ONote) (heNF : e.NF) :
    ∀ (d : ℕ) {α : ONote} {H : ONote → Prop} {f : ℕ → ℕ} {Γ : Finset (ArithmeticFormula ℕ)},
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

/-- **`rankToZero_Zef2`** (rung L-R) — iterate `cutElimPass_Zef2` down the cut rank `d → 0`.
A plain induction over the pass (`rankToZeroAux`): `d` applications collapse the ordinal to
`collapseIter d α` and tower the slot to `ewIterTower f d α`, landing at rank 0. -/
theorem rankToZero_Zef2 {d : ℕ} {Γ : Finset (ArithmeticFormula ℕ)} (f : ℕ → ℕ)
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2 α e H f d Γ) (hf1 : EwF1 f) (_hf2 : EwF2 f) :
    Zef2Prov (collapseIter d α) e H (ewIterTower f d α) 0 Γ :=
  rankToZeroAux e heNF d D hf1.monotone hf1.infl hf1.2 hαNF hαH

end GoodsteinPA.OperatorZeh
