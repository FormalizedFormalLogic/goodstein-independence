/-
# `Zᵉᵏᵈ` — the control-ordinal operator witness-bounded `Z_∞` calculus

The `Z_∞` calculus — derivations `⊢^{α,k}` bounded jointly by an ordinal `α` and a numeric gate
`k`, together with the PA embedding and the numerically-controlled cut-elimination that raises
`k` through the Hardy hierarchy at every cut — is Towsner's design. This file specializes that
numeric gate to an **operator-controlled** form, replacing it with a control ordinal in the
sense of Buchholz's operator-controlled derivations (see the citations at the end of this
docstring).

A calculus whose `exI` witness bound is tied directly to the derivation ordinal `α` cannot absorb
the witness growth under cut-elimination: the principal `exI` cut's witness `hardy γ(·)` grows
super-linearly through commuting `ω`-rules, while cut-elimination only grows `α ↦ α + γ`. The
`d`-bump `d ↦ d + norm α` alone closes the **norm-budget** obstruction of §19.6 but not this
**witness-index** one.

**The fix: a control ordinal `e`.** Decouple the `exI` witness bound from the derivation ordinal
`α` onto a separate **control ordinal** `e`: the witness bound becomes `n ≤ hardy e (k + d)`
(instead of `hardy α (k + d)`). Cut-elimination then *raises `e`* to dominate the cut-formula
bounds while `α` grows freely; the witness stays controlled by `hardy e`, a `hardy`-closed
quantity (operator-controlled derivations, specialized to PA, numeric-`e` form).

This file: the inductive `Zekd` calculus, its structural layer (`mono_k`, `mono_d`, `mono_c`,
`mono_e`, `weakening`), and the ordinal/`norm` bookkeeping used throughout the cut-elimination
suite. The inversion suite lives in `GoodsteinPA.OperatorZinfty.Inversion`, and the §19.5/§19.6
cut reductions in `GoodsteinPA.OperatorZinfty.Cut`.

- [Tow20, §13, §15, §18, §19]
- [Buc03]
-/
module

public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import GoodsteinPA.ToMathlib.Hardy
public import GoodsteinPA.Compat

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

abbrev Form := ArithmeticFormula ℕ
noncomputable def nm (n : ℕ) : Semiterm ℒₒᵣ ℕ 0 := (Semiterm.Operator.numeral ℒₒᵣ n).const
abbrev Seq := Finset Form
noncomputable def atomTrue (φ : Form) : Prop := GoodsteinPA.Compat.gEvalm ℕ (fun _ => 0) (fun _ => 0) φ

/-- **The control-ordinal operator witness-bounded `Z_∞` calculus** `Zᵉᵏᵈ ⊢^{α,e}_{k,d,c} Γ`.
Derivation ordinal `α`; **control ordinal `e`** (governs the witness bound, raised by cut-elim);
effective norm budget `k + d`; ω-premise `n` at `(max k n, d)`; **witness bound `hardy e (k+d)`**
(decoupled from `α`, and threaded inertly through every rule). -/
inductive Zekd : ONote → ONote → ℕ → ℕ → ℕ → Seq → Prop
  | axL {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Γ)
      (hn : Semiformula.nrel r v ∈ Γ) : Zekd α e k d c Γ
  | verumR {α e k d c Γ} (h : (⊤ : Form) ∈ Γ) : Zekd α e k d c Γ
  | trueRel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.rel r v))
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.rel r v ∈ Γ) : Zekd α e k d c Γ
  | trueNrel {α e k d c Γ} {ar} (r : (ℒₒᵣ).Rel ar) (v) (htrue : atomTrue (Semiformula.nrel r v))
      (hτ : norm α < k + d) (hαNF : α.NF) (hmem : Semiformula.nrel r v ∈ Γ) : Zekd α e k d c Γ
  | wk {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zekd α e k d c Δ) : Zekd α e k d c Γ
  | weak {α β e k d c Δ Γ} (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (hsub : Δ ⊆ Γ) (dd : Zekd β e k d c Δ) : Zekd α e k d c Γ
  | andI {α βφ βψ e k d c Γ} (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (dφ : Zekd βφ e k d c (insert φ Γ)) (dψ : Zekd βψ e k d c (insert ψ Γ)) :
      Zekd α e k d c (insert (φ ⋏ ψ) Γ)
  | orI {α β e k d c Γ} (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d)
      (dd : Zekd β e k d c (insert φ (insert ψ Γ))) : Zekd α e k d c (insert (φ ⋎ ψ) Γ)
  | allω {α e k d c Γ} (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
      (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF) (hτ : ∀ n, norm (β n) < max k n + d)
      (dd : ∀ n, Zekd (β n) e (max k n) d c (insert (φ/[nm n]) Γ)) :
      Zekd α e k d c (insert (∀⁰ φ) Γ)
  | exI {α β e k d c Γ} (φ : ArithmeticSemiformula ℕ 1) (n : ℕ) (hβ : β < α)
      (hβNF : β.NF) (hαNF : α.NF) (hτ : norm β < k + d) (hbound : n ≤ hardy e (k + d))
      (dd : Zekd β e k d c (insert (φ/[nm n]) Γ)) : Zekd α e k d c (insert (∃⁰ φ) Γ)
  | cut {α βφ βψ e k d c Γ} (φ : Form) (hcompl : φ.complexity < c) (hβφ : βφ < α) (hβψ : βψ < α)
      (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF) (hτφ : norm βφ < k + d) (hτψ : norm βψ < k + d)
      (d₁ : Zekd βφ e k d c (insert φ Γ)) (d₂ : Zekd βψ e k d c (insert (∼φ) Γ)) :
      Zekd α e k d c Γ

namespace Zekd

/-- **`k`-monotonicity** (the `max`/cofinal part; inversions raise this idempotently). The witness
bound `hardy e (k+d)` rises with `k` via `hardy_monotone`. -/
theorem mono_k : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {k'}, k ≤ k' → Zekd α e k' d c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro k' _; exact Zekd.axL r v hp hn
  | verumR h => intro k' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem =>
      intro k' hk; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      intro k' hk; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | wk hsub _ ih => intro k' hk; exact Zekd.wk hsub (ih hk)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro k' hk; exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hk)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro k' hk
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hk) (ihψ hk)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro k' hk; exact Zekd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hk)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro k' hk
      exact Zekd.allω φ β hβ hβNF hαNF
        (fun n => lt_of_lt_of_le (hτ n) (by have := Nat.add_le_add_right (max_le_max hk (le_refl n)) d; omega))
        (fun n => ih n (max_le_max hk (le_refl n)))
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro k' hk
      exact Zekd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hk)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro k' hk
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hk) (ih₂ hk)

/-- **`d`-monotonicity** (the additive cut-shift budget; the §19.6-commuting case raises this by
`norm α`). The witness bound `hardy e (k+d)` rises with `d` via `hardy_monotone`. -/
theorem mono_d : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {d'}, d ≤ d' → Zekd α e k d' c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro d' _; exact Zekd.axL r v hp hn
  | verumR h => intro d' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem =>
      intro d' hd; exact Zekd.trueRel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem =>
      intro d' hd; exact Zekd.trueNrel r v htrue (lt_of_lt_of_le hτ (by omega)) hαNF hmem
  | wk hsub _ ih => intro d' hd; exact Zekd.wk hsub (ih hd)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro d' hd; exact Zekd.weak hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) hsub (ih hd)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro d' hd
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ihφ hd) (ihψ hd)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro d' hd; exact Zekd.orI φ ψ hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega)) (ih hd)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro d' hd
      exact Zekd.allω φ β hβ hβNF hαNF (fun n => lt_of_lt_of_le (hτ n) (by omega))
        (fun n => ih n hd)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro d' hd
      exact Zekd.exI φ n hβ hβNF hαNF (lt_of_lt_of_le hτ (by omega))
        (le_trans hbound (hardy_monotone _ (by omega))) (ih hd)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro d' hd
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF (lt_of_lt_of_le hτφ (by omega))
        (lt_of_lt_of_le hτψ (by omega)) (ih₁ hd) (ih₂ hd)

/-- **`c`-monotonicity** (cut-rank). -/
theorem mono_c : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {c'}, c ≤ c' → Zekd α e k d c' Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro c' _; exact Zekd.axL r v hp hn
  | verumR h => intro c' _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem => intro c' _; exact Zekd.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => intro c' _; exact Zekd.trueNrel r v htrue hτ hαNF hmem
  | wk hsub _ ih => intro c' hc; exact Zekd.wk hsub (ih hc)
  | weak hβ hβNF hαNF hτ hsub _ ih => intro c' hc; exact Zekd.weak hβ hβNF hαNF hτ hsub (ih hc)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro c' hc; exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ hc) (ihψ hc)
  | orI φ ψ hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zekd.orI φ ψ hβ hβNF hαNF hτ (ih hc)
  | allω φ β hβ hβNF hαNF hτ _ ih => intro c' hc; exact Zekd.allω φ β hβ hβNF hαNF hτ (fun n => ih n hc)
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro c' hc; exact Zekd.exI φ n hβ hβNF hαNF hτ hbound (ih hc)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro c' hc
      exact Zekd.cut φ (lt_of_lt_of_le hcompl hc) hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ hc) (ih₂ hc)

/-- **`e`-monotonicity** (the NEW control axis; cut-elimination raises `e` to dominate cut-formula
bounds). Only the `exI` witness bound `hardy e (k+d)` depends on `e`, and it rises with `e` via
the index-monotonicity `hardy_le_of_lt` (with the budget side condition `norm e ≤ k+d`). -/
theorem mono_e : ∀ {α e k d c Γ}, Zekd α e k d c Γ → ∀ {e'}, e.NF → e'.NF → e < e' →
    norm e ≤ k + d → Zekd α e' k d c Γ := by
  intro α e k d c Γ dd
  induction dd with
  | axL r v hp hn => intro e' _ _ _ _; exact Zekd.axL r v hp hn
  | verumR h => intro e' _ _ _ _; exact Zekd.verumR h
  | trueRel r v htrue hτ hαNF hmem => intro e' _ _ _ _; exact Zekd.trueRel r v htrue hτ hαNF hmem
  | trueNrel r v htrue hτ hαNF hmem => intro e' _ _ _ _; exact Zekd.trueNrel r v htrue hτ hαNF hmem
  | wk hsub _ ih => intro e' he heN' hlt hnorm; exact Zekd.wk hsub (ih he heN' hlt hnorm)
  | weak hβ hβNF hαNF hτ hsub _ ih =>
      intro e' he heN' hlt hnorm; exact Zekd.weak hβ hβNF hαNF hτ hsub (ih he heN' hlt hnorm)
  | andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ihφ ihψ =>
      intro e' he heN' hlt hnorm
      exact Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ihφ he heN' hlt hnorm) (ihψ he heN' hlt hnorm)
  | orI φ ψ hβ hβNF hαNF hτ _ ih =>
      intro e' he heN' hlt hnorm; exact Zekd.orI φ ψ hβ hβNF hαNF hτ (ih he heN' hlt hnorm)
  | allω φ β hβ hβNF hαNF hτ _ ih =>
      intro e' he heN' hlt hnorm
      refine Zekd.allω φ β hβ hβNF hαNF hτ (fun n => ih n he heN' hlt ?_)
      -- premise n runs at index (max k n, d): budget `norm e ≤ max k n + d` from `norm e ≤ k + d`
      have : k ≤ max k n := le_max_left _ _
      omega
  | exI φ n hβ hβNF hαNF hτ hbound _ ih =>
      intro e' he heN' hlt hnorm
      refine Zekd.exI φ n hβ hβNF hαNF hτ ?_ (ih he heN' hlt hnorm)
      exact le_trans hbound (hardy_le_of_lt he heN' hlt hnorm)
  | cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ _ _ ih₁ ih₂ =>
      intro e' he heN' hlt hnorm
      exact Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF hτφ hτψ (ih₁ he heN' hlt hnorm) (ih₂ he heN' hlt hnorm)

theorem lt_osucc {o : ONote} (h : o.NF) : o < osucc o :=
  lt_def.mpr (by rw [repr_osucc h]; exact lt_add_one _)

/-- **`osucc` strict monotonicity** (the §19.6 descent: `βᵢ < γ ⟹ osucc(α+βᵢ) < osucc(α+γ)`). -/
theorem osucc_lt_osucc {x y : ONote} (hx : x.NF) (hy : y.NF) (h : x < y) : osucc x < osucc y := by
  refine lt_def.mpr ?_
  rw [repr_osucc hx, repr_osucc hy, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_lt_succ (lt_def.mp h)

/-- `x < y ⟹ x < osucc y` (NF). -/
theorem lt_osucc_of_lt {x y : ONote} (hy : y.NF) (h : x < y) : x < osucc y :=
  lt_trans h (lt_osucc hy)

/-! #### Ordinal/`norm` bookkeeping for §19.6/§19.7. -/

theorem add_lt_add_left_NF {α γ' γ : ONote} (hαNF : α.NF) (hγ'NF : γ'.NF) (hγNF : γ.NF)
    (h : γ' < γ) : α + γ' < α + γ := by
  haveI := hαNF; haveI := hγ'NF; haveI := hγNF
  exact lt_def.mpr (by rw [repr_add, repr_add]; exact (add_lt_add_iff_left _).mpr (lt_def.mp h))

theorem le_add_left_NF {α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) : γ ≤ α + γ := by
  haveI := hαNF; haveI := hγNF
  exact le_def.mpr (by rw [repr_add]; exact le_add_self)

theorem le_add_right_NF {α γ : ONote} (hαNF : α.NF) (hγNF : γ.NF) : α ≤ α + γ := by
  haveI := hαNF; haveI := hγNF
  exact le_def.mpr (by rw [repr_add]; exact le_self_add)

/-- **The §19.6 descent step**, assembled: `γ' < γ ⟹ osucc (α + γ') < osucc (α + γ)`. -/
theorem add_osucc_descent {α γ' γ : ONote} (hαNF : α.NF) (hγ'NF : γ'.NF) (hγNF : γ.NF)
    (h : γ' < γ) : osucc (α + γ') < osucc (α + γ) :=
  osucc_lt_osucc (ONote.add_nf α γ') (ONote.add_nf α γ) (add_lt_add_left_NF hαNF hγ'NF hγNF h)

@[simp] theorem norm_omegaPow {α : ONote} : norm (oadd α 1 0) = max (norm α) 1 := by
  simp [norm_oadd]

theorem norm_addAux_le (e : ONote) (n : ℕ+) (r : ONote) :
    norm (addAux e n r) ≤ max (norm e) (n : ℕ) + norm r := by
  unfold addAux
  match r with
  | 0 => simp only [norm_oadd, norm_zero]; omega
  | oadd e' n' a' =>
    simp only []
    rcases ONote.cmp e e' with _ | _ | _ <;>
      simp only [norm_oadd, PNat.add_coe] <;> omega

theorem norm_add_le : ∀ {α : ONote}, α.NF → ∀ {γ : ONote}, γ.NF →
    norm (α + γ) ≤ norm α + norm γ := by
  intro α
  induction α with
  | zero => intro _ γ _; simp
  | oadd e n a ihe iha =>
    intro hα γ hγ
    have ha : a.NF := hα.snd
    haveI := ha; haveI := hγ
    have iha' : norm (a + γ) ≤ norm a + norm γ := iha ha hγ
    rw [oadd_add]
    rcases hr : a + γ with _ | ⟨e', n', a'⟩
    · simp only [addAux, norm_oadd, norm_zero]; omega
    · rw [hr] at iha'
      simp only [norm_oadd] at iha'
      simp only [addAux]
      rcases hcmp : ONote.cmp e e' with _ | _ | _
      · simp only [norm_oadd]; omega
      · have hee : e = e' := eq_of_cmp_eq hcmp
        have hge : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr (a + γ) := by
          rw [hr, hee]; exact omega0_le_oadd e' n' a'
        have hra : ONote.repr a < Ordinal.omega0 ^ ONote.repr e := hα.snd'.repr_lt
        have hgγ : Ordinal.omega0 ^ ONote.repr e ≤ ONote.repr γ := by
          by_contra hlt
          push Not at hlt
          have : ONote.repr a + ONote.repr γ < Ordinal.omega0 ^ ONote.repr e :=
            (Ordinal.isPrincipal_add_omega0_opow (ONote.repr e)) hra hlt
          rw [repr_add] at hge
          exact absurd (lt_of_le_of_lt hge this) (lt_irrefl _)
        have habs : a + γ = γ := by
          have : ONote.repr (a + γ) = ONote.repr γ := by
            rw [repr_add]; exact Ordinal.add_of_omega0_opow_le hra hgγ
          exact repr_inj.mp this
        have hnγ : norm γ = max (norm e') (max (n':ℕ) (norm a')) := by
          rw [← habs, hr]; simp [norm_oadd]
        simp only [norm_oadd, PNat.add_coe]; omega
      · simp only [norm_oadd]; omega


/-- Sequent weakening (height-preserving). -/
theorem weakening {α e k d c Δ Γ} (hsub : Δ ⊆ Γ) (dd : Zekd α e k d c Δ) : Zekd α e k d c Γ :=
  Zekd.wk hsub dd

end Zekd

end GoodsteinPA.OperatorZinfty
