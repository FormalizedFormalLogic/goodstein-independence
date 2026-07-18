/-
# GoodsteinPA.HardyMajorization — Part2
-/
module

public import GoodsteinPA.OperatorZef2
public import GoodsteinPA.HardyMajorization.Part1
public meta import GoodsteinPA.HardyMajorization.Part1  -- shake: keep

@[expose] public section

namespace GoodsteinPA.HardyMajorization

open ONote Ordinal GoodsteinPA.OperatorZeh

/-- **`hardy e` at a `max`-shifted argument is padded-dominated by `H_{ω^{e+1}}`.**  Uniform in `z`
(no `norm e ≤ z` gate leaks): the pad `m + norm e` both shifts past the `max m` and pays the
`hardy_le_of_lt` norm gate at `z = 0`. -/
theorem hardy_maxpad (e : ONote) (he : e.NF) (m : ℕ) :
    ∀ z, hardy e (max m z) ≤ hardy (Wpow (e + 1)) (z + (m + norm e)) := by
  intro z
  have he1 : (e + 1).NF := ONote.add_nf e 1
  have hlt : e < Wpow (e + 1) := e_lt_Wpow_succ e he
  have hmono : hardy e (max m z) ≤ hardy e (z + (m + norm e)) :=
    hardy_monotone e (by omega)
  have hgate : hardy e (z + (m + norm e)) ≤ hardy (Wpow (e + 1)) (z + (m + norm e)) :=
    hardy_le_of_lt he (Wpow_NF he1) hlt (by omega)
  exact le_trans hmono hgate

/-- **The base root slot is padded-Hardy-dominated.**  `ewRootSlot e m x = 2(x + hardy e (max m x))
+ 3` fits under `H_{ω^{(e+1)+2}}` at a padded argument: take `f z := hardy e (max m z)` (padded-dom
by `hardy_maxpad`), feed `hEng_of_dom_pad`, and note `2x + 2 f x + 3 ≤` the engine LHS since
`x ≤ f x ≤ 2^{f x + 1}`. -/
theorem ewRootSlot_dom_pad (e : ONote) (he : e.NF) (m : ℕ) :
    ∀ x, ewRootSlot e m x
        ≤ hardy (Wpow ((e + 1) + 2))
            (x + (norm ((e + 1) + 1) + norm (e + 1) + normSum ((e + 1) + 2 + 1)
                    + norm ((e + 1) + 2) + 8 + (m + norm e))) := by
  intro x
  have he₀ : (e + 1).NF := ONote.add_nf e 1
  have he₀0 : e + 1 ≠ 0 := by
    intro h
    have hh := congrArg ONote.repr h
    rw [ONote.repr_add, ONote.repr_one, repr_zero] at hh
    push_cast at hh
    exact (lt_of_lt_of_le zero_lt_one le_add_self).ne' hh
  have hfdom : ∀ z, hardy e (max m z) ≤ hardy (Wpow (e + 1)) (z + (m + norm e)) :=
    hardy_maxpad e he m
  have hEng := hEng_of_dom_pad (f := fun z => hardy e (max m z)) (c := m + norm e)
    he₀ he₀0 hfdom le_rfl
  have hEngx := hEng x
  have hfge : x ≤ hardy e (max m x) := le_trans (le_max_right m x) (le_hardy e (max m x))
  have hpowge : hardy e (max m x) + 1 ≤ 2 ^ (hardy e (max m x) + 1) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  have hunfold : ewRootSlot e m x = 2 * (x + hardy e (max m x)) + 3 := by
    simp only [ewRootSlot, rel1]
  rw [hunfold]
  refine le_trans ?_ hEngx
  omega

/-- `rel1` shift preserves padded domination — the `max K` folds into the pad. -/
theorem rel1_dom_pad {g : ℕ → ℕ} {E : ONote} {c : ℕ}
    (hg : ∀ x, g x ≤ hardy (Wpow E) (x + c)) (K : ℕ) :
    ∀ z, rel1 g K z ≤ hardy (Wpow E) (z + (K + c)) := by
  intro z
  show g (max K z) ≤ hardy (Wpow E) (z + (K + c))
  exact le_trans (hg (max K z)) (hardy_monotone _ (by omega))

/-- General `ω^A + ω^B < ω^{A+1}` for `B < A` (the tower-collapse raise; generalizes the
`hEng_of_dom` `hDlt` step to arbitrary ordered exponents). -/
theorem Wpow_add_lt_Wpow_succ {A B : ONote} (hA : A.NF) (hB : B.NF) (hBA : B < A) :
    Wpow A + Wpow B < Wpow (A + 1) := by
  haveI : (Wpow A).NF := Wpow_NF hA
  haveI : (Wpow B).NF := Wpow_NF hB
  rw [lt_def, ONote.repr_add]
  show (Wpow A).repr + (Wpow B).repr < ω ^ (A + 1).repr * (1 : ℕ) + 0
  have hrA : (Wpow A).repr = ω ^ A.repr := by
    show ω ^ A.repr * (1 : ℕ) + 0 = ω ^ A.repr; simp
  have hrB : (Wpow B).repr = ω ^ B.repr := by
    show ω ^ B.repr * (1 : ℕ) + 0 = ω ^ B.repr; simp
  have hrA1 : (A + 1).repr = A.repr + 1 := by rw [ONote.repr_add, ONote.repr_one]; norm_num
  rw [hrA, hrB, hrA1]
  have hBltA : B.repr < A.repr := by rw [lt_def] at hBA; exact hBA
  have hstep : ω ^ B.repr < ω ^ A.repr :=
    (Ordinal.opow_lt_opow_iff_right (by norm_num : (1 : Ordinal) < ω)).mpr hBltA
  calc ω ^ A.repr + ω ^ B.repr
      < ω ^ A.repr + ω ^ A.repr := (add_lt_add_iff_left _).2 hstep
    _ = ω ^ A.repr * 2 := by rw [show (2 : Ordinal) = 1 + 1 by norm_num, mul_add, mul_one]
    _ < ω ^ A.repr * ω := mul_lt_mul_of_pos_left (by simpa using Ordinal.natCast_lt_omega0 2)
        (Ordinal.opow_pos _ omega0_pos)
    _ = ω ^ (A.repr + 1) := by
        have h := (Ordinal.opow_add ω A.repr 1).symm
        rw [Ordinal.opow_one] at h; exact h
    _ ≤ ω ^ (A.repr + 1) * (1 : ℕ) + 0 := by simp

/-- **Double-Hardy collapse** for ordered `ω`-power levels — `H_{ω^A}(H_{ω^B}(y)) = H_{ω^A+ω^B}(y)`
when `B < A` (generalizes `hEng_of_dom`'s `hC` step). -/
theorem hardy_double_collapse {A B : ONote} (hA : A.NF) (hB : B.NF) (hBA : B < A) (y : ℕ) :
    hardy (Wpow A) (hardy (Wpow B) y) = hardy (Wpow A + Wpow B) y := by
  refine (hardy_add_comp _ (Wpow_NF hA) _ (Wpow_NF hB) (Or.inr ?_) y).symm
  show (Wpow B).repr < ω ^ (lastExp (Wpow A)).repr
  have hlast : lastExp (Wpow A) = A := rfl
  rw [hlast]
  have hrB : (Wpow B).repr = ω ^ B.repr := by
    show ω ^ B.repr * (1 : ℕ) + 0 = ω ^ B.repr; simp
  rw [hrB]
  have hBltA : B.repr < A.repr := by rw [lt_def] at hBA; exact hBA
  exact (Ordinal.opow_lt_opow_iff_right (by norm_num : (1 : Ordinal) < ω)).mpr hBltA

/-- **The tower is padded-Hardy-dominated** (existential level/pad).  Each `ewIter` pass raises
the level to a double Hardy `H_{ω^A}(H_{ω^B}(·))` with `B < A`; `hardy_double_collapse` folds it
to `H_{ω^A+ω^B}` and one `Wpow_add_lt_Wpow_succ` raise brings it back to a SINGLE `ω`-power level
`ω^{A+1}` at a bigger pad — so induction on `d` keeps the single-hardy-at-padded-arg shape.  The
gate `norm (ω^A + ω^B) ≤ x + c'` is paid by putting that norm INTO `c'` (it is not in `p_d`). -/
theorem ewIterTower_dom_pad {g : ℕ → ℕ} {E : ONote} {c : ℕ} (hE : E.NF) (hE0 : E ≠ 0)
    (hg : ∀ x, g x ≤ hardy (Wpow E) (x + c)) (α : ONote) (hα : α.NF) :
    ∀ d, ∃ (E' : ONote) (c' : ℕ), E'.NF ∧ E' ≠ 0 ∧
      ∀ x, ewIterTower g d α x ≤ hardy (Wpow E') (x + c') := by
  intro d
  induction d with
  | zero => exact ⟨E, c, hE, hE0, hg⟩
  | succ d ih =>
    obtain ⟨Ed, cd, hEd, hEd0, hdom⟩ := ih
    have hγ : (collapseIter d α).NF := collapseIter_NF hα d
    haveI := hEd
    haveI : (2 : ONote).NF := nf_ofNat 2
    haveI hB : (Ed + 2).NF := ONote.add_nf Ed 2
    haveI hB1 : (Ed + 2 + 1).NF := ONote.add_nf (Ed + 2) 1
    haveI := hγ
    haveI hA : (Ed + 2 + 1 + collapseIter d α).NF :=
      ONote.add_nf (Ed + 2 + 1) (collapseIter d α)
    have hBA : Ed + 2 < Ed + 2 + 1 + collapseIter d α := by
      have h1 : (Ed + 2 + 1 + collapseIter d α).repr
          = (Ed + 2).repr + 1 + (collapseIter d α).repr := by
        rw [ONote.repr_add (Ed + 2 + 1) (collapseIter d α),
          ONote.repr_add (Ed + 2) 1, ONote.repr_one]
        push_cast
        rfl
      rw [lt_def, h1]
      calc (Ed + 2).repr < (Ed + 2).repr + 1 := lt_add_one _
        _ ≤ (Ed + 2).repr + 1 + (collapseIter d α).repr := le_self_add
    haveI hWA : (Wpow (Ed + 2 + 1 + collapseIter d α)).NF := Wpow_NF hA
    haveI hWB : (Wpow (Ed + 2)).NF := Wpow_NF hB
    haveI hA1 : (Ed + 2 + 1 + collapseIter d α + 1).NF :=
      ONote.add_nf (Ed + 2 + 1 + collapseIter d α) 1
    have hA10 : Ed + 2 + 1 + collapseIter d α + 1 ≠ 0 := by
      intro h
      have hh := congrArg ONote.repr h
      rw [ONote.repr_add, ONote.repr_one, repr_zero] at hh
      push_cast at hh
      exact (lt_of_lt_of_le zero_lt_one le_add_self).ne' hh
    refine ⟨Ed + 2 + 1 + collapseIter d α + 1,
      Nlog (collapseIter d α)
        + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
        + norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2)),
      hA1, hA10, ?_⟩
    intro x
    have hpass := ewIter_hardy_le_of_dom_pad hEd hEd0 hdom (collapseIter d α) hγ x
    have hstep : ewIterTower g (d + 1) α x
        = ewIter (ewIterTower g d α) (collapseIter d α) x := rfl
    rw [hstep]
    refine le_trans hpass ?_
    rw [hardy_double_collapse hA hB hBA]
    have harg : Nlog (collapseIter d α) + x
          + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
        ≤ x + (Nlog (collapseIter d α)
          + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
          + norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2))) := by omega
    refine le_trans (hardy_monotone _ harg) ?_
    haveI hsum : (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2)).NF :=
      ONote.add_nf _ _
    have hgate : norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2))
        ≤ x + (Nlog (collapseIter d α)
          + (norm (Ed + 1) + norm Ed + normSum (Ed + 2 + 1) + norm (Ed + 2) + 8 + cd)
          + norm (Wpow (Ed + 2 + 1 + collapseIter d α) + Wpow (Ed + 2))) := by omega
    exact hardy_le_of_lt hsum (Wpow_NF hA1) (Wpow_add_lt_Wpow_succ hA hB hBA) hgate

/-- **Iterates of a fixed `ω`-power Hardy level are padded-Hardy-dominated** (existential
level/pad, carrying `E₀ < E` so the collapse stays ordered).  Mirror of `ewIterTower_dom_pad`:
`G^[k+1] z = G^[k] (G z)`, the IH + `hardy_arg_add` absorb the pad, `hardy_double_collapse` +
`Wpow_add_lt_Wpow_succ` fold the double Hardy back to a single level.  Instantiated at
`G = Gexp = hardy (Wpow 2)` for the `P*` (`gvb`) half of the `S*`-domination (SERIES-4 S-2). -/
theorem hardy_Wpow_iter_dom_pad (E₀ : ONote) (hE₀ : E₀.NF) :
    ∀ k, ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧ E₀ < E ∧
      ∀ z, (hardy (Wpow E₀))^[k] z ≤ hardy (Wpow E) (z + c) := by
  haveI := hE₀
  have hsucc_lt : ∀ (β : ONote), β.NF → β < β + 1 := by
    intro β hβ
    haveI := hβ
    rw [lt_def, ONote.repr_add, ONote.repr_one]
    push_cast
    exact lt_add_one _
  have hsucc_nf : ∀ (β : ONote), β.NF → (β + 1).NF := by
    intro β hβ; haveI := hβ; exact ONote.add_nf β 1
  have hsucc_ne : ∀ (β : ONote), β.NF → β + 1 ≠ 0 := by
    intro β hβ h
    haveI := hβ
    have hh := congrArg ONote.repr h
    rw [ONote.repr_add, ONote.repr_one, repr_zero] at hh
    push_cast at hh
    exact (lt_of_lt_of_le zero_lt_one le_add_self).ne' hh
  intro k
  induction k with
  | zero =>
      refine ⟨E₀ + 1, 0, hsucc_nf E₀ hE₀, hsucc_ne E₀ hE₀, hsucc_lt E₀ hE₀, fun z => ?_⟩
      simpa using le_hardy (Wpow (E₀ + 1)) z
  | succ k ih =>
      obtain ⟨Ek, ck, hEk, hEk0, hE₀Ek, hdom⟩ := ih
      haveI := hEk
      haveI hWEk : (Wpow Ek).NF := Wpow_NF hEk
      haveI hWE₀ : (Wpow E₀).NF := Wpow_NF hE₀
      haveI hsum : (Wpow Ek + Wpow E₀).NF := ONote.add_nf _ _
      refine ⟨Ek + 1, ck + norm (Wpow Ek + Wpow E₀), hsucc_nf Ek hEk, hsucc_ne Ek hEk,
        lt_trans hE₀Ek (hsucc_lt Ek hEk), fun z => ?_⟩
      have h1 : (hardy (Wpow E₀))^[k + 1] z = (hardy (Wpow E₀))^[k] (hardy (Wpow E₀) z) :=
        Function.iterate_succ_apply _ _ _
      rw [h1]
      have h2 : (hardy (Wpow E₀))^[k] (hardy (Wpow E₀) z)
          ≤ hardy (Wpow Ek) (hardy (Wpow E₀) z + ck) := hdom _
      have h3 : hardy (Wpow E₀) z + ck ≤ hardy (Wpow E₀) (z + ck) := hardy_arg_add _ _ _
      have h4 : hardy (Wpow Ek) (hardy (Wpow E₀) (z + ck))
          = hardy (Wpow Ek + Wpow E₀) (z + ck) := hardy_double_collapse hEk hE₀ hE₀Ek _
      have harg : z + ck ≤ z + (ck + norm (Wpow Ek + Wpow E₀)) := by omega
      have hgate : norm (Wpow Ek + Wpow E₀) ≤ z + (ck + norm (Wpow Ek + Wpow E₀)) := by omega
      calc (hardy (Wpow E₀))^[k] (hardy (Wpow E₀) z)
          ≤ hardy (Wpow Ek) (hardy (Wpow E₀) z + ck) := h2
        _ ≤ hardy (Wpow Ek) (hardy (Wpow E₀) (z + ck)) := hardy_monotone _ h3
        _ = hardy (Wpow Ek + Wpow E₀) (z + ck) := h4
        _ ≤ hardy (Wpow Ek + Wpow E₀) (z + (ck + norm (Wpow Ek + Wpow E₀))) :=
            hardy_monotone _ harg
        _ ≤ hardy (Wpow (Ek + 1)) (z + (ck + norm (Wpow Ek + Wpow E₀))) :=
            hardy_le_of_lt hsum (Wpow_NF (hsucc_nf Ek hEk))
              (Wpow_add_lt_Wpow_succ hEk hE₀ hE₀Ek) hgate

/-- **Padded-domination max-combiner** — two padded Hardy bounds at (possibly different) levels
combine at the joint level `E₁+E₂+1`, both gates paid from the joint pad.  This is `Sslot`'s
`max (tower z) (P* z)` step. -/
theorem dom_pad_max {f g : ℕ → ℕ} {E₁ E₂ : ONote} {c₁ c₂ : ℕ}
    (hE₁ : E₁.NF) (hE₂ : E₂.NF)
    (hf : ∀ z, f z ≤ hardy (Wpow E₁) (z + c₁))
    (hg : ∀ z, g z ≤ hardy (Wpow E₂) (z + c₂)) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧ E₁ < E ∧ E₂ < E ∧
      ∀ z, max (f z) (g z) ≤ hardy (Wpow E) (z + c) := by
  haveI := hE₁
  haveI := hE₂
  haveI h12 : (E₁ + E₂).NF := ONote.add_nf E₁ E₂
  haveI hE : (E₁ + E₂ + 1).NF := ONote.add_nf (E₁ + E₂) 1
  have hrepr : (E₁ + E₂ + 1).repr = E₁.repr + E₂.repr + 1 := by
    rw [ONote.repr_add (E₁ + E₂) 1, ONote.repr_add E₁ E₂, ONote.repr_one]
    push_cast
    rfl
  have hlt₁ : E₁ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₁.repr ≤ E₁.repr + E₂.repr := le_self_add
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hlt₂ : E₂ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₂.repr ≤ E₁.repr + E₂.repr := le_add_self
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hne : E₁ + E₂ + 1 ≠ 0 := by
    intro h
    have hh := congrArg ONote.repr h
    rw [hrepr, repr_zero] at hh
    exact (lt_of_lt_of_le zero_lt_one le_add_self).ne'
      (by exact_mod_cast hh)
  refine ⟨E₁ + E₂ + 1, max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂), hE, hne, hlt₁, hlt₂,
    fun z => ?_⟩
  have harg₁ : z + c₁ ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have harg₂ : z + c₂ ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have hgate₁ : norm (Wpow E₁)
      ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have hgate₂ : norm (Wpow E₂)
      ≤ z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂)) := by omega
  have hb₁ : f z ≤ hardy (Wpow (E₁ + E₂ + 1))
      (z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂))) :=
    le_trans (hf z) (le_trans (hardy_monotone _ harg₁)
      (hardy_le_of_lt (Wpow_NF hE₁) (Wpow_NF hE) (Wpow_lt hlt₁) hgate₁))
  have hb₂ : g z ≤ hardy (Wpow (E₁ + E₂ + 1))
      (z + (max c₁ c₂ + norm (Wpow E₁) + norm (Wpow E₂))) :=
    le_trans (hg z) (le_trans (hardy_monotone _ harg₂)
      (hardy_le_of_lt (Wpow_NF hE₂) (Wpow_NF hE) (Wpow_lt hlt₂) hgate₂))
  exact max_le hb₁ hb₂

/-- **THE `S*`-domination** (SERIES-4 S-2 capstone) — the concrete pipeline slot
`S* z = max (ewIterTower (rel1 (ewRootSlot e m) K) d α z) (P z)` (`Sslot` unfolded; tower over
the embedding's base root slot, `P` any `Gexp`-iterate-bounded value function — the
`gvb_le_iter` shape, taken as a hypothesis because `gvb` lives in `wip/ReadoffValueGate.lean`)
is padded-Hardy-dominated at ONE fixed level: `ewRootSlot_dom_pad → rel1_dom_pad →
ewIterTower_dom_pad` on the tower half, `hardy_Wpow_iter_dom_pad` on the `P` half,
`dom_pad_max` to join. -/
theorem Sstar_dom_pad (e : ONote) (he : e.NF) (m K d : ℕ) (α : ONote) (hα : α.NF)
    {P : ℕ → ℕ} {E₀ : ONote} (hE₀ : E₀.NF) {k V : ℕ}
    (hP : ∀ z, P z ≤ (hardy (Wpow E₀))^[k] (max V z)) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
      ∀ z, max (ewIterTower (rel1 (ewRootSlot e m) K) d α z) (P z)
        ≤ hardy (Wpow E) (z + c) := by
  haveI := he
  haveI h1 : (e + 1).NF := ONote.add_nf e 1
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI hL : ((e + 1) + 2).NF := ONote.add_nf (e + 1) 2
  have hL0 : (e + 1) + 2 ≠ 0 := by
    intro h
    have hh := congrArg ONote.repr h
    rw [ONote.repr_add (e + 1) 2,
      show ((2 : ONote)).repr = ((2 : ℕ) : Ordinal) from repr_ofNat 2, repr_zero] at hh
    push_cast at hh
    exact (lt_of_lt_of_le zero_lt_two le_add_self).ne' hh
  have hrel1 := rel1_dom_pad (ewRootSlot_dom_pad e he m) K
  obtain ⟨E₁, c₁, hE₁, hE₁0, htower⟩ := ewIterTower_dom_pad hL hL0 hrel1 α hα d
  obtain ⟨E₂, c₂, hE₂, hE₂0, _hlt, hiter⟩ := hardy_Wpow_iter_dom_pad E₀ hE₀ k
  have hPdom : ∀ z, P z ≤ hardy (Wpow E₂) (z + (V + c₂)) := by
    intro z
    have hz : P z ≤ (hardy (Wpow E₀))^[k] (z + V) :=
      le_trans (hP z) ((hardy_monotone (Wpow E₀)).iterate k (by omega))
    exact le_trans hz (le_trans (hiter (z + V)) (hardy_monotone _ (by omega)))
  obtain ⟨E, c, hE, hE0, _, _, hmax⟩ := dom_pad_max hE₁ hE₂ htower hPdom
  exact ⟨E, c, hE, hE0, hmax⟩

/-- **Padded-domination composition** — padded-Hardy-dominated functions compose: raise the
outer level to `E₁+E₂+1` (gate = `norm(ω^{E₁})`, paid by the inner VALUE `≥ z + pad`), collapse
the ordered double Hardy, raise once more.  Result level `E₁+E₂+1+1`. -/
theorem dom_pad_comp {f g : ℕ → ℕ} {E₁ E₂ : ONote} {c₁ c₂ : ℕ}
    (hE₁ : E₁.NF) (hE₂ : E₂.NF)
    (hf : ∀ z, f z ≤ hardy (Wpow E₁) (z + c₁))
    (hg : ∀ z, g z ≤ hardy (Wpow E₂) (z + c₂)) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
      ∀ z, f (g z) ≤ hardy (Wpow E) (z + c) := by
  haveI := hE₁
  haveI := hE₂
  haveI h12 : (E₁ + E₂).NF := ONote.add_nf E₁ E₂
  haveI hA : (E₁ + E₂ + 1).NF := ONote.add_nf (E₁ + E₂) 1
  haveI hE : (E₁ + E₂ + 1 + 1).NF := ONote.add_nf (E₁ + E₂ + 1) 1
  haveI hWA : (Wpow (E₁ + E₂ + 1)).NF := Wpow_NF hA
  haveI hWE₂ : (Wpow E₂).NF := Wpow_NF hE₂
  haveI hsum : (Wpow (E₁ + E₂ + 1) + Wpow E₂).NF := ONote.add_nf _ _
  have hrepr : (E₁ + E₂ + 1).repr = E₁.repr + E₂.repr + 1 := by
    rw [ONote.repr_add (E₁ + E₂) 1, ONote.repr_add E₁ E₂, ONote.repr_one]
    push_cast
    rfl
  have hlt₁ : E₁ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₁.repr ≤ E₁.repr + E₂.repr := le_self_add
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hlt₂ : E₂ < E₁ + E₂ + 1 := by
    rw [lt_def, hrepr]
    calc E₂.repr ≤ E₁.repr + E₂.repr := le_add_self
      _ < E₁.repr + E₂.repr + 1 := lt_add_one _
  have hne : E₁ + E₂ + 1 + 1 ≠ 0 := by
    intro h
    have hh := congrArg ONote.repr h
    rw [ONote.repr_add (E₁ + E₂ + 1) 1, ONote.repr_one, repr_zero] at hh
    push_cast at hh
    exact (lt_of_lt_of_le zero_lt_one le_add_self).ne' hh
  refine ⟨E₁ + E₂ + 1 + 1,
    c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂),
    hE, hne, fun z => ?_⟩
  have h1 : f (g z) ≤ hardy (Wpow E₁) (g z + c₁) := hf (g z)
  have h2 : g z + c₁ ≤ hardy (Wpow E₂) (z + c₂) + c₁ := by
    have := hg z
    omega
  have h3 : hardy (Wpow E₂) (z + c₂) + c₁ ≤ hardy (Wpow E₂) (z + c₂ + c₁) :=
    hardy_arg_add _ _ _
  have h4 : hardy (Wpow E₂) (z + c₂ + c₁) ≤ hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))) :=
    hardy_monotone _ (by omega)
  have hY : f (g z) ≤ hardy (Wpow E₁) (hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))) :=
    le_trans h1 (hardy_monotone _ (le_trans h2 (le_trans h3 h4)))
  have hgate₁ : norm (Wpow E₁) ≤ hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))) := by
    have := le_hardy (Wpow E₂)
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))
    omega
  have hraise : hardy (Wpow E₁) (hardy (Wpow E₂)
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))))
      ≤ hardy (Wpow (E₁ + E₂ + 1)) (hardy (Wpow E₂)
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))) :=
    hardy_le_of_lt (Wpow_NF hE₁) (Wpow_NF hA) (Wpow_lt hlt₁) hgate₁
  have hcol := hardy_double_collapse hA hE₂ hlt₂
      (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))
  have hfin : hardy (Wpow (E₁ + E₂ + 1) + Wpow E₂)
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂)))
      ≤ hardy (Wpow (E₁ + E₂ + 1 + 1))
        (z + (c₁ + c₂ + norm (Wpow E₁) + norm (Wpow (E₁ + E₂ + 1) + Wpow E₂))) :=
    hardy_le_of_lt hsum (Wpow_NF hE) (Wpow_add_lt_Wpow_succ hA hE₂ hlt₂) (by omega)
  calc f (g z) ≤ _ := hY
    _ ≤ _ := hraise
    _ = _ := hcol
    _ ≤ _ := hfin

/-- `2^x` sits under `H_{ω²}` — the floor fact that lets an `Nlog` certificate pay a linear
`norm` gate (via `norm < 2^{Nlog+1}`). -/
theorem two_pow_le_hardy_Wpow2 (x : ℕ) : 2 ^ x ≤ hardy (Wpow (ofNat 2)) x := by
  have h := hardy_omega_pow_ofNat 2 x
  have h2 : fastGrowing (ofNat 2) (x + 1) = 2 ^ (x + 1) * (x + 1) := by
    rw [show (ofNat 2 : ONote) = 2 from rfl, ONote.fastGrowing_two]
  rw [h2] at h
  show 2 ^ x ≤ hardy (oadd (ofNat 2) 1 0) x
  have hexp : 2 ^ (x + 1) = 2 * 2 ^ x := by rw [pow_succ]; ring
  have hone : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have hmul : 2 * 2 ^ x * 1 ≤ 2 * 2 ^ x * (x + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [hexp] at h
  omega

/-- **The `α'`-uniform level cap** (SERIES-4 S-3 brick).  The read-off hands a per-`m`
ordinal `α' ≤ γ` together with its `Nlog α'` certificate; the double-Hardy bound of
`ewIter_hardy_le_of_dom_pad` then caps at the FIXED level `ω^{e₀+2+1+γ+1}`: the outer
norm-gate `norm(ω^{e₀+2+1+α'}) ≤ normSum(e₀+2+1) + norm α' + 1` with `norm α' < 2^{Nlog α'+1}`
is paid by the INNER Hardy value, which exceeds `2^{Nlog α' + q}` (`H_{ω^{e₀+2}} ≥ H_{ω²} ≥ 2^·`
since `e₀ ≠ 0`).  `Nlog α'` stays in the argument — the caller bounds it from the
`Zef2TCProv` certificate. -/
theorem ewIter_dom_pad_levelcap {f : ℕ → ℕ} {e₀ γ : ONote} {c : ℕ}
    (he₀ : e₀.NF) (he₀0 : e₀ ≠ 0) (hγ : γ.NF)
    (hdom : ∀ z, f z ≤ hardy (Wpow e₀) (z + c)) :
    ∃ q : ℕ, ∀ (α' : ONote), α'.NF → α' ≤ γ → ∀ x,
      ewIter f α' x
        ≤ hardy (Wpow (e₀ + 2 + 1 + γ + 1))
            (hardy (Wpow (e₀ + 2)) (Nlog α' + x + q)) := by
  haveI := he₀
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI hNFe2 : (e₀ + 2).NF := ONote.add_nf e₀ 2
  haveI hNFe21 : (e₀ + 2 + 1).NF := ONote.add_nf (e₀ + 2) 1
  haveI := hγ
  haveI hNFg : (e₀ + 2 + 1 + γ).NF := ONote.add_nf (e₀ + 2 + 1) γ
  haveI hNFL : (e₀ + 2 + 1 + γ + 1).NF := ONote.add_nf (e₀ + 2 + 1 + γ) 1
  have he₀pos : (1 : Ordinal) ≤ e₀.repr :=
    Order.one_le_iff_ne_zero.mpr
      (fun h0 => he₀0 (repr_inj.mp (by rw [h0, repr_zero])))
  refine ⟨(norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
      + (normSum (e₀ + 2 + 1) + 1) + 2, fun α' hα' hle x => ?_⟩
  haveI := hα'
  haveI hNFA : (e₀ + 2 + 1 + α').NF := ONote.add_nf (e₀ + 2 + 1) α'
  have h0 := ewIter_hardy_le_of_dom_pad he₀ he₀0 hdom α' hα' x
  have h1 : ewIter f α' x
      ≤ hardy (Wpow (e₀ + 2 + 1 + α'))
          (hardy (Wpow (e₀ + 2))
            (Nlog α' + x + ((norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1)
              + norm (e₀ + 2) + 8 + c) + (normSum (e₀ + 2 + 1) + 1) + 2))) :=
    le_trans h0 (hardy_monotone _ (hardy_monotone _ (by omega)))
  -- the inner Hardy value pays the outer norm gate
  have hY2 : 2 ^ (Nlog α' + x + ((norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1)
        + norm (e₀ + 2) + 8 + c) + (normSum (e₀ + 2 + 1) + 1) + 2))
      ≤ hardy (Wpow (e₀ + 2)) (Nlog α' + x + ((norm (e₀ + 1) + norm e₀
        + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
        + (normSum (e₀ + 2 + 1) + 1) + 2)) := by
    refine le_trans (two_pow_le_hardy_Wpow2 _) ?_
    have hlt2 : (ofNat 2 : ONote) < e₀ + 2 := by
      rw [lt_def, ONote.repr_add e₀ 2, repr_ofNat,
        show ((2 : ONote)).repr = ((2 : ℕ) : Ordinal) from repr_ofNat 2]
      have h1lt : (1 : Ordinal) < e₀.repr + 1 := lt_of_le_of_lt he₀pos (lt_add_one _)
      have hsucc : (1 : Ordinal) + 1 < (e₀.repr + 1) + 1 := by
        rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
        exact Order.succ_lt_succ h1lt
      calc ((2 : ℕ) : Ordinal) = 1 + 1 := by push_cast; exact one_add_one_eq_two.symm
        _ < (e₀.repr + 1) + 1 := hsucc
        _ = e₀.repr + ((2 : ℕ) : Ordinal) := by
            rw [add_assoc, one_add_one_eq_two]; push_cast; rfl
    have hn2 : norm (Wpow (ofNat 2)) = 2 := by
      simp [Wpow, ofNat_succ, norm_oadd]
    exact hardy_le_of_lt (Wpow_NF (nf_ofNat 2)) (Wpow_NF hNFe2) (Wpow_lt hlt2)
      (by rw [hn2]; omega)
  have hnormW : norm (Wpow (e₀ + 2 + 1 + α'))
      ≤ normSum (e₀ + 2 + 1) + norm α' + 1 := by
    show norm (oadd (e₀ + 2 + 1 + α') 1 0) ≤ _
    rw [norm_oadd]
    have hna := norm_add_le (e₀ + 2 + 1) α'
    simp only [norm_zero, PNat.one_coe]
    omega
  have hnorm_a : norm α' < 2 ^ (Nlog α' + 1) := norm_lt_two_pow_Nlog α'
  -- 2-power arithmetic: P·q pays K₀ + P
  have hgate : norm (Wpow (e₀ + 2 + 1 + α'))
      ≤ hardy (Wpow (e₀ + 2)) (Nlog α' + x + ((norm (e₀ + 1) + norm e₀
        + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
        + (normSum (e₀ + 2 + 1) + 1) + 2)) := by
    refine le_trans hnormW (le_trans ?_ hY2)
    · -- normSum(e₀+2+1) + norm α' + 1 ≤ 2^(Nlog α' + x + q)
      have hsplit : 2 ^ ((Nlog α' + 1) + ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1))
          ≤ 2 ^ (Nlog α' + x + ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 2)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hpow_add : 2 ^ ((Nlog α' + 1) + ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1))
          = 2 ^ (Nlog α' + 1) * 2 ^ ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1) := pow_add 2 _ _
      have hP2 : 2 ≤ 2 ^ (Nlog α' + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (Nlog α' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hQq : (norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1
          ≤ 2 ^ ((norm (e₀ + 1) + norm e₀ + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1) :=
        Nat.le_of_lt Nat.lt_two_pow_self
      have hmul : 2 ^ (Nlog α' + 1) * ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1)
          ≤ 2 ^ (Nlog α' + 1) * 2 ^ ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1) :=
        Nat.mul_le_mul_left _ hQq
      have hexpand : 2 ^ (Nlog α' + 1) * ((norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + (normSum (e₀ + 2 + 1) + 1) + 1)
          = 2 ^ (Nlog α' + 1) * (norm (e₀ + 1) + norm e₀
            + normSum (e₀ + 2 + 1) + norm (e₀ + 2) + 8 + c)
            + 2 ^ (Nlog α' + 1) * (normSum (e₀ + 2 + 1) + 1)
            + 2 ^ (Nlog α' + 1) := by ring
      have hK : normSum (e₀ + 2 + 1) + 1
          ≤ 2 ^ (Nlog α' + 1) * (normSum (e₀ + 2 + 1) + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  exact le_trans h1 (hardy_le_of_lt (Wpow_NF hNFA) (Wpow_NF hNFL)
    (Wpow_lt (by
      rw [lt_def, ONote.repr_add (e₀ + 2 + 1) α',
        show (e₀ + 2 + 1 + γ + 1).repr = (e₀ + 2 + 1).repr + γ.repr + 1 by
          rw [ONote.repr_add (e₀ + 2 + 1 + γ) 1, ONote.repr_add (e₀ + 2 + 1) γ,
            ONote.repr_one]
          push_cast
          rfl]
      calc (e₀ + 2 + 1).repr + α'.repr
          ≤ (e₀ + 2 + 1).repr + γ.repr := (add_le_add_iff_left _).mpr (repr_le_repr hle)
        _ < (e₀ + 2 + 1).repr + γ.repr + 1 := lt_add_one _))
    hgate)

/-- **Padded Hardy eventually under ONE fastGrowing level** (SERIES-4 S-4 brick):
`H_{ω^L}(m+C) < f_{osucc L}(m)` for `m ≥ C+3`.  Route: `hardy_omega_pow_lt_fastGrowing` into
the successor level's iterate stack — each `f_L` application gains `≥ 1`, so `C+2` of them
absorb the pad, and `monotone_iterate_of_id_le` climbs to the full `m`-stack. -/
theorem hardy_pad_lt_fastGrowing_osucc (L : ONote) (hL : L.NF) (C : ℕ) :
    ∀ m, C + 3 ≤ m → hardy (Wpow L) (m + C) < fastGrowing (osucc L) m := by
  intro m hm
  have h1 : hardy (Wpow L) (m + C) < fastGrowing L (m + C + 1) :=
    hardy_omega_pow_lt_fastGrowing L (m + C)
  have hA : ∀ j, m + j ≤ (fastGrowing L)^[j] m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        have hge1 : 1 ≤ (fastGrowing L)^[j] m := by omega
        have := lt_fastGrowing L hge1
        omega
  have hB : fastGrowing L (m + C + 1) ≤ (fastGrowing L)^[C + 2] m := by
    rw [Function.iterate_succ_apply']
    exact fastGrowing_monotone L (hA (C + 1))
  have hC : (fastGrowing L)^[C + 2] m ≤ (fastGrowing L)^[m] m :=
    Function.monotone_iterate_of_id_le (fun x => le_fastGrowing L x) (by omega) m
  have hD : fastGrowing (osucc L) m = (fastGrowing L)^[m] m := by
    rw [fastGrowing_succ _ (fundamentalSequence_osucc hL)]
  omega

/-- The eventual-domination package: a padded-Hardy-dominated function sits eventually under
the ONE fixed level `f_{osucc L}`. -/
theorem dom_pad_eventuallyLE {f : ℕ → ℕ} {L : ONote} {C : ℕ} (hL : L.NF)
    (hdom : ∀ m, f m ≤ hardy (Wpow L) (m + C)) :
    ∃ o : ONote, o.NF ∧ ∃ N, ∀ m, N ≤ m → f m ≤ fastGrowing o m :=
  ⟨osucc L, osucc_NF hL, C + 3, fun m hm =>
    le_trans (hdom m) (le_of_lt (hardy_pad_lt_fastGrowing_osucc L hL C m hm))⟩

/-- **The fixed pipeline slot `S°` is padded-Hardy-dominated** — `Sstar_dom_pad` at the
`rel1`-free base and CONCRETE `P = Gexp^[k]` (`Gexp = hardy ω²` written `oadd (ofNat 2) 1 0`
so the statement is legible without `Wpow`; the m-uniformization moves all `m`-dependence into
the ARGUMENT, so this single bound serves every `m`). -/
theorem Scirc_dom_pad (e : ONote) (he : e.NF) (Bb d k : ℕ) (α : ONote) (hα : α.NF) :
    ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
      ∀ z, max (ewIterTower (ewRootSlot e Bb) d α z)
          ((hardy (oadd (ofNat 2) 1 0))^[k] z)
        ≤ hardy (oadd E 1 0) (z + c) := by
  haveI := he
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI h1 : (e + 1).NF := ONote.add_nf e 1
  haveI hL : ((e + 1) + 2).NF := ONote.add_nf (e + 1) 2
  have hL0 : (e + 1) + 2 ≠ 0 := by
    intro h
    have hh := congrArg ONote.repr h
    rw [ONote.repr_add (e + 1) 2,
      show ((2 : ONote)).repr = ((2 : ℕ) : Ordinal) from repr_ofNat 2, repr_zero] at hh
    push_cast at hh
    exact (lt_of_lt_of_le zero_lt_two le_add_self).ne' hh
  obtain ⟨E₁, c₁, hE₁, hE₁0, htower⟩ :=
    ewIterTower_dom_pad hL hL0 (ewRootSlot_dom_pad e he Bb) α hα d
  obtain ⟨E₂, c₂, hE₂, hE₂0, _, hiter⟩ := hardy_Wpow_iter_dom_pad (ofNat 2) (nf_ofNat 2) k
  have hiter' : ∀ z, (hardy (oadd (ofNat 2) 1 0))^[k] z ≤ hardy (Wpow E₂) (z + c₂) := hiter
  obtain ⟨E, c, hE, hE0, _, _, hmax⟩ := dom_pad_max hE₁ hE₂ htower hiter'
  exact ⟨E, c, hE, hE0, hmax⟩

/-- `2y + q` sits under `H_{ω²}(y)` once `y ≥ max(q,1)` (the Hardy value is `≥ 4y+3`). -/
theorem two_mul_add_le_hardy_omega_sq {y q : ℕ} (hq : q ≤ y) (hy : 1 ≤ y) :
    2 * y + q ≤ hardy (oadd (ofNat 2) 1 0) y := by
  have h := hardy_omega_pow_ofNat 2 y
  have h2 : fastGrowing (ofNat 2) (y + 1) = 2 ^ (y + 1) * (y + 1) := by
    rw [show (ofNat 2 : ONote) = 2 from rfl, ONote.fastGrowing_two]
  rw [h2] at h
  have h4 : 4 ≤ 2 ^ (y + 1) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (y + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmul : 4 * (y + 1) ≤ 2 ^ (y + 1) * (y + 1) := Nat.mul_le_mul_right _ h4
  omega

/-- **THE MASTER CONVERSION** (SERIES-4 S-3 capstone, slot-abstract form).  Given ANY slot `S`
padded-Hardy-dominated and inflationary, ONE fixed `fastGrowing o` eventually dominates every
value `n` the uniformized read-off produces: `n ≤ ewIter S α' (S (max K₀ m))` at any per-`m`
`α' ≤ γ` carrying its `Nlog` certificate.  Chain: `ewIter_dom_pad_levelcap` (fixed level, α'
absorbed) → the `Nlog` certificate + `two_mul_add_le_hardy_omega_sq` absorb the inner argument
into `Gexp(S(max K₀ m))` (eventually, `m ≥ q`) → three `dom_pad_comp`s collapse the
Hardy stack to ONE `H_{E₅}(m+c₅)` → `hardy_pad_lt_fastGrowing_osucc`. -/
theorem master_conversion {S : ℕ → ℕ} {E_S γ : ONote} {c_S : ℕ}
    (hES : E_S.NF) (hES0 : E_S ≠ 0) (hγ : γ.NF)
    (hSdom : ∀ z, S z ≤ hardy (oadd E_S 1 0) (z + c_S))
    (hSinfl : ∀ z, z ≤ S z) (K₀ : ℕ) :
    ∃ o : ONote, o.NF ∧ ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ α' : ONote, α'.NF → α' ≤ γ → ∀ n : ℕ,
        Nlog α' ≤ S (max K₀ m) →
        n ≤ ewIter S α' (S (max K₀ m)) →
        n ≤ fastGrowing o m := by
  haveI := hES
  haveI : (2 : ONote).NF := nf_ofNat 2
  haveI hNF2 : (E_S + 2).NF := ONote.add_nf E_S 2
  haveI hNF21 : (E_S + 2 + 1).NF := ONote.add_nf (E_S + 2) 1
  haveI := hγ
  haveI hNFg : (E_S + 2 + 1 + γ).NF := ONote.add_nf (E_S + 2 + 1) γ
  haveI hNFL : (E_S + 2 + 1 + γ + 1).NF := ONote.add_nf (E_S + 2 + 1 + γ) 1
  have hSdom' : ∀ z, S z ≤ hardy (Wpow E_S) (z + c_S) := hSdom
  obtain ⟨q, hq⟩ := ewIter_dom_pad_levelcap hES hES0 hγ hSdom'
  -- composition chain: Gexp ∘ (H_{E_S}(·+K₀+c_S)) → E₃; H_{E_S+2} ∘ E₃ → E₄; H_LL ∘ E₄ → E₅
  obtain ⟨E₃, c₃, hE₃, hE₃0, hcomp₁⟩ :=
    dom_pad_comp (f := hardy (Wpow (ofNat 2))) (g := fun z => hardy (Wpow E_S) (z + (K₀ + c_S)))
      (c₁ := 0) (c₂ := K₀ + c_S)
      (nf_ofNat 2) hES (fun z => by simp) (fun z => le_rfl)
  obtain ⟨E₄, c₄, hE₄, hE₄0, hcomp₂⟩ :=
    dom_pad_comp (f := hardy (Wpow (E_S + 2))) (g := fun z => hardy (Wpow E₃) (z + c₃))
      (c₁ := 0) (c₂ := c₃)
      hNF2 hE₃ (fun z => by simp) (fun z => le_rfl)
  obtain ⟨E₅, c₅, hE₅, hE₅0, hcomp₃⟩ :=
    dom_pad_comp (f := hardy (Wpow (E_S + 2 + 1 + γ + 1))) (g := fun z => hardy (Wpow E₄) (z + c₄))
      (c₁ := 0) (c₂ := c₄)
      hNFL hE₄ (fun z => by simp) (fun z => le_rfl)
  refine ⟨osucc E₅, osucc_NF hE₅, q + c₅ + 3, fun m hm α' hα' hle n hNcert hn => ?_⟩
  -- the m-side value x := S (max K₀ m)
  have hx_ge : max K₀ m ≤ S (max K₀ m) := hSinfl _
  have hx_ge_m : m ≤ S (max K₀ m) := le_trans (le_max_right _ _) hx_ge
  have hx_ge_q : q ≤ S (max K₀ m) := le_trans (by omega) hx_ge_m
  have hx_ge_1 : 1 ≤ S (max K₀ m) := le_trans (by omega) hx_ge_m
  -- inner argument absorbed into Gexp x
  have hinner : Nlog α' + S (max K₀ m) + q ≤ 2 * S (max K₀ m) + q := by omega
  have hinner₂ : 2 * S (max K₀ m) + q ≤ hardy (oadd (ofNat 2) 1 0) (S (max K₀ m)) :=
    two_mul_add_le_hardy_omega_sq hx_ge_q hx_ge_1
  -- x ≤ H_{E_S}(m + (K₀ + c_S))
  have hx_dom : S (max K₀ m) ≤ hardy (Wpow E_S) (m + (K₀ + c_S)) :=
    le_trans (hSdom' _) (hardy_monotone _ (by omega))
  have hGx : hardy (oadd (ofNat 2) 1 0) (S (max K₀ m))
      ≤ hardy (Wpow (ofNat 2)) (hardy (Wpow E_S) (m + (K₀ + c_S))) :=
    hardy_monotone _ hx_dom
  have hE₃b : hardy (Wpow (ofNat 2)) (hardy (Wpow E_S) (m + (K₀ + c_S)))
      ≤ hardy (Wpow E₃) (m + c₃) := hcomp₁ m
  -- assemble
  have hmain := hq α' hα' hle (S (max K₀ m))
  have hstep1 : hardy (Wpow (E_S + 2)) (Nlog α' + S (max K₀ m) + q)
      ≤ hardy (Wpow (E_S + 2)) (hardy (Wpow E₃) (m + c₃)) :=
    hardy_monotone _ (le_trans hinner (le_trans hinner₂ (le_trans hGx hE₃b)))
  have hstep2 : hardy (Wpow (E_S + 2)) (hardy (Wpow E₃) (m + c₃))
      ≤ hardy (Wpow E₄) (m + c₄) := hcomp₂ m
  have hstep3 : hardy (Wpow (E_S + 2 + 1 + γ + 1)) (hardy (Wpow E₄) (m + c₄))
      ≤ hardy (Wpow E₅) (m + c₅) := hcomp₃ m
  have hchain : ewIter S α' (S (max K₀ m)) ≤ hardy (Wpow E₅) (m + c₅) :=
    le_trans hmain (le_trans (hardy_monotone _ (le_trans hstep1 hstep2)) hstep3)
  have hfin : hardy (Wpow E₅) (m + c₅) < fastGrowing (osucc E₅) m :=
    hardy_pad_lt_fastGrowing_osucc E₅ hE₅ c₅ m (by omega)
  omega

end GoodsteinPA.HardyMajorization
