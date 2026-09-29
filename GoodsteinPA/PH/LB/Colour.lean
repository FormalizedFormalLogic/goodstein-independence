/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.LB.Cnf

@[expose] public section

/-!
# PH lower bound: The colourings `χ^k_m`, the colour count, Lemma 7.9 (spec §2.7–2.8).

Part of the skeleton indexed in `GoodsteinPA/PH/LowerBound.lean`; statements are the design.
-/

namespace GoodsteinPA.PH.LB

open ONote

/-! ### §2.7  The colourings `χ^k_m` and the colour count -/

/-- `|C^k_m| = k + Σ_{i<m} 3^i`. -/
def ncol (k m : ℕ) : ℕ := k + ∑ i ∈ Finset.range m, 3 ^ i

/-- The coefficient of `ω^j` (`j` finite) in `α`. -/
def coeffAt : ONote → ℕ → ℕ
  | zero, _ => 0
  | oadd e n a, j => if e = ofNat j then n else coeffAt a j

/-- `χ^k_1(α, β)`: the first base-`ω` digit, counted from `ω^k` down, where `β`'s is smaller. -/
def chi1 (k : ℕ) (α β : ONote) : ℕ :=
  ((List.range (k + 1)).find? fun i => decide (coeffAt β (k - i) < coeffAt α (k - i))).getD 0

/-- Base-3 packing of a tuple of `χ`-colours. -/
def pack3 : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + 3 * pack3 cs

/-- `χ^k_m` on a decreasing list `β₀ > … > β_m` (length `m + 1`).  Colours in `C^k_m` are numbers
`< ncol k m`: `C^k_{m+1} = C^k_m ∪ {0̂,1̂,2̂}^m`, the tuple part offset by `ncol k m`. -/
def chiK (k : ℕ) : ℕ → List ONote → ℕ
  | 0, _ => 0
  | 1, bs => chi1 k (bs.getD 0 0) (bs.getD 1 0)
  | m + 2, bs =>
    let cs := (List.range (m + 1)).map fun i => chi3 (bs.getD i 0) (bs.getD (i + 1) 0) (bs.getD (i + 2) 0)
    if cs.all (· == 2) then
      chiK k (m + 1) ((List.range (m + 2)).map fun i => Ed (bs.getD i 0) (bs.getD (i + 1) 0))
    else ncol k (m + 1) + pack3 cs

/-! #### Helper lemmas: `ncol`, `pack3`, `chi3` -/

theorem ncol_succ (k m : ℕ) : ncol k (m + 1) = ncol k m + 3 ^ m := by
  simp [ncol, Finset.sum_range_succ, Nat.add_assoc]

theorem ncol_one (k : ℕ) : ncol k 1 = k + 1 := by simp [ncol]

theorem pack3_lt {l : List ℕ} (h : ∀ x ∈ l, x < 3) : pack3 l < 3 ^ l.length := by
  induction l with
  | nil => simp [pack3]
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [pack3, List.length_cons, pow_succ]
    omega

theorem pack3_inj {l₁ : List ℕ} : ∀ {l₂ : List ℕ}, l₁.length = l₂.length → (∀ x ∈ l₁, x < 3) →
    (∀ x ∈ l₂, x < 3) → pack3 l₁ = pack3 l₂ → l₁ = l₂ := by
  induction l₁ with
  | nil => intro l₂ hl _ _ _; cases l₂ with | nil => rfl | cons _ _ => simp at hl
  | cons c₁ cs₁ ih =>
    intro l₂ hl h₁ h₂ hp
    cases l₂ with
    | nil => simp at hl
    | cons c₂ cs₂ =>
      simp only [pack3] at hp
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hc₁ := h₁ c₁ (List.mem_cons_self ..)
      have hc₂ := h₂ c₂ (List.mem_cons_self ..)
      have e1 : c₁ = c₂ := by omega
      have e2 : pack3 cs₁ = pack3 cs₂ := by omega
      rw [e1, ih hl (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
        (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) e2]

theorem chi3_le_two (a b c : ONote) : chi3 a b c ≤ 2 := by
  unfold chi3; split_ifs <;> omega

theorem chiK_lt (k m : ℕ) (hm : 1 ≤ m) (bs : List ONote) : chiK k m bs < ncol k m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  clear hm
  induction m generalizing bs with
  | zero =>
    rw [chiK, ncol_one]
    unfold chi1
    rcases hf : (List.range (k + 1)).find? _ with _ | c
    · simp
    · have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
      simpa using this
  | succ m ih =>
    rw [chiK]
    split_ifs with h
    · exact lt_of_lt_of_le (ih _) (by rw [ncol_succ k (m + 1)]; exact Nat.le_add_right _ _)
    · rw [ncol_succ k (m + 1)]
      have hlt := pack3_lt (l := (List.range (m + 1)).map fun i =>
        chi3 (bs.getD i 0) (bs.getD (i + 1) 0) (bs.getD (i + 2) 0)) (by
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨i, _, rfl⟩ := hx
          have := chi3_le_two (bs.getD i 0) (bs.getD (i + 1) 0) (bs.getD (i + 2) 0)
          omega)
      simp only [List.length_map, List.length_range] at hlt
      omega

/-- The window `β i, …, β (i + m)`. -/
def window (β : ℕ → ONote) (m i : ℕ) : List ONote := (List.range (m + 1)).map fun j => β (i + j)

/-! #### Helper lemmas: `window`, `coeffAt`, `termAt`/`Ed`, chains -/

theorem window_getD {β : ℕ → ONote} {m i j : ℕ} (hj : j ≤ m) :
    (window β m i).getD j 0 = β (i + j) := by
  simp [window, List.getD_eq_getElem?_getD, Nat.lt_succ_of_le hj]

theorem ofNat_inj' {i j : ℕ} (h : ofNat i = ofNat j) : i = j := by
  have := congrArg ONote.repr h
  simp only [repr_ofNat, Nat.cast_inj] at this
  exact this

/-- An NF exponent with `repr < k + 1` is `ofNat j` for some `j ≤ k`. -/
theorem exists_eq_ofNat_of_repr_lt {e : ONote} (he : e.NF) {k : ℕ}
    (h : e.repr < ((k + 1 : ℕ) : Ordinal)) : ∃ j ≤ k, e = ofNat j := by
  have hω : e.repr < Ordinal.omega0 := lt_of_lt_of_le h (Ordinal.natCast_lt_omega0 _).le
  obtain ⟨j, hj⟩ := Ordinal.lt_omega0.1 hω
  refine ⟨j, ?_, ?_⟩
  · rw [hj] at h
    have : j < k + 1 := by exact_mod_cast h
    omega
  · haveI := he
    exact (repr_inj (a := e) (b := ofNat j)).1 (by rw [hj, repr_ofNat])

theorem coeffAt_eq_zero_of_nfBelow {a : ONote} {j : ℕ} (h : a.NFBelow (j : Ordinal)) :
    coeffAt a j = 0 := by
  induction a with
  | zero => rfl
  | oadd e n a _ ih =>
    have hlt := h.lt
    have hne : e ≠ ofNat j := by
      rintro rfl; simp at hlt
    simp only [coeffAt, if_neg hne]
    exact ih (h.snd.mono hlt.le)

theorem coeffAt_le_rnorm (a : ONote) (j : ℕ) : coeffAt a j ≤ rnorm a := by
  induction a with
  | zero => simp [coeffAt, rnorm]
  | oadd e n a _ ih =>
    simp only [coeffAt, rnorm]
    split_ifs <;> omega

/-- Two NF ordinals below `ω^(k+1)` with `β < α` differ at some base-`ω` digit `j ≤ k`, with
`β`'s digit smaller (the first differing digit from the top qualifies). -/
theorem exists_coeffAt_lt {α : ONote} (hα : α.NF) : ∀ {k : ℕ} {β : ONote}, β.NF → β < α →
    α.NFBelow ((k + 1 : ℕ) : Ordinal) → β.NFBelow ((k + 1 : ℕ) : Ordinal) →
    ∃ j ≤ k, coeffAt β j < coeffAt α j := by
  induction α with
  | zero => intro k β _ hlt _ _; exact absurd hlt (by simp [lt_def])
  | oadd e n a _ ih =>
    intro k β hβ hlt hαb hβb
    obtain ⟨j, hjk, rfl⟩ := exists_eq_ofNat_of_repr_lt hαb.fst hαb.lt
    cases β with
    | zero =>
      refine ⟨j, hjk, ?_⟩
      simp only [coeffAt]
      exact n.pos
    | oadd e' n' b =>
      obtain ⟨j', hj'k, rfl⟩ := exists_eq_ofNat_of_repr_lt hβb.fst hβb.lt
      rcases lt_trichotomy j' j with h | h | h
      · refine ⟨j, hjk, ?_⟩
        have hne : ofNat j' ≠ ofNat j := fun h' => by have := ofNat_inj' h'; omega
        simp only [coeffAt, if_neg hne]
        rw [coeffAt_eq_zero_of_nfBelow (hβb.snd.mono (by simp; exact_mod_cast h.le))]
        exact n.pos
      · subst h
        rcases lt_trichotomy (n' : ℕ) n with h | h | h
        · exact ⟨j', hjk, by simp only [coeffAt]; exact h⟩
        · have hn : n' = n := PNat.coe_inj.1 h
          subst hn
          have hba : b < a := by
            rw [lt_def] at hlt ⊢
            simp only [ONote.repr] at hlt
            exact (add_lt_add_iff_left _).1 hlt
          cases j' with
          | zero =>
            exfalso
            have ha0 : a = 0 := NFBelow_zero.1 (by simpa using hαb.snd)
            rw [ha0] at hba
            exact absurd hba (by simp [lt_def])
          | succ j₀ =>
            obtain ⟨j'', hj'', hlt''⟩ :=
              ih hα.snd hβ.snd hba (by simpa using hαb.snd) (by simpa using hβb.snd)
            refine ⟨j'', by omega, ?_⟩
            have hne : ofNat (j₀ + 1) ≠ ofNat j'' := fun h' => by have := ofNat_inj' h'; omega
            simp only [coeffAt, if_neg hne]
            exact hlt''
        · exact absurd (oadd_lt_oadd_2 hα h) (lt_asymm hlt)
      · exact absurd (oadd_lt_oadd_1 hα (by rw [lt_def]; simp; exact_mod_cast h)) (lt_asymm hlt)

theorem termAt_fst_NF {a : ONote} (ha : a.NF) (i : ℕ) : (termAt a i).1.NF := by
  induction a generalizing i with
  | zero => exact NF.zero
  | oadd e n a _ ih =>
    cases i with
    | zero => exact ha.fst
    | succ i => exact ih ha.snd i

theorem Ed_NF {a : ONote} (ha : a.NF) (b : ONote) : (Ed a b).NF := termAt_fst_NF ha _

theorem termAt_fst_lt_of_NFBelow {a b : ONote} (hb : 0 < b) (h : a.NFBelow b.repr) (i : ℕ) :
    (termAt a i).1 < b := by
  induction a generalizing i with
  | zero => exact hb
  | oadd e n a _ ih =>
    cases i with
    | zero => exact lt_def.2 h.lt
    | succ i => exact ih (h.snd.mono h.lt.le) i

theorem Ed_lt_of_lt_oadd {a b c : ONote} (ha : a.NF) (h : a < oadd b 1 0) (hb : 0 < b) :
    Ed a c < b :=
  termAt_fst_lt_of_NFBelow hb (NF.below_of_lt' (by simpa [lt_def, ONote.repr] using h) ha) _

theorem Chain.le_zero {β : ℕ → ONote} {ℓ : ℕ} (hβ : Chain β ℓ) {i : ℕ} (hi : i ≤ ℓ) :
    β i ≤ β 0 := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (hβ.2 i hi).le.trans (ih (by omega))

/-- `chiK` at `m + 2` on a window, with the `getD`s resolved. -/
theorem chiK_succ_succ_window (k m i : ℕ) (β : ℕ → ONote) :
    chiK k (m + 2) (window β (m + 2) i) =
      if ((List.range (m + 1)).map fun j =>
          chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2))).all (· == 2) then
        chiK k (m + 1) (window (fun p => Ed (β p) (β (p + 1))) (m + 1) i)
      else ncol k (m + 1) +
        pack3 ((List.range (m + 1)).map fun j =>
          chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2))) := by
  rw [chiK]
  have e1 : ((List.range (m + 1)).map fun j => chi3 ((window β (m + 2) i).getD j 0)
      ((window β (m + 2) i).getD (j + 1) 0) ((window β (m + 2) i).getD (j + 2) 0))
      = (List.range (m + 1)).map fun j => chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2)) := by
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [window_getD (by omega), window_getD (by omega), window_getD (by omega),
      Nat.add_assoc, Nat.add_assoc]
  have e2 : ((List.range (m + 2)).map fun j =>
      Ed ((window β (m + 2) i).getD j 0) ((window β (m + 2) i).getD (j + 1) 0))
      = window (fun p => Ed (β p) (β (p + 1))) (m + 1) i := by
    conv_rhs => unfold window
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [window_getD (by omega), window_getD (by omega)]
    simp only [Nat.add_assoc]
  simp only [e1, e2]

/-- **L7.9**: a chain below `ω_m(k+1)` whose consecutive `(m+1)`-windows all get colour `c` has
`ℓ < r(β₀) + m`. -/
theorem chiK_homog_len {k m ℓ c : ℕ} {β : ℕ → ONote} (hm : 1 ≤ m) (hmℓ : m < ℓ) (hβ : Chain β ℓ)
    (htop : β 0 < wtow m (k + 1))
    (hχ : ∀ i, i + m ≤ ℓ → chiK k m (window β m i) = c) : ℓ < rnorm (β 0) + m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  clear hm
  induction m generalizing ℓ c β with
  | zero =>
    -- I. m = 1: the digit at position `c` (from the top) strictly decreases along the chain.
    have hbelow : ∀ i ≤ ℓ, (β i).NFBelow ((k + 1 : ℕ) : Ordinal) := by
      intro i hi
      have h2 : β i < oadd (ofNat (k + 1)) 1 0 :=
        lt_of_le_of_lt (hβ.le_zero hi) (by simpa [wtow] using htop)
      have := NF.below_of_lt' (b := (ofNat (k + 1)).repr)
        (by simpa [lt_def, ONote.repr] using h2) (hβ.1 i hi)
      simpa using this
    have hdesc : ∀ i, i + 1 ≤ ℓ → coeffAt (β (i + 1)) (k - c) < coeffAt (β i) (k - c) := by
      intro i hi
      have h := hχ i hi
      rw [chiK, window_getD (by omega), window_getD le_rfl, Nat.add_zero] at h
      unfold chi1 at h
      obtain ⟨j, hj, hjlt⟩ := exists_coeffAt_lt (hβ.1 i (by omega)) (hβ.1 (i + 1) hi)
        (hβ.2 i hi) (hbelow i (by omega)) (hbelow (i + 1) hi)
      rcases hfind : (List.range (k + 1)).find?
          (fun i' => decide (coeffAt (β (i + 1)) (k - i') < coeffAt (β i) (k - i'))) with _ | c'
      · exfalso
        have := List.find?_eq_none.1 hfind (k - j) (List.mem_range.2 (by omega))
        rw [Nat.sub_sub_self hj] at this
        simp at this
        omega
      · rw [hfind] at h
        simp only [Option.getD_some] at h
        subst h
        have := List.find?_some hfind
        simpa using this
    have hmono : ∀ i ≤ ℓ, coeffAt (β i) (k - c) + i ≤ coeffAt (β 0) (k - c) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have := hdesc i hi
        have := ih (by omega)
        omega
    have := hmono ℓ le_rfl
    have := coeffAt_le_rnorm (β 0) (k - c)
    omega
  | succ m ih =>
    -- II. m + 1 → m + 2 (spec's m → m + 1).
    have hwin : ∀ i, i + (m + 2) ≤ ℓ →
        (if ((List.range (m + 1)).map fun j =>
            chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2))).all (· == 2) then
          chiK k (m + 1) (window (fun p => Ed (β p) (β (p + 1))) (m + 1) i)
        else ncol k (m + 1) +
          pack3 ((List.range (m + 1)).map fun j =>
            chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2)))) = c :=
      fun i hi => (chiK_succ_succ_window k m i β).symm.trans (hχ i hi)
    rcases lt_or_ge c (ncol k (m + 1)) with hc | hc
    · -- CASE 2: `c ∈ C^k_m`; every window takes the recursive branch, so `χ ≡ 2̂`.
      have hall : ∀ i, i + (m + 2) ≤ ℓ → ((List.range (m + 1)).map fun j =>
          chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2))).all (· == 2) = true := by
        intro i hi
        have h := hwin i hi
        by_contra hne
        rw [if_neg hne] at h
        omega
      have h2 : ∀ p, p + 2 ≤ ℓ → chi3 (β p) (β (p + 1)) (β (p + 2)) = 2 := by
        intro p hp
        have := List.all_eq_true.1 (hall (min p (ℓ - (m + 2))) (by omega))
          (chi3 (β p) (β (p + 1)) (β (p + 2))) (by
            rw [List.mem_map]
            refine ⟨p - min p (ℓ - (m + 2)), List.mem_range.2 (by omega), ?_⟩
            have e : min p (ℓ - (m + 2)) + (p - min p (ℓ - (m + 2))) = p := by omega
            rw [e])
        simpa using this
      have hrec : ∀ i, i + (m + 1) ≤ ℓ - 1 →
          chiK k (m + 1) (window (fun p => Ed (β p) (β (p + 1))) (m + 1) i) = c := by
        intro i hi
        have h := hwin i (by omega)
        rwa [if_pos (hall i (by omega))] at h
      have hδchain : Chain (fun p => Ed (β p) (β (p + 1))) (ℓ - 1) :=
        ⟨fun i hi => Ed_NF (hβ.1 i (by omega)) _, fun i hi => chain_Ed_desc hβ h2 i (by omega)⟩
      have hδtop : Ed (β 0) (β 1) < wtow (m + 1) (k + 1) := by
        rw [wtow_succ] at htop
        exact Ed_lt_of_lt_oadd (hβ.1 0 (by omega)) htop (by rw [wtow_succ]; exact oadd_pos _ _ _)
      have := ih hδchain (by omega) hδtop hrec
      have := rnorm_Ed_le (β 0) (β (0 + 1))
      omega
    · -- CASE 1: `c` is a tuple colour; every window takes the tuple branch, so `χ` is constant
      -- and `≠ 2̂`.
      have hnot : ∀ i, i + (m + 2) ≤ ℓ → ((List.range (m + 1)).map fun j =>
          chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2))).all (· == 2) = false ∧
          pack3 ((List.range (m + 1)).map fun j =>
            chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2))) = c - ncol k (m + 1) := by
        intro i hi
        have h := hwin i hi
        by_cases hall : ((List.range (m + 1)).map fun j =>
            chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2))).all (· == 2) = true
        · rw [if_pos hall] at h
          have := chiK_lt k (m + 1) (by omega) (window (fun p => Ed (β p) (β (p + 1))) (m + 1) i)
          omega
        · rw [if_neg hall] at h
          exact ⟨by simpa using hall, by omega⟩
      have hbnd : ∀ i, ∀ x ∈ (List.range (m + 1)).map fun j =>
          chi3 (β (i + j)) (β (i + j + 1)) (β (i + j + 2)), x < 3 := by
        intro i x hx
        rw [List.mem_map] at hx
        obtain ⟨j, _, rfl⟩ := hx
        have := chi3_le_two (β (i + j)) (β (i + j + 1)) (β (i + j + 2))
        omega
      have hconst : ∀ p, p + 3 ≤ ℓ →
          chi3 (β p) (β (p + 1)) (β (p + 2)) = chi3 (β (p + 1)) (β (p + 1 + 1)) (β (p + 1 + 2)) := by
        intro p hp
        set i := min p (ℓ - (m + 3)) with hi
        have h1 := hnot i (by omega)
        have h2 := hnot (i + 1) (by omega)
        have heq := pack3_inj (by simp) (hbnd i) (hbnd (i + 1)) (h1.2.trans h2.2.symm)
        rw [List.map_inj_left] at heq
        have := heq (p - i) (List.mem_range.2 (by omega))
        have e1 : i + (p - i) = p := by omega
        have e2 : i + 1 + (p - i) = p + 1 := by omega
        rw [e1, e2] at this
        exact this
      have hconst0 : ∀ p, p + 2 ≤ ℓ →
          chi3 (β p) (β (p + 1)) (β (p + 2)) = chi3 (β 0) (β 1) (β 2) := by
        intro p
        induction p with
        | zero => intro _; rfl
        | succ p ih => intro hp; rw [← hconst p (by omega), ih (by omega)]
      have hc0 : chi3 (β 0) (β 1) (β 2) < 2 := by
        have h0 := (hnot 0 (by omega)).1
        rw [List.all_eq_false] at h0
        obtain ⟨x, hx, hx2⟩ := h0
        rw [List.mem_map] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        rw [List.mem_range] at hj
        rw [hconst0 (0 + j) (by omega)] at hx2
        have := chi3_le_two (β 0) (β 1) (β 2)
        simp at hx2
        omega
      have := chain_len_le_rnorm hβ (by omega) hc0 (fun i hi => hconst0 i hi)
      omega

end GoodsteinPA.PH.LB

end
