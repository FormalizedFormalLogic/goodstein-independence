/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.ToMathlib.Hardy.Basic

@[expose] public section

/-!
# PH lower bound: CNF data, `r(α)`, `d/K/E`, `ω_m(k)`, `fsStep`; Lemmas 7.6, 7.7, 7.8 (spec §2.1–2.6).

Part of the skeleton indexed in `GoodsteinPA/PH/LowerBound.lean`; statements are the design.
-/

namespace GoodsteinPA.PH.LB

open ONote

/-! ### §2.1–2.3  CNF data -/

/-- Number of CNF terms, `t`. -/
def tlen : ONote → ℕ
  | zero => 0
  | oadd _ _ a => tlen a + 1

/-- Buchholz's `r(α) = max{t, n₁,…,n_t, r(α₁),…,r(α_t)}` (recursing on the tail is harmless: the
tail's own `t` is one smaller). -/
def rnorm : ONote → ℕ
  | zero => 0
  | oadd e n a => max (tlen a + 1) (max (n : ℕ) (max (rnorm e) (rnorm a)))

/-- The `i`-th CNF term (0-based) as `(exponent, coefficient)`; `(0, 0)` past the end. -/
def termAt : ONote → ℕ → ONote × ℕ
  | zero, _ => (0, 0)
  | oadd e n _, 0 => (e, n)
  | oadd _ _ a, i + 1 => termAt a i

/-- `d(α, β)`, 0-based: the first index at which the CNF terms of `α` and `β` differ. -/
def dIdx : ONote → ONote → ℕ
  | oadd e n a, oadd e' n' a' => if e = e' ∧ n = n' then dIdx a a' + 1 else 0
  | _, _ => 0

/-- `K(α, β)`: the coefficient of `α` at the first difference. -/
def Kd (α β : ONote) : ℕ := (termAt α (dIdx α β)).2

/-- `E(α, β)`: the exponent of `α` at the first difference. -/
def Ed (α β : ONote) : ONote := (termAt α (dIdx α β)).1

/-- Buchholz's `ω_m(k)`: `ω_0(k) = k`, `ω_{m+1}(k) = ω^{ω_m(k)}`. -/
def wtow (m k : ℕ) : ONote := (fun a => oadd a 1 0)^[m] (ofNat k)

theorem wtow_succ (m k : ℕ) : wtow (m + 1) k = oadd (wtow m k) 1 0 := by
  simp only [wtow, Function.iterate_succ_apply']

theorem wtow_zero (k : ℕ) : wtow 0 k = ofNat k := rfl

theorem wtow_NF (m k : ℕ) : (wtow m k).NF := by
  induction m with
  | zero => rw [wtow_zero]; exact nf_ofNat k
  | succ m ih => rw [wtow_succ]; exact NF.oadd ih 1 NFBelow.zero

/-- One fundamental-sequence step `α ↦ α[x]` (`0[x] = 0`). -/
def fsStep (o : ONote) (x : ℕ) : ONote :=
  match fundamentalSequence o with
  | Sum.inl none => 0
  | Sum.inl (some a) => a
  | Sum.inr f => f x

theorem fsStep_NF {o : ONote} (ho : o.NF) (x : ℕ) : (fsStep o x).NF := by
  have hp := fundamentalSequence_has_prop o
  unfold fsStep
  rcases e : fundamentalSequence o with (_ | a) | f <;> rw [e] at hp
  · exact NF.zero
  · exact hp.2 ho
  · exact (hp.2.1 x).2.2 ho

theorem fsStep_lt {o : ONote} (ho : o.NF) (h0 : o ≠ 0) (x : ℕ) : fsStep o x < o := by
  have hp := fundamentalSequence_has_prop o
  unfold fsStep
  rcases e : fundamentalSequence o with (_ | a) | f <;> rw [e] at hp
  · exact absurd hp h0
  · rw [lt_def, hp.1]; exact Order.lt_succ _
  · exact (hp.2.1 x).2.1

/-! ### §2.2  Lemma 7.6 (norm growth along fundamental sequences) -/

theorem tlen_le_rnorm : ∀ α : ONote, tlen α ≤ rnorm α
  | zero => le_refl 0
  | oadd a m b => by simp only [tlen, rnorm]; omega

/-- **L7.6a** together with the `tlen` bookkeeping the induction needs -/
theorem fsStep_bounds : ∀ (α : ONote) (k : ℕ),
    rnorm (fsStep α k) ≤ max (rnorm α) k + 1 ∧ tlen (fsStep α k) ≤ tlen α + 1
  | zero, k => by simp [fsStep, fundamentalSequence, rnorm, tlen]
  | oadd a m b, k => by
    have hm1 : (m : ℕ) = m.natPred + 1 := (PNat.natPred_add_one m).symm
    have hra : rnorm (fsStep a k) ≤ max (rnorm a) k + 1 := (fsStep_bounds a k).1
    have ihb := fsStep_bounds b k
    have hnb : tlen b ≤ rnorm b := tlen_le_rnorm b
    rcases eb : fundamentalSequence b with (_ | b') | fb
    · rcases ea : fundamentalSequence a with (_ | a') | fa <;>
        rcases em : (m : ℕ+).natPred with _ | m' <;>
        simp_all only [fsStep, fundamentalSequence, rnorm, tlen, Nat.succPNat_coe,
          PNat.one_coe] <;>
        exact ⟨by omega, by omega⟩
    · simp_all only [fsStep, fundamentalSequence, rnorm, tlen]
      exact ⟨by omega, by omega⟩
    · simp_all only [fsStep, fundamentalSequence, rnorm, tlen]
      exact ⟨by omega, by omega⟩

/-- **L7.6a** (Buchholz gives no proof; the spec's reconstruction is by cases on the last term). -/
theorem rnorm_fsStep_le {o : ONote} (ho : o.NF) (x : ℕ) :
    rnorm (fsStep o x) ≤ max (rnorm o) x + 1 := (fsStep_bounds o x).1

/-- `r(ω_m(k)) ≤ max 1 k`. -/
theorem rnorm_ofNat : ∀ n : ℕ, rnorm (ofNat n) = n
  | 0 => rfl
  | n + 1 => by rw [ofNat_succ]; simp [rnorm, tlen, Nat.succPNat]

theorem rnorm_wtow_le (m k : ℕ) : rnorm (wtow m k) ≤ max 1 k := by
  induction m with
  | zero => rw [wtow_zero, rnorm_ofNat]; omega
  | succ m ih => rw [wtow_succ]; simp only [rnorm, tlen, PNat.one_coe]; omega

/-- **L7.6c**: `r(ω_m(k) + n) ≤ n + 1` for `1 ≤ m`, `k < n`. -/
theorem rnorm_wtow_add_le {m k n : ℕ} (hm : 1 ≤ m) (hkn : k < n) :
    rnorm (wtow m k + ofNat n) ≤ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hE := rnorm_wtow_le m k
  rw [wtow_succ, oadd_add, zero_add, ofNat_succ]
  rcases hw : wtow m k with _ | ⟨e, c, a⟩
  · have : ONote.cmp zero 0 = Ordering.eq := rfl
    simp only [addAux, this, rnorm, tlen, PNat.add_coe, PNat.one_coe, Nat.succPNat_coe]
    omega
  · rw [hw] at hE
    have : ONote.cmp (oadd e c a) 0 = Ordering.gt := rfl
    simp only [addAux, this]
    simp only [rnorm, tlen, PNat.one_coe, Nat.succPNat_coe] at hE ⊢
    omega

/-! ### §2.4–2.6  Lemma 7.7, the 3-colouring `χ`, Lemma 7.8 -/

/-! #### Helpers for `d/K/E` -/

theorem termAt_fst_lt : ∀ {a : ONote} {b : Ordinal} (i : ℕ), NFBelow a b → i < tlen a →
    ONote.repr (termAt a i).1 < b
  | zero, _, _, _, h => by simp [tlen] at h
  | oadd e n a, b, 0, h, _ => h.lt
  | oadd e n a, b, i + 1, h, hi => by
    simp only [termAt]
    simp only [tlen] at hi
    exact (termAt_fst_lt i h.snd (by omega)).trans h.lt

theorem termAt_snd_pos : ∀ {a : ONote} (i : ℕ), i < tlen a → 1 ≤ (termAt a i).2
  | zero, _, h => by simp [tlen] at h
  | oadd e n a, 0, _ => n.pos
  | oadd e n a, i + 1, hi => by
    simp only [termAt]; simp only [tlen] at hi; exact termAt_snd_pos i (by omega)

theorem termAt_snd_le_rnorm : ∀ (a : ONote) (i : ℕ), (termAt a i).2 ≤ rnorm a
  | zero, _ => by simp [termAt]
  | oadd e n a, 0 => by simp only [termAt, rnorm]; omega
  | oadd e n a, i + 1 => by
    have := termAt_snd_le_rnorm a i
    simp only [termAt, rnorm]; omega

theorem rnorm_termAt_fst_le : ∀ (a : ONote) (i : ℕ), rnorm (termAt a i).1 ≤ rnorm a
  | zero, _ => by simp [termAt, rnorm]
  | oadd e n a, 0 => by simp only [termAt, rnorm]; omega
  | oadd e n a, i + 1 => by
    have := rnorm_termAt_fst_le a i
    simp only [termAt, rnorm]; omega

theorem not_lt_zero' (β : ONote) : ¬ β < 0 := by
  rw [lt_def]; simp

theorem lt_of_oadd_lt_oadd {e a b : ONote} {m : ℕ+} (h : oadd e m b < oadd e m a) : b < a := by
  rw [lt_def] at h ⊢
  simp only [ONote.repr] at h
  exact (add_lt_add_iff_left _).1 h

/-- Comparison of two NF `oadd`s, read off lexicographically. -/
theorem oadd_lt_cases {e e' a b : ONote} {n n' : ℕ+} (hα : (oadd e n a).NF)
    (hβ : (oadd e' n' b).NF) (h : oadd e' n' b < oadd e n a) :
    e' < e ∨ (e' = e ∧ (n' : ℕ) < n) ∨ (e' = e ∧ n' = n ∧ b < a) := by
  haveI := hα.fst; haveI := hβ.fst
  rcases lt_trichotomy (ONote.repr e') (ONote.repr e) with h1 | h1 | h1
  · exact Or.inl h1
  · have hee : e' = e := repr_inj.1 h1
    subst hee
    rcases lt_trichotomy (n' : ℕ) n with h2 | h2 | h2
    · exact Or.inr (Or.inl ⟨rfl, h2⟩)
    · have hnn : n' = n := PNat.coe_inj.1 h2
      subst hnn
      exact Or.inr (Or.inr ⟨rfl, rfl, lt_of_oadd_lt_oadd h⟩)
    · exact absurd h (lt_asymm (oadd_lt_oadd_2 hα h2))
  · exact absurd h (lt_asymm (oadd_lt_oadd_1 hα h1))

theorem dIdx_lt_tlen : ∀ {α β : ONote}, α.NF → β.NF → β < α → dIdx α β < tlen α
  | zero, β, _, _, h => absurd h (not_lt_zero' β)
  | oadd e n a, zero, _, _, _ => by simp [dIdx, tlen]
  | oadd e n a, oadd e' n' b, hα, hβ, h => by
    simp only [dIdx, tlen]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      have := dIdx_lt_tlen hα.snd hβ.snd (lt_of_oadd_lt_oadd h)
      omega
    · omega

theorem Kd_pos {α β : ONote} (hα : α.NF) (hβ : β.NF) (h : β < α) : 1 ≤ Kd α β :=
  termAt_snd_pos _ (dIdx_lt_tlen hα hβ h)

theorem Kd_le_rnorm (α β : ONote) : Kd α β ≤ rnorm α := termAt_snd_le_rnorm _ _

theorem dIdx_oadd_ne {e e' a b : ONote} {n n' : ℕ+} (h : ¬ (e = e' ∧ n = n')) :
    dIdx (oadd e n a) (oadd e' n' b) = 0 := by simp [dIdx, h]

/-- **L7.7.** -/
theorem Ed_lt_Ed {α β γ : ONote} (hα : α.NF) (hβ : β.NF) (hγ : γ.NF) (hαβ : β < α) (hβγ : γ < β)
    (hd : dIdx α β ≤ dIdx β γ) (hK : Kd α β ≤ Kd β γ) : Ed β γ < Ed α β := by
  induction α generalizing β γ with
  | zero => exact absurd hαβ (not_lt_zero' β)
  | oadd e n a _ iha =>
    rcases β with _ | ⟨e', n', b⟩
    · exact absurd hβγ (not_lt_zero' γ)
    by_cases hc : e = e' ∧ n = n'
    · obtain ⟨rfl, rfl⟩ := hc
      rcases γ with _ | ⟨e'', n'', c⟩
      · simp [dIdx] at hd
      by_cases hc' : e = e'' ∧ n = n''
      · obtain ⟨rfl, rfl⟩ := hc'
        simp only [dIdx, Kd, Ed, termAt, and_self, if_true] at hd hK ⊢
        exact iha hα.snd hβ.snd hγ.snd (lt_of_oadd_lt_oadd hαβ) (lt_of_oadd_lt_oadd hβγ)
          (by simpa [dIdx] using hd) hK
      · simp [dIdx, hc'] at hd
    · have hd0 : dIdx (oadd e n a) (oadd e' n' b) = 0 := dIdx_oadd_ne hc
      have hEa : Ed (oadd e n a) (oadd e' n' b) = e := by simp [Ed, hd0, termAt]
      have hKa : Kd (oadd e n a) (oadd e' n' b) = n := by simp [Kd, hd0, termAt]
      rw [hEa]; rw [hKa] at hK
      -- `Ed β γ` is either `e'` (first difference at 0) or a tail exponent `< e'`
      have hcase := oadd_lt_cases hα hβ hαβ
      have key : Ed (oadd e' n' b) γ = e' ∧ Kd (oadd e' n' b) γ = n' ∨
          ONote.repr (Ed (oadd e' n' b) γ) < ONote.repr e' := by
        rcases γ with _ | ⟨e'', n'', c⟩
        · exact Or.inl ⟨rfl, rfl⟩
        by_cases hc' : e' = e'' ∧ n' = n''
        · obtain ⟨rfl, rfl⟩ := hc'
          right
          simp only [Ed, dIdx, and_self, if_true, termAt]
          exact termAt_fst_lt _ hβ.snd' (dIdx_lt_tlen hβ.snd hγ.snd (lt_of_oadd_lt_oadd hβγ))
        · left
          simp [Ed, Kd, dIdx_oadd_ne hc', termAt]
      rcases key with ⟨hE, hK'⟩ | hlt
      · rw [hE]; rw [hK'] at hK
        rcases hcase with h1 | ⟨rfl, h2⟩ | ⟨rfl, rfl, _⟩
        · exact h1
        · omega
        · exact absurd ⟨rfl, rfl⟩ hc
      · show ONote.repr _ < ONote.repr e
        rcases hcase with h1 | ⟨rfl, _⟩ | ⟨rfl, _, _⟩
        · exact hlt.trans h1
        · exact hlt
        · exact hlt

/-- The 3-colouring `χ` of decreasing triples: `0̂ = 0`, `1̂ = 1`, `2̂ = 2`. -/
def chi3 (b₀ b₁ b₂ : ONote) : ℕ :=
  if dIdx b₁ b₂ < dIdx b₀ b₁ then 0 else if Kd b₁ b₂ < Kd b₀ b₁ then 1 else 2

/-- A decreasing NF chain `β 0 > … > β ℓ`. -/
def Chain (β : ℕ → ONote) (ℓ : ℕ) : Prop :=
  (∀ i ≤ ℓ, (β i).NF) ∧ ∀ i < ℓ, β (i + 1) < β i

/-- **L7.8a**: a chain on which `χ` is constantly `0̂` or `1̂` has length `ℓ ≤ r(β₀)`. -/
theorem chain_len_le_rnorm {β : ℕ → ONote} {ℓ c : ℕ} (hβ : Chain β ℓ) (hℓ : 2 ≤ ℓ) (hc : c < 2)
    (hχ : ∀ i, i + 2 ≤ ℓ → chi3 (β i) (β (i + 1)) (β (i + 2)) = c) : ℓ ≤ rnorm (β 0) := by
  obtain ⟨hNF, hlt⟩ := hβ
  have hd : ∀ i < ℓ, dIdx (β i) (β (i + 1)) < tlen (β i) := fun i hi =>
    dIdx_lt_tlen (hNF i (by omega)) (hNF (i + 1) (by omega)) (hlt i hi)
  have hk : ∀ i < ℓ, 1 ≤ Kd (β i) (β (i + 1)) := fun i hi =>
    Kd_pos (hNF i (by omega)) (hNF (i + 1) (by omega)) (hlt i hi)
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · -- colour `0̂`: the `d`'s strictly decrease
    have hstep : ∀ i, i + 2 ≤ ℓ → dIdx (β (i + 1)) (β (i + 1 + 1)) < dIdx (β i) (β (i + 1)) := by
      intro i hi
      have := hχ i hi
      unfold chi3 at this
      split_ifs at this with h1 h2 <;> first | exact h1 | omega
    have hacc : ∀ i, i + 1 ≤ ℓ → dIdx (β i) (β (i + 1)) + i ≤ dIdx (β 0) (β 1) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih => intro hi; have := hstep i (by omega); have := ih (by omega); omega
    have h1 := hacc (ℓ - 1) (by omega)
    have h2 : dIdx (β 0) (β 1) < tlen (β 0) := hd 0 (by omega)
    have h3 := tlen_le_rnorm (β 0)
    omega
  · -- colour `1̂`: the `K`'s strictly decrease
    have hstep : ∀ i, i + 2 ≤ ℓ → Kd (β (i + 1)) (β (i + 1 + 1)) < Kd (β i) (β (i + 1)) := by
      intro i hi
      have := hχ i hi
      unfold chi3 at this
      split_ifs at this with h1 h2 <;> first | exact h2 | omega
    have hacc : ∀ i, i + 1 ≤ ℓ → Kd (β i) (β (i + 1)) + i ≤ Kd (β 0) (β 1) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih => intro hi; have := hstep i (by omega); have := ih (by omega); omega
    have h1 := hacc (ℓ - 1) (by omega)
    have h2 := hk (ℓ - 1) (by omega)
    have h3 := Kd_le_rnorm (β 0) (β 1)
    omega

/-- **L7.8b**: on a `2̂`-chain the exponents `E(βᵢ, βᵢ₊₁)` descend. -/
theorem chain_Ed_desc {β : ℕ → ONote} {ℓ : ℕ} (hβ : Chain β ℓ)
    (hχ : ∀ i, i + 2 ≤ ℓ → chi3 (β i) (β (i + 1)) (β (i + 2)) = 2) :
    ∀ i, i + 2 ≤ ℓ → Ed (β (i + 1)) (β (i + 2)) < Ed (β i) (β (i + 1)) := by
  intro i hi
  obtain ⟨hNF, hlt⟩ := hβ
  have := hχ i hi
  unfold chi3 at this
  split_ifs at this with h1 h2 <;> try omega
  exact Ed_lt_Ed (hNF i (by omega)) (hNF (i + 1) (by omega)) (hNF (i + 2) (by omega))
    (hlt i (by omega)) (hlt (i + 1) (by omega)) (not_lt.1 h1) (not_lt.1 h2)

/-- `r(E(α, β)) ≤ r(α)`: the exponent is one of `α`'s CNF exponents. -/
theorem rnorm_Ed_le (α β : ONote) : rnorm (Ed α β) ≤ rnorm α := rnorm_termAt_fst_le _ _

end GoodsteinPA.PH.LB

end
