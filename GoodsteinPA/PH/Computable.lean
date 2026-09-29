/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.Statement
public import GoodsteinPA.ToMathlib.Goodstein.Computability
public import Mathlib.Combinatorics.Colex
public import Foundation.FirstOrder.Arithmetic.R0.Representation

@[expose] public section

/-!
# The Paris–Harrington property is primitive recursive

`PH e r k N` quantifies over colourings of, and subsets of, `{1, …, N}`.  Encoding a subset by its
bitmask and a colouring by the base-`r` digits of a single number (digit `t` is the colour of the
subset with bitmask `t`) turns it into a formula with bounded quantifiers only (`PHbits`), which
Mathlib's `PrimrecRel.forall_lt` / `exists_lt` machinery handles.
-/

namespace GoodsteinPA.PH

open Finset

/-! ### Bitmasks -/

/-- The finite set of bit positions of `n`. -/
def bits (n : ℕ) : Finset ℕ := n.bitIndices.toFinset

/-- The bitmask of a finite set of naturals. -/
def code (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i

@[simp] theorem mem_bits {n i : ℕ} : i ∈ bits n ↔ n.testBit i = true := by
  simp [bits]

@[simp] theorem bits_code (s : Finset ℕ) : bits (code s) = s :=
  Finset.toFinset_bitIndices_sum_two_pow s

@[simp] theorem code_bits (n : ℕ) : code (bits n) = n :=
  Finset.sum_toFinset_bitIndices_two_pow n

theorem lt_two_pow_iff {n B : ℕ} : n < 2 ^ B ↔ ∀ i ∈ bits n, i < B := by
  constructor
  · intro h i hi
    by_contra hc
    have h1 : 2 ^ B ≤ 2 ^ i := Nat.pow_le_pow_right (Nat.succ_pos 1) (not_lt.mp hc)
    have h2 : 2 ^ i ≤ n := Nat.two_pow_le_of_mem_bitIndices (by simpa [bits] using hi)
    omega
  · intro h
    rw [← code_bits n]
    show ∑ i ∈ bits n, 2 ^ i < 2 ^ B
    calc ∑ i ∈ bits n, 2 ^ i ≤ ∑ i ∈ range B, 2 ^ i :=
          sum_le_sum_of_subset (fun i hi => mem_range.mpr (h i hi))
      _ < 2 ^ B := by
          have h1 := Nat.geomSum_eq (le_refl 2) B
          have h2 : 0 < 2 ^ B := Nat.two_pow_pos B
          simp at h1
          omega

theorem code_lt_two_pow {s : Finset ℕ} {B : ℕ} (h : ∀ i ∈ s, i < B) : code s < 2 ^ B :=
  lt_two_pow_iff.mpr (by simpa using h)

/-- A mask `h` codes a subset of `Icc 1 N` exactly when it is below `2 ^ (N+1)` with bit `0` clear. -/
theorem bits_subset_Icc {n N : ℕ} :
    bits n ⊆ Icc 1 N ↔ n < 2 ^ (N + 1) ∧ n.testBit 0 = false := by
  constructor
  · intro h
    refine ⟨lt_two_pow_iff.mpr fun i hi => ?_, ?_⟩
    · have := h hi; simp only [mem_Icc] at this; omega
    · by_contra hc
      have := h (mem_bits.mpr (Bool.not_eq_false _ |>.mp hc))
      simp at this
  · rintro ⟨h1, h0⟩ i hi
    have hlt := lt_two_pow_iff.mp h1 i hi
    simp only [mem_Icc]
    refine ⟨?_, by omega⟩
    rcases Nat.eq_zero_or_pos i with rfl | hp
    · rw [mem_bits, h0] at hi; simp at hi
    · exact hp

/-! ### Bit tests and population count, arithmetically -/

/-- Bit `i` of `n` is set, spelled with division so that primitive recursiveness is immediate. -/
def bit1 (n i : ℕ) : Prop := n / 2 ^ i % 2 = 1

instance (n i : ℕ) : Decidable (bit1 n i) := by unfold bit1; infer_instance

theorem bit1_iff {n i : ℕ} : bit1 n i ↔ n.testBit i = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp [bit1]

theorem not_bit1_iff {n i : ℕ} : ¬ bit1 n i ↔ n.testBit i = false := by
  rw [bit1_iff]; simp

/-- Population count of the bottom `B` bits. -/
def popL (B n : ℕ) : ℕ := ((List.range B).filter (fun j => decide (bit1 n j))).length

theorem popL_eq_card_filter (B n : ℕ) :
    popL B n = ((range B).filter (fun j => n.testBit j = true)).card := by
  induction B with
  | zero => simp [popL]
  | succ B ih =>
    rw [popL, List.range_succ, List.filter_append, List.length_append, ← popL, ih,
      Finset.range_add_one, Finset.filter_insert]
    by_cases h : n.testBit B = true
    · simp [h, ← bit1_iff, bit1_iff.mpr h]
    · simp [bit1_iff, h]

theorem popL_eq_card {B n : ℕ} (h : n < 2 ^ B) : popL B n = (bits n).card := by
  rw [popL_eq_card_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range, mem_bits]
  exact ⟨fun hi => hi.2, fun hi => ⟨lt_two_pow_iff.mp h i (mem_bits.mpr hi), hi⟩⟩

/-! ### Base-`r` digit packing -/

/-- Pack a list of base-`r` digits (least significant first). -/
def pack (r : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + r * pack r ds

theorem digit_pack {r : ℕ} (hr : 0 < r) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < r) → ∀ t, pack r ds / r ^ t % r = ds.getD t 0
  | [], _, t => by simp [pack]
  | d :: ds, hd, 0 => by
    simp only [pack, pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd d (by simp))]
  | d :: ds, hd, t + 1 => by
    simp only [pack, List.getD_cons_succ]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hr,
      Nat.div_eq_of_lt (hd d (by simp)), zero_add]
    exact digit_pack hr ds (fun x hx => hd x (by simp [hx])) t

theorem pack_lt {r : ℕ} (hr : 0 < r) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < r) → pack r ds < r ^ ds.length
  | [], _ => by simp [pack]
  | d :: ds, hd => by
    have ih := pack_lt hr ds (fun x hx => hd x (by simp [hx]))
    have hd0 := hd d (by simp)
    simp only [pack, List.length_cons, pow_succ']
    have hstep : r * (pack r ds + 1) ≤ r * r ^ ds.length :=
      Nat.mul_le_mul (Nat.le_refl r) (by omega)
    have heq : r * (pack r ds + 1) = r * pack r ds + r := Nat.mul_succ r _
    omega

/-! ### The bounded form of `PH` -/

/-- The colour that the packed colouring `C` assigns to the subset with bitmask `t`. -/
def Colour (r C t : ℕ) : ℕ := C / r ^ t % r

/-- `t`'s bits (below `B`) are among `h`'s. -/
def SubMask (B t h : ℕ) : Prop := ∀ j < B, bit1 t j → bit1 h j

instance (B t h : ℕ) : Decidable (SubMask B t h) := by unfold SubMask; infer_instance

/-- Bounded form of `Homog`. -/
def HomogBits (e r N C h : ℕ) : Prop :=
  ∃ i < r, ∀ t < 2 ^ (N + 1), SubMask (N + 1) t h → popL (N + 1) t = e → Colour r C t = i

instance (e r N C h : ℕ) : Decidable (HomogBits e r N C h) := by unfold HomogBits; infer_instance

/-- Bounded form of `RelLarge`. -/
def RelLargeBits (N h : ℕ) : Prop :=
  ∀ a < N + 1, bit1 h a → (∀ b < a, ¬ bit1 h b) → a ≤ popL (N + 1) h

instance (N h : ℕ) : Decidable (RelLargeBits N h) := by unfold RelLargeBits; infer_instance

/-- **The Paris–Harrington property in bounded-quantifier form.** -/
def PHbits (e r k N : ℕ) : Prop :=
  (r = 0 ∧ e ≤ N) ∨
  (0 < r ∧ ∀ C < r ^ 2 ^ (N + 1), ∃ h < 2 ^ (N + 1), ¬ bit1 h 0 ∧ k ≤ popL (N + 1) h ∧
    RelLargeBits N h ∧ HomogBits e r N C h)

instance (e r k N : ℕ) : Decidable (PHbits e r k N) := by unfold PHbits; infer_instance

/-! ### `PHbits` and `PH` agree -/

theorem card_Icc_one (N : ℕ) : (Icc 1 N).card = N := by rw [Nat.card_Icc]; omega

theorem ph_zero (e k N : ℕ) : PH e 0 k N ↔ e ≤ N := by
  constructor
  · intro h
    by_contra hc
    have hempty : ∀ x, x ∉ (Icc 1 N).powersetCard e :=
      Finset.eq_empty_iff_forall_notMem.mp
        (Finset.powersetCard_eq_empty.mpr (by rw [card_Icc_one]; omega))
    obtain ⟨H, -, -, -, i, -⟩ := h (fun s => absurd s.2 (hempty s.1))
    exact i.elim0
  · intro he c
    obtain ⟨t, hts, htc⟩ :=
      Finset.exists_subset_card_eq (s := Icc 1 N) (n := e) (by rw [card_Icc_one]; exact he)
    exact absurd (c ⟨t, Finset.mem_powersetCard.mpr ⟨hts, htc⟩⟩).elim0 (fun h => h)

theorem mem_powerset_bits {h N : ℕ} (hlt : h < 2 ^ (N + 1)) (h0 : ¬ bit1 h 0) :
    bits h ∈ (Icc 1 N).powerset :=
  Finset.mem_powerset.mpr (bits_subset_Icc.mpr ⟨hlt, not_bit1_iff.mp h0⟩)

theorem code_mem_bound {s : Finset ℕ} {N : ℕ} (hs : s ⊆ Icc 1 N) : code s < 2 ^ (N + 1) :=
  code_lt_two_pow fun i hi => by have := hs hi; simp only [mem_Icc] at this; omega

theorem PHbits_iff (e r k N : ℕ) : PHbits e r k N ↔ PH e r k N := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [PHbits, ph_zero, lt_irrefl, false_and, or_false, true_and]
  · constructor
    · -- `PHbits → PH`
      rintro (⟨h0, -⟩ | ⟨-, hb⟩)
      · omega
      intro c
      set f : ℕ → ℕ := fun t =>
        if hs : bits t ∈ (Icc 1 N).powersetCard e then (c ⟨bits t, hs⟩ : ℕ) else 0 with hf
      set ds : List ℕ := (List.range (2 ^ (N + 1))).map f with hds
      have hdlt : ∀ d ∈ ds, d < r := by
        intro d hd
        simp only [hds, List.mem_map] at hd
        obtain ⟨t, -, rfl⟩ := hd
        simp only [hf]
        split
        · exact (c _).isLt
        · exact hr
      have hlen : ds.length = 2 ^ (N + 1) := by simp [hds]
      set C := pack r ds with hC
      have hCb : C < r ^ 2 ^ (N + 1) := by rw [hC, ← hlen]; exact pack_lt hr ds hdlt
      have hdig : ∀ t < 2 ^ (N + 1), Colour r C t = f t := by
        intro t ht
        rw [Colour, hC, digit_pack hr ds hdlt t, hds,
          List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
        rfl
      obtain ⟨h, hhlt, hh0, hhk, hhrl, i₀, hi₀r, hhom⟩ := hb C hCb
      refine ⟨bits h, mem_powerset_bits hhlt hh0, ?_, ?_, ⟨i₀, hi₀r⟩, ?_⟩
      · rwa [← popL_eq_card hhlt]
      · intro a ha hmin
        rw [← popL_eq_card hhlt]
        refine hhrl a ?_ (bit1_iff.mpr (mem_bits.mp ha)) ?_
        · have := (bits_subset_Icc.mpr ⟨hhlt, not_bit1_iff.mp hh0⟩) ha
          simp only [mem_Icc] at this; omega
        · intro b hb' hbb
          exact absurd (hmin b (mem_bits.mpr (bit1_iff.mp hbb))) (by omega)
      · intro s hs hsub
        have hsIcc : s ⊆ Icc 1 N := (Finset.mem_powersetCard.mp hs).1
        have ht : code s < 2 ^ (N + 1) := code_mem_bound hsIcc
        have hsm : SubMask (N + 1) (code s) h := by
          intro j _ hj
          exact bit1_iff.mpr (mem_bits.mp (hsub (by simpa using mem_bits.mpr (bit1_iff.mp hj))))
        have hpop : popL (N + 1) (code s) = e := by
          rw [popL_eq_card ht, bits_code]; exact (Finset.mem_powersetCard.mp hs).2
        have := hhom (code s) ht hsm hpop
        rw [hdig _ ht, hf] at this
        simp only [bits_code, dif_pos hs] at this
        exact Fin.ext this
    · -- `PH → PHbits`
      intro hph
      refine Or.inr ⟨hr, fun C hCb => ?_⟩
      obtain ⟨H, hHp, hHk, hHrl, i, hi⟩ :=
        hph fun s => ⟨Colour r C (code s.1), Nat.mod_lt _ hr⟩
      have hHIcc : H ⊆ Icc 1 N := Finset.mem_powerset.mp hHp
      have hh : code H < 2 ^ (N + 1) := code_mem_bound hHIcc
      have hbc : bits (code H) = H := bits_code H
      refine ⟨code H, hh, ?_, ?_, ?_, i.1, i.2, ?_⟩
      · rw [not_bit1_iff]
        exact ((bits_subset_Icc (N := N)).mp (by rw [hbc]; exact hHIcc)).2
      · rw [popL_eq_card hh, hbc]; exact hHk
      · intro a ha hba hmin
        rw [popL_eq_card hh, hbc]
        refine hHrl a (by rw [← hbc]; exact mem_bits.mpr (bit1_iff.mp hba)) ?_
        intro b hb
        by_contra hab
        exact hmin b (by omega) (bit1_iff.mpr (by rw [← hbc] at hb; exact mem_bits.mp hb))
      · intro t htlt hsm hpop
        have htb : bits t ⊆ Icc 1 N := by
          intro j hj
          have hjB := lt_two_pow_iff.mp htlt j hj
          have : bit1 (code H) j := hsm j hjB (bit1_iff.mpr (mem_bits.mp hj))
          exact hHIcc (by rw [← hbc]; exact mem_bits.mpr (bit1_iff.mp this))
        have hsub : bits t ⊆ H := by
          intro j hj
          have hjB := lt_two_pow_iff.mp htlt j hj
          have : bit1 (code H) j := hsm j hjB (bit1_iff.mpr (mem_bits.mp hj))
          rw [← hbc]; exact mem_bits.mpr (bit1_iff.mp this)
        have hmem : bits t ∈ (Icc 1 N).powersetCard e :=
          Finset.mem_powersetCard.mpr ⟨htb, by rw [← popL_eq_card htlt]; exact hpop⟩
        have := hi (bits t) hmem hsub
        have h2 : Colour r C (code (bits t)) = i.1 := by
          rw [← Fin.val_eq_val] at this; simpa using this
        rwa [code_bits] at h2

/-! ### Bounded quantifiers with a parameter -/

section Bounded
open Primrec

/-- `PrimrecRel.forall_lt` with an arbitrary parameter type. -/
theorem forall_ltb {β : Type*} [Primcodable β] {R : ℕ → β → Prop} (hR : PrimrecRel R) :
    PrimrecRel fun (n : ℕ) (b : β) => ∀ x < n, R x b :=
  (hR.forall_mem_list.comp (Primrec.list_range.comp Primrec.fst) Primrec.snd).of_eq (by simp)

/-- `PrimrecRel.exists_lt` with an arbitrary parameter type. -/
theorem exists_ltb {β : Type*} [Primcodable β] {R : ℕ → β → Prop} (hR : PrimrecRel R) :
    PrimrecRel fun (n : ℕ) (b : β) => ∃ x < n, R x b :=
  (hR.exists_mem_list.comp (Primrec.list_range.comp Primrec.fst) Primrec.snd).of_eq (by simp)

/-- A bounded universal quantifier whose bound and parameter are primitive recursive. -/
theorem bAll {α β : Type*} [Primcodable α] [Primcodable β] {bd : α → ℕ} {g : α → β}
    {R : ℕ → β → Prop} (hbd : Primrec bd) (hg : Primrec g) (hR : PrimrecRel R) :
    PrimrecPred fun a => ∀ x < bd a, R x (g a) := (forall_ltb hR).comp hbd hg

/-- A bounded existential quantifier whose bound and parameter are primitive recursive. -/
theorem bEx {α β : Type*} [Primcodable α] [Primcodable β] {bd : α → ℕ} {g : α → β}
    {R : ℕ → β → Prop} (hbd : Primrec bd) (hg : Primrec g) (hR : PrimrecRel R) :
    PrimrecPred fun a => ∃ x < bd a, R x (g a) := (exists_ltb hR).comp hbd hg

end Bounded

/-! ### `PHbits` is primitive recursive -/

section Primrec
open Primrec

/-- `bit1` is a primitive recursive relation. -/
theorem primrecRel_bit1 : PrimrecRel bit1 :=
  Primrec.eq.comp (Primrec.nat_mod.comp
    (Primrec.nat_div.comp Primrec.fst (Goodstein.primrec_natPow.comp (Primrec.const 2) Primrec.snd))
    (const 2)) (const 1)

theorem primrec_popL : Primrec₂ popL := by
  have hR : PrimrecRel fun (j : ℕ) (q : ℕ × ℕ) => bit1 q.2 j :=
    primrecRel_bit1.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  have := Primrec.list_length.comp
    (PrimrecRel.listFilter hR |>.comp (Primrec.list_range.comp Primrec.fst) Primrec.id)
  exact this.to₂.of_eq fun B n => rfl

theorem primrec_pow2 : Primrec fun N : ℕ => 2 ^ (N + 1) :=
  Goodstein.primrec_natPow.comp (Primrec.const 2) Primrec.succ

end Primrec

/-- Implication of primitive recursive predicates. -/
theorem prImp {α : Type*} [Primcodable α] {p q : α → Prop} (hp : PrimrecPred p)
    (hq : PrimrecPred q) : PrimrecPred fun a => p a → q a :=
  (hp.not.or hq).of_eq fun a => by
    constructor
    · rintro (h | h) hp'; exact absurd hp' h; exact h
    · intro h; by_cases hp' : p a
      · exact Or.inr (h hp')
      · exact Or.inl hp'

theorem primrecRel_SubMask : PrimrecRel fun (B : ℕ) (q : ℕ × ℕ) => SubMask B q.1 q.2 := by
  have h1 : PrimrecPred fun z : ℕ × (ℕ × ℕ) => bit1 z.2.1 z.1 :=
    primrecRel_bit1.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have h2 : PrimrecPred fun z : ℕ × (ℕ × ℕ) => bit1 z.2.2 z.1 :=
    primrecRel_bit1.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  exact (forall_ltb (R := fun (n : ℕ) (b : ℕ × ℕ) => bit1 b.1 n → bit1 b.2 n)
    (prImp h1 h2)).of_eq fun B q => Iff.rfl

/-- The innermost layer of `HomogBits`: `q = (C, h, i, e, r, k, N)`. -/
theorem primrecRel_homogBody :
    PrimrecRel fun (t : ℕ) (q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
      SubMask (q.2.2.2.2.2.2 + 1) t q.2.1 → popL (q.2.2.2.2.2.2 + 1) t = q.2.2.2.1 →
        Colour q.2.2.2.2.1 q.1 t = q.2.2.1 := by
  have hN : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.2.2.2.2.2 + 1 :=
    Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
  have ht : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.1 := Primrec.fst
  have hh : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hr : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.snd))))
  have hC : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hi : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have c1 : PrimrecPred fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      SubMask (z.2.2.2.2.2.2.2 + 1) z.1 z.2.2.1 :=
    primrecRel_SubMask.comp hN (ht.pair hh)
  have c2 : PrimrecPred fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      popL (z.2.2.2.2.2.2.2 + 1) z.1 = z.2.2.2.2.1 :=
    Primrec.eq.comp (primrec_popL.comp hN ht) he
  have c3 : PrimrecPred fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      Colour z.2.2.2.2.2.1 z.2.1 z.1 = z.2.2.2.1 :=
    Primrec.eq.comp (Primrec.nat_mod.comp
      (Primrec.nat_div.comp hC (Goodstein.primrec_natPow.comp hr ht)) hr) hi
  exact prImp c1 (prImp c2 c3)

/-- `HomogBits` is primitive recursive.  `q = (C, h, e, r, k, N)`. -/
theorem primrecPred_homogBits :
    PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      HomogBits q.2.2.1 q.2.2.2.1 q.2.2.2.2.2 q.1 q.2.1 := by
  -- the body, with `i` as the bound variable: `z = (i, C, h, e, r, k, N)`
  have hbody : PrimrecRel fun (i : ℕ) (q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) =>
      ∀ t < 2 ^ (q.2.2.2.2.2 + 1),
        SubMask (q.2.2.2.2.2 + 1) t q.2.1 → popL (q.2.2.2.2.2 + 1) t = q.2.2.1 →
          Colour q.2.2.2.1 q.1 t = i := by
    refine bAll (bd := fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => 2 ^ (z.2.2.2.2.2.2 + 1))
      (g := fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => (z.2.1, z.2.2.1, z.1, z.2.2.2.1, z.2.2.2.2.1,
        z.2.2.2.2.2.1, z.2.2.2.2.2.2)) ?_ ?_ primrecRel_homogBody
    · exact Goodstein.primrec_natPow.comp (Primrec.const 2) (Primrec.succ.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
    · exact (Primrec.fst.comp Primrec.snd).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
          (Primrec.fst.pair
            ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
              ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                Primrec.snd)))).pair
                ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                  (Primrec.snd.comp Primrec.snd))))).pair
                  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
                    (Primrec.snd.comp Primrec.snd))))))))))
  refine (bEx (bd := fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.1)
    (g := fun q : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => q) ?_ Primrec.id hbody).of_eq fun q => Iff.rfl
  exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

/-- `RelLargeBits` is primitive recursive. -/
theorem primrecRel_relLargeBits : PrimrecRel fun (N h : ℕ) => RelLargeBits N h := by
  have hinner : PrimrecRel fun (a : ℕ) (h : ℕ) => ∀ b < a, ¬ bit1 h b :=
    forall_ltb (R := fun (b : ℕ) (h : ℕ) => ¬ bit1 h b)
      (primrecRel_bit1.comp Primrec.snd Primrec.fst).not
  have hbody : PrimrecRel fun (a : ℕ) (w : ℕ × ℕ) =>
      bit1 w.2 a → (∀ b < a, ¬ bit1 w.2 b) → a ≤ popL (w.1 + 1) w.2 := by
    have c1 : PrimrecPred fun z : ℕ × ℕ × ℕ => bit1 z.2.2 z.1 :=
      primrecRel_bit1.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
    have c2 : PrimrecPred fun z : ℕ × ℕ × ℕ => ∀ b < z.1, ¬ bit1 z.2.2 b :=
      hinner.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
    have c3 : PrimrecPred fun z : ℕ × ℕ × ℕ => z.1 ≤ popL (z.2.1 + 1) z.2.2 :=
      Primrec.nat_le.comp Primrec.fst (primrec_popL.comp
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
    exact prImp c1 (prImp c2 c3)
  have hmain := bAll (bd := fun w : ℕ × ℕ => w.1 + 1) (g := fun w : ℕ × ℕ => w)
    (Primrec.succ.comp Primrec.fst) Primrec.id hbody
  exact hmain.of_eq fun w => Iff.rfl

/-- The witness layer of `PHbits`: `q = (C, e, r, k, N)`, bound variable the mask `h`. -/
theorem primrecRel_witness : PrimrecRel fun (h : ℕ) (q : ℕ × ℕ × ℕ × ℕ × ℕ) =>
    ¬ bit1 h 0 ∧ q.2.2.2.1 ≤ popL (q.2.2.2.2 + 1) h ∧ RelLargeBits q.2.2.2.2 h ∧
      HomogBits q.2.1 q.2.2.1 q.2.2.2.2 q.1 h := by
  -- `z = (h, C, e, r, k, N)`
  have hh : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.1 := Primrec.fst
  have hC : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.1 := Primrec.fst.comp Primrec.snd
  have he : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hk : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hN : Primrec fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => z.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have c1 : PrimrecPred fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => ¬ bit1 z.1 0 :=
    (primrecRel_bit1.comp hh (Primrec.const 0)).not
  have c2 : PrimrecPred fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      z.2.2.2.2.1 ≤ popL (z.2.2.2.2.2 + 1) z.1 :=
    Primrec.nat_le.comp hk (primrec_popL.comp (Primrec.succ.comp hN) hh)
  have c3 : PrimrecPred fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => RelLargeBits z.2.2.2.2.2 z.1 :=
    primrecRel_relLargeBits.comp hN hh
  have c4 : PrimrecPred fun z : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      HomogBits z.2.2.1 z.2.2.2.1 z.2.2.2.2.2 z.2.1 z.1 :=
    primrecPred_homogBits.comp
      (hC.pair (hh.pair (he.pair (hr.pair (hk.pair hN)))))
  exact c1.and (c2.and (c3.and c4))

/-- **`PHbits` is primitive recursive.** -/
theorem primrecPred_PHbits :
    PrimrecPred fun p : ℕ × ℕ × ℕ × ℕ => PHbits p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hA0 : PrimrecPred fun q : ℕ × ℕ × ℕ × ℕ × ℕ =>
      ∃ h < 2 ^ (q.2.2.2.2 + 1), ¬ bit1 h 0 ∧ q.2.2.2.1 ≤ popL (q.2.2.2.2 + 1) h ∧
        RelLargeBits q.2.2.2.2 h ∧ HomogBits q.2.1 q.2.2.1 q.2.2.2.2 q.1 h :=
    bEx (bd := fun q : ℕ × ℕ × ℕ × ℕ × ℕ => 2 ^ (q.2.2.2.2 + 1))
      (g := fun q : ℕ × ℕ × ℕ × ℕ × ℕ => q)
      (Goodstein.primrec_natPow.comp (Primrec.const 2) (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
      Primrec.id primrecRel_witness
  -- `p = (e, r, k, N)`
  have hpe : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.1 := Primrec.fst
  have hpr : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hpk : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hpN : Primrec fun p : ℕ × ℕ × ℕ × ℕ => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htop : PrimrecPred fun p : ℕ × ℕ × ℕ × ℕ =>
      ∀ C < p.2.1 ^ 2 ^ (p.2.2.2 + 1),
        ∃ h < 2 ^ (p.2.2.2 + 1), ¬ bit1 h 0 ∧ p.2.2.1 ≤ popL (p.2.2.2 + 1) h ∧
          RelLargeBits p.2.2.2 h ∧ HomogBits p.1 p.2.1 p.2.2.2 C h := by
    refine bAll (bd := fun p : ℕ × ℕ × ℕ × ℕ => p.2.1 ^ 2 ^ (p.2.2.2 + 1))
      (g := fun p : ℕ × ℕ × ℕ × ℕ => p)
      (Goodstein.primrec_natPow.comp hpr (Goodstein.primrec_natPow.comp (Primrec.const 2)
        (Primrec.succ.comp hpN))) Primrec.id ?_
    exact hA0.of_eq fun q => Iff.rfl
  have hzero : PrimrecPred fun p : ℕ × ℕ × ℕ × ℕ => p.2.1 = 0 ∧ p.1 ≤ p.2.2.2 :=
    (Primrec.eq.comp hpr (Primrec.const 0)).and (Primrec.nat_le.comp hpe hpN)
  have hpos : PrimrecPred fun p : ℕ × ℕ × ℕ × ℕ => 0 < p.2.1 :=
    Primrec.nat_lt.comp (Primrec.const 0) hpr
  exact (hzero.or (hpos.and htop)).of_eq fun p => Iff.rfl

/-! ### A Σ₁ definition of `PHx` exists -/

/-- `PHx` in bounded form. -/
def PHbitsx (x N : ℕ) : Prop :=
  PHbits x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2 N

instance (x N : ℕ) : Decidable (PHbitsx x N) := by unfold PHbitsx; infer_instance

theorem PHbitsx_iff (x N : ℕ) : PHbitsx x N ↔ PHx x N := PHbits_iff ..

theorem primrecRel_PHbitsx : PrimrecRel PHbitsx := by
  have hx : Primrec fun w : ℕ × ℕ => Nat.unpair w.1 := Primrec.unpair.comp Primrec.fst
  have hx2 : Primrec fun w : ℕ × ℕ => Nat.unpair (Nat.unpair w.1).2 :=
    Primrec.unpair.comp (Primrec.snd.comp hx)
  exact primrecPred_PHbits.comp ((Primrec.fst.comp hx).pair
    ((Primrec.fst.comp hx2).pair ((Primrec.snd.comp hx2).pair Primrec.snd)))

/-- The characteristic function of `PHx`, as a primitive recursive function of `(x, N)`. -/
def phC (x N : ℕ) : ℕ := if PHbitsx x N then 0 else 1

theorem primrec_phC : Primrec₂ phC := by
  obtain ⟨_, hdec⟩ := primrecRel_PHbitsx
  have h : Primrec fun w : ℕ × ℕ => phC w.1 w.2 := by
    refine (Primrec.ite (c := fun w : ℕ × ℕ => PHbitsx w.1 w.2) ⟨_, hdec⟩ (Primrec.const 0)
      (Primrec.const 1)).of_eq fun w => ?_
    simp only [phC]
    split <;> simp_all
  exact h.to₂

section Existence
open FFL FFL.FirstOrder

/-- The characteristic function of `PHx` on argument vectors `![N, x]`. -/
def phVec (v : List.Vector ℕ 2) : Part ℕ := Part.some (phC (v.get 1) (v.get 0))

theorem partrec_phVec : Nat.Partrec' phVec := by
  apply Nat.Partrec'.of_part
  exact (primrec_phC.to_comp.comp
    (Primrec.vector_get.to_comp.comp Computable.id (Computable.const 1))
    (Primrec.vector_get.to_comp.comp Computable.id (Computable.const 0))).partrec

/-- **Anti-vacuity for the headline**: some Σ₁ formula defines `PHx` pointwise in ℕ. -/
theorem exists_sigma1_PHx_def :
    ∃ φ : Semisentence ℒₒᵣ 2, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ ∧
      ∀ x N : ℕ, (ℕ ⊧/![N, x] φ) ↔ PHx x N := by
  refine ⟨(Arithmetic.codeOfPartrec' phVec)/[‘0’, #0, #1], ?_, fun x N => ?_⟩
  · exact Bounding.Hierarchy.rew _ (by simp [Arithmetic.codeOfPartrec'])
  · have hspec := Arithmetic.codeOfPartrec'_spec partrec_phVec (y := 0) (v := ![N, x])
    rw [← PHbitsx_iff]
    have hphc : phC x N = 0 ↔ PHbitsx x N := by
      simp only [phC]; split <;> simp_all
    rw [← hphc]
    simpa [Semiformula.eval_substs, Matrix.comp_vecCons', phVec, eq_comm] using hspec

end Existence

end GoodsteinPA.PH

end
