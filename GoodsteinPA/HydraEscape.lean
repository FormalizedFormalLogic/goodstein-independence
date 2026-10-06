/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import GoodsteinPA.HydraLowerBound
public import GoodsteinPA.HydraIndependence

@[expose] public section

/-!
# The canonical battle escapes every `f_o` along its own codes (stage 2, P3)

For each `o < ε₀` we exhibit arbitrarily large codes `m` whose canonical battle is still alive at
every step `N ≤ f_o(m)`.  The witness is `padded P k`: `k` single heads next to the hydra of
`ω^P + ω^3`, `P = o + 4` (`osucc` four times).  The heads go first, so the battle outlasts
`hardy (ω^P + ω^3) k = hardy (ω^P) (hardy (ω^3) k)`; the code grows by one squaring per head, so it
stays below `f_3(k) ≤ hardy (ω^3) k`; and `f_o < f_P ≤ hardy (ω^P)` finishes the comparison.
-/

namespace GoodsteinPA.Hydra

open ONote Ordinal
open LeanGallery.Logic.Hydra LeanGallery.Logic.Hydra.Hydra

/-! ### From a Cantor normal form to a hydra -/

/-- The children of the hydra of a Cantor normal form: `n` copies of the hydra of `e` for each
term `ω^e · n`. -/
def kids : ONote → List Hydra
  | 0 => []
  | oadd e n a => List.replicate n (node (kids e)) ++ kids a

/-- On a tail below `ω^e`, inserting `ω^e` `n` times builds the term `ω^e · n` on top. -/
theorem iterate_insertTerm_top {e a : ONote} [e.NF] [a.NF] (ha : NFBelow a (ONote.repr e)) :
    ∀ n : ℕ, (insertTerm e)^[n + 1] a = oadd e n.succPNat a
  | 0 => by
    cases a with
    | zero => rfl
    | oadd a' m b =>
      have : a'.NF := NF.fst ‹_›
      show insertTerm e (oadd a' m b) = _
      simp only [insertTerm, cmp_eq_gt (lt_def.mpr ha.lt)]
      rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', iterate_insertTerm_top ha n]
    simp only [insertTerm, cmp_self]
    rfl

theorem ord_kids : ∀ (α : ONote) [α.NF], ord (node (kids α)) = α
  | 0, _ => ord_leaf
  | oadd e n a, h => by
    have he : e.NF := h.fst
    have ha : a.NF := h.snd
    rw [ord_node, kids, List.map_append, List.map_replicate, sumTerms_replicate_append,
      ← ord_node, ord_kids e, ord_kids a]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    rw [hk, iterate_insertTerm_top h.snd' k]
    congr 1
    exact PNat.eq (by simp [hk])

theorem iterate_insertTerm_zero_NF (β : ONote) [β.NF] : ∀ k, ((insertTerm 0)^[k] β).NF
  | 0 => ‹_›
  | k + 1 => by
    have := iterate_insertTerm_zero_NF β k
    rw [Function.iterate_succ_apply']
    exact insertTerm_NF 0 _

/-- Each extra head shifts the Hardy argument by one. -/
theorem hardy_iterate_insertTerm_zero (β : ONote) [β.NF] :
    ∀ (k t : ℕ), hardy ((insertTerm 0)^[k] β) t = hardy β (t + k)
  | 0, t => rfl
  | k + 1, t => by
    have := iterate_insertTerm_zero_NF β k
    rw [Function.iterate_succ_apply',
      hardy_succ _ (fundamentalSequence_insertTerm_zero ((insertTerm 0)^[k] β))]
    show hardy ((insertTerm 0)^[k] β) (t + 1) = _
    rw [hardy_iterate_insertTerm_zero β k (t + 1)]
    congr 1
    omega

/-! ### Codes of padded hydras -/

theorem pair_zero_bounds (y : ℕ) : y ≤ Nat.pair 0 y ∧ Nat.pair 0 y + 3 ≤ (y + 2) ^ 2 := by
  have hsq : (y + 2) ^ 2 = y * y + 4 * y + 4 := by ring
  have hmul := Nat.le_mul_self y
  unfold Nat.pair
  split <;> constructor <;> omega

/-- Each extra head squares the code (plus change), and adds at least one. -/
theorem toCode_padded (cs : List Hydra) : ∀ k : ℕ,
    toCode (node (List.replicate k leaf ++ cs)) + 2 ≤ (toCode (node cs) + 2) ^ (2 ^ k) ∧
      k ≤ toCode (node (List.replicate k leaf ++ cs))
  | 0 => by simp
  | k + 1 => by
    obtain ⟨ih₁, ih₂⟩ := toCode_padded cs k
    have hcode : toCode (node (List.replicate (k + 1) leaf ++ cs)) =
        Nat.pair 0 (toCode (node (List.replicate k leaf ++ cs))) + 1 := by
      have h0 : toCode leaf = 0 := by rw [leaf, toCode]
      rw [List.replicate_succ, List.cons_append, toCode, h0]
    obtain ⟨hlo, hhi⟩ := pair_zero_bounds (toCode (node (List.replicate k leaf ++ cs)))
    rw [hcode]
    refine ⟨?_, by omega⟩
    calc Nat.pair 0 (toCode (node (List.replicate k leaf ++ cs))) + 1 + 2
        ≤ (toCode (node (List.replicate k leaf ++ cs)) + 2) ^ 2 := by omega
      _ ≤ ((toCode (node cs) + 2) ^ (2 ^ k)) ^ 2 := Nat.pow_le_pow_left ih₁ 2
      _ = (toCode (node cs) + 2) ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

/-! ### The escape -/

/-- `f_o` is strictly below `f_{o+1}` (from `x ≥ 2`). -/
theorem fastGrowing_lt_osucc {o : ONote} (ho : o.NF) {x : ℕ} (hx : 2 ≤ x) :
    fastGrowing o x < fastGrowing (osucc o) x :=
  fastGrowing_lt_succ_index (fundamentalSequence_osucc ho) hx

/-- **P3: the lower bound.**  For every `o < ε₀` there are arbitrarily large codes whose canonical
battle is alive at every step `N ≤ f_o(m)`. -/
theorem escapes : Escapes := by
  intro o ho M
  have h1 := osucc_NF ho
  have h2 := osucc_NF h1
  have h3 := osucc_NF h2
  have hP : (osucc (osucc (osucc (osucc o)))).NF := osucc_NF h3
  set P := osucc (osucc (osucc (osucc o))) with hPdef
  have hchain : ∀ x, 2 ≤ x → fastGrowing o x < fastGrowing P x := fun x hx =>
    lt_trans (fastGrowing_lt_osucc ho hx) (lt_trans (fastGrowing_lt_osucc h1 hx)
      (lt_trans (fastGrowing_lt_osucc h2 hx) (fastGrowing_lt_osucc h3 hx)))
  have hδ : (oadd (ofNat 3) 1 0).NF := NF.oadd_zero _ _
  have hωP : (oadd P 1 0).NF := NF.oadd_zero _ _
  have hcond : (oadd (ofNat 3) 1 0).repr < ω ^ (lastExp (oadd P 1 0)).repr := by
    show ω ^ (ofNat 3).repr * (1 : ℕ+) + 0 < ω ^ P.repr
    have hrP : P.repr = o.repr + 1 + 1 + 1 + 1 := by
      rw [hPdef, repr_osucc h3, repr_osucc h2, repr_osucc h1, repr_osucc ho]
    have e1 : ((1 : ℕ) : Ordinal) ≤ o.repr + 1 := by rw [Nat.cast_one]; exact le_add_self
    have e2 : ((2 : ℕ) : Ordinal) ≤ o.repr + 1 + 1 :=
      (Nat.cast_succ (R := Ordinal) 1).symm ▸ add_le_add_left e1 1
    have e3 : ((3 : ℕ) : Ordinal) ≤ o.repr + 1 + 1 + 1 :=
      (Nat.cast_succ (R := Ordinal) 2).symm ▸ add_le_add_left e2 1
    have e4 : ((4 : ℕ) : Ordinal) ≤ o.repr + 1 + 1 + 1 + 1 :=
      (Nat.cast_succ (R := Ordinal) 3).symm ▸ add_le_add_left e3 1
    rw [hrP, ONote.repr_ofNat]
    simp only [PNat.one_coe, Nat.cast_one, mul_one, add_zero]
    apply (Ordinal.opow_lt_opow_iff_right one_lt_omega0).mpr
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (by norm_num)) e4
  set γ := oadd P 1 0 + oadd (ofNat 3) 1 0 with hγdef
  have hγ : γ.NF := inferInstance
  have hcomp : ∀ x, hardy γ x = hardy (oadd P 1 0) (hardy (oadd (ofNat 3) 1 0) x) :=
    hardy_add_comp _ hωP _ hδ (Or.inr hcond)
  obtain ⟨hhi, hlo⟩ := toCode_padded (kids γ) (M + toCode (node (kids γ)) + 4)
  set C := toCode (node (kids γ))
  set k := M + C + 4 with hkdef
  set Hk := node (List.replicate k leaf ++ kids γ)
  refine ⟨toCode Hk, le_trans (by omega) hlo, fun N hN => ?_⟩
  rw [ofCode_toCode, battle_eq_runFrom]
  apply runFrom_alive_of_lt_hardy
  have hord : ord Hk = (insertTerm 0)^[k] γ := by
    rw [ord_node, List.map_append, List.map_replicate, show ord leaf = 0 from ord_leaf,
      sumTerms_replicate_append, ← ord_node, ord_kids]
  rw [hord, hardy_iterate_insertTerm_zero, Nat.zero_add, Nat.zero_add, hcomp]
  -- the code is below `f_3(k) ≤ hardy (ω^3) k`
  have hk2 : 2 ≤ k := by omega
  have hCk : C + 2 ≤ 2 ^ k := le_trans (by omega) (Nat.lt_two_pow_self).le
  have hcode : toCode Hk ≤ hardy (oadd (ofNat 3) 1 0) k := by
    calc toCode Hk ≤ (C + 2) ^ (2 ^ k) := by omega
      _ ≤ (2 ^ k) ^ (2 ^ k) := Nat.pow_le_pow_left hCk _
      _ = 2 ^ (2 ^ k * k) := by rw [← pow_mul, mul_comm]
      _ ≤ fastGrowing (ofNat 3) k := Goodstein.Dom.two_pow_le_fastGrowing_ofNat_three hk2
      _ ≤ hardy (oadd (ofNat 3) 1 0) k := fastGrowing_le_hardy_omega_pow _ k
  calc N ≤ fastGrowing o (toCode Hk) := hN
    _ < fastGrowing P (toCode Hk) := hchain _ (by omega)
    _ ≤ hardy (oadd P 1 0) (toCode Hk) := fastGrowing_le_hardy_omega_pow P _
    _ ≤ hardy (oadd P 1 0) (hardy (oadd (ofNat 3) 1 0) k) := hardy_monotone _ hcode

section Headline
open FFL FFL.FirstOrder

/-- **PA does not prove that the canonical hydra battle terminates**: for
every Σ₁ formula `φ` defining the battle pointwise in ℕ, `𝗣𝗔 ⊬ ∀ m, ∃ N, φ(m, N)`. -/
theorem pa_not_proves_hydra
    (φ : Semisentence ℒₒᵣ 2) (hφ : Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ)
    (hdef : ∀ m N : ℕ, (ℕ ⊧/![N, m] φ) ↔ battle (ofCode m) N = Hydra.leaf) :
    𝗣𝗔 ⊬ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) :=
  pa_not_proves_hydra_of_escape escapes φ hφ hdef

end Headline

end GoodsteinPA.Hydra

end
