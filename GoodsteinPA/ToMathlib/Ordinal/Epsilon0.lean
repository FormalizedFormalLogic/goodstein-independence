/-
# ε₀-completeness of CNF notations

Mathlib's `Mathlib/SetTheory/Ordinal/Notation.lean` proves that `ONote.repr` is an embedding
`NONote ↪ ε₀` but does NOT prove surjectivity onto ordinals `< ε₀`. This file supplies a pure-mathlib
proof of `exists_NF_repr_eq : ∀ o < ε₀, ∃ x : ONote, x.NF ∧ x.repr = o`, and transfers the result
to any `ℕ`-order obtained by pulling the `NONote` order back along a bijection. A concrete computable
bijection (`natCode`) is constructed from a structural `Encodable ONote` instance.
-/
module

public import Mathlib.SetTheory.Ordinal.Notation
public import Mathlib.SetTheory.Ordinal.Veblen
public import GoodsteinPA.ToMathlib.Ordinal.WellFoundedRank

@[expose] public section

namespace ONote

open Ordinal ONote WellFoundedRank
open scoped Ordinal

/-- For `0 ≠ o < ε₀`, the leading CNF exponent `log ω o` is strictly below `o`. -/
lemma log_omega0_lt_self {o : Ordinal} (ho : o ≠ 0) (hε : o < ε₀) : log ω o < o := by
  have h1 : ω ^ log ω o ≤ o := opow_log_le_self ω ho
  have h2 : log ω o ≤ ω ^ log ω o :=
    (isNormal_opow one_lt_omega0).strictMono.le_apply
  rcases lt_or_eq_of_le (h2.trans h1) with h | h
  · exact h
  · rw [h] at h1
    exact absurd (epsilon_zero_le_of_omega0_opow_le h1) (not_le.2 hε)

/-- **ε₀-completeness of CNF notations.** Every ordinal `< ε₀` is `repr` of some normal-form `ONote`. -/
theorem exists_NF_repr_eq (o : Ordinal) (hε : o < ε₀) : ∃ x : ONote, x.NF ∧ x.repr = o := by
  induction o using WellFoundedLT.induction with
  | _ o IH =>
    obtain rfl | ho := eq_or_ne o 0
    · exact ⟨0, NF.zero, repr_zero⟩
    · -- leading exponent
      set e := log ω o with he
      have hee : e < o := log_omega0_lt_self ho hε
      obtain ⟨eN, heNF, heRepr⟩ := IH e hee (hee.trans hε)
      -- remainder
      set r := o % ω ^ e with hr
      have hre : r < o := mod_opow_log_lt_self ω ho
      obtain ⟨rN, hrNF, hrRepr⟩ := IH r hre (hre.trans hε)
      -- coefficient `c = o / ω^e` is a positive natural number
      have hcpos : 0 < o / ω ^ e := div_opow_log_pos ω ho
      have hclt : o / ω ^ e < ω := div_opow_log_lt o one_lt_omega0
      obtain ⟨m, hm⟩ := lt_omega0.1 hclt
      have hmpos : 0 < m := by rw [hm] at hcpos; exact_mod_cast hcpos
      have hωe : ω ^ e ≠ 0 := (opow_pos e omega0_pos).ne'
      refine ⟨oadd eN ⟨m, hmpos⟩ rN, ?_, ?_⟩
      · -- normal form
        refine NF.oadd heNF _ (NF.below_of_lt' ?_ hrNF)
        rw [hrRepr, heRepr]
        exact mod_lt _ hωe
      · -- value
        have hval : repr (oadd eN ⟨m, hmpos⟩ rN) = ω ^ repr eN * (m : Ordinal) + repr rN := by
          simp [repr]
        rw [hval, heRepr, hrRepr, hr, ← hm]
        exact div_add_mod o (ω ^ e)

/-- `ε₀` is a limit ordinal: it is `ω ^ ε₀`, a nonzero power of the limit `ω`. -/
lemma isSuccLimit_epsilon0 : Order.IsSuccLimit ε₀ := by
  have h := isSuccLimit_opow_left isSuccLimit_omega0 (epsilon_pos 0).ne'
  rwa [omega0_opow_epsilon] at h

/-- Every normal-form `ONote` represents an ordinal `< ε₀`. -/
lemma repr_lt_epsilon0 (x : ONote) (h : x.NF) : x.repr < ε₀ := by
  induction x with
  | zero => exact epsilon_pos 0
  | oadd e n a IHe IHa =>
    have hee : e.repr < ε₀ := IHe h.fst
    have hbelow : a.repr < ω ^ e.repr := h.snd'.repr_lt
    have hsucc : Order.succ e.repr < ε₀ := isSuccLimit_epsilon0.succ_lt hee
    have key : (oadd e n a).repr < ω ^ (Order.succ e.repr) := by
      rw [opow_succ]
      have h1 : (oadd e n a).repr = ω ^ e.repr * ((n : ℕ) : Ordinal) + a.repr := by simp [repr]
      rw [h1]
      calc ω ^ e.repr * ((n : ℕ) : Ordinal) + a.repr
          < ω ^ e.repr * ((n : ℕ) : Ordinal) + ω ^ e.repr := (add_lt_add_iff_left _).2 hbelow
        _ = ω ^ e.repr * (((n : ℕ) : Ordinal) + 1) := by rw [mul_add, mul_one]
        _ ≤ ω ^ e.repr * ω := by
            gcongr
            rw [← Nat.cast_one, ← Nat.cast_add]
            exact (natCast_lt_omega0 _).le
    exact key.trans (((opow_lt_opow_iff_right one_lt_omega0).2 hsucc).trans_eq
      (omega0_opow_epsilon 0))

/-- The range of `NONote.repr` is exactly the ordinals `< ε₀`. -/
theorem range_NONote_repr : Set.range NONote.repr = Set.Iio ε₀ := by
  ext o
  constructor
  · rintro ⟨x, rfl⟩
    exact repr_lt_epsilon0 x.1 x.2
  · intro ho
    obtain ⟨x, hx, hxo⟩ := exists_NF_repr_eq o ho
    exact ⟨⟨x, hx⟩, hxo⟩

/-! ## Transfer to an `ℕ`-order: `ε₀ ≤ orderType` of any pullback of the `NONote` order -/

section Pullback

variable (e : ℕ ≃ NONote)

/-- The `NONote` order pulled back to `ℕ` along a coding `e`. -/
def ltPull (a b : ℕ) : Prop := e a < e b

instance ltPull_wf : IsWellFounded ℕ (ltPull e) :=
  ⟨InvImage.wf e NONote.lt_wf⟩

/-- The `≺`-rank of `n` in the pullback order is the ordinal `NONote.repr (e n)`. -/
lemma rk_ltPull_eq_repr (n : ℕ) : rk (ltPull e) n = NONote.repr (e n) := by
  refine IsWellFounded.induction
    (motive := fun k => rk (ltPull e) k = NONote.repr (e k)) (ltPull e) n ?_
  intro n IH
  refine le_antisymm (rk_le_of_forall (ltPull e) ?_) ?_
  · intro m hm
    rw [IH m hm]
    exact hm
  · by_contra! hlt
    have hlt' : rk (ltPull e) n < ε₀ :=
      hlt.trans (repr_lt_epsilon0 (e n).1 (e n).2)
    obtain ⟨x, hxNF, hxo⟩ := exists_NF_repr_eq (rk (ltPull e) n) hlt'
    -- `m₀ := e.symm ⟨x, hxNF⟩` has `repr (e m₀) = rk n`, and `e m₀ < e n` from `rk n < repr (e n)`.
    set m₀ := e.symm ⟨x, hxNF⟩ with hm₀
    have he : NONote.repr (e m₀) = rk (ltPull e) n := by
      rw [hm₀, Equiv.apply_symm_apply]; exact hxo
    have hrel : ltPull e m₀ n := by
      show e m₀ < e n
      show NONote.repr (e m₀) < NONote.repr (e n)
      rw [he]; exact hlt
    have := rk_lt_of_rel (ltPull e) hrel
    rw [IH m₀ hrel, he] at this
    exact lt_irrefl _ this

/-- **Order type of a `NONote`-pullback.** For any coding `e : ℕ ≃ NONote`, the pullback order on `ℕ`
has order type at least `ε₀`. -/
theorem epsilon0_le_orderType_ltPull : ε₀ ≤ orderType (ltPull e) := by
  by_contra! hlt
  -- name `orderType` itself as some `repr (e n₀)`, then `succ` of it exceeds the sup — contradiction.
  obtain ⟨x, hxNF, hxo⟩ := exists_NF_repr_eq (orderType (ltPull e)) hlt
  set n₀ := e.symm ⟨x, hxNF⟩ with hn₀
  have he : rk (ltPull e) n₀ = orderType (ltPull e) := by
    rw [rk_ltPull_eq_repr, hn₀, Equiv.apply_symm_apply]; exact hxo
  -- `succ (rk n₀) ≤ orderType` (a term of the sup), but `succ (rk n₀) = succ orderType > orderType`.
  have hle : Order.succ (rk (ltPull e) n₀) ≤ orderType (ltPull e) :=
    Ordinal.le_iSup (fun n => Order.succ (rk (ltPull e) n)) n₀
  rw [he] at hle
  exact (Order.lt_succ _).not_ge hle

end Pullback

/-! ## A concrete coding `ℕ ≃ NONote` -/

/-- Structural encoding `ONote → ℕ`. -/
def encodeONote : ONote → ℕ
  | ONote.zero => 0
  | ONote.oadd e n a =>
      Nat.pair (encodeONote e) (Nat.pair ((n : ℕ) - 1) (encodeONote a)) + 1

/-- Structural decoding `ℕ → ONote`, a left inverse of `encodeONote`. -/
def decodeONote : ℕ → ONote
  | 0 => ONote.zero
  | (m + 1) =>
      ONote.oadd (decodeONote (Nat.unpair m).1)
        ⟨(Nat.unpair (Nat.unpair m).2).1 + 1, Nat.succ_pos _⟩
        (decodeONote (Nat.unpair (Nat.unpair m).2).2)
  decreasing_by
    · exact Nat.lt_succ_of_le (Nat.unpair_left_le m)
    · exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le m))

lemma decodeONote_encodeONote : ∀ x : ONote, decodeONote (encodeONote x) = x
  | ONote.zero => by simp only [encodeONote, decodeONote]
  | ONote.oadd e n a => by
      rw [encodeONote, decodeONote]
      simp only [Nat.unpair_pair, decodeONote_encodeONote e, decodeONote_encodeONote a]
      congr 1
      apply Subtype.ext
      show (n : ℕ) - 1 + 1 = (n : ℕ)
      exact Nat.succ_pred_eq_of_pos n.pos

instance : Encodable ONote :=
  Encodable.ofLeftInverse encodeONote decodeONote decodeONote_encodeONote

instance : Infinite NONote :=
  Infinite.of_injective NONote.ofNat (by
    intro m n h
    simpa [NONote.repr, NONote.ofNat] using congrArg NONote.repr h)

instance : Encodable NONote :=
  inferInstanceAs (Encodable {o : ONote // o.NF})

instance : Denumerable NONote :=
  Denumerable.ofEncodableOfInfinite NONote

/-- A concrete **computable** coding of `ℕ` by CNF notations, built from the structural `Encodable ONote`. -/
def natCode : ℕ ≃ NONote := (Denumerable.eqv NONote).symm

/-- **A concrete `ℕ`-order of order type ≥ ε₀.** -/
theorem epsilon0_le_orderType_natCode : ε₀ ≤ orderType (ltPull natCode) :=
  epsilon0_le_orderType_ltPull natCode

end ONote
