/-
# ε₀-completeness of CNF notations

Mathlib's `Mathlib/SetTheory/Ordinal/Notation.lean` proves that `ONote.repr` is an embedding
`NONote ↪ ε₀` but does NOT prove surjectivity onto ordinals `< ε₀`. This file supplies a pure-mathlib
proof of `exists_NF_repr_eq : ∀ o < ε₀, ∃ x : ONote, x.NF ∧ x.repr = o`, and transfers the result
to any `ℕ`-order obtained by pulling the `NONote` order back along a bijection. A concrete computable
bijection (`natCode`) is constructed from a structural `Encodable ONote` instance.
-/
module

public import AlphaCentauri.ToMathlib.ONote.Epsilon0
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

/-- `ε₀` is a limit ordinal: it is `ω ^ ε₀`, a nonzero power of the limit `ω`. -/
lemma isSuccLimit_epsilon0 : Order.IsSuccLimit ε₀ := by
  have h := isSuccLimit_opow_left isSuccLimit_omega0 (epsilon_pos 0).ne'
  rwa [omega0_opow_epsilon] at h

/-- Every normal-form `ONote` represents an ordinal `< ε₀`. -/
lemma repr_lt_epsilon0 (x : ONote) (h : x.NF) : x.repr < ε₀ := h.repr_lt_epsilon0

/-! ## Transfer to an `ℕ`-order: `ε₀ ≤ orderType` of any pullback of the `NONote` order -/

section Pullback

variable (e : ℕ ≃ NONote)

/-- The `≺`-rank of `n` in the pullback order is the ordinal `NONote.repr (e n)`. -/
lemma rk_ltPull_eq_repr (n : ℕ) : rk (ltPull e) n = NONote.repr (e n) := by
  refine WellFounded.induction (r := ltPull e) inferInstance
    (C := fun k => rk (ltPull e) k = NONote.repr (e k)) n ?_
  intro n IH
  refine le_antisymm (rk_le_of_forall (ltPull e) ?_) ?_
  · intro m hm
    rw [IH m hm]
    exact hm
  · by_contra! hlt
    have hlt' : rk (ltPull e) n < ε₀ :=
      hlt.trans (repr_lt_epsilon0 (e n).1 (e n).2)
    obtain ⟨x, hxNF, hxo⟩ := exists_NF_repr_eq (rk (ltPull e) n) hlt'
    -- `m₀ := e.symm (show NONote from ⟨x, hxNF⟩)` has `repr (e m₀) = rk n`, and `e m₀ < e n` from `rk n < repr (e n)`.
    set m₀ := e.symm (show NONote from ⟨x, hxNF⟩) with hm₀
    have he : NONote.repr (e m₀) = rk (ltPull e) n := by
      rw [hm₀, Equiv.apply_symm_apply]; exact hxo
    have hrel : ltPull e m₀ n := by
      show e m₀ < e n
      show NONote.repr (e m₀) < NONote.repr (e n)
      rw [he]; exact hlt
    have := rk_lt_of_rel (ltPull e) hrel
    rw [IH m₀ hrel, he] at this
    exact lt_irrefl _ this

/-- **Order type of a `NONote`-pullback.** For any coding `e : ℕ ≃ NONote`, the pullback order on
`ℕ` has order type at least `ε₀`.  (AlphaCentauri's `epsilon0_le_orderType_ltPull` is the same
statement for `WellFounded.orderType`; this is the `WellFoundedRank.orderType` form.) -/
theorem epsilon0_le_orderType_ltPull' : ε₀ ≤ orderType (ltPull e) := by
  by_contra! hlt
  obtain ⟨x, hxNF, hxo⟩ := exists_NF_repr_eq (orderType (ltPull e)) hlt
  set n₀ := e.symm (show NONote from ⟨x, hxNF⟩) with hn₀
  have he : rk (ltPull e) n₀ = orderType (ltPull e) := by
    rw [rk_ltPull_eq_repr, hn₀, Equiv.apply_symm_apply]; exact hxo
  have hle : Order.succ (rk (ltPull e) n₀) ≤ orderType (ltPull e) :=
    Ordinal.le_iSup (fun n => Order.succ (rk (ltPull e) n)) n₀
  rw [he] at hle
  exact (Order.lt_succ _).not_ge hle

end Pullback

/-! ## A concrete coding `ℕ ≃ NONote` -/

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

/-! `natCode` used to be `(Denumerable.eqv NONote).symm`.  Since mathlib marked
`Nat.Subtype.denumerable` `@[no_expose]`, that route can no longer be related to the *increasing*
enumeration `Nat.Subtype.ofNat` of `Encodable.encode`'s range (which `ONote/Computability.lean`
needs to see `natCode` as monotone in codes), so we build the equiv from that enumeration directly.
Only `Equiv`-ness is used downstream. -/

/-- The range of `Encodable.encode : NONote → ℕ` is decidable and infinite. -/
instance decPredRangeEncode :
    DecidablePred (· ∈ Set.range (Encodable.encode : NONote → ℕ)) :=
  Encodable.decidableRangeEncode NONote

instance infiniteRangeEncode :
    Infinite (Set.range (Encodable.encode : NONote → ℕ)) :=
  Infinite.of_injective _ (Equiv.ofInjective _ Encodable.encode_injective).injective

/-- The increasing enumeration `ℕ → Set.range encode` of the `NONote` codes. -/
def codeEnum (a : ℕ) : Set.range (Encodable.encode : NONote → ℕ) :=
  Nat.Subtype.ofNat (Set.range (Encodable.encode : NONote → ℕ)) a

lemma codeEnum_strictMono : StrictMono codeEnum :=
  strictMono_nat_of_lt_succ fun n => by
    show Nat.Subtype.ofNat _ n < Nat.Subtype.ofNat _ (n + 1)
    rw [show Nat.Subtype.ofNat (Set.range (Encodable.encode : NONote → ℕ)) (n + 1)
        = Nat.Subtype.succ (Nat.Subtype.ofNat _ n) from rfl]
    exact Nat.Subtype.lt_succ_self _

@[simp] lemma natCode_apply (a : ℕ) :
    natCode a = (Encodable.equivRangeEncode NONote).symm (codeEnum a) := by
  show (Encodable.equivRangeEncode NONote).symm
      (Nat.Subtype.orderIsoOfNat (Set.range (Encodable.encode : NONote → ℕ)) a) = _
  rw [Nat.Subtype.orderIsoOfNat_apply]
  rfl

/-- **A concrete `ℕ`-order of order type ≥ ε₀.** -/
theorem epsilon0_le_orderType_natCode' : ε₀ ≤ orderType (ltPull natCode) :=
  epsilon0_le_orderType_ltPull' natCode

end ONote
