/-
# `src/GoodsteinPA/Epsilon0Complete.lean` — ε₀-completeness of CNF notations

mathlib's `Mathlib/SetTheory/Ordinal/Notation.lean` proves that `ONote.repr` is order-preserving and
injective on normal forms — an *embedding* `NONote ↪ ε₀` — but it does NOT prove surjectivity onto the
ordinals `< ε₀`. That surjectivity is the real F-girder of this project (`PENDING_WORK.md`, lap-18
reflection): the lower bound `ε₀ ≤ orderType lt` for the seam order `lt` ultimately needs every ordinal
below ε₀ to be *named* by a CNF notation.

This file fills that gap with a pure-mathlib proof (zero Foundation dependency):

  `exists_NF_repr_eq : ∀ o < ε₀, ∃ x : ONote, x.NF ∧ x.repr = o`.

The proof is the standard Cantor-normal-form recursion. For `o ≠ 0` write `o = ω^e · c + r` with
`e = log ω o`, `c = o / ω^e` (a positive natural number, since `1 ≤ c < ω`), `r = o % ω^e < ω^e`.
Both `e` and `r` are `< o` (the key fact `log ω o < o` for `o < ε₀` is `log_omega0_lt_self`, which
uses that `ω^·` has no fixed point below ε₀), so well-founded recursion on `o` supplies CNF notations
`ē, r̄` for them, and `ONote.oadd ē c r̄` is the notation for `o`.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.SetTheory.Ordinal.Veblen
import GoodsteinPA.TruthSem

namespace GoodsteinPA.Epsilon0Complete

open Ordinal ONote
open scoped Ordinal

/-- For `0 ≠ o < ε₀`, the leading CNF exponent `log ω o` is strictly below `o`.
Equality would force `ω ^ o ≤ o`, i.e. `o` to be an ε-number, contradicting `o < ε₀`. -/
theorem log_omega0_lt_self {o : Ordinal} (ho : o ≠ 0) (hε : o < ε₀) :
    Ordinal.log ω o < o := by
  have h1 : ω ^ Ordinal.log ω o ≤ o := opow_log_le_self ω ho
  have h2 : Ordinal.log ω o ≤ ω ^ Ordinal.log ω o :=
    (isNormal_opow one_lt_omega0).strictMono.le_apply
  rcases lt_or_eq_of_le (h2.trans h1) with h | h
  · exact h
  · rw [h] at h1
    exact absurd (epsilon_zero_le_of_omega0_opow_le h1) (not_le.2 hε)

/-- **ε₀-completeness of CNF notations.** Every ordinal `< ε₀` is `repr` of some normal-form `ONote`.
This is the surjectivity direction missing from mathlib's `Ordinal/Notation.lean`. -/
theorem exists_NF_repr_eq :
    ∀ o : Ordinal, o < ε₀ → ∃ x : ONote, ONote.NF x ∧ ONote.repr x = o := by
  intro o
  induction o using WellFoundedLT.induction with
  | _ o IH =>
    intro hε
    rcases eq_or_ne o 0 with rfl | ho
    · exact ⟨0, ONote.NF.zero, ONote.repr_zero⟩
    · -- leading exponent
      set e := Ordinal.log ω o with he
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
      refine ⟨ONote.oadd eN ⟨m, hmpos⟩ rN, ?_, ?_⟩
      · -- normal form
        refine ONote.NF.oadd heNF _ (ONote.NF.below_of_lt' ?_ hrNF)
        rw [hrRepr, heRepr]
        exact mod_lt _ hωe
      · -- value
        have hval : ONote.repr (ONote.oadd eN ⟨m, hmpos⟩ rN)
            = ω ^ ONote.repr eN * (m : Ordinal) + ONote.repr rN := by
          simp [ONote.repr]
        rw [hval, heRepr, hrRepr, hr, ← hm]
        exact div_add_mod o (ω ^ e)

/-- `ε₀` is a limit ordinal: it is `ω ^ ε₀`, a nonzero power of the limit `ω`. -/
theorem isSuccLimit_epsilon0 : Order.IsSuccLimit ε₀ := by
  have h := isSuccLimit_opow_left isSuccLimit_omega0 (epsilon_pos 0).ne'
  rwa [omega0_opow_epsilon] at h

/-- Every normal-form `ONote` represents an ordinal `< ε₀` (the embedding direction; mathlib states
the type's purpose informally but provides no `repr < ε₀` lemma). -/
theorem repr_lt_epsilon0 : ∀ x : ONote, x.NF → ONote.repr x < ε₀ := by
  intro x
  induction x with
  | zero => intro _; exact epsilon_pos 0
  | oadd e n a _IHe IHa =>
    intro h
    have hee : ONote.repr e < ε₀ := _IHe h.fst
    have hbelow : ONote.repr a < ω ^ ONote.repr e := h.snd'.repr_lt
    have hsucc : Order.succ (ONote.repr e) < ε₀ := isSuccLimit_epsilon0.succ_lt hee
    have key : ONote.repr (ONote.oadd e n a) < ω ^ (Order.succ (ONote.repr e)) := by
      rw [opow_succ]
      have h1 : ONote.repr (ONote.oadd e n a)
          = ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ONote.repr a := by simp [ONote.repr]
      rw [h1]
      calc ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ONote.repr a
          < ω ^ ONote.repr e * ((n : ℕ) : Ordinal) + ω ^ ONote.repr e :=
            (add_lt_add_iff_left _).2 hbelow
        _ = ω ^ ONote.repr e * (((n : ℕ) : Ordinal) + 1) := by rw [mul_add, mul_one]
        _ ≤ ω ^ ONote.repr e * ω := by
            gcongr
            rw [← Nat.cast_one, ← Nat.cast_add]
            exact (natCast_lt_omega0 _).le
    exact key.trans (((opow_lt_opow_iff_right one_lt_omega0).2 hsucc).trans_eq
      (omega0_opow_epsilon 0))

/-- The range of `NONote.repr` is exactly the ordinals `< ε₀`: the embedding (`repr_lt_epsilon0`)
together with the new surjectivity (`exists_NF_repr_eq`). -/
theorem range_NONote_repr : Set.range NONote.repr = Set.Iio ε₀ := by
  ext o
  constructor
  · rintro ⟨x, rfl⟩
    exact repr_lt_epsilon0 x.1 x.2
  · intro ho
    obtain ⟨x, hx, hxo⟩ := exists_NF_repr_eq o ho
    exact ⟨⟨x, hx⟩, hxo⟩

/-! ## Transfer to an `ℕ`-order: `ε₀ ≤ orderType` of any pullback of the `NONote` order

The Boundedness/Seam machinery needs a well-order `lt : ℕ → ℕ → Prop` with `ε₀ ≤ orderType lt`.
Pulling the `NONote` order back along *any* bijection `e : ℕ ≃ NONote` works: the project's rank
`rk (ltPull e) n` equals `NONote.repr (e n)`, and since `repr ∘ e` is onto `[0, ε₀)` (the girder),
no ordinal `< ε₀` can bound all the ranks, forcing `ε₀ ≤ orderType (ltPull e)`. This decouples the
order-type half of F from the concrete *computable* coding (which Worker B/D will pin for the
`ℒₒᵣ`-definability `φ`): the lemma holds for any equiv, so the eventual coding instantiates it. -/

open GoodsteinPA.TruthSem

/-- The `NONote` order pulled back to `ℕ` along a coding `e`. -/
def ltPull (e : ℕ ≃ NONote) (a b : ℕ) : Prop := e a < e b

instance ltPull_wf (e : ℕ ≃ NONote) : IsWellFounded ℕ (ltPull e) :=
  ⟨InvImage.wf e NONote.lt_wf⟩

/-- The ≺-rank of `n` in the pullback order is the ordinal `NONote.repr (e n)`. This is the
`note_rank_eq_repr` of the seam advice — true precisely because `repr ∘ e` is *onto* `[0, ε₀)`. -/
theorem rk_ltPull_eq_repr (e : ℕ ≃ NONote) (n : ℕ) :
    rk (ltPull e) n = NONote.repr (e n) := by
  refine IsWellFounded.induction
    (motive := fun k => rk (ltPull e) k = NONote.repr (e k)) (ltPull e) n ?_
  intro n IH
  refine le_antisymm (rk_le_of_forall (ltPull e) ?_) ?_
  · intro m hm
    rw [IH m hm]
    exact hm
  · by_contra hlt
    rw [not_le] at hlt
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

/-- **The order-type half of F.** For any coding `e : ℕ ≃ NONote`, the pullback order on `ℕ` has
order type at least `ε₀` — exactly the `Seam.ge` obligation. -/
theorem epsilon0_le_orderType_ltPull (e : ℕ ≃ NONote) :
    ε₀ ≤ orderType (ltPull e) := by
  by_contra hlt
  rw [not_le] at hlt
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

/-! ## A concrete coding `ℕ ≃ NONote`

`ONote` derives only `DecidableEq`, so we supply a computable `Encodable ONote` (a structural
pairing) and `Infinite NONote` (the numerals `ofNat n` are distinct), giving `Denumerable NONote`
and hence a coding `ℕ ≃ NONote`. Plugged into `epsilon0_le_orderType_ltPull`, this exhibits a
concrete `ℕ`-order with `ε₀ ≤ orderType`. -/

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

theorem decodeONote_encodeONote : ∀ x : ONote, decodeONote (encodeONote x) = x
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

/-- A concrete **computable** coding of `ℕ` by CNF notations (= `Denumerable.ofNat NONote`). Worker B
must build `φ` defining `ltPull natCode` over THIS decode so the two codings are identical by
construction; computability (not `ofCountable`) is what keeps `ltPull natCode` an `REPred`. -/
def natCode : ℕ ≃ NONote := (Denumerable.eqv NONote).symm

/-- **A concrete `ℕ`-order of order type ≥ ε₀** (the standalone `Seam.ge` witness). -/
theorem epsilon0_le_orderType_natCode :
    ε₀ ≤ orderType (ltPull natCode) :=
  epsilon0_le_orderType_ltPull natCode

end GoodsteinPA.Epsilon0Complete
