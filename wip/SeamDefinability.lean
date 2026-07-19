/-
# `src/GoodsteinPA/SeamDefinability.lean` — binary representability for the F seam (Worker B, step 2)

Foundation's `codeOfREPred` (`Representation.lean:245`) turns a unary r.e. predicate into an
`ℒₒᵣ`-`Semisentence` of arity 1 with the spec `ℕ ⊧/![x] (codeOfREPred A) ↔ A x`. The arithmetization
seam needs the **binary** version: an `ℒₒᵣ`-formula defining the order relation `lt : ℕ → ℕ → Prop`.

`codeOfREPred₂` builds it from the same `codeOfPartrec'` primitive (arity `k+1`, here `k = 2`), and
`codeOfREPred₂_spec` is the binary analogue of `codeOfREPred_spec` — a faithful port of that proof.
-/
import GoodsteinPA.EpsilonOrder
import GoodsteinPA.Epsilon0Complete
import GoodsteinPA.ONoteComp
import Foundation.FirstOrder.Arithmetic.R0.Representation

namespace GoodsteinPA.SeamDefinability

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open GoodsteinPA.Epsilon0Complete GoodsteinPA.EpsilonOrder
open Classical

/-- Binary representability: an `ℒₒᵣ`-`Semisentence` of arity 2 coding the r.e. relation `R`. -/
noncomputable def codeOfREPred₂ (R : ℕ → ℕ → Prop) : Semisentence ℒₒᵣ 2 :=
  let f : List.Vector ℕ 2 →. Unit :=
    fun v ↦ Part.assert (R (v.get 0) (v.get 1)) fun _ ↦ Part.some ()
  (codeOfPartrec' (fun v ↦ (f v).map fun _ ↦ 0))/[‘0’, #0, #1]

/-- The binary analogue of `codeOfREPred_spec`. -/
lemma codeOfREPred₂_spec {R : ℕ → ℕ → Prop}
    (hR : REPred fun v : List.Vector ℕ 2 ↦ R (v.get 0) (v.get 1)) {m n : ℕ} :
    ℕ ⊧/![m, n] (codeOfREPred₂ R) ↔ R m n := by
  let f : List.Vector ℕ 2 →. Unit :=
    fun v ↦ Part.assert (R (v.get 0) (v.get 1)) fun _ ↦ Part.some ()
  suffices
      ℕ ⊧/![m, n] ((codeOfPartrec' fun v ↦ Part.map (fun _ ↦ 0) (f v))/[‘0’, #0, #1]) ↔ R m n from this
  have hpart : Partrec fun v : List.Vector ℕ 2 ↦ (f v).map fun _ ↦ 0 :=
    Partrec.map hR (Computable.const 0).to₂
  simpa [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, f]
    using (codeOfPartrec'_spec (Nat.Partrec'.of_part hpart) (v := ![m, n]) (y := 0)).trans (by simp [f])

/-! ## Instantiating the seam over the concrete CNF coding `natCode`

`Epsilon0Complete` supplies the order-type half (`epsilon0_le_orderType_natCode : ε₀ ≤ orderType
(ltPull natCode)`) and `codeOfREPred₂` supplies the definability tool. The only remaining gap is that
the order `ltPull natCode` is r.e. — which is true (it is *decidable*: `NONote` has a `LinearOrder` via
`cmp`, and `natCode` is computable, `Computable.ofNat`), but mathlib provides no `Computable`/`Primrec`
instance for `ONote.cmp`. We disclose that single fact as an axiom and mark it the F-φ discharge target. -/

/-- **F-φ DISCHARGED (lap 28).** The order `natCode a < natCode b` on ℕ-codes is recursively
enumerable (in fact computable). Formerly the lone disclosed math axiom on the Thm 5.6 route; now a
machine-checked theorem — `GoodsteinPA.ONoteComp.rePred_ltPull_natCode` supplies the `Computable`
proof of CNF comparison via a structural strong recursion (the piece mathlib lacks). Its only
non-`[propext,choice,Quot.sound]` dependency is one 🟢 `native_decide` base-case witness. -/
theorem rePred_ltPull_natCode :
    REPred fun v : List.Vector ℕ 2 ↦ natCode (v.get 0) < natCode (v.get 1) :=
  GoodsteinPA.ONoteComp.rePred_ltPull_natCode

/-- The X-free `ℒₒᵣ`-`Semisentence` defining `natCode`'s order. -/
noncomputable def precφ : Semisentence ℒₒᵣ 2 :=
  codeOfREPred₂ fun a b ↦ natCode a < natCode b

lemma precφ_spec (m n : ℕ) : ℕ ⊧/![m, n] precφ ↔ natCode m < natCode n :=
  codeOfREPred₂_spec rePred_ltPull_natCode

/-- **The arithmetization seam, fully assembled** (modulo the one disclosed comparison axiom). Both
seam halves are now discharged: definability (`hprec`/`hprecXPos`, via `EpsilonOrder` + `precφ`/`hφ`)
and order type (`ge`, via `Epsilon0Complete`). -/
noncomputable def seam : Seam where
  lt := ltPull natCode
  φ := Rewriting.emb precφ
  hφ a b := by
    simp only [Semiformula.eval_emb]
    exact precφ_spec a b
  ge := epsilon0_le_orderType_natCode

end GoodsteinPA.SeamDefinability
