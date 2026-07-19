/-
# Faithfulness bridge: γ's standard-model truth ↔ real Goodstein termination

**Designated audit surface (part 2 of the trust base).** This is the anti-vacuity
certificate of `EXPEDITION-PLAN` Phase 0.3. It ties the *syntactic* sentence
`goodsteinSentence` (`Encoding.lean`) to the *semantic* fact that the genuine Goodstein
process (`Defs.lean`, `native_decide`-anchored) terminates. Per the plan, "the whole value
of Phase 0 lives here": a `sorry`'d `𝗣𝗔 ⊬ γ` against an unfaithful `γ` is worthless.

The bridge factors exactly as the encoding route predicts (neither half is the heroic girder):
  (E) **Encoding correctness** — `codeOfREPred_spec`: Foundation's r.e.-predicate code is true
      in ℕ at `m` iff `goodsteinTerminates m`. This is supplied by Foundation, modulo the
      `REPred goodsteinTerminates` hypothesis (`Encoding.lean`'s `goodsteinTerminates_re`).
  (S) **Eval unfolding** — `Semiformula.eval_all`: `ℕ ⊧ₘ ∀⁰ φ ↔ ∀ x, ℕ ⊧/![x] φ`. Mechanical.

⚠️ **Do not weaken the RHS.** `∀ m, ∃ N, goodsteinSeq m N = 0` (over the audited `goodsteinSeq`
of `Defs.lean`) is the faithful statement of Goodstein's theorem; it is the spec the encoding
must match. The RHS is exactly `∀ m, goodstein_terminates m` of the verified, kernel-clean
termination theorem (`lean-formalizations` `Logic/Goodstein`), whose `Engine` descent is reused
in Phases 3–4 when `γ ⟹ Con(𝗣𝗔)` is proved.
-/
import GoodsteinPA.Encoding
import GoodsteinPA.Defs
import GoodsteinPA.InternalBridge
import GoodsteinPA.Compat

namespace GoodsteinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **Faithfulness bridge (anti-vacuity certificate).** The standard model `ℕ` satisfies the
encoded sentence `goodsteinSentence` iff every Goodstein sequence — the genuine hereditary-base
process of `Defs.lean` — reaches `0`. Proof: universal-closure eval (S) composed with
Foundation's encoding-correctness spec (E). Depends only on `goodsteinTerminates_re`. -/
theorem goodsteinSentence_faithful :
    (ℕ ⊧ₘ goodsteinSentence) ↔ ∀ m, ∃ N, goodsteinSeq m N = 0 := by
  unfold goodsteinSentence
  rw [models_iff]
  -- Eval the transparent Π₂ sentence `∀ m, ∃ N, !igoodsteinDef 0 m N` at ℕ: the `!igoodsteinDef`
  -- splice unfolds to `0 = igoodstein m N` via the `Defined` instance, then `igoodstein_nat`
  -- (`igoodstein = goodsteinSeq` on ℕ) rewrites to the locked RHS. No `codeOfREPred` opacity.
  simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Semiformula.eval_all,
    Semiformula.eval_ex, Semiformula.eval_substs, InternalPow.igoodstein_defined.iff,
    Matrix.cons_val_zero, Semiterm.val_operator₀, Structure.numeral_eq_numeral,
    ORingStructure.zero_eq_zero, Fin.succ_zero_eq_one, Matrix.cons_val_one, Semiterm.val_bvar,
    Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Fin.succ_one_eq_two, Matrix.cons_app_two,
    Function.comp_def]
  simp only [InternalPow.igoodstein_nat, eq_comm]

end GoodsteinPA
