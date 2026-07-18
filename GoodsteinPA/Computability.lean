/-
# Computability of the Goodstein function (Milestone M1 infrastructure)

`Encoding.goodsteinTerminates_re : REPred goodsteinTerminates` bottoms out at computability
of the hereditary-base `bump` (`Defs.lean`), which mathlib does not auto-derive because `bump`
(like `Nat.log`) is defined by well-founded recursion. This file supplies, by hand:

* `primrec_natLog`   — `Nat.log` is primitive recursive (its strong-recursion equation).
* `primrec_bump`     — `bump` is primitive recursive (strong recursion peeling the top power).
* `computable_goodsteinSeq` — `goodsteinSeq` is computable (structural recursion using `bump`).

Pure computability: each lemma typechecks or it doesn't — zero faithfulness risk. The route is
`nat_strong_rec` (course-of-values recursion): every recursive call lands at an index `< n`, so
the value is recoverable from `(List.range n).map (f ·)`.
-/
import Mathlib.Computability.Partrec
import Mathlib.Computability.RE
import Mathlib.Data.Nat.Log
import GoodsteinPA.Defs

namespace GoodsteinPA

open Primrec

/-- `Nat.pow` as a binary primitive-recursive function (mathlib only ships the low-level
`Nat.Primrec.pow`). -/
theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- Single defining equation for `Nat.log` covering all cases, suitable for strong recursion. -/
theorem natLog_rec (b n : ℕ) :
    Nat.log b n = if 1 < b ∧ b ≤ n then Nat.log b (n / b) + 1 else 0 := by
  split
  · rename_i h; exact Nat.log_of_one_lt_of_le h.1 h.2
  · rename_i h
    by_cases hb : 1 < b
    · exact Nat.log_of_lt (by simpa [hb] using h)
    · exact Nat.log_of_left_le_one (by omega) n

/-- **`Nat.log` is primitive recursive.** Strong recursion: `log b n` reduces to `log b (n/b)`
and `n/b < n` whenever `1 < b ≤ n`. -/
theorem primrec_natLog : Primrec₂ (Nat.log) := by
  refine Primrec.nat_strong_rec Nat.log (g := fun b L =>
      if 1 < b ∧ b ≤ L.length then (L[L.length / b]?).map (· + 1) else some 0) ?_ ?_
  · -- Primrec₂ g
    have hcond : PrimrecPred (fun p : ℕ × List ℕ => 1 < p.1 ∧ p.1 ≤ p.2.length) :=
      PrimrecPred.and
        (Primrec.nat_lt.comp (Primrec.const 1) Primrec.fst)
        (Primrec.nat_le.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))
    have hthen : Primrec (fun p : ℕ × List ℕ =>
        (p.2[p.2.length / p.1]?).map (· + 1)) := by
      refine Primrec.option_map
        (Primrec.list_getElem?.comp Primrec.snd
          (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst))
        ?_
      exact (Primrec.succ.comp Primrec.snd).to₂
    exact (Primrec.ite hcond hthen (Primrec.const (some 0))).to₂
  · -- correctness equation
    intro b n
    simp only [List.length_map, List.length_range]
    by_cases hn : n = 0
    · subst hn; simp only [Nat.log_zero_right, Nat.le_zero]
      rw [if_neg (by omega)]
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      by_cases hcond : 1 < b ∧ b ≤ n
      · have hlt : n / b < n := Nat.div_lt_self hpos hcond.1
        rw [if_pos hcond, List.getElem?_map, List.getElem?_range hlt]
        conv_rhs => rw [natLog_rec b n, if_pos hcond]
        rfl
      · rw [if_neg hcond]
        conv_rhs => rw [natLog_rec b n, if_neg hcond]

/-- **`bump` is primitive recursive.** Strong recursion peeling the top power: `bump b n`
calls `bump b (Nat.log b n)` and `bump b (n % b ^ Nat.log b n)`, both at indices `< n` (the
`decreasing_by` bounds of `Defs.bump`), so the value is recoverable from the table of earlier
values. Lookups use `Option.getD 0`; on the genuine table both succeed. -/
theorem primrec_bump : Primrec₂ bump := by
  refine Primrec.nat_strong_rec bump (g := fun b L =>
      if L.length = 0 then some 0
      else some (L.length / b ^ Nat.log b L.length *
        (b + 1) ^ ((L[Nat.log b L.length]?).getD 0) +
        (L[L.length % b ^ Nat.log b L.length]?).getD 0)) ?_ ?_
  · -- Primrec₂ g
    have pn : Primrec (fun p : ℕ × List ℕ => p.2.length) :=
      Primrec.list_length.comp Primrec.snd
    have pe : Primrec (fun p : ℕ × List ℕ => Nat.log p.1 p.2.length) :=
      primrec_natLog.comp Primrec.fst pn
    have ppow : Primrec (fun p : ℕ × List ℕ => p.1 ^ Nat.log p.1 p.2.length) :=
      primrec_natPow.comp Primrec.fst pe
    have pbe : Primrec (fun p : ℕ × List ℕ => (p.2[Nat.log p.1 p.2.length]?).getD 0) :=
      Primrec.option_getD_default.comp (Primrec.list_getElem?.comp Primrec.snd pe)
    have pidx2 : Primrec (fun p : ℕ × List ℕ => p.2.length % p.1 ^ Nat.log p.1 p.2.length) :=
      Primrec.nat_mod.comp pn ppow
    have pbr : Primrec (fun p : ℕ × List ℕ =>
        (p.2[p.2.length % p.1 ^ Nat.log p.1 p.2.length]?).getD 0) :=
      Primrec.option_getD_default.comp (Primrec.list_getElem?.comp Primrec.snd pidx2)
    have pbase1 : Primrec (fun p : ℕ × List ℕ =>
        (p.1 + 1) ^ ((p.2[Nat.log p.1 p.2.length]?).getD 0)) :=
      primrec_natPow.comp (Primrec.succ.comp Primrec.fst) pbe
    have pdiv : Primrec (fun p : ℕ × List ℕ => p.2.length / p.1 ^ Nat.log p.1 p.2.length) :=
      Primrec.nat_div.comp pn ppow
    have helse : Primrec (fun p : ℕ × List ℕ => some (p.2.length / p.1 ^ Nat.log p.1 p.2.length *
        (p.1 + 1) ^ ((p.2[Nat.log p.1 p.2.length]?).getD 0) +
        (p.2[p.2.length % p.1 ^ Nat.log p.1 p.2.length]?).getD 0)) :=
      Primrec.option_some.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp pdiv pbase1) pbr)
    have hcond : PrimrecPred (fun p : ℕ × List ℕ => p.2.length = 0) :=
      Primrec.eq.comp pn (Primrec.const 0)
    exact (Primrec.ite hcond (Primrec.const (some 0)) helse).to₂
  · -- correctness equation
    intro b n
    simp only [List.length_map, List.length_range]
    by_cases hn : n = 0
    · subst hn; simp; rw [bump.eq_def]; simp
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hlt : Nat.log b n < n := Nat.log_lt_self b hn
      have hbpos : 0 < b ^ Nat.log b n := by
        rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · subst hb0; simp [Nat.log_zero_left]
        · exact Nat.pow_pos hbpos
      have hmod : n % b ^ Nat.log b n < n :=
        lt_of_lt_of_le (Nat.mod_lt _ hbpos) (Nat.pow_log_le_self b hn)
      rw [if_neg (by simpa using hn)]
      rw [List.getElem?_map, List.getElem?_range hlt,
          List.getElem?_map, List.getElem?_range hmod]
      simp only [Option.map_some, Option.getD_some]
      conv_rhs => rw [bump.eq_def]
      simp [hn]

/-- `bump` as a `Computable₂` (from the primitive-recursive proof). -/
theorem computable_bump : Computable₂ bump := primrec_bump.to_comp

/-- **`goodsteinSeq` is primitive recursive.** Structural (primitive) recursion on the step
index, each step applying the primitive-recursive `bump` and subtracting one. -/
theorem primrec_goodsteinSeq : Primrec₂ goodsteinSeq := by
  have hh : Primrec₂ (fun (_ : ℕ × ℕ) (p : ℕ × ℕ) => bump (p.1 + 2) p.2 - 1) := by
    have h : Primrec (fun q : (ℕ × ℕ) × (ℕ × ℕ) => bump (q.2.1 + 2) q.2.2 - 1) := by
      refine Primrec.nat_sub.comp ?_ (Primrec.const 1)
      refine primrec_bump.comp ?_ ?_
      · exact Primrec.succ.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      · exact Primrec.snd.comp Primrec.snd
    exact h
  have hrec := Primrec.nat_rec' (f := fun a : ℕ × ℕ => a.2) (g := fun a : ℕ × ℕ => a.1)
    (h := fun (_ : ℕ × ℕ) (p : ℕ × ℕ) => bump (p.1 + 2) p.2 - 1)
    Primrec.snd Primrec.fst hh
  refine hrec.of_eq ?_
  rintro ⟨m, k⟩
  induction k with
  | zero => rfl
  | succ k ih => simp only [goodsteinSeq, base]; rw [← ih]

/-- `goodsteinSeq` as a `Computable₂`. -/
theorem computable_goodsteinSeq : Computable₂ goodsteinSeq := primrec_goodsteinSeq.to_comp

end GoodsteinPA
