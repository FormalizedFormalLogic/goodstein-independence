/-
# `DescentCore.lean` — E-core semantic bricks: `evalNat` order-monotonicity (Rathjen 2.3(iii))

The descent wall **E** factors (see `DESCENT-PLAN.md`) into the proof-translation **E-lift**
(`DescentLift.lean`, done) and **E-core** — Rathjen 2014 §3 "slowing down", whose workhorse is the
order-reflection of `T̂^b_ω` (= `Domination.evalNat`): for ordinals/notations with bounded
coefficients (`Canon`), `α < β ⇔ T̂(α) < T̂(β)` (Rathjen Lemma 2.2/2.3(iii)).

`Domination.lean` already proves the round-trip `canon_repr : toOrdinal (b+1) (evalNat b E) = repr E`
for `Canon`/`NF` notations. Since `toOrdinal (b+1)` is strictly monotone on `ℕ`
(`toOrdinal_mono_and_bound`), `evalNat b` therefore reflects and preserves the notation order
*exactly* on the `Canon` domain. This file records that reflection — the comparison fact Lemma 3.6's
inequality (6) runs on. Pure mathlib/ONote, `#print axioms`-clean, zero `Foundation` dependency.
-/
import GoodsteinPA.Domination

namespace GoodsteinPA.Dom

open ONote Ordinal

/-- `toOrdinal b` reflects strict order (it is strictly monotone on `ℕ`, hence an order embedding). -/
theorem toOrdinal_lt_iff (b : ℕ) (hb : 2 ≤ b) (m n : ℕ) :
    toOrdinal b m < toOrdinal b n ↔ m < n := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    rcases lt_or_eq_of_le hle with h' | h'
    · exact absurd ((toOrdinal_mono_and_bound b hb m).1 n h') (by simpa using h.le)
    · simp [h'] at h
  · exact (toOrdinal_mono_and_bound b hb n).1 m

/-- `toOrdinal b` reflects `≤`. -/
theorem toOrdinal_le_iff (b : ℕ) (hb : 2 ≤ b) (m n : ℕ) :
    toOrdinal b m ≤ toOrdinal b n ↔ m ≤ n := by
  rw [← not_lt, ← not_lt, toOrdinal_lt_iff b hb]

/-- **Rathjen Lemma 2.3(iii) (`evalNat` form).** On the `Canon`/`NF` domain, `evalNat b`
order-reflects: `evalNat b o < evalNat b p ↔ o.repr < p.repr` (equivalently `↔ o < p`). Immediate
from the round-trip `canon_repr` plus strict monotonicity of `toOrdinal (b+1)`. -/
theorem evalNat_lt_iff (b : ℕ) (hb : 2 ≤ b) {o p : ONote}
    (hco : Canon b o) (hcp : Canon b p) (hno : o.NF) (hnp : p.NF) :
    evalNat b o < evalNat b p ↔ o.repr < p.repr := by
  rw [← canon_repr b (by omega) o hco hno, ← canon_repr b (by omega) p hcp hnp]
  exact (toOrdinal_lt_iff (b + 1) (by omega) _ _).symm

/-- `evalNat b` order-reflects `≤` on the `Canon`/`NF` domain. -/
theorem evalNat_le_iff (b : ℕ) (hb : 2 ≤ b) {o p : ONote}
    (hco : Canon b o) (hcp : Canon b p) (hno : o.NF) (hnp : p.NF) :
    evalNat b o ≤ evalNat b p ↔ o.repr ≤ p.repr := by
  rw [← not_lt, ← not_lt, evalNat_lt_iff b hb hcp hco hnp hno]

/-! ## Rathjen's max-coefficient `C : ONote → ℕ` and its bridge to `Canon`

Rathjen 2014 states §3 in terms of `C(α)` = the highest integer coefficient in the complete CNF of `α`
(`C(0)=0`, `C(ω^{α₁}k₁+…) = max{C(αᵢ), kᵢ}`). The repo's `Domination.Canon b o` predicate ("every
coefficient `≤ b`") is exactly `C o ≤ b`; this bridge lets the §3 lemmas be stated with either. -/

/-- **Rathjen's max-coefficient** `C(α)` — the highest integer coefficient appearing anywhere in the
complete CNF of `α` (recursively through exponents and tails). -/
def C : ONote → ℕ
  | 0 => 0
  | ONote.oadd e n r => max (max (C e) (n : ℕ)) (C r)

@[simp] theorem C_zero : C 0 = 0 := rfl

@[simp] theorem C_oadd (e : ONote) (n : ℕ+) (r : ONote) :
    C (ONote.oadd e n r) = max (max (C e) (n : ℕ)) (C r) := rfl

/-- **`Canon` is `C ≤ b`.** The repo's coefficient-bound predicate `Canon b o` (every coefficient
`≤ b`) holds iff the max coefficient `C o ≤ b`. So Rathjen's `C(βₙ) ≤ n+1` is `Canon (n+1) (β n)`. -/
theorem Canon_iff_C_le (b : ℕ) (o : ONote) : Canon b o ↔ C o ≤ b := by
  induction o with
  | zero => exact iff_of_true (Canon_zero b) (by simp)
  | oadd e n r ihe ihr =>
    rw [Canon_oadd, C_oadd, ihe, ihr]; omega

/-- `Canon b o` from `C o ≤ b` (the forward bridge, the form §3 lemmas consume). -/
theorem Canon_of_C_le {b : ℕ} {o : ONote} (h : C o ≤ b) : Canon b o := (Canon_iff_C_le b o).2 h

/-- `evalNat` is strictly monotone in the notation order on the `Canon`/`NF` domain
(`o < p ⇒ evalNat b o < evalNat b p`). The `T̂` half of Rathjen's order isomorphism. -/
theorem evalNat_lt_of_lt (b : ℕ) (hb : 2 ≤ b) {o p : ONote}
    (hco : Canon b o) (hcp : Canon b p) (hno : o.NF) (hnp : p.NF) (h : o < p) :
    evalNat b o < evalNat b p :=
  (evalNat_lt_iff b hb hco hcp hno hnp).2 (ONote.lt_def.1 h)

/-! ## Rathjen's `ωₙ` tower (the `T̂ 3.5` slow-down scaffold)

Rathjen Thm 3.5 builds the first `K` terms of the `C`-bounded sequence from the tower `ω₀ = 1`,
`ωₙ₊₁ = ω^{ωₙ}` (`βⱼ = Σ_{i<K-j} ω_{s-i}`). Two facts about the tower are used: every `ωₙ` has
max-coefficient `C(ωₙ) = 1` (so the head terms are `Canon 1`), and the tower is strictly increasing.
Both are clean, non-vacuous `ONote` facts (no well-foundedness), recorded here as `§3` bricks. -/

/-- Rathjen's tower `ωₙ`: `ω₀ = 1`, `ωₙ₊₁ = ω^{ωₙ}` (= `oadd ωₙ 1 0`). -/
def omegaStack : ℕ → ONote
  | 0 => 1
  | n + 1 => ONote.oadd (omegaStack n) 1 0

@[simp] theorem omegaStack_zero : omegaStack 0 = 1 := rfl

@[simp] theorem omegaStack_succ (n : ℕ) :
    omegaStack (n + 1) = ONote.oadd (omegaStack n) 1 0 := rfl

/-- Every tower level is in normal form. -/
theorem omegaStack_NF : ∀ n, (omegaStack n).NF
  | 0 => by simpa using (inferInstance : ONote.NF 1)
  | n + 1 => by
    have := omegaStack_NF n
    exact ONote.NF.oadd_zero _ _

/-- **`C(ωₙ) = 1`** for all `n` (Rathjen Thm 3.5: "As `C(ωᵣ) = 1` for all `r`"). The base `ω₀ = 1`
has `C = 1`; each `ω^{ωₙ}` keeps the head coefficient `1` and recurses into the exponent. -/
@[simp] theorem C_omegaStack : ∀ n, C (omegaStack n) = 1
  | 0 => rfl
  | n + 1 => by rw [omegaStack_succ, C_oadd, C_omegaStack n]; rfl

/-- `repr ωₙ₊₁ = ω^{repr ωₙ}`. -/
theorem repr_omegaStack_succ (n : ℕ) :
    (omegaStack (n + 1)).repr = ω ^ (omegaStack n).repr := by
  rw [omegaStack_succ, ONote.repr]
  simp

/-- **The tower is strictly increasing**: `repr ωₙ < repr ωₙ₊₁`. Induction: base `repr 1 = 1 < ω =
repr ω₁`; step `repr ωₙ < repr ωₙ₊₁ ⟹ ω^{repr ωₙ} < ω^{repr ωₙ₊₁}` by strict monotonicity of `ω^·`. -/
theorem repr_omegaStack_strictMono : ∀ n, (omegaStack n).repr < (omegaStack (n + 1)).repr
  | 0 => by
    rw [repr_omegaStack_succ, omegaStack_zero, ONote.repr_one]
    simpa using Ordinal.one_lt_omega0
  | n + 1 => by
    have ih := repr_omegaStack_strictMono n
    rw [repr_omegaStack_succ, repr_omegaStack_succ]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 ih

/-! ## Rathjen Lemma 3.6 — the special Goodstein run from `T̂²_ω(β₀)` does not terminate

This is the **kernel of E-core** (see `DESCENT-PLAN.md`): from a descending ε₀-sequence with bounded
coefficients (`C(βₙ) ≤ n+1`, i.e. `Canon (n+1) (β n)`), the special Goodstein sequence seeded at
`m₀ = T̂²_ω(β₀) = evalNat 1 (β 0)` never reaches `0`, because `mₖ ≥ T̂^{k+2}_ω(βₖ) = evalNat (k+1) (β k)`
for all `k` (Rathjen's inequality (6)). The base-bump `S^{b}_{b+1}` is `bump b` (= `evalNat b ∘ toONote b`,
`evalNat_toONote`), and the special Goodstein step is `goodsteinSeq m (k+1) = bump (k+2) (·) - 1`.

**Honest framing (anti-fraud).** As a *Lean/ZFC* statement, the `∀ k` iteration and the non-termination
corollary have a **semantically unsatisfiable** hypothesis — there is no infinite strictly descending
sequence of ordinals (ε₀ is well-founded). Their independence force is therefore *zero on their own*;
the real content of Rathjen §3 is doing this construction **inside PA**, where well-foundedness is not
available — that is the arithmetization wall E-core(b). What is genuinely reusable here is the **finite,
non-vacuous** inductive step `ineq6_step`: it uses no well-foundedness and is exactly the Π₁ kernel the
PA-formalization encodes (one `evalNat` order-reflection per Goodstein step). -/

/-- **Rathjen inequality (6), the inductive step (the non-vacuous E-core kernel).** One special
Goodstein step (`bump (k+2) m - 1`, base `k+2 ↦ k+3`) taken from a value `m ≥ T̂^{k+2}_ω(βₖ)` lands
`≥ T̂^{k+3}_ω(β_{k+1})`, given `βₖ ≻ β_{k+1}` and the coefficient bounds `C(βₖ) ≤ k+1`, `C(β_{k+1}) ≤ k+2`.
Pure finite arithmetic on `ℕ`/`ONote`: the Goodstein step is `evalNat (k+2) ∘ toONote (k+2)` minus one
(`evalNat_toONote`), and the gap survives because `evalNat (k+2)` order-reflects on `Canon (k+2)`/`NF`
(`evalNat_lt_iff`). No well-foundedness; this is what the PA induction of Lemma 3.6 arithmetizes. -/
theorem ineq6_step (k : ℕ) {bk bk1 : ONote}
    (hNFk : bk.NF) (hNFk1 : bk1.NF)
    (hck : Canon (k + 1) bk) (hck1 : Canon (k + 2) bk1)
    (hdesc : bk1.repr < bk.repr)
    {m : ℕ} (hm : evalNat (k + 1) bk ≤ m) :
    evalNat (k + 2) bk1 ≤ bump (k + 2) m - 1 := by
  have hb2 : 2 ≤ k + 2 := by omega
  -- the base-bump `S^{k+2}_{k+3} m` is `evalNat (k+2) (toONote (k+2) m)` (Rathjen `T̂ ∘ T`)
  have hbump : bump (k + 2) m = evalNat (k + 2) (toONote (k + 2) m) :=
    (evalNat_toONote (k + 2) hb2 m).symm
  have hcδ : Canon (k + 2) (toONote (k + 2) m) := Canon_toONote (k + 2) hb2 m
  have hNFδ : (toONote (k + 2) m).NF := toONote_NF (k + 2) hb2 m
  have hδrepr : (toONote (k + 2) m).repr = toOrdinal (k + 2) m := repr_toONote (k + 2) hb2 m
  -- δ := T^{k+2}_ω(m) ≥ βₖ : apply `toOrdinal (k+2)` (monotone) to `m ≥ T̂^{k+2}_ω(βₖ)`, round-trip via canon_repr
  have hbkrepr : bk.repr ≤ (toONote (k + 2) m).repr := by
    rw [hδrepr]
    have hcr : toOrdinal (k + 1 + 1) (evalNat (k + 1) bk) = bk.repr :=
      canon_repr (k + 1) (by omega) bk hck hNFk
    rw [← hcr]
    exact (toOrdinal_le_iff (k + 2) hb2 _ _).2 hm
  -- δ ≥ βₖ ≻ β_{k+1}, so δ ≻ β_{k+1}; then evalNat (k+2) reflects the strict gap
  have hlt : bk1.repr < (toONote (k + 2) m).repr := lt_of_lt_of_le hdesc hbkrepr
  have hev : evalNat (k + 2) bk1 < evalNat (k + 2) (toONote (k + 2) m) :=
    (evalNat_lt_iff (k + 2) hb2 hck1 hcδ hNFk1 hNFδ).2 hlt
  rw [hbump]; omega

/-- **Rathjen inequality (6), iterated** (semantic shadow; vacuous hypotheses — see the section
docstring). For a descending coefficient-bounded sequence `β`, the special Goodstein run seeded at
`evalNat 1 (β 0) = T̂²_ω(β₀)` dominates `T̂^{k+2}_ω(βₖ)` at every step `k`. Induction on `k` via
`ineq6_step`; the base case is `goodsteinSeq m 0 = m = evalNat 1 (β 0)`. -/
theorem lemma36_ineq6 (β : ℕ → ONote) (hNF : ∀ n, (β n).NF)
    (hCanon : ∀ n, Canon (n + 1) (β n)) (hdesc : ∀ n, (β (n + 1)).repr < (β n).repr) :
    ∀ k, evalNat (k + 1) (β k) ≤ goodsteinSeq (evalNat 1 (β 0)) k := by
  intro k
  induction k with
  | zero => simp [goodsteinSeq]
  | succ k ih =>
    have hstep : goodsteinSeq (evalNat 1 (β 0)) (k + 1)
        = bump (k + 2) (goodsteinSeq (evalNat 1 (β 0)) k) - 1 := rfl
    rw [hstep]
    exact ineq6_step k (hNF k) (hNF (k + 1)) (hCanon k) (hCanon (k + 1)) (hdesc k) ih

/-- **Rathjen Lemma 3.6 (semantic shadow; vacuous hypotheses — see the section docstring).** The
special Goodstein sequence seeded at `T̂²_ω(β₀)` never reaches `0`, from inequality (6) plus
`T̂^{k+2}_ω(βₖ) > 0` (since `βₖ ≻ β_{k+1} ⪰ 0`). The PA-internal form of this implication is E-core(b). -/
theorem lemma36_nonterminating (β : ℕ → ONote) (hNF : ∀ n, (β n).NF)
    (hCanon : ∀ n, Canon (n + 1) (β n)) (hdesc : ∀ n, (β (n + 1)).repr < (β n).repr) :
    ∀ k, goodsteinSeq (evalNat 1 (β 0)) k ≠ 0 := by
  intro k hk
  have h6 := lemma36_ineq6 β hNF hCanon hdesc k
  rw [hk] at h6
  have hev0 : evalNat (k + 1) (β k) = 0 := Nat.le_zero.1 h6
  have hcr0 : (β k).repr = 0 := by
    have hcr : toOrdinal (k + 1 + 1) (evalNat (k + 1) (β k)) = (β k).repr :=
      canon_repr (k + 1) (by omega) (β k) (hCanon k) (hNF k)
    rw [hev0, toOrdinal_zero] at hcr
    exact hcr.symm
  have hlt0 : (β (k + 1)).repr < 0 := by rw [← hcr0]; exact hdesc k
  exact Ordinal.not_lt_zero _ hlt0

end GoodsteinPA.Dom
