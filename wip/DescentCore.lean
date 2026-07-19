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
    push Not at hle
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

/-- **`evalNat`'s base-bump law (the substrate bridge).** Raising the evaluation base by one is
exactly the hereditary numeric base-change `bump (b+1)` applied to the value: for a `Canon b`/`NF`
notation, `evalNat (b+1) o = bump (b+1) (evalNat b o)`. Hence the §3 tower `T̂^{k+1}_ω(o) =
evalNat (k+1) o` is the iterated `bump` (`bump (k+1) ∘ ⋯ ∘ bump 2`) of `evalNat 1 o` — the precise
fact that lets the *internal* `ibump` substrate (`InternalBump`) realize `evalNat` inside a model `M`
without coding ONote evaluation separately. Two-step: round-trip `o = toONote (b+1) (evalNat b o)`
(`canon_round_trip`), then `evalNat_toONote`. -/
theorem evalNat_succ_base (b : ℕ) (hb : 2 ≤ b) {o : ONote} (hco : Canon b o) (hno : o.NF) :
    evalNat (b + 1) o = bump (b + 1) (evalNat b o) := by
  conv_lhs => rw [← canon_round_trip b hb o hco hno]
  exact evalNat_toONote (b + 1) (by omega) (evalNat b o)

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

@[simp] theorem C_one : C 1 = 1 := rfl

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
    simp [Ordinal.one_lt_omega0]
  | n + 1 => by
    have ih := repr_omegaStack_strictMono n
    rw [repr_omegaStack_succ, repr_omegaStack_succ]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 ih

/-! ## `C`-arithmetic for the Thm 3.5 tail terms `β_{K(n+1)+i} = ω·αₙ + (K-i)`

Thm 3.5's coefficient bound `C(βᵣ) ≤ r+1` rests on the fact that **multiplying by `ω` raises the
max-coefficient by at most 1** (Rathjen: "since multiplying by ω increases the coefficients by at most
one"). The mechanism is `1 + e` (the exponent shift `ω·ω^e = ω^{1+e}`) only bumping `C` by ≤ 1. Both
are clean structural `ONote` facts (no `NF`, no well-foundedness). -/

/-- Evaluate `1 + oadd e' n' a'`: if the leading exponent `e'` is `0` (a finite head) the head
coefficient grows by `1`; otherwise `1` is absorbed. (From `ONote.addAux`/`cmp`.) -/
theorem one_add_oadd (e' : ONote) (n' : ℕ+) (a' : ONote) :
    (1 : ONote) + ONote.oadd e' n' a' =
      if e' = 0 then ONote.oadd 0 (1 + n') a' else ONote.oadd e' n' a' := by
  rw [show (1 : ONote) = ONote.oadd 0 1 0 from rfl, ONote.oadd_add, ONote.zero_add]
  cases e' with
  | zero => simp [ONote.addAux, ONote.cmp]
  | oadd => simp [ONote.addAux, ONote.cmp]

/-- **`C(1 + e) ≤ C(e) + 1`** — adding `1` raises the max-coefficient by at most 1. -/
theorem C_one_add_le (e : ONote) : C (1 + e) ≤ C e + 1 := by
  cases e with
  | zero => decide
  | oadd e' n' a' =>
    rw [one_add_oadd]
    split
    · next h => subst h; simp only [C_oadd, C_zero, PNat.add_coe, PNat.one_coe]; omega
    · simp only [C_oadd]; omega

/-- `ω` as an `ONote` (`= ω^1·1 = oadd 1 1 0`). -/
def omegaO : ONote := ONote.oadd 1 1 0

/-- **`C(ω·α) ≤ C(α) + 1`** (Rathjen Thm 3.5: multiplying by `ω` bumps coefficients by ≤ 1). Induction
on the `ONote.mul` recursion: the `e₂=0` head case keeps `C` (coefficient `1·n₂`, head exponent `ω¹`);
the `e₂≠0` case shifts the exponent to `1+e₂` (bounded by `C_one_add_le`) and recurses into the tail
(bounded by the IH). -/
theorem C_omega_mul_le : ∀ α : ONote, C (omegaO * α) ≤ C α + 1
  | 0 => by simp [omegaO]
  | ONote.oadd e₂ n₂ a₂ => by
    have ih := C_omega_mul_le a₂
    rw [omegaO] at ih ⊢
    rw [ONote.oadd_mul]
    by_cases h : e₂ = 0
    · subst h
      simp only [↓reduceIte, C_oadd, C_zero, C_one, one_mul]
      have hn : (1 : ℕ) ≤ (n₂ : ℕ) := Nat.succ_le_of_lt n₂.pos
      omega
    · rw [if_neg h]
      simp only [C_oadd] at ih ⊢
      have h1 := C_one_add_le e₂
      have e1 : C e₂ ≤ max (max (C e₂) (n₂ : ℕ)) (C a₂) := le_max_of_le_left (le_max_left _ _)
      have e2 : (n₂ : ℕ) ≤ max (max (C e₂) (n₂ : ℕ)) (C a₂) := le_max_of_le_left (le_max_right _ _)
      have e3 : C a₂ ≤ max (max (C e₂) (n₂ : ℕ)) (C a₂) := le_max_right _ _
      refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega

/-- `C (ofNat m) = m` — the max-coefficient of a finite ordinal is its value. -/
@[simp] theorem C_ofNat (m : ℕ) : C (ONote.ofNat m) = m := by
  cases m with
  | zero => rfl
  | succ k => simp [ONote.ofNat, C, Nat.succPNat]

/-- `1 + e` is never `0` (its CNF always has a head term). -/
theorem one_add_ne_zero (e : ONote) : (1 : ONote) + e ≠ 0 := by
  cases e with
  | zero => decide
  | oadd e' n' a' => rw [one_add_oadd]; split <;> exact fun h => ONote.noConfusion h

/-- **`a` has no finite (exponent-`0`) summand**: every CNF term has a non-zero exponent. `ω·α`
always satisfies this (its exponents are all `1 + …`), so adding a finite tail to it never *merges*
into an existing coefficient — the key to the tight `C(ω·α + finite) = max(C(ω·α), finite)` bound. -/
def NoFin : ONote → Prop
  | 0 => True
  | ONote.oadd e _ r => e ≠ 0 ∧ NoFin r

@[simp] theorem NoFin_zero : NoFin 0 := trivial

theorem NoFin_oadd {e : ONote} {n : ℕ+} {r : ONote} (he : e ≠ 0) (hr : NoFin r) :
    NoFin (ONote.oadd e n r) := ⟨he, hr⟩

/-- **`ω·α` has no finite part.** Its head exponent is `1` (the `e₂=0` case) or `1+e₂` (the `e₂≠0`
case), both non-zero, and the tail recurses. -/
theorem noFin_omega_mul : ∀ α, NoFin (omegaO * α)
  | 0 => by simp [omegaO]
  | ONote.oadd e₂ n₂ a₂ => by
    rw [omegaO, ONote.oadd_mul]
    by_cases h : e₂ = 0
    · subst h; exact NoFin_oadd (by decide) NoFin_zero
    · rw [if_neg h]
      refine NoFin_oadd (one_add_ne_zero e₂) ?_
      rw [← omegaO]; exact noFin_omega_mul a₂

open Ordinal in
/-- **`C(a + n) ≤ max (C a) n`** for a finite `n` added to a `NoFin` (no-finite-part) `a`. Because
`a` has no exponent-`0` term, the finite `n` lands as a fresh bottom summand and never merges into an
existing coefficient. Structural induction mirroring `ONote.add_nfBelow`: the head `(e,n')` is
preserved (`addAux` takes its `gt` branch, since `a`'s tail `+ n` stays strictly below `repr e`) and
`C` of the tail is bounded by the IH. -/
theorem C_add_ofNat_le : ∀ {a : ONote}, a.NF → NoFin a → ∀ m : ℕ,
    C (a + ONote.ofNat m) ≤ max (C a) m
  | 0, _, _, m => by simp
  | ONote.oadd e n tail, hNF, hnf, m => by
    obtain ⟨he, htail⟩ := hnf
    have hNFtail : tail.NF := hNF.snd
    have ih := C_add_ofNat_le hNFtail htail m
    rw [ONote.oadd_add]
    -- `tail + ofNat m` is normal and strictly below `repr e`
    have hrepr1 : (1 : Ordinal) ≤ ONote.repr e := by
      cases e with
      | zero => exact absurd rfl he
      | oadd e'' n'' a'' =>
        exact le_trans (Order.one_le_iff_ne_zero.2 (opow_pos _ omega0_pos).ne')
          (ONote.omega0_le_oadd _ _ _)
    have hbX : ONote.NFBelow (tail + ONote.ofNat m) (ONote.repr e) :=
      ONote.add_nfBelow hNF.snd' ((ONote.nfBelow_ofNat m).mono hrepr1)
    cases hX : tail + ONote.ofNat m with
    | zero =>
      rw [hX] at ih
      simp only [ONote.addAux, C_oadd, C_zero] at ih ⊢
      have e1 : C e ≤ max (max (C e) (n : ℕ)) (C tail) := le_max_of_le_left (le_max_left _ _)
      have e2 : (n : ℕ) ≤ max (max (C e) (n : ℕ)) (C tail) := le_max_of_le_left (le_max_right _ _)
      refine Nat.max_le.mpr ⟨?_, ?_⟩ <;> omega
    | oadd e' n' a' =>
      have hNFe : e.NF := hNF.fst
      have hbXo := hX ▸ hbX
      have hNFe' : e'.NF := hbXo.fst
      have hlt : ONote.repr e' < ONote.repr e := hbXo.lt
      have hcmp : ONote.cmp e e' = Ordering.gt := by
        have hc := @ONote.cmp_compares e e' hNFe hNFe'
        rcases hco : ONote.cmp e e' with _ | _ | _
        · rw [hco] at hc; exact absurd (ONote.lt_def.1 hc) (not_lt.2 hlt.le)
        · rw [hco] at hc; exact absurd (congrArg ONote.repr hc) (ne_of_gt hlt)
        · rfl
      rw [hX] at ih
      simp only [ONote.addAux, hcmp, C_oadd] at ih ⊢
      have e1 : C e ≤ max (max (C e) (n : ℕ)) (C tail) := le_max_of_le_left (le_max_left _ _)
      have e2 : (n : ℕ) ≤ max (max (C e) (n : ℕ)) (C tail) := le_max_of_le_left (le_max_right _ _)
      have e3 : C tail ≤ max (max (C e) (n : ℕ)) (C tail) := le_max_right _ _
      refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨?_, ?_⟩, ?_⟩ <;> omega

/-- `NF` of `ω` as an `ONote`. -/
instance NF_omegaO : (omegaO).NF := by rw [omegaO]; exact ONote.NF.oadd_zero 1 1

/-- **Rathjen Thm 3.5 tail-term `C`-bound.** The tail block `β_{K(n+1)+i} = ω·αₙ + (K-i)` of the
`C`-bounded sequence satisfies `C(βᵣ) ≤ r+1` (here `r = K(n+1)+i`), given the slow bound
`C(αₙ) ≤ K(n+1)` (Rathjen `C(αₙ) ≤ |αₙ| ≤ K(n+1)`) and `i < K`. Combines `C_omega_mul_le`
("·ω bumps `C` by ≤1") with `C_add_ofNat_le` (the finite `K-i` never merges, since `ω·αₙ` is
`NoFin`): `C(ω·αₙ + (K-i)) ≤ max(C(αₙ)+1, K-i) ≤ K(n+1)+1 ≤ r+1`. -/
theorem C_betaTail_le {α : ONote} (hα : α.NF) {K n i : ℕ} (hi : i < K)
    (hCα : C α ≤ K * (n + 1)) :
    C (omegaO * α + ONote.ofNat (K - i)) ≤ K * (n + 1) + i + 1 := by
  have hNFmul : (omegaO * α).NF := ONote.mul_nf omegaO α
  have h1 := C_add_ofNat_le hNFmul (noFin_omega_mul α) (K - i)
  have h2 := C_omega_mul_le α
  have hb1 : C (omegaO * α) ≤ K * (n + 1) + 1 := by omega
  have hb2 : K - i ≤ K * (n + 1) := by
    have : K ≤ K * (n + 1) := Nat.le_mul_of_pos_right K (Nat.succ_pos n)
    omega
  omega

/-! ## Rathjen Thm 3.5 tail-term DESCENT `βᵣ₊₁ < βᵣ`

The other half of Thm 3.5: the constructed sequence strictly descends. Two cases (repr-based, cleaner
than the syntactic `C`): **within a block** (fixed `αₙ`, the finite part `K-i` shrinks as `r` grows) and
**across a block boundary** (`ω·αₙ + 1 > ω·αₙ₊₁ + K`, from `αₙ₊₁ < αₙ` since `ω` absorbs the finite `K`). -/

open Ordinal in
@[simp] theorem repr_omegaO : ONote.repr omegaO = ω := by
  rw [omegaO, ONote.repr]; simp

open Ordinal in
/-- **Within-block descent**: a larger finite tail gives a larger value (`ω·α + (p+1) > ω·α + p`). -/
theorem repr_betaTail_within (α : ONote) (hα : α.NF) (p : ℕ) :
    (omegaO * α + ONote.ofNat p).repr < (omegaO * α + ONote.ofNat (p + 1)).repr := by
  haveI := hα
  haveI : (omegaO * α).NF := ONote.mul_nf omegaO α
  rw [ONote.repr_add, ONote.repr_add, ONote.repr_ofNat, ONote.repr_ofNat]
  exact (add_lt_add_iff_left _).2 (show (↑p : Ordinal) < ↑(p + 1) by exact_mod_cast Nat.lt_succ_self p)

open Ordinal in
/-- **Block-boundary descent**: `ω·αₙ₊₁ + K < ω·αₙ` whenever `αₙ₊₁ ≺ αₙ`. The successor gap
`αₙ₊₁ + 1 ≤ αₙ` scales to `ω·αₙ₊₁ + ω ≤ ω·αₙ`, and the finite `K < ω` is absorbed. -/
theorem repr_betaTail_boundary {αNext α : ONote} (hαN : αNext.NF) (hα : α.NF)
    (hlt : αNext.repr < α.repr) (K : ℕ) :
    (omegaO * αNext + ONote.ofNat K).repr < (omegaO * α).repr := by
  haveI := hαN; haveI := hα
  rw [ONote.repr_add, ONote.repr_mul, ONote.repr_mul, ONote.repr_ofNat, repr_omegaO]
  -- goal : ω * repr αNext + K < ω * repr α
  have hsucc : ω * αNext.repr + ω ≤ ω * α.repr := by
    calc ω * αNext.repr + ω = ω * (Order.succ αNext.repr) := (mul_succ _ _).symm
      _ ≤ ω * α.repr := mul_le_mul_right (Order.succ_le_of_lt hlt) _
  exact lt_of_lt_of_le ((add_lt_add_iff_left _).2 (natCast_lt_omega0 K)) hsucc

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
  exact not_lt_zero hlt0

end GoodsteinPA.Dom
