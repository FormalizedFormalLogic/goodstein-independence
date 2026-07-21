/-
# Goodstein.Dom — Growth
-/
module

public import GoodsteinPA.ToMathlib.Goodstein.Domination.Sequence

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

/-
# The semantic bridge `toOrdinal` ↔ `ONote.repr`

The Goodstein termination proof (`Sequence.lean`) maps each Goodstein term to
an ordinal `< ε₀` via `toOrdinal b n` — read `n` in hereditary base `b`, replace `b` by `ω`.
That ordinal is exactly the `ONote.repr` of the Cantor-normal-form notation of `n` in base
`b`. This file builds that notation, `toONote b n`, and proves the bridge

  `repr (toONote b n) = toOrdinal b n`  (`repr_toONote`)   and   `(toONote b n).NF`.

With the bridge, the ε₀-descent (`seqOrd_step`) is expressed on the
*computable* ordinal notations `ONote`, the home of the fast-growing growth theory
(`ToMathlib/FastGrowing/*`) — the prerequisite for the growth theorem
(`goodsteinLength` tracks `fastGrowingε₀`).
-/



/-- The ordinal **notation** whose `repr` is `Engine.toOrdinal b n`: the Cantor normal form
of `n` written in base `b` with the base read as `ω`. Mirrors `toOrdinal`'s recursion
(peel the top power `b^(log b n)`), keeping everything computable. -/
def toONote (b : ℕ) (n : ℕ) : ONote :=
  if h : n = 0 then 0
  else
    have _hn : n ≠ 0 := h
    oadd (toONote b (Nat.log b n)) (n / b ^ Nat.log b n).toPNat'
        (toONote b (n % b ^ Nat.log b n))
termination_by n
decreasing_by
  · exact Nat.log_lt_self b h
  · have hb : 0 < b ^ Nat.log b n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0; simp [Nat.log_zero_left]
      · exact Nat.pow_pos hbpos
    exact lt_of_lt_of_le (Nat.mod_lt _ hb) (Nat.pow_log_le_self b h)

@[simp] lemma toONote_zero (b : ℕ) : toONote b 0 = 0 := by rw [toONote]; simp

/-- **The bridge (repr side).** `repr (toONote b n) = toOrdinal b n`: the notation really does
represent the engine's ordinal. Structural induction mirroring `toOrdinal_pos`. -/
theorem repr_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ n, (toONote b n).repr = toOrdinal b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have hc_pos : 0 < n / b ^ Nat.log b n := Nat.div_pos hbe_le hbe_pos
      rw [toONote, dif_neg hn, toOrdinal_pos b n hn, ONote.repr, ih _ hlog, ih _ hr_lt_n]
      congr 2
      exact_mod_cast PNat.toPNat'_coe hc_pos

/-- **The bridge (normal-form side).** `toONote b n` is a genuine normal-form notation. The
only nontrivial obligation is the leading-exponent ordering of each `oadd`, i.e. the tail's
ordinal sits below `ω^(leading exponent)` — exactly the remainder bound inside
`Engine.toOrdinal_mono_and_bound` (`toOrdinal b r < ω^(toOrdinal b e')` when `r < b^e'`),
reconstructed here from the public monotonicity + bound. -/
theorem toONote_NF (b : ℕ) (hb : 2 ≤ b) : ∀ n, (toONote b n).NF := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · rw [toONote_zero]; exact NF.zero
    · have hb1 : 1 < b := by omega
      have hlog : Nat.log b n < n := Nat.log_lt_self b hn
      have hbe_pos : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hbe_pos
      have hr_lt_n : n % b ^ Nat.log b n < n := lt_of_lt_of_le hr_lt hbe_le
      have hbound : toOrdinal b (n % b ^ Nat.log b n) < ω ^ toOrdinal b (Nat.log b n) := by
        rcases eq_or_ne (n % b ^ Nat.log b n) 0 with hr0 | hr0
        · rw [hr0, toOrdinal_zero]; exact opow_pos _ omega0_pos
        · have hlogr : Nat.log b (n % b ^ Nat.log b n) < Nat.log b n :=
            (Nat.log_lt_iff_lt_pow hb1 hr0).2 hr_lt
          have hmono : toOrdinal b (Nat.log b (n % b ^ Nat.log b n)) < toOrdinal b (Nat.log b n) :=
            (toOrdinal_mono_and_bound b hb (Nat.log b n)).1 _ hlogr
          refine ((toOrdinal_mono_and_bound b hb (n % b ^ Nat.log b n)).2 hr0).trans_le
            (opow_le_opow_right omega0_pos ?_)
          rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hmono
      rw [toONote, dif_neg hn]
      refine NF.oadd (ih _ hlog) _ (NF.below_of_lt' ?_ (ih _ hr_lt_n))
      rw [repr_toONote b hb, repr_toONote b hb]; exact hbound

/-! ### The Goodstein descent, expressed on `ONote`

With the bridge in hand, the ordinal value `seqOrd m k` (`Sequence.lean`) becomes a computable
notation `seqONote m k`, and the strict ε₀-descent `seqOrd_step` becomes a strict
`ONote` `<`-descent. The Goodstein termination descent now lives on the same `ONote` where the
fast-growing growth theory (`ToMathlib/FastGrowing/*`) does — the bridge that the growth
theorem below crosses. -/

/-- The `k`-th Goodstein term as an ordinal **notation** (read in its base `k+2`). -/
def seqONote (m k : ℕ) : ONote := toONote (k + 2) (goodsteinSeq m k)

lemma seqONote_NF (m k : ℕ) : (seqONote m k).NF := toONote_NF (k + 2) (by omega) _

/-- `repr (seqONote m k) = Engine.seqOrd m k`: the notation carries the engine's ordinal. -/
lemma repr_seqONote (m k : ℕ) : (seqONote m k).repr = seqOrd m k :=
  repr_toONote (k + 2) (by omega) _

/-- **The Goodstein descent on `ONote`.** While the term is nonzero, one Goodstein step
strictly lowers the notation: `seqONote m (k+1) < seqONote m k`. Transported from
`Engine.seqOrd_step` through the `repr` bridge. -/
lemma seqONote_lt (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    seqONote m (k + 1) < seqONote m k := by
  rw [lt_def, repr_seqONote, repr_seqONote]
  exact seqOrd_step m k h

/-- `toONote b n = 0 ↔ n = 0`: the notation vanishes exactly when its argument does (a
nonzero argument produces an `oadd`, which is positive). -/
lemma toONote_eq_zero_iff (b n : ℕ) : toONote b n = 0 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, toONote_zero]⟩
  by_contra hn
  rw [toONote, dif_neg hn] at h
  exact absurd h (oadd_pos _ _ _).ne'

/-- `seqONote m k = 0 ↔ goodsteinSeq m k = 0`: the notation hits `0` exactly at termination.
Hence the ONote descent `seqONote m 0 > seqONote m 1 > …` has length `goodsteinLength m` —
the connection `goodsteinLength` ↔ ε₀-descent that the growth theorem below turns into a
Hardy growth bound. -/
lemma seqONote_eq_zero_iff (m k : ℕ) : seqONote m k = 0 ↔ goodsteinSeq m k = 0 :=
  toONote_eq_zero_iff (k + 2) (goodsteinSeq m k)

/-- The ONote descent reaches `0` exactly at index `goodsteinLength m`. -/
lemma seqONote_goodsteinLength (m : ℕ) : seqONote m (goodsteinLength m) = 0 :=
  (seqONote_eq_zero_iff m (goodsteinLength m)).2 (goodsteinSeq_goodsteinLength m)

/-- Before `goodsteinLength m` the descent is strictly positive. So `goodsteinLength m` is
*precisely* the length of the strict `ONote` descent `seqONote m 0 > … > 0` — the quantity
the growth theorem below identifies with a Hardy value of `seqONote m 0`. -/
lemma seqONote_ne_zero_of_lt (m : ℕ) {k : ℕ} (h : k < goodsteinLength m) :
    seqONote m k ≠ 0 :=
  fun hz => goodsteinSeq_ne_zero_of_lt h ((seqONote_eq_zero_iff m k).1 hz)

/-! ## The growth theorem: `goodsteinLength m = H_{seqONote m 0}(2) − 2`

The crown jewel. The Hardy hierarchy "counts the steps" of a unit-decrement ordinal descent
where the *argument* (= the Goodstein base) grows by one at each step. The bridge is the
**Cichoń correspondence**: one Goodstein step is exactly one budget-incrementing Hardy step
(`hstep`) on the notation. Concretely, on `toONote` (base `b`, value `p ≠ 0`):

  `hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`   (`hstep_toONote`)

i.e. "descend the fundamental-sequence tree of `p`'s notation once at argument `b`" equals
"bump the base `b ↦ b+1` and subtract one" — the operation the Goodstein step performs.
Combined with the intrinsic Hardy step invariant `hardy_hstep` (`H_o(n) = H_{hstep o n}(n+1)`,
proved in `ToMathlib/Hardy/Structure.lean`), the Hardy value `H_{seqONote m k}(k+2)` is
**constant** along the whole Goodstein descent, so telescoping from `k = 0` to
`k = goodsteinLength m` (where the notation is `0` and `H_0(N) = N`) yields
`H_{seqONote m 0}(2) = goodsteinLength m + 2`.

This is the formal "Goodstein grows like the Hardy/fast-growing hierarchy" — the growth
content behind Kirby–Paris independence; this file pins the Goodstein length itself to a
Hardy value. -/

/-- **Notation invariance under `bump`.** The ordinal *notation* of `n` is unchanged by a
hereditary base bump: `toONote (b+1) (bump b n) = toONote b n`. Both are normal-form notations
with the same `repr` (the bump invariance `toOrdinal_bump` at the ordinal level), so they are
equal by `repr_inj`. This is the notation-level companion of `Engine.toOrdinal_bump`. -/
lemma toONote_bump (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    toONote (b + 1) (bump b n) = toONote b n := by
  haveI := toONote_NF (b + 1) (by omega) (bump b n)
  haveI := toONote_NF b hb n
  rw [← repr_inj, repr_toONote (b + 1) (by omega), repr_toONote b hb, toOrdinal_bump b hb]

/-- **Constructor form of `toONote`.** When `1 ≤ c < b` and `s < b^e`, the base-`b` notation
of `c·b^e + s` is `oadd (toONote b e) c (toONote b s)` — `c·b^e + s` already presents the
leading Cantor term, so `log`, `div`, `mod` read off `e`, `c`, `s`. -/
lemma toONote_oadd (b : ℕ) (hb : 2 ≤ b) {c e s : ℕ} (hc : 1 ≤ c) (hcb : c < b)
    (hs : s < b ^ e) : toONote b (c * b ^ e + s) = oadd (toONote b e) ⟨c, hc⟩ (toONote b s) := by
  have hbe_pos : 0 < b ^ e := Nat.pow_pos (by omega)
  have hn0 : c * b ^ e + s ≠ 0 := by positivity
  have hlow : c * b ^ e + s < b ^ (e + 1) := by
    calc c * b ^ e + s < c * b ^ e + b ^ e := by omega
      _ = (c + 1) * b ^ e := by ring
      _ ≤ b * b ^ e := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ (e + 1) := by rw [pow_succ]; ring
  have hge : b ^ e ≤ c * b ^ e + s :=
    (Nat.le_mul_of_pos_left (b ^ e) hc).trans (Nat.le_add_right _ _)
  have hlog : Nat.log b (c * b ^ e + s) = e := Nat.log_eq_of_pow_le_of_lt_pow hge hlow
  have hdiv : (c * b ^ e + s) / b ^ e = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbe_pos, Nat.div_eq_of_lt hs, Nat.zero_add]
  have hmod : (c * b ^ e + s) % b ^ e = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  rw [toONote, dif_neg hn0, hlog, hdiv, hmod]
  congr 1
  exact PNat.coe_injective (by simpa using PNat.toPNat'_coe hc)

/-- Single-digit notation: for `1 ≤ d < b`, `toONote b d = oadd 0 ⟨d,_⟩ 0` (the finite
ordinal `d`). Special case of `toONote_oadd` with exponent and remainder zero. -/
lemma toONote_single (b : ℕ) (hb : 2 ≤ b) {d : ℕ} (hd1 : 1 ≤ d) (hdb : d < b) :
    toONote b d = oadd 0 ⟨d, hd1⟩ 0 := by
  simpa using toONote_oadd b hb hd1 hdb (show (0 : ℕ) < b ^ 0 by simp)

/-- `fundamentalSequence` of `oadd 0 C 0` (a finite ordinal `C`): always a successor —
predecessor `0` when `C = 1`, else `oadd 0 (C-1) 0`. Read off the definition's nested match. -/
lemma fundamentalSequence_oadd_zero_zero (C : ℕ+) :
    fundamentalSequence (oadd 0 C 0) =
      match C.natPred with
      | 0 => Sum.inl (some 0)
      | j + 1 => Sum.inl (some (oadd 0 j.succPNat 0)) := by
  conv_lhs => rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl]
  rcases C.natPred with _ | j <;> rfl

/-- **The `r = 0`, `L = 0` (finite) base case of the Cichoń step.** For a single digit
`1 ≤ c < b`, one Hardy step on `oadd 0 c 0` (the finite ordinal `c`) is the finite notation
of `c − 1` in base `b+1`: `hstep (oadd 0 c 0) b = toONote (b+1) (c−1)`. `oadd 0 c 0` is a
successor, so the step is a single decrement. -/
lemma hstep_oadd_zero_zero (b : ℕ) (hb : 2 ≤ b) (c : ℕ) (hc1 : 1 ≤ c) (hcb : c < b) :
    hstep (oadd 0 ⟨c, hc1⟩ 0) b = toONote (b + 1) (c - 1) := by
  have hnp : PNat.natPred ⟨c, hc1⟩ = c - 1 := PNat.natPred_eq_pred hc1
  rcases eq_or_ne c 1 with rfl | hc2
  · rw [hstep_succ _ (by rw [fundamentalSequence_oadd_zero_zero, hnp]; rfl)]; simp
  · have hfs : fundamentalSequence (oadd 0 ⟨c, hc1⟩ 0)
        = Sum.inl (some (oadd 0 (c - 2).succPNat 0)) := by
      rw [fundamentalSequence_oadd_zero_zero, hnp, show c - 1 = (c - 2) + 1 from by omega]
    rw [hstep_succ _ hfs, toONote_single (b + 1) (by omega) (show 1 ≤ c - 1 by omega) (by omega)]
    show oadd 0 (c - 2).succPNat 0 = oadd 0 ⟨c - 1, by omega⟩ 0
    congr 1
    apply PNat.coe_injective
    change (c - 2) + 1 = c - 1
    omega

/-- Helper for the coefficient peel: for `E ≠ 0`, the fundamental sequence of `oadd E 1 0`
is some `inr g`, and that of `oadd E ⟨k+2⟩ 0` wraps it as `fun i => oadd E ⟨k+1⟩ (g i)`.
Read off the two non-`inl none` branches of `fundamentalSequence (oadd E · 0)` (tail `0`,
`natPred` `0` resp. `k+1`). -/
lemma fundSeq_oadd_coeff (E : ONote) (hE : E ≠ 0) (k : ℕ) :
    ∃ g, fundamentalSequence (oadd E 1 0) = Sum.inr g ∧
      fundamentalSequence (oadd E ⟨k + 2, by omega⟩ 0)
        = Sum.inr (fun i => oadd E k.succPNat (g i)) := by
  rcases e : fundamentalSequence E with (_ | E') | f
  · exact absurd ((fundamentalSequenceProp_inl_none E).1 (e ▸ fundamentalSequence_has_prop E)) hE
  · refine ⟨fun i => oadd E' i.succPNat 0, ?_, ?_⟩ <;>
      · rw [fundamentalSequence]
        simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, e]
        rfl
  · refine ⟨fun i => oadd (f i) 1 0, ?_, ?_⟩ <;>
      · rw [fundamentalSequence]
        simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, e]
        rfl

/-- **Lemma A (coefficient peel).** For `E ≠ 0` and `c ≥ 2`, one Hardy step on `oadd E c 0`
peels the coefficient to `c-1` and leaves a Hardy step on `oadd E 1 0`:
`hstep (oadd E ⟨c⟩ 0) b = oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`. The descent through the
limit `oadd E ⟨c⟩ 0` lands on `oadd E ⟨c-1⟩ (g b)`, whose nonzero tail `g b` peels off
(`hstep_oadd_tail`) leaving exactly `hstep (oadd E 1 0) b = hstep (g b) b`. -/
lemma hstep_oadd_coeff (b : ℕ) {E : ONote} (hE : E ≠ 0) {c : ℕ} (hc : 2 ≤ c)
    (hc1 : 1 ≤ c) :
    hstep (oadd E ⟨c, hc1⟩ 0) b = oadd E ⟨c - 1, by omega⟩ (hstep (oadd E 1 0) b) := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 2 := ⟨c - 2, by omega⟩
  obtain ⟨g, h1, hc2⟩ := fundSeq_oadd_coeff E hE k
  have hgb : g b ≠ 0 := fundamentalSequence_inr_ne_zero h1 b
  have hcoe : (⟨k + 2, hc1⟩ : ℕ+) = ⟨k + 2, by omega⟩ := rfl
  rw [hcoe, hstep_limit _ hc2, hstep_limit _ h1]
  dsimp only
  rw [hstep_oadd_tail E k.succPNat b (g b) hgb]
  congr 1

/-- `evalNat b o` evaluates the ordinal notation `o` at `ω ↦ b+1`: it reads `repr o`'s Cantor
normal form as a base-`(b+1)` numeral. This is the natural-number "size" the borrowing
predecessor (`hstep_oadd_one_zero`) targets: `hstep (oadd E 1 0) b` is the all-digits-`b`
notation of `(b+1)^(evalNat b E) − 1`. -/
def evalNat (b : ℕ) : ONote → ℕ
  | 0 => 0
  | oadd e n r => (n : ℕ) * (b + 1) ^ evalNat b e + evalNat b r

@[simp] lemma evalNat_zero (b : ℕ) : evalNat b 0 = 0 := rfl

lemma evalNat_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    evalNat b (oadd e n r) = (n : ℕ) * (b + 1) ^ evalNat b e + evalNat b r := rfl

/-- **`evalNat` reconstructs `bump`.** Evaluating the base-`b` notation `toONote b L` at
`ω ↦ b+1` gives exactly the hereditary base-bump `bump b L`. Strong induction on `L`,
mirroring `bump`'s own recursion. Hence the borrowing answer for `E = toONote b L`,
`(b+1)^(evalNat b E) − 1`, is exactly `(b+1)^(bump b L) − 1`. -/
lemma evalNat_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ L, evalNat b (toONote b L) = bump b L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases eq_or_ne L 0 with rfl | hL
    · simp
    · have hlog : Nat.log b L < L := Nat.log_lt_self b hL
      have hbe_pos : 0 < b ^ Nat.log b L := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b L ≤ L := Nat.pow_log_le_self b hL
      have hr_lt : L % b ^ Nat.log b L < L :=
        lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have hc_pos : 0 < L / b ^ Nat.log b L := Nat.div_pos hbe_le hbe_pos
      rw [toONote, dif_neg hL, evalNat_oadd, ih _ hlog, ih _ hr_lt, bump_pos b L hL]
      congr 2
      exact_mod_cast PNat.toPNat'_coe hc_pos

/-- **`evalNat` tracks a successor step.** If `fundamentalSequence E = some E'` (i.e. `E` is the
successor of `E'`), then `evalNat b E = evalNat b E' + 1`. Structural recursion on `E`, casing
the `fundamentalSequence` successor branches. -/
lemma evalNat_succ (b : ℕ) : ∀ {E E' : ONote}, fundamentalSequence E = Sum.inl (some E') →
    evalNat b E = evalNat b E' + 1 := by
  intro E
  induction E with
  | zero => intro E' h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r iha ihr =>
    intro E' h
    rw [fundamentalSequence] at h
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0: inner match on (fundamentalSequence a, m.natPred)
      rw [hr] at h
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0
        rw [ha] at h
        rcases hm : m.natPred with _ | k
        · -- m = 1, E' = 0
          rw [hm] at h
          obtain rfl : (0:ONote) = E' := by simpa using h
          have hrz : r = 0 := (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
          have haz : a = 0 := (fundamentalSequenceProp_inl_none a).1 (ha ▸ fundamentalSequence_has_prop a)
          have hm1 : (m : ℕ) = 1 := by
            have := PNat.natPred_add_one m; omega
          subst hrz; subst haz
          simp [evalNat_oadd, hm1]
        · -- m = k+2, E' = oadd 0 (k.succPNat) 0
          rw [hm] at h
          obtain rfl : oadd 0 k.succPNat 0 = E' := by simpa using h
          have hrz : r = 0 := (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
          have haz : a = 0 := (fundamentalSequenceProp_inl_none a).1 (ha ▸ fundamentalSequence_has_prop a)
          have hmk : (m : ℕ) = k + 2 := by
            have := PNat.natPred_add_one m; omega
          subst hrz; subst haz
          simp only [evalNat_oadd, evalNat_zero, Nat.succPNat_coe, pow_zero, mul_one, Nat.add_zero]
          omega
      · -- a successor → fundamentalSequence E = inr, contradicts h
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a limit → fundamentalSequence E = inr, contradicts h
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
    · -- r successor: E' = oadd a m r', recurse on r
      rw [hr] at h
      obtain rfl : oadd a m r' = E' := by simpa using h
      have := ihr hr
      simp only [evalNat_oadd]; omega
    · -- r limit → fundamentalSequence E = inr, contradicts h
      rw [hr] at h; simp at h

/-- **`evalNat` is fixed at the index `b` of a fundamental sequence.** If `E` is a limit with
`fundamentalSequence E = inr f`, then `evalNat b (f b) = evalNat b E`. The descent's coefficient
`b+1` (from `(b).succPNat`) is exactly what makes the base-`(b+1)` evaluation land back on
`evalNat b E`. Structural recursion on `E`; the successor sub-branches use `evalNat_succ`. -/
lemma evalNat_fundSeq (b : ℕ) : ∀ {E : ONote} {f : ℕ → ONote},
    fundamentalSequence E = Sum.inr f → evalNat b (f b) = evalNat b E := by
  intro E
  induction E with
  | zero => intro f h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r iha ihr =>
    intro f h
    rw [fundamentalSequence] at h
    have hbsucc : ((b.succPNat : ℕ+) : ℕ) = b + 1 := by simp [Nat.succPNat]
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0
      rw [hr] at h
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0: fundamentalSequence E is `inl`, contradicts h
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a successor (pred a'): uses evalNat_succ on a
        rw [ha] at h
        have hsa : evalNat b a = evalNat b a' + 1 := evalNat_succ b ha
        have hrz : r = 0 :=
          (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
        subst hrz
        rcases hm : m.natPred with _ | k
        · -- m = 1
          rw [hm] at h
          obtain rfl : (fun i => oadd a' i.succPNat 0) = f := by simpa using h
          have hm1 : (m : ℕ) = 1 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, hbsucc, Nat.add_zero, hm1,
            one_mul, hsa, pow_succ]
          ring
        · -- m = k+2
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd a' i.succPNat 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, hbsucc, Nat.add_zero, Nat.succPNat_coe, hmk,
            hsa, pow_succ, Nat.succ_eq_add_one]
          ring
      · -- a limit (fund seq p): uses evalNat_fundSeq on a
        rw [ha] at h
        have hpa : evalNat b (p b) = evalNat b a := iha ha
        have hrz : r = 0 :=
          (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
        subst hrz
        rcases hm : m.natPred with _ | k
        · -- m = 1
          rw [hm] at h
          obtain rfl : (fun i => oadd (p i) 1 0) = f := by simpa using h
          have hm1 : (m : ℕ) = 1 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, Nat.add_zero, hm1, one_mul, hpa,
            PNat.one_coe]
        · -- m = k+2
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd (p i) 1 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          simp only [evalNat_oadd, evalNat_zero, Nat.add_zero, Nat.succPNat_coe, hmk, hpa,
            Nat.succ_eq_add_one]
          push_cast
          ring
    · -- r successor → fundamentalSequence E is `inl`, contradicts h
      rw [hr] at h; simp at h
    · -- r limit: recurse on r
      rw [hr] at h
      obtain rfl : (fun i => oadd a m (g i)) = f := by simpa using h
      have hgr : evalNat b (g b) = evalNat b r := ihr hr
      simp only [evalNat_oadd, hgr]

/-- Predecessor of a finite successor `oadd 0 ⟨c⟩ 0` (= the ordinal `c`) at any argument:
for `c ≥ 2`, `hstep (oadd 0 ⟨c⟩ 0) n = oadd 0 ⟨c-1⟩ 0`. -/
lemma hstep_finite_pred (c : ℕ) (hc : 2 ≤ c) (n : ℕ) :
    hstep (oadd 0 ⟨c, by omega⟩ 0) n = oadd 0 ⟨c - 1, by omega⟩ 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 := ⟨c - 2, by omega⟩
  have hfs : fundamentalSequence (oadd 0 ⟨e + 2, by omega⟩ 0)
      = Sum.inl (some (oadd 0 ⟨e + 1, by omega⟩ 0)) := by
    rw [fundamentalSequence_oadd_zero_zero]; rfl
  rw [hstep_succ _ hfs]
  rfl

/-- The `c = 1` fundamental sequence when `E` is a **successor** (`fundamentalSequence E = some E'`). -/
lemma fundSeq_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E')) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd E' i.succPNat 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- The `c = 1` fundamental sequence when `E` is a **limit** (`fundamentalSequence E = inr f`). -/
lemma fundSeq_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd (f i) 1 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- One Hardy step on `oadd E 1 0` when `E` is a **successor** with predecessor `E'`: the
descent lands on `oadd E' ⟨b+1⟩ 0`. -/
lemma hstep_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E'))
    (b : ℕ) : hstep (oadd E 1 0) b = hstep (oadd E' b.succPNat 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_succ h)]

/-- One Hardy step on `oadd E 1 0` when `E` is a **limit** with fundamental sequence `f`: the
descent passes to `oadd (f b) 1 0`. -/
lemma hstep_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) (b : ℕ) :
    hstep (oadd E 1 0) b = hstep (oadd (f b) 1 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_limit h)]

/-- Fundamental sequence of the finite ordinal `oadd 0 ⟨c⟩ 0` (`c ≥ 2`): the successor of
`oadd 0 ⟨c-1⟩ 0`. -/
lemma fundSeq_finite_succ (c : ℕ) (hc : 2 ≤ c) :
    fundamentalSequence (oadd 0 ⟨c, by omega⟩ 0) = Sum.inl (some (oadd 0 ⟨c - 1, by omega⟩ 0)) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 := ⟨c - 2, by omega⟩
  rw [fundamentalSequence_oadd_zero_zero]; rfl

/-- **Lemma B, finite base case (PROVED).** For `0 ≤ d ≤ b`, one Hardy step on
`ω^(d+1) = oadd (finite (d+1)) 1 0` at argument `b` is the all-digits-`b` notation
`(b+1)^(d+1) − 1`. Strong induction on `d`: the descent peels the coefficient `b+1` it
produces (`hstep_oadd_coeff`), recurses (`ih`), and the leading exponent reconstructs as a
single base-`(b+1)` digit (`toONote (b+1) d = finite d`, valid since `d ≤ b < b+1`). This is
the base case of the general `hstep_oadd_one_zero` and validates the full borrowing recursion
(descent → coefficient peel → IH → reconstruct) end-to-end. -/
lemma hstep_oadd_one_zero_finite (b : ℕ) (hb : 2 ≤ b) :
    ∀ d, d ≤ b →
      hstep (oadd (oadd 0 d.succPNat 0) 1 0) b = toONote (b + 1) ((b + 1) ^ (d + 1) - 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hdb
    have hbsucc : (b.succPNat : ℕ+) = ⟨b + 1, by omega⟩ := rfl
    rcases Nat.eq_zero_or_pos d with hd | hd
    · -- d = 0: exponent 1, descent on finite 1 → oadd 0 ⟨b+1⟩ 0 → decrement → finite b
      subst hd
      have hE1 : fundamentalSequence (oadd 0 (0 : ℕ).succPNat 0) = Sum.inl (some 0) := by
        rw [fundamentalSequence_oadd_zero_zero]; rfl
      rw [hstep_oadd_one_of_succ hE1 b, hbsucc, hstep_finite_pred (b + 1) (by omega) b,
        show (b + 1) ^ (0 + 1) - 1 = b from by rw [pow_succ, pow_zero, one_mul]; omega]
      exact (toONote_single (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)).symm
    · -- d = e+1 ≥ 1: fundSeq(finite (e+2)) = some (finite (e+1)); descent → coefficient peel → ih e
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have hE' : (oadd 0 e.succPNat 0 : ONote) ≠ 0 := (oadd_pos _ _ _).ne'
      have hple : (1 : ℕ) ≤ (b + 1) ^ (e + 1) := Nat.one_le_pow _ _ (by omega)
      have hfd : fundamentalSequence (oadd 0 (e + 1).succPNat 0)
          = Sum.inl (some (oadd 0 e.succPNat 0)) := by
        rw [fundamentalSequence_oadd_zero_zero]; rfl
      rw [hstep_oadd_one_of_succ hfd b, hbsucc,
        hstep_oadd_coeff b hE' (by omega) (by omega : 1 ≤ b + 1),
        ih e (by omega) (by omega)]
      have hpow : (b + 1) ^ (e + 1 + 1) - 1 = b * (b + 1) ^ (e + 1) + ((b + 1) ^ (e + 1) - 1) := by
        have hsplit : (b + 1) ^ (e + 1 + 1) = (b + 1) * (b + 1) ^ (e + 1) := by rw [pow_succ']
        have hdist : (b + 1) * (b + 1) ^ (e + 1) = b * (b + 1) ^ (e + 1) + (b + 1) ^ (e + 1) := by
          ring
        rw [hsplit, hdist]; omega
      rw [hpow, toONote_oadd (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)
        (show (b + 1) ^ (e + 1) - 1 < (b + 1) ^ (e + 1) by omega)]
      congr 1
      exact (toONote_single (b + 1) (by omega) (show 1 ≤ e + 1 by omega) (by omega)).symm

/-! ### Closing the borrowing core: the `Good`/`Canon` invariant + general predecessor

The lone gap (`hstep_oadd_one_zero`) is the `c = 1` predecessor of `ω^E` for general NF `E`.
We prove a general statement `hstep_pred_pow` for every NF `E` satisfying a coefficient
invariant `Good b E`, by well-founded recursion on `repr E`, then specialize to `E = toONote b L`.

Invariant: throughout the `fundamentalSequence` descent the notation is *canonical in base
`b+1`* (`Canon`: all coefficients `≤ b`) except for at most one coefficient `b+1` parked at the
"active frontier" (`Good`). `Good` is preserved by the limit descent (`Good_fundSeq`); for a
*successor* the `b+1` is forced into the finite lowest term, so its predecessor is fully `Canon`
(`Canon_pred`). A `Canon` NF notation round-trips through `evalNat`
(`canon_round_trip : toONote (b+1) (evalNat b E) = E`) — exactly the successor reconstruction. -/

/-- `toOrdinal B (B^k) = ω^(toOrdinal B k)`: a pure power is a single leading `ω`-power. -/
lemma toOrdinal_pow (B : ℕ) (hB : 2 ≤ B) (k : ℕ) :
    toOrdinal B (B ^ k) = ω ^ toOrdinal B k := by
  have hBk : B ^ k ≠ 0 := pow_ne_zero _ (by omega)
  rw [toOrdinal_pos B _ hBk, Nat.log_pow (by omega), Nat.div_self (Nat.pow_pos (by omega)),
    Nat.mod_self, toOrdinal_zero, Nat.cast_one, mul_one, add_zero]

/-- Constructor form of `toOrdinal` (the ordinal twin of `toONote_oadd`): for `1 ≤ c < B` and
`s < B^k`, `toOrdinal B (c·B^k + s) = ω^(toOrdinal B k)·c + toOrdinal B s`. -/
lemma toOrdinal_oadd (B : ℕ) (hB : 2 ≤ B) {c k s : ℕ} (hc : 1 ≤ c) (hcB : c < B)
    (hs : s < B ^ k) :
    toOrdinal B (c * B ^ k + s) = ω ^ toOrdinal B k * (c : Ordinal) + toOrdinal B s := by
  have hBk_pos : 0 < B ^ k := Nat.pow_pos (by omega)
  have hn0 : c * B ^ k + s ≠ 0 := by positivity
  have hlow : c * B ^ k + s < B ^ (k + 1) := by
    calc c * B ^ k + s < c * B ^ k + B ^ k := by omega
      _ = (c + 1) * B ^ k := by ring
      _ ≤ B * B ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = B ^ (k + 1) := by rw [pow_succ]; ring
  have hge : B ^ k ≤ c * B ^ k + s :=
    (Nat.le_mul_of_pos_left (B ^ k) hc).trans (Nat.le_add_right _ _)
  have hlog : Nat.log B (c * B ^ k + s) = k := Nat.log_eq_of_pow_le_of_lt_pow hge hlow
  have hdiv : (c * B ^ k + s) / B ^ k = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hBk_pos, Nat.div_eq_of_lt hs, Nat.zero_add]
  have hmod : (c * B ^ k + s) % B ^ k = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  rw [toOrdinal_pos B _ hn0, hlog, hdiv, hmod]

/-- `Canon b o`: the notation `o` is in canonical base-`(b+1)` form — every coefficient is
`≤ b` (a valid base-`(b+1)` digit), recursively on exponents and tails. -/
def Canon (b : ℕ) : ONote → Prop
  | 0 => True
  | oadd e n r => (n : ℕ) ≤ b ∧ Canon b e ∧ Canon b r

lemma Canon_zero (b : ℕ) : Canon b 0 := trivial

lemma Canon_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    Canon b (oadd e n r) ↔ (n : ℕ) ≤ b ∧ Canon b e ∧ Canon b r := Iff.rfl

/-- A `Canon` NF notation is recovered by reading `evalNat` back at the ordinal level:
`toOrdinal (b+1) (evalNat b E) = repr E`. Structural induction; the leading-term remainder
bound for `toOrdinal_oadd` comes from `NF` via the engine's strict monotonicity. -/
lemma canon_repr (b : ℕ) (hb : 1 ≤ b) :
    ∀ E : ONote, Canon b E → E.NF → toOrdinal (b + 1) (evalNat b E) = E.repr := by
  have hSM : StrictMono (toOrdinal (b + 1)) := toOrdinal_strictMono (b + 1) (by omega)
  intro E
  induction E with
  | zero => intro _ _; simp
  | oadd e n r ihe ihr =>
    intro hcanon hNF
    obtain ⟨hn, hce, hcr⟩ := (Canon_oadd b e n r).1 hcanon
    have hNFe : e.NF := hNF.fst
    have hNFr : r.NF := hNF.snd
    have hbelow : r.repr < ω ^ e.repr := hNF.snd'.repr_lt
    have hre := ihe hce hNFe
    have hrr := ihr hcr hNFr
    have hbound : evalNat b r < (b + 1) ^ evalNat b e := by
      apply hSM.lt_iff_lt.1
      rw [toOrdinal_pow (b + 1) (by omega), hre, hrr]
      exact hbelow
    rw [evalNat_oadd, toOrdinal_oadd (b + 1) (by omega) n.pos (by omega) hbound, hre, hrr]
    simp

/-- A `Canon` NF notation round-trips through `evalNat`: `toONote (b+1) (evalNat b E) = E`. -/
lemma canon_round_trip (b : ℕ) (hb : 2 ≤ b) (E : ONote) (hcanon : Canon b E) (hNF : E.NF) :
    toONote (b + 1) (evalNat b E) = E := by
  haveI : (toONote (b + 1) (evalNat b E)).NF := toONote_NF (b + 1) (by omega) (evalNat b E)
  haveI : E.NF := hNF
  rw [← repr_inj, repr_toONote (b + 1) (by omega), canon_repr b (by omega) E hcanon hNF]

/-- `Good b o`: `o` is `Canon` except for at most one coefficient `= b+1`, parked at the active
frontier of the descent — the lowest term, deeper in the tail, or (when `o = ω^e`) inside the
exponent. Preserved by the descent; on a *successor* the `b+1` is forced low. -/
def Good (b : ℕ) : ONote → Prop
  | 0 => True
  | oadd e n r =>
      (Canon b e ∧ (n : ℕ) ≤ b ∧ Good b r) ∨
      (Canon b e ∧ (n : ℕ) = b + 1 ∧ r = 0) ∨
      ((n : ℕ) = 1 ∧ r = 0 ∧ Good b e)

lemma Good_zero (b : ℕ) : Good b 0 := trivial

lemma Good_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    Good b (oadd e n r) ↔
      (Canon b e ∧ (n : ℕ) ≤ b ∧ Good b r) ∨
      (Canon b e ∧ (n : ℕ) = b + 1 ∧ r = 0) ∨
      ((n : ℕ) = 1 ∧ r = 0 ∧ Good b e) := Iff.rfl

lemma Good_of_Canon (b : ℕ) : ∀ E, Canon b E → Good b E := by
  intro E
  induction E with
  | zero => intro _; exact trivial
  | oadd e n r _ ihr =>
    intro hc
    obtain ⟨hn, hce, hcr⟩ := (Canon_oadd b e n r).1 hc
    exact (Good_oadd b e n r).2 (Or.inl ⟨hce, hn, ihr hcr⟩)

lemma Canon_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ L, Canon b (toONote b L) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    rcases eq_or_ne L 0 with rfl | hL
    · rw [toONote_zero]; exact Canon_zero b
    · have hlog : Nat.log b L < L := Nat.log_lt_self b hL
      have hbe_pos : 0 < b ^ Nat.log b L := Nat.pow_pos (by omega)
      have hbe_le : b ^ Nat.log b L ≤ L := Nat.pow_log_le_self b hL
      have hr_lt : L % b ^ Nat.log b L < L := lt_of_lt_of_le (Nat.mod_lt _ hbe_pos) hbe_le
      have hcb : L / b ^ Nat.log b L < b := by
        apply Nat.div_lt_of_lt_mul
        have h := Nat.lt_pow_succ_log_self (show 1 < b by omega) L
        rwa [pow_succ] at h
      rw [toONote, dif_neg hL]
      refine (Canon_oadd b _ _ _).2 ⟨?_, ih _ hlog, ih _ hr_lt⟩
      rw [PNat.toPNat'_coe (Nat.div_pos hbe_le hbe_pos)]
      omega

/-- For a `Good` *successor* notation, the predecessor is fully `Canon`: the parked `b+1`
coefficient (if any) is forced into the finite lowest term, which `pred` decrements to `≤ b`. -/
lemma Canon_pred (b : ℕ) : ∀ E E', Good b E → fundamentalSequence E = Sum.inl (some E') →
    Canon b E' := by
  intro E
  induction E with
  | zero => intro E' _ h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r _ ihr =>
    intro E' hgood h
    rw [fundamentalSequence] at h
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0
      rw [hr] at h
      have hrz : r = 0 :=
        (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
      subst hrz
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0
        rw [ha] at h
        have haz : a = 0 :=
          (fundamentalSequenceProp_inl_none a).1 (ha ▸ fundamentalSequence_has_prop a)
        subst haz
        rcases hm : m.natPred with _ | k
        · -- m = 1, E' = 0
          rw [hm] at h
          obtain rfl : (0 : ONote) = E' := by simpa using h
          exact Canon_zero b
        · -- m = k+2, E' = oadd 0 k.succPNat 0
          rw [hm] at h
          obtain rfl : oadd 0 k.succPNat 0 = E' := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          have hmb : (m : ℕ) ≤ b + 1 := by
            rcases (Good_oadd b 0 m 0).1 hgood with ⟨_, hh, _⟩ | ⟨_, hh, _⟩ | ⟨hh, _, _⟩ <;> omega
          refine (Canon_oadd b _ _ _).2 ⟨?_, Canon_zero b, Canon_zero b⟩
          rw [Nat.succPNat_coe]; omega
      · -- a successor → inr, contradicts h (inl)
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a limit → inr, contradicts h (inl)
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
    · -- r successor: E' = oadd a m r', recurse on r
      rw [hr] at h
      obtain rfl : oadd a m r' = E' := by simpa using h
      have hrne : r ≠ 0 := by intro h0; rw [h0] at hr; simp [fundamentalSequence] at hr
      obtain ⟨hca, hmb, hgr⟩ : Canon b a ∧ (m : ℕ) ≤ b ∧ Good b r := by
        rcases (Good_oadd b a m r).1 hgood with H | ⟨_, _, hrz⟩ | ⟨_, hrz, _⟩
        · exact H
        · exact absurd hrz hrne
        · exact absurd hrz hrne
      exact (Canon_oadd b a m r').2 ⟨hmb, hca, ihr r' hgr hr⟩
    · -- r limit → inr, contradicts h (inl)
      rw [hr] at h; simp at h

/-- `Good` is preserved by one step of the limit descent at the working index `b`:
if `Good b E` and `fundamentalSequence E = inr f`, then `Good b (f b)`. -/
lemma Good_fundSeq (b : ℕ) : ∀ E f, Good b E → fundamentalSequence E = Sum.inr f →
    Good b (f b) := by
  intro E
  induction E with
  | zero => intro f _ h; exact absurd h (by simp [fundamentalSequence])
  | oadd a m r iha ihr =>
    intro f hgood h
    rw [fundamentalSequence] at h
    have hbpnat : (b.succPNat : ℕ+) = ⟨b + 1, by omega⟩ := rfl
    have hbnat : ((b.succPNat : ℕ+) : ℕ) = b + 1 := by simp [Nat.succPNat]
    rcases hr : fundamentalSequence r with (_ | r') | g
    · -- r = 0
      rw [hr] at h
      have hrz : r = 0 :=
        (fundamentalSequenceProp_inl_none r).1 (hr ▸ fundamentalSequence_has_prop r)
      subst hrz
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 → inl, contradicts h (inr)
        rw [ha] at h; rcases hm : m.natPred with _ | k <;> rw [hm] at h <;> simp at h
      · -- a successor a'
        rw [ha] at h
        have hga : Good b a := by
          rcases (Good_oadd b a m 0).1 hgood with ⟨hca, _, _⟩ | ⟨hca, _, _⟩ | ⟨_, _, hga⟩
          · exact Good_of_Canon b a hca
          · exact Good_of_Canon b a hca
          · exact hga
        have hca' : Canon b a' := Canon_pred b a a' hga ha
        rcases hm : m.natPred with _ | k
        · -- m = 1: f b = oadd a' b.succPNat 0
          rw [hm] at h
          obtain rfl : (fun i => oadd a' i.succPNat 0) = f := by simpa using h
          show Good b (oadd a' b.succPNat 0)
          exact (Good_oadd b a' b.succPNat 0).2 (Or.inr (Or.inl ⟨hca', hbnat, rfl⟩))
        · -- m = k+2: f b = oadd a k.succPNat (oadd a' b.succPNat 0)
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd a' i.succPNat 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          have hcam : Canon b a ∧ (m : ℕ) ≤ b + 1 := by
            rcases (Good_oadd b a m 0).1 hgood with ⟨hca, hh, _⟩ | ⟨hca, hh, _⟩ | ⟨hh, _, _⟩
            · exact ⟨hca, by omega⟩
            · exact ⟨hca, by omega⟩
            · exfalso; omega
          show Good b (oadd a k.succPNat (oadd a' b.succPNat 0))
          refine (Good_oadd b a k.succPNat _).2 (Or.inl ⟨hcam.1, ?_, ?_⟩)
          · rw [Nat.succPNat_coe]; omega
          · exact (Good_oadd b a' b.succPNat 0).2 (Or.inr (Or.inl ⟨hca', hbnat, rfl⟩))
      · -- a limit p
        rw [ha] at h
        have hga : Good b a := by
          rcases (Good_oadd b a m 0).1 hgood with ⟨hca, _, _⟩ | ⟨hca, _, _⟩ | ⟨_, _, hga⟩
          · exact Good_of_Canon b a hca
          · exact Good_of_Canon b a hca
          · exact hga
        have hgpb : Good b (p b) := iha p hga ha
        rcases hm : m.natPred with _ | k
        · -- m = 1: f b = oadd (p b) 1 0
          rw [hm] at h
          obtain rfl : (fun i => oadd (p i) 1 0) = f := by simpa using h
          show Good b (oadd (p b) 1 0)
          exact (Good_oadd b (p b) 1 0).2 (Or.inr (Or.inr ⟨PNat.one_coe, rfl, hgpb⟩))
        · -- m = k+2: f b = oadd a k.succPNat (oadd (p b) 1 0)
          rw [hm] at h
          obtain rfl : (fun i => oadd a k.succPNat (oadd (p i) 1 0)) = f := by simpa using h
          have hmk : (m : ℕ) = k + 2 := by have := PNat.natPred_add_one m; omega
          have hcam : Canon b a ∧ (m : ℕ) ≤ b + 1 := by
            rcases (Good_oadd b a m 0).1 hgood with ⟨hca, hh, _⟩ | ⟨hca, hh, _⟩ | ⟨hh, _, _⟩
            · exact ⟨hca, by omega⟩
            · exact ⟨hca, by omega⟩
            · exfalso; omega
          show Good b (oadd a k.succPNat (oadd (p b) 1 0))
          refine (Good_oadd b a k.succPNat _).2 (Or.inl ⟨hcam.1, ?_, ?_⟩)
          · rw [Nat.succPNat_coe]; omega
          · exact (Good_oadd b (p b) 1 0).2 (Or.inr (Or.inr ⟨PNat.one_coe, rfl, hgpb⟩))
    · -- r successor → inl, contradicts h (inr)
      rw [hr] at h; simp at h
    · -- r limit g: f b = oadd a m (g b)
      rw [hr] at h
      obtain rfl : (fun i => oadd a m (g i)) = f := by simpa using h
      have hrne : r ≠ 0 := by intro h0; rw [h0] at hr; simp [fundamentalSequence] at hr
      obtain ⟨hca, hmb, hgr⟩ : Canon b a ∧ (m : ℕ) ≤ b ∧ Good b r := by
        rcases (Good_oadd b a m r).1 hgood with H | ⟨_, _, hrz⟩ | ⟨_, hrz, _⟩
        · exact H
        · exact absurd hrz hrne
        · exact absurd hrz hrne
      show Good b (oadd a m (g b))
      exact (Good_oadd b a m (g b)).2 (Or.inl ⟨hca, hmb, ihr g hgr hr⟩)

/-- The general borrowing predecessor for a normal-form notation satisfying the frontier invariant:
one Hardy step on `ω^E` at argument `b` is the base-`(b+1)` notation of `(b+1)^(evalNat b E) − 1`. -/
lemma hstep_pred_pow (b : ℕ) (hb : 2 ≤ b) :
    ∀ E : ONote, E.NF → E ≠ 0 → Good b E →
      hstep (oadd E 1 0) b = toONote (b + 1) ((b + 1) ^ evalNat b E - 1) := by
  suffices H : ∀ o : Ordinal, ∀ E : ONote, E.repr = o → E.NF → E ≠ 0 → Good b E →
      hstep (oadd E 1 0) b = toONote (b + 1) ((b + 1) ^ evalNat b E - 1) by
    exact fun E => H E.repr E rfl
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro E hrepr hNF hne hgood
    have hbpnat : (b.succPNat : ℕ+) = ⟨b + 1, by omega⟩ := rfl
    rcases hfs : fundamentalSequence E with (_ | E') | f
    · exact absurd ((fundamentalSequenceProp_inl_none E).1 (hfs ▸ fundamentalSequence_has_prop E)) hne
    · -- successor: peel the coefficient, recurse on the predecessor, reconstruct
      obtain ⟨hsucc, hNFimp⟩ :=
        (fundamentalSequenceProp_inl_some E E').1 (hfs ▸ fundamentalSequence_has_prop E)
      have hNFE' : E'.NF := hNFimp hNF
      have hltE' : E'.repr < o := by rw [← hrepr, hsucc]; exact Order.lt_succ _
      have hcanonE' : Canon b E' := Canon_pred b E E' hgood hfs
      have hevalE : evalNat b E = evalNat b E' + 1 := evalNat_succ b hfs
      rcases eq_or_ne E' 0 with hE'0 | hE'0
      · subst hE'0
        rw [hstep_oadd_one_of_succ hfs b, hbpnat, hstep_finite_pred (b + 1) (by omega) b,
          hevalE, evalNat_zero,
          show (b + 1) ^ (0 + 1) - 1 = b from by rw [pow_succ, pow_zero, one_mul]; omega]
        exact (toONote_single (b + 1) (by omega) (show 1 ≤ b by omega) (by omega)).symm
      · rw [hstep_oadd_one_of_succ hfs b, hbpnat,
          hstep_oadd_coeff b hE'0 (by omega : 2 ≤ b + 1) (by omega : 1 ≤ b + 1),
          ih E'.repr hltE' E' rfl hNFE' hE'0 (Good_of_Canon b E' hcanonE'), hevalE]
        have hpos : 1 ≤ (b + 1) ^ evalNat b E' := Nat.one_le_pow _ _ (by omega)
        rw [show (b + 1) ^ (evalNat b E' + 1) - 1
              = b * (b + 1) ^ evalNat b E' + ((b + 1) ^ evalNat b E' - 1) from by
            rw [pow_succ']
            have hX : (b + 1) * (b + 1) ^ evalNat b E'
                    = b * (b + 1) ^ evalNat b E' + (b + 1) ^ evalNat b E' := by ring
            omega,
          toONote_oadd (b + 1) (by omega) (show 1 ≤ b by omega) (by omega) (by omega),
          canon_round_trip b hb E' hcanonE' hNFE']
        rfl
    · -- limit: recurse on `f b`; `evalNat_fundSeq` lands the size, no reconstruction
      obtain ⟨_, hbody, _⟩ :=
        (fundamentalSequenceProp_inr E f).1 (hfs ▸ fundamentalSequence_has_prop E)
      have hfbne : f b ≠ 0 := fundamentalSequence_inr_ne_zero hfs b
      have hNFfb : (f b).NF := (hbody b).2.2 hNF
      have hltfb : (f b).repr < o := by rw [← hrepr]; exact repr_lt_repr (hbody b).2.1
      rw [hstep_oadd_one_of_limit hfs b,
        ih (f b).repr hltfb (f b) rfl hNFfb hfbne (Good_fundSeq b E f hgood hfs),
        evalNat_fundSeq b hfs]

/-- For a positive exponent `L`, one Hardy step on `oadd (toONote b L) 1 0` at argument `b`
is the base-`(b+1)` notation of `(b+1)^(bump b L) − 1`. -/
lemma hstep_oadd_one_zero (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (hL : 1 ≤ L) :
    hstep (oadd (toONote b L) 1 0) b = toONote (b + 1) ((b + 1) ^ bump b L - 1) := by
  have hE : toONote b L ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; omega
  have hNF : (toONote b L).NF := toONote_NF b hb L
  have hgood : Good b (toONote b L) := Good_of_Canon b _ (Canon_toONote b hb L)
  rw [hstep_pred_pow b hb (toONote b L) hNF hE hgood, evalNat_toONote b hb L]

/-- The Cichoń step: one Hardy step on the base-`b` notation of `p` at argument `b`
equals the base-`(b+1)` notation of `bump b p − 1`.

- [Cic83]. -/
theorem hstep_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ p, p ≠ 0 →
    hstep (toONote b p) b = toONote (b + 1) (bump b p - 1) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    have hbe_pos : 0 < b ^ Nat.log b p := Nat.pow_pos (by omega)
    have hbe_le : b ^ Nat.log b p ≤ p := Nat.pow_log_le_self b hp
    have hc1 : 1 ≤ p / b ^ Nat.log b p := Nat.div_pos hbe_le hbe_pos
    have hcb : p / b ^ Nat.log b p < b := by
      apply Nat.div_lt_of_lt_mul
      have h := Nat.lt_pow_succ_log_self (show 1 < b by omega) p
      rwa [pow_succ] at h
    have hr_lt : p % b ^ Nat.log b p < b ^ Nat.log b p := Nat.mod_lt _ hbe_pos
    have hp_eq : p = (p / b ^ Nat.log b p) * b ^ Nat.log b p + p % b ^ Nat.log b p := by
      rw [mul_comm]; exact (Nat.div_add_mod p _).symm
    set L := Nat.log b p
    set c := p / b ^ L with hc_def
    set r := p % b ^ L with hr_def
    have htoP : toONote b p = oadd (toONote b L) ⟨c, hc1⟩ (toONote b r) := by
      conv_lhs => rw [hp_eq]
      exact toONote_oadd b hb hc1 hcb hr_lt
    have hbump : bump b p = c * (b + 1) ^ bump b L + bump b r := bump_pos b p hp
    rcases eq_or_ne r 0 with hr0 | hr0
    · -- r = 0: the predecessor of `c·b^L`
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · -- L = 0: a single digit `c`; `oadd 0 c 0` is a successor (PROVED)
        have hEz : toONote b L = 0 := by rw [hL0, toONote_zero]
        have hbumpL : bump b L = 0 := by rw [hL0, bump_zero]
        rw [htoP, hr0, hEz, toONote_zero, hstep_oadd_zero_zero b hb c hc1 hcb]
        congr 1
        rw [hbump, hr0, hbumpL, bump_zero]; simp
      · -- L ≥ 1: borrowing case. Peel the coefficient (`hstep_oadd_coeff`) down to the
        -- `c = 1` predecessor `hstep_oadd_one_zero`, then reconstruct via `toONote_oadd`.
        have hE : toONote b L ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; omega
        have htoP0 : toONote b p = oadd (toONote b L) ⟨c, hc1⟩ 0 := by
          rw [htoP, hr0, toONote_zero]
        have hbump0 : bump b p - 1 = c * (b + 1) ^ bump b L - 1 := by
          rw [hbump, hr0, bump_zero, Nat.add_zero]
        rcases eq_or_ne c 1 with hc1' | hc2'
        · -- c = 1: directly Lemma B
          have hcpn : (⟨c, hc1⟩ : ℕ+) = 1 := PNat.coe_injective hc1'
          rw [htoP0, hcpn, hbump0, hc1', one_mul]
          exact hstep_oadd_one_zero b hb L hLpos
        · -- c ≥ 2: peel to `oadd E ⟨c-1⟩ (hstep (oadd E 1 0) b)`, recombine
          have hMpos : 1 ≤ (b + 1) ^ bump b L := Nat.one_le_pow _ _ (by omega)
          have key : c * (b + 1) ^ bump b L - 1
              = (c - 1) * (b + 1) ^ bump b L + ((b + 1) ^ bump b L - 1) := by
            have h := Nat.sub_one_mul c ((b + 1) ^ bump b L)
            have hcX : (b + 1) ^ bump b L ≤ c * (b + 1) ^ bump b L :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
          rw [htoP0, hstep_oadd_coeff b hE (by omega) hc1, hstep_oadd_one_zero b hb L hLpos,
            hbump0, key]
          rw [toONote_oadd (b + 1) (by omega) (show 1 ≤ c - 1 by omega) (by omega)
              (show (b + 1) ^ bump b L - 1 < (b + 1) ^ bump b L by omega),
            toONote_bump b hb]
    · -- r ≠ 0: leading term preserved, the step happens in the tail
      have hRne : toONote b r ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; exact hr0
      have hbr_pos : 0 < bump b r := by
        rw [bump_pos b r hr0]
        have h1 : 0 < r / b ^ Nat.log b r :=
          Nat.div_pos (Nat.pow_log_le_self _ hr0) (Nat.pow_pos (by omega))
        have h2 : 0 < (b + 1) ^ bump b (Nat.log b r) := Nat.pow_pos (by omega)
        have := Nat.mul_pos h1 h2; omega
      have hbrB : bump b r < (b + 1) ^ bump b L := bump_lt_pow b hb hr_lt
      rw [htoP, hstep_oadd_tail (toONote b L) ⟨c, hc1⟩ b (toONote b r) hRne, ih r (by omega) hr0]
      have hsub : bump b p - 1 = c * (b + 1) ^ bump b L + (bump b r - 1) := by rw [hbump]; omega
      rw [hsub, toONote_oadd (b + 1) (by omega) hc1 (by omega)
        (by omega : bump b r - 1 < (b + 1) ^ bump b L), toONote_bump b hb]

/-- The Cichoń step, specialised to the Goodstein descent: one Goodstein step is one
budget-incrementing Hardy step on the notation. `seqONote m (k+1) = hstep (seqONote m k) (k+2)`
whenever the term is nonzero. -/
lemma hstep_seqONote (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hstep (seqONote m k) (k + 2) = seqONote m (k + 1) := by
  show hstep (toONote (k + 2) (goodsteinSeq m k)) (k + 2) = toONote (k + 1 + 2) (goodsteinSeq m (k + 1))
  rw [hstep_toONote (k + 2) (by omega) (goodsteinSeq m k) h]
  rfl

/-- **The per-step Hardy invariant.** Along the Goodstein descent (while nonzero) the Hardy
value `H_{seqONote m k}(k+2)` is unchanged: `H_{seqONote m k}(k+2) = H_{seqONote m (k+1)}((k+1)+2)`.
Combines the intrinsic step invariant `hardy_hstep` with the Cichoń step `hstep_seqONote`. -/
lemma hardy_seqONote_step (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hardy (seqONote m k) (k + 2) = hardy (seqONote m (k + 1)) (k + 1 + 2) := by
  have ho : seqONote m k ≠ 0 := fun hz => h ((seqONote_eq_zero_iff m k).1 hz)
  rw [hardy_hstep (seqONote m k) (k + 2) ho, hstep_seqONote m k h]

/-- **Telescoping.** For every `j ≤ goodsteinLength m`, the Hardy value at the start equals
the Hardy value `j` steps in: `H_{seqONote m 0}(2) = H_{seqONote m j}(j+2)`. Induction on `j`
using `hardy_seqONote_step` (valid since `j < goodsteinLength m` ⟹ the `j`-th term is nonzero). -/
lemma hardy_seqONote_telescope (m : ℕ) :
    ∀ j, j ≤ goodsteinLength m → hardy (seqONote m 0) 2 = hardy (seqONote m j) (j + 2) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ k ih =>
    intro hj
    have hk : k < goodsteinLength m := Nat.lt_of_succ_le hj
    rw [ih (Nat.le_of_lt hk), hardy_seqONote_step m k (goodsteinSeq_ne_zero_of_lt hk)]

/-- **The growth theorem (Hardy form).** The Hardy value of the starting notation at the
starting base is the Goodstein length plus two: `H_{seqONote m 0}(2) = goodsteinLength m + 2`.
At `j = goodsteinLength m` the descent reaches the zero notation, where `H_0(N) = N`. -/
lemma hardy_seqONote_zero (m : ℕ) : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := by
  rw [hardy_seqONote_telescope m (goodsteinLength m) le_rfl, seqONote_goodsteinLength, hardy_zero]
  rfl

/-- **The growth theorem (length form).** The Goodstein length of `m` is exactly the
Hardy value of its starting notation (read in base 2) at argument 2, minus 2:

  `goodsteinLength m = H_{seqONote m 0}(2) − 2`.

This is Cichoń's identity formalised: the Goodstein length function *is* a Hardy function of
the starting ordinal notation. Since the Hardy/fast-growing hierarchy reaches `ε₀`, this pins
`goodsteinLength`'s growth at the `ε₀` level — the growth content of Kirby–Paris independence.

- [Cic83]. -/
theorem goodsteinLength_eq_hardy (m : ℕ) : goodsteinLength m = hardy (seqONote m 0) 2 - 2 := by
  rw [hardy_seqONote_zero]; omega

end Goodstein.Dom
