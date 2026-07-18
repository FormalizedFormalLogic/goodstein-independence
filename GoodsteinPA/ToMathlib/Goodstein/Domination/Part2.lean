/-
# Goodstein.Dom — Part2
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Notation
public meta import Mathlib.SetTheory.Ordinal.Notation  -- shake: keep
public import Mathlib.Tactic.Ring
public import GoodsteinPA.ToMathlib.Goodstein.Defs
public meta import GoodsteinPA.ToMathlib.Goodstein.Defs  -- shake: keep
public import GoodsteinPA.ToMathlib.Hardy
public meta import GoodsteinPA.ToMathlib.Hardy  -- shake: keep
public import GoodsteinPA.ToMathlib.Goodstein.Domination.Part1
public meta import GoodsteinPA.ToMathlib.Goodstein.Domination.Part1  -- shake: keep

@[expose] public section

namespace Goodstein.Dom

open ONote Ordinal

/-- **`evalNat` is fixed at the index `b` of a fundamental sequence.** If `E` is a limit with
`fundamentalSequence E = inr f`, then `evalNat b (f b) = evalNat b E`. The descent's coefficient
`b+1` (from `(b).succPNat`) is exactly what makes the base-`(b+1)` evaluation land back on
`evalNat b E`. Structural recursion on `E`; the successor sub-branches use `evalNat_succ`. -/
theorem evalNat_fundSeq (b : ℕ) : ∀ {E : ONote} {f : ℕ → ONote},
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
theorem hstep_finite_pred (c : ℕ) (hc : 2 ≤ c) (n : ℕ) :
    hstep (oadd 0 ⟨c, by omega⟩ 0) n = oadd 0 ⟨c - 1, by omega⟩ 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 := ⟨c - 2, by omega⟩
  have hfs : fundamentalSequence (oadd 0 ⟨e + 2, by omega⟩ 0)
      = Sum.inl (some (oadd 0 ⟨e + 1, by omega⟩ 0)) := by
    rw [fundamentalSequence_oadd_zero_zero]; rfl
  rw [hstep_succ _ hfs]
  rfl

/-- The `c = 1` fundamental sequence when `E` is a **successor** (`fundamentalSequence E = some E'`). -/
theorem fundSeq_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E')) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd E' i.succPNat 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- The `c = 1` fundamental sequence when `E` is a **limit** (`fundamentalSequence E = inr f`). -/
theorem fundSeq_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) :
    fundamentalSequence (oadd E 1 0) = Sum.inr (fun i => oadd (f i) 1 0) := by
  rw [fundamentalSequence]
  simp only [show fundamentalSequence (0 : ONote) = Sum.inl none from rfl, h]; rfl

/-- One Hardy step on `oadd E 1 0` when `E` is a **successor** with predecessor `E'`: the
descent lands on `oadd E' ⟨b+1⟩ 0`. -/
theorem hstep_oadd_one_of_succ {E E' : ONote} (h : fundamentalSequence E = Sum.inl (some E'))
    (b : ℕ) : hstep (oadd E 1 0) b = hstep (oadd E' b.succPNat 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_succ h)]

/-- One Hardy step on `oadd E 1 0` when `E` is a **limit** with fundamental sequence `f`: the
descent passes to `oadd (f b) 1 0`. -/
theorem hstep_oadd_one_of_limit {E : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence E = Sum.inr f) (b : ℕ) :
    hstep (oadd E 1 0) b = hstep (oadd (f b) 1 0) b := by
  rw [hstep_limit _ (fundSeq_oadd_one_of_limit h)]

/-- Fundamental sequence of the finite ordinal `oadd 0 ⟨c⟩ 0` (`c ≥ 2`): the successor of
`oadd 0 ⟨c-1⟩ 0`. -/
theorem fundSeq_finite_succ (c : ℕ) (hc : 2 ≤ c) :
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
theorem hstep_oadd_one_zero_finite (b : ℕ) (hb : 2 ≤ b) :
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
theorem toOrdinal_pow (B : ℕ) (hB : 2 ≤ B) (k : ℕ) :
    toOrdinal B (B ^ k) = ω ^ toOrdinal B k := by
  have hBk : B ^ k ≠ 0 := pow_ne_zero _ (by omega)
  rw [toOrdinal_pos B _ hBk, Nat.log_pow (by omega), Nat.div_self (Nat.pow_pos (by omega)),
    Nat.mod_self, toOrdinal_zero, Nat.cast_one, mul_one, add_zero]

/-- Constructor form of `toOrdinal` (the ordinal twin of `toONote_oadd`): for `1 ≤ c < B` and
`s < B^k`, `toOrdinal B (c·B^k + s) = ω^(toOrdinal B k)·c + toOrdinal B s`. -/
theorem toOrdinal_oadd (B : ℕ) (hB : 2 ≤ B) {c k s : ℕ} (hc : 1 ≤ c) (hcB : c < B)
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

theorem Canon_zero (b : ℕ) : Canon b 0 := trivial

theorem Canon_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    Canon b (oadd e n r) ↔ (n : ℕ) ≤ b ∧ Canon b e ∧ Canon b r := Iff.rfl

/-- A `Canon` NF notation is recovered by reading `evalNat` back at the ordinal level:
`toOrdinal (b+1) (evalNat b E) = repr E`. Structural induction; the leading-term remainder
bound for `toOrdinal_oadd` comes from `NF` via the engine's strict monotonicity. -/
theorem canon_repr (b : ℕ) (hb : 1 ≤ b) :
    ∀ E : ONote, Canon b E → E.NF → toOrdinal (b + 1) (evalNat b E) = E.repr := by
  have hSM : StrictMono (toOrdinal (b + 1)) := fun a c hac =>
    (toOrdinal_mono_and_bound (b + 1) (by omega) c).1 a hac
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
theorem canon_round_trip (b : ℕ) (hb : 2 ≤ b) (E : ONote) (hcanon : Canon b E) (hNF : E.NF) :
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

theorem Good_zero (b : ℕ) : Good b 0 := trivial

theorem Good_oadd (b : ℕ) (e : ONote) (n : ℕ+) (r : ONote) :
    Good b (oadd e n r) ↔
      (Canon b e ∧ (n : ℕ) ≤ b ∧ Good b r) ∨
      (Canon b e ∧ (n : ℕ) = b + 1 ∧ r = 0) ∨
      ((n : ℕ) = 1 ∧ r = 0 ∧ Good b e) := Iff.rfl

theorem Good_of_Canon (b : ℕ) : ∀ E, Canon b E → Good b E := by
  intro E
  induction E with
  | zero => intro _; exact trivial
  | oadd e n r _ ihr =>
    intro hc
    obtain ⟨hn, hce, hcr⟩ := (Canon_oadd b e n r).1 hc
    exact (Good_oadd b e n r).2 (Or.inl ⟨hce, hn, ihr hcr⟩)

theorem Canon_toONote (b : ℕ) (hb : 2 ≤ b) : ∀ L, Canon b (toONote b L) := by
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
theorem Canon_pred (b : ℕ) : ∀ E E', Good b E → fundamentalSequence E = Sum.inl (some E') →
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
theorem Good_fundSeq (b : ℕ) : ∀ E f, Good b E → fundamentalSequence E = Sum.inr f →
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

/-- **The general borrowing predecessor.** For every NF `E ≠ 0` satisfying the frontier
invariant `Good b E`, one Hardy step on `ω^E` (`= oadd E 1 0`) at argument `b` is the
all-digits-`b` base-`(b+1)` notation of `(b+1)^(evalNat b E) − 1`. Well-founded recursion on
`repr E`: the limit case closes via the IH on `f b` and `evalNat_fundSeq`; the successor case
peels the coefficient (`hstep_oadd_coeff`), applies the IH to the predecessor `E'`, and
reconstructs `E'` via `canon_round_trip` (valid since `Canon_pred` makes `E'` canonical). -/
theorem hstep_pred_pow (b : ℕ) (hb : 2 ≤ b) :
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

/-- **Lemma B (the `c = 1` predecessor — the borrowing core of C3, FULLY PROVED lap 5).** One Hardy
step on `oadd (toONote b L) 1 0` (i.e. `ω^E` for `E = toONote b L`, `L ≥ 1`) at argument `b` is the
base-`(b+1)` notation of `(b+1)^(bump b L) − 1` — the fully-filled (all-digits-`b`) expansion
produced by the borrowing descent through `fundamentalSequence`.

**PROVED + `#print axioms` clean** — this was the last disclosed `sorry` of C3 and it is discharged.
The proof closes via `hstep_pred_pow` (WF recursion on `repr E`, using the `Good`/`Canon` coefficient-
bound frontier invariant) + `evalNat_toONote`. The plan below is the historical close-out record.

**Supporting engine** (all axiom-clean, this file):
* **finite base case** `hstep_oadd_one_zero_finite` (`E = finite (d+1)`, `d ≤ b`) — exercises
  the whole engine end-to-end (descent `hstep_oadd_one_of_succ` → peel `hstep_oadd_coeff` →
  IH → reconstruct `toONote_oadd`);
* the **answer characterization** `evalNat` + `evalNat_toONote : evalNat b (toONote b L) =
  bump b L` (so the general answer `toONote (b+1) ((b+1)^(evalNat b E) − 1)` is the target);
* both **descent identities**: `evalNat_succ` (`fundamentalSequence E = some E' ⟹
  evalNat b E = evalNat b E' + 1`) and `evalNat_fundSeq` (`fundamentalSequence E = inr f ⟹
  evalNat b (f b) = evalNat b E`).

**Plan to close** — prove the general `∀ NF E ≠ 0, hstep (oadd E 1 0) b =
toONote (b+1) ((b+1)^(evalNat b E) − 1)` by well-founded recursion on `repr E`:
* **limit case CLOSES** outright: `hstep_oadd_one_of_limit` → IH on `f b` → `evalNat_fundSeq`.
* **successor case** needs `evalNat_succ` (done) plus the reconstruction
  `toONote (b+1) (evalNat b E') = E'` for `E' = pred E`. This is the LONE remaining piece: it
  requires a coefficient-bound invariant `Good b E` (all coeffs ≤ b+1, and every coeff-`(b+1)`
  term has tail `0`) carried through the recursion — `Good` holds at the start `toONote b L`
  (coeffs `< b`), is preserved by `f b` (the new `b+1` coeff sits on a tail-`0` term) and by
  `pred`, and for a *successor* `E` forces any `b+1` coeff into the finite lowest term, which
  `pred` then removes — so `pred E` has all coeffs `< b+1` and reconstructs. Then
  `hstep_oadd_one_zero` is the `E = toONote b L` instance (with `evalNat_toONote`).
Verified syntactically by `native_decide` on small cases (see anchors). -/
theorem hstep_oadd_one_zero (b : ℕ) (hb : 2 ≤ b) (L : ℕ) (hL : 1 ≤ L) :
    hstep (oadd (toONote b L) 1 0) b = toONote (b + 1) ((b + 1) ^ bump b L - 1) := by
  have hE : toONote b L ≠ 0 := by rw [Ne, toONote_eq_zero_iff]; omega
  have hNF : (toONote b L).NF := toONote_NF b hb L
  have hgood : Good b (toONote b L) := Good_of_Canon b _ (Canon_toONote b hb L)
  rw [hstep_pred_pow b hb (toONote b L) hNF hE hgood, evalNat_toONote b hb L]

/-- **The Cichoń step (THE C3 CRUX).** One budget-incrementing Hardy step on the base-`b`
notation of `p ≠ 0`, at argument `b`, equals the notation (in base `b+1`) of the
Goodstein operation `bump b p − 1`:

  `hstep (toONote b p) b = toONote (b+1) (bump b p − 1)`.

This is the heart of Cichoń's theorem (1983) identifying the Goodstein descent with the
Hardy descent. Strong induction on `p`, writing `p = c·b^L + r` (leading Cantor term):

* **`r ≠ 0` (FULLY PROVED).** The leading term is preserved and the step happens in the tail:
  `hstep (oadd E C R) b = oadd E C (hstep R b)` (`hstep_oadd_tail`), then the IH on `r < p`
  and the reconstruction `toONote_oadd` + bump-invariance `toONote_bump` close it.
* **`r = 0`.** Here `p = c·b^L` and the step computes the *predecessor* of `c·(b+1)^(bump b L)`.
  - `L = 0` (single digit, FULLY PROVED): `oadd 0 c 0` is a successor (`hstep_oadd_zero_zero`).
  - `L ≥ 1` (**FULLY PROVED**, lap 5, via `hstep_oadd_one_zero`): the genuine **borrowing** case —
    a nested `fundamentalSequence` descent producing the filled `(b+1)`-ary expansion of
    `(b+1)^(bump b L) − 1`. This was the borrowing core of C3; now discharged, `#print axioms` clean.

This theorem is now FULLY PROVED for all `p` (`r ≠ 0`, `r = 0 ∧ L = 0`, and `r = 0 ∧ L ≥ 1`). -/
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
theorem hstep_seqONote (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hstep (seqONote m k) (k + 2) = seqONote m (k + 1) := by
  show hstep (toONote (k + 2) (goodsteinSeq m k)) (k + 2) = toONote (k + 1 + 2) (goodsteinSeq m (k + 1))
  rw [hstep_toONote (k + 2) (by omega) (goodsteinSeq m k) h]
  rfl

/-- **The per-step Hardy invariant.** Along the Goodstein descent (while nonzero) the Hardy
value `H_{seqONote m k}(k+2)` is unchanged: `H_{seqONote m k}(k+2) = H_{seqONote m (k+1)}((k+1)+2)`.
Combines the intrinsic step invariant `hardy_hstep` with the Cichoń step `hstep_seqONote`. -/
theorem hardy_seqONote_step (m k : ℕ) (h : goodsteinSeq m k ≠ 0) :
    hardy (seqONote m k) (k + 2) = hardy (seqONote m (k + 1)) (k + 1 + 2) := by
  have ho : seqONote m k ≠ 0 := fun hz => h ((seqONote_eq_zero_iff m k).1 hz)
  rw [hardy_hstep (seqONote m k) (k + 2) ho, hstep_seqONote m k h]

/-- **Telescoping.** For every `j ≤ goodsteinLength m`, the Hardy value at the start equals
the Hardy value `j` steps in: `H_{seqONote m 0}(2) = H_{seqONote m j}(j+2)`. Induction on `j`
using `hardy_seqONote_step` (valid since `j < goodsteinLength m` ⟹ the `j`-th term is nonzero). -/
theorem hardy_seqONote_telescope (m : ℕ) :
    ∀ j, j ≤ goodsteinLength m → hardy (seqONote m 0) 2 = hardy (seqONote m j) (j + 2) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ k ih =>
    intro hj
    have hk : k < goodsteinLength m := Nat.lt_of_succ_le hj
    rw [ih (Nat.le_of_lt hk), hardy_seqONote_step m k (goodsteinSeq_ne_zero_of_lt hk)]

/-- **C3 — the growth theorem (Hardy form).** The Hardy value of the starting notation at the
starting base is the Goodstein length plus two: `H_{seqONote m 0}(2) = goodsteinLength m + 2`.
At `j = goodsteinLength m` the descent reaches the zero notation, where `H_0(N) = N`. -/
theorem hardy_seqONote_zero (m : ℕ) : hardy (seqONote m 0) 2 = goodsteinLength m + 2 := by
  rw [hardy_seqONote_telescope m (goodsteinLength m) le_rfl, seqONote_goodsteinLength, hardy_zero]
  rfl

/-- **C3 — the growth theorem (length form).** The Goodstein length of `m` is exactly the
Hardy value of its starting notation (read in base 2) at argument 2, minus 2:

  `goodsteinLength m = H_{seqONote m 0}(2) − 2`.

This is Cichoń's identity formalised: the Goodstein length function *is* a Hardy function of
the starting ordinal notation. Since the Hardy/fast-growing hierarchy reaches `ε₀`
(`FastGrowing/Domination.lean`, A4), this pins `goodsteinLength`'s growth at the `ε₀` level —
the growth content of Kirby–Paris independence. -/
theorem goodsteinLength_eq_hardy (m : ℕ) : goodsteinLength m = hardy (seqONote m 0) 2 - 2 := by
  rw [hardy_seqONote_zero]; omega

/-! ### Anti-vacuity anchors (`native_decide`)

The notations are computable; small values pin them (a wrong recursion would fail). -/

example : toONote 2 1 = oadd 0 1 0 := by native_decide          -- `1 = ω^0`
example : toONote 2 2 = oadd (oadd 0 1 0) 1 0 := by native_decide -- `2 = 2^1 ↦ ω^1 = ω`
example : toONote 2 4 = oadd (oadd (oadd 0 1 0) 1 0) 1 0 := by native_decide -- `4 = 2^2 ↦ ω^ω`
example : toONote 3 5 = oadd (oadd 0 1 0) 1 (oadd 0 2 0) := by native_decide  -- `5 = 1·3^1 + 2`
-- the descent: `goodsteinSeq 3` starts `3 ↦ 3 ↦ 3 ↦ 2 ↦ …`, notations strictly drop
example : seqONote 3 0 = oadd (oadd 0 1 0) 1 (oadd 0 1 0) := by native_decide -- `G₀=3` in base 2 ↦ `ω+1`
-- the Cichoń step `hstep_toONote` (now FULLY PROVED) holds; here anchored on computable cases:
example : hstep (toONote 2 3) 2 = toONote 3 (bump 2 3 - 1) := by native_decide
example : hstep (toONote 3 5) 3 = toONote 4 (bump 3 5 - 1) := by native_decide
example : hstep (seqONote 3 0) 2 = seqONote 3 1 := by native_decide
-- C3, witnessed on a computable case: `goodsteinLength 3 = H_{seqONote 3 0}(2) − 2 = 7 − 2 = 5`
example : hardy (seqONote 3 0) 2 = goodsteinLength 3 + 2 := by native_decide


-- ════════════════ ported: Domination.lean ════════════════
/-
# The Hardy ↔ fast-growing bridge: `f_α ≤ H_{ω^α}`

The Cichoń identity (`Logic/Goodstein/Growth.lean`) gives
`goodsteinLength m = H_{toONote 2 m}(2) − 2`. To turn that into "Goodstein grows like the
fast-growing hierarchy" we relate the Hardy hierarchy `H_α` to the fast-growing hierarchy
`f_α`. The classical identity `H_{ω^α} = f_α` holds under the `ω[n]=n` convention; mathlib uses
`ω[n] = n+1`, which makes `H_{ω^α}` strictly *bigger*, so we prove the robust one-sided bound

  `fastGrowing α n ≤ hardy (oadd α 1 0) n`   (`fastGrowing_le_hardy_pow`).

The linchpin is the **Hardy iteration law** `H_{ω^e·(k+1)} = (H_{ω^e})^[k+1]`
(`hardy_oadd_iter`), whose engine is the **leading-term split**
`H_{ω^e·c + R}(n) = H_{ω^e·c}(H_R(n))` (`hardy_split`) — valid because the `NF` condition
`repr R < ω^(repr e)` is exactly the no-absorption side condition the Hardy additive law needs.
-/



/-- **Iterate domination.** If `f ≤ g` pointwise and `g` is monotone, then `f^[j] ≤ g^[j]`
pointwise. -/
theorem iterate_le_iterate {f g : ℕ → ℕ} (hfg : ∀ m, f m ≤ g m) (hg : Monotone g) :
    ∀ j x, f^[j] x ≤ g^[j] x := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ j ih =>
    intro x
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (ih (f x)).trans ((hg.iterate j) (hfg x))

/-- `(· + 1)^[j] n = n + j`. -/
theorem succ_iterate (j n : ℕ) : (fun m => m + 1)^[j] n = n + j := by
  induction j with
  | zero => simp
  | succ j ih => simp only [Function.iterate_succ_apply', ih]; omega

/-- **Leading-term split for the Hardy hierarchy.** For a normal-form notation `oadd e c R`
(so `repr R < ω^(repr e)`), the Hardy function splits its leading Cantor term off the tail:
`H_{ω^e·c + R}(n) = H_{ω^e·c}(H_R(n))`. Well-founded recursion on `repr R`. The `NF` hypothesis
is the no-absorption side condition that makes the Hardy additive law hold. -/
theorem hardy_split (e : ONote) (c : ℕ+) (R : ONote) (hNF : (oadd e c R).NF) (n : ℕ) :
    hardy (oadd e c R) n = hardy (oadd e c 0) (hardy R n) := by
  suffices H : ∀ o : Ordinal, ∀ R : ONote, R.repr = o → (oadd e c R).NF → ∀ n,
      hardy (oadd e c R) n = hardy (oadd e c 0) (hardy R n) by
    exact H R.repr R rfl hNF n
  intro o
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    intro R hrepr hNFR n
    have hNFe : e.NF := hNFR.fst
    have hbelowR : R.repr < ω ^ e.repr := hNFR.snd'.repr_lt
    rcases hfs : fundamentalSequence R with (_ | R') | g
    · -- R = 0
      have hR0 : R = 0 :=
        (fundamentalSequenceProp_inl_none R).1 (hfs ▸ fundamentalSequence_has_prop R)
      subst hR0
      simp
    · -- R successor R'
      have hsucc := (fundamentalSequenceProp_inl_some R R').1 (hfs ▸ fundamentalSequence_has_prop R)
      have hNFR' : R'.NF := hsucc.2 hNFR.snd
      have hltR' : R'.repr < o := by rw [← hrepr, hsucc.1]; exact Order.lt_succ _
      have hbelowR' : R'.repr < ω ^ e.repr :=
        lt_trans (by rw [hrepr]; exact hltR') hbelowR
      have hNFnew : (oadd e c R').NF := NF.oadd hNFe c (NF.below_of_lt' hbelowR' hNFR')
      have hfsnew : fundamentalSequence (oadd e c R) = Sum.inl (some (oadd e c R')) := by
        rw [fundamentalSequence, hfs]
      simp only [hardy_succ _ hfsnew, hardy_succ _ hfs]
      exact ih R'.repr hltR' R' rfl hNFnew (n + 1)
    · -- R limit g
      have hprop := hfs ▸ fundamentalSequence_has_prop R
      have hgnlt : (g n).repr < o := by rw [← hrepr]; exact repr_lt_repr (hprop.2.1 n).2.1
      have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFR.snd
      have hbelowgn : (g n).repr < ω ^ e.repr :=
        lt_trans (by rw [hrepr]; exact hgnlt) hbelowR
      have hNFnew : (oadd e c (g n)).NF := NF.oadd hNFe c (NF.below_of_lt' hbelowgn hNFgn)
      have hfsnew : fundamentalSequence (oadd e c R) = Sum.inr (fun i => oadd e c (g i)) := by
        rw [fundamentalSequence, hfs]
      simp only [hardy_limit _ hfsnew, hardy_limit _ hfs]
      exact ih (g n).repr hgnlt (g n) rfl hNFnew n

/-- Finite Hardy values: `H_{j+1}(n) = n + (j+1)` (the notation `oadd 0 ⟨j+1⟩ 0`). -/
theorem hardy_finite : ∀ j n, hardy (oadd 0 ⟨j + 1, Nat.succ_pos j⟩ 0) n = n + (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro n
    show hardy (oadd 0 1 0) n = n + 1
    rw [show (oadd (0 : ONote) 1 0) = 1 from rfl, hardy_one]
  | succ j ih =>
    intro n
    have hfs : fundamentalSequence (oadd 0 ⟨j + 2, Nat.succ_pos _⟩ 0)
        = Sum.inl (some (oadd 0 ⟨j + 1, Nat.succ_pos j⟩ 0)) := by
      rw [fundamentalSequence_oadd_zero_zero]; rfl
    simp only [hardy_succ _ hfs]
    rw [ih (n + 1)]; omega

/-- **Hardy coefficient step (nonzero exponent).** For `e ≠ 0`,
`H_{ω^e·(k+2)}(n) = H_{ω^e·(k+1)}(H_{ω^e}(n))`. The descent peels one coefficient
(`fundSeq_oadd_coeff`), then `hardy_split` separates the freshly-created lowest term, whose
Hardy value is exactly `H_{ω^e}(n)` (it is the index-`n` fundamental term of `ω^e`). -/
theorem hardy_oadd_coeff_step_ne (e : ONote) (he : e ≠ 0) (hNFe : e.NF) (k n : ℕ) :
    hardy (oadd e ⟨k + 2, Nat.succ_pos _⟩ 0) n
      = hardy (oadd e ⟨k + 1, Nat.succ_pos k⟩ 0) (hardy (oadd e 1 0) n) := by
  obtain ⟨g, hg1, hgk⟩ := fundSeq_oadd_coeff e he k
  have hNFe1 : (oadd e 1 0).NF := NF.oadd hNFe 1 NFBelow.zero
  have hprop := hg1 ▸ fundamentalSequence_has_prop (oadd e 1 0)
  have hgnlt : (g n).repr < (oadd e 1 0).repr := repr_lt_repr (hprop.2.1 n).2.1
  have hNFgn : (g n).NF := (hprop.2.1 n).2.2 hNFe1
  have hbelow : (g n).repr < ω ^ e.repr := by
    have he1 : (oadd e 1 0).repr = ω ^ e.repr := by simp
    rwa [he1] at hgnlt
  have hNFsplit : (oadd e k.succPNat (g n)).NF :=
    NF.oadd hNFe _ (NF.below_of_lt' hbelow hNFgn)
  simp only [hardy_limit _ hgk]
  show hardy (oadd e k.succPNat (g n)) n
      = hardy (oadd e k.succPNat 0) (hardy (oadd e 1 0) n)
  rw [hardy_split e k.succPNat (g n) hNFsplit n]
  have heq : hardy (oadd e 1 0) n = hardy (g n) n := by simp only [hardy_limit _ hg1]
  rw [heq]

/-- **The Hardy iteration law.** `H_{ω^e·(k+1)} = (H_{ω^e})^[k+1]`. For `e = 0` this is
`H_{k+1}(n) = n+(k+1) = (·+1)^[k+1] n`; for `e ≠ 0` it is induction on `k` via the coefficient
step `hardy_oadd_coeff_step_ne`. The linchpin tying Hardy coefficients to iteration. -/
theorem hardy_oadd_iter (e : ONote) (hNFe : e.NF) :
    ∀ k n, hardy (oadd e ⟨k + 1, Nat.succ_pos k⟩ 0) n = (hardy (oadd e 1 0))^[k + 1] n := by
  rcases eq_or_ne e 0 with rfl | he
  · -- e = 0
    have hg : hardy (oadd (0 : ONote) 1 0) = fun n => n + 1 := by
      rw [show (oadd (0 : ONote) 1 0) = 1 from rfl]; exact hardy_one
    intro k n
    rw [hardy_finite k n, hg, succ_iterate]
  · -- e ≠ 0: induction on k via the coefficient step
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have hcoeff := hardy_oadd_coeff_step_ne e he hNFe k n
      have hk2 : (⟨k + 1 + 1, Nat.succ_pos (k + 1)⟩ : ℕ+) = ⟨k + 2, Nat.succ_pos _⟩ := rfl
      rw [hk2, hcoeff, ih (hardy (oadd e 1 0) n), ← Function.iterate_succ_apply]

end Goodstein.Dom
