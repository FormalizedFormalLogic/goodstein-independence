/-
# The Hardy hierarchy `H_α` — definition and basic values

The **Hardy hierarchy** `H_α : ℕ → ℕ` is the companion of the fast-growing hierarchy. This file
introduces it (mirroring `fastGrowing`'s structure on `ONote.fundamentalSequence`):
`H₀(n) = n`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)`.

The classical identity `H_{ω^α} = f_α` connects it back to `fastGrowing`. This file provides
characterization lemmas, monotonicity, and closed forms.
-/
module

public import AlphaCentauri.ToMathlib.ONote.Hardy
public import GoodsteinPA.ToMathlib.FastGrowing.Epsilon0

@[expose] public section

namespace ONote

open ONote Ordinal

/-- If `fundamentalSequence o = Sum.inl none`, then `o = 0`. -/
lemma eq_zero_of_fundamentalSequence_inl_none {o : ONote} (e : fundamentalSequence o = Sum.inl none) : o = 0 := by
  have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact hp

/-- If `fundamentalSequence o = Sum.inl (some a)`, then `a < o`. -/
lemma lt_of_fundamentalSequence_inl_some {o a : ONote} (e : fundamentalSequence o = Sum.inl (some a)) : a < o := by
  have hp := fundamentalSequence_has_prop o; rw [e] at hp
  rw [lt_def, hp.1]; exact Order.lt_succ _

/-- If `fundamentalSequence o = Sum.inr f`, then every `f n < o`. -/
lemma fundamentalSequence_inr_lt {o : ONote} {f : ℕ → ONote}
    (e : fundamentalSequence o = Sum.inr f) (n : ℕ) : f n < o := by
  have hp := fundamentalSequence_has_prop o; rw [e] at hp
  exact (hp.2.1 n).2.1

/-- Unfolding lemma for `hardy`, mirroring `ONote.fastGrowing_def`.

Spelled as an explicit application of the matcher `ONote.hardy.match_1` rather than as `match`
syntax: Lean's matcher cache is module-local, so writing `match ... with` here would mint a fresh
`ONote.hardy_def.match_1` and change this statement.  The two are definitionally equal. -/
lemma hardy_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hardy o = ONote.hardy.match_1 o (motive := fun _ _ => ℕ → ℕ) x
        (e ▸ fundamentalSequence_has_prop o)
        (fun _ => id) (fun a _ n => hardy a (n + 1)) (fun f _ n => hardy (f n) n) := by
  subst x; rw [hardy]

/-- `H₂(n) = n + 2`. -/
@[simp, grind =]
lemma hardy_two : hardy 2 = fun n => n + 2 := by
  rw [@hardy_succ 2 1 rfl]; funext n; rw [hardy_one]

/-! ### Growth theory of the Hardy hierarchy -/

/-- **Monotonicity in the argument, successor form** `H_o(n) ≤ H_o(n+1)`. -/
@[grind .]
lemma hardy_le_succ (o : ONote) (n : ℕ) : hardy o n ≤ hardy o (n + 1) :=
  hardy_monotone o (Nat.le_succ n)

/-! ### Hardy argument-shift

`H_{a+c}(n) = H_a(n+c)` for finite `c`.
-/

private lemma add_ofNat_zero {a : ONote} (ha : a.NF) : a + ofNat 0 = a := by
  haveI := ha
  haveI : (0 : ONote).NF := NF.zero
  rw [ofNat_zero]
  haveI : (a + 0).NF := ONote.add_nf a 0
  apply repr_inj.mp
  rw [repr_add, repr_zero, add_zero]

private lemma add_ofNat_succ {a : ONote} (ha : a.NF) (c : ℕ) : a + ofNat (c + 1) = osucc (a + ofNat c) := by
  haveI := ha
  haveI hac : (a + ofNat c).NF := ONote.add_nf a (ofNat c)
  haveI : (a + ofNat (c + 1)).NF := ONote.add_nf a (ofNat (c + 1))
  haveI : (osucc (a + ofNat c)).NF := osucc_NF hac
  apply repr_inj.mp
  rw [repr_osucc hac, repr_add, repr_add, repr_ofNat, repr_ofNat,
    Nat.cast_add, Nat.cast_one, ← add_assoc]

/-- **Hardy argument-shift / finite-tail additivity:** `H_{a+c}(n) = H_a(n+c)`. -/
theorem hardy_add_ofNat {a : ONote} (ha : a.NF) (c n : ℕ) : hardy (a + ofNat c) n = hardy a (n + c) := by
  induction c generalizing n with
  | zero => rw [add_ofNat_zero ha]; simp
  | succ c ih =>
    rw [add_ofNat_succ ha c]
    have hs := hardy_succ (osucc (a + ofNat c))
      (fundamentalSequence_osucc (ONote.add_nf a (ofNat c)))
    rw [hs]
    show hardy (a + ofNat c) (n + 1) = hardy a (n + (c + 1))
    rw [ih (n + 1)]
    congr 1
    omega

/-- **The Hardy index-monotonicity crux (limit step):** For a limit `o` with fundamental sequence `f`, `H_{o[n]}(n+1) ≤ H_{o[n+1]}(n+1)`. -/
lemma hardy_fundSeq_step {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    hardy (f n) (n + 1) ≤ hardy (f (n + 1)) (n + 1) :=
  hardy_le_of_reaches (fastGrowing_bachmann_reach h n) (fun γ _ => hardy_monotone γ)

/-- **Finite-level argument monotonicity for Hardy:** `Monotone (H_k)` for `k : ℕ`. -/
lemma hardy_ofNat_monotone (k : ℕ) : Monotone (hardy (ofNat k)) := by
  induction k with
  | zero => simpa [ofNat_zero, hardy_zero] using monotone_id
  | succ k ih =>
      rw [hardy_succ _ (fundamentalSequence_ofNat_succ k)]
      exact ih.comp (monotone_id.add_const 1)

/-- **Finite-level index monotonicity for Hardy:** For `m ≤ n`, `H_m(x) ≤ H_n(x)`. -/
@[grind .]
lemma hardy_ofNat_mono {m n : ℕ} (hmn : m ≤ n) (x : ℕ) : hardy (ofNat m) x ≤ hardy (ofNat n) x := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
      refine le_trans ih ?_
      rw [hardy_succ _ (fundamentalSequence_ofNat_succ n)]
      exact hardy_ofNat_monotone n (Nat.le_succ x)

/-- **Monotonicity of `H_ω`:** The Hardy companion of `fastGrowing_monotone_omega`. -/
lemma hardy_monotone_omega : Monotone (hardy (oadd 1 1 0)) := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [hardy_limit _ hfs]
  calc hardy (ofNat (n + 1)) n
      ≤ hardy (ofNat (n + 1)) (n + 1) := hardy_ofNat_monotone (n + 1) (Nat.le_succ n)
    _ ≤ hardy (ofNat (n + 2)) (n + 1) := hardy_ofNat_mono (Nat.le_succ (n + 1)) (n + 1)

end ONote
