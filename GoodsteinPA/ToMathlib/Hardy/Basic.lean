/-
# The Hardy hierarchy `H_α` — definition and basic values

The **Hardy hierarchy** `H_α : ℕ → ℕ` is the companion of the fast-growing hierarchy. This file
introduces it (mirroring `fastGrowing`'s structure on `ONote.fundamentalSequence`):
`H₀(n) = n`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)`.

The classical identity `H_{ω^α} = f_α` connects it back to `fastGrowing`. This file provides
characterization lemmas, monotonicity, and closed forms.
-/
module

public import GoodsteinPA.ToMathlib.FastGrowing.Epsilon0

@[expose] public section

namespace ONote

open ONote Ordinal

/-- The **Hardy hierarchy** `H_α : ℕ → ℕ` for ordinal notations `< ε₀`:
`H₀ = id`, `H_{α+1}(n) = H_α(n+1)`, `H_λ(n) = H_{λ[n]}(n)` (limit `λ`, via
`ONote.fundamentalSequence`). Same well-founded recursion as `ONote.fastGrowing`. -/
def hardy : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => id
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; exact Order.lt_succ _
      fun n => hardy a (n + 1)
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hardy (f n) n
  termination_by o => o

/-- If `fundamentalSequence o = Sum.inl none`, then `o = 0`. -/
lemma eq_zero_of_fundamentalSequence_inl_none {o : ONote} (e : fundamentalSequence o = Sum.inl none) :
    o = 0 := by
  have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact hp

/-- If `fundamentalSequence o = Sum.inl (some a)`, then `a < o`. -/
lemma lt_of_fundamentalSequence_inl_some {o a : ONote}
    (e : fundamentalSequence o = Sum.inl (some a)) : a < o := by
  have hp := fundamentalSequence_has_prop o; rw [e] at hp
  rw [lt_def, hp.1]; exact Order.lt_succ _

/-- If `fundamentalSequence o = Sum.inr f`, then every `f n < o`. -/
lemma fundamentalSequence_inr_lt {o : ONote} {f : ℕ → ONote}
    (e : fundamentalSequence o = Sum.inr f) (n : ℕ) : f n < o := by
  have hp := fundamentalSequence_has_prop o; rw [e] at hp
  exact (hp.2.1 n).2.1

/-- Unfolding lemma for `hardy`, mirroring `ONote.fastGrowing_def`. -/
lemma hardy_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hardy o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => id
      | Sum.inl (some a), _ => fun n => hardy a (n + 1)
      | Sum.inr f, _ => fun n => hardy (f n) n := by
  subst x
  rw [hardy]

/-- `H_o = id` when `o = 0` (the `inl none` branch). -/
@[grind =]
lemma hardy_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    hardy o = id := by
  rw [hardy_def h]

/-- `H_o(n) = H_a(n+1)` when `o` is the successor of `a`. -/
@[grind =>]
lemma hardy_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hardy o = fun n => hardy a (n + 1) := by
  rw [hardy_def h]

/-- `H_o(n) = H_{o[n]}(n)` when `o` is a limit with fundamental sequence `f`. -/
@[grind =>]
lemma hardy_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hardy o = fun n => hardy (f n) n := by
  rw [hardy_def h]

/-- `H₀ = id`. -/
@[simp]
lemma hardy_zero : hardy 0 = id :=
  hardy_zero' _ rfl

/-- `H₁(n) = n + 1` — the first successor level just adds one. -/
@[simp, grind =]
lemma hardy_one : hardy 1 = fun n => n + 1 := by
  rw [@hardy_succ 1 0 rfl]; funext n; rw [hardy_zero]; rfl

/-- `H₂(n) = n + 2`. -/
@[simp, grind =]
lemma hardy_two : hardy 2 = fun n => n + 2 := by
  rw [@hardy_succ 2 1 rfl]; funext n; rw [hardy_one]

/-! ### Growth theory of the Hardy hierarchy -/

/-- **Expansiveness of the Hardy hierarchy:** `n ≤ H_o(n)` for every notation `o`. -/
theorem le_hardy (o : ONote) (n : ℕ) : n ≤ hardy o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact le_rfl
  · have hlt : a < o := lt_of_fundamentalSequence_inl_some e
    rw [hardy_succ o e]
    exact le_trans (Nat.le_succ n) (le_hardy a (n + 1))
  · have hlt : f n < o := fundamentalSequence_inr_lt e n
    rw [hardy_limit o e]
    exact le_hardy (f n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Value transfer for the Hardy hierarchy:** If `b` structurally reaches `a` at budget `x` and every notation `b` reaches has monotone Hardy level, then `H_a(x) ≤ H_b(x)`. -/
theorem hardy_le_of_reaches {x : ℕ} {b a : ONote} (h : Reaches x b a) :
    (∀ γ, Reaches x b γ → Monotone (hardy γ)) → hardy a x ≤ hardy b x := by
  induction h with
  | refl a => intro _; exact le_rfl
  | @succ b γ a hb _ ih =>
      intro hmono
      have hmγ : Monotone (hardy γ) := hmono γ (Reaches.succ hb (Reaches.refl γ))
      have iha : hardy a x ≤ hardy γ x := ih (fun δ hδ => hmono δ (Reaches.succ hb hδ))
      have heq : hardy b x = hardy γ (x + 1) := by rw [hardy_succ _ hb]
      rw [heq]; exact le_trans iha (hmγ (Nat.le_succ x))
  | @limit b a g hb _ ih =>
      intro hmono
      have ihg : hardy a x ≤ hardy (g x) x := ih (fun δ hδ => hmono δ (Reaches.limit hb hδ))
      have heq : hardy b x = hardy (g x) x := by rw [hardy_limit _ hb]
      rw [heq]; exact ihg

/-- **Monotonicity in the argument** of each Hardy level, for every notation `o`. -/
theorem hardy_monotone (o : ONote) : Monotone (hardy o) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact Nat.le_succ n
  · have hlt : a < o := lt_of_fundamentalSequence_inl_some e
    rw [hardy_succ o e]
    exact hardy_monotone a (Nat.le_succ (n + 1))
  · have hlt : f n < o := fundamentalSequence_inr_lt e n
    have hltn1 : f (n + 1) < o := fundamentalSequence_inr_lt e (n + 1)
    rw [hardy_limit o e]
    have mono_fn : Monotone (hardy (f n)) := hardy_monotone (f n)
    have step : hardy (f n) (n + 1) ≤ hardy (f (n + 1)) (n + 1) := by
      apply hardy_le_of_reaches (fastGrowing_bachmann_reach e n)
      intro γ hγ
      have hγo : γ < o := lt_of_le_of_lt (reaches_le hγ) hltn1
      exact hardy_monotone γ
    exact le_trans (mono_fn (Nat.le_succ n)) step
termination_by o
decreasing_by
  · exact hlt
  · exact hlt
  · exact hγo

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

private lemma add_ofNat_succ {a : ONote} (ha : a.NF) (c : ℕ) :
    a + ofNat (c + 1) = osucc (a + ofNat c) := by
  haveI := ha
  haveI hac : (a + ofNat c).NF := ONote.add_nf a (ofNat c)
  haveI : (a + ofNat (c + 1)).NF := ONote.add_nf a (ofNat (c + 1))
  haveI : (osucc (a + ofNat c)).NF := osucc_NF hac
  apply repr_inj.mp
  rw [repr_osucc hac, repr_add, repr_add, repr_ofNat, repr_ofNat,
    Nat.cast_add, Nat.cast_one, ← add_assoc]

/-- **Hardy argument-shift / finite-tail additivity:** `H_{a+c}(n) = H_a(n+c)`. -/
theorem hardy_add_ofNat {a : ONote} (ha : a.NF) (c n : ℕ) :
    hardy (a + ofNat c) n = hardy a (n + c) := by
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
lemma hardy_ofNat_mono {m n : ℕ} (hmn : m ≤ n) (x : ℕ) :
    hardy (ofNat m) x ≤ hardy (ofNat n) x := by
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

/-- **General index monotonicity of the Hardy hierarchy:** For normal-form `a < b` and budget `x ≥ norm a`, `H_a(x) ≤ H_b(x)`. -/
theorem hardy_le_of_lt {x : ℕ} {a b : ONote} (ha : a.NF) (hb : b.NF)
  (hab : a < b) (hnorm : norm a ≤ x) : hardy a x ≤ hardy b x :=
  hardy_le_of_reaches (reaches_of_lt b hb a ha hab hnorm) (fun γ _ => hardy_monotone γ)

/-- **Closed form for finite Hardy levels:** `H_k(x) = x + k`. -/
@[simp, grind =]
lemma hardy_ofNat (k x : ℕ) : hardy (ofNat k) x = x + k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    simp only [hardy_succ _ (fundamentalSequence_ofNat_succ k)]
    rw [ih (x + 1)]; omega

/-- **Closed form for `H_ω`:** `H_ω(n) = 2n + 1`. -/
lemma hardy_omega (n : ℕ) : hardy (oadd 1 1 0) n = 2 * n + 1 := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  have h1 : hardy (oadd 1 1 0) n = hardy (ofNat (n + 1)) n := by
    simp only [hardy_limit _ hfs]
  rw [h1, hardy_ofNat (n + 1) n]
  omega

end ONote
