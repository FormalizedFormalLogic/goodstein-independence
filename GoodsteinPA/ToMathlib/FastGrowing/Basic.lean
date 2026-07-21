/-
# Fast-growing hierarchy over `ONote` — basics and monotonicity

`ONote.fastGrowing` value/monotonicity lemmas, `Reaches`, and fundamental-sequence helpers.
-/
module

public import Mathlib.SetTheory.Ordinal.Notation

@[expose] public section

namespace ONote

open ONote Ordinal

variable {o a b : ONote} {f g : ℕ → ONote} {m n x : ℕ}

/-
# Growth theory of the fast-growing hierarchy

Core monotonicity and expansiveness of the fast-growing hierarchy on ordinal notations below `ε₀`,
the structural `Reaches` descent relation, and the Bachmann reachability result (proved axiom-clean
via CNF fundamental sequences). — Targets for mathlib.
-/



/-- If `fundamentalSequence o = inl (some a)` (`o` is the notation-successor of `a`), then `a < o`. -/
lemma lt_of_fundamentalSequence_succ (h : fundamentalSequence o = Sum.inl (some a)) : a < o := by
  have hp := fundamentalSequence_has_prop o
  rw [h] at hp
  rw [lt_def, hp.1]; exact Order.lt_succ _

/-- If `fundamentalSequence o = inr g` (`o` is a limit with fundamental sequence `g`), then every `g n < o`. -/
lemma fundamentalSequence_lt_of_limit (h : fundamentalSequence o = Sum.inr g) (n : ℕ) : g n < o := by
  have hp := fundamentalSequence_has_prop o
  rw [h] at hp
  exact (hp.2.1 n).2.1

/-- **Expansiveness:** every level of the fast-growing hierarchy dominates the identity, `n ≤ f_o(n)`. -/
theorem le_fastGrowing (o : ONote) (n : ℕ) : n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · -- `o = 0`: `fastGrowing o = Nat.succ`
    rw [fastGrowing_zero' o e]
    exact Nat.le_succ n
  · -- successor: `fastGrowing o n = (fastGrowing a)^[n] n`, `a < o`
    have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [fastGrowing_succ o e]
    exact Function.id_le_iterate_of_id_le (fun m => le_fastGrowing a m) n n
  · -- limit: `fastGrowing o n = fastGrowing (f n) n`, `f n < o`
    have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    rw [fastGrowing_limit o e]
    exact le_fastGrowing (f n) n
termination_by o
decreasing_by all_goals exact hlt

/-- `id ≤ fastGrowing o`, i.e. `fastGrowing o` dominates the identity pointwise. -/
lemma id_le_fastGrowing (o : ONote) : (id : ℕ → ℕ) ≤ fastGrowing o :=
  fun m => le_fastGrowing o m

/-- **Strict expansiveness for positive input:** for `n ≥ 1`, `n < f_o(n)`. -/
theorem lt_fastGrowing (o : ONote) (hn : 1 ≤ n) : n < fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [fastGrowing_zero' o e]
    exact Nat.lt_succ_self n
  · have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [fastGrowing_succ o e]
    -- `n < f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
    have hstep : fastGrowing a n ≤ (fastGrowing a)^[n] n := by
      have hmono := Function.monotone_iterate_of_id_le (id_le_fastGrowing a) hn
      simpa using hmono n
    exact lt_of_lt_of_le (lt_fastGrowing a hn) hstep
  · have hlt : f n < o := fundamentalSequence_lt_of_limit e n
    rw [fastGrowing_limit o e]
    exact lt_fastGrowing (f n) hn
termination_by o
decreasing_by all_goals exact hlt

/-- **Index step at a successor**, proved directly.
If `o` is the successor of `a` (`fundamentalSequence o = inl (some a)`), then for a
positive argument the next index can only grow the value:
`f_a(n) ≤ f_o(n)`. Indeed `f_o n = (f_a)^[n] n ≥ (f_a)^[1] n = f_a n` once `1 ≤ n`. -/
lemma fastGrowing_le_succ_index (h : fundamentalSequence o = Sum.inl (some a)) (hn : 1 ≤ n) :
    fastGrowing a n ≤ fastGrowing o n := by
  rw [fastGrowing_succ o h]
  simpa using (Function.monotone_iterate_of_id_le (id_le_fastGrowing a) hn) n

/-- **Structural descent relation** `Reaches x p r`: from `p` one can step down to `r`
through `fundamentalSequence`, using *predecessor* steps at successor notations and
*index-`x`* steps at limit notations. This is a purely structural (no `fastGrowing`)
relation on `ONote`, and it is exactly the "Bachmann path" along which the fast-growing
hierarchy is monotone in the index. -/
inductive Reaches (x : ℕ) : ONote → ONote → Prop
  | refl (a : ONote) : Reaches x a a
  | succ {p q r : ONote} (h : fundamentalSequence p = Sum.inl (some q))
      (hr : Reaches x q r) : Reaches x p r
  | limit {p r : ONote} {g : ℕ → ONote} (h : fundamentalSequence p = Sum.inr g)
      (hr : Reaches x (g x) r) : Reaches x p r

/-- `Reaches x` is transitive (paths compose). -/
lemma Reaches.trans {c : ONote} (h1 : Reaches x a b) (h2 : Reaches x b c) : Reaches x a c := by
  induction h1 with
  | refl a => exact h2
  | succ h _ ih => exact Reaches.succ h (ih h2)
  | limit h _ ih => exact Reaches.limit h (ih h2)

/-- **Value transfer:** if `p` reaches `r` structurally with positive budget `x`, then `f_r(x) ≤ f_p(x)`. -/
theorem fastGrowing_le_of_reaches (hx : 1 ≤ x) (h : Reaches x p r) : fastGrowing r x ≤ fastGrowing p x := by
  induction h with
  | refl a => exact le_rfl
  | succ hb _ ih => exact le_trans ih (fastGrowing_le_succ_index hb hx)
  | limit hb _ ih => rw [fastGrowing_limit _ hb]; exact ih

/-- A structural reach only goes *down* the ordinal order: `Reaches x p r → r ≤ p`. -/
@[grind →]
lemma reaches_le (h : Reaches x p r) : r ≤ p := by
  induction h with
  | refl a => exact le_rfl
  | @succ p q r hb _ ih =>
      exact le_trans ih (lt_of_fundamentalSequence_succ hb).le
  | @limit p r g hb _ ih =>
      exact le_trans ih (fundamentalSequence_lt_of_limit hb x).le

/-! ### Structural Bachmann reachability, fully proved

The remaining difficulty in index monotonicity is now a pure statement about
`fundamentalSequence`: the descent of `o[n+1]` (budget `n+1`) passes exactly through
`o[n]`. We prove it by structural recursion on `o`, assembling four reusable facts:
`reaches_zero` (every notation descends to 0), `Reaches.oadd_tail` (descend a fixed
prefix's tail), `reaches_coeff_step'`/`reaches_coeff_chain` (drop a leading coefficient),
and `reaches_omega_pow_lift` (lift an exponent reach through `ω^·`). -/

/-- Lifting a successor tail step to `oadd a m ·`. -/
-- `@[grind =]` fails to find patterns since `b'`/`h` don't occur in the LHS pattern;
-- `@[grind =>]` treats it as a forward implication instead.
@[grind =>]
lemma fundamentalSequence_oadd_succ {m : ℕ+} {b' : ONote} (h : fundamentalSequence b = Sum.inl (some b')) :
    fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
  conv_lhs => rw [fundamentalSequence]; rw [h]

/-- Lifting a limit tail step to `oadd a m ·`. -/
-- `@[grind =]` fails (same reason as `fundamentalSequence_oadd_succ`); use `@[grind =>]`.
@[grind =>]
lemma fundamentalSequence_oadd_limit {m : ℕ+} {h : ℕ → ONote} (hb : fundamentalSequence b = Sum.inr h) :
    fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (h i)) := by
  conv_lhs => rw [fundamentalSequence]; rw [hb]

/-- A structural reach on the tail lifts to the whole `oadd a m ·`. -/
-- `@[grind →]` fails to find a trigger pattern for the inductive `Reaches` hypothesis;
-- `@[grind =>]` works instead.
@[grind =>]
lemma Reaches.oadd_tail {m : ℕ+} {d' d : ONote} (h : Reaches x d' d) :
    Reaches x (oadd a m d') (oadd a m d) := by
  induction h with
  | refl c => exact Reaches.refl _
  | succ hb _ ih => exact Reaches.succ (fundamentalSequence_oadd_succ hb) ih
  | limit hb _ ih => exact Reaches.limit (fundamentalSequence_oadd_limit hb) ih

/-- Every notation descends to 0 via fixed-budget fundamental-sequence descent. -/
lemma reaches_zero (o : ONote) (x : ℕ) : Reaches x o 0 := by
  rcases e : fundamentalSequence o with (_ | a) | g
  · have ho : o = 0 := by have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact hp
    rw [ho]; exact Reaches.refl 0
  · have hlt : a < o := lt_of_fundamentalSequence_succ e
    exact Reaches.succ e (reaches_zero a x)
  · have hlt : g x < o := fundamentalSequence_lt_of_limit e x
    exact Reaches.limit e (reaches_zero (g x) x)
termination_by o
decreasing_by all_goals exact hlt

/-- **Coefficient step:** `ω^e·(j+2)` descends to `ω^e·(j+1)` with any budget. -/
lemma reaches_coeff_step' (e : ONote) (j x : ℕ) :
    Reaches x (oadd e (j + 1).succPNat 0) (oadd e j.succPNat 0) := by
  rcases he : fundamentalSequence e with (_ | e') | p
  · have h0 : e = 0 := by have hp := fundamentalSequence_has_prop e; rw [he] at hp; exact hp
    subst h0
    refine Reaches.succ ?_ (Reaches.refl _)
    conv_lhs => rw [fundamentalSequence]
    rfl
  · have hlim : fundamentalSequence (oadd e (j + 1).succPNat 0)
        = Sum.inr (fun i => oadd e j.succPNat (oadd e' i.succPNat 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [he]; rfl
    exact Reaches.limit hlim (Reaches.oadd_tail (reaches_zero (oadd e' x.succPNat 0) x))
  · have hlim : fundamentalSequence (oadd e (j + 1).succPNat 0)
        = Sum.inr (fun i => oadd e j.succPNat (oadd (p i) 1 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [he]; rfl
    exact Reaches.limit hlim (Reaches.oadd_tail (reaches_zero (oadd (p x) 1 0) x))

/-- **Coefficient chain:** `ω^e·(j+1)` descends to `ω^e·1`. -/
lemma reaches_coeff_chain (e : ONote) (j x : ℕ) :
    Reaches x (oadd e j.succPNat 0) (oadd e (0 : ℕ).succPNat 0) := by
  induction j with
  | zero => exact Reaches.refl _
  | succ j ih => exact (reaches_coeff_step' e j x).trans ih

/-- Fundamental sequence of `ω^{successor exponent}`. -/
-- `@[grind =]` fails (same reason as `fundamentalSequence_oadd_succ`); use `@[grind =>]`.
@[grind =>]
lemma fundamentalSequence_omega_pow_succ (he : fundamentalSequence o = Sum.inl (some a)) :
    fundamentalSequence (oadd o 1 0) = Sum.inr (fun i => oadd a i.succPNat 0) := by
  conv_lhs => rw [fundamentalSequence]
  rw [he]; rfl

/-- Fundamental sequence of `ω^{limit exponent}`. -/
-- `@[grind =]` fails (same reason as `fundamentalSequence_oadd_succ`); use `@[grind =>]`.
@[grind =>]
lemma fundamentalSequence_omega_pow_limit {q : ℕ → ONote} (he : fundamentalSequence o = Sum.inr q) :
    fundamentalSequence (oadd o 1 0) = Sum.inr (fun i => oadd (q i) 1 0) := by
  conv_lhs => rw [fundamentalSequence]
  rw [he]; rfl

/-- **Exponent lifting:** a structural reach on exponents lifts through `ω^·`. -/
lemma reaches_omega_pow_lift {p r : ONote} (h : Reaches x p r) : Reaches x (oadd p 1 0) (oadd r 1 0) := by
  induction h with
  | refl c => exact Reaches.refl _
  | @succ p q r hb _ ih =>
      refine Reaches.limit (fundamentalSequence_omega_pow_succ hb) ?_
      exact (reaches_coeff_chain q x x).trans ih
  | @limit p r g hb _ ih =>
      exact Reaches.limit (fundamentalSequence_omega_pow_limit hb) ih

/-- The fundamental sequence of a successor *natural-number* notation is its
predecessor: `(k+1)[·] = k`. (Both branches reduce to `rfl`.) -/
@[simp, grind =]
lemma fundamentalSequence_ofNat_succ (k : ℕ) :
    fundamentalSequence (ofNat (k + 1)) = Sum.inl (some (ofNat k)) := by
  cases k with
  | zero => rfl
  | succ k' => rfl

/-- **Telescoping index monotonicity along a successor chain:** if `g` is a successor chain,
then `f_{g m}(x) ≤ f_{g n}(x)` for `m ≤ n` and `1 ≤ x`. -/
lemma fastGrowing_succ_chain_mono
    (hchain : ∀ k, fundamentalSequence (g (k + 1)) = Sum.inl (some (g k)))
    (hmn : m ≤ n) (hx : 1 ≤ x) :
    fastGrowing (g m) x ≤ fastGrowing (g n) x := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (fastGrowing_le_succ_index (hchain n) hx)

/-- **Finite-level index monotonicity** (the base case): `m ≤ n`, `1 ≤ x ⟹ f_m(x) ≤
f_n(x)`. The `ofNat` instance of `fastGrowing_succ_chain_mono`. -/
lemma fastGrowing_ofNat_mono (hmn : m ≤ n) (hx : 1 ≤ x) :
    fastGrowing (ofNat m) x ≤ fastGrowing (ofNat n) x :=
  fastGrowing_succ_chain_mono fundamentalSequence_ofNat_succ hmn hx

/-- **Finite-level argument monotonicity:** each `f_k` is monotone in its argument. -/
lemma fastGrowing_ofNat_monotone (k : ℕ) : Monotone (fastGrowing (ofNat k)) := by
  induction k with
  | zero =>
      simp only [ofNat_zero, fastGrowing_zero]
      exact fun a b h => Nat.succ_le_succ h
  | succ k ih =>
      rw [fastGrowing_succ _ (fundamentalSequence_ofNat_succ k)]
      intro a b hab
      calc (fastGrowing (ofNat k))^[a] a
          ≤ (fastGrowing (ofNat k))^[a] b := ih.iterate a hab
        _ ≤ (fastGrowing (ofNat k))^[b] b :=
              (Function.monotone_iterate_of_id_le (id_le_fastGrowing (ofNat k)) hab) b

/-- **The Bachmann reachability property (axiom-clean):** for a limit `o` with fundamental sequence `f`,
the next index `f (n+1)` reaches the current index `f n` with budget `n+1`. -/
theorem fastGrowing_bachmann_reach {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    Reaches (n + 1) (f (n + 1)) (f n) := by
  cases o with
  | zero => exact (Sum.inl_ne_inr h).elim
  | oadd a m b =>
    rcases hb : fundamentalSequence b with (_ | b') | hbf
    · -- b = 0 : leading-term cases
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 : `oadd 0 m 0` is a successor → contradicts the limit hypothesis
        rcases hm : m.natPred with _ | k
        · rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inl_ne_inr h).elim
        · rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inl_ne_inr h).elim
      · -- a successor (predecessor a')
        rcases hm : m.natPred with _ | k
        · have hf : f = fun i => oadd a' i.succPNat 0 := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]; exact reaches_coeff_step' a' n (n + 1)
        · have hf : f = fun i => oadd a k.succPNat (oadd a' i.succPNat 0) := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]; exact Reaches.oadd_tail (reaches_coeff_step' a' n (n + 1))
      · -- a limit (fundamental sequence p) : the ω^{limit} residue, via exponent lifting
        rcases hm : m.natPred with _ | k
        · have hf : f = fun i => oadd (p i) 1 0 := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]; exact reaches_omega_pow_lift (fastGrowing_bachmann_reach ha n)
        · have hf : f = fun i => oadd a k.succPNat (oadd (p i) 1 0) := by
            rw [fundamentalSequence, hb, ha, hm] at h; exact (Sum.inr.inj h).symm
          rw [hf]
          exact Reaches.oadd_tail (reaches_omega_pow_lift (fastGrowing_bachmann_reach ha n))
    · -- b a successor ⟹ `oadd a m b` is a successor → contradiction
      rw [fundamentalSequence_oadd_succ hb] at h; exact (Sum.inl_ne_inr h).elim
    · -- b a limit : descend the tail, recursing on b
      have hf : f = fun i => oadd a m (hbf i) := by
        rw [fundamentalSequence_oadd_limit hb] at h; exact (Sum.inr.inj h).symm
      rw [hf]; exact Reaches.oadd_tail (fastGrowing_bachmann_reach hb n)

/-- **The index-monotonicity limit step:** for a limit `o` with fundamental sequence `f`,
`f_{o[n]}(n+1) ≤ f_{o[n+1]}(n+1)`. -/
lemma fastGrowing_fundSeq_step
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    fastGrowing (f n) (n + 1) ≤ fastGrowing (f (n + 1)) (n + 1) :=
  fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n)) (fastGrowing_bachmann_reach h n)

/-- **Index-monotonicity for successor-chain limits:** if the fundamental sequence is a
successor chain, the index step reduces to `fastGrowing_le_succ_index`. -/
lemma fastGrowing_fundSeq_step_of_succ
    (_h : fundamentalSequence o = Sum.inr f)
    (hsucc : ∀ k, fundamentalSequence (f (k + 1)) = Sum.inl (some (f k))) (n : ℕ) :
    fastGrowing (f n) (n + 1) ≤ fastGrowing (f (n + 1)) (n + 1) :=
  fastGrowing_le_succ_index (hsucc n) (Nat.succ_le_succ (Nat.zero_le n))

/-- **Monotonicity propagates across a successor step:** if `o` is the notation-successor of `a`
and `f_a` is monotone, then so is `f_o`. -/
lemma fastGrowing_monotone_succ
    (h : fundamentalSequence o = Sum.inl (some a)) (ha : Monotone (fastGrowing a)) :
    Monotone (fastGrowing o) := by
  rw [fastGrowing_succ o h]
  intro p q hpq
  calc (fastGrowing a)^[p] p
      ≤ (fastGrowing a)^[p] q := ha.iterate p hpq
    _ ≤ (fastGrowing a)^[q] q :=
          (Function.monotone_iterate_of_id_le (id_le_fastGrowing a) hpq) q

/-- **Monotonicity for successor-chain limits:** if the fundamental sequence is a successor chain
and the bottom level is monotone, then `f_o` is monotone. -/
lemma fastGrowing_monotone_of_succ_chain_limit
    (hlim : fundamentalSequence o = Sum.inr f)
    (hchain : ∀ k, fundamentalSequence (f (k + 1)) = Sum.inl (some (f k)))
    (hmono0 : Monotone (fastGrowing (f 0))) :
    Monotone (fastGrowing o) := by
  have hmono : ∀ k, Monotone (fastGrowing (f k)) := by
    intro k
    induction k with
    | zero => exact hmono0
    | succ k ih => exact fastGrowing_monotone_succ (hchain k) ih
  apply monotone_nat_of_le_succ
  intro n
  rw [fastGrowing_limit o hlim]
  calc fastGrowing (f n) n
      ≤ fastGrowing (f n) (n + 1) := hmono n (Nat.le_succ n)
    _ ≤ fastGrowing (f (n + 1)) (n + 1) := fastGrowing_fundSeq_step_of_succ hlim hchain n

/-- **`f_ω` is monotone (axiom-clean).** -/
lemma fastGrowing_monotone_omega : Monotone (fastGrowing (oadd 1 1 0)) := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  exact fastGrowing_monotone_of_succ_chain_limit hfs
    (fun k => fundamentalSequence_ofNat_succ (k + 1)) (fastGrowing_ofNat_monotone 1)

/-- **`f_{ω·(j+1)}` is monotone for every `j` — the whole `ω·k` family (axiom-clean).** -/
lemma fastGrowing_monotone_omega_mul (j : ℕ) :
    Monotone (fastGrowing (oadd 1 j.succPNat 0)) := by
  induction j with
  | zero => exact fastGrowing_monotone_omega
  | succ j ih =>
      have hlim : fundamentalSequence (oadd 1 (j + 1).succPNat 0)
          = Sum.inr (fun i => oadd 1 j.succPNat (ofNat (i + 1))) := rfl
      refine fastGrowing_monotone_of_succ_chain_limit hlim (fun k => rfl) ?_
      have hsucc0 : fundamentalSequence (oadd 1 j.succPNat (ofNat (0 + 1)))
          = Sum.inl (some (oadd 1 j.succPNat 0)) := rfl
      exact fastGrowing_monotone_succ hsucc0 ih

/-- An `oadd` whose tail is a *finite successor* `ofNat (t+1)` is itself a notation
successor (of the same `oadd` with tail `ofNat t`). The structural fact powering every
"finite tail" successor chain. -/
lemma fundamentalSequence_oadd_ofNat_succ (a : ONote) (m : ℕ+) (t : ℕ) :
    fundamentalSequence (oadd a m (ofNat (t + 1))) = Sum.inl (some (oadd a m (ofNat t))) := by
  cases t <;> rfl

/-- **The `ω^2` index step (first instance outside the successor-chain class, axiom-clean).** -/
lemma fastGrowing_omega_sq_index_step (n : ℕ) :
    fastGrowing (oadd 1 n.succPNat 0) (n + 1)
      ≤ fastGrowing (oadd 1 (n + 1).succPNat 0) (n + 1) := by
  have hlim : fundamentalSequence (oadd 1 (n + 1).succPNat 0)
      = Sum.inr (fun i => oadd 1 n.succPNat (ofNat (i + 1))) := rfl
  rw [fastGrowing_limit _ hlim]
  have hchain : ∀ t, fundamentalSequence (oadd 1 n.succPNat (ofNat (t + 1)))
      = Sum.inl (some (oadd 1 n.succPNat (ofNat t))) :=
    fun t => fundamentalSequence_oadd_ofNat_succ 1 n.succPNat t
  have key := fastGrowing_succ_chain_mono (g := fun t => oadd 1 n.succPNat (ofNat t))
    hchain (m := 0) (n := n + 2) (Nat.zero_le _) (x := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  simpa using key

/-- **`f_{ω^2}` is monotone (axiom-clean).** The first limit level outside the successor-chain class. -/
lemma fastGrowing_monotone_omega_sq : Monotone (fastGrowing (oadd (ofNat 2) 1 0)) := by
  have hlim : fundamentalSequence (oadd (ofNat 2) 1 0)
      = Sum.inr (fun i => oadd 1 i.succPNat 0) := rfl
  apply monotone_nat_of_le_succ
  intro n
  rw [fastGrowing_limit _ hlim]
  calc fastGrowing (oadd 1 n.succPNat 0) n
      ≤ fastGrowing (oadd 1 n.succPNat 0) (n + 1) :=
        fastGrowing_monotone_omega_mul n (Nat.le_succ n)
    _ ≤ fastGrowing (oadd 1 (n + 1).succPNat 0) (n + 1) := fastGrowing_omega_sq_index_step n

/-- **Monotonicity in the argument, successor form:** `f_o(n) ≤ f_o(n+1)`. -/
lemma fastGrowing_le_succ (o : ONote) (n : ℕ) :
    fastGrowing o n ≤ fastGrowing o (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | g
  · rw [fastGrowing_zero' o e]
    exact Nat.le_succ _
  · -- successor: `(f_a)^[n] n ≤ (f_a)^[n+1] (n+1)`
    have hlt : a < o := lt_of_fundamentalSequence_succ e
    rw [fastGrowing_succ o e]
    have hmono_a : Monotone (fastGrowing a) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ a k
    calc (fastGrowing a)^[n] n
        ≤ (fastGrowing a)^[n] (n + 1) := hmono_a.iterate n (Nat.le_succ n)
      _ ≤ (fastGrowing a)^[n + 1] (n + 1) := by
            rw [Function.iterate_succ_apply']
            exact le_fastGrowing a _
  · -- limit: `f_{g n}(n) ≤ f_{g (n+1)}(n+1)`
    have hlt : g n < o := fundamentalSequence_lt_of_limit e n
    rw [fastGrowing_limit o e]
    have hmono_gn : Monotone (fastGrowing (g n)) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ (g n) k
    calc fastGrowing (g n) n
        ≤ fastGrowing (g n) (n + 1) := hmono_gn (Nat.le_succ n)
      _ ≤ fastGrowing (g (n + 1)) (n + 1) := fastGrowing_fundSeq_step e n
termination_by o
decreasing_by all_goals exact hlt

/-- **Monotonicity in the argument:** each level `f_o` is monotone. -/
theorem fastGrowing_monotone (o : ONote) : Monotone (fastGrowing o) :=
  monotone_nat_of_le_succ (fastGrowing_le_succ o)


/-
# Toward `fastGrowingε₀` dominating every fixed level

The technical content for establishing index domination that enables the Goodstein/Kirby–Paris
independence result. Continued in `Norm.lean` and `Epsilon0.lean`.
-/

end ONote
