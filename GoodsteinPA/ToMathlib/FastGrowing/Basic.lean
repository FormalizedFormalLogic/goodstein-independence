/-
# Fast-growing hierarchy over `ONote` — basics and monotonicity

`ONote.fastGrowing` value/monotonicity lemmas, `Reaches`, and fundamental-sequence helpers.
-/
module

public import AlphaCentauri.ToMathlib.ONote.FastGrowing

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

/-- `id ≤ fastGrowing o`, i.e. `fastGrowing o` dominates the identity pointwise. -/
lemma id_le_fastGrowing (o : ONote) : (id : ℕ → ℕ) ≤ fastGrowing o :=
  fun m => le_fastGrowing o m

/-- **Index step at a successor**, proved directly.
If `o` is the successor of `a` (`fundamentalSequence o = inl (some a)`), then for a
positive argument the next index can only grow the value:
`f_a(n) ≤ f_o(n)`. Indeed `f_o n = (f_a)^[n] n ≥ (f_a)^[1] n = f_a n` once `1 ≤ n`. -/
lemma fastGrowing_le_succ_index (h : fundamentalSequence o = Sum.inl (some a)) (hn : 1 ≤ n) :
    fastGrowing a n ≤ fastGrowing o n := by
  rw [fastGrowing_succ o h]
  simpa using (Function.monotone_iterate_of_id_le (id_le_fastGrowing a) hn) n

/-! ### Structural Bachmann reachability, fully proved

The remaining difficulty in index monotonicity is now a pure statement about
`fundamentalSequence`: the descent of `o[n+1]` (budget `n+1`) passes exactly through
`o[n]`. We prove it by structural recursion on `o`, assembling four reusable facts:
`reaches_zero` (every notation descends to 0), `Reaches.oadd_tail` (descend a fixed
prefix's tail), `reaches_coeff_step'`/`reaches_coeff_chain` (drop a leading coefficient),
and `reaches_omega_pow_lift` (lift an exponent reach through `ω^·`). -/

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
lemma reaches_coeff_step' (e : ONote) (j x : ℕ) : Reaches x (oadd e (j + 1).succPNat 0) (oadd e j.succPNat 0) := by
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
lemma reaches_coeff_chain (e : ONote) (j x : ℕ) : Reaches x (oadd e j.succPNat 0) (oadd e (0 : ℕ).succPNat 0) := by
  induction j with
  | zero => exact Reaches.refl _
  | succ j ih => exact (reaches_coeff_step' e j x).trans ih

/-- **Exponent lifting:** a structural reach on exponents lifts through `ω^·`. -/
lemma reaches_omega_pow_lift {p r : ONote} (h : Reaches x p r) : Reaches x (oadd p 1 0) (oadd r 1 0) := by
  induction h with
  | refl c => exact Reaches.refl _
  | @succ p q r hb _ ih =>
      refine Reaches.limit (fundamentalSequence_omega_pow_succ hb) ?_
      exact (reaches_coeff_chain q x x).trans ih
  | @limit p r g hb _ ih =>
      exact Reaches.limit (fundamentalSequence_omega_pow_limit hb) ih

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
lemma fastGrowing_ofNat_mono (hmn : m ≤ n) (hx : 1 ≤ x) : fastGrowing (ofNat m) x ≤ fastGrowing (ofNat n) x :=
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
lemma fastGrowing_monotone_omega_mul (j : ℕ) : Monotone (fastGrowing (oadd 1 j.succPNat 0)) := by
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
lemma fastGrowing_le_succ (o : ONote) (n : ℕ) : fastGrowing o n ≤ fastGrowing o (n + 1) := by
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

/-
# Toward `fastGrowingε₀` dominating every fixed level

The technical content for establishing index domination that enables the Goodstein/Kirby–Paris
independence result. Continued in `Norm.lean` and `Epsilon0.lean`.
-/

end ONote
