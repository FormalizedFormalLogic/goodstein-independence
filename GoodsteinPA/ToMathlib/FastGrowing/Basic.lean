/-
# Fast-growing hierarchy over `ONote` — basics and monotonicity

`ONote.fastGrowing` value/monotonicity lemmas, `Reaches`, and fundamental-sequence helpers.
-/
module

public import Mathlib.SetTheory.Ordinal.Notation
public meta import Mathlib.SetTheory.Ordinal.Notation  -- shake: keep
public import Mathlib.Order.Iterate

@[expose] public section

namespace GoodsteinPA.FastGrowing

open ONote Ordinal

/-
# Growth theory of the fast-growing hierarchy

`Mathlib.SetTheory.Ordinal.Notation` already provides the **fast-growing hierarchy**
on ordinal notations below `ε₀`:

* `ONote.fastGrowing : ONote → ℕ → ℕ`  with `f₀ = succ`, `f_{α+1} = fun n => f_α^[n] n`,
  `f_λ = fun n => f_{λ[n]} n` (limit `λ`, via `ONote.fundamentalSequence`);
* `ONote.fastGrowingε₀ : ℕ → ℕ`, the one-step extension to `ε₀` itself.

mathlib proves the *small values* (`fastGrowing_one = (2 * ·)`, `fastGrowing_two = fun n => 2^n * n`,
`fastGrowingε₀_zero = 1`, `fastGrowingε₀_one = 2`) but **none of the growth theory**:
no expansiveness, no monotonicity, no domination. Those are exactly the facts the
Kirby–Paris growth argument needs, and they are the targets here.

These lemmas are mathlib-PR-shaped (they belong next to `ONote.fastGrowing`); developing
them here both serves the Goodstein-independence growth content and is independently useful.

## Normal-form hypotheses
`fastGrowing` is total on all of `ONote`, but the intended (and provable) statements
hold for **normal-form** notations (`ONote.NF`). Carry `[o.NF]`/`(h : o.NF)` where the
proof needs it; the `fundamentalSequence` correctness lemmas
(`ONote.fundamentalSequence_has_prop`, `ONote.FundamentalSequenceProp`) and the
`fastGrowing_zero'/_succ/_limit` characterizations are the entry points.
-/



/-- **Expansiveness.** Every level of the fast-growing hierarchy dominates the
identity: `n ≤ f_o(n)` for every notation `o` (no normal-form hypothesis needed —
`fundamentalSequence_has_prop` holds for all `o`).

Proof by well-founded recursion on `o` (the same `<`-recursion that *defines*
`fastGrowing`), via the three characterizations `fastGrowing_zero'/_succ/_limit`:
* `o = 0`: `f_o = Nat.succ`, so `n ≤ n+1`.
* successor `o = a+1`: `f_o n = (f_a)^[n] n`; by IH `id ≤ f_a`, and iterating a
  function that dominates the identity stays `≥ id` (`id_le_iterate_of_id_le`).
* limit: `f_o n = f_{o[n]} n` with `o[n] < o`, so the IH applies directly. -/
theorem le_fastGrowing (o : ONote) (n : ℕ) : n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · -- `o = 0`: `fastGrowing o = Nat.succ`
    rw [fastGrowing_zero' o e]
    exact Nat.le_succ n
  · -- successor: `fastGrowing o n = (fastGrowing a)^[n] n`, `a < o`
    have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    have ih : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    exact Function.id_le_iterate_of_id_le ih n n
  · -- limit: `fastGrowing o n = fastGrowing (f n) n`, `f n < o`
    have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    exact le_fastGrowing (f n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Strict expansiveness for positive input.** For `n ≥ 1` every level strictly
exceeds the identity, `n < f_o(n)`.

Same well-founded recursion as `le_fastGrowing`:
* `o = 0`: `f_o n = n+1 > n`.
* successor: `n < f_a n` (strict IH) and `f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
  (iterate count is monotone for `id ≤ f_a`, and `1 ≤ n`).
* limit: `n < f_{o[n]} n` directly by the strict IH at `o[n] < o`. -/
theorem lt_fastGrowing (o : ONote) {n : ℕ} (hn : 1 ≤ n) : n < fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [fastGrowing_zero' o e]
    exact Nat.lt_succ_self n
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    -- `n < f_a n = (f_a)^[1] n ≤ (f_a)^[n] n`
    have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    have hstep : fastGrowing a n ≤ (fastGrowing a)^[n] n := by
      have hmono := Function.monotone_iterate_of_id_le hexp hn
      simpa using hmono n
    exact lt_of_lt_of_le (lt_fastGrowing a hn) hstep
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    exact lt_fastGrowing (f n) hn
termination_by o
decreasing_by all_goals exact hlt

/-- **Index step at a successor** (a genuine A3 stepping stone, proved directly).
If `o` is the successor of `a` (`fundamentalSequence o = inl (some a)`), then for a
positive argument the next index can only grow the value:
`f_a(n) ≤ f_o(n)`. Indeed `f_o n = (f_a)^[n] n ≥ (f_a)^[1] n = f_a n` once `1 ≤ n`. -/
theorem fastGrowing_le_succ_index {o a : ONote}
    (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ} (hn : 1 ≤ n) :
    fastGrowing a n ≤ fastGrowing o n := by
  rw [fastGrowing_succ o h]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
  simpa using (Function.monotone_iterate_of_id_le hexp hn) n

/-- **Structural descent relation** `Reaches x β α`: from `β` one can step down to `α`
through `fundamentalSequence`, using *predecessor* steps at successor notations and
*index-`x`* steps at limit notations. This is a purely structural (no `fastGrowing`)
relation on `ONote`, and it is exactly the "Bachmann path" along which the fast-growing
hierarchy is monotone in the index. -/
inductive Reaches (x : ℕ) : ONote → ONote → Prop
  | refl (a : ONote) : Reaches x a a
  | succ {β γ α : ONote} (h : fundamentalSequence β = Sum.inl (some γ))
      (hr : Reaches x γ α) : Reaches x β α
  | limit {β α : ONote} {g : ℕ → ONote} (h : fundamentalSequence β = Sum.inr g)
      (hr : Reaches x (g x) α) : Reaches x β α

/-- `Reaches x` is transitive (paths compose). -/
theorem Reaches.trans {x : ℕ} {a b c : ONote} (h1 : Reaches x a b) (h2 : Reaches x b c) :
    Reaches x a c := by
  induction h1 with
  | refl a => exact h2
  | succ h _ ih => exact Reaches.succ h (ih h2)
  | limit h _ ih => exact Reaches.limit h (ih h2)

/-- **Value transfer (the analytic side, fully proved axiom-clean).** If `β` reaches `α`
structurally with positive budget `x`, then `f_α(x) ≤ f_β(x)`. Each step is justified:
a predecessor step by `fastGrowing_le_succ_index` (iterating an expansive map), a
limit-`x` step by `fastGrowing_limit` (definitional equality). This reduces *all* index
monotonicity of the fast-growing hierarchy to the structural `Reaches` relation. -/
theorem fastGrowing_le_of_reaches {x : ℕ} (hx : 1 ≤ x) {β α : ONote}
    (h : Reaches x β α) : fastGrowing α x ≤ fastGrowing β x := by
  induction h with
  | refl a => exact le_rfl
  | succ hb _ ih => exact le_trans ih (fastGrowing_le_succ_index hb hx)
  | limit hb _ ih => rw [fastGrowing_limit _ hb]; exact ih

/-- A structural reach only goes *down* the ordinal order: `Reaches x β α → α ≤ β`. -/
theorem reaches_le {x : ℕ} {β α : ONote} (h : Reaches x β α) : α ≤ β := by
  induction h with
  | refl a => exact le_rfl
  | @succ β γ α hb _ ih =>
      have hlt : γ < β := by
        have hp := fundamentalSequence_has_prop β; rw [hb] at hp
        rw [lt_def, hp.1]; exact Order.lt_succ _
      exact le_trans ih (le_of_lt hlt)
  | @limit β α g hb _ ih =>
      have hlt : g x < β := by
        have hp := fundamentalSequence_has_prop β; rw [hb] at hp
        exact (hp.2.1 x).2.1
      exact le_trans ih (le_of_lt hlt)

/-! ### Structural Bachmann reachability — the A3 crux, fully proved

The remaining difficulty in index monotonicity is now a pure statement about
`fundamentalSequence`: the descent of `o[n+1]` (budget `n+1`) passes exactly through
`o[n]`. We prove it by structural recursion on `o`, assembling four reusable facts:
`reaches_zero` (every notation descends to 0), `Reaches.oadd_tail` (descend a fixed
prefix's tail), `reaches_coeff_step'`/`reaches_coeff_chain` (drop a leading coefficient),
and `reaches_omega_pow_lift` (lift an exponent reach through `ω^·`). -/

/-- Lifting a successor tail step to `oadd a m ·`. -/
theorem fundamentalSequence_oadd_succ {a : ONote} {m : ℕ+} {b b' : ONote}
    (h : fundamentalSequence b = Sum.inl (some b')) :
    fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
  conv_lhs => rw [fundamentalSequence]; rw [h]

/-- Lifting a limit tail step to `oadd a m ·`. -/
theorem fundamentalSequence_oadd_limit {a : ONote} {m : ℕ+} {b : ONote} {h : ℕ → ONote}
    (hb : fundamentalSequence b = Sum.inr h) :
    fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (h i)) := by
  conv_lhs => rw [fundamentalSequence]; rw [hb]

/-- **Descend a fixed prefix's tail.** A structural reach on the tail lifts to the whole
`oadd a m ·`: every non-`refl` step's source has a non-`inl none` fundamental sequence, so
it lifts via `fundamentalSequence_oadd_succ`/`fundamentalSequence_oadd_limit`. -/
theorem Reaches.oadd_tail {x : ℕ} {a : ONote} {m : ℕ+} {δ' δ : ONote}
    (h : Reaches x δ' δ) : Reaches x (oadd a m δ') (oadd a m δ) := by
  induction h with
  | refl c => exact Reaches.refl _
  | succ hb _ ih => exact Reaches.succ (fundamentalSequence_oadd_succ hb) ih
  | limit hb _ ih => exact Reaches.limit (fundamentalSequence_oadd_limit hb) ih

/-- **Every notation descends to 0.** The fixed-budget descent terminates (well-founded
recursion on `o`, since `fundamentalSequence` always yields a strictly smaller notation),
and it can only terminate at `0`. -/
theorem reaches_zero (o : ONote) (x : ℕ) : Reaches x o 0 := by
  rcases e : fundamentalSequence o with (_ | a) | g
  · have ho : o = 0 := by have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact hp
    rw [ho]; exact Reaches.refl 0
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    exact Reaches.succ e (reaches_zero a x)
  · have hlt : g x < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 x).2.1
    exact Reaches.limit e (reaches_zero (g x) x)
termination_by o
decreasing_by all_goals exact hlt

/-- **Coefficient step** (any budget): `ω^e·(j+2)` descends exactly to `ω^e·(j+1)`. The
descent strips one coefficient, leaving a tail that runs to `0` via `reaches_zero`. Holds
for every exponent `e` (zero ⇒ a finite successor step; successor/limit ⇒ a limit step
plus a tail descent). -/
theorem reaches_coeff_step' (e : ONote) (j x : ℕ) :
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
theorem reaches_coeff_chain (e : ONote) (j x : ℕ) :
    Reaches x (oadd e j.succPNat 0) (oadd e (0 : ℕ).succPNat 0) := by
  induction j with
  | zero => exact Reaches.refl _
  | succ j ih => exact (reaches_coeff_step' e j x).trans ih

/-- Fundamental sequence of `ω^{successor exponent}`. -/
theorem fundamentalSequence_omega_pow_succ {γ' δ : ONote}
    (he : fundamentalSequence γ' = Sum.inl (some δ)) :
    fundamentalSequence (oadd γ' 1 0) = Sum.inr (fun i => oadd δ i.succPNat 0) := by
  conv_lhs => rw [fundamentalSequence]
  rw [he]; rfl

/-- Fundamental sequence of `ω^{limit exponent}`. -/
theorem fundamentalSequence_omega_pow_limit {γ' : ONote} {q : ℕ → ONote}
    (he : fundamentalSequence γ' = Sum.inr q) :
    fundamentalSequence (oadd γ' 1 0) = Sum.inr (fun i => oadd (q i) 1 0) := by
  conv_lhs => rw [fundamentalSequence]
  rw [he]; rfl

/-- **Exponent lifting.** A structural reach on exponents lifts through `ω^·`. Limit
exponent steps lift directly (`ω^λ[i] = (ω^λ)[i]`); a successor exponent step `δ+1 → δ`
expands into a coefficient chain `ω^δ·(x+1) → ω^δ`. This is the one place the difficulty
of limits-of-limits is actually discharged. -/
theorem reaches_omega_pow_lift {x : ℕ} {γ' γ : ONote}
    (h : Reaches x γ' γ) : Reaches x (oadd γ' 1 0) (oadd γ 1 0) := by
  induction h with
  | refl c => exact Reaches.refl _
  | @succ β δ α hb _ ih =>
      refine Reaches.limit (fundamentalSequence_omega_pow_succ hb) ?_
      exact (reaches_coeff_chain δ x x).trans ih
  | @limit β α g hb _ ih =>
      exact Reaches.limit (fundamentalSequence_omega_pow_limit hb) ih

/-- The fundamental sequence of a successor *natural-number* notation is its
predecessor: `(k+1)[·] = k`. (Both branches reduce to `rfl`.) -/
theorem fundamentalSequence_ofNat_succ (k : ℕ) :
    fundamentalSequence (ofNat (k + 1)) = Sum.inl (some (ofNat k)) := by
  cases k with
  | zero => rfl
  | succ k' => rfl

/-- **Telescoping index monotonicity along a successor chain** — the general engine.
If `g : ℕ → ONote` is a *successor chain* (`g (k+1) = g k + 1` notation-wise, i.e.
`fundamentalSequence (g (k+1)) = inl (some (g k))`), then for `m ≤ n` and positive
argument, `f_{g m}(x) ≤ f_{g n}(x)`: just telescope `fastGrowing_le_succ_index`.

This is the reusable core behind every "successor-chain" index comparison —
finite levels (`g = ofNat`), `β+ω` limits, and the *finite slices* `β, β+1, β+2, …`
of a limit's own fundamental sequence (which is how the limit-of-limits residue is
attacked: each `o[n+1]` is reached from `o[n]` by finitely many successor steps). -/
theorem fastGrowing_succ_chain_mono {g : ℕ → ONote}
    (hchain : ∀ k, fundamentalSequence (g (k + 1)) = Sum.inl (some (g k)))
    {m n : ℕ} (hmn : m ≤ n) {x : ℕ} (hx : 1 ≤ x) :
    fastGrowing (g m) x ≤ fastGrowing (g n) x := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (fastGrowing_le_succ_index (hchain n) hx)

/-- **Finite-level index monotonicity** (the base case): `m ≤ n`, `1 ≤ x ⟹ f_m(x) ≤
f_n(x)`. The `ofNat` instance of `fastGrowing_succ_chain_mono`. -/
theorem fastGrowing_ofNat_mono {m n : ℕ} (hmn : m ≤ n) {x : ℕ} (hx : 1 ≤ x) :
    fastGrowing (ofNat m) x ≤ fastGrowing (ofNat n) x :=
  fastGrowing_succ_chain_mono fundamentalSequence_ofNat_succ hmn hx

/-- **Finite-level argument monotonicity**, proved *cleanly* (no limit crux needed,
since finite levels never enter the limit branch). `Monotone (f_k)` for `k : ℕ`, by
induction on `k`: the successor step is `(f_{k})^[a] a ≤ (f_k)^[b] b` for `a ≤ b`,
from the IH (`f_k` monotone) and `le_fastGrowing` (`id ≤ f_k`). -/
theorem fastGrowing_ofNat_monotone (k : ℕ) : Monotone (fastGrowing (ofNat k)) := by
  induction k with
  | zero =>
      simp only [ofNat_zero, fastGrowing_zero]
      exact fun a b h => Nat.succ_le_succ h
  | succ k ih =>
      rw [fastGrowing_succ _ (fundamentalSequence_ofNat_succ k)]
      have hexp : (id : ℕ → ℕ) ≤ fastGrowing (ofNat k) := fun m => le_fastGrowing _ m
      intro a b hab
      calc (fastGrowing (ofNat k))^[a] a
          ≤ (fastGrowing (ofNat k))^[a] b := ih.iterate a hab
        _ ≤ (fastGrowing (ofNat k))^[b] b := (Function.monotone_iterate_of_id_le hexp hab) b

/-- **Monotonicity of `f_ω`, fully proved (axiom-clean).** The first nontrivial limit
level is monotone — discharging the limit case *without* the general crux, using only
finite-level facts (`ω[n] = n+1`, both finite). This is the concrete witness that the
reduction machinery is sound on a genuine limit ordinal.

`f_ω(n) = f_{ofNat(n+1)}(n) ≤ f_{ofNat(n+1)}(n+1) ≤ f_{ofNat(n+2)}(n+1) = f_ω(n+1)`. -/
theorem fastGrowing_monotone_omega : Monotone (fastGrowing (oadd 1 1 0)) := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [fastGrowing_limit _ hfs]
  -- goal: f_{ofNat(n+1)}(n) ≤ f_{ofNat(n+2)}(n+1)
  calc fastGrowing (ofNat (n + 1)) n
      ≤ fastGrowing (ofNat (n + 1)) (n + 1) := fastGrowing_ofNat_monotone (n + 1) (Nat.le_succ n)
    _ ≤ fastGrowing (ofNat (n + 2)) (n + 1) :=
        fastGrowing_ofNat_mono (Nat.le_succ (n + 1)) (Nat.succ_le_succ (Nat.zero_le n))

/-- **The Bachmann reachability crux (A3, structural form) — PROVEN, axiom-clean**
(`[propext, choice, Quot.sound]`; body below is a complete structural recursion on `o`, no `sorry`).

For a limit notation `o` with fundamental sequence `f`, the *next* index `f (n+1)`
structurally reaches the *current* index `f n` with budget `n+1`:
`Reaches (n+1) (f (n+1)) (f n)`.

This is the **Bachmann property** of the standard CNF fundamental sequences: the descent
of `f (n+1)` (at the fixed index `n+1`) passes *exactly* through `f n` — because the
`ONote` fundamental sequence descends tails first and the coefficients pass through every
integer value, so no tail "overshoots". From it, *all* index monotonicity of the
fast-growing hierarchy follows via `fastGrowing_le_of_reaches` (see `fastGrowing_fundSeq_step`).

The proof is a structural recursion on `o` (leading-term cases via `reaches_coeff_step'`;
`ω^{limit}` residue via `reaches_omega_pow_lift`; limit-tail via `Reaches.oadd_tail`). This
replaced the old analytic `sorry`; the successor-chain and `ω^2` cases are the specialisations
`fastGrowing_fundSeq_step_of_succ` / `fastGrowing_omega_sq_…`. -/
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

/-- **The index-monotonicity crux (A3), limit step** — now a corollary of the structural
Bachmann reachability via the value-transfer lemma. For a limit `o` with fundamental
sequence `f`, `f_{o[n]}(n+1) ≤ f_{o[n+1]}(n+1)`. -/
theorem fastGrowing_fundSeq_step {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    fastGrowing (f n) (n + 1) ≤ fastGrowing (f (n + 1)) (n + 1) :=
  fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n)) (fastGrowing_bachmann_reach h n)

/-- **The crux for "successor-chain" limits** — proved in full (axiom-clean).
Whenever the fundamental sequence of `o` is a *successor chain*, i.e. each `f (n+1)`
is the notation-successor of `f n` (`fundamentalSequence (f (n+1)) = inl (some (f n))`),
the index step is just `fastGrowing_le_succ_index`. This covers every limit of the form
`β + ω` (e.g. `ω, ω·k, ω+k`), whose fundamental sequence increments a finite tail.

Consequently the remaining genuine difficulty in `fastGrowing_fundSeq_step` lives
*only* at limits-of-limits (`ω^ω`, `ω^(ω+1)`, …), where `f n` is itself a limit and the
chain is not successor-stepwise — that is the sharp residue of the A3 crux. -/
theorem fastGrowing_fundSeq_step_of_succ {o : ONote} {f : ℕ → ONote}
    (_h : fundamentalSequence o = Sum.inr f)
    (hsucc : ∀ k, fundamentalSequence (f (k + 1)) = Sum.inl (some (f k))) (n : ℕ) :
    fastGrowing (f n) (n + 1) ≤ fastGrowing (f (n + 1)) (n + 1) :=
  fastGrowing_le_succ_index (hsucc n) (Nat.succ_le_succ (Nat.zero_le n))

/-- **Monotonicity propagates across a successor step.** If `o` is the notation-successor
of `a` (`fundamentalSequence o = inl (some a)`) and `f_a` is monotone, then so is `f_o`:
`f_o n = (f_a)^[n] n`, and iterating a monotone, `≥ id` map preserves monotonicity in the
diagonal `n ↦ (f_a)^[n] n`. (The successor companion of `fastGrowing_le_succ_index`, at the
level of the whole `Monotone` predicate.) -/
theorem fastGrowing_monotone_succ {o a : ONote}
    (h : fundamentalSequence o = Sum.inl (some a)) (ha : Monotone (fastGrowing a)) :
    Monotone (fastGrowing o) := by
  rw [fastGrowing_succ o h]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
  intro p q hpq
  calc (fastGrowing a)^[p] p
      ≤ (fastGrowing a)^[p] q := ha.iterate p hpq
    _ ≤ (fastGrowing a)^[q] q := (Function.monotone_iterate_of_id_le hexp hpq) q

/-- **Monotonicity for successor-chain limits — the general engine, axiom-clean.**
If `o` is a limit whose fundamental sequence `f` is a *successor chain*
(`fundamentalSequence (f (k+1)) = inl (some (f k))`), then `f_o` is monotone *provided
only the bottom level `f 0` is monotone*: monotonicity of every `f k` then follows from
`fastGrowing_monotone_succ` along the chain, and the limit step is discharged by
`fastGrowing_fundSeq_step_of_succ`.

This is the clean companion to `fastGrowing_fundSeq_step_of_succ`: it lifts the *index
step* to the whole `Monotone` predicate, and covers every `β + ω`-type limit (`ω`, `ω·k`,
`β+ω`) in one stroke. The genuinely hard residue (`ω^ω`, `ω^(ω+1)`, …) — where the
fundamental sequence is not a successor chain — remains in `fastGrowing_fundSeq_step`. -/
theorem fastGrowing_monotone_of_succ_chain_limit {o : ONote} {f : ℕ → ONote}
    (hlim : fundamentalSequence o = Sum.inr f)
    (hchain : ∀ k, fundamentalSequence (f (k + 1)) = Sum.inl (some (f k)))
    (hmono0 : Monotone (fastGrowing (f 0))) :
    Monotone (fastGrowing o) := by
  have hmono : ∀ k, Monotone (fastGrowing (f k)) := by
    intro k
    induction k with
    | zero => exact hmono0
    | succ k ih => exact fastGrowing_monotone_succ (hchain k) ih
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [fastGrowing_limit o hlim]
  calc fastGrowing (f n) n
      ≤ fastGrowing (f n) (n + 1) := hmono n (Nat.le_succ n)
    _ ≤ fastGrowing (f (n + 1)) (n + 1) := fastGrowing_fundSeq_step_of_succ hlim hchain n

/-- **`f_ω` is monotone, re-derived cleanly from the general engine.** `ω`'s fundamental
sequence is the successor chain `n ↦ ofNat (n+1)`, whose bottom level `f_{ofNat 1}` is
monotone (`fastGrowing_ofNat_monotone`). Compare `fastGrowing_monotone_omega`, which proved
the same fact by hand; this routes through `fastGrowing_monotone_of_succ_chain_limit`. -/
theorem fastGrowing_monotone_omega' : Monotone (fastGrowing (oadd 1 1 0)) := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  exact fastGrowing_monotone_of_succ_chain_limit hfs
    (fun k => fundamentalSequence_ofNat_succ (k + 1)) (fastGrowing_ofNat_monotone 1)

/-- **`f_{ω·(j+1)}` is monotone, for every `j` — the whole `ω·k` family.** Each `ω·(j+1)`
(`= oadd 1 j.succPNat 0`) is a successor-chain limit whose bottom level is `ω·j + 1`, a
notation-successor of `ω·j`; so monotonicity propagates up the `ω·k` ladder by induction
on `k`, with `ω·1 = ω` (`fastGrowing_monotone_omega'`) as the base. This is the first
*infinite family* of limit levels proved monotone — still all `β+ω`-type, but it exercises
the successor-chain engine on genuinely varying notations and is the lemma the `ω^2`
index step consumes. -/
theorem fastGrowing_monotone_omega_mul (j : ℕ) :
    Monotone (fastGrowing (oadd 1 j.succPNat 0)) := by
  induction j with
  | zero => exact fastGrowing_monotone_omega'
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
theorem fundamentalSequence_oadd_ofNat_succ (a : ONote) (m : ℕ+) (t : ℕ) :
    fundamentalSequence (oadd a m (ofNat (t + 1))) = Sum.inl (some (oadd a m (ofNat t))) := by
  cases t <;> rfl

/-- **The `ω^2` index step — the first genuine A3 instance outside the successor-chain
class, proved axiom-clean.** `ω^2`'s fundamental sequence `i ↦ ω·(i+1)` is *not* a
successor chain (consecutive `ω·(i+1)`, `ω·(i+2)` are both limits). The classical trick:
`ω·(n+2)` descends *at index `n+1`* to `ω·(n+1) + (n+2)`, which **is** reachable from
`ω·(n+1)` by a finite successor chain of length `n+2`. So the index step collapses to
`fastGrowing_succ_chain_mono` after one limit unfolding — the concrete realization of the
Bachmann "descent connects the two indices" property. -/
theorem fastGrowing_omega_sq_index_step (n : ℕ) :
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

/-- **`f_{ω^2}` is monotone, axiom-clean.** The first limit level *outside* the
`β+ω` (successor-chain) class proved monotone — a real step into the hard A3 regime.
The limit step `f_{ω·(n+1)}(n) ≤ f_{ω·(n+2)}(n+1)` is `fastGrowing_monotone_omega_mul`
(argument monotonicity at the fixed index `ω·(n+1)`) followed by
`fastGrowing_omega_sq_index_step` (the genuine index increment). -/
theorem fastGrowing_monotone_omega_sq : Monotone (fastGrowing (oadd (ofNat 2) 1 0)) := by
  have hlim : fundamentalSequence (oadd (ofNat 2) 1 0)
      = Sum.inr (fun i => oadd 1 i.succPNat 0) := rfl
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [fastGrowing_limit _ hlim]
  calc fastGrowing (oadd 1 n.succPNat 0) n
      ≤ fastGrowing (oadd 1 n.succPNat 0) (n + 1) :=
        fastGrowing_monotone_omega_mul n (Nat.le_succ n)
    _ ≤ fastGrowing (oadd 1 (n + 1).succPNat 0) (n + 1) := fastGrowing_omega_sq_index_step n

/-- **Monotonicity in the argument, successor form** `f_o(n) ≤ f_o(n+1)`.
Well-founded recursion on `o`; the limit case is reduced to the single crux
`fastGrowing_fundSeq_step`, everything else is `le_fastGrowing` + iterate monotonicity. -/
theorem fastGrowing_le_succ (o : ONote) (n : ℕ) :
    fastGrowing o n ≤ fastGrowing o (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | g
  · rw [fastGrowing_zero' o e]
    exact Nat.le_succ _
  · -- successor: `(f_a)^[n] n ≤ (f_a)^[n+1] (n+1)`
    have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [fastGrowing_succ o e]
    have hmono_a : Monotone (fastGrowing a) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ a k
    calc (fastGrowing a)^[n] n
        ≤ (fastGrowing a)^[n] (n + 1) := hmono_a.iterate n (Nat.le_succ n)
      _ ≤ (fastGrowing a)^[n + 1] (n + 1) := by
            rw [Function.iterate_succ_apply']
            exact le_fastGrowing a _
  · -- limit: `f_{g n}(n) ≤ f_{g (n+1)}(n+1)`
    have hlt : g n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [fastGrowing_limit o e]
    have hmono_gn : Monotone (fastGrowing (g n)) :=
      monotone_nat_of_le_succ fun k => fastGrowing_le_succ (g n) k
    calc fastGrowing (g n) n
        ≤ fastGrowing (g n) (n + 1) := hmono_gn (Nat.le_succ n)
      _ ≤ fastGrowing (g (n + 1)) (n + 1) := fastGrowing_fundSeq_step e n
termination_by o
decreasing_by all_goals exact hlt

/-- **Monotonicity in the argument.** Each level `f_o` is a monotone function of `n`.
Immediate from `fastGrowing_le_succ` via `monotone_nat_of_le_succ`. -/
theorem fastGrowing_monotone (o : ONote) : Monotone (fastGrowing o) :=
  monotone_nat_of_le_succ (fastGrowing_le_succ o)


/-
# A4 — `fastGrowingε₀` dominates every fixed level (the headline domination crux)

The unboundedness that *is* the Goodstein/Kirby–Paris independence content:

> For every notation `o < ε₀`, eventually `fastGrowing o n < fastGrowingε₀ n`.

`fastGrowingε₀` is `mathlib`'s one-step extension of the fast-growing hierarchy to `ε₀`,
built on the *diagonal tower* fundamental sequence `0, 1, ω, ω^ω, ω^ω^ω, …` converging to
`ε₀`:

* `fastGrowingε₀ i = fastGrowing (tower i) i`, where `tower i = (fun a => ω^a)^[i] 0`.

This file pins the tower structure and **proves A4 in full, axiom-clean**. With
A1 (`le_fastGrowing`), A2 (`fastGrowing_monotone`) and A3 (`fastGrowing_bachmann_reach`)
proved in `Basic.lean`, the remaining content of A4 was an **index domination** fact: each
fixed `o` is eventually outgrown because the tower indices climb past it.

## Architecture (all proved, no `sorry`)
1. **Tower structure**: `tower (i+1) = ω^{tower i}`, `fastGrowingε₀` unfolds to
   `fastGrowing (tower i) i`; cofinality `tower_cofinal`.
2. **The CNF norm** `norm` + the **key cofinality bound**
   `lt_fundamentalSequence_of_norm_le` (THE new theorem): for a limit `β` and `α < β` with
   `norm α ≤ x`, already `α < g_β(x)`. Proved by structural induction over all six
   `fundamentalSequence` branches.
3. **General reachability** `reaches_of_lt`: `α < β ∧ norm α ≤ x ⟹ Reaches x β α`, by WF
   recursion on `β` reusing (2) at limits.
4. **Strictness** via the notation successor `osucc`: reach `osucc o` and take one strict
   successor index step (`fastGrowing_lt_succ_index`, needs `2 ≤ n`).

Headline: `fastGrowing_lt_fastGrowingε₀` — every fixed `f_o` is eventually strictly
dominated by `f_{ε₀}`. This is the unboundedness that *is* the Kirby–Paris growth gap.
-/

end GoodsteinPA.FastGrowing
