/-
# Hardy & fast-growing hierarchy — PORTED from ~/src/lean-formalizations (Track 1)
Verbatim merge of FastGrowing/{Basic,Domination,Hardy}.lean (mathlib rev fabf563a7c95,
identical to this repo's pin). Provides `hardy`, `norm`, `hardy_le_of_lt` (= Hmono),
`hardy_monotone` (= Hmono_n), `fastGrowing_*`. WIP — not in build target. Namespace localized.
-/
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Order.Iterate

namespace GoodsteinPA.FastGrowing

open ONote Ordinal


-- ════════════════ ported: Basic.lean ════════════════
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


-- ════════════════ ported: Domination.lean ════════════════
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



/-- **No `ω`-fixed points below `ε₀`, elementarily.** For every normal-form notation,
`repr o < ω ^ repr o`. Proved by *structural induction* on `o` — the inductive hypothesis
at the leading exponent `e` gives `repr e < ω ^ repr e ≤ repr o`, hence `repr e < repr o`,
so `repr o < ω ^ (repr e + 1) ≤ ω ^ repr o` (`NFBelow.repr_lt` + monotonicity). No `ε₀`
fixed-point machinery needed. The key strictness fact underlying the tower's growth. -/
theorem repr_lt_opow_repr : ∀ (o : ONote), o.NF → o.repr < ω ^ o.repr
  | 0, _ => by simp
  | oadd e n a, h => by
      have hIH : e.repr < ω ^ e.repr := repr_lt_opow_repr e h.fst
      have hle : ω ^ e.repr ≤ (oadd e n a).repr := omega0_le_oadd e n a
      have helt : e.repr < (oadd e n a).repr := lt_of_lt_of_le hIH hle
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (oadd e n a).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt helt)
      exact lt_of_lt_of_le h1 h2

/-! ### The CNF norm and structural comparison helpers (toward general Bachmann reachability)

The general index-domination needs a **budget condition**: the diagonal argument `x` must be
large enough that the fundamental-sequence descent of `β` actually passes through `α`. The
right "size of `α`" is its **CNF norm**: the largest finite number (coefficient or finite
tail) appearing anywhere in `α`'s Cantor normal form. -/

/-- **CNF norm** of a notation: the maximum finite coefficient appearing anywhere in its
Cantor normal form (recursively through exponents and tails). `norm 0 = 0`,
`norm (ω^e·n + a) = max (norm e) (max n (norm a))`. This is the budget threshold: if
`norm α ≤ x` then the standard fundamental-sequence descent of any `β > α` reaches `α` with
budget `x` (`reaches_of_lt`). -/
def norm : ONote → ℕ
  | 0 => 0
  | oadd e n a => max (norm e) (max (n : ℕ) (norm a))

@[simp] theorem norm_zero : norm 0 = 0 := rfl

@[simp] theorem norm_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    norm (oadd e n a) = max (norm e) (max (n : ℕ) (norm a)) := rfl

/-- **Trichotomy decomposition of `<` on `oadd`.** For normal-form notations, `α < β`
splits into the three lexicographic cases on (exponent, coefficient, tail). -/
theorem lt_oadd_cases {ea : ONote} {na : ℕ+} {ba e : ONote} {m : ℕ+} {b : ONote}
    (hα : NF (oadd ea na ba)) (hβ : NF (oadd e m b)) (h : oadd ea na ba < oadd e m b) :
    ea < e ∨ (ea = e ∧ (na : ℕ) < (m : ℕ)) ∨ (ea = e ∧ na = m ∧ ba < b) := by
  rcases lt_trichotomy ea.repr e.repr with he | he | he
  · exact Or.inl (lt_def.2 he)
  · have heq : ea = e := (@repr_inj ea e hα.fst hβ.fst).1 he
    subst heq
    rcases lt_trichotomy (na : ℕ) (m : ℕ) with hn | hn | hn
    · exact Or.inr (Or.inl ⟨rfl, hn⟩)
    · have hnm : na = m := PNat.coe_injective hn
      subst hnm
      rcases lt_trichotomy ba.repr b.repr with hb | hb | hb
      · exact Or.inr (Or.inr ⟨rfl, rfl, lt_def.2 hb⟩)
      · have hbeq : ba = b := (@repr_inj ba b hα.snd hβ.snd).1 hb
        subst hbeq; exact absurd h (lt_irrefl _)
      · exact absurd (oadd_lt_oadd_3 (lt_def.2 hb)) (lt_asymm h)
    · exact absurd (oadd_lt_oadd_2 hβ hn) (lt_asymm h)
  · exact absurd (oadd_lt_oadd_1 hβ (lt_def.2 he)) (lt_asymm h)

/-- **The norm bound on a single CNF level.** If a normal-form `δ` has leading exponent
`≤ c` (i.e. `repr δ < ω^(repr c)·ω`) and norm `≤ x`, then `δ < ω^(repr c)·(x+1) =
oadd c (x+1) 0`. The workhorse for the limit cases of the key lemma: a small-norm notation
can't reach past the `(x+1)`-th rung `ω^c·(x+1)` of the relevant fundamental sequence. -/
theorem lt_oadd_of_lead_le {x : ℕ} {c : ONote} (hc : c.NF) {δ : ONote} (hδ : δ.NF)
    (hlead : δ.repr < ω ^ c.repr * ω) (hnorm : norm δ ≤ x) :
    δ < oadd c x.succPNat 0 := by
  cases δ with
  | zero => exact oadd_pos _ _ _
  | oadd ed nd bd =>
    have hpow : ω ^ ed.repr ≤ (oadd ed nd bd).repr := omega0_le_oadd ed nd bd
    have h2 : (ω : Ordinal) ^ ed.repr < ω ^ c.repr * ω := lt_of_le_of_lt hpow hlead
    rw [← opow_succ] at h2
    have hed_le : ed.repr ≤ c.repr :=
      Order.lt_succ_iff.1 ((opow_lt_opow_iff_right one_lt_omega0).1 h2)
    rcases lt_or_eq_of_le hed_le with hlt | heq
    · exact oadd_lt_oadd_1 hδ (lt_def.2 hlt)
    · have hedc : ed = c := (@repr_inj ed c hδ.fst hc).1 heq
      subst hedc
      rw [norm_oadd] at hnorm
      have hnd : (nd : ℕ) ≤ x := (le_max_of_le_right (le_max_left _ _)).trans hnorm
      refine oadd_lt_oadd_2 hδ ?_
      simpa [Nat.succPNat] using Nat.lt_succ_of_le hnd

/-- **The key cofinality bound (general Bachmann reachability core).** For a normal-form
*limit* `β` with standard fundamental sequence `g`, every `α < β` whose CNF norm is `≤ x`
already sits below the `x`-th rung `g x`. Equivalently: the budget `x ≥ norm α` is enough
for the descent of `β` to "catch" `α`.

Proved by structural induction on `β`, following the six branches of
`ONote.fundamentalSequence` exactly. The successor-producing branches contradict the limit
hypothesis. The five limit-producing branches each reduce, after decomposing `α`'s leading
CNF term (`lt_oadd_cases`), to either the inductive hypothesis on the exponent/tail or the
single-level norm bound `lt_oadd_of_lead_le`. This is the one genuinely new theorem of the
A4 development; once it holds, all of general reachability and index domination follow. -/
theorem lt_fundamentalSequence_of_norm_le {x : ℕ} :
    ∀ (β : ONote), β.NF → ∀ (g : ℕ → ONote), fundamentalSequence β = Sum.inr g →
      ∀ (α : ONote), α.NF → α < β → norm α ≤ x → α < g x := by
  intro β
  induction β with
  | zero => intro _ g hg _ _ _ _; exact (Sum.inl_ne_inr hg).elim
  | oadd a m b iha ihb =>
    intro hβ g hg α hα hαβ hnorm
    rcases hb : fundamentalSequence b with (_ | b') | hbf
    · -- b = 0 : leading-term cases
      rcases ha : fundamentalSequence a with (_ | a') | p
      · -- a = 0 : `oadd 0 m 0` is a successor → contradicts the limit `hg`
        rcases hm : m.natPred with _ | k
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
        · rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inl_ne_inr hg).elim
      · -- a a successor (predecessor `a'`)
        have hpa := fundamentalSequence_has_prop a; rw [ha] at hpa
        have ha'NF : a'.NF := hpa.2 hβ.fst
        have harepr : a.repr = Order.succ a'.repr := hpa.1
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L2 : `g = fun i => ω^a'·(i+1)`, `m = 1`
          have hg' : g = fun i => oadd a' i.succPNat 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          refine lt_oadd_of_lead_le ha'NF hα ?_ hnorm
          have hlt : α.repr < (oadd a m b).repr := lt_def.1 hαβ
          rw [hb0, hm1] at hlt
          rw [show (oadd a 1 0).repr = ω ^ a.repr from by
            simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]] at hlt
          rw [harepr, opow_succ] at hlt
          exact hlt
        · -- L3 : `g = fun i => ω^a·(k+1) + ω^a'·(i+1)`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd a' i.succPNat 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases α with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hαβ
            rcases lt_oadd_cases hα (hb0 ▸ hβ) hαβ with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hα hlt
            · rw [heq] at hα hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hα (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat := PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                refine lt_oadd_of_lead_le ha'NF hα.snd ?_ ?_
                · have hba : ba.repr < ω ^ a.repr := hα.snd'.repr_lt
                  rw [harepr, opow_succ] at hba; exact hba
                · rw [norm_oadd] at hnorm
                  exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
      · -- a a limit (fundamental sequence `p`)
        have hb0 : b = 0 := by have hpb := fundamentalSequence_has_prop b; rwa [hb] at hpb
        rcases hm : m.natPred with _ | k
        · -- L4 : `g = fun i => ω^(a[i])`, `m = 1`
          have hg' : g = fun i => oadd (p i) 1 0 := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hm1 : m = 1 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases α with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0, hm1] at hαβ
            rcases lt_oadd_cases hα ((hb0 ▸ hm1 ▸ hβ : NF (oadd a 1 0))) hαβ
              with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, _, hbalt⟩
            · have hnorm_ea : norm ea ≤ x := by
                rw [norm_oadd] at hnorm; exact (le_max_left _ _).trans hnorm
              have hep : ea < p x := iha hβ.fst p ha ea hα.fst hlt hnorm_ea
              exact oadd_lt_oadd_1 hα hep
            · simp only [PNat.one_coe] at hnlt; exact absurd hnlt (by have := na.pos; omega)
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
        · -- L5 : `g = fun i => ω^a·(k+1) + ω^(a[i])`, `m = k+2`
          have hg' : g = fun i => oadd a k.succPNat (oadd (p i) 1 0) := by
            rw [fundamentalSequence, hb, ha, hm] at hg; exact (Sum.inr.inj hg).symm
          have hmval : (m : ℕ) = k + 2 := by rw [← PNat.succPNat_natPred m, hm]; rfl
          rw [hg']
          cases α with
          | zero => exact oadd_pos _ _ _
          | oadd ea na ba =>
            rw [hb0] at hαβ
            rcases lt_oadd_cases hα (hb0 ▸ hβ) hαβ with hlt | ⟨heq, hnlt⟩ | ⟨_, _, hbalt⟩
            · exact oadd_lt_oadd_1 hα hlt
            · rw [heq] at hα hnorm ⊢
              rw [hmval] at hnlt
              rcases Nat.lt_or_ge (na : ℕ) (k + 1) with hna | hna
              · exact oadd_lt_oadd_2 hα (by simpa [Nat.succPNat] using hna)
              · have hnak : (na : ℕ) = k + 1 := le_antisymm (by omega) hna
                have hnaP : na = k.succPNat := PNat.coe_injective (by simpa [Nat.succPNat] using hnak)
                subst hnaP
                refine oadd_lt_oadd_3 ?_
                cases ba with
                | zero => exact oadd_pos _ _ _
                | oadd eb nb bb =>
                  have heb : eb.repr < a.repr := by
                    have hbb : (oadd eb nb bb).repr < ω ^ a.repr := hα.snd'.repr_lt
                    have hle : ω ^ eb.repr ≤ (oadd eb nb bb).repr := omega0_le_oadd eb nb bb
                    exact (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hle hbb)
                  have hnorm_eb : norm eb ≤ x := by
                    rw [norm_oadd, norm_oadd] at hnorm
                    exact (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hnorm
                  have hep : eb < p x := iha hβ.fst p ha eb hα.snd.fst (lt_def.2 heb) hnorm_eb
                  exact oadd_lt_oadd_1 hα.snd hep
            · have hr := lt_def.1 hbalt; rw [repr_zero] at hr
              exact absurd hr not_lt_zero
    · -- b a successor ⟹ `oadd a m b` is a successor → contradicts the limit `hg`
      rw [fundamentalSequence_oadd_succ hb] at hg; exact (Sum.inl_ne_inr hg).elim
    · -- L1 : b a limit, `g = fun i => oadd a m (b[i])` ; descend the tail
      have hg' : g = fun i => oadd a m (hbf i) := by
        rw [fundamentalSequence_oadd_limit hb] at hg; exact (Sum.inr.inj hg).symm
      rw [hg']
      cases α with
      | zero => exact oadd_pos _ _ _
      | oadd ea na ba =>
        rcases lt_oadd_cases hα hβ hαβ with hlt | ⟨rfl, hnlt⟩ | ⟨rfl, hnm, hbalt⟩
        · exact oadd_lt_oadd_1 hα hlt
        · exact oadd_lt_oadd_2 hα hnlt
        · subst hnm
          have hnorm_ba : norm ba ≤ x := by
            rw [norm_oadd] at hnorm; exact (le_max_of_le_right (le_max_right _ _)).trans hnorm
          exact oadd_lt_oadd_3 (ihb hβ.snd hbf hb ba hα.snd hbalt hnorm_ba)

/-- **General Bachmann reachability.** For normal-form `α < β`, once the budget `x` is at
least `norm α`, the standard fundamental-sequence descent of `β` reaches `α`:
`Reaches x β α`. Well-founded recursion on `β`: at a successor we step to the predecessor
and recurse (or stop); at a limit the key cofinality bound `lt_fundamentalSequence_of_norm_le`
guarantees `α < g x`, so we step to `g x` and recurse with the same budget. This is the
general engine `fastGrowing_bachmann_reach` only handled for consecutive indices. -/
theorem reaches_of_lt {x : ℕ} :
    ∀ (β : ONote), β.NF → ∀ (α : ONote), α.NF → α < β → norm α ≤ x → Reaches x β α := by
  intro β hβ α hα hαβ hnorm
  rcases e : fundamentalSequence β with (_ | γ) | g
  · exfalso
    have hβ0 : β = 0 := by have hp := fundamentalSequence_has_prop β; rwa [e] at hp
    rw [hβ0] at hαβ
    have hr : α.repr < 0 := by rw [← repr_zero]; exact lt_def.1 hαβ
    exact absurd hr not_lt_zero
  · have hp := fundamentalSequence_has_prop β; rw [e] at hp
    have hγNF : γ.NF := hp.2 hβ
    have hγβ : γ < β := lt_def.2 (by rw [hp.1]; exact Order.lt_succ _)
    have hαr : α.repr ≤ γ.repr := Order.lt_succ_iff.1 (by rw [← hp.1]; exact lt_def.1 hαβ)
    rcases eq_or_lt_of_le hαr with heq | hlt
    · have hαγ : α = γ := (@repr_inj α γ hα hγNF).1 heq
      subst hαγ; exact Reaches.succ e (Reaches.refl _)
    · exact Reaches.succ e (reaches_of_lt γ hγNF α hα (lt_def.2 hlt) hnorm)
  · have hp := fundamentalSequence_has_prop β; rw [e] at hp
    have hgxNF : (g x).NF := (hp.2.1 x).2.2 hβ
    have hgxlt : g x < β := (hp.2.1 x).2.1
    have hαgx : α < g x := lt_fundamentalSequence_of_norm_le β hβ g e α hα hαβ hnorm
    exact Reaches.limit e (reaches_of_lt (g x) hgxNF α hα hαgx hnorm)
termination_by β => β
decreasing_by all_goals assumption

/-- **Strict successor index step.** At a notation-successor `o` (predecessor `a`), the
value strictly increases for arguments `≥ 2`: `f_a(n) < f_o(n)`. Indeed
`f_o n = (f_a)^[n] n ≥ (f_a)^[2] n = f_a (f_a n) > f_a n`, the last step by strict
expansiveness (`lt_fastGrowing`) since `f_a n ≥ n ≥ 1`. (The `≤`-version is
`fastGrowing_le_succ_index`; strictness needs `2 ≤ n` to fit two iterations in.) -/
theorem fastGrowing_lt_succ_index {o a : ONote}
    (h : fundamentalSequence o = Sum.inl (some a)) {n : ℕ} (hn : 2 ≤ n) :
    fastGrowing a n < fastGrowing o n := by
  rw [fastGrowing_succ o h]
  have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
  have h1n : 1 ≤ n := le_trans one_le_two hn
  have hge : n ≤ fastGrowing a n := le_fastGrowing a n
  have hlt2 : fastGrowing a n < fastGrowing a (fastGrowing a n) :=
    lt_fastGrowing a (le_trans h1n hge)
  have hstep2 : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
    Function.monotone_iterate_of_id_le hexp hn n
  have h2eq : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  calc fastGrowing a n < fastGrowing a (fastGrowing a n) := hlt2
    _ = (fastGrowing a)^[2] n := h2eq.symm
    _ ≤ (fastGrowing a)^[n] n := hstep2

/-- **General index monotonicity of the fast-growing hierarchy** (the full A3, lifted off
the consecutive-index restriction of `fastGrowing_bachmann_reach`). For normal-form `α < β`
and budget `x ≥ norm α` (with `1 ≤ x`), `f_α(x) ≤ f_β(x)`. Immediate from general
reachability (`reaches_of_lt`) and value transfer (`fastGrowing_le_of_reaches`). The budget
condition `norm α ≤ x` is essential: below it the inequality can fail (small-`n` index
reversal). -/
theorem fastGrowing_le_of_lt {x : ℕ} (hx : 1 ≤ x) {α β : ONote} (hα : α.NF) (hβ : β.NF)
    (hαβ : α < β) (hnorm : norm α ≤ x) : fastGrowing α x ≤ fastGrowing β x :=
  fastGrowing_le_of_reaches hx (reaches_of_lt β hβ α hα hαβ hnorm)

/-! ### The notation successor `osucc` (for the strict step in index domination)

To bump the `≤` from `Reaches` to a strict `<` we route the descent through the
notation-successor of `o`: `Reaches n (tower n) (osucc o)` plus the strict successor index
step. `osucc` is defined structurally so its `fundamentalSequence` is transparent
(`inl (some o)`). -/

/-- The **notation successor** `osucc o` (with `repr (osucc o) = repr o + 1` and
`fundamentalSequence (osucc o) = inl (some o)` on normal forms). Defined structurally:
increment the finite tail, recursing through the CNF spine. -/
def osucc : ONote → ONote
  | 0 => oadd 0 1 0
  | oadd 0 n _ => oadd 0 (n + 1) 0
  | oadd (oadd e' n' a') m b => oadd (oadd e' n' a') m (osucc b)

theorem repr_osucc : ∀ {o : ONote}, o.NF → (osucc o).repr = o.repr + 1
  | 0, _ => by simp [osucc]
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [repr_zero, opow_zero] at hlt
        exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact Order.lt_one_iff.1 hlt)
      subst ha0
      show (oadd 0 (n + 1) 0).repr = (oadd 0 n 0).repr + 1
      simp only [ONote.repr, opow_zero, one_mul, add_zero, PNat.add_coe,
        PNat.one_coe, Nat.cast_add, Nat.cast_one]
  | oadd (oadd e' n' a') m b, h => by
      show (oadd (oadd e' n' a') m (osucc b)).repr = (oadd (oadd e' n' a') m b).repr + 1
      simp only [ONote.repr]
      rw [repr_osucc h.snd, ← add_assoc]

theorem osucc_NF : ∀ {o : ONote}, o.NF → (osucc o).NF
  | 0, _ => NF.oadd_zero 0 1
  | oadd 0 n _, _ => NF.oadd_zero 0 (n + 1)
  | oadd (oadd e' n' a') m b, h => by
      refine NF.oadd h.fst m (NF.below_of_lt' ?_ (osucc_NF h.snd))
      rw [repr_osucc h.snd, ← Order.succ_eq_add_one]
      have hElim : Order.IsSuccLimit (ω ^ (oadd e' n' a').repr) := by
        refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
        have hpos : (0 : Ordinal) < (oadd e' n' a').repr := by
          rw [← repr_zero]; exact lt_def.1 (oadd_pos e' n' a')
        exact hpos.ne'
      exact hElim.succ_lt h.snd'.repr_lt

theorem fundamentalSequence_osucc : ∀ {o : ONote}, o.NF →
    fundamentalSequence (osucc o) = Sum.inl (some o)
  | 0, _ => rfl
  | oadd 0 n a, h => by
      have ha0 : a = 0 := by
        have hlt : a.repr < ω ^ (0 : ONote).repr := h.snd'.repr_lt
        rw [repr_zero, opow_zero] at hlt
        exact (@repr_inj a 0 h.snd NF.zero).1 (by rw [repr_zero]; exact Order.lt_one_iff.1 hlt)
      subst ha0
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k.succPNat := ⟨n.natPred, (PNat.succPNat_natPred n).symm⟩
      rfl
  | oadd (oadd e' n' a') m b, h =>
      fundamentalSequence_oadd_succ (fundamentalSequence_osucc h.snd)

theorem norm_osucc_le : ∀ {o : ONote}, norm (osucc o) ≤ norm o + 1
  | 0 => by simp [osucc, norm]
  | oadd 0 n _ => by
      simp only [osucc, norm_oadd, norm_zero, PNat.add_coe, PNat.one_coe]; omega
  | oadd (oadd e' n' a') m b => by
      have ih : norm (osucc b) ≤ norm b + 1 := norm_osucc_le
      simp only [osucc, norm_oadd]; omega

/-- The **diagonal tower** `0, 1, ω, ω^ω, …` underlying `ONote.fastGrowingε₀`:
`tower i = (fun a => ω^a)^[i] 0`. -/
def tower (i : ℕ) : ONote := (fun a => oadd a 1 0)^[i] 0

@[simp] theorem tower_zero : tower 0 = 0 := rfl

/-- `tower (i+1) = ω^{tower i}`. -/
theorem tower_succ (i : ℕ) : tower (i + 1) = oadd (tower i) 1 0 := by
  rw [tower, tower, Function.iterate_succ_apply']

/-- Every tower level is a normal-form notation. -/
theorem tower_NF : ∀ i, (tower i).NF
  | 0 => by rw [tower_zero]; exact NF.zero
  | i + 1 => by rw [tower_succ]; haveI := tower_NF i; exact NF.oadd_zero _ _

/-- The tower is **strictly increasing**: `tower i < tower (i+1) = ω^{tower i}`. The
strictness is exactly `repr_lt_opow_repr` at `tower i`. -/
theorem tower_lt_succ (i : ℕ) : tower i < tower (i + 1) := by
  rw [tower_succ, lt_def]
  have hrepr : ((tower i).oadd 1 0).repr = ω ^ (tower i).repr := by
    simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]
  rw [hrepr]
  exact repr_lt_opow_repr _ (tower_NF i)

/-- The tower is monotone in its index. -/
theorem tower_strictMono : StrictMono tower :=
  strictMono_nat_of_lt_succ tower_lt_succ

/-- `repr (tower (i+1)) = ω ^ repr (tower i)`. -/
theorem repr_tower_succ (i : ℕ) : (tower (i + 1)).repr = ω ^ (tower i).repr := by
  rw [tower_succ]
  simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero]

/-- **Cofinality of the tower in `ε₀`.** Every normal-form notation is below some tower
level. Structural induction: for `o = ω^e·n + a`, the IH gives `e < tower j`, and then
`o < ω^(repr e + 1) ≤ ω^(repr (tower j)) = repr (tower (j+1))`, so `o < tower (j+1)`. -/
theorem tower_cofinal : ∀ (o : ONote), o.NF → ∃ k, o < tower k
  | 0, _ => ⟨1, by rw [lt_def]; simp [tower_succ]⟩
  | oadd e n a, h => by
      obtain ⟨j, hj⟩ := tower_cofinal e h.fst
      refine ⟨j + 1, ?_⟩
      rw [lt_def, repr_tower_succ]
      have hej : e.repr < (tower j).repr := (lt_def).mp hj
      have hbelow : NFBelow (oadd e n a) (e.repr + 1) :=
        NFBelow.oadd h.fst h.snd' (Order.lt_succ _)
      have h1 : (oadd e n a).repr < ω ^ (e.repr + 1) := hbelow.repr_lt
      have h2 : ω ^ (e.repr + 1) ≤ ω ^ (tower j).repr :=
        opow_le_opow_right omega0_pos (Order.succ_le_of_lt hej)
      exact lt_of_lt_of_le h1 h2

/-- `fastGrowingε₀ i = f_{tower i}(i)` — the definitional unfolding, as a named lemma. -/
theorem fastGrowingε₀_eq (i : ℕ) : fastGrowingε₀ i = fastGrowing (tower i) i := rfl

/-- **Index domination — the A4 core, proved axiom-clean.** Once a tower level has overtaken
`o` (`o < tower n`), it strictly dominates `o` at the diagonal argument:
`f_o(n) < f_{tower n}(n)`, for `n ≥ 2` past `norm o`. The full Bachmann reachability strength
(`reaches_of_lt`: `tower n` reaches the successor of `o` with budget `n`, generalizing
`fastGrowing_bachmann_reach` from consecutive indices to arbitrary `α < β`) plus one strict
successor step (`fastGrowing_lt_succ_index`). The growth gap of Kirby–Paris independence. -/
theorem fastGrowing_lt_of_lt_tower {o : ONote} (ho : o.NF) (n : ℕ)
    (hn : norm o < n) (h2 : 2 ≤ n) (h : o < tower n) :
    fastGrowing o n < fastGrowing (tower n) n := by
  -- `tower n` is a limit ordinal for `n ≥ 2`: `repr (tower n) = ω^(repr (tower (n-1)))`
  -- with `tower (n-1) > 0`, so `ω^· ` is a limit.
  have hlimit : Order.IsSuccLimit (tower n).repr := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [repr_tower_succ]
    refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
    have hpos : (0 : ONote) < tower j :=
      tower_zero ▸ tower_strictMono (show (0 : ℕ) < j by omega)
    rw [← repr_zero]; exact (lt_def.1 hpos).ne'
  -- Reach the *successor* of `o`, then take one strict successor step.
  have hNF : (osucc o).NF := osucc_NF ho
  have hlt : osucc o < tower n := by
    rw [lt_def, repr_osucc ho, ← Order.succ_eq_add_one]
    exact hlimit.succ_lt (lt_def.1 h)
  have hnorm : norm (osucc o) ≤ n := le_trans norm_osucc_le (by omega)
  have hreach : Reaches n (tower n) (osucc o) :=
    reaches_of_lt (tower n) (tower_NF n) (osucc o) hNF hlt hnorm
  have hle : fastGrowing (osucc o) n ≤ fastGrowing (tower n) n :=
    fastGrowing_le_of_reaches (le_trans one_le_two h2) hreach
  have hstrict : fastGrowing o n < fastGrowing (osucc o) n :=
    fastGrowing_lt_succ_index (fundamentalSequence_osucc ho) h2
  exact lt_of_lt_of_le hstrict hle

/-- **A4 — domination (the headline crux).** Every fixed level of the fast-growing
hierarchy is eventually strictly dominated by `fastGrowingε₀`. Reduced (axiom-clean modulo
the index-domination core) to `tower_cofinal` + `fastGrowing_lt_of_lt_tower`: pick `k` with
`o < tower k`; for `n ≥ max k 1`, `o < tower k ≤ tower n`, so `f_o(n) < f_{tower n}(n) =
fastGrowingε₀ n`. -/
theorem fastGrowing_lt_fastGrowingε₀ (o : ONote) (ho : o.NF) :
    ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n := by
  obtain ⟨k, hk⟩ := tower_cofinal o ho
  refine ⟨max (max k (norm o + 1)) 2, fun n hn => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨⟨hkn, hnormn⟩, h2n⟩ := hn
  have hlt : o < tower n := lt_of_lt_of_le hk (tower_strictMono.monotone hkn)
  rw [fastGrowingε₀_eq]
  exact fastGrowing_lt_of_lt_tower ho n (by omega) h2n hlt

/-! ### Anti-vacuity anchors for `fastGrowingε₀` (`native_decide`) -/

example : fastGrowingε₀ 0 = 1 := by native_decide
example : fastGrowingε₀ 1 = 2 := by native_decide
example : fastGrowingε₀ 2 = 2048 := by native_decide
-- the tower really is `ω^ω` at level 3 (a genuine limit-of-limits index)
example : tower 3 = oadd (oadd 1 1 0) 1 0 := by native_decide


-- ════════════════ ported: Hardy.lean ════════════════
/-
# The Hardy hierarchy `H_α`

The **Hardy hierarchy** is the companion of the fast-growing hierarchy used in the
Kirby–Paris / Goodstein growth argument. mathlib has `ONote.fastGrowing` but **not**
the Hardy hierarchy at all — this file introduces it, mirroring `fastGrowing`'s
structure on `ONote.fundamentalSequence`:

* `H₀(n) = n`              (identity, vs. `f₀ = succ`)
* `H_{α+1}(n) = H_α(n+1)`  (one step of `+1`, vs. `f_{α+1} n = f_α^[n] n`)
* `H_λ(n) = H_{λ[n]}(n)`   (limit, via the fundamental sequence — same as `fastGrowing`)

It is **computable** (it builds on the computable `fundamentalSequence`), so we can
pin small values with `native_decide` anchors. The classical identity `H_{ω^α} = f_α`
(a long-horizon target, B4) connects it back to `fastGrowing`.

The definition uses the *same* well-founded `<`-recursion on `ONote` that defines
`fastGrowing`; the characterization lemmas `hardy_zero'/_succ/_limit` mirror
`fastGrowing_zero'/_succ/_limit` and are proved the same way (`hardy_def` + `subst`).
-/



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

/-- Unfolding lemma for `hardy`, mirroring `ONote.fastGrowing_def`. -/
theorem hardy_def {o : ONote} {x} (e : fundamentalSequence o = x) :
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
theorem hardy_zero' (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    hardy o = id := by
  rw [hardy_def h]

/-- `H_o(n) = H_a(n+1)` when `o` is the successor of `a`. -/
theorem hardy_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hardy o = fun n => hardy a (n + 1) := by
  rw [hardy_def h]

/-- `H_o(n) = H_{o[n]}(n)` when `o` is a limit with fundamental sequence `f`. -/
theorem hardy_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hardy o = fun n => hardy (f n) n := by
  rw [hardy_def h]

/-- `H₀ = id`. -/
@[simp]
theorem hardy_zero : hardy 0 = id :=
  hardy_zero' _ rfl

/-- `H₁(n) = n + 1` — the first successor level just adds one. -/
theorem hardy_one : hardy 1 = fun n => n + 1 := by
  rw [@hardy_succ 1 0 rfl]; funext n; rw [hardy_zero]; rfl

/-- `H₂(n) = n + 2`. -/
theorem hardy_two : hardy 2 = fun n => n + 2 := by
  rw [@hardy_succ 2 1 rfl]; funext n; rw [hardy_one]

/-! ### Growth theory of the Hardy hierarchy -/

/-- **Expansiveness of the Hardy hierarchy.** `n ≤ H_o(n)` for every notation `o`.
Well-founded recursion on `o` (no normal-form hypothesis): `H₀ = id`; the successor
step uses `n ≤ n+1 ≤ H_a(n+1)` and the limit step is the IH at `o[n] < o`. -/
theorem le_hardy (o : ONote) (n : ℕ) : n ≤ hardy o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact le_rfl
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [hardy_succ o e]
    exact le_trans (Nat.le_succ n) (le_hardy a (n + 1))
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [hardy_limit o e]
    exact le_hardy (f n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Value transfer for the Hardy hierarchy.** If `β` structurally reaches `α` at budget
`x` and *every* notation `β` reaches has a monotone Hardy level, then `H_α(x) ≤ H_β(x)`.
Unlike the fast-growing transfer, the successor step `H_β(x) = H_γ(x+1)` shifts the
argument, so it must absorb the `+1` using monotonicity of the intermediate `H_γ` — hence
the monotonicity hypothesis (supplied, in `hardy_monotone`, by the well-founded IH). -/
theorem hardy_le_of_reaches {x : ℕ} {β α : ONote} (h : Reaches x β α) :
    (∀ γ, Reaches x β γ → Monotone (hardy γ)) → hardy α x ≤ hardy β x := by
  induction h with
  | refl a => intro _; exact le_rfl
  | @succ β γ α hb _ ih =>
      intro hmono
      have hmγ : Monotone (hardy γ) := hmono γ (Reaches.succ hb (Reaches.refl γ))
      have ihγ : hardy α x ≤ hardy γ x := ih (fun δ hδ => hmono δ (Reaches.succ hb hδ))
      have heq : hardy β x = hardy γ (x + 1) := by rw [hardy_succ _ hb]
      rw [heq]; exact le_trans ihγ (hmγ (Nat.le_succ x))
  | @limit β α g hb _ ih =>
      intro hmono
      have ihg : hardy α x ≤ hardy (g x) x := ih (fun δ hδ => hmono δ (Reaches.limit hb hδ))
      have heq : hardy β x = hardy (g x) x := by rw [hardy_limit _ hb]
      rw [heq]; exact ihg

/-- **Monotonicity in the argument** of each Hardy level — fully proved, axiom-clean, for
EVERY notation `o`. Well-founded recursion on `o`: the successor case composes the IH at
`a < o`; the limit case combines monotonicity of `H_{o[n]}` (IH) with the index step
`H_{o[n]}(n+1) ≤ H_{o[n+1]}(n+1)`, which is `hardy_le_of_reaches` applied to the structural
Bachmann reach `fastGrowing_bachmann_reach` (every intermediate is `< o`, so the IH supplies
its monotonicity). The same `Reaches` engine that closes the fast-growing crux. -/
theorem hardy_monotone (o : ONote) : Monotone (hardy o) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e]; exact Nat.le_succ n
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [hardy_succ o e]
    exact hardy_monotone a (Nat.le_succ (n + 1))
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 n).2.1
    have hltn1 : f (n + 1) < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 (n + 1)).2.1
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
theorem hardy_le_succ (o : ONote) (n : ℕ) : hardy o n ≤ hardy o (n + 1) :=
  hardy_monotone o (Nat.le_succ n)

/-! ### Hardy argument-shift (additivity for a finite tail)

`H_{α+c}(n) = H_α(n+c)` for finite `c` — the Hardy hierarchy's additivity restricted to a finite
ordinal added on the right. The §19.6-cut-elimination "option 2" ingredient: it lets a *linearly*
reindexed ω-rule premise (index `n ↦ n+c`) be absorbed by a constant bump of the ordinal, so the
witness bound `H_α(n+c) < G(n)` reduces (for the `c`-bumped ordinal) to the banked domination
`H_{α+c}(n) < G(n)`. Proof: induction on `c` via the successor rule and `α + (c+1) = osucc (α + c)`. -/

private theorem add_ofNat_zero {α : ONote} (hα : α.NF) : α + ofNat 0 = α := by
  haveI := hα
  haveI : (0 : ONote).NF := NF.zero
  rw [ofNat_zero]
  haveI : (α + 0).NF := ONote.add_nf α 0
  apply repr_inj.mp
  rw [repr_add, repr_zero, add_zero]

private theorem add_ofNat_succ {α : ONote} (hα : α.NF) (c : ℕ) :
    α + ofNat (c + 1) = osucc (α + ofNat c) := by
  haveI := hα
  haveI hac : (α + ofNat c).NF := ONote.add_nf α (ofNat c)
  haveI : (α + ofNat (c + 1)).NF := ONote.add_nf α (ofNat (c + 1))
  haveI : (osucc (α + ofNat c)).NF := osucc_NF hac
  apply repr_inj.mp
  rw [repr_osucc hac, repr_add, repr_add, repr_ofNat, repr_ofNat,
    Nat.cast_add, Nat.cast_one, ← add_assoc]

/-- **Hardy argument-shift / finite-tail additivity:** `H_{α+c}(n) = H_α(n+c)`. -/
theorem hardy_add_ofNat {α : ONote} (hα : α.NF) :
    ∀ (c n : ℕ), hardy (α + ofNat c) n = hardy α (n + c) := by
  intro c
  induction c with
  | zero => intro n; rw [add_ofNat_zero hα]; simp
  | succ c ih =>
    intro n
    rw [add_ofNat_succ hα c]
    have hs := hardy_succ (osucc (α + ofNat c))
      (fundamentalSequence_osucc (ONote.add_nf α (ofNat c)))
    rw [hs]
    simp only []
    rw [ih (n + 1)]
    congr 1
    omega

/-- **The Hardy index-monotonicity crux (limit step), now fully proved.** The Hardy
analogue of `fastGrowing_fundSeq_step`: for a limit `o` with fundamental sequence `f`,
`H_{o[n]}(n+1) ≤ H_{o[n+1]}(n+1)`. A corollary of `hardy_le_of_reaches` on the Bachmann
reach, with monotonicity supplied by `hardy_monotone`. -/
theorem hardy_fundSeq_step {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (n : ℕ) :
    hardy (f n) (n + 1) ≤ hardy (f (n + 1)) (n + 1) :=
  hardy_le_of_reaches (fastGrowing_bachmann_reach h n) (fun γ _ => hardy_monotone γ)

/-- **Finite-level argument monotonicity for Hardy**, proved cleanly (no crux).
`Monotone (H_k)` for `k : ℕ`: `H_0 = id`; `H_{k+1} = H_k ∘ (·+1)` is monotone as a
composition. -/
theorem hardy_ofNat_monotone (k : ℕ) : Monotone (hardy (ofNat k)) := by
  induction k with
  | zero => simpa [ofNat_zero, hardy_zero] using monotone_id
  | succ k ih =>
      rw [hardy_succ _ (fundamentalSequence_ofNat_succ k)]
      exact ih.comp (monotone_id.add_const 1)

/-- **Finite-level index monotonicity for Hardy** (no positivity needed, unlike
`fastGrowing`): for `m ≤ n`, `H_m(x) ≤ H_n(x)`. Single step: `H_{k+1}(x) = H_k(x+1) ≥
H_k(x)` by `hardy_ofNat_monotone`. -/
theorem hardy_ofNat_mono {m n : ℕ} (hmn : m ≤ n) (x : ℕ) :
    hardy (ofNat m) x ≤ hardy (ofNat n) x := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
      refine le_trans ih ?_
      rw [hardy_succ _ (fundamentalSequence_ofNat_succ n)]
      exact hardy_ofNat_monotone n (Nat.le_succ x)

/-- **Monotonicity of `H_ω`, fully proved (axiom-clean).** The Hardy companion of
`fastGrowing_monotone_omega`: `H_ω(n) = H_{ofNat(n+1)}(n) ≤ H_{ofNat(n+2)}(n+1) =
H_ω(n+1)`, using only finite-level facts (`ω[n] = n+1`). -/
theorem hardy_monotone_omega : Monotone (hardy (oadd 1 1 0)) := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [hardy_limit _ hfs]
  calc hardy (ofNat (n + 1)) n
      ≤ hardy (ofNat (n + 1)) (n + 1) := hardy_ofNat_monotone (n + 1) (Nat.le_succ n)
    _ ≤ hardy (ofNat (n + 2)) (n + 1) := hardy_ofNat_mono (Nat.le_succ (n + 1)) (n + 1)

/-- **General index monotonicity of the Hardy hierarchy.** For normal-form `α < β` and
budget `x ≥ norm α`, `H_α(x) ≤ H_β(x)`. From general reachability (`reaches_of_lt`) and the
Hardy value transfer (`hardy_le_of_reaches`), discharging the latter's monotonicity side
condition with `hardy_monotone` (every Hardy level is monotone). The Hardy companion of
`fastGrowing_le_of_lt`. -/
theorem hardy_le_of_lt {x : ℕ} {α β : ONote} (hα : α.NF) (hβ : β.NF)
    (hαβ : α < β) (hnorm : norm α ≤ x) : hardy α x ≤ hardy β x :=
  hardy_le_of_reaches (reaches_of_lt β hβ α hα hαβ hnorm) (fun γ _ => hardy_monotone γ)

/-- **Closed form for finite Hardy levels:** `H_k(x) = x + k`. Induction on `k`: `H_0 = id`;
`H_{k+1}(x) = H_k(x+1) = (x+1) + k` via the successor step `(k+1)[·] = k`. -/
theorem hardy_ofNat (k x : ℕ) : hardy (ofNat k) x = x + k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    simp only [hardy_succ _ (fundamentalSequence_ofNat_succ k)]
    rw [ih (x + 1)]; omega

/-- **Closed form for `H_ω`.** `H_ω(n) = 2n + 1` — mathlib's `ω[n] = ofNat (n+1)` makes the
limit step land on the finite level `n+1`, so `H_ω(n) = H_{n+1}(n) = n + (n+1) = 2n+1`. (The
`+1` over the classical `H_ω(n)=n` is exactly the `ω[n]=n+1` convention shift.) -/
theorem hardy_omega (n : ℕ) : hardy (oadd 1 1 0) n = 2 * n + 1 := by
  have hfs : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ofNat (i + 1)) := rfl
  have h1 : hardy (oadd 1 1 0) n = hardy (ofNat (n + 1)) n := by
    simp only [hardy_limit _ hfs]
  rw [h1, hardy_ofNat (n + 1) n]
  omega

/-- **First super-linear Hardy lower bound:** `2n ≤ H_{ω^e}(n)` for every nonzero exponent
`e` (and `n ≥ 1`). Every `ω^e` with `e ≠ 0` is `≥ ω`, and the budget `norm ω = 1 ≤ n` is met,
so `H_ω(n) = 2n+1 ≤ H_{ω^e}(n)` by index monotonicity (`hardy_le_of_lt`); the `e = 1` boundary
is `H_ω` itself. A building block: Hardy values at limit indices grow at least linearly with
slope `≥ 2`, the first step past the identity `H₀ = id`. -/
theorem two_mul_le_hardy_pow {e : ONote} (he : e ≠ 0) (hNFe : e.NF) {n : ℕ} (hn : 1 ≤ n) :
    2 * n ≤ hardy (oadd e 1 0) n := by
  have hNF1 : (1 : ONote).NF := NF.oadd NF.zero 1 NFBelow.zero
  have hNFω : (oadd 1 1 0).NF := NF.oadd hNF1 1 NFBelow.zero
  have hNFe1 : (oadd e 1 0).NF := NF.oadd hNFe 1 NFBelow.zero
  have he_pos : 0 < e.repr := by
    rcases eq_zero_or_pos e.repr with h | h
    · exact absurd ((@repr_inj e 0 hNFe NF.zero).1 (by rw [h, repr_zero])) he
    · exact h
  -- `ω = ω^1 ≤ ω^(repr e)` since `1 ≤ repr e`
  have hle : (oadd 1 1 0).repr ≤ (oadd e 1 0).repr := by
    have hr1 : (oadd 1 1 0).repr = ω ^ (1 : Ordinal) := by simp [ONote.repr]
    have hre : (oadd e 1 0).repr = ω ^ e.repr := by simp [ONote.repr]
    rw [hr1, hre]
    exact opow_le_opow_right omega0_pos (Order.one_le_iff_pos.2 he_pos)
  rcases eq_or_lt_of_le hle with heq | hlt
  · have heqo : oadd 1 1 0 = oadd e 1 0 := (@repr_inj (oadd 1 1 0) (oadd e 1 0) hNFω hNFe1).1 heq
    rw [← heqo, hardy_omega]; omega
  · have hbudget : norm (oadd 1 1 0) ≤ n := by
      have hn1 : norm (oadd 1 1 0) = 1 := by decide
      omega
    have h := hardy_le_of_lt hNFω hNFe1 (lt_def.2 hlt) hbudget
    rw [hardy_omega] at h; omega

/-! ### The Hardy step `hstep` and the step invariant `H_o(n) = H_{hstep o n}(n+1)`

The Hardy hierarchy "counts the steps" of an ordinal descent in which the *argument* grows
by one each time the ordinal drops past a successor. To make that precise we isolate one
**budget-incrementing step** `hstep o n`: descend through limit stages of `o` (each at the
fixed argument `n`) until passing exactly one successor, returning the resulting notation.
The single intrinsic fact we need is then `H_o(n) = H_{hstep o n}(n+1)` (`hardy_hstep`) for
nonzero `o` — the engine that telescopes any unit-step ordinal descent into a Hardy value.
This is the FastGrowing-side prerequisite for C3 (`Goodstein/Growth.lean`), where the
Goodstein descent is shown to *be* this Hardy step (`hstep_seqONote`). -/

/-- The fundamental sequence of a limit notation is everywhere nonzero: every branch of
`ONote.fundamentalSequence` for a limit returns `fun i => oadd …`, and `oadd` is positive.
Needed so the limit recursion of `hstep`/`hardy_hstep` never collapses to `0` prematurely. -/
theorem fundamentalSequence_inr_ne_zero {o : ONote} {f : ℕ → ONote}
    (h : fundamentalSequence o = Sum.inr f) (i : ℕ) : f i ≠ 0 := by
  induction o with
  | zero => simp [fundamentalSequence] at h
  | oadd a m b iha ihb =>
    rw [fundamentalSequence] at h
    split at h
    · injection h with h'; subst h'; exact (oadd_pos _ _ _).ne'
    · exact (Sum.inl_ne_inr h).elim
    · split at h <;>
        first
          | exact (Sum.inl_ne_inr h).elim
          | (injection h with h'; subst h'; simp only []; exact (oadd_pos _ _ _).ne')

/-- One budget-incrementing **Hardy step** on a notation at argument `n`: descend through
limit stages (each at argument `n`) until passing exactly one successor; `hstep 0 n = 0`.
Same well-founded `<`-recursion on `ONote` as `hardy`/`fastGrowing`. -/
def hstep : ONote → ℕ → ONote
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => fun _ => 0
    | Sum.inl (some a), _ => fun _ => a
    | Sum.inr f, h => fun n =>
      have : f n < o := (h.2.1 n).2.1
      hstep (f n) n
  termination_by o => o

/-- Unfolding lemma for `hstep`, mirroring `hardy_def`. -/
theorem hstep_def {o : ONote} {x} (e : fundamentalSequence o = x) :
    hstep o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ONote)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => fun _ => 0
      | Sum.inl (some a), _ => fun _ => a
      | Sum.inr f, _ => fun n => hstep (f n) n := by
  subst x; rw [hstep]

/-- `hstep o = fun _ => a` when `o` is the successor of `a`. -/
theorem hstep_succ (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    hstep o = fun _ => a := by rw [hstep_def h]

/-- `hstep o = fun n => hstep (o[n]) n` when `o` is a limit with fundamental sequence `f`. -/
theorem hstep_limit (o) {f} (h : fundamentalSequence o = Sum.inr f) :
    hstep o = fun n => hstep (f n) n := by rw [hstep_def h]

/-- **Intrinsic Hardy step invariant.** For a nonzero notation, one budget-incrementing
Hardy step preserves the Hardy value: `H_o(n) = H_{hstep o n}(n+1)`. The successor case is
definitional (`H_{a+1}(n) = H_a(n+1)`); the limit case recurses (each fundamental-sequence
member is nonzero by `fundamentalSequence_inr_ne_zero`, so the IH applies). -/
theorem hardy_hstep (o : ONote) (n : ℕ) (h : o ≠ 0) :
    hardy o n = hardy (hstep o n) (n + 1) := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · exact absurd ((fundamentalSequenceProp_inl_none o).1 (e ▸ fundamentalSequence_has_prop o)) h
  · rw [hardy_succ o e, hstep_succ o e]
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp; exact (hp.2.1 n).2.1
    rw [hardy_limit o e, hstep_limit o e]
    exact hardy_hstep (f n) n (fundamentalSequence_inr_ne_zero e n)
termination_by o
decreasing_by exact hlt

/-- **Peeling the leading term of a Hardy step.** When the tail `R` is nonzero, a Hardy step
on `oadd E C R` happens entirely inside the tail: `hstep (oadd E C R) b = oadd E C (hstep R b)`.
Well-founded induction on `R` (its `ONote <`, via `InvImage repr`): if `R` is a successor the
step peels directly; if `R` is a limit the step descends to `R[b] ≠ 0 < R` and the IH applies.
The actual decrement only occurs once `R = 0`. -/
theorem hstep_oadd_tail (E : ONote) (C : ℕ+) (b : ℕ) :
    ∀ R, R ≠ 0 → hstep (oadd E C R) b = oadd E C (hstep R b) := by
  intro R
  induction R using (InvImage.wf repr Ordinal.lt_wf).induction with
  | _ R ih =>
    intro hR
    rcases e : fundamentalSequence R with (_ | R') | g
    · exact absurd ((fundamentalSequenceProp_inl_none R).1 (e ▸ fundamentalSequence_has_prop R)) hR
    · rw [hstep_succ _ (fundamentalSequence_oadd_succ e), hstep_succ _ e]
    · rw [hstep_limit _ (fundamentalSequence_oadd_limit e), hstep_limit _ e]
      have hgb : g b ≠ 0 := fundamentalSequence_inr_ne_zero e b
      have hglt : g b < R := by
        have hp := fundamentalSequence_has_prop R; rw [e] at hp; exact (hp.2.1 b).2.1
      exact ih (g b) (lt_def.1 hglt) hgb

/-! ### Anti-vacuity anchors (`native_decide`)

Standalone witnesses, off any headline axiom path, that a *wrong* definition of
`hardy` would fail to satisfy. They pin both the successor branch (`H_k(n) = n + k`)
and the limit branch: mathlib's fundamental sequence for `ω` is `ω[n] = n + 1`, so
`H_ω(n) = H_{n+1}(n) = n + (n+1) = 2n + 1`. -/

example : hardy 0 5 = 5 := by native_decide
example : hardy 1 5 = 6 := by native_decide
example : hardy 2 5 = 7 := by native_decide
example : hardy 3 5 = 8 := by native_decide
example : hardy 4 5 = 9 := by native_decide
-- limit branch: `H_ω(n) = 2n + 1` (`ω = oadd 1 1 0`, `ω[n] = n + 1`)
example : hardy (oadd 1 1 0) 2 = 5 := by native_decide
example : hardy (oadd 1 1 0) 4 = 9 := by native_decide
example : hardy (oadd 1 1 0) 6 = 13 := by native_decide
-- the new closed forms / lower bound, witnessed concretely (a wrong proof would mis-evaluate):
example : hardy (ofNat 4) 5 = 5 + 4 := by native_decide       -- hardy_ofNat
example : hardy (oadd 1 1 0) 6 = 2 * 6 + 1 := by native_decide -- hardy_omega
example : 2 * 2 ≤ hardy (oadd (oadd 0 2 0) 1 0) 2 := by native_decide -- two_mul_le_hardy_pow at ω²: 4 ≤ 23
-- `hstep`: successor drops one level; `ω` at budget `3` descends to `ω[3]=4` then to `3`.
example : hstep 5 0 = 4 := by native_decide
example : hstep (oadd 1 1 0) 3 = 3 := by native_decide
-- the step invariant in action: `H_ω(3) = H_{hstep ω 3}(4) = H_3(4)`
example : hardy (oadd 1 1 0) 3 = hardy (hstep (oadd 1 1 0) 3) 4 := by native_decide

/-- **Hardy tail-peeling — the additive law, ONote-native form.** Splitting off the tail of an `oadd`
composes the Hardy functions: `hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n)` (i.e.
`H_{ω^{repr a}·m + repr b}(n) = H_{ω^{repr a}·m}(H_{repr b}(n))`, valid since the tail `b` cannot absorb
the leading term). By well-founded recursion on the tail `b` — the same recursion `hardy`/
`fundamentalSequence` use (the fund. seq. of `oadd a m b` acts on the tail `b`): the successor and
limit tail cases each reduce to the IH at the smaller tail; the `b = 0` case is `hardy 0 = id`. No
ordinal-addition machinery needed — purely structural.

This is the **non-absorbing Hardy additive law** (the general `H_{α+β}=H_α∘H_β` is false —
`1+ω=ω` makes `H_{1+ω}=H_ω ≠ H_1∘H_ω`). It is the key brick for the coefficient lemma
`H_{ω^β·j} = (H_{ω^β})^[j]` and hence for B4 (`H_{ω^α} = f_α` at finite `α`). -/
theorem hardy_oadd_tail (a : ONote) (m : ℕ+) (b : ONote) (n : ℕ) :
    hardy (oadd a m b) n = hardy (oadd a m 0) (hardy b n) := by
  rcases e : fundamentalSequence b with (_ | b') | f
  · have hb0 : b = 0 := by
      have hp := fundamentalSequence_has_prop b; rw [e] at hp
      rwa [fundamentalSequenceProp_inl_none] at hp
    rw [hardy_zero' b e, hb0]; rfl
  · have hlt : b' < b := by
      have hp := fundamentalSequence_has_prop b; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    have hfs : fundamentalSequence (oadd a m b) = Sum.inl (some (oadd a m b')) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_succ _ hfs, hardy_succ b e]
    exact hardy_oadd_tail a m b' (n + 1)
  · have hlt : f n < b := by
      have hp := fundamentalSequence_has_prop b; rw [e] at hp
      exact (hp.2.1 n).2.1
    have hfs : fundamentalSequence (oadd a m b) = Sum.inr (fun i => oadd a m (f i)) := by
      conv_lhs => rw [fundamentalSequence]; rw [e]
    rw [hardy_limit _ hfs, hardy_limit b e]
    exact hardy_oadd_tail a m (f n) n
termination_by b
decreasing_by all_goals exact hlt

/-- Anti-vacuity for `hardy_oadd_tail`: `H_{ω·2 + 1}(2) = H_{ω·2}(H_1(2)) = H_{ω·2}(3)`. -/
example : hardy (oadd 1 2 1) 2 = hardy (oadd 1 2 0) (hardy 1 2) := hardy_oadd_tail 1 2 1 2

/-- **Coefficient step.** Bumping the coefficient of `ω^β` by one composes with `H_{ω^β}`:
`H_{ω^β·(j+1)}(x) = H_{ω^β·j}(H_{ω^β}(x))` (for `β ≠ 0`). Case `β` succ/limit, compute the
fundamental sequence of `oadd β (j+1) 0` (its `[x]` is `ω^β·j + (ω^β)[x]`, an `oadd β j _`), then
peel the tail with `hardy_oadd_tail`. -/
theorem hardy_oadd_coeff_step (β : ONote) (hβ : β ≠ 0) (k x : ℕ) :
    hardy (oadd β (k + 1).succPNat 0) x
      = hardy (oadd β k.succPNat 0) (hardy (oadd β 1 0) x) := by
  rcases e : fundamentalSequence β with (_ | β') | f
  · exfalso; apply hβ
    have hp := fundamentalSequence_has_prop β; rw [e] at hp
    exact (fundamentalSequenceProp_inl_none β).mp hp
  · have hfs : fundamentalSequence (oadd β (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd β k.succPNat (oadd β' i.succPNat 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    show hardy (oadd β k.succPNat (oadd β' x.succPNat 0)) x
        = hardy (oadd β k.succPNat 0) (hardy (oadd β 1 0) x)
    rw [hardy_oadd_tail β k.succPNat (oadd β' x.succPNat 0) x,
        hardy_limit (oadd β 1 0) (fundamentalSequence_omega_pow_succ e)]
  · have hfs : fundamentalSequence (oadd β (k + 1).succPNat 0)
        = Sum.inr (fun i => oadd β k.succPNat (oadd (f i) 1 0)) := by
      conv_lhs => rw [fundamentalSequence]
      rw [e]; rfl
    rw [hardy_limit _ hfs]
    show hardy (oadd β k.succPNat (oadd (f x) 1 0)) x
        = hardy (oadd β k.succPNat 0) (hardy (oadd β 1 0) x)
    rw [hardy_oadd_tail β k.succPNat (oadd (f x) 1 0) x,
        hardy_limit (oadd β 1 0) (fundamentalSequence_omega_pow_limit e)]

/-- **The coefficient lemma `H_{ω^β·j} = (H_{ω^β})^[j]`** (`β ≠ 0`, `j = k+1`):
`hardy (oadd β (k+1) 0) x = (hardy (oadd β 1 0))^[k+1] x`. By induction on `k` via the step. -/
theorem hardy_oadd_coeff (β : ONote) (hβ : β ≠ 0) (k x : ℕ) :
    hardy (oadd β k.succPNat 0) x = (hardy (oadd β 1 0))^[k + 1] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [hardy_oadd_coeff_step β hβ k x, ih (hardy (oadd β 1 0) x), ← Function.iterate_succ_apply]

/-! ### The general non-absorbing Hardy additive composition law `H_{γ+δ} = H_γ ∘ H_δ`

`hardy_oadd_tail` handles a single leading term. Generalizing the left summand `γ` to a full
Cantor-normal-form notation gives the additive composition law for *non-absorbing* sums: when
`δ` lies strictly below `γ`'s least exponent (so `γ + δ` is genuine CNF concatenation, no
coefficient merge), `H_{γ+δ}(x) = H_γ(H_δ(x))`. This is the load-bearing infra (B) for the
§19.6 control-ordinal operator calculus — the cut-elim control collapse
`H_{e+α}(x) = H_e(H_α(x))` is the instance with the cut-formula bound `α` below the control
ordinal `e`'s least term. The general `H_{α+β}=H_α∘H_β` is FALSE under absorption
(`1+ω=ω` ⟹ `H_{1+ω}=H_ω ≠ H_1∘H_ω`); the non-absorbing hypothesis is exactly what excludes it. -/

/-- The least (trailing) exponent of a notation's Cantor normal form (`0` for `0`). -/
def lastExp : ONote → ONote
  | 0 => 0
  | oadd e _ a => match a with
    | 0 => e
    | oadd _ _ _ => lastExp a

@[simp] theorem lastExp_zero : lastExp 0 = 0 := rfl
@[simp] theorem lastExp_oadd_zero (e n) : lastExp (oadd e n 0) = e := rfl

theorem lastExp_oadd_ne {e : ONote} {n : ℕ+} {a : ONote} (h : a ≠ 0) :
    lastExp (oadd e n a) = lastExp a := by
  cases a with
  | zero => exact absurd rfl h
  | oadd e' n' a' => rfl

/-- `addAux` concatenates (no merge/absorb) when the right operand's leading exponent is
strictly below `e`. -/
theorem addAux_concat {e : ONote} (he : e.NF) {n : ℕ+} {o : ONote} (ho : o.NF)
    (h : o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < e.repr) :
    addAux e n o = oadd e n o := by
  match o, ho, h with
  | 0, _, _ => rfl
  | oadd e' n' a', ho', h' =>
    have hlt : e'.repr < e.repr := by
      rcases h' with h0 | hf
      · exact absurd h0 (by simp)
      · exact hf e' n' a' rfl
    have hee' : ONote.cmp e e' = Ordering.gt :=
      (@ONote.cmp_compares e e' he ho'.fst).eq_gt.2 hlt
    simp only [addAux, hee']

/-- The least exponent of a nonzero notation lies below any bound it is `NFBelow`. -/
theorem lastExp_repr_lt : ∀ {o : ONote} {b : Ordinal}, NFBelow o b → o ≠ 0 →
    (lastExp o).repr < b := by
  intro o
  induction o with
  | zero => intro b _ h; exact absurd rfl h
  | oadd e n a _ iha =>
    intro b hb _
    rcases eq_or_ne a 0 with ha | ha
    · subst ha; rw [lastExp_oadd_zero]; exact hb.lt
    · rw [lastExp_oadd_ne ha]
      exact lt_trans (iha hb.snd ha) hb.lt

/-- Convert an `NFBelow` fact into the leading-exponent bound `addAux_concat` consumes. -/
theorem nfBelow_concat {o : ONote} {b : Ordinal} (h : NFBelow o b) :
    o = 0 ∨ ∀ e' n' a', o = oadd e' n' a' → e'.repr < b := by
  cases o with
  | zero => left; rfl
  | oadd e' n' a' => right; intro e'' n'' a'' heq; cases heq; exact h.lt

/-- **The general non-absorbing Hardy additive composition law.** For normal-form `γ`, `δ`
with `δ` lying strictly below `γ`'s least exponent (so `γ + δ` is genuine Cantor-normal-form
concatenation, no coefficient merge / absorption), the Hardy hierarchy composes:
`H_{γ+δ}(x) = H_γ(H_δ(x))`. Generalizes `hardy_oadd_tail` (single leading term) by induction
on `γ`. -/
theorem hardy_add_comp : ∀ (γ : ONote), γ.NF → ∀ (δ : ONote), δ.NF →
    (δ = 0 ∨ δ.repr < ω ^ (lastExp γ).repr) → ∀ x,
    hardy (γ + δ) x = hardy γ (hardy δ x) := by
  intro γ
  induction γ with
  | zero =>
    intro _ δ _ _ x
    show hardy ((0 : ONote) + δ) x = hardy (0 : ONote) (hardy δ x)
    rw [ONote.zero_add, hardy_zero]; rfl
  | oadd e n a _ iha =>
    intro hγ δ hδ hcond x
    haveI := hγ
    rcases eq_or_ne δ 0 with hδ0 | hδ0
    · subst hδ0
      have hadd : oadd e n a + 0 = oadd e n a :=
        repr_inj.mp (by rw [repr_add, repr_zero, add_zero])
      rw [hadd, hardy_zero]; rfl
    have he : e.NF := hγ.fst
    have hba : NFBelow a e.repr := hγ.snd'
    have ha : a.NF := ⟨⟨e.repr, hba⟩⟩
    have hle : (lastExp (oadd e n a)).repr ≤ e.repr := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · subst ha0; rw [lastExp_oadd_zero]
      · rw [lastExp_oadd_ne ha0]; exact le_of_lt (lastExp_repr_lt hba ha0)
    have hδlt_e : δ.repr < ω ^ e.repr := by
      rcases hcond with h0 | hlt
      · exact absurd h0 hδ0
      · exact lt_of_lt_of_le hlt (opow_le_opow_right omega0_pos hle)
    have hbδ : NFBelow δ e.repr := NF.below_of_lt' hδlt_e hδ
    have hbaδ : NFBelow (a + δ) e.repr := add_nfBelow hba hbδ
    have hcc : addAux e n (a + δ) = oadd e n (a + δ) :=
      addAux_concat he (⟨⟨_, hbaδ⟩⟩) (nfBelow_concat hbaδ)
    rw [oadd_add, hcc, hardy_oadd_tail e n (a + δ) x]
    rcases eq_or_ne a 0 with ha0 | ha0
    · subst ha0; rw [ONote.zero_add]
    · have ihcond : δ = 0 ∨ δ.repr < ω ^ (lastExp a).repr := by
        right
        rcases hcond with h0 | hlt
        · exact absurd h0 hδ0
        · rwa [lastExp_oadd_ne ha0] at hlt
      rw [iha ha δ hδ ihcond x, hardy_oadd_tail e n a (hardy δ x)]

/-- **Control-ordinal collapse** (the §19.6 operator-calculus cut-elim form of the additive
law). When the cut-formula bound `α` lies below the control ordinal `e`'s least exponent,
nesting `H_e ∘ H_α` collapses to a single `H_{e+α}` with `e + α < ε₀` (ε₀ is closed under
`+`). This is exactly the move the control-ordinal operator needs to keep the witness index
inside a single Hardy level under commuting ω-rules. -/
theorem hardy_add_collapse {e α : ONote} (he : e.NF) (hα : α.NF)
    (hbelow : α = 0 ∨ α.repr < ω ^ (lastExp e).repr) (x : ℕ) :
    hardy (e + α) x = hardy e (hardy α x) :=
  hardy_add_comp e he α hα hbelow x

/-! ### The additive-Hardy INEQUALITY (P1 raised-control bridge)

Lap 178 kernel-refuted the additive-Hardy *equality* `H_{e+β}=H_e∘H_β` (false under absorption,
`1+ω=ω`). The **inequality** `H_{e+β}(x) ≤ H_e(H_β(x))` survives absorption and is the exact bridge
the raised control `raise e α = e + ω^α` needs: with `β = ω^α` it bounds `H_{e+ω^α}` by
`H_e(H_{ω^α}(·))`, and `hardy_omega_pow_lt_fastGrowing` gives `H_{ω^α} < f_α`. Unlike the equality,
this holds for **every** NF `e, β`.  Proof: induction on `e` matching ONote `+`'s `addAux` recursion;
with `s = a₁ + β = oadd e' n' a'` the case split on `cmp e₁ e'` is lt (e absorbed) / gt (concat) /
eq (coefficient merge), each closed by the tail-peel `hardy_oadd_tail` + IH + `le_hardy`/monotonicity,
the eq case additionally by coefficient additivity. -/

/-- Single finite term: `H_{ω^0·p}(y) = y + p` (via `oadd 0 p 0 = ofNat p`). -/
theorem hardy_oadd0 (p : ℕ+) (y : ℕ) : hardy (oadd 0 p 0) y = y + (p : ℕ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k.succPNat := ⟨p.natPred, (PNat.succPNat_natPred p).symm⟩
  rw [show oadd 0 k.succPNat 0 = ofNat (k + 1) from (ofNat_succ k).symm, hardy_ofNat,
    Nat.succPNat_coe]

/-- Coefficient-as-iterate, restated for a `ℕ+` coefficient (`e ≠ 0`):
`H_{ω^e·p}(x) = (H_{ω^e})^[p](x)`. -/
theorem hardy_single_coeff (e : ONote) (he : e ≠ 0) (p : ℕ+) (x : ℕ) :
    hardy (oadd e p 0) x = (hardy (oadd e 1 0))^[(p : ℕ)] x := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k.succPNat := ⟨p.natPred, (PNat.succPNat_natPred p).symm⟩
  rw [hardy_oadd_coeff e he k x, Nat.succPNat_coe]

/-- Coefficient additivity at a single term (`e ≠ 0`):
`H_{ω^e·(m+n)}(x) = H_{ω^e·m}(H_{ω^e·n}(x))`. -/
theorem hardy_coeff_add (e : ONote) (he : e ≠ 0) (m n : ℕ+) (x : ℕ) :
    hardy (oadd e (m + n) 0) x = hardy (oadd e m 0) (hardy (oadd e n 0) x) := by
  rw [hardy_single_coeff e he (m + n) x, hardy_single_coeff e he m,
    hardy_single_coeff e he n x, PNat.add_coe, Function.iterate_add_apply]

/-- **The additive-Hardy inequality** — for NF `e, β`: `H_{e+β}(x) ≤ H_e(H_β(x))`.
Lap 178 refuted the equality; this `≤` survives absorption and is P1's raised-control bridge
(`raise e α = e + ω^α`, then `hardy_omega_pow_lt_fastGrowing`). -/
theorem hardy_add_le_comp : ∀ (e : ONote), e.NF → ∀ (β : ONote), β.NF → ∀ x,
    hardy (e + β) x ≤ hardy e (hardy β x) := by
  intro e
  induction e with
  | zero =>
    intro _ β _ x
    simp [ONote.zero_add, hardy_zero]
  | oadd e₁ n₁ a₁ _ihe₁ iha₁ =>
    intro he β hβ x
    rcases eq_or_ne β 0 with rfl | hβ0
    · rw [show oadd e₁ n₁ a₁ + 0 = oadd e₁ n₁ a₁ from
          repr_inj.mp (by rw [repr_add, repr_zero, add_zero])]
      simp [hardy_zero]
    have he₁ : e₁.NF := he.fst
    have hba₁ : NFBelow a₁ e₁.repr := he.snd'
    have ha₁ : a₁.NF := ⟨⟨e₁.repr, hba₁⟩⟩
    obtain ⟨bβ, hbβ⟩ := hβ.out
    have hsNF : (a₁ + β).NF :=
      ⟨⟨max e₁.repr bβ,
        add_nfBelow (hba₁.mono (le_max_left _ _)) (hbβ.mono (le_max_right _ _))⟩⟩
    have hs0 : a₁ + β ≠ 0 := by
      intro h
      apply hβ0
      have : ONote.repr (a₁ + β) = 0 := by rw [h, repr_zero]
      rw [repr_add] at this
      exact repr_inj.mp (by rw [(Ordinal.add_eq_zero_iff.mp this).2, repr_zero])
    rw [oadd_add]
    cases hh : a₁ + β with
    | zero => exact absurd hh hs0
    | oadd e' n' a' =>
      have he'NF : e'.NF := (hh ▸ hsNF).fst
      cases hcmpc : e₁.cmp e' with
      | lt =>
        simp only [addAux, hcmpc]
        rw [← hh]
        calc hardy (a₁ + β) x
            ≤ hardy a₁ (hardy β x) := iha₁ ha₁ β hβ x
          _ ≤ hardy (oadd e₁ n₁ a₁) (hardy β x) := by
              rw [hardy_oadd_tail e₁ n₁ a₁ (hardy β x)]
              exact le_hardy (oadd e₁ n₁ 0) (hardy a₁ (hardy β x))
      | gt =>
        simp only [addAux, hcmpc]
        rw [← hh]
        calc hardy (oadd e₁ n₁ (a₁ + β)) x
            = hardy (oadd e₁ n₁ 0) (hardy (a₁ + β) x) := hardy_oadd_tail e₁ n₁ (a₁ + β) x
          _ ≤ hardy (oadd e₁ n₁ 0) (hardy a₁ (hardy β x)) := hardy_monotone _ (iha₁ ha₁ β hβ x)
          _ = hardy (oadd e₁ n₁ a₁) (hardy β x) := (hardy_oadd_tail e₁ n₁ a₁ (hardy β x)).symm
      | eq =>
        have hee : e₁ = e' := by
          have := @cmp_compares e₁ e' he₁ he'NF; rw [hcmpc] at this; exact this
        subst hee
        simp only [addAux, hcmpc]
        rcases eq_or_ne e₁ 0 with he₁0 | he₁0
        · subst he₁0
          have ha1z : a₁ = 0 := by
            cases a₁ with
            | zero => rfl
            | oadd e'' n'' a'' =>
                have hlt := NFBelow.lt hba₁; rw [repr_zero] at hlt
                exact absurd hlt not_lt_zero
          have ha'z : a' = 0 := by
            cases a' with
            | zero => rfl
            | oadd e'' n'' a'' =>
                have hlt := NFBelow.lt (hh ▸ hsNF).snd'; rw [repr_zero] at hlt
                exact absurd hlt not_lt_zero
          subst ha1z; subst ha'z
          have hβeq : β = oadd 0 n' 0 := by rw [← ONote.zero_add β]; exact hh
          rw [hβeq]
          rw [hardy_oadd0 (n₁ + n') x, hardy_oadd0 n₁, hardy_oadd0 n' x, PNat.add_coe]
          omega
        · have hcoeff : ∀ z, hardy (oadd e₁ (n₁ + n') a') z
              = hardy (oadd e₁ n₁ 0) (hardy (oadd e₁ n' a') z) := by
            intro z
            rw [hardy_oadd_tail e₁ (n₁ + n') a' z, hardy_oadd_tail e₁ n' a' z,
              hardy_coeff_add e₁ he₁0 n₁ n' (hardy a' z)]
          calc hardy (oadd e₁ (n₁ + n') a') x
              = hardy (oadd e₁ n₁ 0) (hardy (oadd e₁ n' a') x) := hcoeff x
            _ = hardy (oadd e₁ n₁ 0) (hardy (a₁ + β) x) := by rw [hh]
            _ ≤ hardy (oadd e₁ n₁ 0) (hardy a₁ (hardy β x)) := hardy_monotone _ (iha₁ ha₁ β hβ x)
            _ = hardy (oadd e₁ n₁ a₁) (hardy β x) := (hardy_oadd_tail e₁ n₁ a₁ (hardy β x)).symm

/-- **The additive-Hardy inequality at a principal raise** (`β = ω^α = oadd α 1 0`) — the exact P1
shape: `H_{e + ω^α}(x) ≤ H_e(H_{ω^α}(x))`. -/
theorem hardy_add_omega_pow_le {e α : ONote} (he : e.NF) (hα : α.NF) (x : ℕ) :
    hardy (e + oadd α 1 0) x ≤ hardy e (hardy (oadd α 1 0) x) :=
  hardy_add_le_comp e he (oadd α 1 0) (NF.oadd hα 1 NFBelow.zero) x

/-- Leading exponent of a notation's Cantor normal form (`0` for `0`). Companion to
`lastExp`; used to build a single `ω^Q` notation dominating a given `α`. -/
def lead : ONote → ONote
  | 0 => 0
  | oadd e _ _ => e

theorem lead_NF {o : ONote} (ho : o.NF) : (lead o).NF := by
  cases o with
  | zero => exact NF.zero
  | oadd e n a => exact ho.fst

/-- A notation is below `ω^(E+1)` whenever its leading exponent is `≤ E`. The basic
domination brick: any `α` sits below `ω^(osucc (lead α))`. -/
theorem repr_lt_omega_opow_succ {o E : ONote} (ho : o.NF) (hle : (lead o).repr ≤ E.repr) :
    o.repr < ω ^ (E.repr + 1) := by
  cases o with
  | zero => show (0 : ONote).repr < ω ^ (E.repr + 1); rw [repr_zero]; exact opow_pos _ omega0_pos
  | oadd e' c R =>
    have hle' : e'.repr ≤ E.repr := hle
    have hb : NFBelow (oadd e' c R) (e'.repr + 1) := ho.below_of_lt (lt_add_one _)
    refine lt_of_lt_of_le hb.repr_lt (opow_le_opow_right omega0_pos ?_)
    rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
    exact Order.succ_le_succ hle'

/-- Iterate-offset transfer: if `g y + 1 = F (y+1)` for all `y`, then `g^[m] y + 1 = F^[m] (y+1)`. -/
theorem iterate_offset {g F : ℕ → ℕ} (h : ∀ y, g y + 1 = F (y + 1)) (m y : ℕ) :
    g^[m] y + 1 = F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (g y), h y]

private theorem ofNat_succ_ne_zero (k : ℕ) : (ofNat (k + 1) : ONote) ≠ 0 := by
  rw [ofNat_succ]; intro h; exact ONote.noConfusion h

private theorem hardy_omega_pow_ofNat_succ (k x : ℕ) :
    hardy (oadd (ofNat (k + 1)) 1 0) x + 1 = fastGrowing (ofNat (k + 1)) (x + 1) := by
  induction k generalizing x with
  | zero =>
    show hardy (oadd 1 1 0) x + 1 = fastGrowing 1 (x + 1)
    rw [hardy_omega, fastGrowing_one]
    show 2 * x + 1 + 1 = 2 * (x + 1)
    omega
  | succ k ih =>
    rw [fastGrowing_succ _ (fundamentalSequence_ofNat_succ (k + 1)),
        hardy_limit _ (fundamentalSequence_omega_pow_succ (fundamentalSequence_ofNat_succ (k + 1)))]
    show hardy (oadd (ofNat (k + 1)) x.succPNat 0) x + 1
        = (fastGrowing (ofNat (k + 1)))^[x + 1] (x + 1)
    rw [hardy_oadd_coeff (ofNat (k + 1)) (ofNat_succ_ne_zero k) x x]
    exact iterate_offset ih (x + 1) x

/-- **B4 at finite levels: `H_{ω^k}(n) + 1 = f_k(n+1)`** for every `k : ℕ`. The classical Hardy↔
fast-growing identity `H_{ω^α} = f_α`, made precise under mathlib's `ω[n]=n+1` fundamental-sequence
convention — which shifts it by the `+1`/argument-bump seen here. (NB: the clean identity is special to
*finite/successor* exponents; at limit `α` the convention makes `H_{ω^α}` and `f_α` pick different
levels — e.g. `H_{ω^ω}(1)+1 = 8 ≠ f_ω(2) = 2048`.) Proof: induction on `k` from the `ω` base
(`hardy_omega`), the coefficient lemma turning `(ω^{k+1})[x] = ω^k·(x+1)` into `(H_{ω^k})^[x+1]`, and
`iterate_offset` carrying the `+1` through the iteration against `f_{k+1} = (f_k)^[·]`. -/
theorem hardy_omega_pow_ofNat (k x : ℕ) :
    hardy (oadd (ofNat k) 1 0) x + 1 = fastGrowing (ofNat k) (x + 1) := by
  cases k with
  | zero =>
    show hardy (oadd 0 1 0) x + 1 = fastGrowing 0 (x + 1)
    rw [show (oadd 0 1 0 : ONote) = 1 from rfl, hardy_one, fastGrowing_zero]
  | succ k => exact hardy_omega_pow_ofNat_succ k x

-- anti-vacuity: B4 at `ω^2` — `H_{ω^2}(2) + 1 = 23 + 1 = 24 = f_2(3)`
example : hardy (oadd (ofNat 2) 1 0) 2 + 1 = fastGrowing (ofNat 2) 3 := by native_decide

/-- **B4 at the first LIMIT level `ω^ω`:** `H_{ω^ω}(n) + 1 = f_{n+1}(n+1)`. Unlike finite `α`, the
clean `H_{ω^α}(n)+1 = f_α(n+1)` is FALSE at limit `α` (the `ω[n]=n+1` convention makes `H` and `f`
pick different tower levels); the TRUE limit form reads off the fundamental sequence:
`(ω^ω)[n] = ω^{n+1}`, so `H_{ω^ω}(n) = H_{ω^{n+1}}(n)` and finite B4 gives `f_{n+1}(n+1) − 1`. Note the
diagonal `n+1` argument — this is `f_{ε₀}`-flavoured (cf. `fastGrowingε₀`). Concrete witness that the
limit case is tractable with the right (non-`f_α(n+1)`) closed form. -/
theorem hardy_omega_pow_omega (n : ℕ) :
    hardy (oadd (oadd 1 1 0) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1) := by
  have hω : fundamentalSequence (oadd 1 1 0) = Sum.inr (fun i => ONote.ofNat (i + 1)) := rfl
  rw [hardy_limit _ (fundamentalSequence_omega_pow_limit hω)]
  show hardy (oadd (ofNat (n + 1)) 1 0) n + 1 = fastGrowing (ofNat (n + 1)) (n + 1)
  exact hardy_omega_pow_ofNat (n + 1) n

-- anti-vacuity: B4 at `ω^ω` — `H_{ω^ω}(1) + 1 = 7 + 1 = 8 = f_2(2)`
example : hardy (oadd (oadd 1 1 0) 1 0) 1 + 1 = fastGrowing (ofNat 2) 2 := by native_decide

/-- **Hardy is dominated by fast-growing at the same index.** For `n ≥ 2`,
`hardy o n ≤ fastGrowing o n` (no `NF` needed). By well-founded recursion on the notation, mirroring
`le_fastGrowing`: the limit case is the IH verbatim; the successor case chains
`H_o(n) = H_a(n+1) ≤ f_a(n+1) ≤ f_a(f_a n) = (f_a)^[2] n ≤ (f_a)^[n] n = f_o(n)` (IH at `a`, then
`f_a` monotone via `n+1 ≤ f_a n` from `lt_fastGrowing`, then iterate-count monotone for `n ≥ 2`).

The two hierarchies the expedition built are comparable: the Hardy hierarchy (the Goodstein-length
side, via the Cichoń identity `goodsteinLength m = H_{o_m}(2) − 2`) never outruns the fast-growing
hierarchy at the same ordinal index. A reusable bridge toward the matching *upper* bound and `B4`. -/
theorem hardy_le_fastGrowing (o : ONote) (n : ℕ) (hn : 2 ≤ n) :
    hardy o n ≤ fastGrowing o n := by
  rcases e : fundamentalSequence o with (_ | a) | f
  · rw [hardy_zero' o e, fastGrowing_zero' o e]; simp
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [hardy_succ o e, fastGrowing_succ o e]
    have ih : hardy a (n + 1) ≤ fastGrowing a (n + 1) := hardy_le_fastGrowing a (n + 1) (by omega)
    have hexp : (id : ℕ → ℕ) ≤ fastGrowing a := fun m => le_fastGrowing a m
    have hmono : (fastGrowing a)^[2] n ≤ (fastGrowing a)^[n] n :=
      Function.monotone_iterate_of_id_le hexp hn n
    have h2it : (fastGrowing a)^[2] n = fastGrowing a (fastGrowing a n) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; simp
    have hfn : n + 1 ≤ fastGrowing a n := lt_fastGrowing a (by omega)
    have hstep : fastGrowing a (n + 1) ≤ fastGrowing a (fastGrowing a n) := fastGrowing_monotone a hfn
    calc hardy a (n + 1) ≤ fastGrowing a (n + 1) := ih
      _ ≤ fastGrowing a (fastGrowing a n) := hstep
      _ = (fastGrowing a)^[2] n := h2it.symm
      _ ≤ (fastGrowing a)^[n] n := hmono
  · have hlt : f n < o := by
      have hp := fundamentalSequence_has_prop o; rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [hardy_limit o e, fastGrowing_limit o e]
    exact hardy_le_fastGrowing (f n) n hn
termination_by o
decreasing_by all_goals exact hlt

/-- Anti-vacuity for `hardy_le_fastGrowing` at a genuine limit: `H_ω(2) = 5 ≤ f_ω(2) = 2048`. -/
example : hardy (oadd 1 1 0) 2 ≤ fastGrowing (oadd 1 1 0) 2 := hardy_le_fastGrowing _ _ (by norm_num)

/-! ### B4 at an ARBITRARY (transfinite) exponent — the unconditional inequality `H_{ω^α}(n)+1 ≤ f_α(n+1)`

`hardy_omega_pow_ofNat`/`_omega` above give B4 as an *equality* at finite/successor exponents; at a
LIMIT exponent the equality degrades (the `ω[n]=n+1` convention makes `H` and `f` pick different
tower levels — e.g. `H_{ω^ω}(1)+1 = 8 ≠ f_ω(2) = 2048`). The UNCONDITIONAL, load-bearing truth,
proven here for *every* `α : ONote` by well-founded recursion, is the **inequality**

    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1)              -- H_{ω^α}(n) < f_α(n+1)

— exactly the E–W Lemma 19 upper bound the raised-control (P1) obligation needs: with the cut-elim
`raise e α' = e + ω^{α'}` in the absorbing regime, the raised control is `≈ hardy (ω^{α'})`, so this
bound reduces P1 to the fast-growing domination `fastGrowing α' ≤ (iterate of the input slot)`.
Pure Hardy/`fastGrowing` growth theory about the stable defs — calculus-independent. -/

/-! Faithfulness anchors — the exact `+1` shift and the falsity of the bare equality are kernel-checked. -/
example : hardy (oadd 0 1 0) 3 + 1 = fastGrowing 0 (3 + 1) := by native_decide
example : hardy (oadd 1 1 0) 3 + 1 = fastGrowing 1 (3 + 1) := by native_decide
example : hardy (oadd 2 1 0) 2 + 1 = fastGrowing 2 (2 + 1) := by native_decide
-- and the EQUALITY `H_{ω^α} = f_α` is FALSE (off by ≥1), so no lap re-attempts it:
example : hardy (oadd 1 1 0) 3 ≠ fastGrowing 1 3 := by native_decide

/-- **Coefficient composition, unconditional in `β`** (the non-absorbing equal-exponent additive
core): `H_{ω^β·(k+2)}(n) = H_{ω^β·(k+1)}(H_{ω^β}(n))`. For `β ≠ 0` this is the banked
`hardy_oadd_coeff_step`; for `β = 0` everything is finite (`oadd 0 m.succPNat 0 = ofNat (m+1)`,
`H_{ofNat c}(x) = x + c`). -/
theorem hardy_omega_pow_coeff_comp (β : ONote) (k n : ℕ) :
    hardy (oadd β (Nat.succPNat (k + 1)) 0) n
      = hardy (oadd β (Nat.succPNat k) 0) (hardy (oadd β 1 0) n) := by
  rcases eq_or_ne β 0 with hβ | hβ
  · subst hβ
    have e1 : oadd (0 : ONote) (Nat.succPNat (k + 1)) 0 = ofNat (k + 2) := (ofNat_succ (k + 1)).symm
    have e2 : oadd (0 : ONote) (Nat.succPNat k) 0 = ofNat (k + 1) := (ofNat_succ k).symm
    have e3 : oadd (0 : ONote) 1 0 = ofNat 1 := (ofNat_succ 0).symm
    rw [e1, e2, e3]
    simp only [hardy_ofNat]
    omega
  · exact hardy_oadd_coeff_step β hβ k n

/-- **The coefficient intermediate** (the classical Cichoń–Wainer core), parametrized by the
exponent-`β` base bound `hbase` (supplied by the outer IH in the successor case):
`H_{ω^β·(m+1)}(n) + 1 ≤ f_β^{[m+1]}(n+1)`. Induction on the coefficient `m`: base `m=0` is `hbase`;
the step composes via `hardy_omega_pow_coeff_comp` + the IH + iterate-monotonicity. -/
theorem hardy_omega_pow_coeff_le {β : ONote}
    (hbase : ∀ n, hardy (oadd β 1 0) n + 1 ≤ fastGrowing β (n + 1)) :
    ∀ (m n : ℕ), hardy (oadd β (Nat.succPNat m) 0) n + 1 ≤ (fastGrowing β)^[m + 1] (n + 1) := by
  intro m
  induction m with
  | zero =>
      intro n
      show hardy (oadd β 1 0) n + 1 ≤ fastGrowing β (n + 1)
      exact hbase n
  | succ m ih =>
      intro n
      rw [hardy_omega_pow_coeff_comp β m n]
      have h2 : hardy (oadd β 1 0) n + 1 ≤ fastGrowing β (n + 1) := hbase n
      calc hardy (oadd β (Nat.succPNat m) 0) (hardy (oadd β 1 0) n) + 1
          ≤ (fastGrowing β)^[m + 1] (hardy (oadd β 1 0) n + 1) := ih _
        _ ≤ (fastGrowing β)^[m + 1] (fastGrowing β (n + 1)) :=
            (fastGrowing_monotone β).iterate (m + 1) h2
        _ = (fastGrowing β)^[m + 1 + 1] (n + 1) :=
            (Function.iterate_succ_apply (fastGrowing β) (m + 1) (n + 1)).symm

/-- **B4 upper bound at an arbitrary exponent `α`** — `H_{ω^α}(n) + 1 ≤ f_α(n+1)`, unconditional.
Well-founded recursion on `α`: `α = 0` is the equality; `α` a successor exponent reduces to the
coefficient intermediate `hardy_omega_pow_coeff_le` at the IH; `α` a limit uses the IH plus
`fastGrowing` index-monotonicity across the fundamental sequence. -/
theorem hardy_omega_pow_add_one_le (α : ONote) : ∀ n : ℕ,
    hardy (oadd α 1 0) n + 1 ≤ fastGrowing α (n + 1) := by
  haveI : WellFoundedLT ONote := ⟨InvImage.wf repr Ordinal.lt_wf⟩
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro n
    rcases hα : fundamentalSequence α with (_ | β) | f
    · have h0 : α = 0 := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact hp
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [hardy_succ (oadd 0 1 0) hfs1, hardy_zero, fastGrowing_zero]
      simp only [id_eq]; omega
    · have hlt : β < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp
        rw [lt_def, hp.1]; exact Order.lt_succ _
      have homega : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd β i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ hα
      rw [hardy_limit (oadd α 1 0) homega, fastGrowing_succ α hα]
      exact hardy_omega_pow_coeff_le (ih β hlt) n n
    · have hlim_h : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit hα
      have hlt : f n < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact (hp.2.1 n).2.1
      rw [hardy_limit (oadd α 1 0) hlim_h, fastGrowing_limit α hα]
      calc hardy (oadd (f n) 1 0) n + 1
          ≤ fastGrowing (f n) (n + 1) := ih (f n) hlt n
        _ ≤ fastGrowing (f (n + 1)) (n + 1) :=
            fastGrowing_le_of_reaches (Nat.succ_le_succ (Nat.zero_le n))
              (fastGrowing_bachmann_reach hα n)

/-- **The P1 corollary:** `H_{ω^α}(n) < f_α(n+1)`, the strict upper bound the raised-control
obligation consumes, from the `+1 ≤` form. -/
theorem hardy_omega_pow_lt_fastGrowing (α : ONote) (n : ℕ) :
    hardy (oadd α 1 0) n < fastGrowing α (n + 1) := by
  have h := hardy_omega_pow_add_one_le α n
  omega

-- anti-vacuity at a genuine LIMIT exponent (where the bare equality is false): `H_{ω^ω}(1) = 7 < f_ω(2)`.
example : hardy (oadd (oadd 1 1 0) 1 0) 1 < fastGrowing (oadd 1 1 0) 2 :=
  hardy_omega_pow_lt_fastGrowing (oadd 1 1 0) 1

/-- Pointwise domination lifts to iterates: `F ≤ g` pointwise and `g` monotone ⟹ `F^[m] ≤ g^[m]`. -/
private theorem iterate_le_iterate_of_le {F g : ℕ → ℕ} (hFg : ∀ y, F y ≤ g y)
    (hg : Monotone g) (m x : ℕ) : F^[m] x ≤ g^[m] x := by
  induction m generalizing x with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (F x)) (hg.iterate m (hFg x))

/-- **B4 LOWER bound at an arbitrary exponent `α`** — `f_α(n) ≤ H_{ω^α}(n)`, unconditional. The
matching *lower* half of `hardy_omega_pow_add_one_le`: together they bracket
`f_α(n) ≤ H_{ω^α}(n) < f_α(n+1)` (see `hardy_omega_pow_bracket`), the two-sided E–W Lemma 19
sandwich of the Hardy hierarchy by the fast-growing hierarchy at `ω^α`. Well-founded recursion on
`α`: `α = 0` is `n+1 = n+1`; `α` a limit is the IH verbatim (both sides pick index `α[n]` at
argument `n`); `α = β+1` reduces via `hardy_oadd_coeff` to the iterate domination
`(f_β)^[n](n) ≤ (H_{ω^β})^[n](n) ≤ (H_{ω^β})^[n+1](n)` (IH pointwise + `hardy_monotone` + `le_hardy`). -/
theorem fastGrowing_le_hardy_omega_pow (α : ONote) : ∀ n : ℕ,
    fastGrowing α n ≤ hardy (oadd α 1 0) n := by
  haveI : WellFoundedLT ONote := ⟨InvImage.wf repr Ordinal.lt_wf⟩
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro n
    rcases hα : fundamentalSequence α with (_ | β) | f
    · have h0 : α = 0 := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact hp
      subst h0
      have hfs1 : fundamentalSequence (oadd 0 1 0) = Sum.inl (some 0) := rfl
      rw [fastGrowing_zero, hardy_succ (oadd 0 1 0) hfs1, hardy_zero]
      simp only [id_eq]; omega
    · have hlt : β < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp
        rw [lt_def, hp.1]; exact Order.lt_succ _
      have homega : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd β i.succPNat 0) :=
        fundamentalSequence_omega_pow_succ hα
      rw [fastGrowing_succ α hα, hardy_limit (oadd α 1 0) homega]
      show (fastGrowing β)^[n] n ≤ hardy (oadd β n.succPNat 0) n
      rcases eq_or_ne β 0 with hβ0 | hβ0
      · subst hβ0
        rw [fastGrowing_zero, show oadd (0 : ONote) n.succPNat 0 = ofNat (n + 1) from (ofNat_succ n).symm,
          hardy_ofNat, Nat.succ_iterate]
        omega
      · rw [hardy_oadd_coeff β hβ0 n n]
        have hFg : ∀ y, fastGrowing β y ≤ hardy (oadd β 1 0) y := ih β hlt
        have hg : Monotone (hardy (oadd β 1 0)) := hardy_monotone _
        calc (fastGrowing β)^[n] n
            ≤ (hardy (oadd β 1 0))^[n] n := iterate_le_iterate_of_le hFg hg n n
          _ ≤ (hardy (oadd β 1 0))^[n + 1] n := by
              rw [Function.iterate_succ_apply']; exact le_hardy (oadd β 1 0) _
    · have hlim : fundamentalSequence (oadd α 1 0) = Sum.inr (fun i => oadd (f i) 1 0) :=
        fundamentalSequence_omega_pow_limit hα
      have hlt : f n < α := by
        have hp := fundamentalSequence_has_prop α; rw [hα] at hp; exact (hp.2.1 n).2.1
      rw [fastGrowing_limit α hα, hardy_limit (oadd α 1 0) hlim]
      exact ih (f n) hlt n

/-- **The two-sided E–W Lemma 19 bracket at `ω^α`:** `f_α(n) ≤ H_{ω^α}(n) < f_α(n+1)`, unconditional
over every `α : ONote`. The Hardy hierarchy is sandwiched between consecutive fast-growing values —
`H_{ω^α}` sits within one `f_α`-step of `f_α`. Combines `fastGrowing_le_hardy_omega_pow` (lower) and
`hardy_omega_pow_lt_fastGrowing` (upper). -/
theorem hardy_omega_pow_bracket (α : ONote) (n : ℕ) :
    fastGrowing α n ≤ hardy (oadd α 1 0) n ∧ hardy (oadd α 1 0) n < fastGrowing α (n + 1) :=
  ⟨fastGrowing_le_hardy_omega_pow α n, hardy_omega_pow_lt_fastGrowing α n⟩

/-- **Coefficient-general lower bound:** `(f_α)^[k+1](n) ≤ H_{ω^α·(k+1)}(n)` (for `α ≠ 0`).
The `hardy_oadd_coeff` companion of the `ω^α` lower bracket: `H_{ω^α·(k+1)} = (H_{ω^α})^[k+1]`
dominates `(f_α)^[k+1]` because `f_α ≤ H_{ω^α}` pointwise and `H_{ω^α}` is monotone. -/
theorem fastGrowing_iterate_le_hardy_coeff (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    (fastGrowing α)^[k + 1] n ≤ hardy (oadd α k.succPNat 0) n := by
  rw [hardy_oadd_coeff α hα k n]
  exact iterate_le_iterate_of_le (fastGrowing_le_hardy_omega_pow α) (hardy_monotone _) (k + 1) n

/-- Inequality iterate-offset: if `g y + 1 ≤ F (y+1)` for all `y` and `F` is monotone, the `+1`
carries through the iteration one extra argument step: `g^[m] y + 1 ≤ F^[m] (y+1)`. The `≤`
generalization of `iterate_offset` (which needs the exact equality). -/
private theorem iterate_offset_le {g F : ℕ → ℕ} (hF : Monotone F) (h : ∀ y, g y + 1 ≤ F (y + 1))
    (m y : ℕ) : g^[m] y + 1 ≤ F^[m] (y + 1) := by
  induction m generalizing y with
  | zero => exact le_rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact le_trans (ih (g y)) (hF.iterate m (h y))

/-- **Coefficient-general upper bound:** `H_{ω^α·(k+1)}(n) + 1 ≤ (f_α)^[k+1](n+1)` (for `α ≠ 0`).
The `hardy_oadd_coeff` companion of the `ω^α` upper bound: `H_{ω^α·(k+1)} = (H_{ω^α})^[k+1]`, and the
`+1` shift `H_{ω^α}(y)+1 ≤ f_α(y+1)` carries through `k+1` iterations via `iterate_offset_le`. -/
theorem hardy_coeff_add_one_le (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    hardy (oadd α k.succPNat 0) n + 1 ≤ (fastGrowing α)^[k + 1] (n + 1) := by
  rw [hardy_oadd_coeff α hα k n]
  exact iterate_offset_le (fastGrowing_monotone α) (hardy_omega_pow_add_one_le α) (k + 1) n

/-- **The coefficient-general two-sided bracket:** `(f_α)^[k+1](n) ≤ H_{ω^α·(k+1)}(n) < (f_α)^[k+1](n+1)`
(for `α ≠ 0`). The `hardy_oadd_coeff`-lifted form of `hardy_omega_pow_bracket`: the Hardy hierarchy at
`ω^α·(k+1)` is sandwiched between consecutive values of the `(k+1)`-fold iterate of `f_α`. -/
theorem hardy_omega_pow_coeff_bracket (α : ONote) (hα : α ≠ 0) (k n : ℕ) :
    (fastGrowing α)^[k + 1] n ≤ hardy (oadd α k.succPNat 0) n
      ∧ hardy (oadd α k.succPNat 0) n < (fastGrowing α)^[k + 1] (n + 1) :=
  ⟨fastGrowing_iterate_le_hardy_coeff α hα k n,
    Nat.lt_of_succ_le (hardy_coeff_add_one_le α hα k n)⟩

/-! ### The ε₀-diagonal capstone

`fastGrowingε₀ i = f_{tower i}(i)` and `tower (i+1) = ω^{tower i}` (`tower_succ`), so the `ω^α`
bracket at `α = tower i`, argument `i`, pins the ε₀-diagonal against the Hardy function at the next
tower level. This is the `ε₀`-tier reading of the E–W Lemma 19 comparison — the level at which the
Goodstein length function itself lives (`goodsteinLength` tracks `H_{ε₀}`). -/

/-- **The ε₀ diagonal is dominated by Hardy at the tower:** `fastGrowingε₀ i ≤ H_{tower(i+1)}(i)`.
Directly the lower `ω^α` bracket at `α = tower i`, argument `i`, using `tower(i+1) = ω^{tower i}`. -/
theorem fastGrowingε₀_le_hardy_tower_succ (i : ℕ) :
    fastGrowingε₀ i ≤ hardy (tower (i + 1)) i := by
  have h : fastGrowing (tower i) i ≤ hardy (oadd (tower i) 1 0) i :=
    (hardy_omega_pow_bracket (tower i) i).1
  rw [← tower_succ] at h
  exact h

/-- **The matching ε₀-diagonal upper bound:** `H_{tower(i+1)}(i) < f_{tower i}(i+1)` — Hardy at the
next tower level is under the previous diagonal level at the bumped argument. The upper `ω^α` bracket
at `α = tower i`. Together with `fastGrowingε₀_le_hardy_tower_succ` this brackets `H_{tower(i+1)}(i)`
strictly between `fastGrowingε₀ i` and `f_{tower i}(i+1)`. -/
theorem hardy_tower_succ_lt_fastGrowing (i : ℕ) :
    hardy (tower (i + 1)) i < fastGrowing (tower i) (i + 1) := by
  have h := (hardy_omega_pow_bracket (tower i) i).2
  rw [← tower_succ] at h
  exact h

end GoodsteinPA.FastGrowing
