module

public import GoodsteinPA.OperatorZinfty.InductionLeaf
public import GoodsteinPA.ToMathlib.FastGrowing.EWIteration

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

variable {f : ℕ → ℕ} {e : ONote} {m : ℕ}

/-! ## The f-slot elimination suite

The number-theoretic operator slot `f : ℕ → ℕ` is what a plain numeric stage counter cannot be:
the ℕ-stage judgment `Zeh` cannot carry the running-family reduction
(`principal_witness_exceeds_stage`: the `exI` witness `n ≤ hardy e m > m` cannot be lowered to
the output stage).  The fix is the function-slot judgment `Zef`: the ℕ-stage `m` is replaced by
the slot `f`, and the running-family reduction (`cutReduceAllAuxRunning_Zf`) and step motive
(`stepAllω_Zf`) are discharged there as real theorems.  The f-slot enters the elimination
lemmas as:

* **composition at principal cuts** — the reduction's output slot is `f ∘ g` of the premises';
* **max-relativization at ω-nodes** — `rel1 f n = fun x => f (max n x)`;
* **`hardy e` at the root** — `NormControlled` collapses to `hardy e` when `m = 0`.

The reduction/step statements stay at FIXED control with the composed slot; ALL ordinal collapse
and numeric iteration is confined to the (unfinished) rank-lowering pass `cutElimPass_Zf`, where
the control `e` is untouched — the ordinal collapses (`collapse α`) and the slot iterates
(`iterSlot f α`).

- [EW12, Definition 23, Lemma 25, Lemma 27]
-/

/-- **Norm control** (the number-theoretic operator bound, tied to the `(e, m)` axis):
`f` dominates the Hardy witness bound at every relativization depth.  `hardy e` is the root
instantiation (`normControlled_root`); the ω-node re-entry is `normControlled_rel1`.

- [EW12, Definition 23]
- [BW87, p. 181]
-/
def NormControlled (f : ℕ → ℕ) (e : ONote) (m : ℕ) : Prop :=
  ∀ x, hardy e (max m x) ≤ f x

/-- **Root instantiation**: `hardy e` controls the stage-0 axis. -/
lemma normControlled_root (e : ONote) : NormControlled (fun x => hardy e x) e 0 := by
  intro x; simp

/-- **Seam 2 in controlled form — the ω-node re-entry** (real proof): a controlled slot,
relativized at branch `n` and run at the max-adjoined stage, is controlled by `rel1 f n`.
This is `rel1_comp`'s semantic payload: the branch-unbounded demand that overflowed every
`Provable` `d`-slot re-enters through ONE function slot's relativization. -/
lemma normControlled_rel1 (h : NormControlled f e m)
    (n : ℕ) : NormControlled (rel1 f n) e (max m n) := by
  intro x
  have hx := h (max n x)
  have he : max m (max n x) = max (max m n) x := by omega
  rw [he] at hx
  simpa [rel1] using hx

/-- Norm control is monotone in the slot (assembly plumbing: a dominating slot still
controls; reused when a reduction outputs a larger-than-needed composed slot). -/
lemma NormControlled.mono {f'}
    (h : NormControlled f e m) (hff' : ∀ x, f x ≤ f' x) : NormControlled f' e m :=
  fun x => le_trans (h x) (hff' x)

/-- Norm control is antitone in the stage: a slot controlling stage `m` controls any
smaller stage `m' ≤ m` (the `exI` bound only shrinks).  Reused when the reduction runs a
premise at a lower stage than the conclusion. -/
lemma NormControlled.stage_antitone {m'}
    (h : NormControlled f e m) (hm : m' ≤ m) : NormControlled f e m' :=
  fun x => le_trans (hardy_monotone e (by omega)) (h x)

/-- **Composition preserves control at a fixed control** (the numeric update `f ↦ f∘g` at the
*same* control, [EW12, Lemma 25]).  If `g` controls `e` at `m` and `f` is inflationary
(condition `(f.1)`: `2y+1 ≤ f y ⟹ y ≤ f y`), then the composed slot `f ∘ g` still controls `e`
at `m`.  Note: this is the *fixed*-control fact; the *raised*-control demand belongs to
`cutElimPass_Zf`'s pinned iterate, not here. -/
lemma NormControlled.comp {g}
    (hg : NormControlled g e m) (hf : ∀ y, y ≤ f y) : NormControlled (f ∘ g) e m :=
  fun x => le_trans (hg x) (hf (g x))

/-- **The reduction's composed-slot conjunct** (`NormControlled (f∘g) e m`, at fixed control).
From `g` controlled at any stage `m₀` and `f` controlled at the output stage `m`, the composed
slot `f ∘ g` is controlled at `m`.  Unlike `NormControlled.comp` this needs no separate
inflationarity hypothesis on `f`: control of `g` already forces `g` inflationary
(`x ≤ max m₀ x ≤ hardy e (max m₀ x) ≤ g x`, via `le_hardy`), and then
`f (g x) ≥ hardy e (max m (g x)) ≥ hardy e (max m x)` (`hf` at `g x`, `hardy_monotone`). -/
lemma normControlled_comp_running {g} {m₀}
    (hg : NormControlled g e m₀) (hf : NormControlled f e m) : NormControlled (f ∘ g) e m := by
  intro x
  have hxg : x ≤ g x :=
    le_trans (le_trans (le_max_right m₀ x) (le_hardy e (max m₀ x))) (hg x)
  exact le_trans (hardy_monotone e (max_le_max (le_refl m) hxg)) (hf (g x))

/-- **Kernel witness for the stage-`m` reduction gap.**  A stage-`m` reduction has a
principal-`exI` case where the witness satisfies only `n ≤ hardy e m`, which strictly exceeds
the stage `m` at any nontrivial control — e.g. `hardy ω m = 2m+1 > m`.  So `n ≤ hardy e m` does
not give `n ≤ m`, and the family member `fam n` (stage `max m₀ n`) cannot be lowered to the
output stage `m` (`Zeh` has no stage-lowering rule). -/
lemma principal_witness_exceeds_stage (m : ℕ) : m < hardy ONote.omega m := by
  rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]; omega

/-! ## The numeric-slot iterate bricks ([EW12, Definition 16] carriers)

`Function.iterate` (`f^[k]`) is the `k`-fold composition; it preserves exactly the operator
conditions the reduction threads (monotone, inflationary, `NormControlled`) and composes to
iterates (`iter_comp`: counts add — the `∃`-cut lane).  These are the numeric carrier the
ordinal-indexed iterate `iterSlot` (below) is built on.

- [EW12, Definition 16]
-/

/-- The iterate is monotone if `f` is. -/
lemma iter_monotone (hf : Monotone f) (k : ℕ) : Monotone f^[k] := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => rw [Function.iterate_succ]; exact ih.comp hf

/-- The iterate is inflationary if `f` is. -/
lemma iter_infl (hf : ∀ x, x ≤ f x) (k x : ℕ) : x ≤ f^[k] x := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [Function.iterate_succ']
      exact le_trans ih (hf _)

/-- The iterate preserves `NormControlled` (for `k ≥ 1`): `f^[k+1] x ≥ f x ≥ hardy e (max m x)`,
via `f^[k]` inflationary. -/
lemma iter_normControlled
    (hf : NormControlled f e m) (hf_infl : ∀ x, x ≤ f x) (k : ℕ) :
    NormControlled f^[k + 1] e m := by
  intro x
  rw [Function.iterate_succ, Function.comp_apply]
  exact le_trans (hf x) (iter_infl hf_infl k (f x))

/-- Iterate monotone in the index count: `f^[j] ≤ f^[k]` pointwise for `j ≤ k`, `f` inflationary +
monotone.  Feeds `mono_f` when a pass outputs a longer iterate than a sibling branch needs. -/
lemma iter_le_of_le (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    {j k} (hjk : j ≤ k) (x : ℕ) : f^[j] x ≤ f^[k] x := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hjk
  rw [Function.iterate_add_apply]
  exact iter_monotone hf_mono j (iter_infl hf_infl d x)

/-- **Iterates compose to iterates** (`f^[j] ∘ f^[k] = f^[j+k]`) — the numeric core of the
`∃`-cut lane: composing two premise iterates of the same base adds the counts, so the slot
stays `f^[·]`. -/
lemma iter_comp (f : ℕ → ℕ) (j k : ℕ) : f^[j] ∘ f^[k] = f^[j + k] :=
  (Function.iterate_add f j k).symm

/-! ## The collapse and the ordinal-indexed iterate

Relating a rank-`c+1` derivation to a rank-`c` one needs collapsing the ordinal and iterating
the slot.  Two explicit `ONote`-grounded definitions:

- `collapse α := ω^α` (`expTower`) — one rank-collapsing step; iterated `c` times it is the
  rank-lowering tower `Ω_c(α) = Ω^{Ω_{c-1}(α)}`.  NF-preserving + strictly monotone (the descent
  the collapse induction needs) — both proven below, reusing `expTower_NF`/`expTower_lt_expTower`.
- `iterSlot f α` — the **diagonalizing** ordinal-indexed iterate.  Its ROLE matches
  [EW12, Definition 16]'s `f^α`, but its IMPLEMENTATION differs: [EW12]'s `f^α` is a norm-bounded
  transfinite recursion, whereas `iterSlot` is defined by the same fundamental-sequence recursion
  as this repo's `hardy` — a Hardy-style variant [BW87, p. 181]: base `iterSlot f 0 = f`,
  successor `iterSlot f (a+1) n = iterSlot f a (f n)`, limit `iterSlot f λ n = iterSlot f (λ[n]) n`.
  On finite ordinals it agrees with the fixed-count form (`iterSlot f (ofNat k) = f^[k+1]`); at
  limits it diagonalizes — the branch index rides the numeric argument, which `rel1` raises
  (`rel1 (iterSlot f α) n` evaluates the ordinal index at `α[max n x]`-stages, absorbing
  branch-growing budgets).

**Why `iterSlot` must diagonalize.**  A fixed-count definition `iterSlot f α := f^[norm α + 1]`
is refuted at the `allω` reassembly: the branch `n` needs output slot `(rel1 f n)^[norm (β n) + 1]`
while the parent forces branch slot `rel1 (f^[norm α + 1]) n`; `Zef.mono_f` only raises slots, so
reassembly needs `(rel1 f n)^[norm (β n) + 1] ≤ rel1 (f^[norm α + 1]) n` pointwise.  Counterexample
at `α = ω`, `β 2 = ofNat 2`, `f = hardy ω`, `x = 0`: parent side `f^[2] 2 = 11 < 23 = (rel1 f 2)^[3] 0`.
Root cause: `norm` is not monotone along `<` (`norm (ofNat n) = n` grows along ω's fundamental
sequence while `norm ω = 1`), so no fixed ℕ-count read off the parent ordinal dominates the
branches — the diagonalization is forced.

- [EW12, Definition 16]
- [BW87, p. 181]
-/

/-- **`iterSlot`** — the diagonalizing ordinal-indexed numeric-slot iterate.  Its role matches
[EW12, Definition 16]'s `f^α`, but its implementation is a Hardy-style fundamental-sequence
variant [BW87, p. 181]: `iterSlot f 0 = f`; `iterSlot f (a+1) n = iterSlot f a (f n)`;
`iterSlot f λ n = iterSlot f (λ[n]) n` (limit, via `ONote.fundamentalSequence`).  Same well-founded
recursion as `hardy`; `hardy` is `iterSlot` of the successor, up to the base case. -/
def iterSlot (f : ℕ → ℕ) : ONote → ℕ → ℕ
  | o =>
    match fundamentalSequence o, fundamentalSequence_has_prop o with
    | Sum.inl none, _ => f
    | Sum.inl (some a), h =>
      have : a < o := by rw [lt_def, h.1]; exact Order.lt_succ _
      fun n => iterSlot f a (f n)
    | Sum.inr fs, h => fun n =>
      have : fs n < o := (h.2.1 n).2.1
      iterSlot f (fs n) n
  termination_by o => o

/-- Unfolding lemma for `iterSlot`, mirroring `hardy_def`. -/
lemma iterSlot_def (f : ℕ → ℕ) {o : ONote} {x} (e : fundamentalSequence o = x) :
    iterSlot f o =
      match
        (motive := (x : Option ONote ⊕ (ℕ → ONote)) → FundamentalSequenceProp o x → ℕ → ℕ)
        x, e ▸ fundamentalSequence_has_prop o with
      | Sum.inl none, _ => f
      | Sum.inl (some a), _ => fun n => iterSlot f a (f n)
      | Sum.inr fs, _ => fun n => iterSlot f (fs n) n := by
  subst x
  rw [iterSlot]

/-- `iterSlot f o = f` when `o = 0` (the `inl none` branch). -/
lemma iterSlot_zero' (f : ℕ → ℕ) (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    iterSlot f o = f := by
  rw [iterSlot_def f h]

/-- `iterSlot f o n = iterSlot f a (f n)` when `o` is the successor of `a`. -/
lemma iterSlot_succ (f : ℕ → ℕ) (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    iterSlot f o = fun n => iterSlot f a (f n) := by
  rw [iterSlot_def f h]

/-- `iterSlot f o n = iterSlot f (o[n]) n` when `o` is a limit with fundamental sequence `fs`. -/
lemma iterSlot_limit (f : ℕ → ℕ) (o) {fs} (h : fundamentalSequence o = Sum.inr fs) :
    iterSlot f o = fun n => iterSlot f (fs n) n := by
  rw [iterSlot_def f h]

/-- **`iterSlot f α` is inflationary** if `f` is (slot stays inflationary through the pass).
Mirrors `le_hardy`. -/
lemma iterSlot_infl (hf_infl : ∀ x, x ≤ f x) (o : ONote) (n : ℕ) : n ≤ iterSlot f o n := by
  rcases e : fundamentalSequence o with (_ | a) | fs
  · rw [iterSlot_zero' f o e]; exact hf_infl n
  · have hlt : a < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [iterSlot_succ f o e]
    exact le_trans (hf_infl n) (iterSlot_infl hf_infl a (f n))
  · have hlt : fs n < o := by
      have hp := fundamentalSequence_has_prop o
      rw [e] at hp
      exact (hp.2.1 n).2.1
    rw [iterSlot_limit f o e]
    exact iterSlot_infl hf_infl (fs n) n
termination_by o
decreasing_by all_goals exact hlt

/-- **Value transfer for `iterSlot`** (mirror of `hardy_le_of_reaches`, base `f`).  If `β`
structurally reaches `α` at budget `x`, and *every* notation `β` reaches has a monotone slot
iterate, then `iterSlot f α x ≤ iterSlot f β x`.  Unlike the fast-growing transfer, the successor
step `iterSlot f β x = iterSlot f γ (f x)` shifts the argument from `x` to `f x`; that shift is
absorbed by inflationarity (`x ≤ f x`, `hf_infl`) plus monotonicity of the intermediate
`iterSlot f γ` — the exact analog of `hardy_le_of_reaches`'s `Nat.le_succ` absorption. -/
lemma iterSlot_le_of_reaches (hf_infl : ∀ x, x ≤ f x) {x} {β α}
    (h : Reaches x β α) (hmono : ∀ γ, Reaches x β γ → Monotone (iterSlot f γ)) :
    iterSlot f α x ≤ iterSlot f β x := by
  induction h with
  | refl a => exact le_rfl
  | @succ β γ α hb _ ih =>
      have hmγ : Monotone (iterSlot f γ) := hmono γ (Reaches.succ hb (Reaches.refl γ))
      have ihγ : iterSlot f α x ≤ iterSlot f γ x := ih (fun δ hδ => hmono δ (Reaches.succ hb hδ))
      have heq : iterSlot f β x = iterSlot f γ (f x) := by rw [iterSlot_succ f _ hb]
      rw [heq]; exact le_trans ihγ (hmγ (hf_infl x))
  | @limit β α g hb _ ih =>
      have ihg : iterSlot f α x ≤ iterSlot f (g x) x :=
        ih (fun δ hδ => hmono δ (Reaches.limit hb hδ))
      have heq : iterSlot f β x = iterSlot f (g x) x := by rw [iterSlot_limit f _ hb]
      rw [heq]; exact ihg

/-- **`iterSlot f α` is monotone** for `f` monotone + inflationary.
Mirrors `hardy_monotone`: zero case is `hf_mono`, successor threads the IH through `f`'s
monotonicity, and the limit case combines monotonicity of `iterSlot f (α[n])` (IH) with the index
step `iterSlot f (α[n])(n+1) ≤ iterSlot f (α[n+1])(n+1)` = `iterSlot_le_of_reaches` on the
structural Bachmann reach `fastGrowing_bachmann_reach` (every intermediate is `< α`, so the IH
supplies its monotonicity). -/
lemma iterSlot_monotone (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    (α : ONote) : Monotone (iterSlot f α) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases e : fundamentalSequence α with (_ | a) | fs
  · rw [iterSlot_zero' f α e]; exact hf_mono (Nat.le_succ n)
  · have hlt : a < α := by
      have hp := fundamentalSequence_has_prop α; rw [e] at hp
      rw [lt_def, hp.1]; exact Order.lt_succ _
    rw [iterSlot_succ f α e]
    exact iterSlot_monotone hf_mono hf_infl a (hf_mono (Nat.le_succ n))
  · have hlt : fs n < α := by
      have hp := fundamentalSequence_has_prop α; rw [e] at hp
      exact (hp.2.1 n).2.1
    have hltn1 : fs (n + 1) < α := by
      have hp := fundamentalSequence_has_prop α; rw [e] at hp
      exact (hp.2.1 (n + 1)).2.1
    rw [iterSlot_limit f α e]
    have mono_fn : Monotone (iterSlot f (fs n)) := iterSlot_monotone hf_mono hf_infl (fs n)
    have step : iterSlot f (fs n) (n + 1) ≤ iterSlot f (fs (n + 1)) (n + 1) := by
      apply iterSlot_le_of_reaches hf_infl (fastGrowing_bachmann_reach e n)
      intro γ hγ
      have hγα : γ < α := lt_of_le_of_lt (reaches_le hγ) hltn1
      exact iterSlot_monotone hf_mono hf_infl γ
    exact le_trans (mono_fn (Nat.le_succ n)) step
termination_by α
decreasing_by
  · exact hlt
  · exact hlt
  · exact hγα

/-- **`iterSlot f 0 = f`** — the α = 0 (cut-free axiom) case leaves the slot unchanged. -/
lemma iterSlot_zero (f : ℕ → ℕ) : iterSlot f 0 = f :=
  iterSlot_zero' f 0 rfl

/-- **Budgeted ordinal-monotonicity of `iterSlot`** (mirror of `hardy_le_of_lt`): for `β < α`
(both NF) and a budget `x ≥ norm β`, `iterSlot f β x ≤ iterSlot f α x`.  Composes
`reaches_of_lt` (the general Bachmann reachability `Reaches x α β`) with `iterSlot_le_of_reaches`
(value transfer) and `iterSlot_monotone` (the per-notation monotonicity).

`iterSlot f ·` is not ordinal-monotone at a fixed small argument, but it is monotone once the
argument reaches the `norm`-budget of the smaller ordinal.  So any output slot whose read is
node-relative (argument `≥ norm` of the node's ordinal — e.g. a relativized
`rel1 (iterSlot f α) K` with `K ≥ norm α`) restores the `weak`/`exI`/`cut` slot-lift that the bare
`iterSlot f α` cannot supply. -/
lemma iterSlot_le_of_lt (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    {x} {α β} (hα : α.NF) (hβ : β.NF) (hβα : β < α) (hnorm : norm β ≤ x) :
    iterSlot f β x ≤ iterSlot f α x :=
  iterSlot_le_of_reaches hf_infl (reaches_of_lt α hα β hβ hβα hnorm)
    (fun γ _ => iterSlot_monotone hf_mono hf_infl γ)

end GoodsteinPA.OperatorZeh
