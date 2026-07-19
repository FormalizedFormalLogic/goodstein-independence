module

public import GoodsteinPA.OperatorZinfty
public import GoodsteinPA.ToMathlib.FastGrowing.EWIteration

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## §5 The f-slot elimination suite (A2 — LOCK §3/§6; pins 1–2 DISCHARGED in §7, pin 3 `sorry`)

The Eguchi–Weiermann number-theoretic operator slot `f : ℕ → ℕ` (arXiv:1205.2879, Def. 23 +
Lemma 25) is what the `(k,d)` counter could never be (SPIKE-W4B: both seams are ℕ-slot
overflow failures; SPIKE-Z1 §6: the non-affine function-slot absorbs both).

**LOCK §1-A1/§3 amendment (RATIFIED lap 184, `REBUILD-Z-LAP4-RATIFICATION-2026-07-02.md`):** the
draft kept the ℕ-stage judgment `Zeh` f-free with the slot only in the elimination *statements*,
but laps 2–3 proved in-kernel that the ℕ-stage `Zeh` **cannot** carry the running-family reduction
(`principal_witness_exceeds_stage`: the `exI` witness `n ≤ hardy e m > m` cannot be lowered to the
output stage — the exact ℕ-budget failure LOCK R4 forbids).  The fix is the R4-compliant
function-slot judgment `Zef` (§7): the ℕ-stage `m` is replaced by the slot `f`.  Pins 1–2
(`cutReduceAllAuxRunning_Zf`, `stepAllω_Zf`) are DISCHARGED there as real theorems.  The f-slot
enters the elimination lemmas as:

* **composition at principal cuts** — the reduction's output slot is `f ∘ g` of the premises';
* **max-relativization at ω-nodes** — `rel1 f n = fun x => f (max n x)`;
* **`hardy e` at the root** — `NormControlled` collapses to `hardy e` when `m = 0`.

These signatures are the lap-1 draft as **JUDGE-AMENDED** (2026-07-02,
`E-2026-07-02-JUDGE-rebuild-z-lap1-validation.md`, ratifying the lap-176 finding
`REBUILD-Z-LAP1-FINDING-2026-07-02-fslot-control-raise.md` — Option A, kernel-forced):
the reduction/step statements stay at **FIXED control** with the composed slot (E–W
Lemma 25 — the raised-control conjunct of the original draft was refutable two independent
ways: the K2b re-tag failure, and an `axL`-instantiation making the conjunct falsifiable
outright).  ALL ordinal COLLAPSE and numeric ITERATION is confined to `cutElimPass_Zf`
(E–W Lemma 27/30); per the lap-5 restatement (C1) the control `e` is UNTOUCHED — the ordinal
collapses (`collapse α`) and the slot iterates (`iterSlot f α`), where the P1 domination obligation
is paid by the pinned iterate — not by composition, not by a raised control.  Pins 1–2 are
DISCHARGED (§7, slot judgment `Zef`); pin 3 `cutElimPass_Zf` stays `sorry` (lap-5 entrance gate,
discharge FORBIDDEN). -/

/-- **Norm control** (the E–W "number-theoretic operator" bound, tied to the `(e, m)` axis):
`f` dominates the Hardy witness bound at every relativization depth.  `hardy e` is the root
instantiation (`normControlled_root`); the ω-node re-entry is `normControlled_rel1`. -/
def NormControlled (f : ℕ → ℕ) (e : ONote) (m : ℕ) : Prop :=
  ∀ x, hardy e (max m x) ≤ f x

/-- **Root instantiation** (LOCK §3, third bullet): `hardy e` controls the stage-0 axis. -/
theorem normControlled_root (e : ONote) : NormControlled (fun x => hardy e x) e 0 := by
  intro x; simp

/-- **Seam 2 in controlled form — the ω-node re-entry** (real proof): a controlled slot,
relativized at branch `n` and run at the max-adjoined stage, is controlled by `rel1 f n`.
This is `rel1_comp`'s semantic payload: the branch-unbounded demand that overflowed every
`Zekd` `d`-slot re-enters through ONE function slot's relativization. -/
theorem normControlled_rel1 {f : ℕ → ℕ} {e : ONote} {m : ℕ} (h : NormControlled f e m)
    (n : ℕ) : NormControlled (rel1 f n) e (max m n) := by
  intro x
  have hx := h (max n x)
  have he : max m (max n x) = max (max m n) x := by omega
  rw [he] at hx
  simpa [rel1] using hx

/-- Norm control is monotone in the slot (assembly plumbing: a dominating slot still
controls; reused when a reduction outputs a larger-than-needed composed slot). -/
theorem NormControlled.mono {f f' : ℕ → ℕ} {e : ONote} {m : ℕ}
    (h : NormControlled f e m) (hff' : ∀ x, f x ≤ f' x) : NormControlled f' e m :=
  fun x => le_trans (h x) (hff' x)

/-- Norm control is antitone in the stage: a slot controlling stage `m` controls any
smaller stage `m' ≤ m` (the `exI` bound only shrinks).  Reused when the reduction runs a
premise at a lower stage than the conclusion. -/
theorem NormControlled.stage_antitone {f : ℕ → ℕ} {e : ONote} {m m' : ℕ}
    (h : NormControlled f e m) (hm : m' ≤ m) : NormControlled f e m' :=
  fun x => le_trans (hardy_monotone e (by omega)) (h x)

/-- **Composition preserves control at a FIXED control** (E–W Lemma 25's numeric update,
`f ↦ f∘g`, at the *same* control — the faithful reduction shape per the lap-176 finding
`REBUILD-Z-LAP1-FINDING-2026-07-02-fslot-control-raise.md`, Option A).  If `g` controls `e`
at `m` and `f` is inflationary (E–W condition `(f.1)`: `2y+1 ≤ f y ⟹ y ≤ f y`), then the
composed slot `f ∘ g` still controls `e` at `m`.  This is the banked plumbing that discharges
the reduction conjunct `NormControlled (f∘g) e m` once the raise is confined to the
elimination pass — VALIDATING the lap-176 claim that Option A's reduction discharge is
near-immediate.  Note: this is the *fixed*-control fact (K2b-benign); the *raised*-control
demand belongs to `cutElimPass_Zf`'s pinned iterate, NOT here. -/
theorem NormControlled.comp {f g : ℕ → ℕ} {e : ONote} {m : ℕ}
    (hg : NormControlled g e m) (hf : ∀ y, y ≤ f y) : NormControlled (f ∘ g) e m :=
  fun x => le_trans (hg x) (hf (g x))

/-- **The reduction's composed-slot conjunct, DISCHARGED** (the `NormControlled (f∘g) e m` half
of pins 1–2, at FIXED control — Option A).  From `g` controlled at ANY stage `m₀` and `f`
controlled at the output stage `m`, the composed slot `f ∘ g` is controlled at `m`.  Unlike
`NormControlled.comp` this needs NO separate inflationarity hypothesis on `f`: control of `g`
already forces `g` inflationary (`x ≤ max m₀ x ≤ hardy e (max m₀ x) ≤ g x`, via `le_hardy`), and
then `f (g x) ≥ hardy e (max m (g x)) ≥ hardy e (max m x)` (`hf` at `g x`, `hardy_monotone`).
This is the kernel proof behind the judge's Q1 ruling ("discharge near-immediate via the banked
`NormControlled.comp` + hardy-inflationarity") — it does NOT touch the derivation, so it splits
cleanly off the reduction pins' second conjunct. -/
theorem normControlled_comp_running {f g : ℕ → ℕ} {e : ONote} {m₀ m : ℕ}
    (hg : NormControlled g e m₀) (hf : NormControlled f e m) : NormControlled (f ∘ g) e m := by
  intro x
  have hxg : x ≤ g x :=
    le_trans (le_trans (le_max_right m₀ x) (le_hardy e (max m₀ x))) (hg x)
  exact le_trans (hardy_monotone e (max_le_max (le_refl m) hxg)) (hf (g x))

/-- **Kernel witness for the stage-`m` reduction gap (the candidate sixth-trap root, now the
LOCK §1-A1 obstruction).**  The former stage-`m` reduction `redDeriv` (deleted lap 184) had a
principal-`exI` case where the witness satisfies only `n ≤ hardy e m`, which STRICTLY exceeds the
principal `exI` case the witness satisfies only `n ≤ hardy e m`, which STRICTLY exceeds the
stage `m` at any nontrivial control — e.g. `hardy ω m = 2m+1 > m`.  So `n ≤ hardy e m` does
NOT give `n ≤ m`, and the family member `fam n` (stage `max m₀ n`) cannot be lowered to the
output stage `m` (`Zeh` has no stage-lowering rule; LOCK §1 A1).  This is the reduction-stage
analog of the judge's fifth-trap kernel fact `hardy ω 0 = 1 > 0`. -/
theorem principal_witness_exceeds_stage (m : ℕ) : m < hardy ONote.omega m := by
  rw [show ONote.omega = oadd 1 1 0 from rfl, hardy_omega]; omega

/-! ## The numeric-slot ITERATE bricks (E–W Def 16 carriers; ported from `wip/ZefCutElim.lean`)

`Function.iterate` (`f^[k]`) is the `k`-fold composition; it preserves exactly the operator
conditions the reduction threads (monotone, inflationary, `NormControlled`) and composes to
iterates (`iter_comp`: counts ADD — the `∃`-cut lane).  These are the numeric carrier the pin-3
restatement's output slot (`iterSlot`, below) is built on.  All sorry-free — the ported bricks
were `#print axioms`-clean in `wip/ZefCutElim.lean`. -/

/-- The iterate is monotone if `f` is. -/
theorem iter_monotone {f : ℕ → ℕ} (hf : Monotone f) : ∀ k, Monotone f^[k]
  | 0 => monotone_id
  | k + 1 => by rw [Function.iterate_succ]; exact (iter_monotone hf k).comp hf

/-- The iterate is inflationary if `f` is. -/
theorem iter_infl {f : ℕ → ℕ} (hf : ∀ x, x ≤ f x) : ∀ k x, x ≤ f^[k] x
  | 0, x => le_rfl
  | k + 1, x => by
      rw [Function.iterate_succ']
      exact le_trans (iter_infl hf k x) (hf _)

/-- The iterate preserves `NormControlled` (for `k ≥ 1`): `f^[k+1] x ≥ f x ≥ hardy e (max m x)`,
via `f^[k]` inflationary. -/
theorem iter_normControlled {f : ℕ → ℕ} {e : ONote} {m : ℕ}
    (hf : NormControlled f e m) (hf_infl : ∀ x, x ≤ f x) (k : ℕ) :
    NormControlled f^[k + 1] e m := by
  intro x
  rw [Function.iterate_succ, Function.comp_apply]
  exact le_trans (hf x) (iter_infl hf_infl k (f x))

/-- Iterate monotone in the index count: `f^[j] ≤ f^[k]` pointwise for `j ≤ k`, `f` inflationary +
monotone.  Feeds `mono_f` when a pass outputs a longer iterate than a sibling branch needs. -/
theorem iter_le_of_le {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    {j k : ℕ} (hjk : j ≤ k) : ∀ x, f^[j] x ≤ f^[k] x := by
  intro x
  obtain ⟨d, rfl⟩ := Nat.le.dest hjk
  rw [Function.iterate_add_apply]
  exact iter_monotone hf_mono j (iter_infl hf_infl d x)

/-- **Iterates compose to iterates** (`f^[j] ∘ f^[k] = f^[j+k]`) — the numeric core of the
`∃`-cut lane: composing two premise iterates of the SAME base ADDS the counts, so the slot stays
`f^[·]`.  This is why pin 3's `f'` is a *pinned* iterate (Q2), not a free slot. -/
theorem iter_comp (f : ℕ → ℕ) (j k : ℕ) : f^[j] ∘ f^[k] = f^[j + k] :=
  (Function.iterate_add f j k).symm

/-! ## §5b The collapse + ordinal-indexed iterate — pin-3's restatement carriers (LOCK Addendum 2,
C2/C5; **iterate AMENDED by the lap-5 judge pass — SEVENTH statement trap**)

Pin 3 relates a rank-`c+1` derivation to a rank-`c` one by COLLAPSING the ordinal and ITERATING the
slot.  Two explicit ONote-grounded definitions:

- `collapse α := ω^α` (`expTower`) — E–W Lemma 27's Ω-free predicative shadow `φ 0 β = ω^β` for one
  rank step; iterated `c` times it is the rank-lowering tower `Ω_c(α) = Ω^{Ω_{c-1}(α)}`
  (paper §5, `arai`-style tower).  NF-preserving + strictly monotone (the descent the collapse
  induction needs) — both proven below (C5), reusing `expTower_NF`/`expTower_lt_expTower`.
- `iterSlot f α` — the **diagonalizing** ordinal-indexed iterate (E–W Def 16's `f^α`; Lemma 19's
  `F^α(0)` is a TRANSFINITE iterate, not a syntactic count).  Defined by the same
  fundamental-sequence recursion as the repo's `hardy` (which is exactly the successor's
  `iterSlot`): base `iterSlot f 0 = f`, successor `iterSlot f (a+1) n = iterSlot f a (f n)`,
  limit `iterSlot f λ n = iterSlot f (λ[n]) n`.  On finite ordinals it agrees with the retired
  count form (`iterSlot f (ofNat k) = f^[k+1]`); at limits it DIAGONALIZES — the branch index
  rides the numeric argument, which `rel1` raises (`rel1 (iterSlot f α) n` evaluates the ordinal
  index at `α[max n x]`-stages, absorbing branch-growing budgets).

**⚠️ SEVENTH STATEMENT TRAP (caught by the lap-5 judge pass; kernel evidence
`wip/JudgeTrap7Probe.lean`).**  The lap-5 draft's fixed-count form
`iterSlot f α := f^[norm α + 1]` is refuted at the `allω` reassembly: the pass's induction hands
branch `n` its output at slot `(rel1 f n)^[norm (β n) + 1]`, while the pin's conclusion forces the
parent's branch slot `rel1 (f^[norm α + 1]) n`; `Zef.mono_f` only RAISES slots, so reassembly needs
`(rel1 f n)^[norm (β n) + 1] ≤ rel1 (f^[norm α + 1]) n` pointwise.  Kernel counterexample at
`α = ω`, `β 2 = ofNat 2`, `f = hardy ω`, `x = 0`: parent side `f^[2] 2 = 11 < 23 = (rel1 f 2)^[3] 0`.
Root cause: `norm` is not monotone along `<` (`norm (ofNat n) = n` grows along ω's fundamental
sequence while `norm ω = 1`), so NO fixed ℕ-count read off the parent ordinal dominates the
branches — the diagonalization is forced.  (The box's lap-5 docstring mis-read its own statement:
it described branch slots as `rel1 (iterSlot f (β n)) n`, but the conclusion's slot parameter puts
`iterSlot f α` — the branch ordinal never enters the branch slot.) -/

/-- **`iterSlot`** — the diagonalizing ordinal-indexed numeric-slot iterate (E–W Def 16's `f^α` /
Lemma 19's `F^α(0)`): `iterSlot f 0 = f`; `iterSlot f (a+1) n = iterSlot f a (f n)`;
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
theorem iterSlot_def (f : ℕ → ℕ) {o : ONote} {x} (e : fundamentalSequence o = x) :
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
theorem iterSlot_zero' (f : ℕ → ℕ) (o : ONote) (h : fundamentalSequence o = Sum.inl none) :
    iterSlot f o = f := by
  rw [iterSlot_def f h]

/-- `iterSlot f o n = iterSlot f a (f n)` when `o` is the successor of `a`. -/
theorem iterSlot_succ (f : ℕ → ℕ) (o) {a} (h : fundamentalSequence o = Sum.inl (some a)) :
    iterSlot f o = fun n => iterSlot f a (f n) := by
  rw [iterSlot_def f h]

/-- `iterSlot f o n = iterSlot f (o[n]) n` when `o` is a limit with fundamental sequence `fs`. -/
theorem iterSlot_limit (f : ℕ → ℕ) (o) {fs} (h : fundamentalSequence o = Sum.inr fs) :
    iterSlot f o = fun n => iterSlot f (fs n) n := by
  rw [iterSlot_def f h]

/-- **C5: `iterSlot f α` is inflationary** if `f` is (slot stays inflationary through the pass).
Mirrors `le_hardy`. -/
theorem iterSlot_infl {f : ℕ → ℕ} (hf_infl : ∀ x, x ≤ f x) (o : ONote) (n : ℕ) :
    n ≤ iterSlot f o n := by
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
theorem iterSlot_le_of_reaches {f : ℕ → ℕ} (hf_infl : ∀ x, x ≤ f x) {x : ℕ} {β α : ONote}
    (h : Reaches x β α) :
    (∀ γ, Reaches x β γ → Monotone (iterSlot f γ)) → iterSlot f α x ≤ iterSlot f β x := by
  induction h with
  | refl a => intro _; exact le_rfl
  | @succ β γ α hb _ ih =>
      intro hmono
      have hmγ : Monotone (iterSlot f γ) := hmono γ (Reaches.succ hb (Reaches.refl γ))
      have ihγ : iterSlot f α x ≤ iterSlot f γ x := ih (fun δ hδ => hmono δ (Reaches.succ hb hδ))
      have heq : iterSlot f β x = iterSlot f γ (f x) := by rw [iterSlot_succ f _ hb]
      rw [heq]; exact le_trans ihγ (hmγ (hf_infl x))
  | @limit β α g hb _ ih =>
      intro hmono
      have ihg : iterSlot f α x ≤ iterSlot f (g x) x :=
        ih (fun δ hδ => hmono δ (Reaches.limit hb hδ))
      have heq : iterSlot f β x = iterSlot f (g x) x := by rw [iterSlot_limit f _ hb]
      rw [heq]; exact ihg

/-- **C5 (discharged lap 6): `iterSlot f α` is monotone** for `f` monotone + inflationary.
Mirrors `hardy_monotone`: zero case is `hf_mono`, successor threads the IH through `f`'s
monotonicity, and the limit case combines monotonicity of `iterSlot f (α[n])` (IH) with the index
step `iterSlot f (α[n])(n+1) ≤ iterSlot f (α[n+1])(n+1)` = `iterSlot_le_of_reaches` on the
structural Bachmann reach `fastGrowing_bachmann_reach` (every intermediate is `< α`, so the IH
supplies its monotonicity). -/
theorem iterSlot_monotone {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
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

/-- **C5: `iterSlot f 0 = f`** — the α = 0 (cut-free axiom) case leaves the slot unchanged. -/
theorem iterSlot_zero (f : ℕ → ℕ) : iterSlot f 0 = f :=
  iterSlot_zero' f 0 rfl

/-- **BUDGETED ordinal-monotonicity of `iterSlot`** (mirror of `hardy_le_of_lt`): for `β < α`
(both NF) and a budget `x ≥ norm β`, `iterSlot f β x ≤ iterSlot f α x`.  Composes
`reaches_of_lt` (the general Bachmann reachability `Reaches x α β`) with `iterSlot_le_of_reaches`
(value transfer) and `iterSlot_monotone` (the per-notation monotonicity).

This is the form-independent CRUX LEMMA for the trap-8 fix (`REBUILD-Z-TRAP8-2026-07-02.md`):
`iterSlot f ·` is NOT ordinal-monotone at a FIXED small argument
(`no_fixed_arg_monotone_unbounded_slot`), but it IS monotone once the argument reaches the
`norm`-budget of the smaller ordinal.  So any pin-3 output slot whose READ is node-relative
(argument `≥ norm` of the node's ordinal — e.g. a relativized `rel1 (iterSlot f α) K` with
`K ≥ norm α`) restores the `weak`/`exI`/`cut` slot-lift that the bare `iterSlot f α` cannot
supply.  Banked here so the architect's node-relative C2 amendment can splice it directly. -/
theorem iterSlot_le_of_lt {f : ℕ → ℕ} (hf_mono : Monotone f) (hf_infl : ∀ x, x ≤ f x)
    {x : ℕ} {α β : ONote} (hα : α.NF) (hβ : β.NF) (hβα : β < α) (hnorm : norm β ≤ x) :
    iterSlot f β x ≤ iterSlot f α x :=
  iterSlot_le_of_reaches hf_infl (reaches_of_lt α hα β hβ hβα hnorm)
    (fun γ _ => iterSlot_monotone hf_mono hf_infl γ)

end GoodsteinPA.OperatorZeh
