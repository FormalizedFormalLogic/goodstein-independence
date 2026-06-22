/-
# The witness bound: why the current `src/Zinfty.lean` cut-elimination cannot reach the headline

**Lap-4 architectural finding (2026-06-22).**  `src/GoodsteinPA/Zinfty.lean` machine-checks a
beautiful, axiom-clean ε₀ cut-elimination for the `Z_∞` calculus.  But that calculus's `∃`-rule
(`Deriv.exI`) places **no bound on the witness numeral** relative to the ordinal: `exI φ n d`
accepts *any* `n : ℕ` and only does `o ↦ o + 1`.  The ordinal measure `o` does not track Towsner's
numeric index `k`, and there is no Hardy bound `value(t) ≤ h_α(k)` on witnesses.

Towsner's whole unprovability argument is a sandwich:

  Thm 16.7  (M4, embedding)        PA⁺ ⊢ φ  ⟹  ∃ α<ε₀, k, c.  Z_∞ ⊢^{α,k}_c φ
  Thm 19.9  (M5, cut-elimination)  Z_∞ ⊢^{α,k}_c φ  ⟹  Z_∞ ⊢^{α',k}_0 φ,  α'<ε₀   [DONE for (α,c)]
  Thm 17.1  (M6, lower bound)      no cut-free Z_∞ ⊢^{α,k}_0  ∀x∃y g_y(x)=0  for α<ε₀

The **bottom slice (17.1) is the load-bearing inequality** — it is *why* PA cannot prove Goodstein.
Its proof inducts on α and, at the `I∃` step, uses the witness bound `value(t) ≤ h_α(k) < G(n)` to
force the introduced atom `g_t(n)=0` to be **false**.  Drop the witness bound and the lower bound
is simply **false**: one can take the witness to be `G(n)` itself.

This file makes that undeniable.  `unbounded_proves_goodstein` below is a *machine-checked* proof
that the witness-**unbounded** cut-free calculus (the structural analogue of the current
`src/Zinfty.lean`) derives the Goodstein sentence at ordinal **2** — so no lower bound can hold for
it, and the completed `(α,c)` cut-elimination, however clean, **cannot** reach the headline.

The fix (Towsner-faithful) is the **witness-bounded, Hardy-indexed** calculus `B` below: the `∃`-rule
carries `v ≤ h α k`, the `True` rule carries `τ α < k`, and the `∀`-rule's premises use numeric
bound `max k n`.  The lower bound (`lowerBound`) is then *true* — stated here against the abstract
Hardy data `(h, τ, G)`, proof deferred (a genuine frontier; see the invariant note on `lowerBound`).

Self-contained over an abstract atomic base (`atom m n` = "`g_m(n)=0`", true iff
`goodsteinSeq n m = 0`), exactly the standard Schütte/Tait setup.  WIP — not in the build target.
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.Lattice.Nat
import GoodsteinPA.Defs

namespace GoodsteinPA.WitnessBound

open Ordinal

/-- The Goodstein fragment of formulas (negation-normal, one-sided).  These are the only formula
shapes that appear in a *cut-free* derivation of the Goodstein sentence (subformula property):
the sentence `∀x∃y g_y(x)=0`, the existentials `∃y g_y(n)=0`, and the closed atoms `g_m(n)=0`.

We write `g_m(n)` for `goodsteinSeq n m` (Towsner's `g_y(x)` is our `goodsteinSeq x y`), so
`atom m n` is the closed atomic sentence "`goodsteinSeq n m = 0`". -/
inductive GForm
  | atom (m n : ℕ)   -- `g_m(n) = 0`
  | gEx (n : ℕ)      -- `∃y g_y(n) = 0`
  | gAll             -- `∀x ∃y g_y(x) = 0`
  deriving DecidableEq

namespace GForm

/-- An atom `g_m(n)=0` is *true in ℕ* iff the Goodstein sequence seeded at `n` has reached `0` by
step `m`.  (Goodstein sequences are eventually-`0` and stay `0`, so this is monotone in `m`.) -/
def atomTrue (m n : ℕ) : Prop := goodsteinSeq n m = 0

instance (m n : ℕ) : Decidable (atomTrue m n) := by unfold atomTrue; infer_instance

end GForm

open GForm

/-! ### The Goodstein function `G` and the atomic facts (grounded, no abstract hypotheses)

These discharge the `HG` hypothesis of `lowerBound_existential` *concretely*, and record the
monotonicity ("once `0`, stays `0`") that makes `G` the genuine first-zero step. -/

/-- `bump b 0 = 0`: `0` is the fixed point that makes a Goodstein sequence absorb at `0`. -/
@[simp] theorem bump_zero (b : ℕ) : bump b 0 = 0 := by rw [bump]; simp

/-- **Once zero, stays zero.**  `g_{m+1}(n) = bump (base m) (g_m(n)) - 1`, and `bump _ 0 - 1 = 0`. -/
theorem goodstein_zero_succ {n m : ℕ} (h : goodsteinSeq n m = 0) :
    goodsteinSeq n (m + 1) = 0 := by
  simp [goodsteinSeq, h]

/-- The Goodstein function `G n`: the first step at which the sequence seeded at `n` reaches `0`
(Towsner Def 7.1).  `Nat.sInf` of the zero-set (`0` if never — but Goodstein's theorem says always). -/
noncomputable def G (n : ℕ) : ℕ := sInf {m | goodsteinSeq n m = 0}

/-- **`HG`, concretely.**  A true atom `g_m(n)=0` forces `m ≥ G n` — `G n` is the *least* zero step.
This discharges the abstract `HG` hypothesis of `lowerBound_existential` against the real `G`. -/
theorem G_le_of_atomTrue {m n : ℕ} (h : atomTrue m n) : G n ≤ m :=
  Nat.sInf_le h

/-- **Upward closure of the zero-set.**  Once a Goodstein sequence reaches `0` it stays `0`. -/
theorem goodstein_zero_mono {n m : ℕ} (h : goodsteinSeq n m = 0) :
    ∀ {j : ℕ}, m ≤ j → goodsteinSeq n j = 0 := by
  intro j hj
  induction hj with
  | refl => exact h
  | step _ ih => exact goodstein_zero_succ ih

/-- Given termination at `n`, `G n` is itself a zero step (the threshold is attained). -/
theorem goodstein_G {n : ℕ} (hterm : ∃ m, goodsteinSeq n m = 0) : goodsteinSeq n (G n) = 0 :=
  Nat.sInf_mem hterm

/-- **The atomic truth ↔ threshold characterization.**  Under termination, `g_m(n)=0` is true iff
`m ≥ G n`.  This is exactly the semantic content the lower bound consumes: the witness-bounded `∃`
introduces a *false* atom precisely when its witness `v < G n`.  (`→` needs no termination.) -/
theorem atomTrue_iff_G_le {m n : ℕ} (hterm : ∃ m, goodsteinSeq n m = 0) :
    atomTrue m n ↔ G n ≤ m :=
  ⟨G_le_of_atomTrue, fun hle => goodstein_zero_mono (goodstein_G hterm) hle⟩

/-- A sequent is a finite **set** of fragment formulas (Tait one-sided, set-based ⇒ contraction is
free, no explicit `C` rule). -/
abbrev Seq := Finset GForm

/-! ## The witness-**unbounded** cut-free calculus `U` — the current architecture, and why it fails

`U α Γ` is the cut-free `Z_∞` fragment with **no** witness bound on `∃` and **no** numeric index
`k` — structurally exactly what `src/Zinfty.lean`'s `Deriv` provides (its `exI` takes an arbitrary
numeral, its `o` just does `+1`).  We show it proves the Goodstein sentence at ordinal `2`. -/
inductive U : Ordinal.{0} → Seq → Prop
  | trueR {α : Ordinal} {Γ : Seq} {m n : ℕ}
      (hmem : atom m n ∈ Γ) (htrue : atomTrue m n) : U α Γ
  | weak {α β : Ordinal} {Δ Γ : Seq} (hβ : β ≤ α) (hsub : Δ ⊆ Γ) (d : U β Δ) : U α Γ
  | exI {α β : Ordinal} {Γ : Seq} {n v : ℕ} (hβ : β < α) (hmem : gEx n ∈ Γ)
      (d : U β (insert (atom v n) Γ)) : U α Γ          -- witness `v` is *unrestricted*
  | allI {α : Ordinal} {Γ : Seq} (β : ℕ → Ordinal) (hmem : gAll ∈ Γ)
      (hβ : ∀ n, β n < α) (d : ∀ n, U (β n) (insert (gEx n) Γ)) : U α Γ

/-- **The architectural gap, machine-checked.**  Granting only that every Goodstein sequence
terminates (Goodstein's theorem, `Hterm` — *true*, and exactly what the headline is about), the
witness-**unbounded** cut-free calculus derives the full Goodstein sentence `∀x∃y g_y(x)=0` at
ordinal `2`.  Hence **no** lower bound à la Towsner 17.1 can hold for this calculus, and the
clean `(α,c)` cut-elimination of `src/Zinfty.lean` — which never constrains witnesses — cannot be
the cut-free system that the headline needs.  The witness bound (calculus `B` below) is essential. -/
theorem unbounded_proves_goodstein (Hterm : ∀ n, ∃ m, goodsteinSeq n m = 0) :
    U 2 ({gAll} : Seq) := by
  refine U.allI (fun _ => 1) (by simp) (fun n => one_lt_two) (fun n => ?_)
  -- For each `n`, pick the step `m` at which the sequence seeded at `n` first hits `0`.
  obtain ⟨m, hm⟩ := Hterm n
  -- `g_m(n)=0` is a true atom, closing the leaf at ordinal `0`; then `I∃` with witness `m`.
  refine U.exI (β := 0) (n := n) (v := m) zero_lt_one (by simp) ?_
  exact U.trueR (m := m) (n := n) (by simp) hm

/-! ## The witness-**bounded**, Hardy-indexed calculus `B` — the corrected architecture (Towsner §15)

The bounds are an ordinal `α` (height) and a numeric index `k`.  The data controlling witnesses:

* `h : Ordinal → ℕ → ℕ`  — the Hardy hierarchy `h_α` (Towsner Def 6.3),
* `τ : Ordinal → ℕ`      — ordinal complexity (Towsner Def 8.1).

Rules (Towsner §15), cut-free (`c = 0`):

* `True`:  a true atom in `Γ`, side condition `τ α < k`;
* `W`   :  from `Δ ⊆ Γ`, premise bound `β < α`, `τ β < k`;
* `I∃`  :  **witness bound** `v ≤ h α k`, premise bound `β < α`, `τ β < k`;
* `I∀`  :  ω-rule, premise `n` at numeric bound `max k n`, ordinal `β n < α`, `τ (β n) < max k n`.

(Contraction is free via `Finset`.) -/
section Bounded
variable (h : Ordinal.{0} → ℕ → ℕ) (τ : Ordinal.{0} → ℕ) (G : ℕ → ℕ)

inductive B : Ordinal.{0} → ℕ → Seq → Prop
  | trueR {α : Ordinal} {k : ℕ} {Γ : Seq} {m n : ℕ}
      (hmem : atom m n ∈ Γ) (htrue : atomTrue m n) (hτ : τ α < k) : B α k Γ
  | weak {α β : Ordinal} {k : ℕ} {Δ Γ : Seq}
      (hβ : β < α) (hτ : τ β < k) (hsub : Δ ⊆ Γ) (d : B β k Δ) : B α k Γ
  | exI {α β : Ordinal} {k : ℕ} {Γ : Seq} {n v : ℕ}
      (hβ : β < α) (hτ : τ β < k) (hbound : v ≤ h α k)
      (hmem : gEx n ∈ Γ) (d : B β k (insert (atom v n) Γ)) : B α k Γ
  | allI {α : Ordinal} {k : ℕ} {Γ : Seq} (β : ℕ → Ordinal)
      (hmem : gAll ∈ Γ) (hβ : ∀ n, β n < α) (hτ : ∀ n, τ (β n) < max k n)
      (d : ∀ n, B (β n) (max k n) (insert (gEx n) Γ)) : B α k Γ

/-- **The `∃`-side lower bound — the witness bound's load-bearing consequence, machine-checked.**

Restricted to the `∀`-free Goodstein fragment (sequents of pending existentials `∃y g_y(n)=0` and
false atoms `g_m(n)=0`), the witness-bounded cut-free calculus *cannot* derive a sequent all of
whose existentials are "out of reach" — `h α k < G n` — and all of whose atoms are false (`m < G n`,
i.e. `g_m(n) ≠ 0`).  This is *exactly why the witness bound bites*: every `∃` the calculus can
discharge introduces an atom `g_v(n)=0` with `v ≤ h α k < G n`, which is **false**, so the leaf can
never be closed by the `True` rule, and the ordinal strictly descends — a well-founded impossibility.

Compare `unbounded_proves_goodstein`: without the witness bound, the witness can be `G n` and the
identical sequent *is* derivable.  The two theorems together pin the witness bound as the precise
mechanism separating "headline-reaching" from "vacuous" cut-free `Z_∞`.

Hypotheses (Towsner §6/§8 facts, supplied abstractly — discharged later from the Hardy hierarchy):
* `Hmono`  `h_β(k) ≤ h_α(k)` for `β < α` with `τ β < k`            (Lemma 16.10, monotonicity),
* `HG`     a true atom `g_m(n)=0` forces `m ≥ G n`                 (Goodstein reaches `0` at `G n`).

The full Towsner 17.1 (with the Goodstein **sentence** `∀x∃y g_y(x)=0` present, hence the `I∀`
ω-rule and *accumulating* existentials) needs a more refined invariant than Towsner states — see
`ON-LINE-REQUEST.md` and the lap-4 note in `STATUS.md`; that is the remaining frontier (`gAll`-case). -/
theorem lowerBound_existential
    (Hmono : ∀ {β α : Ordinal.{0}} {k : ℕ}, β < α → τ β < k → h β k ≤ h α k)
    (HG : ∀ {m n : ℕ}, atomTrue m n → G n ≤ m) :
    ∀ (α : Ordinal.{0}) (k : ℕ) (Γ : Seq),
      (∀ f ∈ Γ, (∃ n, f = gEx n ∧ h α k < G n) ∨ (∃ m n, f = atom m n ∧ m < G n)) →
      ¬ B h τ α k Γ := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro k Γ hcond hB
    cases hB with
    | trueR hmem htrue hτ =>
      -- A true atom `g_m(n)=0` in `Γ` forces `G n ≤ m`; but every atom of `Γ` is false (`m < G n`).
      rename_i m n
      rcases hcond _ hmem with ⟨n', hf, _⟩ | ⟨m', n', hf, hlt⟩
      · exact absurd hf (by simp)
      · obtain ⟨rfl, rfl⟩ : m = m' ∧ n = n' := by simpa [GForm.atom.injEq] using hf
        exact absurd (HG htrue) (by omega)
    | weak hβ hτ hsub d =>
      -- Weakening: `Δ ⊆ Γ` inherits the invariant at the smaller bound `β` (monotonicity of `h`).
      rename_i β Δ
      refine IH β hβ k Δ (fun f hf => ?_) d
      rcases hcond f (hsub hf) with ⟨n, hfn, hgt⟩ | ⟨m, n, hfm, hlt⟩
      · exact Or.inl ⟨n, hfn, lt_of_le_of_lt (Hmono hβ hτ) hgt⟩
      · exact Or.inr ⟨m, n, hfm, hlt⟩
    | exI hβ hτ hbound hmem d =>
      -- The introduced witness atom `g_v(n)=0` has `v ≤ h α k < G n`, hence is false: invariant holds.
      rename_i β n v
      have hgtn : h α k < G n := by
        rcases hcond _ hmem with ⟨n', hfn, hgt⟩ | ⟨_, _, hf, _⟩
        · obtain rfl : n = n' := by simpa [GForm.gEx.injEq] using hfn
          exact hgt
        · exact absurd hf (by simp)
      refine IH β hβ k (insert (atom v n) Γ) (fun f hf => ?_) d
      rcases Finset.mem_insert.mp hf with rfl | hfΓ
      · exact Or.inr ⟨v, n, rfl, lt_of_le_of_lt hbound hgtn⟩
      · rcases hcond f hfΓ with ⟨n', hfn, hgt⟩ | ⟨m, n', hfm, hlt⟩
        · exact Or.inl ⟨n', hfn, lt_of_le_of_lt (Hmono hβ hτ) hgt⟩
        · exact Or.inr ⟨m, n', hfm, hlt⟩
    | allI β hmem _ _ _ =>
      -- The `∀`-rule needs `gAll ∈ Γ`, but this fragment has none.
      rcases hcond _ hmem with ⟨_, hf, _⟩ | ⟨_, _, hf, _⟩ <;> exact absurd hf (by simp)

end Bounded

/-- `lowerBound_existential` against the **real** Goodstein function `G` (its `HG` least-zero
property discharged by `G_le_of_atomTrue`).  Only the Hardy monotonicity `Hmono` — a Towsner §6
fact about a concrete `h_α` — remains abstract; that is the next brick (mathlib `ONote.fastGrowing`
or a bespoke Hardy hierarchy + `τ` over `ONote`). -/
theorem lowerBound_existential_real (h : Ordinal.{0} → ℕ → ℕ) (τ : Ordinal.{0} → ℕ)
    (Hmono : ∀ {β α : Ordinal.{0}} {k : ℕ}, β < α → τ β < k → h β k ≤ h α k) :
    ∀ (α : Ordinal.{0}) (k : ℕ) (Γ : Seq),
      (∀ f ∈ Γ, (∃ n, f = gEx n ∧ h α k < G n) ∨ (∃ m n, f = atom m n ∧ m < G n)) →
      ¬ B h τ α k Γ :=
  lowerBound_existential h τ G Hmono @G_le_of_atomTrue

/-! ## The full Goodstein lower bound (Towsner Thm 17.1), as an honest decomposition

The full lower bound (with the Goodstein **sentence** present, hence the `I∀` ω-rule) is the
headline-relevant girder M6.  We isolate its single open frontier — the **bounding lemma** — as a
named disclosed `sorry`, and machine-check the contradiction-extraction from it.  Any rigorous proof
of `bounding` (see `ON-LINE-REQUEST.md`) immediately yields the full lower bound `lowerBound`. -/
section FullLowerBound
variable (h : Ordinal.{0} → ℕ → ℕ) (τ : Ordinal.{0} → ℕ)

/-- **Bounded satisfaction** of a fragment formula at `(α,k)`: a witness bounded by the Hardy value
`h α (max k ·)`, input-adjusted (the universal at input `x` is allowed witness up to `h α (max k x)`).
Provisional interpretation — its exact shape is part of the `bounding` invariant design. -/
def sat (α : Ordinal.{0}) (k : ℕ) : GForm → Prop
  | .gAll     => ∀ x, G x ≤ h α (max k x)
  | .gEx n    => G n ≤ h α (max k n)
  | .atom m n => G n ≤ m

/-- Ordinal-monotonicity of `sat` (same numeric bound `k`): from `sat` at `(a,k)` to `(b,k)` for
`a < b` with `τ a < k`.  Atoms are bound-independent; `gEx`/`gAll` lift by `Hmono`. -/
theorem sat_mono_ord (Hmono : ∀ {a b : Ordinal.{0}} {j : ℕ}, a < b → τ a < j → h a j ≤ h b j)
    {a b : Ordinal.{0}} {k : ℕ} {f : GForm} (hab : a < b) (hτ : τ a < k) (hs : sat h a k f) :
    sat h b k f := by
  cases f with
  | atom m n => exact hs
  | gEx n => exact le_trans hs (Hmono hab (lt_of_lt_of_le hτ (le_max_left k n)))
  | gAll => exact fun x => le_trans (hs x) (Hmono hab (lt_of_lt_of_le hτ (le_max_left k x)))

/-- **Bounding lemma — frontier isolated to the `I∀` case.**  A cut-free, witness-bounded derivation
of `Γ` makes *some* formula of `Γ` bounded-true.  The `True`/`W`/`I∃` cases are **machine-verified**
below; the lone `sorry` is the `I∀` (ω-rule) case with *accumulated* existentials — exactly the
invariant subtlety in `ON-LINE-REQUEST.md`.  Held at `sorry` per the anti-fraud charter.

`Hmono_n` (numeric monotonicity of the Hardy hierarchy `h a j ≤ h a j'` for `j ≤ j'`) is a standard
§6 fact, used in `I∃` to lift a witness bounded by `h α k` to the input-adjusted `h α (max k n)`. -/
theorem bounding (Hmono : ∀ {a b : Ordinal.{0}} {j : ℕ}, a < b → τ a < j → h a j ≤ h b j)
    (Hmono_n : ∀ (a : Ordinal.{0}) {j j' : ℕ}, j ≤ j' → h a j ≤ h a j') :
    ∀ {α : Ordinal.{0}} {k : ℕ} {Γ : Seq}, B h τ α k Γ → ∃ f ∈ Γ, sat h α k f := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro k Γ hB
    cases hB with
    | trueR hmem htrue hτ =>
      rename_i m n
      exact ⟨atom m n, hmem, G_le_of_atomTrue htrue⟩
    | weak hβ hτ hsub d =>
      obtain ⟨f, hfΔ, hsat⟩ := IH _ hβ d
      exact ⟨f, hsub hfΔ, sat_mono_ord h τ Hmono hβ hτ hsat⟩
    | exI hβ hτ hbound hmem d =>
      rename_i β n v
      obtain ⟨f, hf, hsat⟩ := IH _ hβ d
      rcases Finset.mem_insert.mp hf with rfl | hfΓ
      · -- IH returned the introduced (false) atom `g_v(n)=0`: hence `gEx n` is bounded-true at `(α,k)`.
        refine ⟨gEx n, hmem, ?_⟩
        exact le_trans hsat (le_trans hbound (Hmono_n α (le_max_left k n)))
      · exact ⟨f, hfΓ, sat_mono_ord h τ Hmono hβ hτ hsat⟩
    | allI βfn hmem hβ hτ d =>
      -- FRONTIER: the ω-rule with accumulated existentials (see ON-LINE-REQUEST.md).
      sorry

/-- **The full Goodstein lower bound (Towsner Thm 17.1), modulo `bounding`** — machine-checked
contradiction-extraction.  Goodstein domination (`Hdom`: some input `x` whose Goodstein length `G x`
outruns the Hardy bound `h α (max k x)`, Towsner Thm 7.2/9.8) rules out any cut-free witness-bounded
derivation of the Goodstein sentence.  This is the headline-relevant shape of M6. -/
theorem lowerBound (Hmono : ∀ {a b : Ordinal.{0}} {j : ℕ}, a < b → τ a < j → h a j ≤ h b j)
    (Hmono_n : ∀ (a : Ordinal.{0}) {j j' : ℕ}, j ≤ j' → h a j ≤ h a j')
    (α : Ordinal.{0}) (k : ℕ) (Hdom : ∃ x, h α (max k x) < G x) :
    ¬ B h τ α k ({gAll} : Seq) := by
  intro hB
  obtain ⟨f, hf, hsat⟩ := bounding h τ Hmono Hmono_n hB
  rw [Finset.mem_singleton] at hf
  subst hf
  obtain ⟨x, hx⟩ := Hdom
  exact absurd (hsat x) (not_le.mpr hx)

end FullLowerBound

end GoodsteinPA.WitnessBound
