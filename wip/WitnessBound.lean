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

end GoodsteinPA.WitnessBound
