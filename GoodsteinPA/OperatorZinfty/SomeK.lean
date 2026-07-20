module

public import GoodsteinPA.OperatorZinfty.Cut
public import GoodsteinPA.OperatorZinfty.BoundedTruth

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

/-- A derivability wrapper where the witness index `K` is allowed to be chosen later, extracting
some finite witness budget rather than fixing it in advance. -/
def ProvableSomeK (α e : ONote) (d c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ K : ℕ, Provable α e K d c Γ

namespace ProvableSomeK

variable {α e : ONote} {d c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-- Embed a concrete `Provable` derivation into the existential-budget wrapper. -/
lemma of {K : ℕ} (dd : Provable α e K d c Γ) : ProvableSomeK α e d c Γ := ⟨K, dd⟩

/-- Convert the ordinal-upper-bound wrapper back to an exact-ordinal existential-budget
derivation by raising the stored derivation ordinal when needed. -/
lemma ofProv {K : ℕ} (hαNF : α.NF) (dd : ProvableSlack α e K d c Γ) : ProvableSomeK α e d c Γ := by
  rcases dd with ⟨α', hα', hα'NF, hnorm, D⟩
  by_cases hEq : α' = α
  · subst hEq
    exact ⟨K, D⟩
  · have hrepr_ne : α'.repr ≠ α.repr := by
      intro hr
      exact hEq (repr_inj.mp hr)
    have hlt : α' < α := lt_def.mpr (lt_of_le_of_ne (le_def.mp hα') hrepr_ne)
    exact ⟨K, Provable.weak hlt hα'NF hαNF hnorm (Finset.Subset.refl _) D⟩

/-- Identity/complementary-literal axiom for the existential-budget wrapper. -/
lemma axL {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    ProvableSomeK α e d c Γ :=
  ⟨0, Provable.axL r v hp hn⟩

/-- Truth of `⊤` for the existential-budget wrapper. -/
lemma verumR (h : (⊤ : ArithmeticFormula ℕ) ∈ Γ) : ProvableSomeK α e d c Γ := ⟨0, Provable.verumR h⟩

/-- True positive atomic leaf for the existential-budget wrapper; the finite index is
chosen large enough to pay the norm side condition. -/
lemma trueRel {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (htrue : atomTrue (Semiformula.rel r v)) (hαNF : α.NF)
    (hmem : Semiformula.rel r v ∈ Γ) : ProvableSomeK α e d c Γ := by
  let K := norm α + 1
  exact ⟨K, Provable.trueRel r v htrue (by dsimp [K]; omega) hαNF hmem⟩

/-- True negative atomic leaf for the existential-budget wrapper; the finite index is
chosen large enough to pay the norm side condition. -/
lemma trueNrel {ar : ℕ}
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (htrue : atomTrue (Semiformula.nrel r v)) (hαNF : α.NF)
    (hmem : Semiformula.nrel r v ∈ Γ) : ProvableSomeK α e d c Γ := by
  let K := norm α + 1
  exact ⟨K, Provable.trueNrel r v htrue (by dsimp [K]; omega) hαNF hmem⟩

/-- Existential-budget surface for bounded true closed-substitution leaves. -/
lemma ofBoundedTruth {n : ℕ}
    (q : ℕ) (w : Fin n → ArithmeticTerm ℕ) (ψ : ArithmeticSemiformula ℕ n)
    (hψq : ψ.complexity ≤ q)
    (hpack : ∃ K : ℕ, BoundedTruth e K d w ψ ∧ 2 * q < K + d)
    (hmem : (Rew.subst w ▹ ψ) ∈ Γ) :
    ProvableSomeK (ONote.ofNat (2 * q)) e d c Γ := by
  rcases hpack with ⟨K, hBT, hbudget⟩
  exact ⟨K, provableOfBoundedTruth_probe q w ψ hψq hBT hbudget hmem⟩

/-- Monotonicity in the sequent for the existential-budget wrapper. -/
lemma wk {Δ : Finset (ArithmeticFormula ℕ)} (hsub : Δ ⊆ Γ) (dd : ProvableSomeK α e d c Δ) :
  ProvableSomeK α e d c Γ := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, Provable.wk hsub D⟩

/-- Monotonicity in the additive norm-budget component. -/
lemma mono_d {d' : ℕ} (hd : d ≤ d') (dd : ProvableSomeK α e d c Γ) : ProvableSomeK α e d' c Γ := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.mono_d hd⟩

/-- Monotonicity in the cut-rank/complexity bound. -/
lemma mono_c {c' : ℕ} (hc : c ≤ c') (dd : ProvableSomeK α e d c Γ) : ProvableSomeK α e d c' Γ := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.mono_c hc⟩

/-- Control-ordinal monotonicity for the existential-budget wrapper.  The wrapper can
raise `K`, so the `norm e ≤ K+d` side condition of `Provable.mono_e` is paid locally. -/
lemma mono_e {e' : ONote}
    (heNF : e.NF) (he'NF : e'.NF) (hlt : e < e')
    (dd : ProvableSomeK α e d c Γ) :
    ProvableSomeK α e' d c Γ := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (norm e)
  refine ⟨K, (D0.mono_k (by dsimp [K]; omega)).mono_e heNF he'NF hlt ?_⟩
  dsimp [K]
  omega

/-- Ordinal/sequent weakening for the existential-budget wrapper: choose a finite
index large enough for the source ordinal norm side condition. -/
lemma weak {β : ONote} {Δ : Finset (ArithmeticFormula ℕ)}
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (hsub : Δ ⊆ Γ) (dd : ProvableSomeK β e d c Δ) :
    ProvableSomeK α e d c Γ := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (norm β + 1)
  refine ⟨K, Provable.weak hβ hβNF hαNF ?_ hsub (D0.mono_k ?_)⟩
  · dsimp [K]; omega
  · dsimp [K]; omega

/-- Combined monotonicity in the two numeric side budgets. -/
lemma mono {d' c' : ℕ} (hd : d ≤ d') (hc : c ≤ c') (dd : ProvableSomeK α e d c Γ) :
  ProvableSomeK α e d' c' Γ :=
  mono_c hc (mono_d hd dd)

/-- One-shot lift used by proof embeddings: raise the derivation ordinal, control ordinal,
numeric side budgets, and sequent at the same time, choosing a larger finite `K` internally. -/
lemma lift {β e' : ONote} {d' c' : ℕ} {Δ : Finset (ArithmeticFormula ℕ)}
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (heNF : e.NF) (he'NF : e'.NF) (he : e < e')
    (hd : d ≤ d') (hc : c ≤ c') (hsub : Δ ⊆ Γ)
    (dd : ProvableSomeK β e d c Δ) :
    ProvableSomeK α e' d' c' Γ :=
  mono hd hc (mono_e heNF he'NF he (weak hβ hβNF hαNF hsub dd))

/-- `andI` for the existential-budget wrapper: choose a finite index large enough for
both premises and both norm side conditions. -/
lemma andI {βφ βψ : ONote}
    (φ ψ : ArithmeticFormula ℕ) (hβφ : βφ < α) (hβψ : βψ < α)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
    (dφ : ProvableSomeK βφ e d c (insert φ Γ))
    (dψ : ProvableSomeK βψ e d c (insert ψ Γ)) :
    ProvableSomeK α e d c (insert (φ ⋏ ψ) Γ) := by
  rcases dφ with ⟨Kφ, Dφ⟩
  rcases dψ with ⟨Kψ, Dψ⟩
  let K := max Kφ (max Kψ (max (norm βφ + 1) (norm βψ + 1)))
  refine ⟨K, Provable.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF ?_ ?_ ?_ ?_⟩
  · dsimp [K]; omega
  · dsimp [K]; omega
  · exact Dφ.mono_k (by dsimp [K]; omega)
  · exact Dψ.mono_k (by dsimp [K]; omega)

/-- `orI` for the existential-budget wrapper. -/
lemma orI {β : ONote}
    (φ ψ : ArithmeticFormula ℕ) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (dd : ProvableSomeK β e d c (insert φ (insert ψ Γ))) :
    ProvableSomeK α e d c (insert (φ ⋎ ψ) Γ) := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (norm β + 1)
  refine ⟨K, Provable.orI φ ψ hβ hβNF hαNF ?_ ?_⟩
  · dsimp [K]; omega
  · exact D0.mono_k (by dsimp [K]; omega)

/-- `allω` for the existential-budget wrapper when the premise family is already
uniform at one finite base index `K`.  A fully existential premise family is not
enough: the rule needs a single finite budget whose `max K n` handles every branch. -/
lemma allω {K : ℕ}
    (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
    (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
    (hτ : ∀ n, norm (β n) < max K n + d)
    (dd : ∀ n, Provable (β n) e (max K n) d c (insert (φ/[nm n]) Γ)) :
    ProvableSomeK α e d c (insert (∀⁰ φ) Γ) :=
  ⟨K, Provable.allω φ β hβ hβNF hαNF hτ dd⟩

/-- `exI` for the existential-budget wrapper.  The wrapper chooses a finite
index large enough for both the premise derivation and the explicit witness. -/
lemma exI {β : ONote}
    (φ : ArithmeticSemiformula ℕ 1) (n : ℕ)
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (dd : ProvableSomeK β e d c (insert (φ/[nm n]) Γ)) :
    ProvableSomeK α e d c (insert (∃⁰ φ) Γ) := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (max (norm β + 1) n);
  use K;
  apply Provable.exI φ n hβ hβNF hαNF ?_ ?_ (D0.mono_k ?_);
  · omega
  · trans K + d;
    . omega;
    . apply le_hardy;
  · omega

/-- `cut` for the existential-budget wrapper. -/
lemma cut {βφ βψ : ONote}
    (φ : ArithmeticFormula ℕ) (hcompl : φ.complexity < c)
    (hβφ : βφ < α) (hβψ : βψ < α)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
    (d₁ : ProvableSomeK βφ e d c (insert φ Γ))
    (d₂ : ProvableSomeK βψ e d c (insert (∼φ) Γ)) :
    ProvableSomeK α e d c Γ := by
  rcases d₁ with ⟨K₁, D₁⟩
  rcases d₂ with ⟨K₂, D₂⟩
  use max K₁ (max K₂ (max (norm βφ + 1) (norm βψ + 1)));
  apply Provable.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF ?_ ?_ (D₁.mono_k ?_) (D₂.mono_k ?_);
  all_goals omega;

/-- Disjunction inversion for the existential-budget wrapper. -/
lemma orInv {φ ψ : ArithmeticFormula ℕ} (dd : ProvableSomeK α e d c Γ) (hmem : (φ ⋎ ψ) ∈ Γ) :
  ProvableSomeK α e d c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  rcases dd with ⟨K, D⟩;
  exact ⟨K, D.orInv hmem⟩

/-- Left conjunction inversion for the existential-budget wrapper. -/
lemma andInvL {φ ψ : ArithmeticFormula ℕ} (dd : ProvableSomeK α e d c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
  ProvableSomeK α e d c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.andInvL hmem⟩

/-- Right conjunction inversion for the existential-budget wrapper. -/
lemma andInvR {φ ψ : ArithmeticFormula ℕ} (dd : ProvableSomeK α e d c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
  ProvableSomeK α e d c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.andInvR hmem⟩

/-- Universal inversion for the existential-budget wrapper.  The extracted witness
index is the raw derivation index raised to `max K n₀`, matching `Provable.allInv`. -/
lemma allInv {φ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ) (dd : ProvableSomeK α e d c Γ) (hmem : (∀⁰ φ) ∈ Γ) :
  ProvableSomeK α e d c (insert (φ/[nm n₀]) (Γ.erase (∀⁰ φ))) := by
  rcases dd with ⟨K, D⟩
  exact ⟨max K n₀, D.allInv n₀ hmem⟩

/-- Principal conjunction/disjunction cut reduction for the existential-budget wrapper.
This is the `someK` surface of the fixed-index raw reduction, reused after choosing one finite
`K` large enough for both premises and the reduction ordinal.

- [Tow20, §19.5] -/
lemma cutReduceConj {a b : ArithmeticFormula ℕ} {β δ : ONote}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ)
    (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hC : ProvableSomeK α e d c (insert (a ⋏ b) Γ))
    (hNC : ProvableSomeK β e d c (insert (∼a ⋎ ∼b) Γ)) :
    ProvableSomeK (osucc δ) e d c Γ := by
  rcases hC with ⟨Kα, DC⟩;
  rcases hNC with ⟨Kβ, DNC⟩;
  use max Kα (max Kβ (max (norm α + 1) (max (norm β + 1) (norm δ + 1))));
  apply Provable.cutReduceConj ha hb hαδ hβδ hαNF hβNF hδNF ?_ ?_ ?_ (DC.mono_k ?_) (DNC.mono_k ?_);
  all_goals omega;

/-- Principal disjunction/conjunction cut reduction for the existential-budget wrapper.
Dual to `cutReduceConj`; again the wrapper absorbs the finite witness-index bookkeeping. -/
lemma cutReduceDisj {a b : ArithmeticFormula ℕ} {β δ : ONote}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ)
    (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hC : ProvableSomeK α e d c (insert (a ⋎ b) Γ))
    (hNC : ProvableSomeK β e d c (insert (∼a ⋏ ∼b) Γ)) :
    ProvableSomeK (osucc δ) e d c Γ := by
  rcases hC with ⟨Kα, DC⟩
  rcases hNC with ⟨Kβ, DNC⟩
  use max Kα (max Kβ (max (norm α + 1) (max (norm β + 1) (norm δ + 1))));
  apply Provable.cutReduceDisj ha hb hαδ hβδ hαNF hβNF hδNF ?_ ?_ ?_ (DC.mono_k ?_) (DNC.mono_k ?_);
  all_goals omega;

/-- Existential-budget surface for the proved ∀/∃ cut-reduction norm-budget auxiliary
(cf. [Tow20, §19.6]).

This is intentionally still the *fixed-family* theorem: the ∀-side family is supplied at one
finite index `k₀`. The wrapper absorbs the ∃-side finite index and converts the `ProvableSlack`
ordinal upper bound back to an exact `ProvableSomeK` derivation. -/
lemma cutReduceAllAux {φ : ArithmeticSemiformula ℕ 1} {k₀ d₀ : ℕ}
    {γ : ONote} {Δ : Finset (ArithmeticFormula ℕ)}
    (hφc : φ.complexity < c) (hαNF : α.NF) (hγNF : γ.NF) (heNF : e.NF)
    (hd₀ : d₀ ≤ d)
    (fam : ∀ n, Provable α e k₀ d₀ c (insert (φ/[nm n]) Γ))
    (D : ProvableSomeK γ e d c Δ) (hmem : (∃⁰ ∼φ) ∈ Δ) :
    ProvableSomeK (osucc (α + γ)) e (d + norm α + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  rcases D with ⟨Kγ, Dγ⟩
  let K := max Kγ (max k₀ (norm γ + 1))
  have hprov : ProvableSlack (osucc (α + γ)) e K (d + norm α + 1) c
      (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
    GoodsteinPA.OperatorZinfty.cutReduceAllAux hφc hαNF heNF fam
      (Dγ.mono_k (by dsimp [K]; omega)) hγNF (by dsimp [K]; omega)
      (by dsimp [K]; omega) hd₀ hmem
  exact ofProv (osucc_NF (ONote.add_nf α γ)) hprov

/-- Control-raised surface for the fixed-family ∀/∃ cut reduction (cf. [Tow20, §19.6]).

This is the part of the full `Provable` cut-elimination assembly where the norm-budget auxiliary
has already fired and the control ordinal is then raised to enlarge every existential witness
bound.  The existential-budget wrapper chooses the finite index needed by `mono_e` internally. -/
lemma cutReduceAllAux_control {φ : ArithmeticSemiformula ℕ 1} {k₀ d₀ : ℕ}
    {γ e' : ONote} {Δ : Finset (ArithmeticFormula ℕ)}
    (hφc : φ.complexity < c) (hαNF : α.NF) (hγNF : γ.NF)
    (heNF : e.NF) (he'NF : e'.NF) (helt : e < e')
    (hd₀ : d₀ ≤ d)
    (fam : ∀ n, Provable α e k₀ d₀ c (insert (φ/[nm n]) Γ))
    (D : ProvableSomeK γ e d c Δ) (hmem : (∃⁰ ∼φ) ∈ Δ) :
    ProvableSomeK (osucc (α + γ)) e' (d + norm α + 1) c
      (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
  mono_e heNF he'NF helt
    (cutReduceAllAux hφc hαNF hγNF heNF hd₀ fam D hmem)

end ProvableSomeK

end GoodsteinPA.OperatorZinfty
