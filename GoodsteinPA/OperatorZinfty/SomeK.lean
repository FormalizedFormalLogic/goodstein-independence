module

public import GoodsteinPA.OperatorZinfty.Cut
public import GoodsteinPA.OperatorZinfty.BoundedTruth

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

/-- A derivability wrapper where the witness index `K` is allowed to be chosen later, extracting
some finite witness budget rather than fixing it in advance. -/
def ZekdSomeK (α e : ONote) (d c : ℕ) (Γ : Seq) : Prop :=
  ∃ K : ℕ, Zekd α e K d c Γ

namespace ZekdSomeK

/-- Embed a concrete `Zekd` derivation into the existential-budget wrapper. -/
theorem of {α e : ONote} {K d c : ℕ} {Γ : Seq}
    (dd : Zekd α e K d c Γ) : ZekdSomeK α e d c Γ :=
  ⟨K, dd⟩

/-- Convert the ordinal-upper-bound wrapper back to an exact-ordinal existential-budget
derivation by raising the stored derivation ordinal when needed. -/
theorem ofProv {α e : ONote} {K d c : ℕ} {Γ : Seq}
    (hαNF : α.NF) (dd : ZekdProv α e K d c Γ) : ZekdSomeK α e d c Γ := by
  rcases dd with ⟨α', hα', hα'NF, hnorm, D⟩
  by_cases hEq : α' = α
  · subst hEq
    exact ⟨K, D⟩
  · have hrepr_ne : α'.repr ≠ α.repr := by
      intro hr
      exact hEq (repr_inj.mp hr)
    have hlt : α' < α := lt_def.mpr (lt_of_le_of_ne (le_def.mp hα') hrepr_ne)
    exact ⟨K, Zekd.weak hlt hα'NF hαNF hnorm (Finset.Subset.refl _) D⟩

/-- Identity/complementary-literal axiom for the existential-budget wrapper. -/
theorem axL {α e : ONote} {d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (hp : Semiformula.rel r v ∈ Γ) (hn : Semiformula.nrel r v ∈ Γ) :
    ZekdSomeK α e d c Γ :=
  ⟨0, Zekd.axL r v hp hn⟩

/-- Truth of `⊤` for the existential-budget wrapper. -/
theorem verumR {α e : ONote} {d c : ℕ} {Γ : Seq}
    (h : (⊤ : Form) ∈ Γ) : ZekdSomeK α e d c Γ :=
  ⟨0, Zekd.verumR h⟩

/-- True positive atomic leaf for the existential-budget wrapper; the finite index is
chosen large enough to pay the norm side condition. -/
theorem trueRel {α e : ONote} {d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (htrue : atomTrue (Semiformula.rel r v)) (hαNF : α.NF)
    (hmem : Semiformula.rel r v ∈ Γ) : ZekdSomeK α e d c Γ := by
  let K := norm α + 1
  exact ⟨K, Zekd.trueRel r v htrue (by dsimp [K]; omega) hαNF hmem⟩

/-- True negative atomic leaf for the existential-budget wrapper; the finite index is
chosen large enough to pay the norm side condition. -/
theorem trueNrel {α e : ONote} {d c ar : ℕ} {Γ : Seq}
    (r : (ℒₒᵣ).Rel ar) (v : Fin ar → ArithmeticTerm ℕ)
    (htrue : atomTrue (Semiformula.nrel r v)) (hαNF : α.NF)
    (hmem : Semiformula.nrel r v ∈ Γ) : ZekdSomeK α e d c Γ := by
  let K := norm α + 1
  exact ⟨K, Zekd.trueNrel r v htrue (by dsimp [K]; omega) hαNF hmem⟩

/-- Existential-budget surface for bounded true closed-substitution leaves. -/
theorem ofBoundedTruth {e : ONote} {d c n : ℕ} {Γ : Seq}
    (q : ℕ) (w : Fin n → ArithmeticTerm ℕ) (ψ : ArithmeticSemiformula ℕ n)
    (hψq : ψ.complexity ≤ q)
    (hpack : ∃ K : ℕ, ZekdBoundedTruth e K d w ψ ∧ 2 * q < K + d)
    (hmem : (Rew.subst w ▹ ψ) ∈ Γ) :
    ZekdSomeK (ONote.ofNat (2 * q)) e d c Γ := by
  rcases hpack with ⟨K, hBT, hbudget⟩
  exact ⟨K, zekdOfBoundedTruth_probe q w ψ hψq hBT hbudget hmem⟩

/-- Monotonicity in the sequent for the existential-budget wrapper. -/
theorem wk {α e : ONote} {d c : ℕ} {Δ Γ : Seq}
    (hsub : Δ ⊆ Γ) (dd : ZekdSomeK α e d c Δ) :
    ZekdSomeK α e d c Γ := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, Zekd.wk hsub D⟩

/-- Monotonicity in the additive norm-budget component. -/
theorem mono_d {α e : ONote} {d d' c : ℕ} {Γ : Seq}
    (hd : d ≤ d') (dd : ZekdSomeK α e d c Γ) :
    ZekdSomeK α e d' c Γ := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.mono_d hd⟩

/-- Monotonicity in the cut-rank/complexity bound. -/
theorem mono_c {α e : ONote} {d c c' : ℕ} {Γ : Seq}
    (hc : c ≤ c') (dd : ZekdSomeK α e d c Γ) :
    ZekdSomeK α e d c' Γ := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.mono_c hc⟩

/-- Control-ordinal monotonicity for the existential-budget wrapper.  The wrapper can
raise `K`, so the `norm e ≤ K+d` side condition of `Zekd.mono_e` is paid locally. -/
theorem mono_e {α e e' : ONote} {d c : ℕ} {Γ : Seq}
    (heNF : e.NF) (he'NF : e'.NF) (hlt : e < e')
    (dd : ZekdSomeK α e d c Γ) :
    ZekdSomeK α e' d c Γ := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (norm e)
  refine ⟨K, (D0.mono_k (by dsimp [K]; omega)).mono_e heNF he'NF hlt ?_⟩
  dsimp [K]
  omega

/-- Ordinal/sequent weakening for the existential-budget wrapper: choose a finite
index large enough for the source ordinal norm side condition. -/
theorem weak {α β e : ONote} {d c : ℕ} {Δ Γ : Seq}
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (hsub : Δ ⊆ Γ) (dd : ZekdSomeK β e d c Δ) :
    ZekdSomeK α e d c Γ := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (norm β + 1)
  refine ⟨K, Zekd.weak hβ hβNF hαNF ?_ hsub (D0.mono_k ?_)⟩
  · dsimp [K]; omega
  · dsimp [K]; omega

/-- Combined monotonicity in the two numeric side budgets. -/
theorem mono {α e : ONote} {d d' c c' : ℕ} {Γ : Seq}
    (hd : d ≤ d') (hc : c ≤ c') (dd : ZekdSomeK α e d c Γ) :
    ZekdSomeK α e d' c' Γ :=
  mono_c hc (mono_d hd dd)

/-- One-shot lift used by proof embeddings: raise the derivation ordinal, control ordinal,
numeric side budgets, and sequent at the same time, choosing a larger finite `K` internally. -/
theorem lift {α β e e' : ONote} {d d' c c' : ℕ} {Δ Γ : Seq}
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (heNF : e.NF) (he'NF : e'.NF) (he : e < e')
    (hd : d ≤ d') (hc : c ≤ c') (hsub : Δ ⊆ Γ)
    (dd : ZekdSomeK β e d c Δ) :
    ZekdSomeK α e' d' c' Γ :=
  mono hd hc (mono_e heNF he'NF he (weak hβ hβNF hαNF hsub dd))

/-- `andI` for the existential-budget wrapper: choose a finite index large enough for
both premises and both norm side conditions. -/
theorem andI {α βφ βψ e : ONote} {d c : ℕ} {Γ : Seq}
    (φ ψ : Form) (hβφ : βφ < α) (hβψ : βψ < α)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
    (dφ : ZekdSomeK βφ e d c (insert φ Γ))
    (dψ : ZekdSomeK βψ e d c (insert ψ Γ)) :
    ZekdSomeK α e d c (insert (φ ⋏ ψ) Γ) := by
  rcases dφ with ⟨Kφ, Dφ⟩
  rcases dψ with ⟨Kψ, Dψ⟩
  let K := max Kφ (max Kψ (max (norm βφ + 1) (norm βψ + 1)))
  refine ⟨K, Zekd.andI φ ψ hβφ hβψ hβφNF hβψNF hαNF ?_ ?_ ?_ ?_⟩
  · dsimp [K]; omega
  · dsimp [K]; omega
  · exact Dφ.mono_k (by dsimp [K]; omega)
  · exact Dψ.mono_k (by dsimp [K]; omega)

/-- `orI` for the existential-budget wrapper. -/
theorem orI {α β e : ONote} {d c : ℕ} {Γ : Seq}
    (φ ψ : Form) (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (dd : ZekdSomeK β e d c (insert φ (insert ψ Γ))) :
    ZekdSomeK α e d c (insert (φ ⋎ ψ) Γ) := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (norm β + 1)
  refine ⟨K, Zekd.orI φ ψ hβ hβNF hαNF ?_ ?_⟩
  · dsimp [K]; omega
  · exact D0.mono_k (by dsimp [K]; omega)

/-- `allω` for the existential-budget wrapper when the premise family is already
uniform at one finite base index `K`.  A fully existential premise family is not
enough: the rule needs a single finite budget whose `max K n` handles every branch. -/
theorem allω {α e : ONote} {K d c : ℕ} {Γ : Seq}
    (φ : ArithmeticSemiformula ℕ 1) (β : ℕ → ONote)
    (hβ : ∀ n, β n < α) (hβNF : ∀ n, (β n).NF) (hαNF : α.NF)
    (hτ : ∀ n, norm (β n) < max K n + d)
    (dd : ∀ n, Zekd (β n) e (max K n) d c (insert (φ/[nm n]) Γ)) :
    ZekdSomeK α e d c (insert (∀⁰ φ) Γ) :=
  ⟨K, Zekd.allω φ β hβ hβNF hαNF hτ dd⟩

/-- `exI` for the existential-budget wrapper.  The wrapper chooses a finite
index large enough for both the premise derivation and the explicit witness. -/
theorem exI {α β e : ONote} {d c : ℕ} {Γ : Seq}
    (φ : ArithmeticSemiformula ℕ 1) (n : ℕ)
    (hβ : β < α) (hβNF : β.NF) (hαNF : α.NF)
    (dd : ZekdSomeK β e d c (insert (φ/[nm n]) Γ)) :
    ZekdSomeK α e d c (insert (∃⁰ φ) Γ) := by
  rcases dd with ⟨K0, D0⟩
  let K := max K0 (max (norm β + 1) n)
  refine ⟨K, Zekd.exI φ n hβ hβNF hαNF ?_ ?_ (D0.mono_k ?_)⟩
  · dsimp [K]; omega
  · exact le_trans (by dsimp [K]; omega) (le_hardy e (K + d))
  · dsimp [K]; omega

/-- `cut` for the existential-budget wrapper. -/
theorem cut {α βφ βψ e : ONote} {d c : ℕ} {Γ : Seq}
    (φ : Form) (hcompl : φ.complexity < c)
    (hβφ : βφ < α) (hβψ : βψ < α)
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hαNF : α.NF)
    (d₁ : ZekdSomeK βφ e d c (insert φ Γ))
    (d₂ : ZekdSomeK βψ e d c (insert (∼φ) Γ)) :
    ZekdSomeK α e d c Γ := by
  rcases d₁ with ⟨K₁, D₁⟩
  rcases d₂ with ⟨K₂, D₂⟩
  let K := max K₁ (max K₂ (max (norm βφ + 1) (norm βψ + 1)))
  refine ⟨K, Zekd.cut φ hcompl hβφ hβψ hβφNF hβψNF hαNF ?_ ?_ ?_ ?_⟩
  · dsimp [K]; omega
  · dsimp [K]; omega
  · exact D₁.mono_k (by dsimp [K]; omega)
  · exact D₂.mono_k (by dsimp [K]; omega)

/-- Disjunction inversion for the existential-budget wrapper. -/
theorem orInv {φ ψ : Form} {α e : ONote} {d c : ℕ} {Γ : Seq}
    (dd : ZekdSomeK α e d c Γ) (hmem : (φ ⋎ ψ) ∈ Γ) :
    ZekdSomeK α e d c (insert φ (insert ψ (Γ.erase (φ ⋎ ψ)))) := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.orInv hmem⟩

/-- Left conjunction inversion for the existential-budget wrapper. -/
theorem andInvL {φ ψ : Form} {α e : ONote} {d c : ℕ} {Γ : Seq}
    (dd : ZekdSomeK α e d c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
    ZekdSomeK α e d c (insert φ (Γ.erase (φ ⋏ ψ))) := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.andInvL hmem⟩

/-- Right conjunction inversion for the existential-budget wrapper. -/
theorem andInvR {φ ψ : Form} {α e : ONote} {d c : ℕ} {Γ : Seq}
    (dd : ZekdSomeK α e d c Γ) (hmem : (φ ⋏ ψ) ∈ Γ) :
    ZekdSomeK α e d c (insert ψ (Γ.erase (φ ⋏ ψ))) := by
  rcases dd with ⟨K, D⟩
  exact ⟨K, D.andInvR hmem⟩

/-- Universal inversion for the existential-budget wrapper.  The extracted witness
index is the raw derivation index raised to `max K n₀`, matching `Zekd.allInv`. -/
theorem allInv {φ : ArithmeticSemiformula ℕ 1} (n₀ : ℕ)
    {α e : ONote} {d c : ℕ} {Γ : Seq}
    (dd : ZekdSomeK α e d c Γ) (hmem : (∀⁰ φ) ∈ Γ) :
    ZekdSomeK α e d c (insert (φ/[nm n₀]) (Γ.erase (∀⁰ φ))) := by
  rcases dd with ⟨K, D⟩
  exact ⟨max K n₀, D.allInv n₀ hmem⟩

/-- Principal conjunction/disjunction cut reduction for the existential-budget wrapper.
This is the `someK` surface of Towsner §19.5: the fixed-index raw reduction is reused after
choosing one finite `K` large enough for both premises and the reduction ordinal. -/
theorem cutReduceConj {a b : Form} {d c : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ)
    (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hC : ZekdSomeK α e d c (insert (a ⋏ b) Γ))
    (hNC : ZekdSomeK β e d c (insert (∼a ⋎ ∼b) Γ)) :
    ZekdSomeK (osucc δ) e d c Γ := by
  rcases hC with ⟨Kα, DC⟩
  rcases hNC with ⟨Kβ, DNC⟩
  let K := max Kα (max Kβ (max (norm α + 1) (max (norm β + 1) (norm δ + 1))))
  refine ⟨K, Zekd.cutReduceConj ha hb hαδ hβδ hαNF hβNF hδNF ?_ ?_ ?_
    (DC.mono_k ?_) (DNC.mono_k ?_)⟩
  · dsimp [K]; omega
  · dsimp [K]; omega
  · dsimp [K]; omega
  · dsimp [K]; omega
  · dsimp [K]; omega

/-- Principal disjunction/conjunction cut reduction for the existential-budget wrapper.
Dual to `cutReduceConj`; again the wrapper absorbs the finite witness-index bookkeeping. -/
theorem cutReduceDisj {a b : Form} {d c : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ)
    (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hC : ZekdSomeK α e d c (insert (a ⋎ b) Γ))
    (hNC : ZekdSomeK β e d c (insert (∼a ⋏ ∼b) Γ)) :
    ZekdSomeK (osucc δ) e d c Γ := by
  rcases hC with ⟨Kα, DC⟩
  rcases hNC with ⟨Kβ, DNC⟩
  let K := max Kα (max Kβ (max (norm α + 1) (max (norm β + 1) (norm δ + 1))))
  refine ⟨K, Zekd.cutReduceDisj ha hb hαδ hβδ hαNF hβNF hδNF ?_ ?_ ?_
    (DC.mono_k ?_) (DNC.mono_k ?_)⟩
  · dsimp [K]; omega
  · dsimp [K]; omega
  · dsimp [K]; omega
  · dsimp [K]; omega
  · dsimp [K]; omega

/-- Existential-budget surface for the proved §19.6 norm-budget auxiliary.

This is intentionally still the *fixed-family* theorem: the ∀-side family is supplied at one
finite index `k₀`. The wrapper absorbs the ∃-side finite index and converts the `ZekdProv`
ordinal upper bound back to an exact `ZekdSomeK` derivation. -/
theorem cutReduceAllAux {φ : ArithmeticSemiformula ℕ 1} {c k₀ d₀ d : ℕ}
    {α γ e : ONote} {Γ Δ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (hγNF : γ.NF) (heNF : e.NF)
    (hd₀ : d₀ ≤ d)
    (fam : ∀ n, Zekd α e k₀ d₀ c (insert (φ/[nm n]) Γ))
    (D : ZekdSomeK γ e d c Δ) (hmem : (∃⁰ ∼φ) ∈ Δ) :
    ZekdSomeK (osucc (α + γ)) e (d + norm α + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  rcases D with ⟨Kγ, Dγ⟩
  let K := max Kγ (max k₀ (norm γ + 1))
  have hprov : ZekdProv (osucc (α + γ)) e K (d + norm α + 1) c
      (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
    GoodsteinPA.OperatorZinfty.cutReduceAllAux hφc hαNF heNF fam
      (Dγ.mono_k (by dsimp [K]; omega)) hγNF (by dsimp [K]; omega)
      (by dsimp [K]; omega) hd₀ hmem
  exact ofProv (osucc_NF (ONote.add_nf α γ)) hprov

/-- Control-raised surface for the fixed-family §19.6 forall/ex cut reduction.

This is the part of the full operator cut-elimination assembly where the norm-budget auxiliary
has already fired and the control ordinal is then raised to enlarge every existential witness
bound.  The existential-budget wrapper chooses the finite index needed by `mono_e` internally. -/
theorem cutReduceAllAux_control {φ : ArithmeticSemiformula ℕ 1} {c k₀ d₀ d : ℕ}
    {α γ e e' : ONote} {Γ Δ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (hγNF : γ.NF)
    (heNF : e.NF) (he'NF : e'.NF) (helt : e < e')
    (hd₀ : d₀ ≤ d)
    (fam : ∀ n, Zekd α e k₀ d₀ c (insert (φ/[nm n]) Γ))
    (D : ZekdSomeK γ e d c Δ) (hmem : (∃⁰ ∼φ) ∈ Δ) :
    ZekdSomeK (osucc (α + γ)) e' (d + norm α + 1) c
      (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
  mono_e heNF he'NF helt
    (cutReduceAllAux hφc hαNF hγNF heNF hd₀ fam D hmem)

end ZekdSomeK

end GoodsteinPA.OperatorZinfty
