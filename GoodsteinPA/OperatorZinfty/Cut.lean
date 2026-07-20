module

public import GoodsteinPA.OperatorZinfty.Inversion

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

namespace Provable

variable {α e : ONote} {k d c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-- **∧/∨ cut reduction, conjunction case**.

- [Tow20, §19.5] -/
lemma cutReduceConj {a b : ArithmeticFormula ℕ} {β δ : ONote}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Provable α e k d c (insert (a ⋏ b) Γ)) (hNC : Provable β e k d c (insert (∼a ⋎ ∼b) Γ)) :
    Provable (osucc δ) e k d c Γ := by
  have hA : Provable α e k d c (insert a Γ) := Provable.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvL (Finset.mem_insert_self _ _))
  have hB : Provable α e k d c (insert b Γ) := Provable.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvR (Finset.mem_insert_self _ _))
  have hNab : Provable β e k d c (insert (∼a) (insert (∼b) Γ)) := Provable.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.orInv (Finset.mem_insert_self _ _))
  have cutA : Provable δ e k d c (insert (∼b) Γ) :=
    Provable.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ
      (Provable.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hA) hNab
  exact Provable.cut b hb (lt_trans hαδ (lt_osucc hδNF)) (lt_osucc hδNF) hαNF hδNF (osucc_NF hδNF)
    hτα hτδ hB cutA

/-- **∧/∨ cut reduction, disjunction case** (dual). -/
lemma cutReduceDisj {a b : ArithmeticFormula ℕ} {β δ : ONote}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Provable α e k d c (insert (a ⋎ b) Γ)) (hNC : Provable β e k d c (insert (∼a ⋏ ∼b) Γ)) :
    Provable (osucc δ) e k d c Γ := by
  have hAB : Provable α e k d c (insert a (insert b Γ)) := Provable.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.orInv (Finset.mem_insert_self _ _))
  have hNa : Provable β e k d c (insert (∼a) Γ) := Provable.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvL (Finset.mem_insert_self _ _))
  have hNb : Provable β e k d c (insert (∼b) Γ) := Provable.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvR (Finset.mem_insert_self _ _))
  have cutA : Provable δ e k d c (insert b Γ) :=
    Provable.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ hAB
      (Provable.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hNa)
  exact Provable.cut b hb (lt_osucc hδNF) (lt_trans hβδ (lt_osucc hδNF)) hδNF hβNF (osucc_NF hδNF)
    hτδ hτβ cutA hNb


end Provable

/-! ### `ProvableSlack` — the `Provable`-style wrapper (bound-as-upper-bound)

`Provable` carries an *exact* derivation ordinal, so every ordinal-raise (e.g. `wk`'s
`γ ↦ osucc(α+γ)` in cut-elimination) needs `NF` of the source. The wrapper bundles an upper
bound + the source's `NF`, so the `≤`-slack absorbs the `osucc`/`+1` bookkeeping uniformly and
`NF` is always available. This is the surface the ∀/∃ cut reduction `cutReduceAllAux` is stated
over (matching the role of the unbounded `Provable` wrapper for the plain `Z_∞` calculus). -/
def ProvableSlack (α e : ONote) (k d c : ℕ) (Γ : Finset (ArithmeticFormula ℕ)) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ norm α' < k + d ∧ Provable α' e k d c Γ

namespace ProvableSlack

variable {α e : ONote} {k d c : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}

/-- Monotonicity in `α` (≤), `k`, `d`, `c` (the control `e` is raised separately by `mono_e`,
which carries a budget side condition). The carried norm bound `norm α' < k+d` rides up to `k'+d'`. -/
lemma mono {β} {k' d' c'}
    (hα : α ≤ β) (hk : k ≤ k') (hd : d ≤ d') (hc : c ≤ c') :
    ProvableSlack α e k d c Γ → ProvableSlack β e k' d' c' Γ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', le_trans hα' hα, hNF, by omega, ((D.mono_k hk).mono_d hd).mono_c hc⟩

/-- Control-ordinal raising at the wrapper level. -/
lemma mono_e {e'}
    (heNF : e.NF) (he'NF : e'.NF) (hlt : e < e') (hbudget : norm e ≤ k + d) :
    ProvableSlack α e k d c Γ → ProvableSlack α e' k d c Γ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', hα', hNF, hnorm, D.mono_e heNF he'NF hlt hbudget⟩

/-- Sequent weakening. -/
lemma weakening {Δ} (h : Γ ⊆ Δ) :
    ProvableSlack α e k d c Γ → ProvableSlack α e k d c Δ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', hα', hNF, hnorm, D.wk h⟩

/-- Respect set-equality of sequents. -/
lemma cast {Δ} (e0 : Γ = Δ) :
    ProvableSlack α e k d c Γ → ProvableSlack α e k d c Δ := fun h => e0 ▸ h

/-- Lift a raw `Provable` derivation (NF ordinal + norm bound) into the wrapper. -/
lemma of (hNF : α.NF) (hnorm : norm α < k + d)
    (D : Provable α e k d c Γ) : ProvableSlack α e k d c Γ := ⟨α, le_refl _, hNF, hnorm, D⟩

end ProvableSlack

/-! ### ∀/∃ cut reduction `cutReduceAllAux` — norm-budget half

The induction core of the ∀/∃ cut reduction, for the control-ordinal witness-bounded calculus over
the **norm-carrying** `ProvableSlack` wrapper. Cut the ∀-inversion family `fam` (over `φ`, control `e`,
index `(k₀,dd₀)`) against an ∃-side derivation `D : Provable γ e k dd c Δ` containing `∃∼φ`, producing
a `Provable`-derivation of `Δ.erase(∃∼φ) ∪ Γ` at ordinal `osucc(α+γ)`, control `e` (inert), index
`(k, dd+norm α+1)`.

⚠️ **SCOPE.** This statement takes `fam` at the **FIXED** index `k₀` and keeps `e` inert — proving
the NORM-budget half cleanly, but it is **NOT yet feedable by `cutReduceAll`**: `allInv` produces
the ∀-family at the *running* index `max k₀ n` (the n-th ω-premise lives higher), and a derivation
with witnesses up to `hardy e (max k₀ n + dd₀)` does NOT exist at the smaller fixed index `k₀`.
Closing the **witness-budget** half needs `fam` at `max k₀ n` AND the control `e` *raised* — the
numeric single-index bound is provably FALSE (`h_{βₙ#ω}(max{k,n}) ≰ max{h_{β#ω}(k),n}` for large
`n`). The fix is operator-controlled derivations, cf. [EW12, §4, Definition 23]. This proof is the
reusable **norm-machinery + structural port**: every case carries to the `H`-calculus verbatim
except the `exI`/`allω` witness side-condition (`n ≤ hardy e (k+d)` ⤳ `n ∈ H`).

**Norm-budget resolution.** The commuting `allω` norm budget is closed by THREE coupled moves:
1. **norm-carrying wrapper** `ProvableSlack α e k d c Γ := ∃ α', α'≤α ∧ α'.NF ∧ norm α'<k+d ∧ Provable α' …`,
   so the IH EXPOSES `norm α' < (its k)+(its d)` — exactly the `allω` premise's norm budget (a plain
   `α'≤α` wrapper threw this away, since `norm` is not `≤`-monotone);
2. **thread `norm γ < k+dd`** through the induction (each case's child budget is supplied by that rule's
   own `hτ` side-condition; used only to bound `norm(osucc(α+γ))` at the result);
3. **d-bump `dd ↦ dd+norm α+1`** — the `+1` absorbs the `osucc`, giving STRICT budgets everywhere
   (and killing the leaf `k+dd=0` edge). Control `e` stays inert (witnesses stay `≤ hardy e (·)`); it is
   raised only at the top-level cut in `cutReduceAll` via `mono_e`.

`induction D` generalizes `e k dd c Δ` (and reverts `fam`/`heNF`/`hφc`, re-supplied per-case via the
IH), keeping `α k₀ dd₀ Γ φ hαNF` fixed — the `allInv` precedent scaled to carry the external family.
Each constructor case is proved by a dedicated `cutReduceAllAux_*` helper below (heartbeats are
counted per-declaration, so splitting the eleven cases out of the single induction keeps every
individual declaration within the default budget).

- [Tow20, §19.6]
- [EW12, §4, Definition 23]
- [Buc03, §6]
-/

variable {φ : ArithmeticSemiformula ℕ 1} {α : ONote} {k₀ dd₀ : ℕ} {Γ : Finset (ArithmeticFormula ℕ)}
  (hαNF : α.NF) {e' : ONote} {k' dd' c' : ℕ}
  (hφc : φ.complexity < c') (heNF : e'.NF) (fam : ∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ))

/-- Moving an `insert` past an `erase` only ever shrinks the set, regardless of whether the
inserted element is the erased one. Used to weaken the case lemmas of `cutReduceAllAux`. -/
private lemma erase_insert_union_subset {a b : ArithmeticFormula ℕ} {s t : Finset (ArithmeticFormula ℕ)} :
    (insert a s).erase b ∪ t ⊆ insert a (s.erase b ∪ t) := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  tauto

/-- The converse inclusion of `erase_insert_union_subset`, valid when the inserted element differs
from the erased one. Used to weaken the case lemmas of `cutReduceAllAux`. -/
private lemma insert_erase_union_subset {a b : ArithmeticFormula ℕ} {s t : Finset (ArithmeticFormula ℕ)}
    (hab : a ≠ b) :
    insert a (s.erase b ∪ t) ⊆ (insert a s).erase b ∪ t := by
  intro x hx
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
  rcases hx with rfl | hx
  · exact Or.inl ⟨hab, Or.inl rfl⟩
  · tauto

/-- `cutReduceAllAux`, the `axL` case. -/
private lemma cutReduceAllAux_axL {γ' : ONote} {Δ : Finset (ArithmeticFormula ℕ)} {ar}
    (r : (ℒₒᵣ).Rel ar) (v) (hp : Semiformula.rel r v ∈ Δ) (hn : Semiformula.nrel r v ∈ Δ) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
  ⟨0, le_def.mpr (by simp), NF.zero, by simp only [norm_zero]; omega, Provable.axL r v
    (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
    (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))⟩

/-- `cutReduceAllAux`, the `verumR` case. -/
private lemma cutReduceAllAux_verumR {γ' : ONote} {Δ : Finset (ArithmeticFormula ℕ)}
    (h : (⊤ : ArithmeticFormula ℕ) ∈ Δ) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
  ⟨0, le_def.mpr (by simp), NF.zero, by simp only [norm_zero]; omega, Provable.verumR
    (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))⟩

include hαNF in
/-- `cutReduceAllAux`, the `trueRel` case. -/
private lemma cutReduceAllAux_trueRel {γ' : ONote} {Δ : Finset (ArithmeticFormula ℕ)} {ar}
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (r : (ℒₒᵣ).Rel ar) (v)
    (htrue : atomTrue (Semiformula.rel r v)) (hmemA : Semiformula.rel r v ∈ Δ) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
  ⟨_, le_trans (le_add_left_NF hαNF hγNF) (le_of_lt (lt_osucc (ONote.add_nf α _))),
    hγNF, by omega, Provable.trueRel r v htrue (by omega) hγNF
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩

include hαNF in
/-- `cutReduceAllAux`, the `trueNrel` case. -/
private lemma cutReduceAllAux_trueNrel {γ' : ONote} {Δ : Finset (ArithmeticFormula ℕ)} {ar}
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (r : (ℒₒᵣ).Rel ar) (v)
    (htrue : atomTrue (Semiformula.nrel r v)) (hmemA : Semiformula.nrel r v ∈ Δ) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Δ.erase (∃⁰ ∼φ) ∪ Γ) :=
  ⟨_, le_trans (le_add_left_NF hαNF hγNF) (le_of_lt (lt_osucc (ONote.add_nf α _))),
    hγNF, by omega, Provable.trueNrel r v htrue (by omega) hγNF
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩

include hαNF hφc heNF fam in
/-- `cutReduceAllAux`, the `wk` case. -/
private lemma cutReduceAllAux_wk {γ' : ONote} {Δsub Δsup : Finset (ArithmeticFormula ℕ)}
    (hsub : Δsub ⊆ Δsup) (D' : Provable γ' e' k' dd' c' Δsub)
    (ih : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      γ'.NF → norm γ' < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ Δsub →
      ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Δsub.erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (hk : k₀ ≤ k') (hdd : dd₀ ≤ dd') (_hmem : (∃⁰ ∼φ) ∈ Δsup) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Δsup.erase (∃⁰ ∼φ) ∪ Γ) := by
  by_cases hd : (∃⁰ ∼φ) ∈ Δsub
  · exact (ih hφc heNF fam hγNF hγb hk hdd hd).weakening (by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
      rcases hx with ⟨hne, hxs⟩ | hxΓ
      · exact Or.inl ⟨hne, hsub hxs⟩
      · exact Or.inr hxΓ)
  · refine ⟨γ', le_trans (le_add_left_NF hαNF hγNF) (le_of_lt (lt_osucc (ONote.add_nf α _))),
      hγNF, by omega, (D'.mono_d (by omega)).wk (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩

include hαNF hφc heNF fam in
/-- `cutReduceAllAux`, the `weak` case. -/
private lemma cutReduceAllAux_weak {γ' β : ONote} {Δsub Δsup : Finset (ArithmeticFormula ℕ)}
    (hβ : β < γ') (hβNF : β.NF) (hτ : norm β < k' + dd') (hsub : Δsub ⊆ Δsup)
    (D' : Provable β e' k' dd' c' Δsub)
    (ih : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      β.NF → norm β < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ Δsub →
      ProvableSlack (osucc (α + β)) e' k' (dd' + norm α + 1) c' (Δsub.erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ'.NF) (hk : k₀ ≤ k') (hdd : dd₀ ≤ dd') (_hmem : (∃⁰ ∼φ) ∈ Δsup) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Δsup.erase (∃⁰ ∼φ) ∪ Γ) := by
  by_cases hd : (∃⁰ ∼φ) ∈ Δsub
  · exact ((ih hφc heNF fam hβNF (by omega) hk hdd hd).weakening (by
      intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
      rcases hx with ⟨hne, hxs⟩ | hxΓ
      · exact Or.inl ⟨hne, hsub hxs⟩
      · exact Or.inr hxΓ)).mono
      (le_of_lt (add_osucc_descent hαNF hβNF hγNF hβ)) le_rfl le_rfl le_rfl
  · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (le_add_left_NF hαNF hγNF)
      (le_of_lt (lt_osucc (ONote.add_nf α _))))), hβNF, by omega,
      (D'.mono_d (by omega)).wk (by
        intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩

include hαNF hφc heNF fam in
/-- `cutReduceAllAux`, the `andI` case. -/
private lemma cutReduceAllAux_andI {γ' βφ βψ : ONote} {Γ₀ : Finset (ArithmeticFormula ℕ)}
    {ψ₁ ψ₂ : ArithmeticFormula ℕ} (hβφ : βφ < γ') (hβψ : βψ < γ') (hβφNF : βφ.NF) (hβψNF : βψ.NF)
    (hτφ : norm βφ < k' + dd') (hτψ : norm βψ < k' + dd')
    (ihφ : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      βφ.NF → norm βφ < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ insert ψ₁ Γ₀ →
      ProvableSlack (osucc (α + βφ)) e' k' (dd' + norm α + 1) c' ((insert ψ₁ Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (ihψ : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      βψ.NF → norm βψ < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ insert ψ₂ Γ₀ →
      ProvableSlack (osucc (α + βψ)) e' k' (dd' + norm α + 1) c' ((insert ψ₂ Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (hk : k₀ ≤ k') (hdd : dd₀ ≤ dd') (hmem : (∃⁰ ∼φ) ∈ insert (ψ₁ ⋏ ψ₂) Γ₀) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' ((insert (ψ₁ ⋏ ψ₂) Γ₀).erase (∃⁰ ∼φ) ∪ Γ) := by
  have hhead : (ψ₁ ⋏ ψ₂) ≠ (∃⁰ ∼φ) := by intro h; simp [Wedge.wedge, ExsQuantifier.exs] at h
  have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
  obtain ⟨aφ, haφle, haφNF, haφnorm, Dφ⟩ := ihφ hφc heNF fam hβφNF (by omega) hk hdd
    (Finset.mem_insert_of_mem hmem0)
  obtain ⟨aψ, haψle, haψNF, haψnorm, Dψ⟩ := ihψ hφc heNF fam hβψNF (by omega) hk hdd
    (Finset.mem_insert_of_mem hmem0)
  have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
  have Dφ' : Provable aφ e' k' (dd' + norm α + 1) c' (insert ψ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    Dφ.wk erase_insert_union_subset
  have Dψ' : Provable aψ e' k' (dd' + norm α + 1) c' (insert ψ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    Dψ.wk erase_insert_union_subset
  have hAnd : Provable (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
      (insert (ψ₁ ⋏ ψ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    Provable.andI ψ₁ ψ₂
      (lt_of_le_of_lt haφle (add_osucc_descent hαNF hβφNF hγNF hβφ))
      (lt_of_le_of_lt haψle (add_osucc_descent hαNF hβψNF hγNF hβψ))
      haφNF haψNF hsuccNF haφnorm haψnorm Dφ' Dψ'
  refine ProvableSlack.of hsuccNF
    (lt_of_le_of_lt norm_osucc_le (by have := norm_add_le_of_nf hαNF hγNF; omega))
    (hAnd.wk (insert_erase_union_subset hhead))

include hαNF hφc heNF fam in
/-- `cutReduceAllAux`, the `orI` case. -/
private lemma cutReduceAllAux_orI {γ' β : ONote} {Γ₀ : Finset (ArithmeticFormula ℕ)}
    {ψ₁ ψ₂ : ArithmeticFormula ℕ} (hβ : β < γ') (hβNF : β.NF) (hτ : norm β < k' + dd')
    (ih : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      β.NF → norm β < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ insert ψ₁ (insert ψ₂ Γ₀) →
      ProvableSlack (osucc (α + β)) e' k' (dd' + norm α + 1) c' ((insert ψ₁ (insert ψ₂ Γ₀)).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (hk : k₀ ≤ k') (hdd : dd₀ ≤ dd') (hmem : (∃⁰ ∼φ) ∈ insert (ψ₁ ⋎ ψ₂) Γ₀) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' ((insert (ψ₁ ⋎ ψ₂) Γ₀).erase (∃⁰ ∼φ) ∪ Γ) := by
  have hhead : (ψ₁ ⋎ ψ₂) ≠ (∃⁰ ∼φ) := by intro h; simp [Vee.vee, ExsQuantifier.exs] at h
  have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
  obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))
  have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
  have Da' : Provable a e' k' (dd' + norm α + 1) c'
      (insert ψ₁ (insert ψ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
    Da.wk (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  have hOr : Provable (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
      (insert (ψ₁ ⋎ ψ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    Provable.orI ψ₁ ψ₂ (lt_of_le_of_lt hale (add_osucc_descent hαNF hβNF hγNF hβ))
      haNF hsuccNF hanorm Da'
  refine ProvableSlack.of hsuccNF
    (lt_of_le_of_lt norm_osucc_le (by have := norm_add_le_of_nf hαNF hγNF; omega))
    (hOr.wk (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto))

include hαNF hφc heNF fam in
/-- `cutReduceAllAux`, the `allω` case. -/
private lemma cutReduceAllAux_allω {γ' : ONote} {Γ₀ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {β : ℕ → ONote}
    (hβ : ∀ n, β n < γ') (hβNF : ∀ n, (β n).NF) (hτ : ∀ n, norm (β n) < max k' n + dd')
    (ih : ∀ n, φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      (β n).NF → norm (β n) < max k' n + dd' → k₀ ≤ max k' n → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ insert (χ/[nm n]) Γ₀ →
      ProvableSlack (osucc (α + β n)) e' (max k' n) (dd' + norm α + 1) c'
        ((insert (χ/[nm n]) Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (hk : k₀ ≤ k') (hdd : dd₀ ≤ dd') (hmem : (∃⁰ ∼φ) ∈ insert (∀⁰ χ) Γ₀) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' ((insert (∀⁰ χ) Γ₀).erase (∃⁰ ∼φ) ∪ Γ) := by
  have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
  have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
  have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
  have ihn : ∀ n, ProvableSlack (osucc (α + β n)) e' (max k' n) (dd' + norm α + 1) c'
      (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
    intro n
    exact (ih n hφc heNF fam (hβNF n) (by have := hτ n; omega)
      (le_trans hk (le_max_left _ _)) hdd (Finset.mem_insert_of_mem hmem0)).weakening (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  choose β' hβ'le hβ'NF hβ'norm Dβ' using ihn
  have hAll : Provable (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
      (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    Provable.allω χ β'
      (fun n => lt_of_le_of_lt (hβ'le n) (add_osucc_descent hαNF (hβNF n) hγNF (hβ n)))
      hβ'NF hsuccNF hβ'norm Dβ'
  refine ProvableSlack.of hsuccNF
    (lt_of_le_of_lt norm_osucc_le (by have := norm_add_le_of_nf hαNF hγNF; omega))
    (hAll.wk (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl ⟨hhead, Or.inl rfl⟩
      · tauto))

include hαNF hφc heNF fam in
/-- `cutReduceAllAux`, the `exI` case. -/
private lemma cutReduceAllAux_exI {γ' β : ONote} {Γ₀ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticSemiformula ℕ 1} {n : ℕ}
    (hβ : β < γ') (hβNF : β.NF) (hτ : norm β < k' + dd') (hbound : n ≤ hardy e' (k' + dd'))
    (dχ : Provable β e' k' dd' c' (insert (χ/[nm n]) Γ₀))
    (ih : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      β.NF → norm β < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ insert (χ/[nm n]) Γ₀ →
      ProvableSlack (osucc (α + β)) e' k' (dd' + norm α + 1) c' ((insert (χ/[nm n]) Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (hk : k₀ ≤ k') (hdd : dd₀ ≤ dd') (hmem : (∃⁰ ∼φ) ∈ insert (∃⁰ χ) Γ₀) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' ((insert (∃⁰ χ) Γ₀).erase (∃⁰ ∼φ) ∪ Γ) := by
  have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
  by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
  · -- principal exI: χ = ∼φ; cut `fam n` against the ∃-premise at the cut formula `φ/[nm n]`.
    have hχ : χ = ∼φ := by have := hhd; simpa [ExsQuantifier.exs] using this
    subst hχ
    rw [Finset.erase_insert_eq_erase]
    have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
    have hcompl : (φ/[nm n]).complexity < c' := by simpa using hφc
    have hαlt : α < osucc (α + γ') :=
      lt_of_le_of_lt (le_add_right_NF hαNF hγNF) (lt_osucc (ONote.add_nf α γ'))
    have famn : Provable α e' k' (dd' + norm α + 1) c'
        (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      (((fam n).mono_k hk).mono_d (by omega)).wk (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
    by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
    · obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hd)
      have Da' : Provable a e' k' (dd' + norm α + 1) c'
          (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Da.wk (by
          intro x hx
          simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have hCut : Provable (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
        Provable.cut (φ/[nm n]) hcompl hαlt
          (lt_of_le_of_lt hale (add_osucc_descent hαNF hβNF hγNF hβ))
          hαNF haNF hsuccNF (by omega) hanorm famn Da'
      exact ProvableSlack.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := norm_add_le_of_nf hαNF hγNF; omega)) hCut
    · have Dβ' : Provable β e' k' (dd' + norm α + 1) c'
          (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        (dχ.mono_d (by omega)).wk (by
          intro x hx
          simp only [hNeg, Finset.mem_insert] at hx
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
          rcases hx with rfl | hxΓ₀
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
      have hCut : Provable (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
        Provable.cut (φ/[nm n]) hcompl hαlt
          (lt_of_lt_of_le hβ (le_trans (le_add_left_NF hαNF hγNF)
            (le_of_lt (lt_osucc (ONote.add_nf α γ')))))
          hαNF hβNF hsuccNF (by omega) (by omega) famn Dβ'
      exact ProvableSlack.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := norm_add_le_of_nf hαNF hγNF; omega)) hCut
  · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
    obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
      (Finset.mem_insert_of_mem hmem0)
    have Da' : Provable a e' k' (dd' + norm α + 1) c' (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      Da.wk (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
    have hExI : Provable (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
        (insert (∃⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
      Provable.exI χ n (lt_of_le_of_lt hale (add_osucc_descent hαNF hβNF hγNF hβ))
        haNF hsuccNF hanorm (le_trans hbound (hardy_monotone _ (by omega))) Da'
    refine ProvableSlack.of hsuccNF
      (lt_of_le_of_lt norm_osucc_le (by have := norm_add_le_of_nf hαNF hγNF; omega))
      (hExI.wk (by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl ⟨hhd, Or.inl rfl⟩
        · tauto))

include hαNF hφc heNF fam in
/-- `cutReduceAllAux`, the `cut` case. -/
private lemma cutReduceAllAux_cut {γ' βφ βψ : ONote} {Γ₀ : Finset (ArithmeticFormula ℕ)}
    {χ : ArithmeticFormula ℕ} (hχc : χ.complexity < c') (hβφ : βφ < γ') (hβψ : βψ < γ')
    (hβφNF : βφ.NF) (hβψNF : βψ.NF) (hτφ : norm βφ < k' + dd') (hτψ : norm βψ < k' + dd')
    (ih₁ : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      βφ.NF → norm βφ < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ insert χ Γ₀ →
      ProvableSlack (osucc (α + βφ)) e' k' (dd' + norm α + 1) c' ((insert χ Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (ih₂ : φ.complexity < c' → e'.NF → (∀ n, Provable α e' k₀ dd₀ c' (insert (φ/[nm n]) Γ)) →
      βψ.NF → norm βψ < k' + dd' → k₀ ≤ k' → dd₀ ≤ dd' → (∃⁰ ∼φ) ∈ insert (∼χ) Γ₀ →
      ProvableSlack (osucc (α + βψ)) e' k' (dd' + norm α + 1) c' ((insert (∼χ) Γ₀).erase (∃⁰ ∼φ) ∪ Γ))
    (hγNF : γ'.NF) (hγb : norm γ' < k' + dd') (hk : k₀ ≤ k') (hdd : dd₀ ≤ dd') (hmem : (∃⁰ ∼φ) ∈ Γ₀) :
    ProvableSlack (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) := by
  obtain ⟨a₁, ha₁le, ha₁NF, ha₁norm, D₁⟩ := ih₁ hφc heNF fam hβφNF (by omega) hk hdd
    (Finset.mem_insert_of_mem hmem)
  obtain ⟨a₂, ha₂le, ha₂NF, ha₂norm, D₂⟩ := ih₂ hφc heNF fam hβψNF (by omega) hk hdd
    (Finset.mem_insert_of_mem hmem)
  have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
  have D₁' : Provable a₁ e' k' (dd' + norm α + 1) c' (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    D₁.wk (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  have D₂' : Provable a₂ e' k' (dd' + norm α + 1) c' (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
    D₂.wk (by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
  have hCut : Provable (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
    Provable.cut χ hχc
      (lt_of_le_of_lt ha₁le (add_osucc_descent hαNF hβφNF hγNF hβφ))
      (lt_of_le_of_lt ha₂le (add_osucc_descent hαNF hβψNF hγNF hβψ))
      ha₁NF ha₂NF hsuccNF ha₁norm ha₂norm D₁' D₂'
  exact ProvableSlack.of hsuccNF
    (lt_of_le_of_lt norm_osucc_le (by have := norm_add_le_of_nf hαNF hγNF; omega)) hCut

lemma cutReduceAllAux {φ : ArithmeticSemiformula ℕ 1} {c k₀ dd₀ : ℕ} {α e : ONote} {Γ : Finset (ArithmeticFormula ℕ)}
    (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (fam : ∀ n, Provable α e k₀ dd₀ c (insert (φ/[nm n]) Γ))
    {γ : ONote} {k dd : ℕ} {Δ : Finset (ArithmeticFormula ℕ)} (D : Provable γ e k dd c Δ) (hγNF : γ.NF)
    (hγb : norm γ < k + dd) (hk : k₀ ≤ k) (hdd : dd₀ ≤ dd) (hmem : (∃⁰ ∼φ) ∈ Δ) :
    ProvableSlack (osucc (α + γ)) e k (dd + norm α + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  induction D with
  | axL r v hp hn => exact cutReduceAllAux_axL r v hp hn
  | verumR h => exact cutReduceAllAux_verumR h
  | trueRel r v htrue hτ hαNF' hmemA => exact cutReduceAllAux_trueRel hαNF hγNF hγb r v htrue hmemA
  | trueNrel r v htrue hτ hαNF' hmemA => exact cutReduceAllAux_trueNrel hαNF hγNF hγb r v htrue hmemA
  | @wk γ' e' k' dd' c' Δsub Δsup hsub D' ih =>
      exact cutReduceAllAux_wk hαNF hφc heNF fam hsub D' ih hγNF hγb hk hdd hmem
  | @weak γ' β e' k' dd' c' Δsub Δsup hβ hβNF hαNF' hτ hsub D' ih =>
      exact cutReduceAllAux_weak hαNF hφc heNF fam hβ hβNF hτ hsub D' ih hγNF hk hdd hmem
  | @andI γ' βφ βψ e' k' dd' c' Γ₀ ψ₁ ψ₂ hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ dφ dψ ihφ ihψ =>
      exact cutReduceAllAux_andI hαNF hφc heNF fam hβφ hβψ hβφNF hβψNF hτφ hτψ ihφ ihψ hγNF hγb hk hdd hmem
  | @orI γ' β e' k' dd' c' Γ₀ ψ₁ ψ₂ hβ hβNF hαNF' hτ dχ ih =>
      exact cutReduceAllAux_orI hαNF hφc heNF fam hβ hβNF hτ ih hγNF hγb hk hdd hmem
  | @allω γ' e' k' dd' c' Γ₀ χ β hβ hβNF hαNF' hτ dχ ih =>
      exact cutReduceAllAux_allω hαNF hφc heNF fam hβ hβNF hτ ih hγNF hγb hk hdd hmem
  | @exI γ' β e' k' dd' c' Γ₀ χ n hβ hβNF hαNF' hτ hbound dχ ih =>
      exact cutReduceAllAux_exI hαNF hφc heNF fam hβ hβNF hτ hbound dχ ih hγNF hγb hk hdd hmem
  | @cut γ' βφ βψ e' k' dd' c' Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ d₁ d₂ ih₁ ih₂ =>
      exact cutReduceAllAux_cut hαNF hφc heNF fam hχc hβφ hβψ hβφNF hβψNF hτφ hτψ ih₁ ih₂ hγNF hγb hk hdd hmem

end GoodsteinPA.OperatorZinfty
