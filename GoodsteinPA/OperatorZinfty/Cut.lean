module

public import GoodsteinPA.OperatorZinfty.Inversion

@[expose] public section

namespace GoodsteinPA.OperatorZinfty

open LO LO.FirstOrder ONote

namespace Zekd

/-- **∧/∨ cut reduction, conjunction case** (Towsner §19.5). -/
theorem cutReduceConj {a b : Form} {c k d : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Zekd α e k d c (insert (a ⋏ b) Γ)) (hNC : Zekd β e k d c (insert (∼a ⋎ ∼b) Γ)) :
    Zekd (osucc δ) e k d c Γ := by
  have hA : Zekd α e k d c (insert a Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvL (Finset.mem_insert_self _ _))
  have hB : Zekd α e k d c (insert b Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.andInvR (Finset.mem_insert_self _ _))
  have hNab : Zekd β e k d c (insert (∼a) (insert (∼b) Γ)) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.orInv (Finset.mem_insert_self _ _))
  have cutA : Zekd δ e k d c (insert (∼b) Γ) :=
    Zekd.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ
      (Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hA) hNab
  exact Zekd.cut b hb (lt_trans hαδ (lt_osucc hδNF)) (lt_osucc hδNF) hαNF hδNF (osucc_NF hδNF)
    hτα hτδ hB cutA

/-- **∧/∨ cut reduction, disjunction case** (dual). -/
theorem cutReduceDisj {a b : Form} {c k d : ℕ} {α β δ e : ONote} {Γ : Seq}
    (ha : a.complexity < c) (hb : b.complexity < c)
    (hαδ : α < δ) (hβδ : β < δ) (hαNF : α.NF) (hβNF : β.NF) (hδNF : δ.NF)
    (hτα : norm α < k + d) (hτβ : norm β < k + d) (hτδ : norm δ < k + d)
    (hC : Zekd α e k d c (insert (a ⋎ b) Γ)) (hNC : Zekd β e k d c (insert (∼a ⋏ ∼b) Γ)) :
    Zekd (osucc δ) e k d c Γ := by
  have hAB : Zekd α e k d c (insert a (insert b Γ)) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hC.orInv (Finset.mem_insert_self _ _))
  have hNa : Zekd β e k d c (insert (∼a) Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvL (Finset.mem_insert_self _ _))
  have hNb : Zekd β e k d c (insert (∼b) Γ) := Zekd.wk
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto)
    (hNC.andInvR (Finset.mem_insert_self _ _))
  have cutA : Zekd δ e k d c (insert b Γ) :=
    Zekd.cut a ha hαδ hβδ hαNF hβNF hδNF hτα hτβ hAB
      (Zekd.wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) hNa)
  exact Zekd.cut b hb (lt_osucc hδNF) (lt_trans hβδ (lt_osucc hδNF)) hδNF hβNF (osucc_NF hδNF)
    hτδ hτβ cutA hNb


end Zekd

/-! ### `ZekdProv` — the `Provable`-style wrapper (bound-as-upper-bound)

`Zekd` carries an *exact* derivation ordinal, so every ordinal-raise (e.g. `wk`'s
`γ ↦ osucc(α+γ)` in cut-elimination) needs `NF` of the source. The wrapper bundles an upper
bound + the source's `NF`, so the `≤`-slack absorbs the `osucc`/`+1` bookkeeping uniformly and
`NF` is always available. This is the surface §19.6 `cutReduceAll` is stated over (matching the
unbounded `Zinfty.lean Provable`). -/
def ZekdProv (α e : ONote) (k d c : ℕ) (Γ : Seq) : Prop :=
  ∃ α', α' ≤ α ∧ α'.NF ∧ norm α' < k + d ∧ Zekd α' e k d c Γ

namespace ZekdProv

/-- Monotonicity in `α` (≤), `k`, `d`, `c` (the control `e` is raised separately by `mono_e`,
which carries a budget side condition). The carried norm bound `norm α' < k+d` rides up to `k'+d'`. -/
theorem mono {α β e : ONote} {k d c k' d' c' : ℕ} {Γ : Seq}
    (hα : α ≤ β) (hk : k ≤ k') (hd : d ≤ d') (hc : c ≤ c') :
    ZekdProv α e k d c Γ → ZekdProv β e k' d' c' Γ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', le_trans hα' hα, hNF, by omega, ((D.mono_k hk).mono_d hd).mono_c hc⟩

/-- Control-ordinal raising at the wrapper level. -/
theorem mono_e {α e e' : ONote} {k d c : ℕ} {Γ : Seq}
    (heNF : e.NF) (he'NF : e'.NF) (hlt : e < e') (hbudget : norm e ≤ k + d) :
    ZekdProv α e k d c Γ → ZekdProv α e' k d c Γ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', hα', hNF, hnorm, D.mono_e heNF he'NF hlt hbudget⟩

/-- Sequent weakening. -/
theorem weakening {α e : ONote} {k d c : ℕ} {Γ Δ : Seq} (h : Γ ⊆ Δ) :
    ZekdProv α e k d c Γ → ZekdProv α e k d c Δ := by
  rintro ⟨α', hα', hNF, hnorm, D⟩
  exact ⟨α', hα', hNF, hnorm, D.wk h⟩

/-- Respect set-equality of sequents. -/
theorem cast {α e : ONote} {k d c : ℕ} {Γ Δ : Seq} (e0 : Γ = Δ) :
    ZekdProv α e k d c Γ → ZekdProv α e k d c Δ := fun h => e0 ▸ h

/-- Lift a raw `Zekd` derivation (NF ordinal + norm bound) into the wrapper. -/
theorem of {α e : ONote} {k d c : ℕ} {Γ : Seq} (hNF : α.NF) (hnorm : norm α < k + d)
    (D : Zekd α e k d c Γ) : ZekdProv α e k d c Γ := ⟨α, le_refl _, hNF, hnorm, D⟩

end ZekdProv

/-! ### §19.6 ∀/∃ cut reduction `cutReduceAllAux` — **norm-budget half PROVED** (lap 12, axiom-clean)

The induction core of Towsner §19.6, ported from `src/Zinfty.lean:854 cutReduceAllAux` to the
control-ordinal witness-bounded calculus over the **norm-carrying** `ZekdProv` wrapper. Cut the
∀-inversion family `fam` (over `φ`, control `e`, index `(k₀,dd₀)`) against an ∃-side derivation
`D : Zekd γ e k dd c Δ` containing `∃∼φ`, producing a `Zekd`-derivation of `Δ.erase(∃∼φ) ∪ Γ` at
ordinal `osucc(α+γ)`, control `e` (inert), index `(k, dd+norm α+1)`.

⚠️ **SCOPE (lap-12, see `ANALYSIS-…-cutelim-k-threading.md` ADDENDUM 7).** This statement takes `fam`
at the **FIXED** index `k₀` and keeps `e` inert — proving the NORM-budget half cleanly (the lap-6→11
friction), but it is **NOT yet feedable by `cutReduceAll`**: `allInv` produces the ∀-family at the
*running* index `max k₀ n` (the n-th ω-premise lives higher), and a derivation with witnesses up to
`hardy e (max k₀ n + dd₀)` does NOT exist at the smaller fixed index `k₀`. Closing the **witness-budget**
half needs `fam` at `max k₀ n` AND the control `e` *raised* — the numeric single-index bound is provably
FALSE (`h_{βₙ#ω}(max{k,n}) ≰ max{h_{β#ω}(k),n}` for large `n`). The literature-correct fix is Buchholz
**operator-controlled** derivations (on disk: `papers/buchholz-beweistheorie-skriptum.pdf`). This proof
is the reusable **norm-machinery + structural port**: every case carries to the `H`-calculus verbatim
except the `exI`/`allω` witness side-condition (`n ≤ hardy e (k+d)` ⤳ `n ∈ H`). Banked, off the live chain.

**Norm-budget resolution (the lap-6→11 friction; see ADDENDUM 6).** The historical blocker — the
commuting `allω` norm budget — is closed by THREE coupled moves:
1. **norm-carrying wrapper** `ZekdProv α e k d c Γ := ∃ α', α'≤α ∧ α'.NF ∧ norm α'<k+d ∧ Zekd α' …`,
   so the IH EXPOSES `norm α' < (its k)+(its d)` — exactly the `allω` premise's norm budget (a plain
   `α'≤α` wrapper threw this away, since `norm` is not `≤`-monotone — the 5-lap wall);
2. **thread `norm γ < k+dd`** through the induction (each case's child budget is supplied by that rule's
   own `hτ` side-condition; used only to bound `norm(osucc(α+γ))` at the result);
3. **d-bump `dd ↦ dd+norm α+1`** — the `+1` absorbs the `osucc`, giving STRICT budgets everywhere
   (and killing the leaf `k+dd=0` edge). Control `e` stays inert (witnesses stay `≤ hardy e (·)`); it is
   raised only at the top-level cut in `cutReduceAll` via `mono_e`.

`induction D` generalizes `e k dd c Δ` (and reverts `fam`/`heNF`/`hφc`, re-supplied per-case via the
IH), keeping `α k₀ dd₀ Γ φ hαNF` fixed — the `allInv` precedent scaled to carry the external family. -/
set_option maxHeartbeats 1600000 in
theorem cutReduceAllAux {φ : ArithmeticSemiformula ℕ 1} {c k₀ dd₀ : ℕ} {α e : ONote} {Γ : Seq}
    (hφc : φ.complexity < c) (hαNF : α.NF) (heNF : e.NF)
    (fam : ∀ n, Zekd α e k₀ dd₀ c (insert (φ/[nm n]) Γ)) :
    ∀ {γ : ONote} {k dd : ℕ} {Δ : Seq}, Zekd γ e k dd c Δ → γ.NF → norm γ < k + dd →
      k₀ ≤ k → dd₀ ≤ dd → (∃⁰ ∼φ) ∈ Δ →
      ZekdProv (osucc (α + γ)) e k (dd + norm α + 1) c (Δ.erase (∃⁰ ∼φ) ∪ Γ) := by
  intro γ k dd Δ D
  induction D with
  | axL r v hp hn =>
      intro hγNF hγb hk hdd hmem
      exact ⟨0, le_def.mpr (by simp), NF.zero, by simp only [norm_zero]; omega, Zekd.axL r v
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩))
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩))⟩
  | verumR h =>
      intro hγNF hγb hk hdd hmem
      exact ⟨0, le_def.mpr (by simp), NF.zero, by simp only [norm_zero]; omega, Zekd.verumR
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩))⟩
  | trueRel r v htrue hτ hαNF' hmemA =>
      intro hγNF hγb hk hdd hmem
      refine ⟨_, le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
        hγNF, by omega, Zekd.trueRel r v htrue (by omega) hγNF
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩
  | trueNrel r v htrue hτ hαNF' hmemA =>
      intro hγNF hγb hk hdd hmem
      refine ⟨_, le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
        hγNF, by omega, Zekd.trueNrel r v htrue (by omega) hγNF
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hmemA⟩))⟩
  | @wk γ' e' k' dd' c' Δsub Δsup hsub D' ih =>
      intro hγNF hγb hk hdd hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact (ih hφc heNF fam hγNF hγb hk hdd hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)
      · refine ⟨γ', le_trans (Zekd.le_add_left_NF hαNF hγNF) (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))),
          hγNF, by omega, (D'.mono_d (by omega)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @weak γ' β e' k' dd' c' Δsub Δsup hβ hβNF hαNF' hτ hsub D' ih =>
      intro hγNF hγb hk hdd hmem
      by_cases hd : (∃⁰ ∼φ) ∈ Δsub
      · exact ((ih hφc heNF fam hβNF (by omega) hk hdd hd).weakening (by
          intro x hx; simp only [Finset.mem_union, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨hne, hxs⟩ | hxΓ
          · exact Or.inl ⟨hne, hsub hxs⟩
          · exact Or.inr hxΓ)).mono
          (le_of_lt (Zekd.add_osucc_descent hαNF hβNF hγNF hβ)) le_rfl le_rfl le_rfl
      · refine ⟨β, le_of_lt (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
          (le_of_lt (Zekd.lt_osucc (ONote.add_nf α _))))), hβNF, by omega,
          (D'.mono_d (by omega)).wk (by
            intro x hx; simp only [Finset.mem_union, Finset.mem_erase]
            exact Or.inl ⟨fun e0 => hd (e0 ▸ hx), hsub hx⟩)⟩
  | @andI γ' βφ βψ e' k' dd' c' Γ₀ ψ₁ ψ₂ hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ dφ dψ ihφ ihψ =>
      intro hγNF hγb hk hdd hmem
      have hhead : (ψ₁ ⋏ ψ₂) ≠ (∃⁰ ∼φ) := by intro h; simp [Wedge.wedge, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      obtain ⟨aφ, haφle, haφNF, haφnorm, Dφ⟩ := ihφ hφc heNF fam hβφNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem0)
      obtain ⟨aψ, haψle, haψNF, haψnorm, Dψ⟩ := ihψ hφc heNF fam hβψNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem0)
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have Dφ' : Zekd aφ e' k' (dd' + norm α + 1) c' (insert ψ₁ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Dφ.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have Dψ' : Zekd aψ e' k' (dd' + norm α + 1) c' (insert ψ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Dψ.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have hAnd : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
          (insert (ψ₁ ⋏ ψ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zekd.andI ψ₁ ψ₂
          (lt_of_le_of_lt haφle (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
          (lt_of_le_of_lt haψle (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
          haφNF haψNF hsuccNF haφnorm haψnorm Dφ' Dψ'
      refine ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
        (hAnd.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhead, Or.inl rfl⟩
          · tauto))
  | @orI γ' β e' k' dd' c' Γ₀ ψ₁ ψ₂ hβ hβNF hαNF' hτ dχ ih =>
      intro hγNF hγb hk hdd hmem
      have hhead : (ψ₁ ⋎ ψ₂) ≠ (∃⁰ ∼φ) := by intro h; simp [Vee.vee, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have Da' : Zekd a e' k' (dd' + norm α + 1) c'
          (insert ψ₁ (insert ψ₂ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ))) :=
        Da.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have hOr : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
          (insert (ψ₁ ⋎ ψ₂) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zekd.orI ψ₁ ψ₂ (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
          haNF hsuccNF hanorm Da'
      refine ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
        (hOr.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhead, Or.inl rfl⟩
          · tauto))
  | @allω γ' e' k' dd' c' Γ₀ χ β hβ hβNF hαNF' hτ dχ ih =>
      intro hγNF hγb hk hdd hmem
      have hhead : (∀⁰ χ) ≠ (∃⁰ ∼φ) := by intro h; simp [UnivQuantifier.all, ExsQuantifier.exs] at h
      have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have ihn : ∀ n, ZekdProv (osucc (α + β n)) e' (max k' n) (dd' + norm α + 1) c'
          (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) := by
        intro n
        exact (ih n hφc heNF fam (hβNF n) (by have := hτ n; omega)
          (le_trans hk (le_max_left _ _)) hdd (Finset.mem_insert_of_mem hmem0)).weakening (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      choose β' hβ'le hβ'NF hβ'norm Dβ' using ihn
      have hAll : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
          (insert (∀⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        Zekd.allω χ β'
          (fun n => lt_of_le_of_lt (hβ'le n) (Zekd.add_osucc_descent hαNF (hβNF n) hγNF (hβ n)))
          hβ'NF hsuccNF hβ'norm Dβ'
      refine ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
        (hAll.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl ⟨hhead, Or.inl rfl⟩
          · tauto))
  | @exI γ' β e' k' dd' c' Γ₀ χ n hβ hβNF hαNF' hτ hbound dχ ih =>
      intro hγNF hγb hk hdd hmem
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      by_cases hhd : (∃⁰ χ) = (∃⁰ ∼φ)
      · -- principal exI: χ = ∼φ; cut `fam n` against the ∃-premise at the cut formula `φ/[nm n]`.
        have hχ : χ = ∼φ := by have := hhd; simpa [ExsQuantifier.exs] using this
        subst hχ
        rw [Finset.erase_insert_eq_erase]
        have hNeg : (∼φ)/[nm n] = ∼(φ/[nm n]) := by simp
        have hcompl : (φ/[nm n]).complexity < c' := by simpa using hφc
        have hαlt : α < osucc (α + γ') :=
          lt_of_le_of_lt (Zekd.le_add_right_NF hαNF hγNF) (Zekd.lt_osucc (ONote.add_nf α γ'))
        have famn : Zekd α e' k' (dd' + norm α + 1) c'
            (insert (φ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          (((fam n).mono_k hk).mono_d (by omega)).wk (by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_union] at hx ⊢; tauto)
        by_cases hd : (∃⁰ ∼φ) ∈ Γ₀
        · obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
            (Finset.mem_insert_of_mem hd)
          have Da' : Zekd a e' k' (dd' + norm α + 1) c'
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            Da.wk (by
              intro x hx
              simp only [hNeg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
          have hCut : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
            Zekd.cut (φ/[nm n]) hcompl hαlt
              (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
              hαNF haNF hsuccNF (by omega) hanorm famn Da'
          exact ZekdProv.of hsuccNF
            (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega)) hCut
        · have Dβ' : Zekd β e' k' (dd' + norm α + 1) c'
              (insert (∼(φ/[nm n])) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
            (dχ.mono_d (by omega)).wk (by
              intro x hx
              simp only [hNeg, Finset.mem_insert] at hx
              simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
              rcases hx with rfl | hxΓ₀
              · exact Or.inl rfl
              · exact Or.inr (Or.inl ⟨fun e0 => hd (e0 ▸ hxΓ₀), hxΓ₀⟩))
          have hCut : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
            Zekd.cut (φ/[nm n]) hcompl hαlt
              (lt_of_lt_of_le hβ (le_trans (Zekd.le_add_left_NF hαNF hγNF)
                (le_of_lt (Zekd.lt_osucc (ONote.add_nf α γ')))))
              hαNF hβNF hsuccNF (by omega) (by omega) famn Dβ'
          exact ZekdProv.of hsuccNF
            (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega)) hCut
      · have hmem0 : (∃⁰ ∼φ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
        obtain ⟨a, hale, haNF, hanorm, Da⟩ := ih hφc heNF fam hβNF (by omega) hk hdd
          (Finset.mem_insert_of_mem hmem0)
        have Da' : Zekd a e' k' (dd' + norm α + 1) c' (insert (χ/[nm n]) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Da.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
        have hExI : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c'
            (insert (∃⁰ χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
          Zekd.exI χ n (lt_of_le_of_lt hale (Zekd.add_osucc_descent hαNF hβNF hγNF hβ))
            haNF hsuccNF hanorm (le_trans hbound (hardy_monotone _ (by omega))) Da'
        refine ZekdProv.of hsuccNF
          (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega))
          (hExI.wk (by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢
            rcases hx with rfl | hx
            · exact Or.inl ⟨hhd, Or.inl rfl⟩
            · tauto))
  | @cut γ' βφ βψ e' k' dd' c' Γ₀ χ hχc hβφ hβψ hβφNF hβψNF hαNF' hτφ hτψ d₁ d₂ ih₁ ih₂ =>
      intro hγNF hγb hk hdd hmem
      obtain ⟨a₁, ha₁le, ha₁NF, ha₁norm, D₁⟩ := ih₁ hφc heNF fam hβφNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem)
      obtain ⟨a₂, ha₂le, ha₂NF, ha₂norm, D₂⟩ := ih₂ hφc heNF fam hβψNF (by omega) hk hdd
        (Finset.mem_insert_of_mem hmem)
      have hsuccNF : (osucc (α + γ')).NF := osucc_NF (ONote.add_nf α γ')
      have D₁' : Zekd a₁ e' k' (dd' + norm α + 1) c' (insert χ (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₁.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have D₂' : Zekd a₂ e' k' (dd' + norm α + 1) c' (insert (∼χ) (Γ₀.erase (∃⁰ ∼φ) ∪ Γ)) :=
        D₂.wk (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hx ⊢; tauto)
      have hCut : Zekd (osucc (α + γ')) e' k' (dd' + norm α + 1) c' (Γ₀.erase (∃⁰ ∼φ) ∪ Γ) :=
        Zekd.cut χ hχc
          (lt_of_le_of_lt ha₁le (Zekd.add_osucc_descent hαNF hβφNF hγNF hβφ))
          (lt_of_le_of_lt ha₂le (Zekd.add_osucc_descent hαNF hβψNF hγNF hβψ))
          ha₁NF ha₂NF hsuccNF ha₁norm ha₂norm D₁' D₂'
      exact ZekdProv.of hsuccNF
        (lt_of_le_of_lt norm_osucc_le (by have := Zekd.norm_add_le hαNF hγNF; omega)) hCut

end GoodsteinPA.OperatorZinfty
