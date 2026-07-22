module

public import GoodsteinPA.Zef2TC.Readoff

@[expose] public section

namespace GoodsteinPA.E1EmbeddingGrind

open LO LO.FirstOrder LO.FirstOrder.ArithmeticTerm ONote
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty
open GoodsteinPA.ReadoffValueGate (Gated Gated_and_iff Gated_or_iff Gated_all_iff Gated_exs_iff
  Gated_mono)

/-- If the read-off pipeline's instance body `goodsteinBodyE/[nm m]` unfolds to `∃⁰ χ` and
`χ/[nm n]` is a true numeral instance, then `n` bounds the actual Goodstein sequence length
`goodsteinLength m`. -/
lemma goodsteinBodyE_semantic_link {m n : ℕ} {χ : ArithmeticSemiformula ℕ 1}
    (hχ : goodsteinBodyE/[nm m] = (∃⁰ χ)) (h : atomTrue (χ/[nm n])) :
    Goodstein.Dom.goodsteinLength m ≤ n := by
  have hbody := Semiformula.exs.inj hχ
  rw [← hbody] at h
  have h' : atomTrue ((((Rew.subst (L := ℒₒᵣ) ![nm m]).q ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹
        (((↑(LO.FirstOrder.Arithmetic.igoodsteinDef))/[(‘0’ : Semiterm ℒₒᵣ Empty 2), #1, #0])
          : ArithmeticSemisentence 2))) : ArithmeticSemiformula ℕ 1)/[nm n]) := h
  apply Goodstein.Dom.goodsteinLength_le (m := m) (N := n)
  rw [← GoodsteinPA.InternalPow.igoodstein_nat]
  simp only [atomTrue, Semiformula.eval_rew, Function.comp_def] at h'
  have hcast : ∀ (E : Fin 3 → ℕ) (ε₁ ε₂ : Empty → ℕ),
      Semiformula.gEval (Arithmetic.standardModel ℕ) E ε₁
        (↑(LO.FirstOrder.Arithmetic.igoodsteinDef)) →
      Semiformula.gEval (Arithmetic.standardModel ℕ) E ε₂
        (↑(LO.FirstOrder.Arithmetic.igoodsteinDef)) := by
    intro E ε₁ ε₂ hh
    rwa [show ε₂ = ε₁ from funext fun a => a.elim]
  have h'' := hcast _ _ Empty.elim h'
  have hkey := GoodsteinPA.InternalPow.igoodstein_defined.iff.mp h''
  have hq1 : ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #1 : ArithmeticSemiterm ℕ 1)
      = Rew.bShift (nm m) := by
    show (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #(Fin.succ 0) = _
    rw [Rew.q_bvar_succ]
    simp
  -- `hkey` (post-`simp`) carries a bare `Semiterm.val`; state `hval` in the same form (the ℕ-model's
  -- `Structure ℒₒᵣ ℕ` instance IS `standardModel ℕ`) so the `rw` matches, not via the `gVal` shim.
  have hval : Semiterm.val (L := ℒₒᵣ) (ξ := ℕ) (fun _ => n) (fun _ => 0)
      ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #1) = m := by
    rw [hq1]
    simp [Matrix.empty_eq]
  simp at hkey
  rw [hval] at hkey
  simpa using hkey.symm

/-- `readoff_value_pipeline` strengthened with a `Nlog α'` certificate: the collapsed ordinal
`α'` produced by a `Zef2TC` derivation of a singleton `{(∃⁰ φ)}` has `Nlog α'` bounded by the
tower value at `0`, together with the usual read-off witness `n`. -/
lemma readoff_value_pipeline' {φ : ArithmeticSemiformula ℕ 1} {P : ℕ → ℕ}
    (hP_mono : Monotone P)
    {α e : ONote} {H : ONote → Prop} {B K d : ℕ}
    (heNF : e.NF) (hαNF : α.NF) (hαH : Cl H α)
    (D : Zef2TC α e H (rel1 (ewRootSlot e B) K) d {(∃⁰ φ)})
    (V : ℕ) (hroot : Gated P V (∃⁰ φ)) :
    ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
      Nlog α' ≤ ewIterTower (rel1 (ewRootSlot e B) K) d α 0 ∧
      ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P) α'
              (Sslot (ewIterTower (rel1 (ewRootSlot e B) K) d α) P V) ∧
        atomTrue (φ/[nm n]) := by
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) K) := rel1_monotone hf1.monotone K
  have hinfl : ∀ x, x ≤ rel1 (ewRootSlot e B) K x := rel1_infl hf1.infl K
  have hlow : ∀ m, 2 * m + 1 ≤ rel1 (ewRootSlot e B) K m := rel1_low hf1.monotone hf1.2 K
  obtain ⟨α', hα'le, hα'NF, _hα'H, hα'N, D0⟩ :=
    rankToZeroAuxTC e heNF d D hmono hinfl hlow (three_le_rel1_rootSlot e B K) hαNF hαH
  obtain ⟨n, hn, htn⟩ := readoff_value_Zef2TC
    (ewIterTower_monotone hmono hinfl α d) (ewIterTower_infl hinfl α d)
    hP_mono D0 V hroot
  exact ⟨α', hα'le, hα'NF, hα'N, n, hn, htn⟩

/-- The per-`m` slot stage `K_m` of `embedding_Zef2TC_V3` can be taken as `max K₀ m` for a
single `m`-independent `K₀`. -/
lemma embedding_Zef2TC_V3_linearK :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ B d K₀ : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
        ∃ H : ONote → Prop, Cl H α ∧
          Zef2TC α e H (rel1 (ewRootSlot e B) (max K₀ m)) d {(goodsteinBodyE/[nm m])} := by
  intro h
  -- upstream `𝗣𝗔 ⊢ σ` repackages as a `Derivation2 𝗣𝗔 {↑σ}` via `provable_iff_derivable2`
  have hV3 : BudgetedEmbedsV3 {(↑GoodsteinPA.goodsteinSentence : ArithmeticFormula ℕ)} := by
    obtain ⟨d2⟩ := (provable_iff_derivable2 (L := ℒₒᵣ)).mp h
    exact budgetedEmbeddingV3 d2
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, hD⟩ := hV3
  use B, d, envSup (fun _ => 0) N, e, α, he, hαNF
  intro m
  have hD0 := hD (fun _ => 0)
  have himg : ({(↑GoodsteinPA.goodsteinSentence : ArithmeticFormula ℕ)} :
        Finset (ArithmeticFormula ℕ)).image
        (fun φ => asg (fun _ => 0) ▹ φ)
      = {(↑GoodsteinPA.goodsteinSentence : ArithmeticFormula ℕ)} := by
    rw [Finset.image_singleton, asg_emb_fix]
  rw [himg, coe_goodsteinSentence_eq] at hD0
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) (envSup (fun _ => 0) N)) :=
    rel1_monotone hf1.1.monotone _
  have hinv := allω_inversion (φ := goodsteinBodyE) m hD0 hmono
  rw [rel1_rel1] at hinv
  use fun _ => True, Cl_of_NF hαNF
  have hctx : insert (goodsteinBodyE/[nm m])
        (({(∀⁰ goodsteinBodyE : ArithmeticFormula ℕ)} :
          Finset (ArithmeticFormula ℕ)).erase (∀⁰ goodsteinBodyE))
      = {(goodsteinBodyE/[nm m])} := by
    rw [Finset.erase_singleton]
    rfl
  rw [hctx] at hinv
  exact hinv.change_H

/-- `readoff_value_goodstein` strengthened with the `Nlog α'` certificate and the linear slot
stage `max K₀ m` for a single `m`-independent `K₀`. -/
lemma readoff_value_goodstein'
    (h : 𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) :
    ∃ B d K₀ : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
      ∃ χ : ArithmeticSemiformula ℕ 1,
        goodsteinBodyE/[nm m] = (∃⁰ χ) ∧ Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) ∧
        ∀ (P : ℕ → ℕ) (V : ℕ), Monotone P → Gated P V (∃⁰ χ) →
          ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
            Nlog α' ≤ ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α 0 ∧
            ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P)
                    α' (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P V) ∧
              atomTrue (χ/[nm n]) := by
  obtain ⟨B, d, K₀, e, α, heNF, hαNF, hall⟩ := embedding_Zef2TC_V3_linearK h
  use B, d, K₀, e, α, heNF, hαNF
  intro m
  obtain ⟨H, hαH, D⟩ := hall m
  obtain ⟨χ, hχeq, hchiS⟩ := goodsteinBodyE_inst_shape m
  rw [hχeq] at D
  use χ, hχeq, hchiS
  intro P V hP_mono hroot
  exact readoff_value_pipeline' hP_mono heNF hαNF hαH D V hroot

/-- **Wainer classification, specialized to the Goodstein embedding route.** If PA proves the
Goodstein sentence, the Goodstein length function is eventually bounded by a fixed
fast-growing `fastGrowing o` for some `o < ε₀`. The three explicit hypotheses `Hcert`, `HSdom`,
`Hconv` are the verbatim statements of theorems proven independently in sibling modules
(`GoodsteinPA.ReadoffValueGate.gated_certificate_uniform`, `ONote.Scirc_dom_pad`,
`ONote.master_conversion`) that cannot import each other; discharging them here — together
with the read-off pipeline (`readoff_value_goodstein'`), the `m`-uniformization of its slot
stage, and the semantic link (`goodsteinBodyE_semantic_link`) — completes the Wainer bound at
the exact type consumed as `wainer_bound_of_pa_proves_goodstein` in `GoodsteinPA/Statement.lean`.
- [BW87, Theorem I] -/
theorem wainer_bound_witness
    (Hcert : ∀ {G : ℕ → ℕ}, Monotone G → (∀ x, x + 1 ≤ G x) →
      (∀ a b, a + b ≤ G (max a b)) → (∀ a b, a * b ≤ G (max a b)) →
      ∀ (body : ArithmeticSemiformula ℕ 2), ∃ k : ℕ, ∀ (m V : ℕ)
        (χ : ArithmeticSemiformula ℕ 1),
        χ = (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹ body →
        Arithmetic.Hierarchy 𝚺 1 (∃⁰ χ) →
        ∃ P : ℕ → ℕ, Monotone P ∧ Gated P V (∃⁰ χ) ∧
          ∀ z, P z ≤ G^[k] (max (max V m) z))
    (HSdom : ∀ (e : ONote), e.NF → ∀ (Bb d k : ℕ) (α : ONote), α.NF →
      ∃ (E : ONote) (c : ℕ), E.NF ∧ E ≠ 0 ∧
        ∀ z, max (ewIterTower (ewRootSlot e Bb) d α z)
            ((hardy (oadd (ofNat 2) 1 0))^[k] z)
          ≤ hardy (oadd E 1 0) (z + c))
    (Hconv : ∀ {S : ℕ → ℕ} {E_S γ : ONote} {c_S : ℕ}, E_S.NF → E_S ≠ 0 → γ.NF →
      (∀ z, S z ≤ hardy (oadd E_S 1 0) (z + c_S)) → (∀ z, z ≤ S z) → ∀ K₀ : ℕ,
      ∃ o : ONote, o.NF ∧ ∃ N : ℕ, ∀ m, N ≤ m →
        ∀ α' : ONote, α'.NF → α' ≤ γ → ∀ n : ℕ,
          Nlog α' ≤ S (max K₀ m) →
          n ≤ ewIter S α' (S (max K₀ m)) →
          n ≤ fastGrowing o m)
    (h : 𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) :
    ∃ o : ONote, o.NF ∧
      Goodstein.EventuallyLE Goodstein.Dom.goodsteinLength
        (fun n => fastGrowing o n) := by
  obtain ⟨B, d, K₀, e, α, heNF, hαNF, hall⟩ := readoff_value_goodstein' h
  -- ONE iterate count k for the whole numeral family, at the FIXED matrix B₀
  obtain ⟨k, hk⟩ := Hcert (G := Gexp) Gexp_monotone succ_le_Gexp add_le_Gexp_max
    mul_le_Gexp_max
    ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹
      ((((↑(LO.FirstOrder.Arithmetic.igoodsteinDef))/[(‘0’ : Semiterm ℒₒᵣ Empty 2), #1, #0])
        : ArithmeticSemisentence 2)))
  -- the fixed slot S° and its domination
  obtain ⟨E_S, c_S, hES, hES0, hSdom⟩ := HSdom e heNF B d k α hαNF
  have hf1 := ewRootSlot_f1 e B
  have hTmono : Monotone (ewIterTower (ewRootSlot e B) d α) :=
    ewIterTower_monotone hf1.monotone hf1.infl α d
  have hSmono : Monotone (fun x => max (ewIterTower (ewRootSlot e B) d α x)
      ((hardy (oadd (ofNat 2) 1 0))^[k] x)) :=
    fun a b hab => max_le_max (hTmono hab) ((Gexp_iter_monotone k) hab)
  have hSinfl : ∀ x, x ≤ max (ewIterTower (ewRootSlot e B) d α x)
      ((hardy (oadd (ofNat 2) 1 0))^[k] x) :=
    fun x => le_trans (le_Gexp_iter k x) (le_max_right _ _)
  have hγNF : (collapseIter d α).NF := collapseIter_NF hαNF d
  obtain ⟨o, hoNF, N, hN⟩ := Hconv hES hES0 hγNF hSdom hSinfl K₀
  use o, hoNF, N
  intro m hm
  obtain ⟨χ, hχeq, hSig, hmain⟩ := hall m
  have hχB : χ = (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹
        ((((↑(LO.FirstOrder.Arithmetic.igoodsteinDef))/[(‘0’ : Semiterm ℒₒᵣ Empty 2), #1, #0])
          : ArithmeticSemisentence 2))) :=
    (Semiformula.exs.inj hχeq).symm
  obtain ⟨P, hPmono, hPgated, hPle⟩ := hk m 0 χ hχB hSig
  obtain ⟨α', hle, hα'NF, hNcert, n, hn, htrue⟩ := hmain P 0 hPmono hPgated
  have hglen : Goodstein.Dom.goodsteinLength m ≤ n :=
    goodsteinBodyE_semantic_link hχeq htrue
  -- m-uniformization: fold the rel1-staged tower and the per-m P into the fixed slot
  have hT_m : ∀ x, ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α x
      ≤ ewIterTower (ewRootSlot e B) d α (max (max K₀ m) x) :=
    ewIterTower_rel1_le hf1.monotone hf1.infl (max K₀ m) α d
  have hP' : ∀ x, P x ≤ (hardy (oadd (ofNat 2) 1 0))^[k] (max (max K₀ m) x) := by
    intro x
    refine le_trans (hPle x) ((Gexp_iter_monotone k) (by omega))
  have hSl : ∀ x, Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P x
      ≤ rel1 (fun x => max (ewIterTower (ewRootSlot e B) d α x)
          ((hardy (oadd (ofNat 2) 1 0))^[k] x)) (max K₀ m) x :=
    fun x => max_le_max (hT_m x) (hP' x)
  have hrmono := rel1_monotone hSmono (max K₀ m)
  have hrinfl := rel1_infl hSinfl (max K₀ m)
  have hy : Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P 0
      ≤ max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
          ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) := by
    have := hSl 0
    rwa [show rel1 (fun x => max (ewIterTower (ewRootSlot e B) d α x)
        ((hardy (oadd (ofNat 2) 1 0))^[k] x)) (max K₀ m) 0
      = max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
          ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) by
        show (fun x => max _ _) (max (max K₀ m) 0) = _
        rw [Nat.max_zero]] at this
  have h5 := ewIter_mono_slot hSl hrmono hrinfl α'
    (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P 0)
  have h6 := ewIter_monotone hrmono hrinfl α' hy
  have h7 := ewIter_rel1_le hSmono hSinfl α' (max K₀ m)
    (max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
      ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)))
  have h8 : max (max K₀ m) (max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
      ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)))
      = max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
          ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) :=
    max_eq_right (hSinfl (max K₀ m))
  rw [h8] at h7
  have hNcert' : Nlog α' ≤ max (ewIterTower (ewRootSlot e B) d α (max K₀ m))
      ((hardy (oadd (ofNat 2) 1 0))^[k] (max K₀ m)) := by
    refine le_trans hNcert (le_trans ?_ (le_max_left _ _))
    have := hT_m 0
    rwa [Nat.max_zero] at this
  have hfinal : n ≤ ewIter (fun x => max (ewIterTower (ewRootSlot e B) d α x)
      ((hardy (oadd (ofNat 2) 1 0))^[k] x)) α'
      ((fun x => max (ewIterTower (ewRootSlot e B) d α x)
        ((hardy (oadd (ofNat 2) 1 0))^[k] x)) (max K₀ m)) :=
    le_trans hn (le_trans h5 (le_trans h6 h7))
  exact le_trans hglen (hN m hm α' hα'NF hle n hNcert' hfinal)

end GoodsteinPA.E1EmbeddingGrind
