/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.Zef2TC.Wainer
public import GoodsteinPA.ToMathlib.Hardy.Majorization

@[expose] public section

/-!
# Wainer's bound, general form

**Statement.**  If PA proves a Π₂ sentence `∀ m, ∃ N, φ(m, N)` with `φ` a
Σ₁ formula, then a single `f_o` (`o` a normal-form `ONote`, i.e. `o < ε₀`) eventually bounds a
witness: for all large `m` there is `N ≤ f_o(m)` with `φ(m, N)` true in ℕ.  Bound variables:
`#0 = N`, `#1 = m`.  This is the upper half of the Kreisel–Wainer classification of the
PA-provably total functions (Buchholz–Wainer 1987).

**Proof.**  The Goodstein-specific pipeline of `E1EmbeddingGrind` with the sentence abstracted:
the embedding of a PA derivation into the witness-bounded calculus (`budgetedEmbeddingV3`) and the
ω-inversion, rank collapse, value read-off and Hardy conversion never looked at the sentence beyond
its `∀¹ ∃⁰` shape and Σ₁-ness.  Each general lemma below is the verbatim Goodstein proof with
`goodsteinBody` replaced by `∃¹ φ`; the only genuinely new piece is `bodyE_semantic_link`, which
reads the true atom back as `ℕ ⊧/![n, m] φ` instead of through `igoodstein`.
-/

namespace GoodsteinPA.Wainer

open FFL FFL.FirstOrder FFL.FirstOrder.ArithmeticTerm ONote Ordinal
open GoodsteinPA.OperatorZeh GoodsteinPA.OperatorZinfty
open GoodsteinPA.E1EmbeddingGrind GoodsteinPA.ReadoffValueGate

/-- The embedded `∃¹ φ` body (general form of `goodsteinBodyE`). -/
noncomputable def bodyE (φ : Semisentence ℒₒᵣ 2) : Semiformula ℒₒᵣ ℕ 1 :=
  Rewriting.emb (∃¹ φ : Semisentence ℒₒᵣ 1)

/-- The embedded sentence is the ∀-closure of the embedded body (general `coe_goodsteinSentence_eq`). -/
theorem coe_pi2_eq (φ : Semisentence ℒₒᵣ 2) :
    (↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) : Semiformula ℒₒᵣ ℕ 0) = ∀¹ bodyE φ := by
  simp [bodyE, Rewriting.emb]

/-- General `embedding_Zef2TC_V3_linearK`: the per-`m` stage is `max K₀ m` for a uniform `K₀`. -/
theorem embedding_linearK (φ : Semisentence ℒₒᵣ 2) :
    (𝗣𝗔 ⊢ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ)) →
      ∃ B d K₀ : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
        ∃ H : ONote → Prop, Cl H α ∧
          Zef2TC α e H (rel1 (ewRootSlot e B) (max K₀ m)) d {((bodyE φ)/[nm m])} := by
  intro h
  have hV3 : BudgetedEmbedsV3 {(↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) : Semiformula ℒₒᵣ ℕ 0)} := by
    obtain ⟨d2⟩ := (provable_iff_derivable2 (L := ℒₒᵣ)).mp h
    exact budgetedEmbeddingV3 d2
  obtain ⟨B, d, N, e, α, he, hαNF, hNlogB, hD⟩ := hV3
  refine ⟨B, d, envSup (fun _ => 0) N, e, α, he, hαNF, fun m => ?_⟩
  have hD0 := hD (fun _ => 0)
  have himg : ({(↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) : Semiformula ℒₒᵣ ℕ 0)} :
        Finset (Semiformula ℒₒᵣ ℕ 0)).image
        (fun ψ => asg (fun _ => 0) ▹ ψ)
      = {(↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ) : Semiformula ℒₒᵣ ℕ 0)} := by
    rw [Finset.image_singleton, asg_emb_fix]
  rw [himg, coe_pi2_eq] at hD0
  have hf1 := ewRootSlot_f1 e B
  have hmono : Monotone (rel1 (ewRootSlot e B) (envSup (fun _ => 0) N)) :=
    rel1_monotone hf1.1.monotone _
  have hinv := allω_inversion (φ := bodyE φ) m hD0 hmono
  rw [rel1_rel1] at hinv
  refine ⟨fun _ => True, Cl_of_NF hαNF, ?_⟩
  have hctx : insert ((bodyE φ)/[nm m])
        (({(∀¹ bodyE φ : Semiformula ℒₒᵣ ℕ 0)} :
          Finset (Semiformula ℒₒᵣ ℕ 0)).erase (∀¹ bodyE φ))
      = {((bodyE φ)/[nm m])} := by
    rw [Finset.erase_singleton]
    rfl
  rw [hctx] at hinv
  exact hinv.change_H

/-- General `goodsteinBodyE_inst_shape`: the instance is `∃¹ χ` for the substituted matrix, Σ₁. -/
theorem bodyE_inst_shape (φ : Semisentence ℒₒᵣ 2) (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ) (m : ℕ) :
    (bodyE φ)/[nm m] = ∃¹ ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹
        ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹ φ)) ∧
      ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 ((bodyE φ)/[nm m]) := by
  refine ⟨rfl, ?_⟩
  apply Bounding.Hierarchy.rew
  apply Bounding.Hierarchy.rew
  exact Bounding.Hierarchy.exs hφ

/-- General `readoff_value_goodstein'`. -/
theorem readoff_value (φ : Semisentence ℒₒᵣ 2) (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ)
    (h : 𝗣𝗔 ⊢ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ)) :
    ∃ B d K₀ : ℕ, ∃ e α : ONote, e.NF ∧ α.NF ∧ ∀ m : ℕ,
      ∃ χ : Semiformula ℒₒᵣ ℕ 1,
        (bodyE φ)/[nm m] = (∃¹ χ) ∧ ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (∃¹ χ) ∧
        ∀ (P : ℕ → ℕ) (V : ℕ), Monotone P → Gated P V (∃¹ χ) →
          ∃ α', α' ≤ collapseIter d α ∧ α'.NF ∧
            Nlog α' ≤ ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α 0 ∧
            ∃ n, n ≤ ewIter (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P)
                    α' (Sslot (ewIterTower (rel1 (ewRootSlot e B) (max K₀ m)) d α) P V) ∧
              atomTrue (χ/[nm n]) := by
  obtain ⟨B, d, K₀, e, α, heNF, hαNF, hall⟩ := embedding_linearK φ h
  refine ⟨B, d, K₀, e, α, heNF, hαNF, fun m => ?_⟩
  obtain ⟨H, hαH, D⟩ := hall m
  obtain ⟨hχeq, hchiS⟩ := bodyE_inst_shape φ hφ m
  rw [hχeq] at D hchiS
  refine ⟨_, hχeq, hchiS, fun P V hP_mono hroot => ?_⟩
  exact readoff_value_pipeline' hP_mono heNF hαNF hαH D V hroot

/-- **The semantic link**: a true atom at the read-off numeral `n` is a true instance
`ℕ ⊧/![n, m] φ`.  (General form of `goodsteinBodyE_semantic_link`, which instead concluded
`goodsteinLength m ≤ n` through `igoodstein`.) -/
theorem bodyE_semantic_link (φ : Semisentence ℒₒᵣ 2) {m n : ℕ}
    (h : atomTrue ((((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹
        ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹ φ)) : Semiformula ℒₒᵣ ℕ 1)/[nm n])) :
    ℕ ⊧/![n, m] φ := by
  simp only [atomTrue, Semiformula.eval_rew, Function.comp_def] at h
  unfold Semiformula.Evalb
  convert h using 2
  · funext x
    refine Fin.cases ?_ (fun i => ?_) x
    · simp [Rew.q_bvar_zero]
    · rw [Fin.fin_one_eq_zero i]
      have hq1 : ((Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #1 : Semiterm ℒₒᵣ ℕ 1)
          = Rew.bShift (nm m) := by
        show (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q #(Fin.succ 0) = _
        rw [Rew.q_bvar_succ]
        simp
      simp [hq1, Matrix.empty_eq]

/-- General `wainer_bound_witness`: the three hypotheses are, verbatim, the statements of
`ReadoffValueGate.gated_certificate_uniform`, `Scirc_dom_pad` and
`master_conversion` (discharged in `pa_provable_pi2_eventually_witnessed_below_fastGrowing`). -/
theorem wainer_bound_witness_general (φ : Semisentence ℒₒᵣ 2) (hφ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ)
    (Hcert : ∀ {G : ℕ → ℕ}, Monotone G → (∀ x, x + 1 ≤ G x) →
      (∀ a b, a + b ≤ G (max a b)) → (∀ a b, a * b ≤ G (max a b)) →
      ∀ (body : Semiformula ℒₒᵣ ℕ 2), ∃ k : ℕ, ∀ (m V : ℕ)
        (χ : Semiformula ℒₒᵣ ℕ 1),
        χ = (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹ body →
        ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (∃¹ χ) →
        ∃ P : ℕ → ℕ, Monotone P ∧ Gated P V (∃¹ χ) ∧
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
    (h : 𝗣𝗔 ⊢ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ)) :
    ∃ o : ONote, o.NF ∧ ∃ M : ℕ, ∀ m, M ≤ m →
      ∃ N ≤ fastGrowing o m, ℕ ⊧/![N, m] φ := by
  obtain ⟨B, d, K₀, e, α, heNF, hαNF, hall⟩ := readoff_value φ hφ h
  -- ONE iterate count k for the whole numeral family, at the FIXED matrix B₀
  obtain ⟨k, hk⟩ := Hcert (G := Gexp) Gexp_monotone succ_le_Gexp add_le_Gexp_max
    mul_le_Gexp_max
    ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹
      φ)
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
  refine ⟨o, hoNF, N, fun m hm => ?_⟩
  obtain ⟨χ, hχeq, hSig, hmain⟩ := hall m
  have hχB : χ = (Rew.subst (L := ℒₒᵣ) (ξ := ℕ) ![nm m]).q ▹
      ((Rew.emb : Rew ℒₒᵣ Empty 1 ℕ 1).q ▹ φ) :=
    (Semiformula.exs.inj hχeq).symm
  obtain ⟨P, hPmono, hPgated, hPle⟩ := hk m 0 χ hχB hSig
  obtain ⟨α', hle, hα'NF, hNcert, n, hn, htrue⟩ := hmain P 0 hPmono hPgated
  have hsem : ℕ ⊧/![n, m] φ := by
    rw [hχB] at htrue
    exact bodyE_semantic_link φ htrue
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
  exact ⟨n, hN m hm α' hα'NF hle n hNcert' hfinal, hsem⟩

/-- **Wainer's bound.**  If PA proves `∀ m, ∃ N, φ(m, N)` with `φ` Σ₁, then a
single `f_o`, `o < ε₀`, eventually bounds a witness. -/
theorem pa_provable_pi2_eventually_witnessed_below_fastGrowing
    (φ : Semisentence ℒₒᵣ 2) (hφ : Bounding.Hierarchy ℬ[<, ℒₒᵣ] 𝚺 1 φ)
    (h : 𝗣𝗔 ⊢ ↑(∀¹ ∃¹ φ : Sentence ℒₒᵣ)) :
    ∃ o : ONote, o.NF ∧ ∃ M : ℕ, ∀ m, M ≤ m →
      ∃ N ≤ fastGrowing o m, ℕ ⊧/![N, m] φ :=
  wainer_bound_witness_general φ hφ ReadoffValueGate.gated_certificate_uniform
    Scirc_dom_pad master_conversion h

/-! ## The Goodstein instance: the original bound as a corollary -/

/-- The Σ₁ matrix of `goodsteinSentence`: `igoodstein m N = 0`. -/
noncomputable def goodsteinMatrix : Semisentence ℒₒᵣ 2 :=
  (↑(FFL.FirstOrder.Arithmetic.igoodsteinDef) : Semisentence ℒₒᵣ 3)/[(‘0’ : Semiterm ℒₒᵣ Empty 2), #1, #0]

theorem goodsteinSentence_eq_pi2 : GoodsteinPA.goodsteinSentence = ∀¹ ∃¹ goodsteinMatrix := rfl

theorem goodsteinMatrix_sigma1 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 goodsteinMatrix := by
  simp [goodsteinMatrix]

theorem goodsteinMatrix_eval {m N : ℕ} (h : ℕ ⊧/![N, m] goodsteinMatrix) :
    Goodstein.goodsteinSeq m N = 0 := by
  rw [← GoodsteinPA.InternalPow.igoodstein_nat]
  simp [goodsteinMatrix, Semiformula.eval_substs] at h
  exact h.symm

/-- **The Goodstein bound, re-derived from the general theorem** (same type as
`WainerRoute.wainer_bound_of_pa_proves_goodstein`). -/
theorem wainer_bound_of_pa_proves_goodstein_via_general :
    (𝗣𝗔 ⊢ ↑GoodsteinPA.goodsteinSentence) →
      ∃ o : ONote, o.NF ∧ Goodstein.EventuallyLE Goodstein.Dom.goodsteinLength
        (fun n => fastGrowing o n) := by
  intro h
  rw [goodsteinSentence_eq_pi2] at h
  obtain ⟨o, ho, M, hM⟩ :=
    pa_provable_pi2_eventually_witnessed_below_fastGrowing goodsteinMatrix goodsteinMatrix_sigma1 h
  refine ⟨o, ho, M, fun m hm => ?_⟩
  obtain ⟨N, hN, hsem⟩ := hM m hm
  exact le_trans (Goodstein.Dom.goodsteinLength_le (goodsteinMatrix_eval hsem)) hN

end GoodsteinPA.Wainer


end
