module

public import GoodsteinPA.OperatorZinfty
public import GoodsteinPA.ToMathlib.FastGrowing.EWIteration

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## §0 The SPIKE-W4 transforms (LOCK §1 verbatim; `wip/` copies were re-derivations). -/

@[simp] theorem norm_expTower (α : ONote) : norm (expTower α) = max (norm α) 1 :=
  Zekd.norm_omegaPow

/-- SPIKE-W4's family-uniform control raise `raise e α := e + ω^α`. -/
def raise (e α : ONote) : ONote := e + expTower α

theorem raise_NF {e α : ONote} (he : e.NF) (hα : α.NF) : (raise e α).NF := by
  haveI := he; haveI := expTower_NF hα
  exact ONote.add_nf e (expTower α)

theorem raise_lt_raise {e β α : ONote} (he : e.NF) (hβ : β.NF) (hα : α.NF) (h : β < α) :
    raise e β < raise e α :=
  Zekd.add_lt_add_left_NF he (expTower_NF hβ) (expTower_NF hα) (expTower_lt_expTower hβ h)

/-- `ω·(m+1)` as an explicit `ONote` (the W4B two-level-configuration family). -/
def wmul (m : ℕ) : ONote := oadd 1 m.succPNat 0

theorem wmul_NF (m : ℕ) : (wmul m).NF := nf_one.oadd m.succPNat NFBelow.zero

@[simp] theorem norm_one : norm (1 : ONote) = 1 := rfl

@[simp] theorem norm_wmul (m : ℕ) : norm (wmul m) = m + 1 := by
  rw [wmul, norm_oadd, norm_one, norm_zero, Nat.succPNat_coe]
  omega

/-- Equal-exponent CNF merge, parametric (kernel-computed; W4B's rail brick). -/
theorem wmul_add_wmul (a b : ℕ) :
    wmul a + wmul b = oadd 1 (a.succPNat + b.succPNat) 0 := rfl

theorem one_lt_omegaO : (1 : ONote) < ONote.omega :=
  oadd_lt_oadd_1 nf_one ONote.zero_lt_one

theorem omegaO_NF : (ONote.omega).NF := nf_one.oadd 1 NFBelow.zero

theorem wmul_lt_expTower_omega (m : ℕ) : wmul m < expTower ONote.omega :=
  oadd_lt_oadd_1 (wmul_NF m) one_lt_omegaO

/-- Any `oadd 1 K 1`-shaped notation (an `osucc` of an `ω·K` notation) sits below `ω^ω`. -/
theorem osucc_omega_coeff_lt (K : ℕ+) : osucc (oadd 1 K 0) < expTower ONote.omega := by
  have h : (osucc (oadd 1 K 0)).NF := osucc_NF (nf_one.oadd K NFBelow.zero)
  rw [show osucc (oadd 1 K 0) = oadd 1 K 1 from rfl] at h ⊢
  exact oadd_lt_oadd_1 h one_lt_omegaO

theorem osucc_wmul_lt_expTower_omega (m : ℕ) : osucc (wmul m) < expTower ONote.omega :=
  osucc_omega_coeff_lt m.succPNat

/-! ## §1 The operator layer (LOCK §1 verbatim). -/

/-- The pin's closure conditions: closed under `+`, `ω^·` (`expTower`), `osucc`, `ofNat`. -/
structure IsOperator (H : ONote → Prop) : Prop where
  ofNat_mem : ∀ n : ℕ, H (ONote.ofNat n)
  add_mem : ∀ {α β : ONote}, H α → H β → H (α + β)
  expTower_mem : ∀ {α : ONote}, H α → H (expTower α)
  osucc_mem : ∀ {α : ONote}, H α → H (osucc α)

/-- Inductive closure of a generator set under the pin's four operations.  Membership
witnesses are finite trees — the "represented, countable" operator shape. -/
inductive Cl (S : ONote → Prop) : ONote → Prop
  | base {β : ONote} : S β → Cl S β
  | ofNat (n : ℕ) : Cl S (ONote.ofNat n)
  | add {α β : ONote} : Cl S α → Cl S β → Cl S (α + β)
  | expTower {α : ONote} : Cl S α → Cl S (expTower α)
  | osucc {α : ONote} : Cl S α → Cl S (osucc α)

/-- The closure of ANY generator set is an operator (the pin's conditions, verbatim). -/
theorem isOperator_Cl (S : ONote → Prop) : IsOperator (Cl S) where
  ofNat_mem := Cl.ofNat
  add_mem := Cl.add
  expTower_mem := Cl.expTower
  osucc_mem := Cl.osucc

/-- Closure is monotone in the generators (feeds `Zeh.mono_H`). -/
theorem Cl_mono {S S' : ONote → Prop} (h : ∀ β, S β → S' β) :
    ∀ {β : ONote}, Cl S β → Cl S' β := by
  intro β hβ
  induction hβ with
  | base hb => exact Cl.base (h _ hb)
  | ofNat n => exact Cl.ofNat n
  | add _ _ ih₁ ih₂ => exact Cl.add ih₁ ih₂
  | expTower _ ih => exact Cl.expTower ih
  | osucc _ ih => exact Cl.osucc ih

/-- `Cl` is the LEAST operator over its generators: closure membership maps into any
`IsOperator` set containing the generators (the bridge between the abstract-`H` and
generated-`H` formulations of the pin). -/
theorem Cl_sub_of_isOperator {S H : ONote → Prop} (hop : IsOperator H)
    (hSH : ∀ β, S β → H β) : ∀ {β : ONote}, Cl S β → H β := by
  intro β hβ
  induction hβ with
  | base hb => exact hSH _ hb
  | ofNat n => exact hop.ofNat_mem n
  | add _ _ ih₁ ih₂ => exact hop.add_mem ih₁ ih₂
  | expTower _ ih => exact hop.expTower_mem ih
  | osucc _ ih => exact hop.osucc_mem ih

/-- The relativization generator set: adjoin the branch numeral (the work order's
"`H[n]` is generation from `gen ∪ {ofNat n}`").  `Zeh.allω` runs premise `n` over it. -/
def adjoin (H : ONote → Prop) (n : ℕ) : ONote → Prop := fun β => H β ∨ β = ONote.ofNat n

/-- The relativized operator `H[n]`. -/
def relOp (H : ONote → Prop) (n : ℕ) : ONote → Prop := Cl (adjoin H n)

/-! ### The kernel findings (K1)–(K3): what set-membership can and cannot carry at `ε₀`. -/

/-- `ω^e·n` (zero tail) is in every closure, by `n`-fold equal-exponent merge of
`expTower e` (kernel-computed merges via `repr_inj`). -/
theorem oaddZero_mem {S : ONote → Prop} {ε : ONote} (hε : ε.NF) (hεS : Cl S ε) :
    ∀ n : ℕ+, Cl S (oadd ε n 0) := by
  have key : ∀ k : ℕ, Cl S (oadd ε k.succPNat 0) := by
    intro k
    induction k with
    | zero => exact Cl.expTower hεS
    | succ k ih =>
        have hNF : (oadd ε k.succPNat 0).NF := hε.oadd _ NFBelow.zero
        have hNF' : (expTower ε).NF := expTower_NF hε
        have hNF'' : (oadd ε (k + 1).succPNat 0).NF := hε.oadd _ NFBelow.zero
        haveI := hNF; haveI := hNF'; haveI := hNF''
        have hsum : oadd ε k.succPNat 0 + expTower ε = oadd ε (k + 1).succPNat 0 := by
          refine repr_inj.mp ?_
          rw [repr_add (oadd ε k.succPNat 0) (expTower ε)]
          simp only [expTower, ONote.repr, Nat.succPNat_coe, PNat.one_coe,
            Nat.cast_one, add_zero, mul_one]
          have hc : (((k + 1).succ : ℕ) : Ordinal) = ((k.succ : ℕ) : Ordinal) + 1 := by
            push_cast
            try rfl
          rw [hc, mul_add, mul_one]
        exact hsum ▸ Cl.add ih (Cl.expTower hεS)
  intro n
  have h := key n.natPred
  rwa [PNat.succPNat_natPred] at h

/-- **(K1) VACUITY.**  Every normal-form notation is in the closure of EVERY generator set:
at the `ε₀` level, all of the notation system is hereditarily generated from numerals by
`+` and `ω^·`.  Consequence: the pinned membership side conditions are uniformly
dischargeable (good for the seams) and carry NO numeric information (fatal for any
membership-based bound). -/
theorem Cl_of_NF {S : ONote → Prop} : ∀ {β : ONote}, β.NF → Cl S β := by
  intro β
  induction β with
  | zero =>
      intro _
      exact Cl.ofNat 0
  | oadd ε n a ihε iha =>
      intro h
      have hε : ε.NF := h.fst
      have ha : a.NF := h.snd
      have hhead : (oadd ε n 0).NF := hε.oadd n NFBelow.zero
      haveI := hhead; haveI := ha; haveI := h
      have hsplit : oadd ε n 0 + a = oadd ε n a := by
        refine repr_inj.mp ?_
        rw [repr_add (oadd ε n 0) a]
        simp [ONote.repr]
      exact hsplit ▸ Cl.add (oaddZero_mem hε (ihε hε) n) (iha ha)

/-- The relativization only grows the operator (feeds every `Cl_mono`/`mono_H` re-key). -/
theorem adjoin_le (H : ONote → Prop) (n : ℕ) : ∀ γ, H γ → adjoin H n γ :=
  fun _ h => Or.inl h

/-- Adjoining a fresh numeral commutes past an inner relativization (the operator-side
analog of `max (max k a) b = max (max k b) a`; feeds the non-principal `allω` re-key). -/
theorem adjoin_swap (H : ONote → Prop) (a b : ℕ) :
    ∀ γ, adjoin (adjoin H a) b γ → adjoin (adjoin H b) a γ := by
  rintro γ ((hg | rfl) | rfl)
  · exact Or.inl (Or.inl hg)
  · exact Or.inr rfl
  · exact Or.inl (Or.inr rfl)

/-- Adjoining the SAME numeral twice collapses (the operator-side analog of
`max (max k n₀) n₀ = max k n₀`; feeds the principal `allω` re-key). -/
theorem adjoin_idem (H : ONote → Prop) (n : ℕ) :
    ∀ γ, adjoin (adjoin H n) n γ → adjoin H n γ := by
  rintro γ ((hg | rfl) | rfl)
  · exact Or.inl hg
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- Relativization is monotone in the base operator (feeds the non-principal `allω`
side-condition re-key `relOp H n → relOp (adjoin H n₀) n`). -/
theorem adjoin_base_mono {H H' : ONote → Prop} (n : ℕ) (h : ∀ γ, H γ → H' γ) :
    ∀ γ, adjoin H n γ → adjoin H' n γ := by
  rintro γ (hg | rfl)
  · exact Or.inl (h _ hg)
  · exact Or.inr rfl

/-- `ω·(n+1)` is a member of every closure — by an `n`-sized tree of equal-exponent merges
(the seam-2 reversal brick; feeds `probe_allomega_reassembly_Zf`). -/
theorem wmul_mem (S : ONote → Prop) (n : ℕ) : Cl S (wmul n) := by
  induction n with
  | zero => exact Cl.expTower (Cl.ofNat 1)
  | succ n ih =>
      have h : wmul n + wmul 0 = wmul (n + 1) := rfl
      exact h ▸ Cl.add ih (Cl.expTower (Cl.ofNat 1))

/-! ### Ordinal-splice descent bricks (assembly plumbing, not judge-gated)

The §19.6 reduction outputs ordinal `osucc (α + γ)`; its inner descent cites these pure
`ONote` facts (no `Zeh` manipulation — reused by, but distinct from, the gated reduction).
Each composes the banked `Zekd` ordinal lemmas.  Built ahead so the discharge lap is pure
assembly. -/

/-- The reduction-output ordinal is NF whenever its components are. -/
theorem osucc_add_NF {α γ : ONote} (hα : α.NF) (hγ : γ.NF) : (osucc (α + γ)).NF :=
  osucc_NF (ONote.add_nf α γ)

/-- **Splice descent, `osucc` form:** `γ' < γ ⟹ osucc (α + γ') < osucc (α + γ)` (the branch
premise's ordinal strictly drops below the spliced output). -/
theorem osucc_add_lt_osucc_add {α γ' γ : ONote} (hα : α.NF) (hγ' : γ'.NF) (hγ : γ.NF)
    (h : γ' < γ) : osucc (α + γ') < osucc (α + γ) :=
  Zekd.osucc_lt_osucc (ONote.add_nf α γ') (ONote.add_nf α γ)
    (Zekd.add_lt_add_left_NF hα hγ' hγ h)

/-- **Splice descent, bare form:** `γ' < γ ⟹ α + γ' < osucc (α + γ)` (a premise below `γ`
lies strictly below the spliced output — the direct `weak`/`exI` descent witness). -/
theorem add_lt_osucc_add {α γ' γ : ONote} (hα : α.NF) (hγ' : γ'.NF) (hγ : γ.NF)
    (h : γ' < γ) : α + γ' < osucc (α + γ) :=
  Zekd.lt_osucc_of_lt (ONote.add_nf α γ) (Zekd.add_lt_add_left_NF hα hγ' hγ h)

/-- Membership of the reduction-output ordinal by closure (the seam-1 brick, named for the
reduction's use site: `osucc (α + γ)` is a member whenever `α`, `γ` are). -/
theorem osucc_add_mem {S : ONote → Prop} {α γ : ONote} (hα : Cl S α) (hγ : Cl S γ) :
    Cl S (osucc (α + γ)) :=
  Cl.osucc (Cl.add hα hγ)

/-- Ordinal `+` is monotone in both arguments (non-strict; the wrapper's `≤`-slack bound for
the cut combinator). -/
theorem add_le_add_NF {α₁ β₁ α₂ β₂ : ONote} (hα₁ : α₁.NF) (hβ₁ : β₁.NF)
    (hα₂ : α₂.NF) (hβ₂ : β₂.NF) (h₁ : α₁ ≤ β₁) (h₂ : α₂ ≤ β₂) : α₁ + α₂ ≤ β₁ + β₂ := by
  haveI := hα₁; haveI := hβ₁; haveI := hα₂; haveI := hβ₂
  exact le_def.mpr (by rw [repr_add, repr_add]; exact add_le_add (le_def.mp h₁) (le_def.mp h₂))

/-- `osucc` non-strict monotonicity (pairs with `Zekd.osucc_lt_osucc`). -/
theorem osucc_le_osucc {x y : ONote} (hx : x.NF) (hy : y.NF) (h : x ≤ y) : osucc x ≤ osucc y := by
  refine le_def.mpr ?_
  rw [repr_osucc hx, repr_osucc hy, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_le_succ (le_def.mp h)

end GoodsteinPA.OperatorZeh
