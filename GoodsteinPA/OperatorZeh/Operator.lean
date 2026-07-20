/-
# `OperatorZeh` substrate — `ONote`/`expTower` transforms for the `Zᵉ` calculus

Shared operator-notation lemmas underlying the operator-controlled calculi `Zeh`
(`GoodsteinPA.OperatorZeh.Zeh`) and its function-slot form `Zef` (`GoodsteinPA.OperatorZeh.Zef`):
the family-uniform raise `raise e α := e + ω^α`, the two-level-configuration constant `wmul`,
and the CNF/ordinal-splice bricks reused by the cut-elimination reductions in
`GoodsteinPA.OperatorZeh.Cut`.

**Provenance.** The rule skeleton and the Hardy witness bound follow the restricted infinitary
calculus `Z∞` [Tow20, §13, §15], where controlled cut-elimination is already present via a
Hardy-function gate ([Tow20, §19.6, §19.7, §19.9]). Carrying that control through an explicit
operator — an ordinal-valued `H` for `Zeh`, or a number-theoretic slot `f : ℕ → ℕ` for `Zef` — is
the Buchholz-style operator-controlled derivation methodology in its number-theoretic form
[EW12, §4]: `Zef`'s cut-reduction composes the slots (`f ∘ g`) and a size-norm gates the running
family `f^α` (`GoodsteinPA.OperatorZeh.Slot`'s `iterSlot`, `NormControlled`)
[EW12, Definition 16, Definition 23, Lemma 25]. In this PA/`ε₀` setting `Zeh`'s ordinal operator
`H` turns out to carry no information (`Zeh.change_H`); only `Zef`'s numeric slot `f` is
load-bearing. The inversion suite (`GoodsteinPA.OperatorZeh.Inversion`, mirroring `Provable.allInv`)
follows [Tow20] alone.

- [Tow20, §13, §15, §19]
- [EW12, §4, Definition 16, Definition 23, Lemma 25]
-/
module

public import GoodsteinPA.OperatorZinfty.InductionLeaf
public import GoodsteinPA.ToMathlib.FastGrowing.EWIteration

@[expose] public section

namespace GoodsteinPA.OperatorZeh

open LO LO.FirstOrder ONote Ordinal
open GoodsteinPA.OperatorZinfty

/-! ## ONote/expTower transforms -/

@[simp] lemma norm_expTower (α : ONote) : norm (expTower α) = max (norm α) 1 :=
  norm_omegaPow

/-- The family-uniform control raise `raise e α := e + ω^α`. -/
def raise (e α : ONote) : ONote := e + expTower α

lemma raise_NF {e α} (he : e.NF) (hα : α.NF) : (raise e α).NF := by
  haveI := he; haveI := expTower_NF hα
  exact ONote.add_nf e (expTower α)

lemma raise_lt_raise {e β α} (he : e.NF) (hβ : β.NF) (hα : α.NF) (h : β < α) :
    raise e β < raise e α :=
  add_lt_add_left_NF he (expTower_NF hβ) (expTower_NF hα) (expTower_lt_expTower hβ h)

/-- `ω·(m+1)` as an explicit `ONote` (the W4B two-level-configuration family). -/
def wmul (m : ℕ) : ONote := oadd 1 m.succPNat 0

lemma wmul_NF (m : ℕ) : (wmul m).NF := nf_one.oadd m.succPNat NFBelow.zero

@[simp] lemma norm_one : norm (1 : ONote) = 1 := rfl

@[simp] lemma norm_wmul (m : ℕ) : norm (wmul m) = m + 1 := by
  rw [wmul, norm_oadd, norm_one, norm_zero, Nat.succPNat_coe]
  omega

/-- Equal-exponent CNF merge, parametric (kernel-computed; W4B's rail brick). -/
lemma wmul_add_wmul (a b : ℕ) : wmul a + wmul b = oadd 1 (a.succPNat + b.succPNat) 0 := rfl

lemma one_lt_omegaO : (1 : ONote) < ONote.omega :=
  oadd_lt_oadd_1 nf_one ONote.zero_lt_one

lemma omegaO_NF : (ONote.omega).NF := nf_one.oadd 1 NFBelow.zero

lemma wmul_lt_expTower_omega (m : ℕ) : wmul m < expTower ONote.omega :=
  oadd_lt_oadd_1 (wmul_NF m) one_lt_omegaO

/-- Any `oadd 1 K 1`-shaped notation (an `osucc` of an `ω·K` notation) sits below `ω^ω`. -/
lemma osucc_omega_coeff_lt (K : ℕ+) : osucc (oadd 1 K 0) < expTower ONote.omega := by
  have h : (osucc (oadd 1 K 0)).NF := osucc_NF (nf_one.oadd K NFBelow.zero)
  rw [show osucc (oadd 1 K 0) = oadd 1 K 1 from rfl] at h ⊢
  exact oadd_lt_oadd_1 h one_lt_omegaO

lemma osucc_wmul_lt_expTower_omega (m : ℕ) : osucc (wmul m) < expTower ONote.omega :=
  osucc_omega_coeff_lt m.succPNat

/-! ## The operator layer -/

/-- **Operator.** The closure conditions an `H : ONote → Prop` must satisfy to serve as a
Buchholz-style operator: closed under `+`, `ω^·` (`expTower`), `osucc`, `ofNat`. The concrete
closure conditions are specific to this formalization.

- [EW12, §4]
-/
structure IsOperator (H : ONote → Prop) : Prop where
  ofNat_mem : ∀ n : ℕ, H (ONote.ofNat n)
  add_mem : ∀ {α β : ONote}, H α → H β → H (α + β)
  expTower_mem : ∀ {α : ONote}, H α → H (expTower α)
  osucc_mem : ∀ {α : ONote}, H α → H (osucc α)

/-- Inductive closure of a generator set under the four operations.  Membership
witnesses are finite trees — the "represented, countable" operator shape. -/
inductive Cl (S : ONote → Prop) : ONote → Prop
  | base {β : ONote} : S β → Cl S β
  | ofNat (n : ℕ) : Cl S (ONote.ofNat n)
  | add {α β : ONote} : Cl S α → Cl S β → Cl S (α + β)
  | expTower {α : ONote} : Cl S α → Cl S (expTower α)
  | osucc {α : ONote} : Cl S α → Cl S (osucc α)

/-- The closure of any generator set is an operator. -/
lemma isOperator_Cl (S : ONote → Prop) : IsOperator (Cl S) where
  ofNat_mem := Cl.ofNat
  add_mem := Cl.add
  expTower_mem := Cl.expTower
  osucc_mem := Cl.osucc

/-- Closure is monotone in the generators (feeds `Zeh.mono_H`). -/
lemma Cl_mono {S S'} (h : ∀ β, S β → S' β) {β} (hβ : Cl S β) : Cl S' β := by
  induction hβ with
  | base hb => exact Cl.base (h _ hb)
  | ofNat n => exact Cl.ofNat n
  | add _ _ ih₁ ih₂ => exact Cl.add ih₁ ih₂
  | expTower _ ih => exact Cl.expTower ih
  | osucc _ ih => exact Cl.osucc ih

/-- `Cl` is the least operator over its generators: closure membership maps into any
`IsOperator` set containing the generators (the bridge between the abstract-`H` and
generated-`H` formulations). -/
lemma Cl_sub_of_isOperator {S H} (hop : IsOperator H)
    (hSH : ∀ β, S β → H β) {β} (hβ : Cl S β) : H β := by
  induction hβ with
  | base hb => exact hSH _ hb
  | ofNat n => exact hop.ofNat_mem n
  | add _ _ ih₁ ih₂ => exact hop.add_mem ih₁ ih₂
  | expTower _ ih => exact hop.expTower_mem ih
  | osucc _ ih => exact hop.osucc_mem ih

/-- The relativization generator set: adjoin the branch numeral `ofNat n` to the generators.
`Zeh.allω` runs premise `n` over it.

- [EW12, §4]
-/
def adjoin (H : ONote → Prop) (n : ℕ) : ONote → Prop := fun β => H β ∨ β = ONote.ofNat n

/-- The relativized operator `H[n]` — the closure of `H` adjoined with `ofNat n`.

- [EW12, §4]
-/
def relOp (H : ONote → Prop) (n : ℕ) : ONote → Prop := Cl (adjoin H n)

/-! ### The kernel findings (K1)–(K3): what set-membership can and cannot carry at `ε₀`. -/

/-- `ω^e·n` (zero tail) is in every closure, by `n`-fold equal-exponent merge of
`expTower e` (kernel-computed merges via `repr_inj`). -/
lemma oaddZero_mem {S} {ε} (hε : ε.NF) (hεS : Cl S ε) (n : ℕ+) :
    Cl S (oadd ε n 0) := by
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
  have h := key n.natPred
  rwa [PNat.succPNat_natPred] at h

/-- **(K1) VACUITY.**  Every normal-form notation is in the closure of EVERY generator set:
at the `ε₀` level, all of the notation system is hereditarily generated from numerals by
`+` and `ω^·`.  Consequence: membership side conditions are uniformly dischargeable (good for
the seams) and carry no numeric information (fatal for any membership-based bound). -/
lemma Cl_of_NF {S} {β} (h : β.NF) : Cl S β := by
  induction β with
  | zero =>
      exact Cl.ofNat 0
  | oadd ε n a ihε iha =>
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
lemma adjoin_le (H : ONote → Prop) (n : ℕ) (γ) (h : H γ) : adjoin H n γ :=
  Or.inl h

/-- Adjoining a fresh numeral commutes past an inner relativization (the operator-side
analog of `max (max k a) b = max (max k b) a`; feeds the non-principal `allω` re-key). -/
lemma adjoin_swap (H : ONote → Prop) (a b : ℕ) (γ) (h : adjoin (adjoin H a) b γ) :
    adjoin (adjoin H b) a γ := by
  rcases h with (hg | rfl) | rfl
  · exact Or.inl (Or.inl hg)
  · exact Or.inr rfl
  · exact Or.inl (Or.inr rfl)

/-- Adjoining the SAME numeral twice collapses (the operator-side analog of
`max (max k n₀) n₀ = max k n₀`; feeds the principal `allω` re-key). -/
lemma adjoin_idem (H : ONote → Prop) (n : ℕ) (γ) (h : adjoin (adjoin H n) n γ) : adjoin H n γ := by
  rcases h with (hg | rfl) | rfl
  · exact Or.inl hg
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- Relativization is monotone in the base operator (feeds the non-principal `allω`
side-condition re-key `relOp H n → relOp (adjoin H n₀) n`). -/
lemma adjoin_base_mono {H H'} (n : ℕ) (h : ∀ γ, H γ → H' γ)
    (γ) (hg : adjoin H n γ) : adjoin H' n γ := by
  rcases hg with hg | rfl
  · exact Or.inl (h _ hg)
  · exact Or.inr rfl

/-- `ω·(n+1)` is a member of every closure — by an `n`-sized tree of equal-exponent merges
(the seam-2 reversal brick; feeds `probe_allomega_reassembly_Zf`). -/
lemma wmul_mem (S : ONote → Prop) (n : ℕ) : Cl S (wmul n) := by
  induction n with
  | zero => exact Cl.expTower (Cl.ofNat 1)
  | succ n ih =>
      have h : wmul n + wmul 0 = wmul (n + 1) := rfl
      exact h ▸ Cl.add ih (Cl.expTower (Cl.ofNat 1))

/-! ### Ordinal-splice descent bricks (assembly plumbing)

The [Tow20, Theorem 19.6] reduction outputs ordinal `osucc (α + γ)`; its inner descent cites
these pure `ONote` facts (no `Zeh` manipulation — reused by, but distinct from, the reduction
itself). Each composes the `Provable` ordinal lemmas. -/

/-- The reduction-output ordinal is NF whenever its components are. -/
lemma osucc_add_NF {α γ} (hα : α.NF) (hγ : γ.NF) : (osucc (α + γ)).NF :=
  osucc_NF (ONote.add_nf α γ)

/-- **Splice descent, `osucc` form:** `γ' < γ ⟹ osucc (α + γ') < osucc (α + γ)` (the branch
premise's ordinal strictly drops below the spliced output). -/
lemma osucc_add_lt_osucc_add {α γ' γ} (hα : α.NF) (hγ' : γ'.NF) (hγ : γ.NF)
    (h : γ' < γ) : osucc (α + γ') < osucc (α + γ) :=
  osucc_lt_osucc (ONote.add_nf α γ') (ONote.add_nf α γ)
    (add_lt_add_left_NF hα hγ' hγ h)

/-- **Splice descent, bare form:** `γ' < γ ⟹ α + γ' < osucc (α + γ)` (a premise below `γ`
lies strictly below the spliced output — the direct `weak`/`exI` descent witness). -/
lemma add_lt_osucc_add {α γ' γ} (hα : α.NF) (hγ' : γ'.NF) (hγ : γ.NF)
    (h : γ' < γ) : α + γ' < osucc (α + γ) :=
  lt_osucc_of_lt (ONote.add_nf α γ) (add_lt_add_left_NF hα hγ' hγ h)

/-- Membership of the reduction-output ordinal by closure (the seam-1 brick, named for the
reduction's use site: `osucc (α + γ)` is a member whenever `α`, `γ` are). -/
lemma osucc_add_mem {S} {α γ} (hα : Cl S α) (hγ : Cl S γ) :
    Cl S (osucc (α + γ)) :=
  Cl.osucc (Cl.add hα hγ)

/-- Ordinal `+` is monotone in both arguments (non-strict; the wrapper's `≤`-slack bound for
the cut combinator). -/
lemma add_le_add_NF {α₁ β₁ α₂ β₂ : ONote} (hα₁ : α₁.NF) (hβ₁ : β₁.NF)
    (hα₂ : α₂.NF) (hβ₂ : β₂.NF) (h₁ : α₁ ≤ β₁) (h₂ : α₂ ≤ β₂) : α₁ + α₂ ≤ β₁ + β₂ := by
  haveI := hα₁; haveI := hβ₁; haveI := hα₂; haveI := hβ₂
  exact le_def.mpr (by rw [repr_add, repr_add]; exact add_le_add (le_def.mp h₁) (le_def.mp h₂))

/-- `osucc` non-strict monotonicity (pairs with `osucc_lt_osucc`). -/
lemma osucc_le_osucc {x y} (hx : x.NF) (hy : y.NF) (h : x ≤ y) : osucc x ≤ osucc y := by
  refine le_def.mpr ?_
  rw [repr_osucc hx, repr_osucc hy, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_le_succ (le_def.mp h)

end GoodsteinPA.OperatorZeh
