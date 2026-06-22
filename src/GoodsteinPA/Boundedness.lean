/-
# `Boundedness.lean` — the `Prog_≺(X)` / `TI_≺(X)` formulas + corollary bridges (lap-13)

The transfinite-induction formula scaffolding the Boundedness theorem (Buchholz Thm 5.4) inverts,
plus the corollary bridges connecting `⊨^γ`-truth of `X`-atoms to the ≺-rank.
The order `≺` is given by a depth-2 `LX`-formula `prec` (`#0 ≺ #1`); for the headline `prec` is the
ℒₒᵣ-definable CNF-ε₀ order. `X t` is the set-variable atom `Xat t`.

  `Prog_≺(X) := ∀x ((∀y (y ≺ x → X y)) → X x)`
  `TI_≺(X)   := Prog_≺(X) → ∀x X x`

The de-Bruijn shapes are pinned so the Boundedness induction's inversion cases line up; the proof of
Boundedness itself is the next target. The corollary step (`‖≺‖ ≤ 2^β` from `⊨^{2^β} Xn ∀n`) is here.
-/
import GoodsteinPA.ZinftyGen
import GoodsteinPA.LangX
import GoodsteinPA.TruthSem
import GoodsteinPA.XPositive

namespace GoodsteinPA.Boundedness

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.LangX GoodsteinPA.TruthSem GoodsteinPA.XPositive

/-- The set-variable atom `X t`. -/
def Xat {n} (t : Semiterm LX ℕ n) : Semiformula LX ℕ n := Semiformula.rel Xsym ![t]

variable (prec : Semiformula LX ℕ 2)

/-- `∀y (y ≺ x → X y)` as a depth-1 formula (free `x = #0`). At depth 2, `prec` reads `#0 ≺ #1`
with `#0 = y`, `#1 = x`. -/
def hyp : Semiformula LX ℕ 1 := ∀⁰ (prec 🡒 Xat (#0))

/-- `Prog_≺(X) := ∀x ((∀y (y ≺ x → X y)) → X x)`. -/
def Prog : Semiformula LX ℕ 0 := ∀⁰ (hyp prec 🡒 Xat (#0))

/-- `TI_≺(X) := Prog_≺(X) → ∀x X x`. -/
def TI : Semiformula LX ℕ 0 := Prog prec 🡒 ∀⁰ (Xat (#0))

-- Probes: the formulas typecheck and their negations have the expected `∃`/`∀` shape for inversion.
example : Form LX := Prog prec
example : Form LX := TI prec
example : ∼(Prog prec) = ∃⁰ ∼(hyp prec 🡒 Xat (#0)) := by simp [Prog]
example : ∼(TI prec) = (Prog prec) ⋏ ∼(∀⁰ (Xat (#0))) := by simp [TI, Semiformula.imp_eq]

/-! ## Corollary bridges: `⊨^γ`-truth of `X`-atoms ↔ the ≺-rank

These connect the Boundedness conclusion (`⊨^{2^β} Xn` for all `n`) to `‖≺‖ ≤ 2^β` — the corollary
`Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`. -/

section Corollary
variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]

/-- The numeral `nm n` denotes `n` in the `structLX` carrier (its `ℒₒᵣ`-fragment is the standard
model). -/
theorem val_nm_structLX (S : ℕ → Prop) (n : ℕ) :
    Semiterm.val (structLX S) ![] (id : ℕ → ℕ) (nm n) = n := by
  letI inst : Structure LX ℕ := structLX S
  haveI : Structure.Zero LX ℕ := ⟨rfl⟩
  haveI : Structure.One LX ℕ := ⟨rfl⟩
  haveI : Structure.Add LX ℕ := ⟨fun _ _ => rfl⟩
  simp [nm]

/-- `⊨^γ (X (numeral n)) ↔ |n|_≺ < γ` — the carrier reads the `X`-atom on a numeral as the level-set
membership, i.e. as the ≺-rank bound. -/
theorem models_Xat_nm (γ : Ordinal.{0}) (n : ℕ) :
    models lt γ (Xat (nm n)) ↔ rk lt n < γ := by
  unfold models Xat
  rw [Semiformula.eval_rel₁, structLX_rel_Xsym]
  simp only [Matrix.cons_val_zero, val_nm_structLX]
  rfl

/-- **The corollary's order-type step.** If `⊨^γ (X (numeral n))` for every `n`, then `‖≺‖ ≤ γ`.
With `γ := 2^β` this is `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β` once Boundedness supplies the hypothesis. -/
theorem orderType_le_of_models_Xat {γ : Ordinal.{0}}
    (h : ∀ n, models lt γ (Xat (nm n))) : orderType lt ≤ γ :=
  orderType_le_of_forall lt (fun n => (models_Xat_nm lt γ n).mp (h n))

end Corollary

/-! ## Boundedness (Buchholz Thm 5.4) — the 8→5-case induction

Buchholz: for X-positive `Γ`, `Z∞ ⊢^β_1 ¬Prog_≺(X), ¬Xs₁,…,¬Xs_k, Γ` with `|sᵢ|_≺ ≤ α`
⟹ `⊨^{α+2^β} Γ`. We prove the **cut-free** specialisation (`cr d = 0`): the three `Cut` cases
(Buchholz 6/7/8) are then vacuous (a `cut` node has `cr ≥ 1`), leaving 5 cases.

The induction is **nested**: an outer strong induction on the ordinal height `o d` (the `¬Prog`
inversion case shrinks it strictly) wrapping an inner structural induction on the derivation `d`
(the height-preserving `weak`/`andI`/`orI`/`allω` cases). See
`papers/buchholz-beweistheorie-lecture-notes.pdf` p.29 + `ANALYSIS-2026-06-22-lap13-boundedness-design.md`.

**Faithfulness of the X-atom leaf.** Our generic `axTrue` is more permissive than Buchholz's `Z∞`
at `LX`: it admits a *lone* true X-literal, which Buchholz forbids (his only X-axiom is the *pair*
`{Xs,¬Xt}`). Boundedness is false for lone-X leaves, so we carry `XFreeAx d` (every `axTrue` leaf
uses an `ℒₒᵣ`-relation); the X-pair axiom enters via `axL` (a genuine complementary pair, handled in
case 1.2). The embedding `embedC` over `LX` discharges `XFreeAx` by routing X-atom identity axioms
through `axL` rather than `axTrue`. -/

section Main

/-- The ambient ℕ-model for the Boundedness derivations: `X := ∅`. The choice is immaterial — every
X-free leaf is `S`-independent and `XFreeAx` forbids X-literal leaves — but fixing it lets `LitTrue`
(under this instance) connect to `models` (under the level-set instance). -/
noncomputable instance ambient : Structure LX ℕ := structLX (fun _ => False)

variable (lt : ℕ → ℕ → Prop) [IsWellFounded ℕ lt]

/-- `tval lt t = |tᴺ|_≺` — the ≺-rank of the ℕ-value of a closed `LX`-term (X-free, so the carrier
is immaterial). -/
noncomputable def tval (t : Semiterm LX ℕ 0) : Ordinal.{0} :=
  rk lt (Semiterm.val (structLX (fun _ => False)) ![] id t)

/-- **The X-atom on a closed term reads the ≺-rank bound.** -/
theorem models_Xat' (γ : Ordinal.{0}) (t : Semiterm LX ℕ 0) :
    models lt γ (Xat t) ↔ tval lt t < γ := by
  unfold models Xat tval
  rw [Semiformula.eval_rel₁, structLX_rel_Xsym]
  simp only [Matrix.cons_val_zero, levelSet]
  rw [val_structLX_eq (levelSet lt γ) (fun _ => False)]

/-- **The negated X-atom is true at `γ` iff the rank is `≥ γ`.** -/
theorem models_negXat (γ : Ordinal.{0}) (t : Semiterm LX ℕ 0) :
    models lt γ (∼(Xat t)) ↔ γ ≤ tval lt t := by
  have : ∼(Xat t) = Semiformula.nrel Xsym ![t] := rfl
  rw [this]
  unfold models tval
  rw [Semiformula.eval_nrel₁, structLX_rel_Xsym]
  simp only [Matrix.cons_val_zero, levelSet]
  rw [val_structLX_eq (levelSet lt γ) (fun _ => False)]
  exact not_lt

/-- A true **X-free** literal is `models`-true at every level (its truth is carrier-independent). -/
theorem models_inl_lit (γ : Ordinal.{0}) (b : Bool) {k} (r₀ : (ℒₒᵣ).Rel k)
    (v : Fin k → Semiterm LX ℕ 0) (htrue : LitTrue (signedLit b (Sum.inl r₀) v)) :
    models lt γ (signedLit b (Sum.inl r₀) v) := by
  have hv : (fun i => Semiterm.val (structLX (levelSet lt γ)) ![] id (v i))
      = (fun i => Semiterm.val (structLX (fun _ => False)) ![] id (v i)) :=
    funext fun i => val_structLX_eq _ _ _ _ (v i)
  cases b <;>
    · simp only [signedLit, models, LitTrue, Semiformula.eval_rel, Semiformula.eval_nrel,
        Semiformula.Evalm] at htrue ⊢
      rw [hv]; exact htrue

/-- **X-free axTrue leaves only** (Buchholz-faithfulness; see the section header). -/
def XFreeAx : {Δ : Seq LX} → Deriv Δ → Prop
  | _, .axL _ _ _ _ => True
  | _, .axTrue _ r _ _ _ => Sum.isLeft r = true
  | _, .verumR _ => True
  | _, .weak d _ => XFreeAx d
  | _, .andI _ _ dφ dψ => XFreeAx dφ ∧ XFreeAx dψ
  | _, .orI _ _ d => XFreeAx d
  | _, .allω _ d => ∀ n, XFreeAx (d n)
  | _, .exI _ _ d => XFreeAx d
  | _, .cut _ d₁ d₂ => XFreeAx d₁ ∧ XFreeAx d₂

variable (prec : Semiformula LX ℕ 2)

/-- A formula's **role** in a Boundedness sequent: the negated progressiveness `¬Prog`, a bounded
negative X-atom `¬Xt` (`|tᴺ|_≺ ≤ α`), or an X-positive formula. -/
def PartItem (α : Ordinal.{0}) (A : Form LX) : Prop :=
  A = ∼(Prog prec) ∨
  (∃ t : Semiterm LX ℕ 0, A = ∼(Xat t) ∧ tval lt t ≤ α) ∨
  XPos A

/-- The Boundedness sequent invariant: every member has a valid role. -/
def Partition (α : Ordinal.{0}) (Δ : Seq LX) : Prop := ∀ A ∈ Δ, PartItem lt prec α A

/-- The Boundedness conclusion: some **X-positive** member is `⊨^γ`-true. -/
def SatPos (γ : Ordinal.{0}) (Δ : Seq LX) : Prop := ∃ A ∈ Δ, XPos A ∧ models lt γ A

/-- **X-positivity is rewrite-invariant** (substitution touches terms, not relation symbols or
connective structure): needed for the ω-rule / `∃`-witness cases, where `χ` X-positive ⟹ each
instance `χ/[nm n]` X-positive. -/
theorem xpos_rew : ∀ {n₁} (χ : Semiformula LX ℕ n₁) {n₂} (ω : Rew LX ℕ n₁ ℕ n₂),
    XPos χ → XPos (ω ▹ χ) := by
  intro n₁ χ
  induction χ using Semiformula.rec' with
  | hverum => intro n₂ ω h; simp [XPos]
  | hfalsum => intro n₂ ω h; simp [XPos]
  | hrel r v => intro n₂ ω h; rw [Semiformula.rew_rel]; simp [XPos]
  | hnrel r v => intro n₂ ω h; rw [Semiformula.rew_nrel]; simpa [XPos] using h
  | hand φ ψ ihφ ihψ =>
      intro n₂ ω h
      simp only [LogicalConnective.HomClass.map_and, XPos] at *
      exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hor φ ψ ihφ ihψ =>
      intro n₂ ω h
      simp only [LogicalConnective.HomClass.map_or, XPos] at *
      exact ⟨ihφ ω h.1, ihψ ω h.2⟩
  | hall φ ih => intro n₂ ω h; rw [Rewriting.app_all]; exact ih ω.q h
  | hexs φ ih => intro n₂ ω h; rw [Rewriting.app_exs]; exact ih ω.q h

/-- `χ/[nm n]` stays X-positive. -/
theorem xpos_subst {χ : SyntacticSemiformula LX 1} (n : ℕ) (h : XPos χ) : XPos (χ/[nm n]) :=
  xpos_rew χ _ h

/-- `SatPos` lifts to a higher level (X-positive members are monotone in `γ`). -/
theorem satpos_mono {γ δ : Ordinal.{0}} (h : γ ≤ δ) {Δ : Seq LX} :
    SatPos lt γ Δ → SatPos lt δ Δ :=
  fun ⟨A, hA, hpos, hm⟩ => ⟨A, hA, hpos, models_mono lt h hpos hm⟩

/-- `SatPos` transports along a superset. -/
theorem satpos_subset {γ : Ordinal.{0}} {Δ Δ' : Seq LX} (h : Δ ⊆ Δ') :
    SatPos lt γ Δ → SatPos lt γ Δ' :=
  fun ⟨A, hA, hpos, hm⟩ => ⟨A, h hA, hpos, hm⟩

/-- `(X #0)/[nm n] = X (nm n)`. -/
theorem xat_subst (n : ℕ) : (Xat (#0 : Semiterm LX ℕ 1))/[nm n] = Xat (nm n) := by
  simp [Xat, Semiformula.rew_rel, Matrix.constant_eq_singleton]

/-- The `¬Prog` body `∼(hyp 🡒 X #0)` substitutes to `hyp/[nm n] ⋏ ¬X(nm n)` — the two Buchholz
case-2 conjuncts (the X-positive `∀y≺n Xy` and the bounded negative atom `¬Xn`). -/
theorem chi_subst (n : ℕ) :
    (∼(hyp prec 🡒 Xat (#0)))/[nm n] = (hyp prec)/[nm n] ⋏ ∼(Xat (nm n)) := by
  have h1 : ∼(hyp prec 🡒 Xat (#0)) = hyp prec ⋏ ∼(Xat (#0)) := by simp [Semiformula.imp_eq]
  rw [h1]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_neg, xat_subst]

/-- `hyp prec = ∀y(y≺x → Xy)` is X-positive whenever the order literal `∼prec` is (it holds for the
headline's `ℒₒᵣ`-definable, X-free order `≺`). -/
theorem hyp_xpos (h : XPos (∼ prec)) : XPos (hyp prec) := by
  simpa [hyp, Xat, Semiformula.imp_eq, XPos] using h

/-- `|nm n|_≺ = |n|_≺`. -/
theorem tval_nm (n : ℕ) : tval lt (nm n) = rk lt n := by unfold tval; rw [val_nm]

/-! ### `XFreeAx`-tracking provability `PXF` + smart constructors

The cut-free (`cr = 0`) derivability predicate that *also* records `XFreeAx`. Mirrors `Provable`'s
smart constructors; used to port `andInvAux` so the ∧-inversion preserves the leaf condition. -/

/-- Cut-free, `XFreeAx`-tracking provability at height `≤ α`. -/
def PXF (α : Ordinal.{0}) (Γ : Seq LX) : Prop := ∃ d : Deriv Γ, d.o ≤ α ∧ d.cr = 0 ∧ XFreeAx d

theorem PXF.mono {α β : Ordinal.{0}} {Γ : Seq LX} (h : α ≤ β) : PXF α Γ → PXF β Γ
  | ⟨d, ho, hcr, hxf⟩ => ⟨d, ho.trans h, hcr, hxf⟩

theorem PXF.weakening {α : Ordinal.{0}} {Γ Δ : Seq LX} (h : Γ ⊆ Δ) : PXF α Γ → PXF α Δ
  | ⟨d, ho, hcr, hxf⟩ =>
    ⟨Deriv.weak d h, by simpa only [Deriv.o] using ho, by simpa only [Deriv.cr] using hcr, hxf⟩

theorem PXF.axL {Γ : Seq LX} {k} (r : LX.Rel k) (v) (hp : Semiformula.rel r v ∈ Γ)
    (hn : Semiformula.nrel r v ∈ Γ) : PXF 0 Γ :=
  ⟨Deriv.axL r v hp hn, by simp [Deriv.o], by simp [Deriv.cr], by simp [XFreeAx]⟩

theorem PXF.axTrue {Γ : Seq LX} {k} (b : Bool) (r : LX.Rel k) (v) (hxfree : Sum.isLeft r = true)
    (htrue : LitTrue (signedLit b r v)) (hmem : signedLit b r v ∈ Γ) : PXF 0 Γ :=
  ⟨Deriv.axTrue b r v htrue hmem, by simp [Deriv.o], by simp [Deriv.cr], hxfree⟩

theorem PXF.verumR {Γ : Seq LX} (h : (⊤ : Form LX) ∈ Γ) : PXF 0 Γ :=
  ⟨Deriv.verumR h, by simp [Deriv.o], by simp [Deriv.cr], by simp [XFreeAx]⟩

theorem PXF.andI {α β : Ordinal.{0}} {Γ : Seq LX} (φ ψ : Form LX)
    (hφ : PXF α (insert φ Γ)) (hψ : PXF β (insert ψ Γ)) :
    PXF (max α β + 1) (insert (φ ⋏ ψ) Γ) :=
  match hφ, hψ with
  | ⟨dφ, hoφ, hcφ, hxφ⟩, ⟨dψ, hoψ, hcψ, hxψ⟩ =>
    ⟨Deriv.andI φ ψ dφ dψ, by simp only [Deriv.o]; exact add_le_add (max_le_max hoφ hoψ) le_rfl,
      by simp only [Deriv.cr, hcφ, hcψ, max_self], ⟨hxφ, hxψ⟩⟩

theorem PXF.orI {α : Ordinal.{0}} {Γ : Seq LX} (φ ψ : Form LX)
    (h : PXF α (insert φ (insert ψ Γ))) : PXF (α + 1) (insert (φ ⋎ ψ) Γ) :=
  match h with
  | ⟨d, ho, hc, hx⟩ =>
    ⟨Deriv.orI φ ψ d, by simp only [Deriv.o]; gcongr,
      by simp only [Deriv.cr]; exact hc, hx⟩

theorem PXF.exI {α : Ordinal.{0}} {Γ : Seq LX} (φ : SyntacticSemiformula LX 1) (n : ℕ)
    (h : PXF α (insert (φ/[nm n]) Γ)) : PXF (α + 1) (insert (∃⁰ φ) Γ) :=
  match h with
  | ⟨d, ho, hc, hx⟩ =>
    ⟨Deriv.exI φ n d, by simp only [Deriv.o]; gcongr,
      by simp only [Deriv.cr]; exact hc, hx⟩

/-- Reshuffle helpers (standalone so `DecidableEq (Form LX)` doesn't blow the heartbeat limit inside
the big `andInv_xfree` induction — mirrors `ZinftyGen.invPush1`/`invPull1`). -/
theorem invPush1' (b a e : Form LX) (s : Seq LX) :
    insert b ((insert a s).erase e) ⊆ insert a (insert b (s.erase e)) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto

theorem invPull1' (b : Form LX) {a e : Form LX} (h : a ≠ e) (s : Seq LX) :
    insert a (insert b (s.erase e)) ⊆ insert b ((insert a s).erase e) := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
  rcases hx with rfl | hx
  · tauto
  · tauto

theorem PXF.allω {β : ℕ → Ordinal.{0}} {Γ : Seq LX} (φ : SyntacticSemiformula LX 1)
    (h : ∀ n, PXF (β n) (insert (φ/[nm n]) Γ)) : PXF ((⨆ n, β n) + 1) (insert (∀⁰ φ) Γ) := by
  choose d ho hc hx using h
  refine ⟨Deriv.allω φ d, ?_, ?_, hx⟩
  · simp only [Deriv.o]
    exact add_le_add (Ordinal.iSup_le fun n => (ho n).trans (Ordinal.le_iSup β n)) le_rfl
  · simp only [Deriv.cr, hc, ciSup_const]

/-- **∧-inversion preserving `XFreeAx`** (with the height bound). Replay of `ZinftyGen.andInvAux` at
cut rank `0` (so the `cut` case is vacuous) tracking the leaf predicate — inversions never introduce
an `axTrue` node, so `XFreeAx` is preserved. -/
theorem andInv_xfree {Δ : Seq LX} (d : Deriv Δ) {φ ψ : Form LX} :
    XFreeAx d → d.cr = 0 → (φ ⋏ ψ) ∈ Δ →
    PXF d.o (insert φ (Δ.erase (φ ⋏ ψ))) ∧ PXF d.o (insert ψ (Δ.erase (φ ⋏ ψ))) := by
  induction d with
  | @axL Γ k r v hp hn =>
    intro _ _ _
    have hr : Semiformula.rel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hp⟩
    have hn' : Semiformula.nrel r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), hn⟩
    simp only [Deriv.o]
    exact ⟨PXF.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn'),
      PXF.axL r v (Finset.mem_insert_of_mem hr) (Finset.mem_insert_of_mem hn')⟩
  | @axTrue Γ k b r v htrue hmem' =>
    intro hxf _ _
    have hl : signedLit b r v ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by cases b <;> simp [signedLit]), hmem'⟩
    simp only [Deriv.o]
    exact ⟨PXF.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl),
      PXF.axTrue b r v hxf htrue (Finset.mem_insert_of_mem hl)⟩
  | @verumR Γ h =>
    intro _ _ _
    have ht : (⊤ : Form LX) ∈ Γ.erase (φ ⋏ ψ) :=
      Finset.mem_erase.mpr ⟨Semiformula.ne_of_ne_complexity (by simp), h⟩
    simp only [Deriv.o]
    exact ⟨PXF.verumR (Finset.mem_insert_of_mem ht), PXF.verumR (Finset.mem_insert_of_mem ht)⟩
  | @weak Δ' Γ d' hsub ih =>
    intro hxf hcr hmem
    simp only [Deriv.o]
    by_cases hd : (φ ⋏ ψ) ∈ Δ'
    · obtain ⟨P1, P2⟩ := ih hxf hcr hd
      exact ⟨P1.weakening (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub)),
        P2.weakening (Finset.insert_subset_insert _ (Finset.erase_subset_erase _ hsub))⟩
    · have base : PXF d'.o Δ' := ⟨d', le_rfl, hcr, hxf⟩
      have hΔ : Δ' ⊆ Γ.erase (φ ⋏ ψ) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun e => hd (e ▸ hx), hsub hx⟩
      exact ⟨base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx)),
        base.weakening (fun x hx => Finset.mem_insert_of_mem (hΔ hx))⟩
  | @andI Γ₀ φ' ψ' dφ dψ ihφ ihψ =>
    intro hxf hcr hmem
    have hcrφ : dφ.cr = 0 := by
      have : dφ.cr ≤ 0 := by simp only [Deriv.cr] at hcr; exact hcr ▸ le_max_left _ _
      exact nonpos_iff_eq_zero.mp this
    have hcrψ : dψ.cr = 0 := by
      have : dψ.cr ≤ 0 := by simp only [Deriv.cr] at hcr; exact hcr ▸ le_max_right _ _
      exact nonpos_iff_eq_zero.mp this
    have hbφ : dφ.o ≤ (Deriv.andI φ' ψ' dφ dψ).o := by
      simp only [Deriv.o]; exact le_trans (le_max_left _ _) (self_le_add_right _ 1)
    have hbψ : dψ.o ≤ (Deriv.andI φ' ψ' dφ dψ).o := by
      simp only [Deriv.o]; exact le_trans (le_max_right _ _) (self_le_add_right _ 1)
    by_cases hhd : (φ' ⋏ ψ') = (φ ⋏ ψ)
    · obtain ⟨rfl, rfl⟩ := (Semiformula.and_inj _ _ _ _).mp hhd.symm
      refine ⟨?_, ?_⟩
      · by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hd)).1.weakening ?_).mono hbφ
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : PXF dφ.o (insert φ Γ₀) := ⟨dφ, le_rfl, hcrφ, hxf.1⟩
          refine (base.weakening ?_).mono hbφ
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
      · by_cases hd : (φ ⋏ ψ) ∈ Γ₀
        · refine ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hd)).2.weakening ?_).mono hbψ
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
        · have base : PXF dψ.o (insert ψ Γ₀) := ⟨dψ, le_rfl, hcrψ, hxf.2⟩
          refine (base.weakening ?_).mono hbψ
          intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢
          rcases hx with rfl | hx
          · tauto
          · exact Or.inr ⟨fun e => hd (e ▸ hx), Or.inr hx⟩
    · have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhd e.symm
      simp only [Deriv.o]
      refine ⟨?_, ?_⟩
      · have Pφ := ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).1).weakening
          (invPush1' φ φ' (φ ⋏ ψ) Γ₀)
        have Pψ := ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).1).weakening
          (invPush1' φ ψ' (φ ⋏ ψ) Γ₀)
        exact (PXF.andI φ' ψ' Pφ Pψ).weakening (invPull1' φ hhd Γ₀)
      · have Pφ := ((ihφ hxf.1 hcrφ (Finset.mem_insert_of_mem hmem0)).2).weakening
          (invPush1' ψ φ' (φ ⋏ ψ) Γ₀)
        have Pψ := ((ihψ hxf.2 hcrψ (Finset.mem_insert_of_mem hmem0)).2).weakening
          (invPush1' ψ ψ' (φ ⋏ ψ) Γ₀)
        exact (PXF.andI φ' ψ' Pφ Pψ).weakening (invPull1' ψ hhd Γ₀)
  | @orI Γ₀ φ' ψ' d' ih =>
    intro hxf hcr hmem
    have hhead : (φ' ⋎ ψ') ≠ (φ ⋏ ψ) := by intro h; simp [Vee.vee, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have mk : ∀ b : Form LX,
        PXF d'.o (insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))) →
        PXF (d'.o + 1) (insert b ((insert (φ' ⋎ ψ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have hsub : insert b ((insert φ' (insert ψ' Γ₀)).erase (φ ⋏ ψ))
            ⊆ insert φ' (insert ψ' (insert b (Γ₀.erase (φ ⋏ ψ)))) := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_erase] at hx ⊢; tauto
      exact (PXF.orI φ' ψ' (P.weakening hsub)).weakening (invPull1' b hhead Γ₀)
    simp only [Deriv.o]
    exact ⟨mk φ ((ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).1),
      mk ψ ((ih hxf hcr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem0))).2)⟩
  | @allω Γ₀ χ' d' ih =>
    intro hxf hcr hmem
    have hhead : (∀⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    have hcr' : ∀ m, (d' m).cr = 0 := fun m => by
      have : (d' m).cr ≤ 0 := by
        simp only [Deriv.cr] at hcr; exact le_trans (le_iSup (fun n => (d' n).cr) m) hcr.le
      exact nonpos_iff_eq_zero.mp this
    have mk : ∀ b : Form LX,
        (∀ m, PXF (d' m).o (insert b ((insert (χ'/[nm m]) Γ₀).erase (φ ⋏ ψ)))) →
        PXF ((⨆ m, (d' m).o) + 1) (insert b ((insert (∀⁰ χ') Γ₀).erase (φ ⋏ ψ))) := by
      intro b P
      have key : ∀ m, PXF (d' m).o (insert (χ'/[nm m]) (insert b (Γ₀.erase (φ ⋏ ψ)))) :=
        fun m => (P m).weakening (invPush1' b (χ'/[nm m]) (φ ⋏ ψ) Γ₀)
      exact (PXF.allω χ' key).weakening (invPull1' b hhead Γ₀)
    simp only [Deriv.o]
    exact ⟨mk φ (fun m => (ih m (hxf m) (hcr' m) (Finset.mem_insert_of_mem hmem0)).1),
      mk ψ (fun m => (ih m (hxf m) (hcr' m) (Finset.mem_insert_of_mem hmem0)).2)⟩
  | @exI Γ₀ χ' n d' ih =>
    intro hxf hcr hmem
    have hhead : (∃⁰ χ') ≠ (φ ⋏ ψ) := by intro h; simp [ExsQuantifier.exs, Wedge.wedge] at h
    have hmem0 : (φ ⋏ ψ) ∈ Γ₀ := (Finset.mem_insert.mp hmem).resolve_left fun e => hhead e.symm
    simp only [Deriv.o]
    refine ⟨?_, ?_⟩
    · have P := ((ih hxf hcr (Finset.mem_insert_of_mem hmem0)).1).weakening
        (invPush1' φ (χ'/[nm n]) (φ ⋏ ψ) Γ₀)
      exact (PXF.exI χ' n P).weakening (invPull1' φ hhead Γ₀)
    · have P := ((ih hxf hcr (Finset.mem_insert_of_mem hmem0)).2).weakening
        (invPush1' ψ (χ'/[nm n]) (φ ⋏ ψ) Γ₀)
      exact (PXF.exI χ' n P).weakening (invPull1' ψ hhead Γ₀)
  | @cut Γ₀ ξ d₁ d₂ ih₁ ih₂ =>
    intro _ hcr _
    exfalso
    have h1 : (↑ξ.complexity + 1 : ℕ∞) ≤ 0 := hcr ▸ le_max_left _ _
    simp at h1

/-- **Boundedness (Buchholz Thm 5.4), cut-free.** For an X-positive-decomposed sequent `Δ` (every
member is `¬Prog`, a bounded `¬Xt`, or X-positive), a cut-free `XFreeAx` derivation of `Δ` at height
`o d` yields `⊨^{α+2^{o d}}` of some X-positive member. The corollary `‖≺‖ ≤ 2^β` follows.

`hprec` is the semantic spec of the order formula `prec` (`⟦prec⟧ = lt`); `hprecXPos` says the order
literal is X-free. Both are discharged by the arithmetization seam (the `ℒₒᵣ`-definable ε₀ order). -/
theorem boundedness
    (hprec : ∀ (γ : Ordinal.{0}) (n : ℕ),
      models lt γ ((hyp prec)/[nm n]) ↔ ∀ m : ℕ, lt m n → rk lt m < γ)
    (hprecXPos : XPos (∼ prec)) (β : Ordinal.{0}) :
    ∀ {Δ : Seq LX} (α : Ordinal.{0}) (d : Deriv Δ),
      d.o ≤ β → d.cr = 0 → XFreeAx d → Partition lt prec α Δ →
      SatPos lt (α + 2 ^ d.o) Δ := by
  induction β using Ordinal.induction with
  | _ β outerIH =>
  intro Δ α d
  induction d generalizing α with
  | axL r v hp hn =>
    intro hob hcr hxf hpart
    cases r with
    | inl r₀ =>
      rcases litTrue_or_neg (Semiformula.rel (Sum.inl r₀) v) with ht | ht
      · exact ⟨Semiformula.rel (Sum.inl r₀) v, hp, by simp [XPos],
          models_inl_lit lt _ true r₀ v ht⟩
      · exact ⟨Semiformula.nrel (Sum.inl r₀) v, hn, by simp [XPos],
          models_inl_lit lt _ false r₀ v ht⟩
    | inr rx =>
      cases rx
      have hv1 : v = ![v 0] := by funext i; refine Fin.cases ?_ (fun j => j.elim0) i; rfl
      have hbound : tval lt (v 0) ≤ α := by
        rcases hpart (Semiformula.nrel Xsym v) hn with h | ⟨t', heq, hb⟩ | hpos
        · rw [Prog] at h; simp [Xat, Xsym] at h
        · simp only [Xat, Xsym] at heq
          injection heq with e1 e2 e3 e4
          rw [show v = ![t'] from e4]; simpa using hb
        · simp [XPos, Xsym] at hpos
      refine ⟨Xat (v 0), hv1 ▸ hp, by simp [Xat, XPos], ?_⟩
      rw [models_Xat']
      simp only [Deriv.o, Ordinal.opow_zero]
      exact lt_of_le_of_lt hbound (lt_add_of_pos_right α one_pos)
  | axTrue b r v htrue hmem =>
    intro hob hcr hxf hpart
    cases r with
    | inr rx => simp [XFreeAx] at hxf
    | inl r₀ =>
      exact ⟨signedLit b (Sum.inl r₀) v, hmem, by cases b <;> simp [signedLit, XPos],
        models_inl_lit lt _ b r₀ v htrue⟩
  | verumR h =>
    intro hob hcr hxf hpart
    exact ⟨⊤, h, by simp [XPos], by simp [models]⟩
  | weak d' hsub ih =>
    intro hob hcr hxf hpart
    obtain ⟨A, hA, hposA, hmodA⟩ := ih α hob hcr hxf (fun B hB => hpart B (hsub hB))
    exact ⟨A, hsub hA, hposA, hmodA⟩
  | @andI Γ φ ψ dφ dψ ihφ ihψ =>
    intro hob hcr hxf hpart
    set D := Deriv.andI φ ψ dφ dψ with hD
    have hposφψ : XPos (φ ⋏ ψ) := by
      rcases hpart (φ ⋏ ψ) (Finset.mem_insert_self _ _) with h | ⟨t, heq, _⟩ | hc
      · rw [Prog] at h; simp [Xat, Xsym] at h
      · simp [Xat] at heq
      · exact hc
    obtain ⟨hposφ, hposψ⟩ := hposφψ
    have hoφ : dφ.o ≤ D.o := by
      rw [hD]; simp only [Deriv.o]; exact le_trans (le_max_left _ _) (self_le_add_right _ 1)
    have hoψ : dψ.o ≤ D.o := by
      rw [hD]; simp only [Deriv.o]; exact le_trans (le_max_right _ _) (self_le_add_right _ 1)
    have hlφ : α + 2 ^ dφ.o ≤ α + 2 ^ D.o :=
      (add_le_add_iff_left α).mpr (Ordinal.opow_le_opow_right two_pos hoφ)
    have hlψ : α + 2 ^ dψ.o ≤ α + 2 ^ D.o :=
      (add_le_add_iff_left α).mpr (Ordinal.opow_le_opow_right two_pos hoψ)
    have crφ : dφ.cr = 0 := by
      have : dφ.cr ≤ 0 := by rw [hD] at hcr; simp only [Deriv.cr] at hcr; exact hcr ▸ le_max_left _ _
      exact nonpos_iff_eq_zero.mp this
    have crψ : dψ.cr = 0 := by
      have : dψ.cr ≤ 0 := by rw [hD] at hcr; simp only [Deriv.cr] at hcr; exact hcr ▸ le_max_right _ _
      exact nonpos_iff_eq_zero.mp this
    have hpartφ : Partition lt prec α (insert φ Γ) := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hBΓ
      · exact Or.inr (Or.inr hposφ)
      · exact hpart B (Finset.mem_insert_of_mem hBΓ)
    have hpartψ : Partition lt prec α (insert ψ Γ) := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hBΓ
      · exact Or.inr (Or.inr hposψ)
      · exact hpart B (Finset.mem_insert_of_mem hBΓ)
    obtain ⟨A, hA, hposA, hmA⟩ := ihφ α (le_trans hoφ hob) crφ hxf.1 hpartφ
    rcases Finset.mem_insert.mp hA with hAeq | hAΓ
    · rw [hAeq] at hmA
      obtain ⟨A', hA', hposA', hmA'⟩ := ihψ α (le_trans hoψ hob) crψ hxf.2 hpartψ
      rcases Finset.mem_insert.mp hA' with hA'eq | hA'Γ
      · rw [hA'eq] at hmA'
        exact ⟨φ ⋏ ψ, Finset.mem_insert_self _ _, ⟨hposφ, hposψ⟩,
          (models_and lt _ φ ψ).mpr ⟨models_mono lt hlφ hposφ hmA, models_mono lt hlψ hposψ hmA'⟩⟩
      · exact ⟨A', Finset.mem_insert_of_mem hA'Γ, hposA', models_mono lt hlψ hposA' hmA'⟩
    · exact ⟨A, Finset.mem_insert_of_mem hAΓ, hposA, models_mono lt hlφ hposA hmA⟩
  | @orI Γ φ ψ d' ih =>
    intro hob hcr hxf hpart
    set D := Deriv.orI φ ψ d' with hD
    have hposφψ : XPos (φ ⋎ ψ) := by
      rcases hpart (φ ⋎ ψ) (Finset.mem_insert_self _ _) with h | ⟨t, heq, _⟩ | hc
      · rw [Prog] at h; simp [Xat, Xsym] at h
      · simp [Xat] at heq
      · exact hc
    obtain ⟨hposφ, hposψ⟩ := hposφψ
    have ho : d'.o ≤ D.o := by rw [hD]; simp only [Deriv.o]; exact self_le_add_right _ 1
    have hl : α + 2 ^ d'.o ≤ α + 2 ^ D.o :=
      (add_le_add_iff_left α).mpr (Ordinal.opow_le_opow_right two_pos ho)
    have cr0 : d'.cr = 0 := by
      have : d'.cr ≤ 0 := by rw [hD] at hcr; simpa only [Deriv.cr] using hcr.le
      exact nonpos_iff_eq_zero.mp this
    have hpartd' : Partition lt prec α (insert φ (insert ψ Γ)) := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB'
      · exact Or.inr (Or.inr hposφ)
      · rcases Finset.mem_insert.mp hB' with rfl | hBΓ
        · exact Or.inr (Or.inr hposψ)
        · exact hpart B (Finset.mem_insert_of_mem hBΓ)
    obtain ⟨A, hA, hposA, hmA⟩ := ih α (le_trans ho hob) cr0 hxf hpartd'
    rcases Finset.mem_insert.mp hA with hAeq | hA'
    · rw [hAeq] at hmA
      exact ⟨φ ⋎ ψ, Finset.mem_insert_self _ _, ⟨hposφ, hposψ⟩,
        (models_or lt _ φ ψ).mpr (Or.inl (models_mono lt hl hposφ hmA))⟩
    · rcases Finset.mem_insert.mp hA' with hAeq | hAΓ
      · rw [hAeq] at hmA
        exact ⟨φ ⋎ ψ, Finset.mem_insert_self _ _, ⟨hposφ, hposψ⟩,
          (models_or lt _ φ ψ).mpr (Or.inr (models_mono lt hl hposψ hmA))⟩
      · exact ⟨A, Finset.mem_insert_of_mem hAΓ, hposA, models_mono lt hl hposA hmA⟩
  | @allω Γ χ d' ih =>
    intro hob hcr hxf hpart
    set D := Deriv.allω χ d' with hD
    have hposall : XPos (∀⁰ χ) := by
      rcases hpart (∀⁰ χ) (Finset.mem_insert_self _ _) with h | ⟨t, heq, _⟩ | hc
      · rw [Prog] at h; simp [Xat, Xsym] at h
      · simp [Xat] at heq
      · exact hc
    have hposχ : XPos χ := hposall
    have hole : ∀ n, (d' n).o ≤ D.o := fun n => by
      rw [hD]; simp only [Deriv.o]
      exact le_trans (Ordinal.le_iSup (fun m => (d' m).o) n) (self_le_add_right _ 1)
    have hcr0 : ∀ n, (d' n).cr = 0 := fun n => by
      have : (d' n).cr ≤ 0 := by
        rw [hD] at hcr; simp only [Deriv.cr] at hcr
        exact le_trans (le_iSup (fun m => (d' m).cr) n) hcr.le
      exact nonpos_iff_eq_zero.mp this
    have hl : ∀ n, α + 2 ^ (d' n).o ≤ α + 2 ^ D.o := fun n =>
      (add_le_add_iff_left α).mpr (Ordinal.opow_le_opow_right two_pos (hole n))
    by_cases hG : ∃ A ∈ Γ, XPos A ∧ models lt (α + 2 ^ D.o) A
    · obtain ⟨A, hAΓ, hposA, hmA⟩ := hG
      exact ⟨A, Finset.mem_insert_of_mem hAΓ, hposA, hmA⟩
    · refine ⟨∀⁰ χ, Finset.mem_insert_self _ _, hposall, (models_all lt _ χ).mpr (fun n => ?_)⟩
      obtain ⟨A, hA, hposA, hmA⟩ := ih n α (le_trans (hole n) hob) (hcr0 n) (hxf n)
        (by intro B hB
            rcases Finset.mem_insert.mp hB with rfl | hBΓ
            · exact Or.inr (Or.inr (xpos_subst n hposχ))
            · exact hpart B (Finset.mem_insert_of_mem hBΓ))
      rcases Finset.mem_insert.mp hA with hAeq | hAΓ
      · rw [hAeq] at hmA; exact models_mono lt (hl n) (xpos_subst n hposχ) hmA
      · exact absurd ⟨A, hAΓ, hposA, models_mono lt (hl n) hposA hmA⟩ hG
  | @exI Γ χ n d' ih =>
    intro hob hcr hxf hpart
    set D := Deriv.exI χ n d' with hD
    have ho : d'.o ≤ D.o := by rw [hD]; simp only [Deriv.o]; exact self_le_add_right _ 1
    have hl : α + 2 ^ d'.o ≤ α + 2 ^ D.o :=
      (add_le_add_iff_left α).mpr (Ordinal.opow_le_opow_right two_pos ho)
    have cr0 : d'.cr = 0 := by
      have : d'.cr ≤ 0 := by rw [hD] at hcr; simpa only [Deriv.cr] using hcr.le
      exact nonpos_iff_eq_zero.mp this
    rcases hpart (∃⁰ χ) (Finset.mem_insert_self _ _) with hPa | ⟨t, heq, _⟩ | hPc
    · -- **Buchholz case 2** (`∃⁰χ = ∼Prog`): invert the inner `hyp ⋏ ∼X` and combine the two IHs
      -- (outer IH on the inversion outputs, which strictly shrink the height). THE crux.
      have hχ : χ = ∼(hyp prec 🡒 Xat (#0)) := by
        have hPa' := hPa
        rw [show ∼(Prog prec) = ∃⁰ ∼(hyp prec 🡒 Xat (#0)) from by simp [Prog]] at hPa'
        injection hPa'
      subst hχ
      set φ₁ := (hyp prec)/[nm n] with hφ₁
      set φ₂ := ∼(Xat (nm n)) with hφ₂
      have hC : (∼(hyp prec 🡒 Xat (#0)))/[nm n] = φ₁ ⋏ φ₂ := chi_subst prec n
      have hposφ₁ : XPos φ₁ := xpos_subst n (hyp_xpos prec hprecXPos)
      -- height bookkeeping
      have hDo : D.o = d'.o + 1 := by rw [hD]; rfl
      have hd'β : d'.o < β := lt_of_lt_of_le (hDo ▸ lt_add_one d'.o) hob
      -- invert the conjunction `χ/[nm n] = φ₁ ⋏ φ₂`
      have hmemC : (φ₁ ⋏ φ₂) ∈ insert ((∼(hyp prec 🡒 Xat (#0)))/[nm n]) Γ :=
        hC ▸ Finset.mem_insert_self _ _
      set E := (insert ((∼(hyp prec 🡒 Xat (#0)))/[nm n]) Γ).erase (φ₁ ⋏ φ₂) with hE
      have hEsub : E ⊆ Γ := by
        intro e he
        rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase he) with rfl | hg
        · exact absurd hC (Finset.ne_of_mem_erase he)
        · exact hg
      obtain ⟨⟨d₁, hd₁o, hd₁cr, hd₁xf⟩, ⟨d₂, hd₂o, hd₂cr, hd₂xf⟩⟩ :=
        andInv_xfree d' hxf cr0 hmemC
      have hdβ₁ : α + 2 ^ d₁.o ≤ α + 2 ^ D.o :=
        (add_le_add_iff_left α).mpr (Ordinal.opow_le_opow_right two_pos (le_trans hd₁o ho))
      -- IH on premise (1): `insert φ₁ E`
      have hpart₁ : Partition lt prec α (insert φ₁ E) := by
        intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hBE
        · exact Or.inr (Or.inr hposφ₁)
        · exact hpart B (Finset.mem_insert_of_mem (hEsub hBE))
      obtain ⟨A₁, hA₁, hposA₁, hmA₁⟩ :=
        outerIH d'.o hd'β α d₁ hd₁o hd₁cr hd₁xf hpart₁
      rcases Finset.mem_insert.mp hA₁ with hA₁eq | hA₁E
      · -- (Case 2) the witness is `φ₁ = ∀y≺n Xy` ⟹ `|n|_≺ ≤ α + 2^{d'.o}`; feed IH on premise (2)
        rw [hA₁eq] at hmA₁
        have hmφ₁ : models lt (α + 2 ^ d'.o) φ₁ :=
          models_mono lt ((add_le_add_iff_left α).mpr
            (Ordinal.opow_le_opow_right two_pos hd₁o)) hposφ₁ hmA₁
        have hrkn : rk lt n ≤ α + 2 ^ d'.o := rk_le_of_forall lt ((hprec (α + 2 ^ d'.o) n).mp hmφ₁)
        -- IH on premise (2): `insert φ₂ E` at the bumped bound `α' = α + 2^{d'.o}`
        have hpart₂ : Partition lt prec (α + 2 ^ d'.o) (insert φ₂ E) := by
          intro B hB
          rcases Finset.mem_insert.mp hB with rfl | hBE
          · exact Or.inr (Or.inl ⟨nm n, rfl, by rw [tval_nm]; exact hrkn⟩)
          · rcases hpart B (Finset.mem_insert_of_mem (hEsub hBE)) with hP | ⟨s, hs, hbs⟩ | hP
            · exact Or.inl hP
            · exact Or.inr (Or.inl ⟨s, hs, le_trans hbs (self_le_add_right α _)⟩)
            · exact Or.inr (Or.inr hP)
        obtain ⟨A₂, hA₂, hposA₂, hmA₂⟩ :=
          outerIH d'.o hd'β (α + 2 ^ d'.o) d₂ hd₂o hd₂cr hd₂xf hpart₂
        rcases Finset.mem_insert.mp hA₂ with hA₂eq | hA₂E
        · rw [hA₂eq] at hposA₂; simp [φ₂, XPos, Xat, Xsym] at hposA₂
        · -- the witness sits in `E ⊆ Γ ⊆ Δ`; the level `(α+2^{d'.o})+2^{d₂.o}` ≤ `α + 2^{D.o}`
          have hpoweq : (2 : Ordinal) ^ D.o = 2 ^ d'.o + 2 ^ d'.o := by
            rw [hDo, show d'.o + 1 = Order.succ d'.o from rfl, Ordinal.opow_succ, Ordinal.mul_two]
          have hlev : (α + 2 ^ d'.o) + 2 ^ d₂.o ≤ α + 2 ^ D.o := by
            refine le_trans ((add_le_add_iff_left _).mpr
              (Ordinal.opow_le_opow_right two_pos hd₂o)) ?_
            rw [add_assoc, ← hpoweq]
          exact ⟨A₂, Finset.mem_insert_of_mem (hEsub hA₂E), hposA₂,
            models_mono lt hlev hposA₂ hmA₂⟩
      · -- (Case 1) the witness already sits in `E ⊆ Γ ⊆ Δ`
        exact ⟨A₁, Finset.mem_insert_of_mem (hEsub hA₁E), hposA₁,
          models_mono lt hdβ₁ hposA₁ hmA₁⟩
    · simp [Xat] at heq
    · -- Buchholz case 4 (X-positive `∃`): introduce the witness `n` and lift via monotonicity.
      have hposχ : XPos χ := hPc
      obtain ⟨A, hA, hposA, hmA⟩ := ih α (le_trans ho hob) cr0 hxf
        (by intro B hB
            rcases Finset.mem_insert.mp hB with rfl | hBΓ
            · exact Or.inr (Or.inr (xpos_subst n hposχ))
            · exact hpart B (Finset.mem_insert_of_mem hBΓ))
      rcases Finset.mem_insert.mp hA with hAeq | hAΓ
      · rw [hAeq] at hmA
        exact ⟨∃⁰ χ, Finset.mem_insert_self _ _, hPc,
          (models_ex lt _ χ).mpr ⟨n, models_mono lt hl (xpos_subst n hposχ) hmA⟩⟩
      · exact ⟨A, Finset.mem_insert_of_mem hAΓ, hposA, models_mono lt hl hposA hmA⟩
  | cut φ d₁ d₂ ih₁ ih₂ =>
    intro hob hcr hxf hpart
    exfalso
    have h1 : (↑φ.complexity + 1 : ℕ∞) ≤ 0 := hcr ▸ le_max_left _ _
    simp at h1

/-- **Boundedness Corollary** `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`, reduced to its post-inversion core:
from a cut-free `XFreeAx` derivation of `{¬Prog_≺(X), X(nm n)}` at height `≤ β` for **every** `n`
(what `embedC` + `cutElim` + the TI/∀ inversions supply), Boundedness gives `⊨^{2^β} X(nm n)`, i.e.
`|n|_≺ < 2^β` for all `n`, hence `‖≺‖ ≤ 2^β`. -/
theorem orderType_le_of_deriv (β : Ordinal.{0})
    (hprec : ∀ (γ : Ordinal.{0}) (n : ℕ),
      models lt γ ((hyp prec)/[nm n]) ↔ ∀ m : ℕ, lt m n → rk lt m < γ)
    (hprecXPos : XPos (∼ prec))
    (h : ∀ n, ∃ d : Deriv (insert (∼(Prog prec)) {Xat (nm n)}), d.o ≤ β ∧ d.cr = 0 ∧ XFreeAx d) :
    orderType lt ≤ 2 ^ β := by
  refine orderType_le_of_forall lt (fun n => ?_)
  obtain ⟨d, hdo, hdc, hdx⟩ := h n
  have hpart : Partition lt prec 0 (insert (∼(Prog prec)) {Xat (nm n)}) := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA'
    · exact Or.inl rfl
    · rw [Finset.mem_singleton] at hA'; subst hA'; exact Or.inr (Or.inr (by simp [Xat, XPos]))
  obtain ⟨A, hA, hposA, hmA⟩ :=
    boundedness lt prec hprec hprecXPos d.o 0 d (le_refl _) hdc hdx hpart
  rw [zero_add] at hmA
  rcases Finset.mem_insert.mp hA with rfl | hA'
  · exact absurd hposA (by simp [Prog, hyp, Xat, Xsym, XPos, Semiformula.imp_eq])
  · rw [Finset.mem_singleton] at hA'; subst hA'
    exact lt_of_lt_of_le ((models_Xat_nm lt (2 ^ d.o) n).mp hmA)
      (Ordinal.opow_le_opow_right two_pos hdo)

end Main

end GoodsteinPA.Boundedness
