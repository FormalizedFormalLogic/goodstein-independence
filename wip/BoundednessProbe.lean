/-
# `wip/BoundednessProbe.lean` — instantiate the generic Z∞ at `(LX, structLX S)` (lap-13)

Validates that the generic M5 (`ZinftyGen`) instantiates at the Buchholz language `LX` with the
`⊨^S` carrier `structLX S`, and — crucially — that the **X-atom axiom** of Buchholz §5
(`Xs, ¬Xt` for `sᴺ = tᴺ`) is derivable in the generic calculus *for any* `S`, as `S n ∨ ¬S n`.
(See `ANALYSIS-2026-06-22-lap13-boundedness-design.md`: the X-atom axiom must be S-independent —
this lemma is exactly that fact, the reason ZinftyGen's truth-leaf `axTrue` suffices for the
Buchholz route despite `structLX S` having no canonical instance.)
-/
import GoodsteinPA.ZinftyGen
import GoodsteinPA.LangX

namespace GoodsteinPA.BoundednessProbe

open LO LO.FirstOrder
open GoodsteinPA.ZinftyGen GoodsteinPA.ZinftyGen.Deriv GoodsteinPA.LangX

section
variable (S : ℕ → Prop) [inst : Structure LX ℕ] (hinst : inst = structLX S)
include hinst

/-- **The Buchholz X-atom axiom, generically.** With the ambient ℕ-model of `LX` being `structLX S`,
for closed terms `s t` of equal ℕ-value the Tait sequent `{X s, ¬X t}` is `Z∞`-derivable at
height/rank `0`, for *any* `S` (it is `S(sᴺ) ∨ ¬S(tᴺ)`, decided by `em` since `sᴺ = tᴺ`). -/
theorem Xatom_axiom (s t : Semiterm LX ℕ 0)
    (hval : Semiterm.valm ℕ ![] id s = Semiterm.valm ℕ ![] id t) :
    Provable 0 0 ({signedLit true Xsym ![s], signedLit false Xsym ![t]} : Seq LX) := by
  subst hinst
  letI : Structure LX ℕ := structLX S
  by_cases h : S (Semiterm.valm ℕ ![] id s)
  · -- `X s` is true.
    refine Provable.axTrue true Xsym ![s] ?_ (by simp)
    show LitTrue (signedLit true Xsym ![s])
    simp only [signedLit, LitTrue, Semiformula.eval_rel₁, Xsym]
    exact h
  · -- `¬X t` is true, since `tᴺ = sᴺ ∉ S`.
    refine Provable.axTrue false Xsym ![t] ?_ (by simp)
    show LitTrue (signedLit false Xsym ![t])
    have ht : ¬ S (Semiterm.valm ℕ ![] id t) := hval ▸ h
    simp only [signedLit, LitTrue, Semiformula.eval_nrel₁, Xsym]
    exact ht

end

end GoodsteinPA.BoundednessProbe
