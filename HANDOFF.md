# HANDOFF — 2026-06-22 (lap 13)

> **Branch** `plan` · HEAD `2c9f625` · 10 commits this lap · working tree clean · build **green**
> (`lake build GoodsteinPA`, 1264 jobs) · headline `peano_not_proves_goodstein` = honest `sorry`
> (`[propext, sorryAx, choice, Quot.sound]`, 0 math axioms — anti-fraud guard intact).
> **Lap 13 EXECUTED the Buchholz Boundedness route: read §5 end-to-end and built ALL the
> Boundedness prerequisites green + axiom-clean in `src/`.** Read
> `ANALYSIS-2026-06-22-lap13-boundedness-design.md` FIRST, then `PENDING_WORK.md` (lap-13 top).

## ✅ Lap-13 deliverables (all green, axiom-clean, promoted to `src/`)
1. **`LangX.lean`** — `structLX (S:ℕ→Prop) : Structure LX ℕ`, the **`⊨^α` carrier** (standard `ℒₒᵣ` +
   `X↦S`) + the two `DecidableEq` instances + `eval_Xatom`. Was lap-13 task (i), the most-leveraged lego.
2. **`ZinftyGen.lean`** — **M5 cut-elim generalised over `{L}[ORing L][Structure L ℕ][DecEq…]`**
   (the whole 1564-line Z∞, mechanical port). `Provable.cutElim` `#print axioms` clean. Reused wholesale.
3. **`TruthSem.lean`** — `rk`(`|n|_≺`)/`orderType`(`‖≺‖`)/`levelSet`(`U^γ`)/`models`(`⊨^γ`)/`Sat` +
   **`models_lMap` (X-FREE INVARIANCE)** + `orderType_le_of_forall`.
4. **`XPositive.lean`** — `XPos` + **`models_mono` (⊨^γ monotone in γ on X-positive formulas)** +
   `eval_mono`/`val_structLX_eq`.
5. **`Boundedness.lean`** — `Prog_≺(X)`/`TI_≺(X)`/`Xat` formula scaffolding over `LX` (de-Bruijn shapes
   + inversion shapes verified) **+ the corollary's downstream half**: `val_nm_structLX`,
   `models_Xat_nm` (`⊨^γ X(nm n) ↔ |n|_≺<γ`), `orderType_le_of_models_Xat` (`∀n ⊨^γ X(nm n) ⟹ ‖≺‖≤γ`).
   So once Boundedness 5.4 supplies `⊨^{2^β} Xn ∀n`, the corollary `‖≺‖ ≤ 2^β` is **already wired**.
6. **`wip/BoundednessProbe.lean`** — `Xatom_axiom`: the Buchholz X-atom axiom `{Xs,¬Xt}` (sᴺ=tᴺ) is
   derivable in generic Z∞ at `(LX,structLX S)` for **any** S. (Validation; stays in wip.)

## 🎯 THE crux still open — Boundedness Thm 5.4 (the 8-case induction)
All ingredients are now in place. **KEY SIMPLIFICATION found this lap:** our `cutElim` reduces to
**cut-rank `0`** (fully cut-free), and Buchholz's Boundedness is stated for `⊢^β_1`; a `c=0` derivation
is a special case, and at `c=0` there is **no `cut` node** (a cut has `cr ≥ 1`). So Boundedness for
`Provable β 0` needs **NO cut cases** — Buchholz's cases 6/7/8 are vacuous. The induction on the
`Deriv` over `LX` then has cases:
- `axL`/`axTrue`/`verumR` = Buchholz case 1 (Ax): true X-free literal → `models_lMap`; X-pair `{Xs,¬Xt}`
  → `Xatom_axiom`-style reasoning (`|s|_≺ = |t|_≺ ≤ α < α+2^β`).
- `weak` = Rep/structural (case 5): IH + `Sat` weakening.
- `andI` = case 3 (⋀ C, C∈Γ): IH on both + X-positivity (`models_mono`).
- `orI` = case 4 (⋁ C): IH.
- `allω` = the inner `∀y≺x` / Γ-∀: IH over the numeral family.
- `exI` = **case 2 (the heart): principal `∃` is `¬Prog` ⟹ invert (`allInv` on the inner `∀y≺x`) to get
  `…,∀y≺s₀ Xy` and `…,¬Xs₀`, IH both, combine** (else principal is a Γ-`∃`, = case 4). Conclude
  `Sat lt (α+2^β) Γ`. Uses `models_mono` for the `β₀≤β` exponent bumps.
Then **Corollary** `‖≺‖ ≤ 2^β` — **already wired** via `orderType_le_of_models_Xat` (just feed it the
Boundedness output `∀n, ⊨^{2^β} (Xat (nm n))`).

## 🎯 After Boundedness — assemble the headline
- **M4 `embedC` over LX** (mechanical `{L}` generalisation like M5; PA(X) axioms are true in
  `structLX S` for *any* S, since first-order induction holds for any fixed unary predicate) ⟹ Thm 5.5.
- **Thm 5.6** `Z⊢TI(X) ⟹ ‖≺‖<ε₀` = 5.5 + cutElim (to `c=0`, height `<ε₀`) + 5.4-Corollary.
- **Goodstein⟹TI_≺(X)** bridge (VERIFY-(b)) + arithmetization seam (OT↔ε₀, `‖≺‖=ε₀`) ⟹ discharge headline.

## Notes
- **LOCKED untouched:** `Defs.lean`, `Bridge.lean` RHS, `goodsteinTerminates`, headline `sorry` intact.
- **Build:** `lake build GoodsteinPA` (1264). Test wip via `lake env lean wip/<f>.lean`.
- **Literature on disk:** Buchholz §5 = the route (`papers/buchholz-beweistheorie-lecture-notes.pdf`
  pp.26–31, READ this lap; the precise statements are quoted in the lap-13 analysis doc). Read PDFs via
  the `pages` param. No open `ON-LINE-REQUEST.md`. `WebFetch` dead; `WebSearch` works.
- **Aristotle:** idle. Next genuinely-open self-contained lemma to feed: the `exI`/`¬Prog`-inversion
  core of Boundedness once its statement is pinned, or the OT↔ε₀ order-type seam.
- **Banked off-path (do NOT resume):** witness-bounded `wip/` calculi (Towsner/operator-H). The ℒₒᵣ-only
  `src/Zinfty.lean`/`src/Embedding.lean` stay for existing users; the live chain uses the LX versions.

## Lap-13 commits (8)
structLX carrier · generic M5 (axiom-clean) · promote LangX+ZinftyGen · X-atom probe + Buchholz
design doc · TruthSem (⊨^γ + X-free invariance) · XPositive (⊨^γ monotonicity) · Boundedness
Prog/TI scaffolding · PENDING/HANDOFF refresh.
