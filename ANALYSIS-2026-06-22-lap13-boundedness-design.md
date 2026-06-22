# ANALYSIS (lap 13) — Boundedness design, grounded in a full read of Buchholz §5 (pp. 26–31)

Lap 13 read `papers/buchholz-beweistheorie-lecture-notes.pdf` pp. 26–31 end-to-end (the `Z∞` system,
Thms 5.1–5.6, the X-positive truth semantics, the arithmetization of ordinals `< ε₀`). This doc records
the precise calculus + the **one real design subtlety** (S-dependence of the X-atom leaf) and the chosen
resolution, so the Boundedness formalization is faithful rather than improvised.

## What lap 13 SHIPPED (all green, in `src/`)
- `LangX.structLX (S : ℕ → Prop) : Structure LX ℕ` — the `⊨^S` carrier (standard `ℒₒᵣ` + `X ↦ S`) +
  the two `DecidableEq` instances + `eval_Xatom` (X t ⊨ iff S(val t)). The most-leveraged lego.
- `ZinftyGen.lean` — **M5 cut-elimination generalised over `{L}[ORing L][Structure L ℕ][DecEq…]`**,
  `Provable.cutElim` `#print axioms = [propext, choice, Quot.sound]`. The big mechanical port; confirms
  VERIFY-(a) was right (plumbing, not math).
- `wip/BoundednessProbe.lean` `Xatom_axiom` — the Buchholz X-atom axiom `{Xs,¬Xt}` (sᴺ=tᴺ) is derivable
  in the generic calculus at `(LX, structLX S)` **for any S** (it is `S n ∨ ¬S n`). Green.

## Buchholz's `Z∞`, verbatim (the exact objects to formalize)

- **Language** `ℒ₀(X) := ℒ₀ ∪ {X}` (one unary set variable). = our `LX`.
- **Axioms** `AX(Z∞)` = sequents `Δ` of closed literals with **either** `Δ ∩ TRUE₀ ≠ ∅`
  (TRUE₀ = true closed **X-free** atomic literals) **or** `{Xs, ¬Xt} ⊆ Δ` with `sᴺ = tᴺ`.
- **Rules** `(Ax_Δ)`, `(⋀_A)` (ω-rule / all conjuncts), `(⋁^μ_A)` (one disjunct), `(Cut_C)`, `(Rep)`.
  Judgement `Z∞ ⊢^α_m Γ`: height `α`, all cut-formulas have `rk < m`.
- **Thm 5.1** `R_C`: `⊢^α_m Γ,C` & `⊢^β_m Γ,¬C` & `rk C ≤ m` ⟹ `⊢^{α#β}_m Γ`. = our `cutReduce*`/`atomCut`.
- **Thm 5.2** `E`: `⊢^α_{m+1} Γ` ⟹ `⊢^{3^α}_m Γ`. = our `cutElimStep` (we use ω-towers; both stay `<ε₀`).
- **Thm 5.3** Inversion. = our inversions.
- **Truth semantics**: `|n|_≺ := sup{|i|_≺+1 : i ≺ n}` (≺-rank), `‖≺‖ = sup{|n|_≺+1}` (order type),
  `⊨^α A :⟺ (ℕ, {n : |n|_≺ < α}) ⊨ A`, `⊨^α {A₁,…,A_k} :⟺ ⊨^α A₁ ∨ … ∨ ⊨^α A_k`.
  `Prog_≺(F) := ∀x(∀y≺x F y → F x)`, `TI_≺(F) := Prog_≺(F) → ∀x F x`. `Γ` **X-positive** = no `¬Xt` sub.
- **Thm 5.4 (Boundedness)** `Γ` X-positive: `Z∞ ⊢^β_1 ¬Prog_≺(X),¬Xs₁,…,¬Xs_k,Γ` & `|sᵢ|_≺ ≤ α`
  ⟹ `⊨^{α+2^β} Γ`. Induction on `β` over the cut-free derivation; **8 cases** (p.29), each ≤4 lines:
  1.1 `Ax`, TRUE₀ hit — trivial. 1.2 `Ax`, X-pair `Xt,¬Xs` (tᴺ=sᴺ) — `|t|=|s| ≤ α < α+2^β` ⟹ `⊨ Xt`.
  2 last = `⋁` on `¬Prog` (= `∃x(∀y≺x Xy ∧ ¬Xx)`): invert (5.3a) to (1) `…,∀y≺s₀ Xy` & (2) `…,¬Xs₀`;
    IH on (1); Case |s₀|<α+2^β done else IH-(2) gives `|s₀|≤α+2^{β₀}`. 3 `⋀ C` / 4 `⋁ C` (C∈Γ): IH +
    X-positivity. 5 `Rep`: IH. 6 `Cut` on `C∈TRUE₀`: IH on both, `⊨ ¬C` impossible. 7 `Cut Ys` (Y≠X):
    `0=0` reduction. 8 `Cut Xs₀`: (1) `…,Xs₀` (2) `…,¬Xs₀`; IH-(1) then `|s₀|<α+2^{β₀}`; combine with
    IH-(2) at `α+2^{β₀}`.
  - **Corollary** `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`: invert TI to `⊢^β_1 ¬Prog,Xn` ∀n; 5.4 (α=0,k=0) ⟹
    `⊨^{2^β} Xn` ∀n ⟹ `|n|<2^β` ∀n ⟹ `‖≺‖ ≤ 2^β`.
- **Thm 5.5 (Embedding)** closed `Z`-derivation ⟹ `Z∞ ⊢^{ō(d)}_{dg(d)} Γ`; Cor: `Z ⊢ Γ` ⟹ `⊢^{ω·k}_m Γ`.
  Induction lifts `∀` to ω-rule, `Ind^{x,t}_F` to a tower of `Cut_{F(i)}` (the meta-induction). = our M4
  `embedC` (which already gives `∃ c ∀ e ∃ α, Provable α c …`).
- **Thm 5.6** `Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`. Proof = 5.5 then 5.2 (iterate to cut-free, height `< ε₀`)
  then 5.4-Cor (`‖≺‖ ≤ 2^β < ε₀` since ε₀ ε-number). **This is PA ⊬ TI(ε₀).**
- **Arithmetization** (p.32): `OT ⊆ ℕ` ordinal notations + `≺` primitive-recursive, `o : OT → ε₀` an
  iso onto `[0,ε₀)`, `|a|_≺ = o(a)` (Cor to Lemma 5.10). `(OT,≺)` is the ε₀-order with `‖≺‖ = ε₀`.

## THE design subtlety: the X-atom leaf is S-dependent, but must be used S-independently

Our generic `ZinftyGen` folds **both** Buchholz leaf kinds into ONE truth rule
`axTrue : LitTrue (signedLit b r v) → … ` where `LitTrue φ := Evalm ℕ φ` under the **ambient**
`[Structure L ℕ]`. At `L = LX` there is **no canonical** `Structure LX ℕ` — truth of `X t` needs a
chosen `S`. So:
- X-**free** literal: `LitTrue` = real arithmetic truth = **S-independent** (matches Buchholz TRUE₀). ✓
- X-atom **pair** `{Xs,¬Xt}` (sᴺ=tᴺ): derivable under `structLX S` for **any** S (it's `S n ∨ ¬S n`).
  ✓ = `BoundednessProbe.Xatom_axiom`. So the Buchholz X-pair axiom is **free** from our truth leaf.
- A **lone** `Xs` axTrue leaf would require `S(sᴺ)` — **S-dependent**, and **NOT** a Buchholz axiom.

Why it matters: in the Corollary, ONE fixed derivation `d : Z∞ ⊢^β_1 ¬Prog,Xn` is re-interpreted by
Boundedness at **varying** sets `U^γ = {m : |m|_≺ < γ}` (the IH lowers the exponent `β→β₀`, hence the
set). For the induction to go through, every axTrue **leaf** of `d` must be true under **every** `U^γ`
relevant — i.e. leaf truth must be **U-independent**. X-free leaves and X-pair leaves are U-independent;
a lone-`Xs` leaf is not (it would need `|s|_≺ < (the specific γ)`).

**Resolution (the architecture for the Boundedness file):**
1. `⊨^γ A` is defined with the structure passed **explicitly**: `Eval (structLX {n | |n|_≺ < γ}) ![] id A`
   — NOT via an ambient instance. So the exponent-indexed set is first-class and can vary in the proof.
2. The derivation `d` lives over an **ambient** `[Structure LX ℕ]` (whatever the embedding built it under).
   Boundedness is proved by induction on `d`'s `Deriv`, producing `⊨^γ` facts. The bridge from a leaf to
   `⊨^γ` is:
   - **X-free invariance lemma** (NEW, light): `Eval (structLX S) e ε φ = Eval (structLX S') e ε φ`
     for `φ` with no `Xsym` atom — so a true X-free leaf is `⊨^γ`-true for every γ. Proof: induction on φ
     (the only structure-touching case is the atom, and X-free atoms don't read the `X ↦ ·` component).
   - **X-pair** leaf: handled structurally (always `⊨^γ`), independent of the ambient structure.
   - **lone-Xs** leaf: does NOT occur in the derivations we feed (the embedding of `Z ⊢ TI(X)` never
     asserts a bare `Xs` — PA(X)'s axioms are X-free + induction, and TI is an implication). To keep the
     theorem self-contained, Boundedness carries a hypothesis `XPositive`/`NoLoneXLeaf` ruling it out, OR
     (cleaner) is stated for derivations whose X-atom leaves are pairs — discharged by the embedding.

So **no re-proof of cut-elim is needed**: `ZinftyGen` is reused wholesale; the only new pieces are the
truth semantics + the X-free-invariance lemma + the 8-case Boundedness induction. This is the plan.

## Lap-13 NEXT (in order)
1. **Truth-semantics layer** (`wip/TruthSem.lean`, importing `ZinftyGen`+`LangX`): `rank ≺ n` (`|n|_≺`),
   `orderType ≺` (`‖≺‖`), `models γ A` (`⊨^γ`, via explicit `structLX`), `Sat γ Γ` (sequent), `Prog`,
   `XPositive`. Plus the **X-free invariance** lemma. All light/self-contained.
2. **Boundedness (Thm 5.4)** — the 8-case induction on `Deriv` over `LX`. THE new theorem.
3. **Corollary** `‖≺‖ ≤ 2^β`, then assemble with M4 (`embedC` over LX) + M5 (`cutElim`) for **Thm 5.6**.
4. **Goodstein ⟹ TI_≺(X)** bridge (VERIFY-(b)) + arithmetization seam (OT↔ε₀) ⟹ headline.

## Still to settle (flag for a literature/online request if it bites)
- M4 (`embedC`) is currently hardwired to `ℒₒᵣ`; needs the same `{L}` generalisation as M5 (mechanical),
  **and** PA-over-LX with induction extended to L(X)-formulas (Buchholz's `Z`). The truth of all PA(X)
  axioms in `structLX S` (any S) — induction included — holds because first-order induction over ℕ is
  valid for any fixed unary predicate `S`. Confirm when porting `embedC.axm`/`provable_true`.
