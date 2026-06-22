# ANALYSIS (lap 12) — PIVOT: Buchholz's **Boundedness** route reuses M4+M5 and AVOIDS the witness-bounded wall

**TL;DR.** Reading Buchholz "Beweistheorie" §5 (`papers/buchholz-beweistheorie-lecture-notes.pdf`,
pp. 26–31) end-to-end shows the project took the HARD road. The standard Gentzen-style ordinal analysis
of PA bounds PA's proof-theoretic ordinal via the **witness-FREE** infinitary `Z∞` (height `α`, cut-rank
`m`) plus a **Boundedness** theorem about `TI_≺(X)` — *not* via Towsner's witness-bounded calculus. The
two pieces this needs, **Embedding** and **Cut-Elimination**, are EXACTLY our done-and-axiom-clean **M4
`embedC`** and **M5 `Provable.cutElim`**. The genuinely-new work is **Boundedness (Thm 5.4)** — one clean
induction on a cut-free derivation with an `X`-positive truth semantics — plus the **Goodstein ⟹ TI(ε₀)**
bridge. The §19.6 witness-bounded cut-elim wall (lap-12 proved it needs the Buchholz operator `H`, a
multi-lap build) is **entirely off this route**. This is a course-correction BACK to `DIRECTION.md`'s
original Gentzen plan, after the lap-4→11 drift into Towsner's harder variant.

## Buchholz §5 — the route, verbatim (the precise statements to formalize)

`Z` = PA in Tait/sequent form (with set variables `X₀,X₁,…`, unary predicate symbols). `Z∞` = its
infinitary version: ω-rule `⋀_{∀xA}` over all numerals, `TRUE₀` axioms (`A` for `A ∈ TRUE₀`), atoms
`Xs,¬Xt` (for `sᴺ=tᴺ`), `Cut`, `Rep`. Judgement `Z∞ ⊢^α_m Γ` = derivation of height `α`, cut-rank `< m`.

- **Thm 5.1 (cut reduction `R_C`):** `d ⊢^α_m Γ,C  &  e ⊢^β_m Γ,¬C  &  rk(C) ≤ m  ⟹  R_C(d,e) ⊢^{α#β}_m Γ`.
  (`#` = natural sum.) — **= M5 `cutReduceConj/Disj/All` + `atomCut`.**
- **Thm 5.2 (cut-rank reduction `E`):** `d ⊢^α_{m+1} Γ  ⟹  E(d) ⊢^{3^α}_m Γ`. — **= M5 `cutElimStep`** (M5 uses
  `ω^α`-style towers; Buchholz `3^α`; both stay `< ε₀`, the only thing that matters).
- **Thm 5.3 (Inversion):** `Z∞ ⊢^α_m Γ,⋀_{ι}A_ι ⟹ Z∞ ⊢^α_m Γ,A_ι`, and the `∨` form. — **= M5 inversions.**
- **Thm 5.4 (BOUNDEDNESS) — THE NEW PIECE.** For `≺` wellfounded and `Γ` **X-positive** (no `¬Xt`
  subformula): `Z∞ ⊢^β_1 ¬Prog_≺(X), ¬Xs₁,…,¬Xsₖ, Γ  &  |s₁|_≺,…,|sₖ|_≺ ≤ α  ⟹  ⊨^{α+2^β} Γ`,
  where `⊨^α A :⟺ (ℕ, {n : |n|_≺ < α}) ⊨ A` (truth with `X` read as the ≺-initial-segment of norm `< α`),
  `|n|_≺` = ≺-rank, `‖≺‖` = order type, `Prog_≺(F) := ∀x(∀y≺x F(y) → F(x))`,
  `TI_≺(F) := Prog_≺(F) → ∀x F(x)`. Proof: induction on `β` over the cut-free derivation (8 rule cases,
  each a few lines; cf. p.29). **Corollary:** `Z∞ ⊢^β_1 TI_≺(X) ⟹ ‖≺‖ ≤ 2^β`.
- **Thm 5.5 (Embedding):** `Z ⊢ Γ` (Γ closed) `⟹ Z∞ ⊢^{ω·k}_m Γ` for some `k,m < ω`. — **= M4 `embedC`**
  (embedC gives the existential `∃ c, ∀ e, ∃ α, Provable α c …`; the finite height `ω·k` is what cut-elim
  then consumes — any `α < ε₀` suffices for Boundedness).
- **Thm 5.6:** `Z ⊢ TI_≺(X) ⟹ ‖≺‖ < ε₀`. **Proof = 5.5 then 5.2 (iterate to cut-free, height `< ε₀`)
  then 5.4-Corollary (`‖≺‖ ≤ 2^β < ε₀`, since `ε₀` is an ε-number).** ∎ This is PA ⊬ TI(ε₀).
- **Thm 5.9 (Beckmann sharpening, optional):** `Z_m ⊢ TI_≺(X) ⟹ ‖≺‖ < ω_{m+1}` — not needed for ε₀.

## Why Boundedness AVOIDS the lap-11 obstruction (the conflation that caused the drift)

Lap 11 correctly disproved **witness**-boundedness on the witness-free cut-free `Z∞`: `∃y g_y(5)=0` is
true, has a cut-free derivation at height `1` (one `exI` over an `axTrue` leaf), with witness `G(5)`
(astronomically large) — so HEIGHT does NOT bound witnesses, and naive witness-extraction is dead. From
this lap 11 concluded "the witness bound must live in the calculus ⟹ Towsner's witness-bounded `Zᵏ`" and
put the §19.6 wall back on the critical path. **That inference skipped Buchholz's actual fix:** Boundedness
(5.4) is NOT witness-extraction. It bounds the **order type** of `≺` using the **set variable `X` and
X-positivity** with the truth semantics `⊨^α` (`X` = the ≺-initial segment of rank `< α`). The `exI`-with-
huge-witness move is irrelevant — `X` appears positively and is pinned to the *actual* order, so a cut-free
proof of `TI_≺(X)` at height `β` genuinely forces `‖≺‖ ≤ 2^β`. No witness ever needs bounding.

So "boundedness" (Buchholz, TI/order-type — VALID, reuses M5) was conflated with "witness boundedness"
(Towsner, Hardy/`Zᵏ` — needs the operator-`H` wall). The lap-12 §19.6 result (`cutReduceAllAux`,
norm-machinery, axiom-clean, banked in `wip/OperatorZinfty.lean`) and lap-12 ADDENDUM 7 (numeric witness
control provably insufficient — needs operator `H`) together show the Towsner road is a genuine multi-lap
wall. The Buchholz road sidesteps it.

## What is REUSED vs NEW (the new critical path)

**Reused, already done & axiom-clean:**
- **M5** `src/Zinfty.lean` `Provable α c` + `cutElim`/`cutReduce*`/inversions = `Z∞` + Thms 5.1/5.2/5.3.
- **M4** `src/Embedding.lean` `embedC` + `provable_true` (ω-completeness) + `provable_em*` = Thm 5.5.
- **Phase 0** `Defs.lean`/`Encoding.lean` — the base-bumping ↔ CNF-ordinal encoding (feeds Goodstein⟹TI).

**New (the lap-13+ plan):**
1. **Set variable `X`** in the `Z∞` language: extend `ℒₒᵣ` → `ℒₒᵣ ∪ {X}` (one unary predicate). M5's
   logical rules + cut-elim are language-generic; `embedC`'s `axm` case (`provable_true`) only needs the
   PA axioms (which are `X`-free), so it extends. **Verify early:** that M5/M4 re-parametrise over the
   language cleanly (or add `X` as a fixed extra relation symbol).
2. **Truth semantics `⊨^α Γ`** (`X` := `{n : |n|_≺ < α}`) over `Z∞` sequents, + `Prog_≺`, `|n|_≺`, `‖≺‖`,
   X-positivity. Light, self-contained arithmetic/ordinal defs.
3. **Boundedness (Thm 5.4)** — induction on the cut-free `Provable β 0`-derivation (the 8 cases of p.29).
   THE new theorem. Clean (no Hardy, no witness bound).
4. **Goodstein ⟹ TI_≺(X)** for an `ε₀`-order `≺` (the bridge): PA ⊢ "every Goodstein sequence terminates"
   ⟹ PA ⊢ `TI_≺(X)` for the CNF-ε₀ order (Goodstein descent = ε₀-descent; Kirby–Paris/Cichoń). Reuses
   Phase-0 encoding. **Verify early:** the exact instance/shape (free `X` vs the arithmetic instance).
5. **Assembly:** PA ⊢ Goodstein ⟹ PA ⊢ TI_≺(X) ⟹ (5.6) `‖≺‖ < ε₀`, but the ε₀-order has `‖≺‖ = ε₀` ⟹
   `False` ⟹ discharge the headline `sorry`. `#print axioms` must be clean.

**Dropped from the critical path (banked, not deleted):** M6 (Hardy lower bound `lowerBound_hardy_self
contained`, the `B` calculus) — Towsner-specific, a correct theorem but not on the Buchholz route. The
witness-bounded `wip/` calculi (`Zekd` etc.) — banked; lap-12 `cutReduceAllAux` norm-machinery stays as
reference for the (now off-path) operator-`H` build.

## Confidence + the two things to verify on lap 13 before full commit

**High confidence** this is the right route: it is the literature-standard Gentzen analysis (Buchholz §5,
Buss Handbook ch.II), it reuses the two hardest done pieces (M4+M5), and the alternative is provably walled
(ADDENDUM 7). It is also a return to `DIRECTION.md`'s original "Gentzen ordinal analysis, TI(ε₀)" plan.
**Two early checks** (do these first on lap 13, before deep work): (a) M5/M4 cleanly accommodate the set
variable `X` (extend language or add a fixed relation symbol); (b) the Goodstein ⟹ TI_≺(X) bridge's exact
statement is provable in PA with the Phase-0 encoding. If both clear, execute steps 2–5. Neither is a known
wall (unlike the operator-`H`), but both are unverified, so confirm before sinking laps.
