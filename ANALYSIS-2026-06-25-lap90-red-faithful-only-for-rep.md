# Lap 90 — `red` is Buchholz `d[0]` ONLY for Rep-reducible chains; `redSoundGen` (full generality) is FALSE

## The finding

Decomposing `redSound` (`Crux2Blueprint.lean`) into a structural induction `redSoundGen : ∀ d,
ZDerivation d → ZDerivation (red d)` exposed a faithfulness gap in the lap-89 tag-4 dispatch (`iRK`).
**The general statement `redSoundGen` is false**, and its two K-branch sub-residuals
(`ZDerivation_red_zK_replace`, `ZDerivation_red_zK_splice`) are false **as stated** for arbitrary chains.

## Why (Buchholz Def 3.2 case 5.2, verbatim, paper md lines 74–88)

```
5. d = K^r_Π d₀…dₗ, Π = Γ→C, dᵢ ⊢ Πᵢ = Γᵢ→Aᵢ.
   j₀ minimal s.t. A_{j₀} ∈ {C,⊥} & ∀i≤j₀ (Γᵢ ⊆ Γ,A₀…A_{i−1}).
   d critical iff ∀i≤j₀ (tp(dᵢ) ⋪ Π).
   5.2 (d not critical): i ≤ j₀ minimal s.t. tp(dᵢ) ◁ Π.
     5.2.1 (dᵢ critical):     d[0] := K^{r'}_Π (i/dᵢ{0},dᵢ{1}),  r'=max{rk(A(dᵢ)),r}
     5.2.2 (dᵢ not critical): tp(d):=tp(dᵢ),  d[n] := K^r_{tp(d)(Π,n)}(i/dᵢ[n])
```

Two independent discrepancies between Buchholz and the repo's `iRK`/`red`:

1. **Conclusion change in 5.2.2.** Buchholz's `d[n]` has conclusion `tp(dᵢ)(Π,n)` — the conclusion is
   REDUCED by the selected premise's inference symbol. The repo's `iRKr = iCritAux d i (red dᵢ) = zK
   (fstIdx d) r (seqUpdate ds i (red dᵢ))` KEEPS `fstIdx = Π` (also `fstIdx_iRK = fstIdx d`). This matches
   Buchholz **iff `tp(dᵢ) = Rep`** (then `Rep(Π,0) = Π`). For `tp(dᵢ) = R_∀xF` (an I-rule premise) the
   conclusion becomes `Γ→F(n) ≠ Π`, so `iRKr` is unfaithful and the resulting chain is INVALID (the
   replaced premise `red dᵢ = dᵢ[0]` then derives `tp(dᵢ)(end dᵢ,0) ≠ end dᵢ`, breaking the threading
   `fstIdx (red dᵢ) = fstIdx dᵢ` that `ZDerivation_iCritAux_of` requires).

2. **`dᵢ` need not be a chain.** `5.2.1/5.2.2` dispatch on "`dᵢ` critical?", which only types when `dᵢ`
   is a chain. But `iperm (tp dᵢ) Π` (= `isPermPrem`) admits `tp dᵢ ∈ {isymR (I-rule), isymLk (axiom),
   isymRep}` — so the minimal permissible premise can be an **I-rule (when `Aᵢ = C`, only possible at
   `i = j₀`) or an axiom (`L^k_A` with `A ∈ Γ`)**. For such `dᵢ` the repo's sub-test `permIdx dᵢ <
   lh (zKseq dᵢ)` runs on a non-chain (`zKseq` of an axiom/atom is junk, `lh = 0`), mis-dispatches to
   `iRKs` (splice), and splices `znth (zKseq (red dᵢ)) {0,1}` = junk → invalid chain.

Minor third discrepancy: the repo's `permIdx` searches ALL premises `< lh ds`; Buchholz restricts the
permissibility/criticality search to `i ≤ j₀`. (Also the repo's `isChainInf` takes `j₀` existential, not
minimal.) These widen the set of selectable `dᵢ` beyond Buchholz's.

## The saving grace — Corollary 2.1 (the ⊥-orbit is all-`Rep`)

For `ZDerivesEmpty d` (Π = `→⊥`: `Γ = ∅`, `C = ⊥`) the selected premise is ALWAYS `Rep`:
- axiom premises `L^k_A` need `A ∈ Γ = ∅` — impossible;
- I-rule premises have succedent `∀xF`/`¬A`, never `⊥`, so `Aᵢ = ⊥` (forced for `i = j₀` since `C = ⊥`)
  can't be an I-rule, and for `i < j₀` permissibility via `R` needs `Aᵢ = C = ⊥` — impossible;
- so the only permissible premises are `Rep` (atom/Ind/chain), and `tp(d) = Rep`.

This is exactly **Buchholz Corollary 2.1: "`tp(d)` can only be `Rep` for `→⊥`"** — a `→⊥` derivation
reduces to another `→⊥` derivation, conclusion unchanged. So on the ⊥-orbit `red d = d[0]` faithfully,
and `iRKr` keeping `Π` is correct THERE.

## Consequence for the proof architecture

`redSound : ∀ d, ZDerivesEmpty d → ZDerivation (red d)` is the TRUE target; the over-general
`redSoundGen : ∀ d, ZDerivation d → ZDerivation (red d)` (current skeleton) is **false** and must be
replaced. But the structural recursion of `red` on a ⊥-chain still dives into NON-⊥ sub-derivations:
- 5.1 critical recurses on the auxiliaries' premise reducts `dᵢ[k]`, `dⱼ[0]` (subformula sequents);
- 5.2.2 recurses on `red dᵢ` for the selected `Rep` chain `dᵢ` (not a ⊥-derivation).

So the induction needs the **genuine Buchholz Thm 3.4(b) invariant**, which tracks the REDUCED sequent:
> `red d` is a `ZDerivation` of `tp(d)(end d, 0)` (not of `end d`).
The repo's `red` (always keeping `Π = fstIdx d` for chains) computes `d[0]` faithfully only when
`tp(d) = Rep`; for `tp(d) ≠ Rep` it has the WRONG endsequent. Therefore the right statement is roughly:

  `redSoundF : ∀ d, ZDerivation d → tp d = isymRep → ZDerivation (red d) ∧ fstIdx (red d) = fstIdx d`

with the cases where `tp d ≠ Rep` handled by a SEPARATE reduct that performs the conclusion reduction
`tp(d)(Π,0)` — i.e. the repo needs the **general `d[n]` reduct (with conclusion reduction), of which the
current `red` is the `Rep`-restricted shadow.** Two clean routes:

- **(A) Restrict to Rep (cheapest to headline).** Prove `redSound` for `ZDerivesEmpty` by a `⊥`-orbit
  induction: carry the invariant "every chain reached is critical-or-has-only-Rep-permissible-premises"
  (true on the ⊥-orbit by Cor 2.1 applied hereditarily to the reduct's premises). The 5.1 auxiliaries'
  premise-reducts `dᵢ[k]/dⱼ[0]` are reductions of I-rules/chains whose endsequents are tracked by
  Thm 3.4(a) — these need the general reduct, so (A) alone may not close without (B).
- **(B) Build the general `d[n]`** (conclusion-reducing) and prove Thm 3.4(b) verbatim
  (`red d ⊢ tp(d)(Π,0)`), then specialise to the ⊥-orbit where `tp = Rep ⟹ Π` unchanged. This is the
  faithful port but is more work (needs `tp`-driven conclusion reduction in the reduct).

## Immediate action (this lap)

- K-branch residuals (`ZDerivation_red_zK_replace/_splice`) get a WARNING docstring: false as stated;
  hold pending the Rep-restriction / general-`d[n]` decision. They are NOT to be "proven" as-is.
- `redSoundGen` similarly flagged: false in full generality; it is a scaffold, the real target is
  `redSound` over `ZDerivesEmpty` with the Thm-3.4 invariant.
- `red_zK_rep`/`red_zK_splice` (pure rewriting) and the 5 trivial `redSoundGen` cases REMAIN valid and
  reusable regardless of which route.

Next lap: pick route (A) vs (B). Recommendation: (A) first — try the ⊥-orbit invariant
`tp d = isymRep` carried through the induction, falling back to (B)'s general reduct only for the 5.1
auxiliaries if their endsequent tracking demands it.
