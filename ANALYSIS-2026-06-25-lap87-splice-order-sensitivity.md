# Lap 87 — the 5.2.1 splice VALIDITY object must be ordered insert-at-`i`, not the banked end-append model

**Operator objective:** discharge `peano_not_proves_goodstein` axiom-free. Sole blocker = crux-2 =
`redSound` (internalized cut-elimination). Lap-86 isolated the genuinely-new content of the 5.2.1
sub-critical splice case to "(a) the splice OBJECT + (b) its `zKValidF`". This lap lands a reusable piece
of (b) AND surfaces a precise object-correctness finding that retargets the splice validity build.

## What landed (green, axiom-clean `[propext, choice, Quot.sound]`)
`InternalZ.lean`, after `zKValidF_seqUpdate`:
- splice end-sequent read-outs `chainAsucc`/`chainAnt`_{`seqCons_seqUpdate_{top,lt}`, `seqUpdate_{self,of_ne}`};
- **`isChainInf_iSpliceEnd`** — reduces `isChainInf` of the end-append splice `seqCons (seqUpdate ds j a) b`
  to local end-sequent threading hypotheses (mirror of `isChainInf_of_last`, `j₀ = lh ds`);
- **`zKValidF_iSpliceEnd`** — reduces faithful validity of that splice to the `isChainInf` core + per-half
  well-formedness; off-`j`/below-top conjuncts inherit from the original chain, at-`j`/top from the halves.

These are correct REDUCTIONS regardless of object choice (they take threading as hypotheses).

## The finding — VALIDITY is order-sensitive; the banked descent object is end-append (order-free)
Buchholz Def 3.2, the chain-rule abbreviation (paper md line 75):

> `K^r_{Π'}(i/d'ᵢ … d'_m) := K^r_{Π'} d₀ … d_{i−1} d'ᵢ … d'_m d_{i+1} … dₗ`

So **5.2.1** `d[0] := K^{r'}_Π (i/dᵢ{0}, dᵢ{1})` is the **ordered in-place splice**

  `d₀ … d_{i−1}  dᵢ{0}  dᵢ{1}  d_{i+1} … dₗ`     (`r' = max{rk(A(dᵢ)), r}`, premise `i` → two halves, order kept).

The chain-validity side condition (paper md line 76, = `isChainInf`):

> `j₀` minimal s.t. `A_{j₀} ∈ {C,⊥}` & `∀i ≤ j₀ ( Γᵢ ⊆ Γ, A₀,…,A_{i−1} )`

threads each premise's antecedent **only to STRICTLY-EARLIER succedents** `A₀…A_{i−1}` (or the conclusion
antecedent `Γ`). This is order-SENSITIVE.

Why the cut threads under the ordered splice: by Thm 3.4(a) applied to the critical premise `dᵢ`,
`dᵢ{0} ⊢ Γᵢ → A(dᵢ)` (succedent = cut subformula `A(dᵢ)`) and `dᵢ{1} ⊢ A(dᵢ), Γᵢ → Aᵢ` (antecedent gains
`A(dᵢ)`, succedent = the ORIGINAL `Aᵢ`). In the ordered splice `dᵢ{0}` sits at index `i`, `dᵢ{1}` at `i+1`:
- `dᵢ{1}`'s new antecedent formula `A(dᵢ)` threads back to `dᵢ{0}`'s succedent at `i < i+1`. ✓
- `dᵢ{1}`'s succedent is `Aᵢ` — RESTORING the succedent that downstream premises (now shifted `+1`) thread to.
- all `d_{i+1…l}` shift `+1`; relative order — hence all threading indices — preserved. ✓

**The banked ordinal-descent model `seqCons (seqUpdate ds j a) b`** (lap-82: `iord_descent_iSpliceEnd`,
`iotil_iSpliceEnd_lt`, `idg_iSpliceEnd_le`) puts the in-place half at `j` and the OTHER half `b` at the
very END (index `lh ds`). That is fine for the ordinal `õ` = `#`-fold = `⨆ ω^{õ·}` natural sum, which is
**order-independent** (commutativity of `#`). But it is WRONG for `isChainInf`: the cut formula in the
in-place half's antecedent would have to thread to `b`'s succedent at index `lh ds`, which is NOT `< j`.
So `isChainInf` of the end-append splice is generically UNSATISFIABLE — `zKValidF_iSpliceEnd`'s
`isChainInf` hypothesis cannot be met by the genuine halves. The end-append lemma is the ORDINAL-side
packaging, not the validity object.

## Retarget for the splice validity (the corrected (a)+(b))
Build the **ordered insert-at-`i`** object `iSpliceInsert ds i a b := d₀…d_{i−1} a b d_{i+1}…dₗ`
(length `lh ds + 1`), and prove:
1. `isChainInf s r' (iSpliceInsert ds i a b)` from the original `isChainInf s r ds` (distinguished `j₀`)
   + the two halves' genuine end-sequents (`dᵢ{0} ⊢ Γᵢ→A(dᵢ)`, `dᵢ{1} ⊢ A(dᵢ),Γᵢ→Aᵢ`) + `rk(A(dᵢ)) ≤ r'`.
   The new distinguished index is `j₀+1` (shifted); threading: `< i` premises unchanged; `a`(=`dᵢ{0}`) at
   `i` keeps `Γᵢ`'s threading, succedent now `A(dᵢ)`; `b`(=`dᵢ{1}`) at `i+1` threads `A(dᵢ)→i`, rest of `Γᵢ`
   as before; `> i` premises shift `+1`, threading to earlier succedents preserved by the shift.
2. `zKValidF` via the same per-half well-formedness packaging (reuse the `forall`-over-premises pattern).
3. **Descent transfer**: `õ(iSpliceInsert ds i a b) = õ(seqCons (seqUpdate ds i a) b)` (same `#`-multiset,
   `#` comm/assoc — `iseqNaddIdg` is permutation-invariant), so the banked `iord_descent_iSpliceEnd`
   descent carries over to the validity object. (Prove the `iseqNaddIdg` equality, or a direct
   `iord_descent` on the insert object mirroring `iotil_iSpliceEnd_lt`.)

Mechanics needed: a `seqInsert` coded-sequence op (insert one element, shift the tail) via
`PR.Construction` — mirror `seqUpdateAux` (≈100 lines incl. read-outs + `Seq`/`lh`/`znth` lemmas +
`𝚺₁`-definability). Then the three lemmas above. This is the genuine 5.2.1 validity object; the lap-87
end-append reductions remain as the ordinal-side interface and as the `forall`-premise template.

## Status
Build green 1325 jobs. Headline still honest `sorry` (0 math axioms). This finding corrects the lap-86
plan's implicit assumption that the banked end-append splice model serves BOTH descent and validity —
it serves only descent; validity needs the ordered insert object.
