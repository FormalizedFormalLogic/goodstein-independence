# E — Judge: `zAxBot` IS Buchholz's endform/Ax0 false-left case (Ren + Codex, 2026-06-27, ~lap 162)

> **VALIDATE, don't trust.** Codex (parallel reviewer) found the Buchholz source provision; I independently
> read the same transcript lines + the Lean rule and resolved the open/closed nuance Codex flagged. Convergent,
> but I verified the source myself (the baton warns our agreement isn't independent — so I checked the artifact).

## Verdict: faithful (a CORRECTION, not a patch) — ~85%
The `zAxBot` (tag-8 ⊥-left leaf) is NOT an invented convenience rule. It is the Lean realization of Buchholz's
**Ax0 / endform** axiom for the false-antecedent case. Source-verified in `scratchpad/buchholz-gentzen.txt`:
- **:555** — `Γ→C has endform :⇔ C ≈ ⊤ or Γ contains a false minimal formula`. `⊥` is a false minimal formula
  ⟹ `⊥ ∈ Γ` puts `Γ→C` in endform for ANY `C`. Exactly the ex-falso case.
- **:834-836** — `Ax(Z)` (mathematical axioms) closure: (i) `Π∈Ax(Z) ⇒ Π(a/t)∈Ax(Z) and A,Π∈Ax(Z)` (substitution
  + antecedent-weakening); (ii) `FV(Π)=∅ ⇒ (Π∈Ax(Z) ⇔ Π has endform)`.
- **:840** — `If Π∈Ax(Z), then Ax0Π ⊢ Π`. So `Ax0` is the constructor; `zAxBot` is its tag-8 Lean form.

The Lean rule (`InternalZ.lean:5498`, ZPhi clause): `d = zAxBot s ∧ inAnt (^⊥) (seqAnt s)`. Constructor at
`:664` (`⟪s,8,0⟫+1`), `iotil = idg = iord = 0` (`:2777/2775/2781`) — a genuine terminal leaf, descends below any
nonempty chain. The design has landed in ZPhi + intro/inversion (`InternalZ:9113-ish`); the Crux2Blueprint
consumer wrapper (`zDerivation_zAxBot`) is the one residual sorry — in-flight, not yet closed.

## The open/closed seam (Codex's caveat 2), resolved
Buchholz's endform⟺Ax(Z) IFF (:836) is stated **only for closed sequents** (`FV(Π)=∅`); open endform sequents
reach Ax(Z) via the closure conditions (:835, substitution + weakening). The Lean `zAxBot` carries **no
`FV(s)=∅` guard** — it fires on any `⊥∈seqAnt s`, open or closed. So it matches the endform *condition* (:555)
directly rather than the closed-IFF construction. **This is sound and almost certainly intended:**
- **Sound** regardless of closedness: an open `Γ→C` denotes its universal closure; `⊥∈Γ` makes `⋀Γ` false for
  all valuations ⟹ `Γ→C` valid vacuously. Ex falso holds open or closed.
- **Intended**: Buchholz's closure conditions (:835) exist precisely to propagate endform-axiomhood across
  substitution + weakening; admitting the open `⊥∈Γ` sequent directly is the same set in spirit. The closed-only
  IFF is a characterization technicality, not a restriction that excludes open false-left sequents.

**Honest label**: `zAxBot` = Buchholz Ax0 for the false-left endform case, applied to open sequents directly
(sound; Buchholz reaches the same via Ax(Z) closure). NOT "Buchholz Z + an invented rule." The one obligation it
adds: **M2 (Foundation/PA → Z) must produce/admit `zAxBot` for PA's ex-falso** — a real but ordinary bridge case.

## Action (Codex caveat 1: audit NOW) — essentially DONE, one doc nit
The source audit is complete and favorable. The only follow-through: drop a one-line provenance comment next to
`zAxBot`/the ZPhi clause ("= Buchholz Ax0 endform false-left, :555/:834; open-sequent form sound, M2 must admit")
so the design intent is pinned before more lemmas stack on it. No need to block grinding on it.

## Numbers
`zAxBot` faithful: **~85%** (source provision verified; residual 15% = the open-sequent directness being a design
choice M2 must honor, + the still-sorried `zDerivation_zAxBot` wrapper). Overall campaign **~55-60% unchanged** —
the M2 bridge surface grew by exactly one constructor. The standing yellow flag (encoding surface grows faster
than M2 validates it) holds, but this specific edit is plugging an omitted source axiom case, not cheating.

## How this could be wrong
- I read endform (:555) + Ax(Z) (:834) but not Buchholz's full §5 atomic-derivation treatment — if §5 imposes a
  closedness or rank side-condition on the false-left Ax0 that `zAxBot` omits, the "directly on open sequents"
  call weakens from "intended" to "admissible extension M2 must simulate." Worth a 10-min §5 read before M2.
- Convergence caveat: Codex and I now both read the source, but the same transcript — if the transcript is an
  abridged/edited Buchholz, a provision in the full paper could refine this. Low risk; the endform definition is
  unambiguous as written.
