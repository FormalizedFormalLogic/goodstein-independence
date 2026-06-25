# Judge directive — M1b de-risk: attack the crux FIRST (2026-06-25)

> Steering for the redSoundF grind. Supersedes the lap-96 handoff's "▶ NEXT" *ordering* (not its
> content). The lap-96 plan lists the 5 validity leaves in dispatch order (Ind → replace → splice →
> crit). That order is **backwards for de-risking** — fix it.

## The order to work M1b
**Attack `ZDerivation_red_zK_crit` (Buchholz Def 3.2 case 5.1, the cut-rank degree-drop) FIRST**, as a
standalone fail-fast spike — before Ind, before the replace branches, before splice.

### Why (this is the whole point)
Of the 5 open validity leaves, **5.1 is the only one whose feasibility is in genuine doubt.** It is the
genuinely-new content: internalizing Buchholz Thm 3.4's degree-drop (`red(d) = K^{r-1} d{0} d{1}`,
cut-rank `r → r-1`) over coded derivations in IΣ₁. The others are plumbing or near-done:
`ZDerivation_red_zK_replace` is already PROVED (modulo the conclusion-tracking IH); Ind
(`zKValidF_iIndReduct_of_zInd`) is count-tracking; splice (5.2.1) is gated to critical-chain premises
where the halves are genuine.

**The easy leaves have no standalone value.** If 5.1 doesn't internalize, `redSoundF` is dead, the
headline dies, and every Ind/replace/splice leaf you closed was wasted motion. So there is no use ever
doing them until 5.1's feasibility is settled. Front-loading 5.1 means you learn the answer at lap ~10,
not lap ~40 — and the pre-agreed overrun pivot (`E-ROUTE-OPTIONS-2026-06-24.md`, fires if M1 passes
~40 laps without `redSoundF`) then triggers with maximum runway left instead of as a cliff.

⚠️ Do NOT let "11 src sorries" or a desire for a green lap pull you into closing the easy leaves first.
Closing 4 of 5 while 5.1 sits untouched is the failure mode, not progress (charter: hardest-first).

## Before grinding 5.1 — two cheap de-risks
1. **Faithfulness pin (do once).** Confirm the validity invariant `zKValidF` / `redConcl` faithfully is
   Buchholz Thm 3.4(b) / Thm 6.2 ("principal sequent ⊆ Γ, cut-rank strictly drops") — read against the
   PDF in `papers/`, NOT transcribed from docstrings. Guards against proving `redSoundF` against a wrong
   invariant (a green, axiom-clean, *unfaithful* cut-elim — the kernel can't catch that).
2. **Mine the precedent.** Bryce-Goré (`scratchpad/Gentzen-bg/`, arXiv:2603.00487) machine-checked the
   analogous reduct+validity in Coq. Read their cut-elim section + `cut_elim.v` structure: did THEY flag
   validity-preservation as the hard part, or treat it as routine? If they needed a lemma our 5-leaf
   decomposition lacks, that's the hidden risk — surface it from their proof, early.

## High-payoff long-shot (worth 1-2 laps, ~15% it pays)
Characterize which `(chain, selected-premise-tag)` combinations are actually **reachable** by
`red`-iteration from a `ZDerivesEmpty` (∅→⊥) witness. Current judge read: the non-Rep `_crit`/`_splice`
cases ARE reachable (~85%) — `red`'s table recursion descends into non-⊙ sub-derivations whose selected
premises can be non-Rep. BUT if a reachability lemma shows the reachable set is Rep-only at every level,
`redSoundF` can be replaced by a Rep-restricted invariant that **skips the hardest leaves entirely**.
Either it deletes the wall (~15%, huge) or it kills the doubt and confirms the general motive is
necessary. Cheap to check, asymmetric payoff.

## What the literature already settles (don't re-litigate)
"Can IΣ₁ internalize this validity argument?" is YES — `PRWO(ε₀) → Con(PA)` being PA-provable is the
classical Gentzen / ordinal-analysis result; crux-2 IS that, formalized. So **existence is not the
risk** — only the Lean-engineering cost is open (threading Thm 3.4 through the Σ₁/Fixpoint/coded
recursion). Don't burn laps re-checking whether it's possible in principle; it is.
