# ON-LINE-REQUEST — literature gaps for the box (offline)

A networked host session fulfils these: commit `ON-LINE-FINDINGS-<date>-<topic>.md`, delete the
answered item here, and remove this file once nothing is left open.

---

## ✅ RESOLVED (lap 5, self-answered via WebSearch egress) — no open asks

The lap-4 request (the rigorous invariant for the bounded cut-free lower bound, Towsner Thm 17.1
`I∀` case) is **resolved**. WebSearch worked server-side this lap, so the literature was reachable:
the correct device is the **Schwichtenberg–Wainer / Arai *disjunctive* boundedness lemma** ("*some*
formula of the sequent is witnessed below `H_α(N)`"), applied **after ∀-inversion** (the universal is
inverted away, not carried/accumulated through the induction). This is now **machine-checked** in
`wip/LowerBoundHardy.lean` (`B.allInv` + `lowerBound_hardy`, axiom-clean). Write-up + references:
`ANALYSIS-2026-06-22-bounding-resolution.md` (SW *Proofs and Computations* Ch.4; Arai arXiv:2003.13207;
Pakhomov, *Unprovability in Mathematics*, arXiv:2109.06258).

**Nothing is currently open.** A host may `git mv` this file's history to `archive/` or delete it;
the box will re-create it if a new literature gap appears. (Optional, non-blocking: a PDF of Arai
arXiv:2003.13207 in `papers/` would let us cross-check the exact bound bookkeeping, but the
architecture above does not depend on it.)
