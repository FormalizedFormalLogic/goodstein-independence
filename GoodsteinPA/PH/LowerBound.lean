/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

module

public import GoodsteinPA.PH.LB.Escape

@[expose] public section

/-!
# The Paris–Harrington lower bound (Buchholz Thm 7.5, after Loebl–Nešetřil)

Section numbers (§2.x, HS1, …) refer to Buchholz, *Beweistheorie* 1997/98, printed pp. 46–49.

Conventions, which differ from Buchholz on purpose:
* Mathlib's `ONote.fundamentalSequence` coincides with Buchholz's `α[n]` (`ω^{a+1}[i] = ω^a·(i+1)`,
  `ω^λ[i] = ω^{λ[i]}`, last-term rule), so the descent and the colouring transfer unchanged.
* CNF term indices are **0-based** here (Buchholz: `1..t`).  `dIdx` is the first differing index;
  Lemma 7.8a's count becomes `ℓ ≤ dIdx + 1 ≤ tlen ≤ rnorm`.
* The repo's `hardy` has **no `+1` at limits** (Buchholz's `H` does).  So HS2 becomes an inequality,
  `hardy (wtow m k) (k+1) + m + 1 ≤ descLen m k`, proved like stage 2's P2
  (`HydraLowerBound.runFrom_alive_of_lt_hardy`: successor = `hardy_succ`, limit = `hardy_limit` +
  `hardy_le_succ`).
* Our `PH` colours subsets of `{1,…,N}`; Buchholz's `[N]` is `{0,…,N−1}`.  The bad colouring reads
  element `j` as descent index `j − 1`.  Shifting only raises `min`, so the bound survives.
-/

end
