# Codex Wind-Down - 2026-06-24 16:00 EDT

This note is for reboot/session recovery. It does not replace `HANDOFF.md`; read that first.

## Current Repo State

- Branch: `plan`
- Actual HEAD at wind-down: `986400a docs(lap 74): HANDOFF - reflection + gap-(B) closed + fvSubst_substs1; next = ZDerivation_zsubst`
- Worktree: clean at wind-down.
- Latest project handoff: `HANDOFF.md` / `HANDOFF-2026-06-24-lap74.md`
- Latest reflection: `REFLECTION-2026-06-24-lap74.md`
- Build status was reported in the lap-74 handoff as green, `lake build GoodsteinPA` = 1323 jobs. I did not rerun the build during this wind-down note.

## Operator Decision

The required endpoint is axiom-free. Do not recommend the one-axiom Gentzen shortcut as the project endpoint.

The operator clarified that an external certified repo can be acceptable as a response to mathlib requests, so the relevant bar is:

- final theorem kernel-checks in this repo,
- no `sorryAx`,
- no project-specific math axioms,
- reproducible build and clear theorem equivalence.

Therefore the viable path is to build the missing proof-theory infrastructure here, not necessarily upstream every component into mathlib first.

## Current Mathematical Shape

The earlier calculus-bridge concern is real but now tracked. Current lap-74 framing says the hard wall is crux 2, localized to `RedSound` in `InternalZ.lean`: internalized finitary Buchholz-Z cut-elimination via the validity-preserving Option-A reduct.

Current ladder:

1. rung 0.5: done.
2. rung 1: `zsubst`; definition done, correctness in progress.
3. rung 2: Ind reduct.
4. rung 3: K/cut reduct.
5. rung 4: `RedSound` tag dispatch.

Deferred after `RedSound`: C0.5 Foundation-to-Z bridge from `not Con(PA)` to a Z empty-sequent derivation. This is explicitly tracked in `PENDING_WORK.md` and the lap-74 reflection.

Second mandatory front: `PA_delta1Definable` remains an upstream/Foundation axiom and must be discharged for a genuinely axiom-free endpoint.

## Next Action

Continue exactly where `HANDOFF.md` says:

1. Finish `ZDerivation_zsubst`.
2. First prove the term helpers:
   - `termFvSubst_numeral`
   - `termFvSubst_qqAdd`
   - closedness for `^&e ^+ numeral 1`
3. Add `IsSemiterm LOR 0 (zIndTerm d)` to `zIndWff`.
4. Prove `ZDerivation_zsubst` with `a,t` fixed outside the induction. Do not use a motive carrying unbounded `forall a t`; it is not Delta-1.
5. Do zK last; likely needs substitution invariance for `tp`, `iperm`, and `isChainInf`.

## Anti-Fraud

Do not discharge `src/GoodsteinPA/Reduction.lean` or `src/GoodsteinPA/Statement.lean` until `#print axioms peano_not_proves_goodstein` is clean.

Do not axiomatize `RedSound`, `PA_delta1Definable`, or the Foundation-to-Z bridge.
