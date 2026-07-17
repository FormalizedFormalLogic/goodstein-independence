# How this came to be

No grand plan:

1. I watched a YouTube video about Goodstein's theorem. Neat.
2. "Let's formalize it." Mathlib's 1000-theorems list wanted it, so someone was
   even asking.
3. "Wait, PA isn't strong enough to prove this? That's weird."
4. So formalize *that* too. The independence became the point, and the Goodstein
   process became the setup.
5. Having finished it, I am only very slightly wiser about *why* PA cannot prove
   Goodstein.

Step 5 is the honest one. Formalization gets sold as a route to understanding, and
I can't claim much of that here. What is here instead is an artifact you do not have
to take my word for: the axiom ledger (in the [README](../README.md#status)) is
machine-checked, and so is the bridge that keeps the statement from being vacuous.

The work was AI-assisted, with Claude (via Claude Code) driving a Lean build loop
against a hand-written [blueprint](../README.md#blueprint--docs). The axiom ledger and
the faithfulness anchor exist precisely because of that: they are the checks that let a
reader trust the result without trusting the process that produced it.
