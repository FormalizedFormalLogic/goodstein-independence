/-
# GoodsteinPA — Goodstein independence over PA (Kirby–Paris), expedition library

Track 2 of the Goodstein effort: the *syntactic* `𝗣𝗔 ⊬ γ`, built on Foundation's first-order
+ incompleteness apparatus. (Track 1, the mathlib-only growth theory, lives in
`~/src/lean-formalizations`.) See `DIRECTION.md` at the repo root.
-/
import GoodsteinPA.Computability
import GoodsteinPA.Encoding
import GoodsteinPA.Bridge
import GoodsteinPA.Reduction
import GoodsteinPA.Statement
import GoodsteinPA.Zinfty
import GoodsteinPA.ZinftyGen
import GoodsteinPA.LangX
import GoodsteinPA.TruthSem
import GoodsteinPA.XPositive
import GoodsteinPA.Boundedness
import GoodsteinPA.XFreeCutElim
import GoodsteinPA.Hardy

import GoodsteinPA.Domination
import GoodsteinPA.LowerBound
import GoodsteinPA.Embedding

import GoodsteinPA.EmbeddingX
import GoodsteinPA.EpsilonOrder
import GoodsteinPA.Epsilon0Complete
import GoodsteinPA.SeamDefinability

import GoodsteinPA.Thm56
import GoodsteinPA.EmbeddingBound

-- E-core (the Goodstein⟹TI descent, Rathjen §2–3): proof-translation lift + semantic backbone
-- + the arithmetization induction scaffold. Not yet wired into the headline (E = `DescentE` is
-- still a `Prop`), but kept in the build so the §3 bricks stay green.
import GoodsteinPA.DescentLift
import GoodsteinPA.DescentCore
import GoodsteinPA.DescentArith
