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
import GoodsteinPA.ONoteComp
import GoodsteinPA.SeamDefinability

import GoodsteinPA.Thm56
import GoodsteinPA.EmbeddingBound

-- E-core (the Goodstein⟹TI descent, Rathjen §2–3): proof-translation lift + semantic backbone
-- + the arithmetization induction scaffold. Not yet wired into the headline (E = `DescentE` is
-- still a `Prop`), but kept in the build so the §3 bricks stay green.
import GoodsteinPA.DescentLift
import GoodsteinPA.DescentCore
import GoodsteinPA.Grzegorczyk
import GoodsteinPA.DescentArith
import GoodsteinPA.InternalPow
import GoodsteinPA.InternalDigits
import GoodsteinPA.InternalLog
import GoodsteinPA.InternalBump
import GoodsteinPA.InternalONote
import GoodsteinPA.InternalCor34
import GoodsteinPA.InternalGoodstein
import GoodsteinPA.DescentSlowdown
import GoodsteinPA.InternalBridge
import GoodsteinPA.DescentInternal

-- E via first-order completeness (lap-30 redirect): `DescentE` reduced to ONE semantic obligation
-- (`paLX_models_TI_of_PA_provable`). Modulo that disclosed `sorry`, the headline chains; NOT wired
-- into `Statement.lean` (anti-fraud). See `DescentSemantic.lean` docstring + `DESCENT-PLAN.md §5`.
import GoodsteinPA.DescentSemantic
import GoodsteinPA.DescentConstruction
import GoodsteinPA.ReductModel
import GoodsteinPA.XCongruence
