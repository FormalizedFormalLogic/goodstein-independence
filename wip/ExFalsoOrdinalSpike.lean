/-
# SPIKE (lap 162) — the ⊥-exit ex-falso ORDINAL obstruction: settles route 4 vs route 2.

CONTEXT. `exFalsoClose` (`Crux2Blueprint:3477`) must turn `⊥ ∈ seqAnt s` into a
`GenReductCert (zK s r ds)` for a GENERAL succedent `C = seqSucc s`. The lap-161 handoff mandated
ROUTE 4 (build the reduct as a formula-structure R-intro tower over `C` — `zIall`/`zIneg` bottoming
at a `⊥`-leaf `zAtom`), calling it "pure assembly, infra all present". This spike REFUTES route 4 on
ordinal grounds and CONFIRMS the directive's ROUTE 2 (a new `iotil = 0` ⊥-left leaf `zAxBot`) is
REQUIRED — NOT pure assembly.

THE OBSTRUCTION. `GenReductCert` via `certReplace` demands `iRedDescent v (zK s r ds)`, whose
`otil_lt` field is the STRICT drop `icmp (iotil v) (iotil (zK s r ds)) = 0`, with
`iotil (zK s r ds) = iseqNaddIdg ds` (`iotil_zK`). A degenerate single-leaf ⊥-exit chain has
`iseqNaddIdg ds = ω^0 = 1` (`leaf_chain_iseqNaddIdg`). EVERY R-intro raises `iotil` by `+1`
(`iotil_zIall`/`iotil_zIneg = iadd · (ω^0)`), so even the cheapest route-4 tower `zIneg s p (zAtom s')`
already has `iotil = ω^0 = 1` (`tower_iotil`) — EQUAL to the chain's, so `icmp = 1 ≠ 0`
(`tower_no_drop`): the strict drop FAILS. Route 4 cannot close the degenerate case.

WHY THE INTERFACE CAN'T BE WEAKENED. One might hope to descend at the `iord` level instead
(`iord d = iotower (iotil d) (idg d)` is a height-`idg` tower; a tag-8 leaf has `iord 0`). But the
terminal ex-falso reduct is later SPLICED as a `{3,4}`-producer-premise cert by
`certReplace_of_premise_cert` (`:3317-3318`), which propagates the PARENT's strict `iotil` drop from
the per-premise strict `iotil` drop via the `#`-fold `iseqNaddIdg` (`iotil_iCritAux_lt`). An
`iord`-only (idg-dropping) premise does NOT shrink that fold. So the reduct genuinely needs
`iotil = 0`.

THE FIX (route 2). Only `iotil = 0` strict-drops below `iseqNaddIdg ds ≠ 0` (`icmp_zero_pos`,
exactly the `leafCloseC` move, available unconditionally via `hposlast`). The sole existing
`iotil = 0` constructor is `zAtom`, which derives `Γ→C` only for `C ∈ Γ` (not `⊥ ∈ Γ`). So a NEW
`iotil = 0` ⊥-left leaf `zAxBot` (ZPhi disjunct `⊥∈Γ ⟹ Γ→C`) is REQUIRED; `leaf_reduct_drops` shows
ANY `iotil=0` leaf reduct satisfies `iRedDescent` (the `zAxBot` closing template). GOOD NEWS: the
ordinal dispatchers (`ioNext`/`idgTable`) already default unknown tags to `0`, so a tag-8 `zAxBot`
auto-gets `iotil = idg = iord = 0` with NO dispatcher edits — the cost is the ZPhi disjunct +
blueprint/definability + the destructuring ripple, NOT the ordinal table.

Checked with: `lake env lean wip/ExFalsoOrdinalSpike.lean` (exit 0).
-/
import GoodsteinPA.Crux2Blueprint

namespace GoodsteinPA.InternalZ

open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ISigma1
open GoodsteinPA.InternalONote

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

/-- A degenerate single-leaf chain (`lh = 1`, the lone entry an `iotil=0` leaf) folds to `ω^0 = 1`. -/
lemma leaf_chain_iseqNaddIdg {ds : V} (h1 : lh ds = 1) (hleaf : iotil (znth ds 0) = 0) :
    iseqNaddIdg ds = (ocOadd 0 1 0 : V) := by
  rw [iseqNaddIdg, show lh ds = 0 + 1 from by rw [h1, zero_add], iseqNaddIdgAux_succ,
    iseqNaddIdgAux_zero, hleaf, inadd_zero_left]

/-- The cheapest route-4 ex-falso tower `zIneg s p (zAtom s')` has `iotil = ω^0 = 1`. -/
lemma tower_iotil (s p s' : V) : iotil (zIneg s p (zAtom s')) = (ocOadd 0 1 0 : V) := by
  rw [iotil_zIneg, iotil_zAtom, iadd_zero_left]

/-- **ROUTE 4 REFUTED.** Against a degenerate single-leaf ⊥-exit chain, the route-4 tower's `iotil`
EQUALS `iotil (zK s r ds)`, so the strict drop `iRedDescent.otil_lt` FAILS (`icmp = 1 ≠ 0`). -/
lemma tower_no_drop {s r ds p s' : V} (hds : Seq ds) (h1 : lh ds = 1)
    (hleaf : iotil (znth ds 0) = 0) :
    ¬ iRedDescent (zIneg s p (zAtom s')) (zK s r ds) := by
  intro h
  have heq : icmp (iotil (zIneg s p (zAtom s'))) (iotil (zK s r ds)) = (1 : V) := by
    rw [tower_iotil, iotil_zK s r ds hds, leaf_chain_iseqNaddIdg h1 hleaf, icmp_self _ _ le_rfl]
  rw [h.otil_lt] at heq
  simp at heq

/-- **ROUTE 2 CONFIRMED.** Any `iotil = 0` leaf reduct (the `zAxBot` template; witnessed here by the
existing `iotil=0` leaf `zAtom s''`) strict-drops below ANY chain with `iseqNaddIdg ds ≠ 0` — exactly
the `leafCloseC`/`icmp_zero_pos` move, available unconditionally via `hposlast`. -/
lemma leaf_reduct_drops {s r ds s'' : V} (hds : Seq ds) (hpos : iseqNaddIdg ds ≠ 0) :
    iRedDescent (zAtom s'') (zK s r ds) where
  dg_le := by rw [idg_zAtom]; exact zero_le
  otil_lt := by rw [iotil_zAtom, iotil_zK s r ds hds]; exact icmp_zero_pos hpos
  nf := by rw [iotil_zAtom]; exact isNF_zero

end GoodsteinPA.InternalZ
