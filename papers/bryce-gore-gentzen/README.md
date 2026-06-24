# Bryce–Goré: Coq formalization of Gentzen's `Con(PA)` — provenance pointer

**Not vendored here** (the upstream repo has **no LICENSE file**, so its Coq source is not redistributed
into this Apache-licensed repo). The full source is cloned locally and is **box-readable directly**:

- **Local clone:** `~/src/Gentzen` (commit `f34542a`, 2023-09-01, 18,074 lines Coq)
- **Upstream:** https://github.com/aarondroidbryce/Gentzen
- **Paper:** Aaron Bryce & Rajeev Goré, *"A Formally Verified Constructive Proof of the Consistency of Peano
  Arithmetic Using Ordinal Assignments"*, arXiv:2603.00487 (Feb-2026 draft) — https://arxiv.org/html/2603.00487
- **Ordinal library:** Pierre Castéran & Evelyne Contejean's Cantor/ε₀ Coq development (under
  `theories/Casteran/`).
- **Predecessor:** Morgan Sinclaire, "Formally Verifying Peano Arithmetic" (Boise State thesis).

**Why it matters here:** worked precedent for the **C0.5 Foundation→Z bridge**. See the full analysis in
`ON-LINE-FINDINGS-2026-06-24-bryce-gore-gentzen.md` (repo root) — three-layer PA→PA_ω bridge blueprint,
the per-rule ordinal arithmetic to cross-check `iord`/`iR`, the main theorem `PA_Consistent`, and the
finitary-Z-vs-infinitary-PA_ω route caveat.

Key file map (paths into `~/src/Gentzen/theories/`):
| File | What |
|---|---|
| `gentzen.v` | main theorem `PA_Consistent` (`:290`) + the `danger`/cut-free consistency closure |
| `Logic/Peano.v` | the bridge: `Peano_Theorems_Base` (`:21`) → `…_Implication` (`:67`) → `PA_closed_PA_omega` (`:489`) |
| `Logic/PA_omega.v` | the infinitary system `PA_omega_theorem` (`:24`); ω-rule `w_rule1/2` (`:100`) |
| `Logic/proof_trees.v` | `ptree` (`:13`), `ptree_ord` (`:160`), `ptree_deg` (`:115`), `valid` (`:205`) |
| `Logic/cut_elim.v` | reduction `R` = `cut_elimination` (`:231`); top `cut_elim` (`:1198`) |
| `Maths/ordinals.v` | the ε₀ CNF `ord` type (`:12`), `nf` (`:163`), `ord_2_exp` (`:524`) |
| `Casteran/` | Castéran–Contejean RPO ordinal library (well-foundedness engine) |
