/-
# `fastGrowingε₀` — the diagonal `f_{ε₀}`

Index domination of `fastGrowing` by the `ε₀`-diagonal `fastGrowingε₀`.
-/
module

public import GoodsteinPA.ToMathlib.FastGrowing.Norm

@[expose] public section

namespace ONote

open ONote Ordinal

/-- `fastGrowingε₀ i = f_{tower i}(i)` — the definitional unfolding, as a named lemma. -/
lemma fastGrowingε₀_eq (i : ℕ) : fastGrowingε₀ i = fastGrowing (tower i) i := rfl

/-- **Index domination (axiom-clean):** once a tower level overtakes `o` (`o < tower n`),
it strictly dominates `o` at the diagonal, `f_o(n) < f_{tower n}(n)` for `n ≥ 2` past `norm o`. -/
theorem fastGrowing_lt_of_lt_tower {o : ONote} (ho : o.NF) (n : ℕ)
    (hn : norm o < n) (h2 : 2 ≤ n) (h : o < tower n) :
    fastGrowing o n < fastGrowing (tower n) n := by
  -- `tower n` is a limit ordinal for `n ≥ 2`: `repr (tower n) = ω^(repr (tower (n-1)))`
  -- with `tower (n-1) > 0`, so `ω^· ` is a limit.
  have hlimit : Order.IsSuccLimit (tower n).repr := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [repr_tower_succ]
    refine isSuccLimit_opow_left isSuccLimit_omega0 ?_
    have hpos : (0 : ONote) < tower j :=
      tower_zero ▸ tower_strictMono (show (0 : ℕ) < j by omega)
    rw [← repr_zero]; exact (lt_def.1 hpos).ne'
  -- Reach the *successor* of `o`, then take one strict successor step.
  have hNF : (osucc o).NF := osucc_NF ho
  have hlt : osucc o < tower n := by
    rw [lt_def, repr_osucc ho, ← Order.succ_eq_add_one]
    exact hlimit.succ_lt (lt_def.1 h)
  have hnorm : norm (osucc o) ≤ n := le_trans norm_osucc_le (by omega)
  have hreach : Reaches n (tower n) (osucc o) :=
    reaches_of_lt (tower n) (tower_NF n) (osucc o) hNF hlt hnorm
  have hle : fastGrowing (osucc o) n ≤ fastGrowing (tower n) n :=
    fastGrowing_le_of_reaches (le_trans one_le_two h2) hreach
  have hstrict : fastGrowing o n < fastGrowing (osucc o) n :=
    fastGrowing_lt_succ_index (fundamentalSequence_osucc ho) h2
  exact lt_of_lt_of_le hstrict hle

/-- **Domination (the headline result):** every fixed level of the fast-growing hierarchy
is eventually strictly dominated by `fastGrowingε₀`. -/
theorem fastGrowing_lt_fastGrowingε₀ (o : ONote) (ho : o.NF) :
    ∃ N, ∀ n ≥ N, fastGrowing o n < fastGrowingε₀ n := by
  obtain ⟨k, hk⟩ := tower_cofinal o ho
  refine ⟨max (max k (norm o + 1)) 2, ?_⟩
  intro n hn
  simp only [ge_iff_le, max_le_iff] at hn
  obtain ⟨⟨hkn, hnormn⟩, h2n⟩ := hn
  have hlt : o < tower n := lt_of_lt_of_le hk (tower_strictMono.monotone hkn)
  rw [fastGrowingε₀_eq]
  exact fastGrowing_lt_of_lt_tower ho n (by omega) h2n hlt

end ONote
