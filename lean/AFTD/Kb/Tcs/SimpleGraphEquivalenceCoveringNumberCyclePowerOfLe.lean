import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberTop

/-!
# simple_graph_equivalence_covering_number_cycle_power_of_le

Topic: combinatorics   Node: ac2cea5cb036

Provenance: formalization of a published result. Source: arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs), Theorem 1.2 (the case n ≤ 2k + 1; the Lean adds n ≥ 2 so that the graph has an edge).

If 2 ≤ n ≤ 2k + 1 then every two vertices of C_n are at cyclic distance at most k, so C_n^k = K_n and eq(C_n^k) = 1.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_of_le (n k : ℕ) (hn : 2 ≤ n)
    (hnk : n ≤ 2 * k + 1) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) = 1 := by
  have h_top : simple_graph_cycle_power n k = ⊤ := by
    have : NeZero n := ⟨by omega⟩
    ext u v
    simp only [simple_graph_cycle_power, SimpleGraph.top_adj]
    constructor
    · rintro ⟨huv, -⟩
      exact huv
    · intro huv
      refine ⟨huv, ?_⟩
      have : NeZero (u - v) := ⟨fun h => huv (sub_eq_zero.mp h)⟩
      rw [← neg_sub u v, ZMod.val_neg_of_ne_zero (u - v)]
      have hlt := ZMod.val_lt (u - v)
      omega
  rw [h_top]
  have : Fact (1 < n) := ⟨by omega⟩
  have : Nontrivial (ZMod n) := ZMod.nontrivial n
  exact simple_graph_equivalence_covering_number_top
