import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteWellCoveredExistsPerfectMatchingRavindra
import AFTD.Kb.Tcs.BipartiteRavindraMatchingPowerTwoWellCoveredDiamLeTwo
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPowerOne

/-!
# bipartite_all_powers_well_covered_diameter_le_two

Topic: graphs   Node: 85661d12ccff

Provenance: formalization of a published result. Source: arXiv:2610.09300, Theorem 1.3

Every finite connected bipartite simple graph G with at least two vertices whose positive integer powers G^d (for d ≥ 1) are all well-covered has diameter at most 2.
-/

/-- Every connected bipartite graph with at least two vertices whose powers are all well-covered has diameter at most 2. -/
theorem bipartite_all_powers_well_covered_diameter_le_two :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.Connected →
      G.IsBipartite →
      2 ≤ Fintype.card V →
      (∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d)) →
      G.diam ≤ 2 := by
  intro V _ G hconn hbip hcard hpow
  have hwc : simple_graph_is_well_covered G := by
    rw [← simple_graph_power_one G]
    exact hpow 1 le_rfl
  obtain ⟨M, hM, hrav⟩ :=
    bipartite_well_covered_exists_perfect_matching_ravindra G hconn hbip hcard hwc
  exact bipartite_ravindra_matching_power_two_well_covered_diam_le_two G hconn hbip M hM hrav
    (hpow 2 (by norm_num))
