import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphIsValid
import AFTD.Kb.Tcs.MixedGraphIsRegular
import AFTD.Kb.Tcs.MixedGraphHasCycle
import AFTD.Kb.Tcs.MixedGraphHasGirth
import AFTD.Kb.Tcs.MixedCageOrder
import AFTD.Kb.Tcs.CirculantMixedGraphValidAndRegular
import AFTD.Kb.Tcs.CirculantMixedGraphCycleGExists
import AFTD.Kb.Tcs.CirculantMixedGraphNoCycleLtG

/-!
# mixed_cage_order_one_le

Topic: graphs   Node: e9a17ac62513

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Theorem 4.2 (with Definition 4.1).

For z ≥ 1 and g ≥ 3, n(1, z, g) ≤ N(z, g), where N(z, g) = z(g − 1) + 2 for even z and (z + 1)(g − 1) for odd z: the circulant M(z, g) on 2m = N(z, g) vertices with arcs of jumps 1..⌈z/2⌉ and m+1..m+⌊z/2⌋ and the antipodal edges is a (1, z, g)-mixed graph.
-/

theorem mixed_cage_order_one_le (z g : ℕ) (hz : 1 ≤ z) (hg : 3 ≤ g) :
    mixed_cage_order 1 z g ≤ if Even z then z * (g - 1) + 2 else (z + 1) * (g - 1) := by
  unfold mixed_cage_order
  apply Nat.sInf_le
  have h1 := circulant_mixed_graph_valid_and_regular z g hz hg
  have h2 := circulant_mixed_graph_cycle_g_exists z g hz hg
  have h3 := circulant_mixed_graph_no_cycle_lt_g z g hz hg
  dsimp only at h1 h2 h3
  exact ⟨_, _, h1.1, h1.2, h2, h3⟩
