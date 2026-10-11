import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphNoLeafOfPowerWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered

/-!
# diam_le_one_of_forall_power_well_covered_of_degree_eq_one

Topic: graphs   Node: 2ddc65a6498c

Provenance: helper lemma. Partial result on OP-160 (arXiv:2610.09300 (On graphs whose powers are well-covered), Question 3.9); a direct consequence of the paper's Corollary 2.6 (simple_graph_no_leaf_of_power_well_covered).

If a finite connected graph G has a vertex of degree 1 and G^d is well-covered for every d ≥ 1, then diam(G) ≤ 1 (G is K_2). In particular OP-160's diameter bound holds, with room to spare, for graphs with a leaf, e.g. trees.
-/

theorem diam_le_one_of_forall_power_well_covered_of_degree_eq_one {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hwc : ∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d)) (v : V)
    (hleaf : G.degree v = 1) : G.diam ≤ 1 := by
  by_contra h
  rw [not_le] at h
  exact simple_graph_no_leaf_of_power_well_covered G hconn (by omega) (hwc _ (by omega)) v hleaf
