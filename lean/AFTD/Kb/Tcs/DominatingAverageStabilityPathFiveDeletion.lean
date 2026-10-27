import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarLikeDeletionNumber
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDecidable
import AFTD.Kb.Tcs.DominatingAverageStabilityPathFiveDeleteEndpoint

/-!
# dominating_average_stability_path_five_deletion

Topic: graphs   Node: 6ad6b96d96b4

Provenance: helper lemma. Finite sharpness certificate for the original OP-544 / IN-263 stability question. arXiv:2208.10475v2 Theorem2.9 supplies the extremal background. This formalizes the already computationally observed P5 obstruction to a smaller coefficient, not a proof of the universal bound or a research advance.

The minimum star-like vertex deletion distance of the five-vertex path is exactly1.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem dominating_average_stability_path_five_deletion :
    letI := dominating_average_stability_path_five_decidable
    simple_graph_star_like_deletion_number (SimpleGraph.pathGraph 5) = 1 := by
  letI := dominating_average_stability_path_five_decidable
  change simple_graph_star_like_deletion_number (SimpleGraph.pathGraph 5) = 1
  unfold simple_graph_star_like_deletion_number
  have hmem : 1 ∈ {k : ℕ | ∃ X : Finset (Fin 5),
      simple_graph_is_star_like ((SimpleGraph.pathGraph 5).induce (Xᶜ : Set (Fin 5))) ∧
      X.card = k} :=
    ⟨{0}, dominating_average_stability_path_five_delete_endpoint, by simp⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨1,hmem⟩
  rintro k ⟨X,hX,rfl⟩
  by_contra hbad
  have hxzero : X.card = 0 := by omega
  have hx : X = ∅ := Finset.card_eq_zero.mp hxzero
  subst X
  have hempty : ¬ simple_graph_is_star_like
      ((SimpleGraph.pathGraph 5).induce ((∅ : Finset (Fin 5))ᶜ : Set (Fin 5))) := by
    unfold simple_graph_is_star_like simple_graph_leaf_neighbor_count
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    decide +kernel
  exact hempty hX
