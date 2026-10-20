import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPathGraphWalkLengthGe

/-!
# simple_graph_path_graph_dist_ge

Topic: graphs   Node: 1fb814afc441

Provenance: helper lemma. for simple_graph_path_radio_labeling_four_mul_add_three (RT-4, OP-384)

In the path graph P_n the distance between u and v is at least |u - v|.
-/

theorem simple_graph_path_graph_dist_ge {n : ℕ} (u v : Fin n) :
    |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| ≤ (SimpleGraph.pathGraph n).dist u v := by
  obtain ⟨p, hp⟩ := (SimpleGraph.pathGraph_preconnected n u v).exists_walk_length_eq_dist
  rw [← hp]
  exact simple_graph_path_graph_walk_length_ge p
