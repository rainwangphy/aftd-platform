import AFTD.Prelude
import AFTD.Kb.Tcs.GraphCost

/-!
# retained_line_msf_weight

Topic: algorithms   Node: d38b2e691ee3

Provenance: helper lemma. OP-815, proposed here; compares independent edge retention on the line with classical random spanning-tree results.

For a graph on the first n nonnegative integers, the minimum total edge length among its spanning forests, one tree in each connected component.
-/

noncomputable def retained_line_msf_weight {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  sInf {x : ℝ | ∃ F : SimpleGraph (Fin n),
    Maximal (fun H : SimpleGraph (Fin n) => H ≤ G ∧ H.IsAcyclic) F ∧
    x = graph_cost (fun i j => |(i.val : ℝ) - (j.val : ℝ)|) F}
