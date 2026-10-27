import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDominatingSets
import AFTD.Kb.Tcs.DominatingPartitionFunction

/-!
# dominating_occupancy

Topic: graphs   Node: 9c9ea3a39802

Provenance: formalization of a published result. Source: arXiv:2208.10475v2; OP-542

The normalized lambda-biased dominating occupancy rho_G(lam) of a finite simple graph G on vertex set V is the sum over all dominating sets S of |S| * lam^{|S|} divided by |V| * Z_G(lam).
-/

open Classical in
/-- The normalized lambda-biased dominating occupancy rho_G(lam) of a finite simple graph G. -/
noncomputable def dominating_occupancy {V : Type*} [Fintype V]
    (G : SimpleGraph V) (lam : ℝ) : ℝ := (∑ S ∈ simple_graph_dominating_sets G, (S.card : ℝ) * lam ^ S.card) /
    ((Fintype.card V : ℝ) * dominating_partition_function G lam)
