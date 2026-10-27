import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDominatingSets

/-!
# dominating_partition_function

Topic: graphs   Node: 3963c753c075

Provenance: formalization of a published result. Source: arXiv:2208.10475v2; OP-542

The dominating set partition function Z_G(lam) of a finite simple graph G is the sum over all dominating sets S of G of lam^{|S|}.
-/

open Classical in
/-- The dominating set partition function Z_G(lam) of a finite simple graph G. -/
noncomputable def dominating_partition_function {V : Type*} [Fintype V]
    (G : SimpleGraph V) (lam : ℝ) : ℝ := ∑ S ∈ simple_graph_dominating_sets G, lam ^ S.card
