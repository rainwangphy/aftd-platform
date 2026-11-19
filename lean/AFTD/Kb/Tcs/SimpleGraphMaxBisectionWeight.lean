import AFTD.Prelude
import AFTD.Kb.Tcs.IsGraphBisection
import AFTD.Kb.Tcs.SimpleGraphCutWeight

/-!
# simple_graph_max_bisection_weight

Topic: graphs   Node: 42419b50b91a

Provenance: formalization of a published result. Source: arXiv:2611.22760, Section 1

For a finite simple graph G with edge weights w : G.edgeSet → ℝ, the maximum bisection weight bis_w(G) is the supremum of simple_graph_cut_weight G w S over all bisections S.
-/

/-- The maximum weight bis_w(G) of a bisection of G under edge weights w. -/
noncomputable def simple_graph_max_bisection_weight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : G.edgeSet → ℝ) : ℝ := ⨆ (S : Finset V) (_ : is_graph_bisection S), simple_graph_cut_weight G w S
