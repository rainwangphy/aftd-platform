import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# is_minimal_k_factor_critical

Topic: graphs   Node: 2dbb0a5be08c

Provenance: formalization of a published result. Source: arXiv:2611.09072, Section 1

A simple graph G is minimal k-factor-critical if G is k-factor-critical and for every edge e of G, the graph G - e is not k-factor-critical.
-/

/-- A simple graph G is minimal k-factor-critical if G is k-factor-critical and deleting any edge yields a graph that is not k-factor-critical. -/
def is_minimal_k_factor_critical {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop := is_k_factor_critical G k ∧ ∀ e ∈ G.edgeSet, ¬ is_k_factor_critical (G.deleteEdges {e}) k
