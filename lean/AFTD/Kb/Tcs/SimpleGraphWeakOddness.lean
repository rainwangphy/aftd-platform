import AFTD.Prelude
import AFTD.Kb.Tcs.IsEvenFactor

/-!
# simple_graph_weak_oddness

Topic: graphs   Node: 64d01b94093a

Provenance: formalization of a published result. Source: arXiv:2611.32276, Section 1

The weak oddness of a finite simple graph G is the infimum of the number of odd components over all even factors of G.
-/

/-- The weak oddness of a graph is the minimum number of odd components in any even factor. -/
noncomputable def simple_graph_weak_oddness {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := sInf {k : ℕ | ∃ (H : SimpleGraph V), is_even_factor G H ∧ H.oddComponents.ncard = k}
