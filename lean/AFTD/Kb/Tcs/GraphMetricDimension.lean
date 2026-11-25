import AFTD.Prelude
import AFTD.Kb.Tcs.IsResolvingSet

/-!
# graph_metric_dimension

Topic: graphs   Node: 922ebc6df58e

Provenance: formalization of a published result. Source: arXiv:2611.29819 Definition 1.1

The metric dimension of a simple graph G is the minimum cardinality of a finite resolving set of vertices in G.
-/

/-- The metric dimension of a simple graph G is the minimum cardinality of a finite resolving set of G. -/
noncomputable def graph_metric_dimension {V : Type*} (G : SimpleGraph V) : ℕ := sInf { n : ℕ | ∃ S : Finset V, is_resolving_set G (S : Set V) ∧ S.card = n }
