import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDominating

/-!
# simple_graph_domination_number

Topic: graphs   Node: 1af400f4fc94

Provenance: formalization of a published result. Source: arXiv:2610.28936 Definition 2.1

The domination number gamma(G) of a finite simple graph G is the minimum cardinality of a dominating set of G.
-/

/-- The domination number of a finite simple graph. -/
noncomputable def simple_graph_domination_number {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := sInf {k : ℕ | ∃ S : Finset V, simple_graph_is_dominating G (S : Set V) ∧ S.card = k}
