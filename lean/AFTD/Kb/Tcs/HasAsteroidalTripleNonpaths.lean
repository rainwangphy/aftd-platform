import AFTD.Prelude
import AFTD.Kb.Tcs.IsPathGraph
import AFTD.Kb.Tcs.ClosedNeighborSet

/-!
# has_asteroidal_triple_nonpaths

Topic: graphs   Node: d7dbc93d17d3

Provenance: formalization of a published result. Source: arXiv:2611.09627:403

A graph H contains an asteroidal triple of nonpaths if there exist three pairwise disjoint, pairwise antiadjacent subsets of vertices, each inducing a connected subgraph that is not a path graph, such that for every pair there is a path connecting them that avoids the closed neighborhood of the third.
-/

/-- A graph H has an asteroidal triple of nonpaths if it contains three pairwise disjoint, pairwise antiadjacent connected vertex sets, none of which induces a path graph, such that any two can be joined by a walk in H avoiding the closed neighborhood of the third. -/
def has_asteroidal_triple_nonpaths {V : Type*} (H : SimpleGraph V) : Prop := ∃ (A₁ A₂ A₃ : Set V),
    Disjoint A₁ A₂ ∧ Disjoint A₁ A₃ ∧ Disjoint A₂ A₃ ∧
    (∀ u ∈ A₁, ∀ v ∈ A₂, ¬ H.Adj u v) ∧
    (∀ u ∈ A₁, ∀ v ∈ A₃, ¬ H.Adj u v) ∧
    (∀ u ∈ A₂, ∀ v ∈ A₃, ¬ H.Adj u v) ∧
    (H.induce A₁).Connected ∧ ¬ is_path_graph (H.induce A₁) ∧
    (H.induce A₂).Connected ∧ ¬ is_path_graph (H.induce A₂) ∧
    (H.induce A₃).Connected ∧ ¬ is_path_graph (H.induce A₃) ∧
    (∃ u ∈ A₁, ∃ v ∈ A₂, ∃ p : H.Walk u v, ∀ x ∈ p.support, x ∉ closed_neighbor_set H A₃) ∧
    (∃ u ∈ A₁, ∃ v ∈ A₃, ∃ p : H.Walk u v, ∀ x ∈ p.support, x ∉ closed_neighbor_set H A₂) ∧
    (∃ u ∈ A₂, ∃ v ∈ A₃, ∃ p : H.Walk u v, ∀ x ∈ p.support, x ∉ closed_neighbor_set H A₁)
