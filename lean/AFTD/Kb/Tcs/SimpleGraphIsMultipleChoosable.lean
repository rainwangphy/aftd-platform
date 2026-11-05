import AFTD.Prelude

/-!
# simple_graph_is_multiple_choosable

Topic: graphs   Node: 5ffa7c69195a

Provenance: formalization of a published result. Source: arXiv:2611.03151, Section 1; Erdős, Rubin, Taylor (1979)

A simple graph G is (a:b)-choosable if for every assignment L of a-element color lists (from ℕ) to the vertices of G, there exists an (L:b)-coloring: an assignment of a b-element subset φ(v) ⊆ L(v) to each vertex v such that adjacent vertices receive disjoint subsets. (Colors are natural numbers, which loses no generality since the lists are finite.)
-/

/-- A simple graph is (a:b)-choosable if every assignment of a-element color lists admits an (L:b)-coloring. -/
def simple_graph_is_multiple_choosable {V : Type*} (G : SimpleGraph V) (a b : ℕ) : Prop := ∀ L : V → Finset ℕ, (∀ v, (L v).card = a) →
    ∃ φ : V → Finset ℕ, (∀ v, φ v ⊆ L v ∧ (φ v).card = b) ∧
      ∀ {u v}, G.Adj u v → Disjoint (φ u) (φ v)
