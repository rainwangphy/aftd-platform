import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultipleChoosable

/-!
# simple_graph_is_choosable

Topic: graphs   Node: 9e5cdf5d2507

Provenance: formalization of a published result. Source: arXiv:2611.03151, Section 1; Erdős, Rubin, Taylor (1979)

A simple graph G is k-choosable if it is (k:1)-choosable, i.e., for every assignment of k-element color lists to the vertices, there exists a proper coloring choosing a color from each vertex's list.
-/

/-- A simple graph is k-choosable if it is (k:1)-choosable. -/
def simple_graph_is_choosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop := simple_graph_is_multiple_choosable G k 1
