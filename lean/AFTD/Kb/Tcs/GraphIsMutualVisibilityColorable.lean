import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsMutualVisibilitySet

/-!
# graph_is_mutual_visibility_colorable

Topic: graphs   Node: 65a244f41f2a

Provenance: formalization of a published result. Source: arXiv:2610.39430, Definition 1.1

A simple graph G is mutual-visibility n-colorable if there exists a coloring of the vertices of G with n colors such that every color class is a mutual-visibility set.
-/

/-- A graph admits a mutual-visibility colouring with n colours if its vertices can be partitioned into n mutual-visibility sets. -/
def graph_is_mutual_visibility_colorable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop := ∃ c : V → Fin n, ∀ i : Fin n, graph_is_mutual_visibility_set G {v | c v = i}
