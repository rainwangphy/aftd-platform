import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsMutualVisibilityColorable

/-!
# graph_mutual_visibility_chromatic_number

Topic: graphs   Node: 3a69622ff56b

Provenance: formalization of a published result. Source: arXiv:2610.39430, Definition 1.1

The mutual-visibility chromatic number of a simple graph G is the infimum in ℕ∞ of the natural numbers n such that G is mutual-visibility n-colorable.
-/

/-- The mutual-visibility chromatic number χ_μ(G) is the minimum number of mutual-visibility sets partitioning V(G). -/
noncomputable def graph_mutual_visibility_chromatic_number {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨅ n ∈ {n : ℕ | graph_is_mutual_visibility_colorable G n}, (n : ℕ∞)
