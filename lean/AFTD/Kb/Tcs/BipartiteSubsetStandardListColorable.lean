import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetGraph

/-!
# bipartite_subset_standard_list_colorable

Topic: graphs   Node: d9bb4d26a8de

Provenance: formalization of a published result. Source: arXiv:2610.42094, Section 1.3

For integers k and r, bipartite_subset_standard_list_colorable k r asserts that the bipartite subset graph bipartite_subset_graph k r admits a proper coloring c from the standard lists where each vertex Sum.inl S receives a color in S.1 and each vertex Sum.inr T receives a color in T.1, with colors in Fin (2 * k - 1).
-/

/-- Whether G(k,r) has a proper list coloring where L(a_S) = S and L(b_T) = T. -/
def bipartite_subset_standard_list_colorable (k r : ℕ) : Prop := ∃ c : (bipartite_subset_graph k r).Coloring (Fin (2 * k - 1)),
    ∀ v, c v ∈ Sum.elim Subtype.val Subtype.val v
