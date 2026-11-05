import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree
import AFTD.Kb.Tcs.InstPartialOrderColoredRootedTree

/-!
# nearest_ancestor_of_color

Topic: data_structures   Node: 34d729a17274

Provenance: formalization of a published result. Source: arXiv:2611.03620 Section 2

Vertex u is the nearest proper ancestor of vertex v having color c if u is an ancestor of v with color c and no intermediate ancestor between u and v has color c.
-/

/-- Nearest proper ancestor of color c. -/
def nearest_ancestor_of_color (T : ColoredRootedTree) (v : T.V) (c : Fin 4) (u : T.V) : Prop := u < v ∧ T.color u = c ∧ ∀ w : T.V, u < w → w < v → T.color w ≠ c
