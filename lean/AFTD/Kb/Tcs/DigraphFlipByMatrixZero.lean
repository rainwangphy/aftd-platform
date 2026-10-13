import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphFlipByMatrix

/-!
# digraph_flip_by_matrix_zero

Topic: graphs   Node: 90532789c1ed

Provenance: helper lemma. Sanity lemma for digraph_flip_by_matrix (arXiv:2610.13798, Sec. 2.2).

Flipping by the zero matrix changes nothing.
-/

theorem digraph_flip_by_matrix_zero {V : Type*} (D : Digraph V) :
    digraph_flip_by_matrix D 0 = D := by
  ext x y
  simp [digraph_flip_by_matrix]
