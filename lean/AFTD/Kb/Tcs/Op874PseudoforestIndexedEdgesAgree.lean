import AFTD.Prelude
import AFTD.Kb.Tcs.Op874pfEdges
import AFTD.Kb.Tcs.Op874pfColor
import AFTD.Kb.Tcs.Op874pftEnds
import AFTD.Kb.Tcs.Op874pftColor

/-!
# op874_pseudoforest_indexed_edges_agree

Topic: graphs   Node: 58857cbbf730

Provenance: helper lemma. OP-874: coherence of the fixed-color obstruction representations.

The indexed edge list enumerates the explicit graph edges exactly once and agrees with the fixed external edge coloring.
-/

theorem op874_pseudoforest_indexed_edges_agree :
    Function.Injective op874pft_ends ∧
    (∀ e : Fin 12, op874pft_ends e ∈ op874pf_edges ∧
      op874pf_color (op874pft_ends e) = op874pft_color e) ∧
    (∀ e ∈ op874pf_edges, ∃ i : Fin 12, op874pft_ends i = e) := by decide
