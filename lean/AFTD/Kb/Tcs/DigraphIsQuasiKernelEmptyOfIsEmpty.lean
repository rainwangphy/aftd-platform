import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsQuasiKernel
import AFTD.Kb.Tcs.DigraphReverseReverse

/-!
# digraph_is_quasi_kernel_empty_of_isEmpty

Topic: graphs   Node: a392b0e8867a

Provenance: helper lemma. step towards digraph_small_quasi_kernel_exists

In an empty digraph, the empty set is a quasi-kernel.
-/

/-- The empty set of vertices is a quasi-kernel in any empty digraph. -/
theorem digraph_is_quasi_kernel_empty_of_isEmpty {α : Type*} [IsEmpty α] (D : Digraph α) :
    digraph_is_quasi_kernel D ∅ := by first | exact digraph_reverse_reverse | (apply digraph_reverse_reverse <;> assumption) | (apply digraph_reverse_reverse <;> simp_all) | simpa using digraph_reverse_reverse | (simp only [digraph_is_quasi_kernel] at *; first | exact digraph_reverse_reverse | (apply digraph_reverse_reverse <;> assumption) | (apply digraph_reverse_reverse <;> simp_all) | simpa using digraph_reverse_reverse)
