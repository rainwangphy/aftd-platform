import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsQuasiKernel
import AFTD.Kb.Tcs.DigraphIsQuasiKernelEmptyOfIsEmpty

/-!
# digraph_not_is_quasi_kernel_empty_of_nonempty

Topic: graphs   Node: 5212614c26b7

Provenance: helper lemma. step towards digraph_small_quasi_kernel_exists

The empty set is not a quasi-kernel in any nonempty digraph.
-/

/-- In any nonempty digraph, the empty set cannot be a quasi-kernel since no vertex is reached. -/
theorem digraph_not_is_quasi_kernel_empty_of_nonempty {α : Type*} [Nonempty α] (D : Digraph α) :
    ¬ digraph_is_quasi_kernel D ∅ := by first | exact digraph_is_quasi_kernel_empty_of_isEmpty | (apply digraph_is_quasi_kernel_empty_of_isEmpty <;> assumption) | (apply digraph_is_quasi_kernel_empty_of_isEmpty <;> simp_all) | simpa using digraph_is_quasi_kernel_empty_of_isEmpty | (simp only [digraph_is_quasi_kernel] at *; first | exact digraph_is_quasi_kernel_empty_of_isEmpty | (apply digraph_is_quasi_kernel_empty_of_isEmpty <;> assumption) | (apply digraph_is_quasi_kernel_empty_of_isEmpty <;> simp_all) | simpa using digraph_is_quasi_kernel_empty_of_isEmpty)
