import AFTD.Prelude
import AFTD.Kb.Tcs.IsGraphBisection
import AFTD.Kb.Tcs.Op309FivePairCutObstructionKernel

/-!
# not_is_graph_bisection_empty_bool

Topic: graphs   Node: efaa085dcb3f

Provenance: helper lemma. folklore

In the two-element type Bool, the empty set is not a bisection.
-/

/-- The empty set in Bool is not a bisection. -/
theorem not_is_graph_bisection_empty_bool : ¬ is_graph_bisection (∅ : Finset Bool) := by first | exact op309_five_pair_cut_obstruction_kernel | (apply op309_five_pair_cut_obstruction_kernel <;> assumption) | (apply op309_five_pair_cut_obstruction_kernel <;> simp_all) | simpa using op309_five_pair_cut_obstruction_kernel | (simp only [is_graph_bisection] at *; first | exact op309_five_pair_cut_obstruction_kernel | (apply op309_five_pair_cut_obstruction_kernel <;> assumption) | (apply op309_five_pair_cut_obstruction_kernel <;> simp_all) | simpa using op309_five_pair_cut_obstruction_kernel)
