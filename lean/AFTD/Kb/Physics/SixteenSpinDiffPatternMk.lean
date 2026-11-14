import AFTD.Prelude
import AFTD.Kb.Physics.SixteenSpinDiffPattern
import AFTD.Kb.GameTheoryEconomics.RankingSwapApplyLeft

/-!
# sixteen_spin_diff_pattern_mk

Topic: quantum_mechanics   Node: f758a12029cf

Provenance: helper lemma. step towards op_1695_pi_over_eight_eq_bipartite_subgraphs

On a concrete unordered pair {u, v}, the π/8 difference pattern of a spin configuration sp says exactly that sp differs in components 1 and 3 and agrees in component 2.
-/

/-- Computation rule for `sixteen_spin_diff_pattern` on an explicit unordered pair. -/
theorem sixteen_spin_diff_pattern_mk {V : Type*} (sp : V → Fin 4 → Fin 2) (u v : V) :
    sixteen_spin_diff_pattern sp s(u, v) ↔ (sp u 1 ≠ sp v 1 ∧ sp u 2 = sp v 2 ∧ sp u 3 ≠ sp v 3) := by first | exact ranking_swap_apply_left | (apply ranking_swap_apply_left <;> assumption) | (apply ranking_swap_apply_left <;> simp_all) | simpa using ranking_swap_apply_left | (simp only [sixteen_spin_diff_pattern] at *; first | exact ranking_swap_apply_left | (apply ranking_swap_apply_left <;> assumption) | (apply ranking_swap_apply_left <;> simp_all) | simpa using ranking_swap_apply_left)
