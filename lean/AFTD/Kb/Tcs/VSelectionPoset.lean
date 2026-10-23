import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.Tcs.ComparisonTreeCorrectForSelection
import AFTD.Kb.Tcs.ComparisonTreeDepth

/-!
# v_selection_poset

Topic: algorithms   Node: a5f6e4cf2c2c

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 2, line 270

For a natural number n, a partial order P on Fin n, and a rank i, V_i(P) is the infimum of depths of all comparison decision trees on n elements that correctly select the i-th smallest element for P.
-/

/-- The minimum worst-case number of comparisons V_i(P) to select the i-th smallest element for poset P. -/
noncomputable def v_selection_poset (n : ℕ) (P : PartialOrder (Fin n)) (i : ℕ) : ℕ := open scoped Classical in
  sInf { d : ℕ | ∃ T : ComparisonTree n, comparison_tree_correct_for_selection n P i T ∧ comparison_tree_depth T = d }
