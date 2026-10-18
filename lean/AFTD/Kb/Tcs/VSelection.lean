import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonSelectionComplexity

/-!
# v_selection

Topic: algorithms   Node: b8745e7826a2

Provenance: formalization of a published result. Source: scout/2610-18740-selecting-the-7th-smallest-of-16-elements-takes-exactly-28.md:Sec. 1

The minimum number of pairwise comparisons V_i(n) needed in the worst case by a deterministic comparison algorithm (decision tree) to find the i-th smallest element among n distinct elements, defined for 0 < i ∧ i ≤ n as the comparison selection complexity of 0-based rank i - 1 in Fin n, and 0 otherwise.
-/

/-- The minimum worst-case comparison complexity V_i(n) to find the i-th smallest of n elements. -/
noncomputable def v_selection (n : ℕ) (i : ℕ) : ℕ := if h : 0 < i ∧ i ≤ n then comparison_selection_complexity (n := n) ⟨i - 1, by omega⟩ else 0
