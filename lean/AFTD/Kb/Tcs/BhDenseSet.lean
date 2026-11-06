import AFTD.Prelude
import AFTD.Kb.Tcs.BhDenseStage

/-!
# bh_dense_set

Topic: combinatorics   Node: 03d06320655c

Provenance: helper lemma. step towards infinite_bh_set_upper_density_eq_one_div_h

The infinite set produced by the construction (paper (3.2)): the union of all stages `S_k`.
-/

/-- The union of all stages of the recursive construction. -/
noncomputable def bh_dense_set (h : ℕ) : Set ℕ := {x | ∃ k, x ∈ bh_dense_stage h k}
