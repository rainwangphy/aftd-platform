import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsRationalSubspace
import AFTD.Kb.NumberTheory.IntToEuclidean

/-!
# is_rational_subspace_bot

Topic: elementary_number_theory   Node: dbe807f3152b

Provenance: helper lemma. arXiv:2610.37711, Definition 3.1

The zero subspace ⊥ of ℝ^n is a rational subspace.
-/

/-- The trivial subspace ⊥ is rational. -/
theorem is_rational_subspace_bot (n : ℕ) : is_rational_subspace n ⊥ := by
  refine ⟨∅, ?_⟩
  simp
