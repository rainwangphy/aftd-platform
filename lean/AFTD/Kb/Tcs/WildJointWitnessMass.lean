import AFTD.Prelude

/-!
# wild_joint_witness_mass

Topic: graphs   Node: 2b51831c6f79

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

W = n(n-1)/2 for n = 3q, the total number of unordered vertex pairs, equal to the sum over supports T of the multiplicity mu(T).
-/

/-- Witness mass W = n(n-1)/2 with n = 3q (= sum_T mu(T)). -/
noncomputable def wild_joint_witness_mass (q : ℕ) : ℝ := ((3*q : ℝ) * ((3*q : ℝ) - 1)) / 2
