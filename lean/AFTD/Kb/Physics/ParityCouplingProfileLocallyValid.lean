import AFTD.Prelude

/-!
# parity_coupling_profile_locally_valid

Topic: quantum_mechanics   Node: d1587805f94d

Provenance: helper lemma. Exact counterexample to an auxiliary OP-827 proof route, experiments 22515 and 22523.

The five rational parameters in the parity coupling counterexample satisfy each local product inequality.
-/

theorem parity_coupling_profile_locally_valid :
    (3 : ℝ) / 4 * (3 / 4) ≤ 9 / 16 ∧
    (9 : ℝ) / 16 * (3 / 8) ≤ 3 / 4 ∧
    (3 : ℝ) / 4 * (1 / 2) ≤ 3 / 8 := by norm_num
