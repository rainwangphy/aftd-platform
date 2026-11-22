import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationWitnessX
import AFTD.Kb.Physics.ThermomajorizationWitnessY
import AFTD.Kb.Physics.ThermomajorizationExpectedMissedError

/-!
# thermomajorization_witness_value

Topic: quantum_mechanics   Node: 049e9240f634

Provenance: helper lemma. step towards thermomajorization_random_single_probe_sharp_witness_family

For dimension n, weight function q on probe ranks, and triple t = (a,j,b), the witness value is the expected missed error of the witness pair (witness_x n a j b, witness_y n j).
-/

/-- The expected missed error at the witness pair indexed by a triple (a,j,b); notation helper for the finite-maximum over the witness family. -/
noncomputable def thermomajorization_witness_value (n : ℕ) (q : Finset.Ioo 0 n → ℝ) (t : ℕ × ℕ × ℕ) : ℝ := thermomajorization_expected_missed_error n q (thermomajorization_witness_x n t.1 t.2.1 t.2.2) (thermomajorization_witness_y n t.2.1)
