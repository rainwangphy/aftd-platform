import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.Physics.ThermomajorizationDiff

/-!
# thermomajorization_expected_missed_error

Topic: quantum_mechanics   Node: 7e5ffdb4a26d

Provenance: formalization of a published result. Source: OP-2138

For dimension n : ℕ, a function q : Finset.Ioo 0 n → ℝ on the subtype of probe ranks, and population vectors x, y : Fin n → ℝ, the expected missed conversion error thermomajorization_expected_missed_error n q x y is thermomajorization_probe_error n (Finset.Ioo 0 n) x y - ∑ k : Finset.Ioo 0 n, q k * max 0 (thermomajorization_diff x y (k : ℕ)).
-/

/-- Expected thermomajorization missed conversion error under random single probe distribution q. -/
noncomputable def thermomajorization_expected_missed_error
    (n : ℕ) (q : Finset.Ioo 0 n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  thermomajorization_probe_error n (Finset.Ioo 0 n) x y -
    ∑ k : Finset.Ioo 0 n, q k * max 0 (thermomajorization_diff x y (k : ℕ))
