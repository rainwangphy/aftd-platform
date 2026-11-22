import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationExpectedMissedError
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# thermomajorization_random_probe_worst_error

Topic: quantum_mechanics   Node: 9c2f2dc3cc98

Provenance: formalization of a published result. Source: OP-2138

For dimension n : ℕ and a function q : Finset.Ioo 0 n → ℝ on the subtype of probe ranks, the worst-case expected missed conversion error thermomajorization_random_probe_worst_error n q is ⨆ (x ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}) (y ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}), thermomajorization_expected_missed_error n q x y.
-/

/-- Worst-case expected missed conversion error under random single probe distribution q. -/
noncomputable def thermomajorization_random_probe_worst_error
    (n : ℕ) (q : Finset.Ioo 0 n → ℝ) : ℝ :=
  ⨆ (x ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v})
    (y ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}),
    thermomajorization_expected_missed_error n q x y
