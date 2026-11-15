import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# thermomajorization_missed_error

Topic: quantum_mechanics   Node: 6337b0fbe608

Provenance: formalization of a published result. Source: arXiv:2610.35433

For dimension n and probe set F : Finset ℕ, thermomajorization_missed_error n F is the supremum over all nonincreasing probability vectors x, y in stdSimplex ℝ (Fin n) satisfying Antitone x and Antitone y of the difference thermomajorization_probe_error n (Finset.Ioo 0 n) x y - thermomajorization_probe_error n F x y.
-/

/-- Worst-case missed conversion error over nonincreasing probability vectors for probe set F. -/
noncomputable def thermomajorization_missed_error (n : ℕ) (F : Finset ℕ) : ℝ := ⨆ (x ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}) (y ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}), (thermomajorization_probe_error n (Finset.Ioo 0 n) x y - thermomajorization_probe_error n F x y)
