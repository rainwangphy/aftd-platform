import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# thermomajorization_pointwise_missed_error

Topic: quantum_mechanics   Node: b760cbf65140

Provenance: formalization of a published result. Source: arXiv:2610.35433

For dimension n : ℕ, probe set F : Finset ℕ, and rank j : ℕ, the pointwise missed error thermomajorization_pointwise_missed_error n F j is the supremum over nonincreasing probability vectors x, y in stdSimplex ℝ (Fin n) of the difference thermomajorization_diff x y j - thermomajorization_probe_error n F x y.
-/

/-- Pointwise worst-case missed conversion error at rank j under probe set F. -/
noncomputable def thermomajorization_pointwise_missed_error (n : ℕ) (F : Finset ℕ) (j : ℕ) : ℝ := ⨆ (x ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}) (y ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}), (thermomajorization_diff x y j - thermomajorization_probe_error n F x y)
