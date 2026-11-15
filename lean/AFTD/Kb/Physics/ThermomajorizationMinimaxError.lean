import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationMissedError

/-!
# thermomajorization_minimax_error

Topic: quantum_mechanics   Node: b64b213cd5a1

Provenance: formalization of a published result. Source: arXiv:2610.35433

For dimension n and budget m : ℕ, the minimax missed error thermomajorization_minimax_error n m is the infimum of thermomajorization_missed_error n F over all subsets F of Finset.Ioo 0 n with cardinality m (elements of Finset.powersetCard m (Finset.Ioo 0 n)).
-/

/-- Optimal minimax missed thermomajorization conversion error for a budget of m probes. -/
noncomputable def thermomajorization_minimax_error (n m : ℕ) : ℝ := ⨅ F ∈ Finset.powersetCard m (Finset.Ioo 0 n), thermomajorization_missed_error n F
