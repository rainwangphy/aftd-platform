import AFTD.Prelude

/-!
# const_vec

Topic: communication   Node: 15c03d4655b5

Provenance: helper lemma. step towards commuting_quantum_efficiency_classical_lower_bound

The normalized constant vector of the real Euclidean space on ι.
-/

/-- The constant vector with all coordinates (√(card ι))⁻¹ in EuclideanSpace ℝ ι. -/
noncomputable def const_vec (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => (Real.sqrt (Fintype.card ι))⁻¹)
