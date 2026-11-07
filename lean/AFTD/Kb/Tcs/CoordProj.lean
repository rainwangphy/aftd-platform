import AFTD.Prelude

/-!
# coord_proj

Topic: communication   Node: 494627c3f0b7

Provenance: helper lemma. step towards commuting_quantum_efficiency_classical_lower_bound

The coordinate projection onto a finite set S of coordinates: the sum over i in S of the rank-one map v ↦ ⟪e_i, v⟫ • e_i, as a continuous linear endomorphism of the real Euclidean space with orthonormal basis (single i 1).
-/

/-- Sum of rank-one coordinate projections over S, as a continuous linear endomorphism of EuclideanSpace ℝ ι. -/
noncomputable def coord_proj {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := ∑ i ∈ S, InnerProductSpace.rankOne ℝ (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single i (1:ℝ))
