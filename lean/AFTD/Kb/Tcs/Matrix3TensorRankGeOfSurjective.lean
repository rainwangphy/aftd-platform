import AFTD.Prelude
import AFTD.Kb.Tcs.Matrix3TensorRankGe
import AFTD.Kb.Tcs.Matrix3TensorRankLeOfSurjective

/-!
# matrix3_tensor_rank_ge_of_surjective

Topic: algebraic_complexity   Node: 6561b3883a4f

If f : R → S is a surjective homomorphism of commutative semirings and every valid triad decomposition of 3x3 matrix multiplication over S has at least r products, then the same holds over R.
-/

theorem matrix3_tensor_rank_ge_of_surjective {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (hf : Function.Surjective f) (r : ℕ) (h : matrix3_tensor_rank_ge S r) : matrix3_tensor_rank_ge R r := by
  intro L hL
  obtain ⟨L', hlen, hL'⟩ := matrix3_tensor_rank_le_of_surjective f hf L.length ⟨L, le_rfl, hL⟩
  exact (h L' hL').trans hlen
