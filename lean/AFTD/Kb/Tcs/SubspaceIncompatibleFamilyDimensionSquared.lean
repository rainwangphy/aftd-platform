import AFTD.Prelude
import AFTD.Kb.Tcs.HasSubspaceCompatibleIncompatibleFamily
import AFTD.Kb.Tcs.SubspaceIncompatibleFamilyOfMicData
import AFTD.Kb.Tcs.ExistsRankOneMicWithInvertibleDual

/-!
# subspace_incompatible_family_dimension_squared

Topic: quantum   Node: 6876635650e6

Provenance: formalization of a published result. Source: arXiv:2610.37347 (Measurement incompatibility and noiseless quantum codes), Corollary 1

For every integer d >= 2, there exists a family of d^2 binary measurements on C^d that is incompatible on C^d and jointly measurable after compression to any proper subspace, so has_subspace_compatible_incompatible_family d (d ^ 2) holds.
-/

/-- For every d >= 2, there exists a family of d^2 binary measurements on C^d incompatible globally but compatible on every proper subspace. -/
theorem subspace_incompatible_family_dimension_squared (d : ℕ) (hd : 2 ≤ d) : has_subspace_compatible_incompatible_family d (d ^ 2) := by
  obtain ⟨vs, fs, F0, j0, h1, h2, h3, h4, h5, h6, h7⟩ := exists_rank_one_mic_with_invertible_dual d hd
  exact subspace_incompatible_family_of_mic_data vs fs F0 j0 h1 h2 h3 h4 h5 h6 h7
