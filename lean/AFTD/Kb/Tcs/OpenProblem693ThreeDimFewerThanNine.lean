import AFTD.Prelude
import AFTD.Kb.Tcs.HasSubspaceCompatibleIncompatibleFamily
import AFTD.Kb.Tcs.PptQutritSourceProjectionBasisFromIsometryFactor
import AFTD.Kb.Tcs.RankTwoQutritProjectionIsometry
import AFTD.Kb.Tcs.PptQutritSourceNormalizedGramIfThreeLemmas
import AFTD.Kb.Tcs.PptQutritBellStatePartialTransposeInvariant
import AFTD.Kb.Tcs.RealPositiveQutritGramNormalizer
import AFTD.Kb.Tcs.OpenProblem693ThreeDimFewerThanNineIfLemmas
import AFTD.Kb.Tcs.PptQutritBellAliceBinaryEffectsValid
import AFTD.Kb.Tcs.PptQutritSteeredNormalizerMarginalIdentity
import AFTD.Kb.Tcs.ThreeOrthonormalRowsCodimensionOne
import AFTD.Kb.Tcs.RankFourPptNormalCompletionPhase
import AFTD.Kb.Tcs.RealSymmetricCommutingPairOrthogonalDiagonalization
import AFTD.Kb.Tcs.QutritFixedPhaseSchurFourProductDecomposition
import AFTD.Kb.Tcs.FiniteWeightedThreeBinaryHiddenModelHasParent
import AFTD.Kb.Tcs.PptQutritSteeredEffectIsValid
import AFTD.Kb.Tcs.RankOneQutritCompressionThreeBinaryParent
import AFTD.Kb.Tcs.PptQutritSteeredEffect
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.PptQutritBellVector

/-!
# open_problem_693_three_dim_fewer_than_nine

Topic: quantum   Node: b9601ec9d826

Provenance: formalization of a published result. Source: arXiv:2610.37347 (Measurement incompatibility and noiseless quantum codes), after Corollary 1

There exists a natural number k strictly less than 9 such that has_subspace_compatible_incompatible_family 3 k holds, meaning there is a family of k binary measurements on C^3 that is incompatible on C^3 yet jointly measurable on every proper subspace.
-/

/-- Open Problem OP-693: existence of a family of strictly fewer than 9 binary measurements on C^3 incompatible globally but compatible on all proper subspaces. -/
theorem open_problem_693_three_dim_fewer_than_nine : ∃ k < 9, has_subspace_compatible_incompatible_family 3 k := by
  have hselect := ppt_qutrit_source_projection_basis_from_isometry_factor
    rank_two_qutrit_projection_isometry
  have hgram := ppt_qutrit_source_normalized_gram_if_three_lemmas hselect
    ppt_qutrit_bell_state_partial_transpose_invariant real_positive_qutrit_gram_normalizer
  apply open_problem_693_three_dim_fewer_than_nine_if_lemmas hgram
    ppt_qutrit_bell_alice_binary_effects_valid
    ppt_qutrit_steered_normalizer_marginal_identity
    three_orthonormal_rows_codimension_one
    rank_four_ppt_normal_completion_phase
    real_symmetric_commuting_pair_orthogonal_diagonalization
    qutrit_fixed_phase_schur_four_product_decomposition
    (finite_weighted_three_binary_hidden_model_has_parent 2 4)
    ppt_qutrit_steered_effect_is_valid
  intro P hP hPP hrank
  exact rank_one_qutrit_compression_three_binary_parent
    ppt_qutrit_steered_effect P ppt_qutrit_steered_effect_is_valid hP hPP hrank
