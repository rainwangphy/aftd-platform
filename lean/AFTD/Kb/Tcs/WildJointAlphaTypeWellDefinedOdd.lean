import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointCanonicalMatchingIsInvolution
import AFTD.Kb.Tcs.WildInvolutionThreeSetIsomorphism
import AFTD.Kb.Tcs.WildJointAlphaEqOfMatchingIsomorphism
import AFTD.Kb.Tcs.WildJointCanonicalType
import AFTD.Kb.Tcs.WildJointAlpha
import AFTD.Kb.Tcs.WildJointCanonicalMatching

/-!
# wild_joint_alpha_type_well_defined_odd

Topic: graphs   Node: 1e8be717679d

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry supporting the mixed-moment route for https://arxiv.org/html/2610.22142v1. Exact experiment9566 exposed the missing parity assumption. The original false helper remains retired and its proof record is preserved. No wild-number bound or research advance is claimed.

For odd q>=3, any two three-element subsets of the same canonical type have equal conditional whole-bad probabilities alpha. This faithfully corrects the retired helper by adding the essential odd-q hypothesis; it does not strengthen the parent formula, which already assumes odd q.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000

theorem wild_joint_alpha_type_well_defined_odd
    (q : ℕ) (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (S T : Finset (Fin (3*q))) (hS : S.card = 3) (hT : T.card = 3)
    (hty : wild_joint_canonical_type q hq S = wild_joint_canonical_type q hq T) :
    wild_joint_alpha q S = wild_joint_alpha q T := by
  classical
  let z : Fin (3*q) := ⟨0,by omega⟩
  have hfixed : z ∈ S ↔ z ∈ T := by
    dsimp only [wild_joint_canonical_type] at hty
    split_ifs at hty <;> simp_all [z] <;> aesop
  have hedge : (∃ x ∈ S, ∃ y ∈ S, wild_joint_canonical_matching q x y) ↔
      ∃ x ∈ T, ∃ y ∈ T, wild_joint_canonical_matching q x y := by
    dsimp only [wild_joint_canonical_type] at hty
    split_ifs at hty <;> simp_all [z] <;> aesop
  obtain ⟨f,hf,hfix,hrel⟩ := wild_joint_canonical_matching_is_involution q hq hodd
  have hedge' : (∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ f x = y) ↔
      ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ f x = y := by
    simpa only [hrel] using hedge
  obtain ⟨e,he,heT⟩ := wild_involution_three_set_isomorphism
    f f hf hf z z hfix hfix S T hS hT hfixed hedge'
  apply wild_joint_alpha_eq_of_matching_isomorphism q S T e heT
  intro x y
  rw [hrel,hrel,← he]
  simp only [e.injective.eq_iff,ne_eq]
