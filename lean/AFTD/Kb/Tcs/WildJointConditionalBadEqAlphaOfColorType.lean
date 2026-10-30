import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointConditionedBadProbabilityTransport
import AFTD.Kb.Tcs.WildNormalizedColorCanonicalIsomorphism
import AFTD.Kb.Tcs.WildJointCanonicalTypeValues
import AFTD.Kb.Tcs.WildJointAlphaTypeWellDefinedOdd
import AFTD.Kb.Tcs.WildJointAlphaOfColorType
import AFTD.Kb.Tcs.WildJointCanonicalType
import AFTD.Kb.Tcs.WildJointFirstBlock
import AFTD.Kb.Tcs.WildJointCanonicalMatching
import AFTD.Kb.Tcs.WildJointAlpha
import AFTD.Kb.Tcs.WildJointBlock
import AFTD.Kb.Tcs.WildJointTypeD
import AFTD.Kb.Tcs.WildJointTypeB
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.Tcs.WildJointTypeA
import AFTD.Kb.Tcs.WildJointTypeC
import AFTD.Kb.Tcs.WildJointColorType

/-!
# wild_joint_conditional_bad_eq_alpha_of_color_type

Topic: graphs   Node: 7a4ad7869d9e

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry and exact permutation conditioning supporting wild_joint_expected_ID_eq_alpha_sum. This uses the corrected odd-q orbit theorem; it does not establish the main weighted sign or a new wild-number bound.

For odd q>=3 and a normalized symmetric row-injective array, the conditional probability that a chosen WHOLE color is bad, given a prescribed three-element first block, equals alpha_of_color_type of that triple and color. The equality is of exact finite-cardinality ratios; all proper cuts are included.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 10000

theorem wild_joint_conditional_bad_eq_alpha_of_color_type
    (q : ℕ) (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (A : Fin (3*q) → Fin (3*q) → Fin (3*q))
    (hid : ∀ x, A x x = x) (hsym : ∀ x y, A x y = A y x)
    (hinj : ∀ x, Function.Injective (A x))
    (T : Finset (Fin (3*q))) (hT : T.card = 3) (i : Fin (3*q)) :
    (((univ.filter fun σ : Equiv.Perm (Fin (3*q)) =>
      wild_joint_first_block q σ = T ∧
        wild_joint_bad_relation q (wild_joint_block q σ) (fun x y => x ≠ y ∧ A x y = i)).card : ℝ) /
      (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ = T).card) =
    wild_joint_alpha_of_color_type q hq A T i := by
  classical
  obtain ⟨e,hei,heR⟩ := wild_normalized_color_canonical_isomorphism q hq hodd A hid hsym hinj i
  have hcard : (T.image e).card = 3 := by
    rw [card_image_of_injective T e.injective,hT]
  have hzero : (⟨0,by omega⟩ : Fin (3*q)) ∈ T.image e ↔ i ∈ T := by
    rw [← hei]
    simp only [mem_image,e.injective.eq_iff,exists_eq_right]
  have hedge : (∃ x ∈ T.image e, ∃ y ∈ T.image e, wild_joint_canonical_matching q x y) ↔
      ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ A x y = i := by
    constructor
    · rintro ⟨u,hu,v,hv,hxy⟩
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
      exact ⟨x,hx,y,hy,(heR x y).mp hxy⟩
    · rintro ⟨x,hx,y,hy,hxy⟩
      exact ⟨e x,mem_image.mpr ⟨x,hx,rfl⟩,e y,mem_image.mpr ⟨y,hy,rfl⟩,(heR x y).mpr hxy⟩
  have hty : wild_joint_canonical_type q hq (T.image e) = wild_joint_color_type q A T i := by
    unfold wild_joint_canonical_type wild_joint_color_type
    simp only [hedge,hzero]
  have htrans := wild_joint_conditioned_bad_probability_transport q
    (fun x y => x ≠ y ∧ A x y = i) (wild_joint_canonical_matching q)
    T (T.image e) e rfl heR
  change _ = wild_joint_alpha q (T.image e) at htrans
  rw [htrans]
  have heq (U : Finset (Fin (3*q))) (hU : U.card = 3)
      (htU : wild_joint_canonical_type q hq U = wild_joint_color_type q A T i) :
      wild_joint_alpha q (T.image e) = wild_joint_alpha q U :=
    wild_joint_alpha_type_well_defined_odd q hq hodd _ U hcard hU (hty.trans htU.symm)
  have hv := wild_joint_canonical_type_values q hq
  have hbound : wild_joint_color_type q A T i ≤ 3 := by
    unfold wild_joint_color_type
    split_ifs <;> omega
  unfold wild_joint_alpha_of_color_type
  split_ifs with h0 h1 h2
  · apply heq
    · norm_num [wild_joint_type_A,Fin.ext_iff]
    · exact hv.1.trans h0.symm
  · apply heq
    · norm_num [wild_joint_type_B,Fin.ext_iff]
    · exact hv.2.1.trans h1.symm
  · apply heq
    · norm_num [wild_joint_type_C,Fin.ext_iff]
    · exact hv.2.2.1.trans h2.symm
  · apply heq
    · norm_num [wild_joint_type_D,Fin.ext_iff]
    · have hh : wild_joint_color_type q A T i = 3 := by omega
      exact hv.2.2.2.trans hh.symm
