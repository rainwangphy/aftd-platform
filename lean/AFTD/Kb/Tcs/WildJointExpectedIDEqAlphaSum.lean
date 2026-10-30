import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointExpectedID
import AFTD.Kb.Tcs.WildJointMultiplicity
import AFTD.Kb.Tcs.WildJointAlphaOfColorType
import AFTD.Kb.Tcs.WildJointColorType
import AFTD.Kb.Tcs.WildJointAlpha
import AFTD.Kb.Tcs.WildJointInvalidCount
import AFTD.Kb.Tcs.WildJointBadColorCount
import AFTD.Kb.Tcs.WildJointBlock
import AFTD.Kb.Tcs.WildJointBlockSet
import AFTD.Kb.Tcs.WildJointFirstBlock
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.Tcs.WildJointCanonicalMatching
import AFTD.Kb.Tcs.WildJointCanonicalType
import AFTD.Kb.Tcs.WildJointTypeA
import AFTD.Kb.Tcs.WildJointTypeB
import AFTD.Kb.Tcs.WildJointTypeC
import AFTD.Kb.Tcs.WildJointTypeD
import AFTD.Kb.Tcs.WildJointInvalidCountEqSumMultiplicity
import AFTD.Kb.Tcs.WildJointCanonicalTypeValues
import AFTD.Kb.Tcs.WildJointAlphaTypeWellDefinedOdd
import AFTD.Kb.Tcs.WildJointConditionalBadEqAlphaOfColorType
import AFTD.Kb.Tcs.WildJointFirstBlockFiberMass
import AFTD.Kb.Tcs.WildJointFirstBlockMixedReduction

/-!
# wild_joint_expected_ID_eq_alpha_sum

Topic: graphs   Node: 7e6155438fd8

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

Core reduction: E[I*D] = q/C(n,3) * sum over 3-sets T of mu(T) * sum_i alpha_of_color_type(T,i), where alpha_of_color_type is the alpha of the colour-i orbit type of T.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
lemma wild_joint_bad_count_eq_indicator_sum (q : ℕ)
    (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (σ : Equiv.Perm (Fin (3*q))) :
    (wild_joint_bad_color_count q A σ : ℝ) =
      ∑ i : Fin (3*q),if wild_joint_bad_relation q (wild_joint_block q σ)
        (fun x y => x≠y ∧ A x y=i) then (1 : ℝ) else 0 := by
  classical
  simp [wild_joint_bad_color_count,sum_ite]

lemma wild_joint_first_block_bad_fiber_sum (q : ℕ)
    (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (T : Finset (Fin (3*q))) :
    (∑ σ ∈ (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ=T),
      (wild_joint_bad_color_count q A σ : ℝ)) =
    ∑ i : Fin (3*q),((univ.filter fun σ : Equiv.Perm (Fin (3*q)) =>
      wild_joint_first_block q σ=T ∧ wild_joint_bad_relation q (wild_joint_block q σ)
        (fun x y => x≠y ∧ A x y=i)).card : ℝ) := by
  classical
  simp_rw [wild_joint_bad_count_eq_indicator_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [sum_ite,filter_filter]

/-- Reduction of E[I*D] to a single sum of mu(T) against colour-type alphas. -/
theorem wild_joint_expected_ID_eq_alpha_sum (q : ℕ) (hq : 3 ≤ q) (hodd : q % 2 = 1) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (hid : ∀ a, A a a = a) (hsym : ∀ a b, A a b = A b a) (hinj : ∀ a, Function.Injective (A a)) : wild_joint_expected_ID q A = ((q : ℝ) / ((3*q).choose 3 : ℝ)) * ∑ T ∈ (Finset.univ.filter (fun T : Finset (Fin (3*q)) => T.card = 3)), (wild_joint_multiplicity q A T : ℝ) * (∑ i : Fin (3*q), wild_joint_alpha_of_color_type q hq A T i) := by
  classical
  let F := fun T : Finset (Fin (3*q)) =>
    (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ=T).card
  let N : ℝ := (3*q).factorial
  let C : ℝ := (3*q).choose 3
  have hN : N≠0 := by dsimp [N]; exact_mod_cast Nat.factorial_ne_zero (3*q)
  have hC : C≠0 := by
    dsimp [C]
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : 3≤3*q))
  have hmass (T : Finset (Fin (3*q))) (hT : T.card=3) : (F T : ℝ)*C=N := by
    have h := wild_joint_first_block_fiber_mass q hq T hT
    rw [Fintype.card_perm,Fintype.card_fin] at h
    dsimp [F,C,N]
    exact_mod_cast h
  have hF (T : Finset (Fin (3*q))) (hT : T.card=3) : (F T : ℝ)≠0 := by
    intro hh
    have h := hmass T hT
    rw [hh,zero_mul] at h
    exact hN h.symm
  have hfiber (T : Finset (Fin (3*q))) (hT : T.card=3) :
      (∑ σ ∈ (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ=T),
        (wild_joint_bad_color_count q A σ : ℝ)) =
      (N/C)*(∑ i : Fin (3*q),wild_joint_alpha_of_color_type q hq A T i) := by
    rw [wild_joint_first_block_bad_fiber_sum,mul_sum]
    apply sum_congr rfl
    intro i _
    have h := wild_joint_conditional_bad_eq_alpha_of_color_type q hq hodd A hid hsym hinj T hT i
    change _/(F T : ℝ)=_ at h
    have hn := (div_eq_iff (hF T hT)).mp h
    have hm : (F T : ℝ)=N/C := (eq_div_iff hC).mpr (hmass T hT)
    rw [hm] at hn
    exact hn.trans (mul_comm _ _)
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin (3*q)))),
      wild_joint_first_block q σ ∈ (univ.filter fun T : Finset (Fin (3*q)) => T.card=3) := by
    intro σ _
    exact mem_filter.mpr ⟨mem_univ _,wild_joint_first_block_fiber_mass_card q hq σ⟩
  have hdecomp := sum_fiberwise_of_maps_to hmaps
    (fun σ : Equiv.Perm (Fin (3*q)) =>
      (wild_joint_multiplicity q A (wild_joint_first_block q σ) : ℝ)*
        (wild_joint_bad_color_count q A σ : ℝ))
  have hsum : (∑ σ : Equiv.Perm (Fin (3*q)),
      (wild_joint_multiplicity q A (wild_joint_first_block q σ) : ℝ)*
        (wild_joint_bad_color_count q A σ : ℝ)) =
      (N/C)*(∑ T ∈ (univ.filter fun T : Finset (Fin (3*q)) => T.card=3),
        (wild_joint_multiplicity q A T : ℝ)*
          (∑ i : Fin (3*q),wild_joint_alpha_of_color_type q hq A T i)) := by
    rw [← hdecomp,mul_sum]
    apply sum_congr rfl
    intro T hT
    have hc := (mem_filter.mp hT).2
    calc
      _ = (wild_joint_multiplicity q A T : ℝ)*
          (∑ σ ∈ (univ.filter fun σ : Equiv.Perm (Fin (3*q)) => wild_joint_first_block q σ=T),
            (wild_joint_bad_color_count q A σ : ℝ)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro σ hσ
        rw [(mem_filter.mp hσ).2]
      _ = _ := by rw [hfiber T hc]; ring
  unfold wild_joint_expected_ID
  rw [wild_joint_first_block_mixed_reduction q hq A hid hsym hinj]
  rw [hsum]
  change (1/N)*((q : ℝ)*((N/C)*_))=((q : ℝ)/C)*_
  field_simp [hN,hC]
  <;> ring
