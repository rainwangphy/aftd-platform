import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointInvalidCountEqSumMultiplicity
import AFTD.Kb.Tcs.WildJointBadColorCount
import AFTD.Kb.Tcs.WildJointFirstBlock
import AFTD.Kb.Tcs.WildJointMultiplicity
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.Tcs.WildJointInvalidCount
import AFTD.Kb.Tcs.WildJointBlockSet
import AFTD.Kb.Tcs.WildJointBlock

/-!
# wild_joint_first_block_mixed_reduction

Topic: graphs   Node: 19554308938b

Provenance: helper lemma. IN-382 / OP-306 campaign9. Explicit residual finite-counting tasks for wild_joint_expected_ID_eq_alpha_sum; no wild-number advance is claimed.

For q>=3 and a normalized array, summing I times the whole-bad count D over all permutations equals q times the sum of first-block witness multiplicity times D. This is block symmetry with full color deduplication.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
lemma wild_joint_bad_relation_block_relabel (q : ℕ)
    (p : Fin (3*q) → Fin q) (R : Fin (3*q) → Fin (3*q) → Prop)
    (e : Equiv.Perm (Fin q)) :
    wild_joint_bad_relation q (fun v => e (p v)) R ↔ wild_joint_bad_relation q p R := by
  classical
  have forward (p : Fin (3*q) → Fin q) (e : Equiv.Perm (Fin q)) :
      wild_joint_bad_relation q p R → wild_joint_bad_relation q (fun v => e (p v)) R := by
    rintro ⟨B,hB,hBU,hR⟩
    refine ⟨B.image e,hB.image _,?_,?_⟩
    · intro hh
      apply hBU
      apply eq_univ_of_forall
      intro b
      have : e b ∈ B.image e := by rw [hh]; exact mem_univ _
      simpa only [mem_image,e.injective.eq_iff,exists_eq_right] using this
    · intro x y hxy
      simpa only [mem_image,e.injective.eq_iff,exists_eq_right] using hR x y hxy
  constructor
  · intro h
    have := forward (fun v => e (p v)) e.symm h
    simpa only [Equiv.symm_apply_apply] using this
  · exact forward p e

noncomputable def wild_joint_position_relabel (q : ℕ) (e : Equiv.Perm (Fin q)) :
    Equiv.Perm (Fin (3*q)) :=
  let E : Fin q × Fin 3 ≃ Fin (3*q) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm q 3))
  E.symm.trans ((e.prodCongr (Equiv.refl (Fin 3))).trans E)

lemma wild_joint_position_relabel_block (q : ℕ) (e : Equiv.Perm (Fin q))
    (σ : Equiv.Perm (Fin (3*q))) (v : Fin (3*q)) :
    wild_joint_block q ((wild_joint_position_relabel q e).trans σ) v =
      e.symm (wild_joint_block q σ v) := by
  apply Fin.ext
  simp [wild_joint_block,wild_joint_position_relabel,finProdFinEquiv,Fin.divNat]
  omega

lemma wild_joint_position_relabel_bad_count (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q))
    (e : Equiv.Perm (Fin q)) (σ : Equiv.Perm (Fin (3*q))) :
    wild_joint_bad_color_count q A ((wild_joint_position_relabel q e).trans σ) =
      wild_joint_bad_color_count q A σ := by
  classical
  unfold wild_joint_bad_color_count
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and]
  have hp : wild_joint_block q ((wild_joint_position_relabel q e).trans σ) =
      fun v => e.symm (wild_joint_block q σ v) := funext (wild_joint_position_relabel_block q e σ)
  rw [hp]
  exact wild_joint_bad_relation_block_relabel q _ _ e.symm

lemma wild_joint_block_set_zero (q : ℕ) (hq : 0<q) (σ : Equiv.Perm (Fin (3*q))) :
    wild_joint_block_set q σ ⟨0,hq⟩ = wild_joint_first_block q σ := by
  ext v
  simp only [wild_joint_block_set,wild_joint_first_block,mem_filter,mem_univ,true_and,Fin.val_mk]
  omega

lemma wild_joint_position_swap_first (q : ℕ) (hq : 0<q)
    (b : Fin q) (σ : Equiv.Perm (Fin (3*q))) :
    wild_joint_first_block q
      ((wild_joint_position_relabel q (Equiv.swap ⟨0,hq⟩ b)).trans σ) =
      wild_joint_block_set q σ b := by
  rw [← wild_joint_block_set_zero q hq]
  ext v
  rw [wild_joint_block_set_mem,wild_joint_block_set_mem,wild_joint_position_relabel_block]
  rw [Equiv.symm_apply_eq]
  simp

theorem wild_joint_first_block_mixed_reduction
    (q : ℕ) (hq : 3 ≤ q)
    (A : Fin (3*q) → Fin (3*q) → Fin (3*q))
    (hid : ∀ x, A x x = x) (hsym : ∀ x y, A x y = A y x)
    (hinj : ∀ x, Function.Injective (A x)) :
    (∑ σ : Equiv.Perm (Fin (3*q)),
      (wild_joint_invalid_count q A σ : ℝ) * (wild_joint_bad_color_count q A σ : ℝ)) =
    (q : ℝ) * ∑ σ : Equiv.Perm (Fin (3*q)),
      (wild_joint_multiplicity q A (wild_joint_first_block q σ) : ℝ) *
        (wild_joint_bad_color_count q A σ : ℝ) := by
  classical
  have hb (b : Fin q) :
      (∑ σ : Equiv.Perm (Fin (3*q)),
        (wild_joint_multiplicity q A (wild_joint_block_set q σ b) : ℝ)*
          (wild_joint_bad_color_count q A σ : ℝ)) =
      ∑ σ : Equiv.Perm (Fin (3*q)),
        (wild_joint_multiplicity q A (wild_joint_first_block q σ) : ℝ)*
          (wild_joint_bad_color_count q A σ : ℝ) := by
    let t := wild_joint_position_relabel q (Equiv.swap (⟨0,by omega⟩ : Fin q) b)
    let E : Equiv.Perm (Equiv.Perm (Fin (3*q))) :=
      { toFun := fun σ => t.trans σ
        invFun := fun σ => t.symm.trans σ
        left_inv := by intro σ; ext v; simp
        right_inv := by intro σ; ext v; simp }
    apply Fintype.sum_equiv E
    intro σ
    dsimp [E,t]
    rw [wild_joint_position_swap_first q (by omega),wild_joint_position_relabel_bad_count]
  simp_rw [wild_joint_invalid_count_eq_sum_multiplicity q A hid hsym hinj,Nat.cast_sum,sum_mul]
  rw [sum_comm]
  simp_rw [hb]
  simp
