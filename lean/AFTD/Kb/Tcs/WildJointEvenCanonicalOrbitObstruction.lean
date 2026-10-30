import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointAlpha
import AFTD.Kb.Tcs.WildJointCanonicalType
import AFTD.Kb.Tcs.WildJointBadRelation
import AFTD.Kb.Tcs.WildJointCanonicalMatching
import AFTD.Kb.Tcs.WildJointFirstBlock
import AFTD.Kb.Tcs.WildJointBlock

/-!
# wild_joint_even_canonical_orbit_obstruction

Topic: graphs   Node: a09df847dd07

Provenance: helper lemma. IN-382 / OP-306 campaign9. Refutes the AFTD agent helper wild_joint_alpha_type_well_defined as stated, not a published paper claim. Discovered by exact experiment9566; Lean proves the unequal probabilities using explicit connected/disconnected certificates without evaluating 12! permutations.

At q=4, the canonical triples {1,2,11} and {1,2,3} have the same declared type, but their conditional whole-bad matching probabilities are respectively 1 and strictly less than 1. Thus the helper asserting type invariance for all q>=3 is false; an odd-q hypothesis is essential. This does not refute the main conjecture or the parent mixed moment, which assumes odd q.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
def in382_good_perm : Equiv.Perm (Fin 12) where
  toFun := ![1,2,3,0,4,5,6,7,9,8,10,11]
  invFun := ![3,0,1,2,4,5,6,7,9,8,10,11]
  left_inv := by intro x; fin_cases x <;> decide
  right_inv := by intro x; fin_cases x <;> decide

def in382_bad_perm : Equiv.Perm (Fin 12) where
  toFun := ![1,2,11,0,3,4,5,6,7,8,9,10]
  invFun := ![3,0,1,4,5,6,7,8,9,10,11,2]
  left_inv := by intro x; fin_cases x <;> decide
  right_inv := by intro x; fin_cases x <;> decide

theorem in382_good_first : wild_joint_first_block 4 in382_good_perm = {1,2,3} := by
  classical
  ext x
  simp only [wild_joint_first_block, mem_filter, mem_univ, true_and]
  fin_cases x <;> norm_num [wild_joint_first_block,wild_joint_block,in382_good_perm, Fin.ext_iff]

theorem in382_bad_first : wild_joint_first_block 4 in382_bad_perm = {1,2,11} := by
  classical
  ext x
  simp only [wild_joint_first_block, mem_filter, mem_univ, true_and]
  fin_cases x <;> norm_num [wild_joint_first_block,wild_joint_block,in382_bad_perm, Fin.ext_iff]

theorem in382_good_connected :
    ¬wild_joint_bad_relation 4 (wild_joint_block 4 in382_good_perm)
      (wild_joint_canonical_matching 4) := by
  unfold wild_joint_bad_relation wild_joint_block wild_joint_canonical_matching
  decide +kernel

theorem in382_bad_closed : ∀ x ∈ ({1,2,11} : Finset (Fin 12)),
    ∀ y, wild_joint_canonical_matching 4 x y → y ∈ ({1,2,11} : Finset (Fin 12)) := by
  intro x hx y hxy
  simp only [mem_insert,mem_singleton] at hx
  rcases hx with rfl|rfl|rfl <;> fin_cases y <;>
    norm_num [wild_joint_canonical_matching, Fin.ext_iff] at *

theorem in382_bad_condition_implies_bad (σ : Equiv.Perm (Fin 12))
    (hσ : wild_joint_first_block 4 σ = {1,2,11}) :
    wild_joint_bad_relation 4 (wild_joint_block 4 σ) (wild_joint_canonical_matching 4) := by
  classical
  refine ⟨{0},by simp,by decide,?_⟩
  have hmem : ∀ x, wild_joint_block 4 σ x ∈ ({0} : Finset (Fin 4)) ↔
      x ∈ ({1,2,11} : Finset (Fin 12)) := by
    intro x
    rw [← hσ]
    simp only [mem_singleton, wild_joint_first_block, mem_filter, mem_univ, true_and]
    change (⟨(σ.symm x).val / 3, _⟩ : Fin 4) = 0 ↔ (σ.symm x).val < 3
    rw [Fin.ext_iff]
    simp only [Fin.val_zero, Nat.div_eq_zero_iff]
    norm_num []
  intro x y hxy
  rw [hmem, hmem]
  constructor
  · exact fun hx => in382_bad_closed x hx y hxy
  · intro hy
    apply in382_bad_closed y hy x
    simpa only [wild_joint_canonical_matching, ne_comm, min_comm, max_comm] using hxy

theorem wild_joint_even_canonical_orbit_obstruction :
    wild_joint_canonical_type 4 (by omega) {1,2,11} =
      wild_joint_canonical_type 4 (by omega) {1,2,3} ∧
    wild_joint_alpha 4 {1,2,11} = 1 ∧ wild_joint_alpha 4 {1,2,3} < 1 := by
  classical
  have hedge₁ : ∃ x ∈ ({1,2,11} : Finset (Fin 12)),
      ∃ y ∈ ({1,2,11} : Finset (Fin 12)), wild_joint_canonical_matching 4 x y :=
    ⟨1,by simp,2,by simp,by norm_num [wild_joint_canonical_matching,Fin.ext_iff]⟩
  have hedge₂ : ∃ x ∈ ({1,2,3} : Finset (Fin 12)),
      ∃ y ∈ ({1,2,3} : Finset (Fin 12)), wild_joint_canonical_matching 4 x y :=
    ⟨1,by simp,2,by simp,by norm_num [wild_joint_canonical_matching,Fin.ext_iff]⟩
  refine ⟨?_,?_,?_⟩
  · simp only [wild_joint_canonical_type, if_pos hedge₁, if_pos hedge₂]
    norm_num [Fin.ext_iff]
  · let D : Finset (Equiv.Perm (Fin 12)) := univ.filter fun σ =>
      wild_joint_first_block 4 σ = {1,2,11}
    have hpos : 0 < D.card := card_pos.mpr ⟨in382_bad_perm,
      mem_filter.mpr ⟨mem_univ _,in382_bad_first⟩⟩
    have heq : (univ.filter fun σ : Equiv.Perm (Fin 12) =>
        wild_joint_first_block 4 σ = {1,2,11} ∧
        wild_joint_bad_relation 4 (wild_joint_block 4 σ) (wild_joint_canonical_matching 4)) = D := by
      ext σ
      simp only [D,mem_filter,mem_univ,true_and]
      exact ⟨And.left,fun h => ⟨h,in382_bad_condition_implies_bad σ h⟩⟩
    unfold wild_joint_alpha
    rw [heq]
    change (D.card : ℝ) / (D.card : ℝ) = 1
    exact div_self (ne_of_gt (by exact_mod_cast hpos))
  · let D : Finset (Equiv.Perm (Fin 12)) := univ.filter fun σ =>
      wild_joint_first_block 4 σ = {1,2,3}
    let N : Finset (Equiv.Perm (Fin 12)) := univ.filter fun σ =>
      wild_joint_first_block 4 σ = {1,2,3} ∧
        wild_joint_bad_relation 4 (wild_joint_block 4 σ) (wild_joint_canonical_matching 4)
    have hD : in382_good_perm ∈ D := mem_filter.mpr ⟨mem_univ _,in382_good_first⟩
    have hN : in382_good_perm ∉ N := by
      intro h
      exact in382_good_connected (mem_filter.mp h).2.2
    have hsub : N ⊆ D := by intro σ h; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.1⟩
    have hlt : N.card < D.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro h; exact hN (h.symm ▸ hD)⟩)
    have hpos : (0 : ℝ) < D.card := by exact_mod_cast card_pos.mpr ⟨in382_good_perm,hD⟩
    change (N.card : ℝ) / (D.card : ℝ) < 1
    apply (div_lt_one hpos).mpr
    exact_mod_cast hlt
