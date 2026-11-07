import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanTopForm

/-!
# boolean_top_form_eq_zero_of_not_injective

Topic: combinatorics   Node: 1eda8f11ecdf

Provenance: formalization of a published result. Source: arXiv:2611.03452 Lemma 2.7 (iii) -- Parity Decision Trees of Depth O(4^d log ||f_hat||_1) for Boolean Functions f of F_2-Degree d

For any natural number d, module V over ZMod 2, function p : V → ZMod 2, and tuple h : Fin d → V that is not injective (¬ Function.Injective h), booleanTopForm d p h = 0.
-/

open scoped BigOperators symmDiff

/-- In a module over `ZMod 2`, every element is its own negative. -/
private lemma boolean_top_form_eq_zero_of_not_injective_add_self {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (x : V) : x + x = 0 := by
  have h : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 x, h, zero_smul]

/-- Toggling a single element `a` changes the sum of `v` over a finset by `v a`. -/
private lemma boolean_top_form_eq_zero_of_not_injective_symmDiff_singleton {d : ℕ} {V : Type*}
    [AddCommGroup V] (v : Fin d → V) (hv : ∀ k, v k + v k = 0) (a : Fin d)
    (T : Finset (Fin d)) :
    ∑ k ∈ T ∆ ({a} : Finset (Fin d)), v k = ∑ k ∈ T, v k + v a := by
  by_cases ha : a ∈ T
  · have hset : T ∆ ({a} : Finset (Fin d)) = T.erase a := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      by_cases hx : x = a
      · subst hx; simp [ha]
      · simp [hx]
    rw [hset, Finset.sum_erase_eq_sub ha, sub_eq_add_neg,
      neg_eq_of_add_eq_zero_right (hv a)]
  · have hset : T ∆ ({a} : Finset (Fin d)) = insert a T := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      by_cases hx : x = a
      · subst hx; simp [ha]
      · simp [hx]
    rw [hset, Finset.sum_insert ha, add_comm]

/-- If `v i = v j` with `i ≠ j` and all values are self-inverse, then summing over `S ∆ {i,j}`
gives the same result as summing over `S`. -/
private lemma boolean_top_form_eq_zero_of_not_injective_symmDiff_pair {d : ℕ} {V : Type*}
    [AddCommGroup V] (v : Fin d → V) (hv : ∀ k, v k + v k = 0) {i j : Fin d}
    (hij : i ≠ j) (hveq : v i = v j) (S : Finset (Fin d)) :
    ∑ k ∈ S ∆ ({i, j} : Finset (Fin d)), v k = ∑ k ∈ S, v k := by
  have hset : S ∆ ({i, j} : Finset (Fin d)) = (S ∆ ({i} : Finset (Fin d))) ∆ {j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;> simp_all
  rw [hset, boolean_top_form_eq_zero_of_not_injective_symmDiff_singleton v hv j,
    boolean_top_form_eq_zero_of_not_injective_symmDiff_singleton v hv i, add_assoc]
  have hzero : v i + v j = 0 := by
    rw [← hveq]
    exact hv i
  rw [hzero, add_zero]

/-- The top form vanishes on any tuple with repeated vectors. -/
theorem boolean_top_form_eq_zero_of_not_injective {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (p : V → ZMod 2) (h : Fin d → V) (hinj : ¬ Function.Injective h) :
    booleanTopForm d p h = 0 := by
  obtain ⟨i, j, hveq, hij⟩ := Function.not_injective_iff.mp hinj
  unfold booleanTopForm
  refine Finset.sum_involution (s := Finset.univ)
    (f := fun S => p (∑ k ∈ S, h k)) (g := fun S _ => S ∆ ({i, j} : Finset (Fin d))) ?_ ?_ ?_ ?_
  · intro S _
    rw [boolean_top_form_eq_zero_of_not_injective_symmDiff_pair h
      (fun k => boolean_top_form_eq_zero_of_not_injective_add_self (h k)) hij hveq S]
    exact boolean_top_form_eq_zero_of_not_injective_add_self _
  · intro S _ _
    have key : (i ∈ (S ∆ ({i, j} : Finset (Fin d)))) ↔ ¬ (i ∈ S) := by
      simp [Finset.mem_symmDiff]
    intro hEq
    rw [hEq] at key
    tauto
  · intro S _
    exact Finset.mem_univ _
  · intro S _
    exact symmDiff_symmDiff_cancel_right ({i, j} : Finset (Fin d)) S
