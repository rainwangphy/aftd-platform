import AFTD.Prelude
import AFTD.Kb.Tcs.SignedCoordinateDist

/-!
# signed_coordinate_dist_self

Topic: information   Node: bd44a3caf5b5

Provenance: helper lemma. arXiv:2611.00868, Section 2, Eq. (10)

For every positive integer n, coordinate i : Fin n, and boolean value b, the dictator distance of the signed coordinate indicator x ↦ if x i = b then 1 else 0 is 0.
-/

/-- Sanity lemma: dictator distance of a signed coordinate indicator is zero. -/
lemma signed_coordinate_dist_self (n : ℕ) (hn : 0 < n) (i : Fin n) (b : Bool) :
    signed_coordinate_dist n (fun x ↦ if x i = b then 1 else 0) = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold signed_coordinate_dist
  have hterm : ∀ (i' : Fin n) (b' : Bool),
      0 ≤ (1 / (2 : ℝ) ^ n) *
        ∑ x : Fin n → Bool,
          if (if x i = b then (1:ℝ) else 0) ≠ (if x i' = b' then 1 else 0) then 1 else 0 := by
    intro i' b'
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    split_ifs <;> norm_num
  have hinner : (⨅ b' : Bool,
      (1 / (2 : ℝ) ^ n) *
        ∑ x : Fin n → Bool,
          if (if x i = b then (1:ℝ) else 0) ≠ (if x i = b' then 1 else 0) then 1 else 0) = 0 := by
    refine ciInf_eq_of_forall_ge_of_forall_gt_exists_lt (fun b' => hterm i b') ?_
    intro w hw
    exact ⟨b, by simp [hw]⟩
  refine ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_
  · intro i'
    exact le_ciInf (fun b' => hterm i' b')
  · intro w hw
    exact ⟨i, by rw [hinner]; exact hw⟩
