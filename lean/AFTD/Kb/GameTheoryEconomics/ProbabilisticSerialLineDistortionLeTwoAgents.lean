import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCostLe
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignmentTwoSame
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignmentTwoSameOne
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignmentTwoSplit
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignmentTwoSplitSwap
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment

/-!
# probabilistic_serial_line_distortion_le_two_agents

Topic: social_choice   Node: 8d7f8b30ac3e

Provenance: original. Related work: OP-1158, case n = 2; arXiv:2611.05777 bounds probabilistic serial on general metrics, not this line case

Case n = 2 of OP-1158: for two agents at real positions a_0, a_1 and two items at real positions b_0, b_1, with each agent ranking the items by distance (ties broken arbitrarily), the cost of the probabilistic serial assignment, sum_ij X_ij |a_i - b_j|, is at most 2 times the minimum perfect-matching cost.
-/

theorem probabilistic_serial_line_distortion_le_two_agents (a b : Fin 2 → ℝ)
    (pref : Fin 2 → Equiv.Perm (Fin 2)) (h : is_line_distance_preference_profile a b pref) :
    probabilistic_serial_line_cost a b pref ≤ 2 * line_min_matching_cost a b := by
  have tri : ∀ x y u v : ℝ, |x - v| ≤ |x - u| + |y - u| + |y - v| := by
    intro x y u v
    have h1 := abs_sub_le x u v
    have h2 := abs_sub_le u y v
    have h3 : |u - y| = |y - u| := abs_sub_comm u y
    linarith
  have t1 := tri (a 0) (a 1) (b 0) (b 1)
  have t2 := tri (a 0) (a 1) (b 1) (b 0)
  have t3 := tri (a 1) (a 0) (b 0) (b 1)
  have t4 := tri (a 1) (a 0) (b 1) (b 0)
  have n1 := abs_nonneg (a 0 - b 0)
  have n2 := abs_nonneg (a 0 - b 1)
  have n3 := abs_nonneg (a 1 - b 0)
  have n4 := abs_nonneg (a 1 - b 1)
  have hp : ∀ π : Equiv.Perm (Fin 2), π = 1 ∨ π = Equiv.swap 0 1 := by decide
  obtain ⟨σ0, -, hσ0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Equiv.Perm (Fin 2)))
    (fun σ : Equiv.Perm (Fin 2) => ∑ i, |a i - b (σ i)|)
  have hopt : line_min_matching_cost a b = ∑ i, |a i - b (σ0 i)| := hσ0
  have m1 := line_min_matching_cost_le a b 1
  have m2 := line_min_matching_cost_le a b (Equiv.swap 0 1)
  simp only [Fin.sum_univ_two, Equiv.Perm.coe_one, id, Equiv.swap_apply_left,
    Equiv.swap_apply_right] at m1 m2
  have h0 := h 0 0 1 (by decide)
  have h1 := h 1 0 1 (by decide)
  have q0 : pref 0 1 ≠ pref 0 0 := fun e => by have := (pref 0).injective e; simp at this
  have q1 : pref 1 1 ≠ pref 1 0 := fun e => by have := (pref 1).injective e; simp at this
  unfold probabilistic_serial_line_cost
  simp only [Fin.sum_univ_two]
  rcases hp σ0 with rfl | rfl <;>
  simp only [Fin.sum_univ_two, Equiv.Perm.coe_one, id, Equiv.swap_apply_left,
    Equiv.swap_apply_right] at hopt <;>
  rw [hopt] <;>
  rcases (by omega : pref 0 0 = 0 ∨ pref 0 0 = 1) with e0 | e0 <;>
  rcases (by omega : pref 1 0 = 0 ∨ pref 1 0 = 1) with e1 | e1 <;>
  [ (have f0 : pref 0 1 = 1 := by omega
     have f1 : pref 1 1 = 1 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_same pref e0 e1] at *);
    (have f0 : pref 0 1 = 1 := by omega
     have f1 : pref 1 1 = 0 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_split pref e0 e1] at *);
    (have f0 : pref 0 1 = 0 := by omega
     have f1 : pref 1 1 = 1 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_split_swap pref e0 e1] at *);
    (have f0 : pref 0 1 = 0 := by omega
     have f1 : pref 1 1 = 0 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_same_one pref e0 e1] at *);
    (have f0 : pref 0 1 = 1 := by omega
     have f1 : pref 1 1 = 1 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_same pref e0 e1] at *);
    (have f0 : pref 0 1 = 1 := by omega
     have f1 : pref 1 1 = 0 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_split pref e0 e1] at *);
    (have f0 : pref 0 1 = 0 := by omega
     have f1 : pref 1 1 = 1 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_split_swap pref e0 e1] at *);
    (have f0 : pref 0 1 = 0 := by omega
     have f1 : pref 1 1 = 0 := by omega
     simp only [probabilistic_serial_fractional_assignment_two_same_one pref e0 e1] at *)] <;>
  rw [e0, f0] at h0 <;> rw [e1, f1] at h1 <;> norm_num at h0 h1 ⊢ <;> linarith
