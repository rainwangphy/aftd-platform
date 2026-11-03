import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoTypeChoresHaveAlphaPmmsFpo
import AFTD.Kb.GameTheoryEconomics.IsTwoTypeAllocation
import AFTD.Kb.GameTheoryEconomics.IsAlphaPmmsTwoTypeChores
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimalTwoTypeChores

/-!
# two_chore_types_exact_pmms_fpo_incompatible

Topic: fair_division   Node: 2686f3d4456a

Provenance: helper lemma. OP-886; experiment 12769

Exact pairwise maximin share fairness and fractional Pareto optimality are incompatible for two chore types: the property two_type_chores_have_alpha_pmms_fpo 1 is false.
-/

def two_chore_types_exact_pmms_fpo_incompatible_p : Fin 3 → ℝ := fun _ => 1
def two_chore_types_exact_pmms_fpo_incompatible_q : Fin 3 → ℝ := ![4, 3, 3]

theorem two_chore_types_exact_pmms_fpo_incompatible_no_pmms_if_y0_zero (x y : Fin 3 → ℕ)
    (hx : ∑ i, x i = 2) (hy : ∑ i, y i = 3)
    (hy0 : y 0 = 0)
    (hpmms : is_alpha_pmms_two_type_chores 1 two_chore_types_exact_pmms_fpo_incompatible_p two_chore_types_exact_pmms_fpo_incompatible_q x y) : False := by
  have hysum : y 1 + y 2 = 3 := by
    have h := hy
    rw [Fin.sum_univ_three] at h
    omega
  have hxsum : x 0 + x 1 + x 2 = 2 := by
    have h := hx
    rw [Fin.sum_univ_three] at h
    exact h
  have hy_ge : y 1 ≥ 2 ∨ y 2 ≥ 2 := by omega
  rcases hy_ge with hy1 | hy2
  · have hij : (1 : Fin 3) ≠ 0 := by decide
    have hs : 0 ≤ x 1 + x 0 := by omega
    have ht : 1 ≤ y 1 + y 0 := by omega
    have hbound := hpmms 1 0 hij 0 1 hs ht
    dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q] at hbound
    have : y 1 + y 0 - 1 = y 1 - 1 := by omega
    rw [this] at hbound
    push_cast at hbound
    have hy1_r : (2 : ℝ) ≤ (y 1 : ℝ) := by exact_mod_cast hy1
    have hx0_r : (x 0 : ℝ) ≤ 2 := by
      have : x 0 ≤ 2 := by omega
      exact_mod_cast this
    have hx1_pos : (0 : ℝ) ≤ (x 1 : ℝ) := by positivity
    have h_sub : ((y 1 - 1 : ℕ) : ℝ) = (y 1 : ℝ) - 1 := by
      have : ((y 1 - 1 : ℕ) : ℝ) + 1 = (y 1 : ℝ) := by
        have : y 1 - 1 + 1 = y 1 := Nat.sub_add_cancel (by omega)
        exact_mod_cast this
      linarith
    rw [h_sub] at hbound
    push_cast at *
    have hle : 1 * (0 : ℝ) + 3 * 1 < 1 * (x 1 : ℝ) + 3 * (y 1 : ℝ) := by linarith
    have hle2 : 1 * ((x 1 : ℝ) + (x 0 : ℝ)) + 3 * ((y 1 : ℝ) - 1) < 1 * (x 1 : ℝ) + 3 * (y 1 : ℝ) := by linarith
    have hmax : max (1 * (0 : ℝ) + 3 * 1) (1 * ((x 1 : ℝ) + (x 0 : ℝ)) + 3 * ((y 1 : ℝ) - 1)) < 1 * (x 1 : ℝ) + 3 * (y 1 : ℝ) := max_lt hle hle2
    have : 1 * max (1 * (0 : ℝ) + 3 * (1 : ℝ)) (1 * ((x 1 : ℝ) + (x 0 : ℝ)) + 3 * ((y 1 : ℝ) - 1)) =
      max (1 * (0 : ℝ) + 3 * (1 : ℝ)) (1 * ((x 1 : ℝ) + (x 0 : ℝ)) + 3 * ((y 1 : ℝ) - 1)) := by ring
    linarith
  · have hij : (2 : Fin 3) ≠ 0 := by decide
    have hs : 0 ≤ x 2 + x 0 := by omega
    have ht : 1 ≤ y 2 + y 0 := by omega
    have hbound := hpmms 2 0 hij 0 1 hs ht
    dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q] at hbound
    have : y 2 + y 0 - 1 = y 2 - 1 := by omega
    rw [this] at hbound
    push_cast at hbound
    have hy2_r : (2 : ℝ) ≤ (y 2 : ℝ) := by exact_mod_cast hy2
    have hx0_r : (x 0 : ℝ) ≤ 2 := by
      have : x 0 ≤ 2 := by omega
      exact_mod_cast this
    have hx2_pos : (0 : ℝ) ≤ (x 2 : ℝ) := by positivity
    have h_sub : ((y 2 - 1 : ℕ) : ℝ) = (y 2 : ℝ) - 1 := by
      have : ((y 2 - 1 : ℕ) : ℝ) + 1 = (y 2 : ℝ) := by
        have : y 2 - 1 + 1 = y 2 := Nat.sub_add_cancel (by omega)
        exact_mod_cast this
      linarith
    rw [h_sub] at hbound
    push_cast at *
    have hle : 1 * (0 : ℝ) + 3 * 1 < 1 * (x 2 : ℝ) + 3 * (y 2 : ℝ) := by linarith
    have hle2 : 1 * ((x 2 : ℝ) + (x 0 : ℝ)) + 3 * ((y 2 : ℝ) - 1) < 1 * (x 2 : ℝ) + 3 * (y 2 : ℝ) := by linarith
    have hmax : max (1 * (0 : ℝ) + 3 * 1) (1 * ((x 2 : ℝ) + (x 0 : ℝ)) + 3 * ((y 2 : ℝ) - 1)) < 1 * (x 2 : ℝ) + 3 * (y 2 : ℝ) := max_lt hle hle2
    have : 1 * max (1 * (0 : ℝ) + 3 * (1 : ℝ)) (1 * ((x 2 : ℝ) + (x 0 : ℝ)) + 3 * ((y 2 : ℝ) - 1)) =
      max (1 * (0 : ℝ) + 3 * (1 : ℝ)) (1 * ((x 2 : ℝ) + (x 0 : ℝ)) + 3 * ((y 2 : ℝ) - 1)) := by ring
    linarith

theorem two_chore_types_exact_pmms_fpo_incompatible_no_pmms_if_x0_two (x y : Fin 3 → ℕ)
    (hx : x 0 = 2 ∧ x 1 = 0 ∧ x 2 = 0)
    (hy : ∑ i, y i = 3)
    (hy0 : y 0 ≥ 1)
    (hpmms : is_alpha_pmms_two_type_chores 1 two_chore_types_exact_pmms_fpo_incompatible_p two_chore_types_exact_pmms_fpo_incompatible_q x y) : False := by
  have hysum : y 0 + y 1 + y 2 = 3 := by
    have h := hy
    rw [Fin.sum_univ_three] at h
    exact h
  have hy_le : y 1 ≤ 1 ∨ y 2 ≤ 1 := by omega
  have hx0_r : (x 0 : ℝ) = 2 := by exact_mod_cast hx.1
  have hy0_r : (1 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hy0
  rcases hy_le with hy1 | hy2
  · have hij : (0 : Fin 3) ≠ 1 := by decide
    have hs : 1 ≤ x 0 + x 1 := by omega
    have ht : 1 ≤ y 0 + y 1 := by omega
    have hbound := hpmms 0 1 hij 1 1 hs ht
    dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q] at hbound
    have : x 0 + x 1 - 1 = 1 := by omega
    have : y 0 + y 1 - 1 = y 0 + y 1 - 1 := rfl
    rw [‹x 0 + x 1 - 1 = 1›] at hbound
    push_cast at hbound
    have h_sub : ((y 0 + y 1 - 1 : ℕ) : ℝ) = (y 0 : ℝ) + (y 1 : ℝ) - 1 := by
      have : ((y 0 + y 1 - 1 : ℕ) : ℝ) + 1 = (y 0 : ℝ) + (y 1 : ℝ) := by
        have : y 0 + y 1 - 1 + 1 = y 0 + y 1 := Nat.sub_add_cancel (by omega)
        exact_mod_cast this
      linarith
    rw [h_sub] at hbound
    push_cast at *
    have hy1_r : (y 1 : ℝ) ≤ 1 := by exact_mod_cast hy1
    have hle : 1 * (1 : ℝ) + 4 * 1 < 1 * (x 0 : ℝ) + 4 * (y 0 : ℝ) := by linarith
    have hle2 : 1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 1 : ℝ) - 1) < 1 * (x 0 : ℝ) + 4 * (y 0 : ℝ) := by linarith
    have hmax : max (1 * (1 : ℝ) + 4 * 1) (1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 1 : ℝ) - 1)) < 1 * (x 0 : ℝ) + 4 * (y 0 : ℝ) := max_lt hle hle2
    have : 1 * max (1 * (1 : ℝ) + 4 * 1) (1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 1 : ℝ) - 1)) =
      max (1 * (1 : ℝ) + 4 * 1) (1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 1 : ℝ) - 1)) := by ring
    linarith
  · have hij : (0 : Fin 3) ≠ 2 := by decide
    have hs : 1 ≤ x 0 + x 2 := by omega
    have ht : 1 ≤ y 0 + y 2 := by omega
    have hbound := hpmms 0 2 hij 1 1 hs ht
    dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q] at hbound
    have : x 0 + x 2 - 1 = 1 := by omega
    have : y 0 + y 2 - 1 = y 0 + y 2 - 1 := rfl
    rw [‹x 0 + x 2 - 1 = 1›] at hbound
    push_cast at hbound
    have h_sub : ((y 0 + y 2 - 1 : ℕ) : ℝ) = (y 0 : ℝ) + (y 2 : ℝ) - 1 := by
      have : ((y 0 + y 2 - 1 : ℕ) : ℝ) + 1 = (y 0 : ℝ) + (y 2 : ℝ) := by
        have : y 0 + y 2 - 1 + 1 = y 0 + y 2 := Nat.sub_add_cancel (by omega)
        exact_mod_cast this
      linarith
    rw [h_sub] at hbound
    push_cast at *
    have hy2_r : (y 2 : ℝ) ≤ 1 := by exact_mod_cast hy2
    have hle : 1 * (1 : ℝ) + 4 * 1 < 1 * (x 0 : ℝ) + 4 * (y 0 : ℝ) := by linarith
    have hle2 : 1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 2 : ℝ) - 1) < 1 * (x 0 : ℝ) + 4 * (y 0 : ℝ) := by linarith
    have hmax : max (1 * (1 : ℝ) + 4 * 1) (1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 2 : ℝ) - 1)) < 1 * (x 0 : ℝ) + 4 * (y 0 : ℝ) := max_lt hle hle2
    have : 1 * max (1 * (1 : ℝ) + 4 * 1) (1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 2 : ℝ) - 1)) =
      max (1 * (1 : ℝ) + 4 * 1) (1 * (1 : ℝ) + 4 * ((y 0 : ℝ) + (y 2 : ℝ) - 1)) := by ring
    linarith

theorem two_chore_types_exact_pmms_fpo_incompatible_not_fpo_if_y0_x1 (x y : Fin 3 → ℕ)
    (hy0 : y 0 ≥ 1) (hx1 : x 1 ≥ 1)
    (hfpo : is_fractionally_pareto_optimal_two_type_chores two_chore_types_exact_pmms_fpo_incompatible_p two_chore_types_exact_pmms_fpo_incompatible_q x y) : False := by
  apply hfpo
  refine ⟨![ (x 0 : ℝ) + 7/8, (x 1 : ℝ) - 7/8, (x 2 : ℝ) ],
          ![ (y 0 : ℝ) - 1/4, (y 1 : ℝ) + 1/4, (y 2 : ℝ) ], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · dsimp; positivity
    · dsimp
      have : (1 : ℝ) ≤ (x 1 : ℝ) := by exact_mod_cast hx1
      linarith
    · dsimp; positivity
  · intro i
    fin_cases i
    · dsimp
      have : (1 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hy0
      linarith
    · dsimp; positivity
    · dsimp; positivity
  · simp [Fin.sum_univ_three]
  · simp [Fin.sum_univ_three]
  · intro i
    fin_cases i
    · dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
      linarith
    · dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
      linarith
    · dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
      linarith
  · refine ⟨0, ?_⟩
    dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
    linarith

theorem two_chore_types_exact_pmms_fpo_incompatible_not_fpo_if_y0_x2 (x y : Fin 3 → ℕ)
    (hy0 : y 0 ≥ 1) (hx2 : x 2 ≥ 1)
    (hfpo : is_fractionally_pareto_optimal_two_type_chores two_chore_types_exact_pmms_fpo_incompatible_p two_chore_types_exact_pmms_fpo_incompatible_q x y) : False := by
  apply hfpo
  refine ⟨![ (x 0 : ℝ) + 7/8, (x 1 : ℝ), (x 2 : ℝ) - 7/8 ],
          ![ (y 0 : ℝ) - 1/4, (y 1 : ℝ), (y 2 : ℝ) + 1/4 ], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · dsimp; positivity
    · dsimp; positivity
    · dsimp
      have : (1 : ℝ) ≤ (x 2 : ℝ) := by exact_mod_cast hx2
      linarith
  · intro i
    fin_cases i
    · dsimp
      have : (1 : ℝ) ≤ (y 0 : ℝ) := by exact_mod_cast hy0
      linarith
    · dsimp; positivity
    · dsimp; positivity
  · simp [Fin.sum_univ_three]; ring
  · simp [Fin.sum_univ_three]; ring
  · intro i
    fin_cases i
    · dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
      linarith
    · dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
      linarith
    · dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
      linarith
  · refine ⟨0, ?_⟩
    dsimp [two_chore_types_exact_pmms_fpo_incompatible_p, two_chore_types_exact_pmms_fpo_incompatible_q]
    linarith

/-- Exact PMMS and fractional Pareto optimality are incompatible for two chore types. -/
theorem two_chore_types_exact_pmms_fpo_incompatible :
    ¬ two_type_chores_have_alpha_pmms_fpo 1 := by
  intro h
  have hp_pos : ∀ i : Fin 3, 0 < two_chore_types_exact_pmms_fpo_incompatible_p i := by
    intro i
    dsimp [two_chore_types_exact_pmms_fpo_incompatible_p]
    norm_num
  have hq_pos : ∀ i : Fin 3, 0 < two_chore_types_exact_pmms_fpo_incompatible_q i := by
    intro i
    fin_cases i <;> { dsimp [two_chore_types_exact_pmms_fpo_incompatible_q]; norm_num }
  rcases h 3 (by omega) 2 3 two_chore_types_exact_pmms_fpo_incompatible_p two_chore_types_exact_pmms_fpo_incompatible_q hp_pos hq_pos with ⟨x, y, ⟨hx, hy⟩, hfpo, hpmms⟩
  have hxsum : x 0 + x 1 + x 2 = 2 := by
    have h := hx
    rw [Fin.sum_univ_three] at h
    exact h
  have hy0_cases : y 0 = 0 ∨ y 0 ≥ 1 := by omega
  rcases hy0_cases with hy0 | hy0
  · exact two_chore_types_exact_pmms_fpo_incompatible_no_pmms_if_y0_zero x y hx hy hy0 hpmms
  · have hx_cases : (x 0 = 2 ∧ x 1 = 0 ∧ x 2 = 0) ∨ x 1 ≥ 1 ∨ x 2 ≥ 1 := by omega
    rcases hx_cases with hx2 | hx1 | hx2
    · exact two_chore_types_exact_pmms_fpo_incompatible_no_pmms_if_x0_two x y hx2 hy hy0 hpmms
    · exact two_chore_types_exact_pmms_fpo_incompatible_not_fpo_if_y0_x1 x y hy0 hx1 hfpo
    · exact two_chore_types_exact_pmms_fpo_incompatible_not_fpo_if_y0_x2 x y hy0 hx2 hfpo
