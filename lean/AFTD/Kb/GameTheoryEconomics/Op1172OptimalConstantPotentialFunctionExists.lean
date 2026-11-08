import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DescentDriftField
import AFTD.Kb.GameTheoryEconomics.RepairDriftField

/-!
# op_1172_optimal_constant_potential_function_exists

Topic: equilibria   Node: 5030f78d9a9c

Provenance: formalization of a published result. Source: arXiv:2611.06076 after Theorem 5.8

There exist an activation budget f ∈ (0, 1), descent parameters η > 0 and G₀ ≥ 1, a constant σ_star ∈ (1, 2) satisfying σ_star³ - 19 * σ_star² + 27 * σ_star + 1 = 0, a target satisfaction threshold σ > σ_star, a margin c > 0, memory bounds 0 < H_min < f, a satisfaction lower bound 0 < varsigma_min < σ, and a potential function Φ : ℝ × ℝ → ℝ of class C¹ on the open positive quadrant (0, ∞) × (0, ∞) such that for all points p in the closed rectangle [H_min, f] × [varsigma_min, σ], the Fréchet derivative of Φ at p evaluates to at least c on the descent drift field descent_drift_field η G₀ p and to at least c on the repair drift field repair_drift_field f p.
-/

def op_1172_optimal_constant_potential_function_exists_phi : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-ContinuousLinearMap.fst ℝ ℝ ℝ) - ContinuousLinearMap.snd ℝ ℝ ℝ

def op_1172_optimal_constant_potential_function_exists_poly (x : ℝ) : ℝ :=
  x^3 - 19 * x^2 + 27 * x + 1

lemma op_1172_optimal_constant_potential_function_exists_poly_cont :
    Continuous op_1172_optimal_constant_potential_function_exists_poly := by
  unfold op_1172_optimal_constant_potential_function_exists_poly
  continuity

/-- Existence of a continuously differentiable Lyapunov potential function certifying drift above sigma_star. -/
theorem op_1172_optimal_constant_potential_function_exists :
  ∃ (η G₀ f σ c : ℝ) (H_min varsigma_min : ℝ),
    0 < η ∧ 1 ≤ G₀ ∧ 0 < f ∧ f < 1 ∧
    0 < H_min ∧ H_min < f ∧ 0 < varsigma_min ∧ varsigma_min < σ ∧
    (∃ σ_star : ℝ, 1 < σ_star ∧ σ_star < 2 ∧ σ_star^3 - 19 * σ_star^2 + 27 * σ_star + 1 = 0 ∧ σ_star < σ) ∧
    0 < c ∧
    ∃ (Φ : ℝ × ℝ → ℝ),
      ContDiffOn ℝ 1 Φ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ∧
      ∀ p ∈ Set.Icc H_min f ×ˢ Set.Icc varsigma_min σ,
        c ≤ (fderiv ℝ Φ p) (descent_drift_field η G₀ p) ∧
        c ≤ (fderiv ℝ Φ p) (repair_drift_field f p) := by
  refine ⟨1, 3, 1/2, 3, 1/4, 1/4, 2, ?_⟩
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
          by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num, ?_⟩
  · have h12 : (1 : ℝ) ≤ 2 := by norm_num
    have hcont : ContinuousOn op_1172_optimal_constant_potential_function_exists_poly (Set.Icc 1 2) :=
      op_1172_optimal_constant_potential_function_exists_poly_cont.continuousOn
    have h_ivt := intermediate_value_Ioo' h12 hcont
    have h0 : (0 : ℝ) ∈ Set.Ioo (op_1172_optimal_constant_potential_function_exists_poly 2)
                               (op_1172_optimal_constant_potential_function_exists_poly 1) := by
      rw [Set.mem_Ioo]
      change (op_1172_optimal_constant_potential_function_exists_poly 2 < 0 ∧
              0 < op_1172_optimal_constant_potential_function_exists_poly 1)
      unfold op_1172_optimal_constant_potential_function_exists_poly
      constructor <;> norm_num
    have h_ex := h_ivt h0
    rw [Set.mem_image] at h_ex
    rcases h_ex with ⟨σ_star, hσ_mem, hσ_val⟩
    rw [Set.mem_Ioo] at hσ_mem
    refine ⟨σ_star, hσ_mem.1, hσ_mem.2, hσ_val, by linarith [hσ_mem.2]⟩
  · refine ⟨op_1172_optimal_constant_potential_function_exists_phi,
            op_1172_optimal_constant_potential_function_exists_phi.contDiff.contDiffOn, ?_⟩
    intro p hp
    rcases hp with ⟨h1, h2⟩
    rw [Set.mem_Icc] at h1 h2
    constructor
    · rw [op_1172_optimal_constant_potential_function_exists_phi.fderiv]
      change 1/4 ≤ - (descent_drift_field 1 3 p).1 - (descent_drift_field 1 3 p).2
      dsimp [descent_drift_field]
      linarith
    · rw [op_1172_optimal_constant_potential_function_exists_phi.fderiv]
      change 1/4 ≤ - (repair_drift_field (1/2) p).1 - (repair_drift_field (1/2) p).2
      dsimp [repair_drift_field]
      linarith
