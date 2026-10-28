import AFTD.Prelude

/-!
# two_type_identical_valuations_all_allocations_pareto_optimal

Topic: fair_division   Node: 1ce6d0999788

Provenance: helper lemma. arXiv:2610.19099

In a two-type goods fair division instance, if all agents have identical per-item valuations, then every complete count allocation is Pareto optimal.
-/

lemma two_type_identical_valuations_all_allocations_pareto_optimal_sum_val
    (n a b : ℕ) (p q : Fin n → ℝ) (x y : Fin n → ℕ)
    (hx : ∑ i, x i = a) (hy : ∑ i, y i = b)
    (hp_eq : ∀ i j, p i = p j) (hq_eq : ∀ i j, q i = q j) (i₀ : Fin n) :
    ∑ i, (p i * (x i : ℝ) + q i * (y i : ℝ)) = p i₀ * (a : ℝ) + q i₀ * (b : ℝ) := by
  open Finset in
  have hx_real : ∑ i, (x i : ℝ) = (a : ℝ) := by
    have : ((∑ i, x i : ℕ) : ℝ) = (a : ℝ) := by rw [hx]
    push_cast at this
    exact this
  have hy_real : ∑ i, (y i : ℝ) = (b : ℝ) := by
    have : ((∑ i, y i : ℕ) : ℝ) = (b : ℝ) := by rw [hy]
    push_cast at this
    exact this
  have h1 : (∑ i, (p i * (x i : ℝ) + q i * (y i : ℝ))) =
            ∑ i, (p i₀ * (x i : ℝ) + q i₀ * (y i : ℝ)) := by
    apply sum_congr rfl
    intro i _
    rw [hp_eq i i₀, hq_eq i i₀]
  rw [h1, sum_add_distrib, ← mul_sum, ← mul_sum, hx_real, hy_real]

/-- When all agents have identical valuations, every complete allocation of two types of goods is Pareto optimal. -/
theorem two_type_identical_valuations_all_allocations_pareto_optimal
    (n a b : ℕ) (p q : Fin n → ℝ) (x y : Fin n → ℕ)
    (hx : ∑ i, x i = a) (hy : ∑ i, y i = b)
    (hp_eq : ∀ i j, p i = p j) (hq_eq : ∀ i j, q i = q j) :
    ¬ ∃ x' y' : Fin n → ℕ, (∑ i, x' i = a) ∧ (∑ i, y' i = b) ∧
      (∀ i : Fin n, p i * (x i : ℝ) + q i * (y i : ℝ) ≤ p i * (x' i : ℝ) + q i * (y' i : ℝ)) ∧
      (∃ i : Fin n, p i * (x i : ℝ) + q i * (y i : ℝ) < p i * (x' i : ℝ) + q i * (y' i : ℝ)) := by
  open Finset in
  rintro ⟨x', y', hx', hy', hle, i₀, hlt⟩
  have sum_eq := two_type_identical_valuations_all_allocations_pareto_optimal_sum_val n a b p q x y hx hy hp_eq hq_eq i₀
  have sum_eq' := two_type_identical_valuations_all_allocations_pareto_optimal_sum_val n a b p q x' y' hx' hy' hp_eq hq_eq i₀
  have h_sum_lt : ∑ i, (p i * (x i : ℝ) + q i * (y i : ℝ)) <
                  ∑ i, (p i * (x' i : ℝ) + q i * (y' i : ℝ)) := by
    apply sum_lt_sum
    · intro i _
      exact hle i
    · exact ⟨i₀, mem_univ i₀, hlt⟩
  rw [sum_eq, sum_eq'] at h_sum_lt
  exact lt_irrefl _ h_sum_lt
