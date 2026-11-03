import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimalTwoTypeChores

/-!
# single_chore_type_b_zero_is_fpo

Topic: fair_division   Node: c04e47dacafb

Provenance: helper lemma. folklore; OP-886

For n agents with strictly positive chore costs p : Fin n → ℝ and arbitrary costs q : Fin n → ℝ, any integer allocation x, y : Fin n → ℕ in which every agent receives zero type-B chores (y i = 0 for all i : Fin n) is fractionally Pareto optimal.
-/

/-- When all type-B chore counts are zero, every allocation is fractionally Pareto optimal. -/
theorem single_chore_type_b_zero_is_fpo {n : ℕ} (p q : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (x y : Fin n → ℕ) (hy : ∀ i, y i = 0) :
    is_fractionally_pareto_optimal_two_type_chores p q x y := by
  intro h
  rcases h with ⟨f, g, hf, hg, hsumf, hsumg, hle, hstrict⟩
  rcases hstrict with ⟨k, hk⟩
  have hsumg' : ∑ i, g i = 0 := by
    simpa [hy] using hsumg
  have hg_all : ∀ i, g i = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (f := g)
      (fun i _ => hg i)).mp hsumg'
    simpa using this
  have hf_all_le : ∀ i, f i ≤ (x i : ℝ) := by
    intro i
    have hi : p i * f i ≤ p i * (x i : ℝ) := by
      simpa [hg_all i, hy i] using hle i
    exact le_of_mul_le_mul_left hi (hp i)
  have hlt_k : p k * f k < p k * (x k : ℝ) := by
    simpa [hg_all k, hy k] using hk
  have hf_k_lt : f k < (x k : ℝ) :=
    lt_of_mul_lt_mul_left hlt_k (le_of_lt (hp k))
  have hsum_lt : ∑ i, f i < ∑ i, (x i : ℝ) := by
    simpa using (Finset.sum_lt_sum (s := Finset.univ)
      (fun i _ => hf_all_le i) ⟨k, Finset.mem_univ k, hf_k_lt⟩)
  linarith
