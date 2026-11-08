import AFTD.Prelude
import AFTD.Kb.Optimization.PopulationCapacity
import AFTD.Kb.Optimization.ThermallyReachableSubsetBasePolytope
import AFTD.Kb.Optimization.BlockPopulationCapacity
import AFTD.Kb.Optimization.FiberSumVec
import AFTD.Kb.Optimization.SubmodularBasePolytope
import AFTD.Kb.Optimization.ThermallyReachableMicro
import AFTD.Kb.Optimization.IsGibbsStochastic
import AFTD.Kb.Optimization.ThermallyReachableBlockPopulations

/-!
# target_population_le_capacity

Topic: submodular   Node: 96da5b43b09c

Provenance: helper lemma. arXiv:2610.35433, Eq. (6)

For any natural number n, target population vector y in stdSimplex ℝ (Fin n), Gibbs vector γ in stdSimplex ℝ (Fin n) with strictly positive entries (∀ i, 0 < γ i), and subset S : Finset (Fin n), the sum ∑ i ∈ S, y i is at most population_capacity γ y S.
-/

lemma target_population_le_capacity_mem_reachable {n : ℕ} {y γ : Fin n → ℝ} (hy : y ∈ stdSimplex ℝ (Fin n)) :
    y ∈ thermally_reachable_block_populations id γ y := by
  refine ⟨y, hy, ⟨fun i j => if i = j then 1 else 0, ?_, ?_⟩, ?_⟩
  · refine ⟨fun i j => ?_, fun j => ?_, fun i => ?_⟩
    · dsimp only
      split_ifs <;> linarith
    · dsimp only
      simp
    · dsimp only
      simp
  · intro i
    dsimp only
    simp
  · ext k
    dsimp [fiber_sum_vec]
    have : (Finset.univ.filter (fun i : Fin n => i = k)) = {k} := by
      ext i
      simp
    rw [this]
    simp

/-- A target state population on any subset is at most its own population capacity. -/
theorem target_population_le_capacity {n : ℕ}
    {y γ : Fin n → ℝ} (hy : y ∈ stdSimplex ℝ (Fin n)) (hγ : γ ∈ stdSimplex ℝ (Fin n))
    (hγ_pos : ∀ i, 0 < γ i) (S : Finset (Fin n)) :
    (∑ i ∈ S, y i) ≤ population_capacity γ y S := by
  have _ := hγ
  have _ := hγ_pos
  have hy_reach : y ∈ thermally_reachable_block_populations id γ y :=
    target_population_le_capacity_mem_reachable hy
  have h_sub := thermally_reachable_subset_base_polytope id Function.surjective_id γ y hy_reach
  exact h_sub.1 S
