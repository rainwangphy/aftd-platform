import AFTD.Prelude
import AFTD.Kb.Optimization.ThermallyReachableBlockPopulations
import AFTD.Kb.Optimization.BlockPopulationCapacity
import AFTD.Kb.Optimization.SubmodularBasePolytope
import AFTD.Kb.Optimization.FiberSumVec
import AFTD.Kb.Optimization.ThermallyReachableMicro

/-!
# thermally_reachable_subset_base_polytope

Topic: submodular   Node: 179485369df8

Provenance: helper lemma. arXiv:2610.35433:888

For any surjective block-assignment map proj : Fin n → Fin m and vectors γ, x : Fin n → ℝ, thermally_reachable_block_populations proj γ x is a subset of submodular_base_polytope (block_population_capacity proj γ x).
-/

/-- Every thermally reachable block population vector satisfies the capacity constraints and belongs to the base polytope. -/
theorem thermally_reachable_subset_base_polytope {n m : ℕ} (proj : Fin n → Fin m) (hsurj : Function.Surjective proj) (γ x : Fin n → ℝ) : thermally_reachable_block_populations proj γ x ⊆ submodular_base_polytope (block_population_capacity proj γ x) := by
  have _ := hsurj
  intro p hp
  rcases hp with ⟨x', hx'sim, hreach, rfl⟩
  constructor
  · intro S
    dsimp [block_population_capacity]
    apply le_csSup
    · use 1
      rintro y ⟨q, hq, rfl⟩
      rcases hq with ⟨x'', hx''sim, _, rfl⟩
      dsimp [fiber_sum_vec]
      have hp_nonneg : ∀ k, 0 ≤ ∑ i with proj i = k, x'' i :=
        fun k => Finset.sum_nonneg (fun i _ => hx''sim.1 i)
      have h_le_univ : ∑ k ∈ S, (∑ i with proj i = k, x'' i) ≤ ∑ k, (∑ i with proj i = k, x'' i) :=
        Finset.sum_le_univ_sum_of_nonneg (fun k => hp_nonneg k)
      rw [Finset.sum_fiberwise Finset.univ proj x'', hx''sim.2] at h_le_univ
      exact h_le_univ
    · exact Set.mem_image_of_mem _ ⟨x', hx'sim, hreach, rfl⟩
  · dsimp [fiber_sum_vec]
    rw [Finset.sum_fiberwise Finset.univ proj x', hx'sim.2]
