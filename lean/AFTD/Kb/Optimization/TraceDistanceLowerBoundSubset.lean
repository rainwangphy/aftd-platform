import AFTD.Prelude
import AFTD.Kb.Optimization.PopulationCapacity
import AFTD.Kb.Optimization.ThermallyReachablePopulations
import AFTD.Kb.Optimization.ThermallyReachableMicro
import AFTD.Kb.Optimization.ThermallyReachableBlockPopulations
import AFTD.Kb.Optimization.FiberSumVec

/-!
# trace_distance_lower_bound_subset

Topic: submodular   Node: 539e6d1613c4

Provenance: helper lemma. arXiv:2610.35433, Eq. (51)

For any natural number n, vectors x, y, γ : Fin n → ℝ with y in stdSimplex ℝ (Fin n), subset S : Finset (Fin n), and vector x' in thermally_reachable_populations γ x, the population deficit (∑ i ∈ S, y i) - population_capacity γ x S is at most (1 / 2 : ℝ) * ∑ i : Fin n, |x' i - y i|.
-/

/-- Every thermally reachable state has trace distance to y at least the capacity deficit y(S) - C_ρ(S). -/
theorem trace_distance_lower_bound_subset {n : ℕ}
    {x y γ : Fin n → ℝ} (hy : y ∈ stdSimplex ℝ (Fin n)) (S : Finset (Fin n))
    {x' : Fin n → ℝ} (hx' : x' ∈ thermally_reachable_populations γ x) :
    (∑ i ∈ S, y i) - population_capacity γ x S ≤ (1 / 2 : ℝ) * ∑ i : Fin n, |x' i - y i| := by
  -- Step 1: any reachable population vector lies in the simplex
  have hx'_sim : x' ∈ stdSimplex ℝ (Fin n) := by
    obtain ⟨z, hz, _, hxz⟩ := hx'
    have h : x' = z := by
      funext k
      rw [hxz]
      simp [fiber_sum_vec, Finset.sum_filter]
    rw [h]
    exact hz
  -- Step 2: the capacity is an upper bound for the reachable subset sums
  have hcap : ∑ i ∈ S, x' i ≤ population_capacity γ x S := by
    dsimp [population_capacity, block_population_capacity]
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro p ⟨q, hq, rfl⟩
      rcases hq with ⟨z, hz, _, hqz⟩
      have hzq : q = z := by
        funext k
        rw [hqz]
        simp [fiber_sum_vec, Finset.sum_filter]
      subst hzq
      calc ∑ i ∈ S, q i ≤ ∑ i, q i :=
            Finset.sum_le_univ_sum_of_nonneg (fun i => hz.1 i)
        _ = 1 := hz.2
    · exact Set.mem_image_of_mem _ hx'
  -- Step 3: for two probability vectors, a subset deficit is at most half the L1 distance
  have hkey : ∑ i ∈ S, (y i - x' i) ≤ (1 / 2 : ℝ) * ∑ i : Fin n, |x' i - y i| := by
    have hmain : ∑ i ∈ S, (y i - x' i) ≤ (1 / 2 : ℝ) * ∑ i : Fin n, |y i - x' i| := by
      have hd : ∑ i, (y i - x' i) = 0 := by
        rw [Finset.sum_sub_distrib, hy.2, hx'_sim.2, sub_self]
      have hdecomp := Finset.sum_add_sum_compl S (fun i => y i - x' i)
      have hdabs := Finset.sum_add_sum_compl S (fun i => |y i - x' i|)
      have hSc : ∑ i ∈ Sᶜ, (y i - x' i) = -(∑ i ∈ S, (y i - x' i)) := by
        rw [hd] at hdecomp; linarith
      have h1 : ∑ i ∈ S, (y i - x' i) ≤ ∑ i ∈ S, |y i - x' i| :=
        Finset.sum_le_sum (fun i _ => le_abs_self _)
      have h2 : ∑ i ∈ S, (y i - x' i) ≤ ∑ i ∈ Sᶜ, |y i - x' i| := by
        have h3 : ∑ i ∈ Sᶜ, (-(y i - x' i)) ≤ ∑ i ∈ Sᶜ, |(-(y i - x' i))| :=
          Finset.sum_le_sum (fun i _ => le_abs_self _)
        rw [Finset.sum_neg_distrib, hSc] at h3
        have habs : ∑ i ∈ Sᶜ, |(-(y i - x' i))| = ∑ i ∈ Sᶜ, |y i - x' i| :=
          Finset.sum_congr rfl (fun i _ => by rw [abs_neg])
        linarith
      linarith
    have habs : ∑ i : Fin n, |y i - x' i| = ∑ i : Fin n, |x' i - y i| :=
      Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)
    linarith
  have hdiff : (∑ i ∈ S, y i) - ∑ i ∈ S, x' i = ∑ i ∈ S, (y i - x' i) :=
    (Finset.sum_sub_distrib (s := S) (f := y) (g := x')).symm
  linarith
