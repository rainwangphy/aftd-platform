import AFTD.Prelude

/-!
# mnw2_sum_groups

Topic: fair_division   Node: e3d19f9fc0fc

For allocations O, N of m goods to two agents, item values u and weights c(a, b), ∑_g c(O g, N g) u_g equals ∑_{a,b} c(a, b) · u(G_{ab}), where G_{ab} is the set of goods that O gives to a and N gives to b.
-/

/-- A sum whose weight depends only on the pair (O g, N g) splits into the four group sums. -/
theorem mnw2_sum_groups {m : ℕ} (u : Fin m → ℝ) (O N : Fin m → Fin 2) (c : Fin 2 → Fin 2 → ℝ) : ∑ g, c (O g) (N g) * u g = c 0 0 * ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 0), u g + c 1 0 * ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 0), u g + c 0 1 * ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 1), u g + c 1 1 * ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 1), u g := by
  simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  rcases h2 (O g) with ho | ho <;> rcases h2 (N g) with hn | hn <;> simp [ho, hn]
