import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2SumGroups
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# mnw2_bundle_value

Topic: fair_division   Node: 93dbd0e8e2ea

If τ(g) = T(O g, N g) for a map T : {0,1}² → {0,1}, then the value u(X_k) of agent k's bundle under τ is the sum of the group sums u(G_{ab}) over the groups (a, b) with T(a, b) = k.
-/

/-- If an allocation `τ` decides each good by its group (O g, N g), each bundle value is a sum of group sums. -/
theorem mnw2_bundle_value {m : ℕ} (u : Fin m → ℝ) (O N τ : Fin m → Fin 2) (T : Fin 2 → Fin 2 → Fin 2) (hτ : ∀ g, τ g = T (O g) (N g)) (k : Fin 2) : additive_valuation u (bundle_of τ k) = (if T 0 0 = k then 1 else 0) * ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 0), u g + (if T 1 0 = k then 1 else 0) * ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 0), u g + (if T 0 1 = k then 1 else 0) * ∑ g ∈ Finset.univ.filter (fun g => O g = 0 ∧ N g = 1), u g + (if T 1 1 = k then 1 else 0) * ∑ g ∈ Finset.univ.filter (fun g => O g = 1 ∧ N g = 1), u g := by
  have e := mnw2_sum_groups u O N (fun a b => if T a b = k then (1 : ℝ) else 0)
  try simp only at e
  rw [← e]
  unfold additive_valuation bundle_of
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hτ g]
  split_ifs <;> simp
