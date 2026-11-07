import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteWassersteinDist

/-!
# subset_expected_transport_cost

Topic: online_algorithms   Node: 7c44e839e988

Provenance: formalization of a published result. Source: arXiv:2611.04275, Section 2.2, eq. (2.5)

The expected Wasserstein-1 distance g_k between the uniform distribution over a uniformly random k-element subset A ⊆ Fin n of servers s : Fin n → X in a pseudo metric space X and the uniform distribution on all n servers, for 1 ≤ k ≤ n, and 0 if k = 0 or n < k.
-/

/-- Expected Wasserstein-1 distance g_k between the uniform distribution on a random k-subset of servers and the full server distribution. -/
noncomputable def subset_expected_transport_cost {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) (s : Fin n → X) (k : ℕ) : ℝ :=
  if k = 0 ∨ n < k then 0
  else
    ((Nat.choose n k : ℝ))⁻¹ *
      ∑ A ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
        discrete_wasserstein_dist
          (fun _ : A => 1 / (k : ℝ)) (fun (i : A) => s i.1)
          (fun _ : Fin n => 1 / (n : ℝ)) s
