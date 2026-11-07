import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteWassersteinDist

/-!
# empirical_expected_transport_cost

Topic: online_algorithms   Node: 28d1354dc7b3

Provenance: formalization of a published result. Source: arXiv:2611.04275, Section 2.2, eq. (2.4)

The expected Wasserstein-1 distance f_t between the empirical distribution of t independent uniform samples from a sequence of n servers s : Fin n → X in a pseudo metric space X (each sample index chosen uniformly from Fin n) and the uniform distribution on all n servers, for t, n ≥ 1, and 0 if t = 0 or n = 0.
-/

/-- Expected Wasserstein-1 distance f_t between empirical distribution of t i.i.d. uniform server samples and the full server distribution. -/
noncomputable def empirical_expected_transport_cost {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) (s : Fin n → X) (t : ℕ) : ℝ :=
  if t = 0 ∨ n = 0 then 0
  else
    ((n : ℝ) ^ t)⁻¹ *
      ∑ I : Fin t → Fin n,
        discrete_wasserstein_dist
          (fun _ : Fin t => 1 / (t : ℝ)) (s ∘ I)
          (fun _ : Fin n => 1 / (n : ℝ)) s
