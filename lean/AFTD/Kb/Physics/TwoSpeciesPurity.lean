import AFTD.Prelude

/-!
# two_species_purity

Topic: statistical_mechanics   Node: 16116ed1f7dd

Provenance: original. Related work: arXiv:2405.02158

Given a natural number k and real parameters tau and alpha, letting S = (Fin k -> Bool) * (Fin k -> Bool) with half-system energy e(s) = sum_{j in Fin k} (if s.1 j then 1 else -1) + alpha * sum_{j in Fin k} (if s.2 j then 1 else -1) and unnormalized bipartite filter matrix M(s_A, s_B) = exp(-tau^2 * (e(s_A) + e(s_B))^2 / 4), two_species_purity(k, tau, alpha) is the purity ratio Tr((M M^T)^2) / (Tr(M M^T))^2.
-/

/-- Bipartite entanglement purity of the two-species energy-filtered state on 4k qubits. -/
noncomputable def two_species_purity (k : ℕ) (τ α : ℝ) : ℝ :=
  let M : Matrix ((Fin k → Bool) × (Fin k → Bool)) ((Fin k → Bool) × (Fin k → Bool)) ℝ :=
    fun sA sB =>
      let eA := (∑ j : Fin k, if sA.1 j then (1 : ℝ) else (-1 : ℝ)) +
        α * (∑ j : Fin k, if sA.2 j then (1 : ℝ) else (-1 : ℝ))
      let eB := (∑ j : Fin k, if sB.1 j then (1 : ℝ) else (-1 : ℝ)) +
        α * (∑ j : Fin k, if sB.2 j then (1 : ℝ) else (-1 : ℝ))
      Real.exp (- (τ^2 * (eA + eB)^2 / 4))
  let R := M * M.transpose
  (R * R).trace / (R.trace)^2
