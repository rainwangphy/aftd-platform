import AFTD.Prelude

/-!
# energy_filter_sequence_purity

Topic: statistical_mechanics   Node: bde060f80fc0

Provenance: original. Related work: arXiv:2405.02158 Energy-filtered quantum states and the emergence of non-local correlations

Given a sequence filter a : ℤ → ℝ and a parameter k : ℕ, energy_filter_sequence_purity a k is the Renyi-2 purity Tr((Tr_B |psi_n><psi_n|)^2) of the energy-filtered state on n = 4k spins with equal bipartition into two subsystems of 2k spins, given by Tr((M M^T)^2) / (Tr(M M^T))^2 where M(sA, sB) = a(2k - |sA| - |sB|).
-/

/-- The bipartite Renyi-2 purity Tr((Tr_B |psi_n><psi_n|)^2) of the energy-filtered state on n = 4k spins with equal bipartition. -/
noncomputable def energy_filter_sequence_purity (a : ℤ → ℝ) (k : ℕ) : ℝ :=
  let w : (Fin (2 * k) → Bool) → ℤ := fun s => ∑ j : Fin (2 * k), if s j then 1 else 0
  let M : Matrix (Fin (2 * k) → Bool) (Fin (2 * k) → Bool) ℝ :=
    fun sA sB => a (2 * (k : ℤ) - w sA - w sB)
  let R := M * M.transpose
  (R * R).trace / (R.trace)^2
