import AFTD.Prelude

/-!
# energy_filter_renyi_moment

Topic: statistical_mechanics   Node: 733f546e933a

Provenance: formalization of a published result. Source: knowledgebase, OP-1115

For a filter sequence a : ℤ → ℝ, half-chain parameter k : ℕ (representing n = 4k spins), and real exponent q, energy_filter_renyi_moment a k q is the Renyi-q moment Tr(rho_n^q) of the reduced density matrix on 2k spins, computed as (∑ s, λ_s^q) / (∑ s, λ_s)^q where λ_s are the eigenvalues of M * Mᴴ and M sA sB = a (2k - |sA| - |sB|).
-/

/-- The Renyi-q moment Tr(rho_n^q) of the reduced density matrix on 2k qubits for the symmetric-sector energy-filtered state on 4k spins. -/
noncomputable def energy_filter_renyi_moment (a : ℤ → ℝ) (k : ℕ) (q : ℝ) : ℝ :=
  let w : (Fin (2 * k) → Bool) → ℤ := fun s => ∑ j : Fin (2 * k), if s j then 1 else 0
  let M : Matrix (Fin (2 * k) → Bool) (Fin (2 * k) → Bool) ℝ :=
    fun sA sB => a (2 * (k : ℤ) - w sA - w sB)
  let hR := Matrix.isHermitian_mul_conjTranspose_self M
  (∑ s, (hR.eigenvalues s) ^ q) / (∑ s, hR.eigenvalues s) ^ q
