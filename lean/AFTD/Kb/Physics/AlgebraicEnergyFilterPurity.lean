import AFTD.Prelude

/-!
# algebraic_energy_filter_purity

Topic: statistical_mechanics   Node: 0b1779622180

Provenance: original. Related work: arXiv:2405.02158; OP-889

For natural k and real s, the Renyi-2 purity Tr((Tr_B |psi><psi|)^2) of the algebraic energy-filtered state proportional to (1+|H|)^(-s) |+>^tensor(4k) on 4k spins with equal bipartition into two subsystems of 2k spins, given by Tr((M M^T)^2) / (Tr(M M^T))^2 where M(sA, sB) = (1 + |e(sA) + e(sB)|)^(-s).
-/

/-- Bipartite Renyi-2 purity of an algebraic energy-filtered state on 4k spins -/
noncomputable def algebraic_energy_filter_purity (k : ℕ) (s : ℝ) : ℝ :=
  let M : Matrix (Fin (2 * k) → Bool) (Fin (2 * k) → Bool) ℝ :=
    fun sA sB =>
      let eA := ∑ j : Fin (2 * k), if sA j then (1 : ℝ) else (-1 : ℝ)
      let eB := ∑ j : Fin (2 * k), if sB j then (1 : ℝ) else (-1 : ℝ)
      (1 + |eA + eB|) ^ (-s)
  let R := M * M.transpose
  (R * R).trace / (R.trace)^2
