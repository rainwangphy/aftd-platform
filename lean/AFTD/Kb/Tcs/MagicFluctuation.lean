import AFTD.Prelude
import AFTD.Kb.Tcs.PauliLiouvilleMomentTwo
import AFTD.Kb.Tcs.Hn

/-!
# magicFluctuation

Topic: quantum   Node: 4ecda7b431ce

Provenance: formalization of a published result. Source: Quantum 8, 1422 (2024)

For an n-qubit pure state ψ in Hn n, with D = 2^n, magicFluctuation n ψ is the scaled magic fluctuation statistic Real.sqrt D * (D * pauliLiouvilleMomentTwo n ψ - (7 - 14 / D + 8 / (D ^ 2))).
-/

/-- The scaled second Pauli moment fluctuation statistic for an n-qubit pure state. -/
noncomputable def magicFluctuation (n : ℕ) (ψ : Hn n) : ℝ := let D : ℝ := (2 ^ n : ℝ); Real.sqrt D * (D * pauliLiouvilleMomentTwo n ψ - (7 - 14 / D + 8 / (D ^ 2)))
