import AFTD.Prelude
import AFTD.Kb.Tcs.GhzPauliCoeff

/-!
# ghz_correlation_vector

Topic: quantum   Node: 33491b6c518d

Provenance: formalization of a published result. Source: arXiv:2610.35838 Eq. 10

For parameter alpha in R, orthonormal frames e, f of R^3, and indices mu, nu in {0, 1, 2, 3}, the correlation vector tau_{mu nu} has components (tau_{mu nu})_1 = sin(2*alpha) * (a_1 c_1 - a_2 c_2), (tau_{mu nu})_2 = -sin(2*alpha) * (a_1 c_2 + a_2 c_1), and (tau_{mu nu})_3 = cos(2*alpha) * a_0 c_0 + a_0 c_3 + a_3 c_0 + cos(2*alpha) * a_3 c_3.
-/

/-- The correlation vector tau_{mu nu} for the generalized GHZ state |GHZ_alpha> in frames e and f. -/
noncomputable def ghz_correlation_vector (α : ℝ) (e f : Matrix (Fin 3) (Fin 3) ℝ) (μ ν : Fin 4) : Fin 3 → ℝ :=
  let a := ghz_pauli_coeff e μ
  let c := ghz_pauli_coeff f ν
  fun k =>
    if k = 0 then
      Real.sin (2 * α) * (a 1 * c 1 - a 2 * c 2)
    else if k = 1 then
      - Real.sin (2 * α) * (a 1 * c 2 + a 2 * c 1)
    else
      Real.cos (2 * α) * a 0 * c 0 + a 0 * c 3 + a 3 * c 0 + Real.cos (2 * α) * a 3 * c 3
