import AFTD.Prelude
import AFTD.Kb.Tcs.GaussAxis
import AFTD.Kb.Tcs.PauliBasisToMatrix

/-!
# gaussPauliFrame

Topic: quantum   Node: 882d4e8a8268

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

The single-qubit Pauli frame C(m)_{ij} = Re tr(m^* σ_i m σ_j)/2 of a 2x2 matrix m.
-/

/-- Single-qubit Pauli frame C(m)_{ij} = Re tr(m† σ_i m σ_j)/2. -/
noncomputable def gaussPauliFrame (m : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (Matrix.trace (m.conjTranspose * (gaussAxis i).toMatrix * m * (gaussAxis j).toMatrix)).re / 2
