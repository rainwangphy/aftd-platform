import AFTD.Prelude
import AFTD.Kb.Tcs.GaussPauliExpect
import AFTD.Kb.Tcs.GaussAxis
import AFTD.Kb.Tcs.PauliBasis

/-!
# gaussCorr

Topic: quantum   Node: aaab6eb80525

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

2-qubit correlation matrix of qubits 1 and 2: A_{ij} = ⟨σ_i ⊗ σ_j ⊗ I⟩.
-/

/-- Correlation matrix A_{ij} = Re⟨ψ|σ_i⊗σ_j⊗I|ψ⟩ of the first two qubits. -/
noncomputable def gaussCorr (ψ : EuclideanSpace ℂ (Fin 3 → Fin 2)) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => gaussPauliExpect ψ (fun q => if q = 0 then gaussAxis i else if q = 1 then gaussAxis j else PauliBasis.I)
