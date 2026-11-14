import AFTD.Prelude
import AFTD.Kb.Tcs.GaussPauliExpect
import AFTD.Kb.Tcs.GaussAxis
import AFTD.Kb.Tcs.PauliBasis

/-!
# gaussBlochB

Topic: quantum   Node: 19c8daa3508c

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

Bloch vector of the second qubit: b_i = ⟨I ⊗ σ_i ⊗ I⟩.
-/

/-- Bloch vector of the second qubit, b_i = Re⟨ψ|I⊗σ_i⊗I|ψ⟩. -/
noncomputable def gaussBlochB (ψ : EuclideanSpace ℂ (Fin 3 → Fin 2)) : Fin 3 → ℝ := fun i => gaussPauliExpect ψ (fun q => if q = 1 then gaussAxis i else PauliBasis.I)
