import AFTD.Prelude
import AFTD.Kb.Tcs.GaussPauliExpect
import AFTD.Kb.Tcs.GaussAxis
import AFTD.Kb.Tcs.PauliBasis

/-!
# gaussBlochA

Topic: quantum   Node: a63c87edac83

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

Bloch vector of the first qubit: a_i = ⟨σ_i ⊗ I ⊗ I⟩.
-/

/-- Bloch vector of the first qubit, a_i = Re⟨ψ|σ_i⊗I⊗I|ψ⟩. -/
noncomputable def gaussBlochA (ψ : EuclideanSpace ℂ (Fin 3 → Fin 2)) : Fin 3 → ℝ := fun i => gaussPauliExpect ψ (fun q => if q = 0 then gaussAxis i else PauliBasis.I)
