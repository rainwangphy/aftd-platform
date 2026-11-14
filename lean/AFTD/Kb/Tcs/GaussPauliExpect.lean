import AFTD.Prelude
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliMatrix

/-!
# gaussPauliExpect

Topic: quantum   Node: cae3a6fdc053

Provenance: helper lemma. step towards three_qubit_gaussian_witness_not_locally_real

Real part of the Pauli expectation of the 3-qubit Pauli string p in the pure state ψ, i.e. Re⟨ψ|P_p|ψ⟩.
-/

/-- Real part of the quadratic form ⟨ψ| P_p |ψ⟩ of a Pauli string in a pure state. -/
noncomputable def gaussPauliExpect (ψ : EuclideanSpace ℂ (Fin 3 → Fin 2)) (p : PauliString 3) : ℝ := (∑ s : Fin 3 → Fin 2, ∑ t : Fin 3 → Fin 2, (starRingEnd ℂ) (ψ s) * pauliMatrix p s t * ψ t).re
