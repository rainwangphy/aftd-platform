import AFTD.Prelude
import AFTD.Kb.Tcs.PauliOp
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.InstFintypePauliString

/-!
# pauliLiouvilleMomentTwo

Topic: quantum   Node: 0c6c94bdfe57

Provenance: formalization of a published result. Source: arXiv:2404.14488, Quantum 8, 1422 (2024)

For an n-qubit pure state ψ, the second Pauli-Liouville moment m_2(ψ) is (1/2^n) times the sum over all n-qubit Pauli strings P of |⟨ψ|P|ψ⟩|^4.
-/

/-- The second Pauli-Liouville moment m_2(ψ) = (1/2^n) ∑_P |⟨ψ|P|ψ⟩|^4 of an n-qubit pure state ψ. -/
noncomputable def pauliLiouvilleMomentTwo (n : ℕ) (ψ : Hn n) : ℝ := (1 / (2 ^ n : ℝ)) * ∑ p : PauliString n, ‖inner (𝕜 := ℂ) ψ (pauliOp p ψ)‖ ^ 4
