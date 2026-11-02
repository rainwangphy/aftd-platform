import AFTD.Prelude

/-!
# magic_square_key_guess_success

Topic: quantum   Node: 28658ea67b3d

Provenance: formalization of a published result. Source: arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Sec. 6, proof of Theorem 6.1 (the success probability p_M of a guess).

Given dA dB dE : ℕ, Alice's effects A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ, a complex matrix ρ indexed by (Fin dA × Fin dB) × Fin dE, and the adversary's family M : (Fin 3 → Bool) → Matrix (Fin dE) (Fin dE) ℂ: magic_square_key_guess_success A ρ M is the real number Σ_{k : Fin 3 → Bool} Re Tr(((A 0 k ⊗ₖ I_{Fin dB}) ⊗ₖ M k) * ρ), Kronecker products grouped left as written, Re the real part of the complex trace. It is the success probability of the adversary's guessing measurement M (outcomes: sign strings) for Alice's key K, her whole answer on row x = 0: Σ_k Tr((A_{k|0} ⊗ I_B ⊗ M_k) ρ).
-/

/-- The probability that the adversary's measurement `M` (outcome: a guessed sign string) guesses Alice's whole answer `K` on row `x = 0`. -/
noncomputable def magic_square_key_guess_success {dA dB dE : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ)
    (M : (Fin 3 → Bool) → Matrix (Fin dE) (Fin dE) ℂ) : ℝ := open scoped Kronecker in
  ∑ k : Fin 3 → Bool,
    (((A 0 k ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) ⊗ₖ M k) * ρ).trace.re
