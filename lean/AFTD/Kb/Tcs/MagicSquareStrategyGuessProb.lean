import AFTD.Prelude
import AFTD.Kb.Tcs.IsPovm
import AFTD.Kb.Tcs.MagicSquareKeyGuessSuccess

/-!
# magic_square_strategy_guess_prob

Topic: quantum   Node: 1b6824b1fd50

Provenance: formalization of a published result. Source: arXiv:2610.12001, Theorem 6.1

The maximum probability p_guess(K | E, x = 0) of an adversary guessing Alice's first row K in a strategy with effects A and state ρ, defined as the supremum of the guessing success probability over all guessing POVMs M on the adversary system.
-/

/-- The maximum probability p_guess(K | E, x = 0) of guessing Alice's first row K in strategy (A, ρ). -/
noncomputable def magic_square_strategy_guess_prob {dA dB dE : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ) : ℝ := sSup {p : ℝ | ∃ M : (Fin 3 → Bool) → Matrix (Fin dE) (Fin dE) ℂ,
    is_povm dE M ∧ p = magic_square_key_guess_success A ρ M}
