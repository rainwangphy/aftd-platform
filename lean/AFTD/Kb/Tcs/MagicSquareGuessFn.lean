import AFTD.Prelude
import AFTD.Kb.Tcs.IsPovm
import AFTD.Kb.Tcs.MagicSquareStrategyValid
import AFTD.Kb.Tcs.MagicSquareScore
import AFTD.Kb.Tcs.MagicSquareKeyGuessSuccess

/-!
# magic_square_guess_fn

Topic: quantum   Node: 555b14187781

Provenance: formalization of a published result. Source: arXiv:2610.12001 (Exact value and rigidity of the 2x3 magic rectangle), Sec. 6, the function g(w) defined before Corollary 6.2.

magic_square_guess_fn w is the real supremum (sSup in ℝ) of the set of reals p for which there exist dA dB dE : ℕ, A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ, B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ, a complex matrix ρ indexed by (Fin dA × Fin dB) × Fin dE, and M : (Fin 3 → Bool) → Matrix (Fin dE) (Fin dE) ℂ with magic_square_strategy_valid A B ρ, is_povm dE M, w ≤ magic_square_score A B ρ and p = magic_square_key_guess_success A ρ M. This is g(w): the supremum, over all finite-dimensional magic-square strategies with quantum side information whose score is at least w, of the adversary's guessing probability p_guess(K | E, x = 0) for Alice's complete first-row answer K (itself the supremum over the adversary's guessing POVMs).
-/

/-- `g(w)` of arXiv:2610.12001, Sec. 6: the supremum of the adversary's guessing probability `p_guess(K | E, x = 0)` for Alice's first-row answer `K`, over all valid finite-dimensional magic-square strategies with score at least `w` and all of the adversary's guessing POVMs. -/
noncomputable def magic_square_guess_fn (w : ℝ) : ℝ :=
  sSup {p : ℝ | ∃ (dA dB dE : ℕ) (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (ρ : Matrix ((Fin dA × Fin dB) × Fin dE) ((Fin dA × Fin dB) × Fin dE) ℂ)
    (M : (Fin 3 → Bool) → Matrix (Fin dE) (Fin dE) ℂ),
    magic_square_strategy_valid A B ρ ∧ is_povm dE M ∧ w ≤ magic_square_score A B ρ ∧
      p = magic_square_key_guess_success A ρ M}
