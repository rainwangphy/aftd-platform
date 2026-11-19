import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameEvenWinsPlay

/-!
# parity_game_even_wins_play_of_frequently_zero

Topic: automata   Node: 1994e62ff868

Provenance: helper lemma. arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time): sanity lemma for the min-parity winning condition

A play that visits priority 0 infinitely often is won by Even under the min-parity condition.
-/

theorem parity_game_even_wins_play_of_frequently_zero {V : Type} (prio : V → ℕ) (π : ℕ → V)
    (h : ∀ N, ∃ n, N ≤ n ∧ prio (π n) = 0) : parity_game_even_wins_play prio π := by
  exact ⟨0, rfl, h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
