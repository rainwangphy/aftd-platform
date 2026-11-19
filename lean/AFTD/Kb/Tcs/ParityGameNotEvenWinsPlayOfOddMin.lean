import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameEvenWinsPlay

/-!
# parity_game_not_even_wins_play_of_odd_min

Topic: automata   Node: 2df91dd4e64c

Provenance: helper lemma. arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time): sanity lemma for the min-parity winning condition

If an odd priority k occurs infinitely often along a play and every smaller priority occurs only finitely often, then Even does not win the play under the min-parity condition (the least priority seen infinitely often is unique).
-/

theorem parity_game_not_even_wins_play_of_odd_min {V : Type} (prio : V → ℕ) (π : ℕ → V) (k : ℕ)
    (hk : k % 2 = 1) (hf : ∀ N, ∃ n, N ≤ n ∧ prio (π n) = k)
    (hlt : ∀ j, j < k → ∃ N, ∀ n, N ≤ n → prio (π n) ≠ j) : ¬ parity_game_even_wins_play prio π := by
  rintro ⟨k', hk', hf', hlt'⟩
  rcases Nat.lt_trichotomy k k' with h | h | h
  · obtain ⟨N, hN⟩ := hlt' k h
    obtain ⟨n, hn, e⟩ := hf N
    exact hN n hn e
  · omega
  · obtain ⟨N, hN⟩ := hlt k' h
    obtain ⟨n, hn, e⟩ := hf' N
    exact hN n hn e
