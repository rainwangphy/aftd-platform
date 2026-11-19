import AFTD.Prelude

/-!
# parity_game_even_wins_play

Topic: automata   Node: 6b157be19d29

Provenance: formalization of a published result. Source: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Section 2 (Even wins a play iff the least priority occurring infinitely often is even)

For a priority map prio : V → ℕ and an infinite sequence of vertices π : ℕ → V, Even wins the play π (min-parity condition) if there is an even natural number k such that prio (π n) = k for infinitely many n (for every N there is n ≥ N with prio (π n) = k) and every j < k occurs as prio (π n) for only finitely many n (there is N with prio (π n) ≠ j for all n ≥ N); that is, the least priority occurring infinitely often along π exists and is even. No condition that π follows edges is part of this definition.
-/

/-- Even wins the infinite play `π` under the min-parity condition: the least priority seen infinitely often along `π` is even. -/
def parity_game_even_wins_play {V : Type} (prio : V → ℕ) (π : ℕ → V) : Prop :=
  ∃ k, k % 2 = 0 ∧ (∀ N, ∃ n, N ≤ n ∧ prio (π n) = k) ∧
    ∀ j, j < k → ∃ N, ∀ n, N ≤ n → prio (π n) ≠ j
