import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameEvenWinsPlay

/-!
# parity_game_even_wins_from

Topic: automata   Node: b72f3e58c0d1

Provenance: formalization of a published result. Source: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Section 2 (memoryless winning strategy from a vertex)

A game on a finite vertex type V is given by own : V → Bool (own v = true means Even owns v, false means Odd owns v), E : V → V → Bool (E v w = true means there is an edge from v to w) and prio : V → ℕ (the priority of each vertex). A player is a Boolean: true is Even, false is Odd. parity_game_even_wins_from own E prio v (arguments in this order) says that there is a map σ : V → V (a positional strategy of Even) with E u (σ u) = true for every vertex u owned by Even, such that every infinite sequence π : ℕ → V with π 0 = v, with E (π n) (π (n+1)) = true for all n, and with π (n+1) = σ (π n) whenever π n is owned by Even, is won by Even in the min-parity sense (parity_game_even_wins_play prio π: the least priority occurring infinitely often along π is even). By positional determinacy of parity games this is equivalent to Even having a winning strategy from v.
-/

/-- Even wins the parity game from vertex `v` with a positional strategy `σ` (min-parity condition): every play from `v` in which Even follows `σ` is won by Even. By positional determinacy this is the same as Even having any winning strategy from `v`. -/
def parity_game_even_wins_from {V : Type} (own : V → Bool) (E : V → V → Bool) (prio : V → ℕ)
    (v : V) : Prop :=
  ∃ σ : V → V, (∀ u, own u = true → E u (σ u) = true) ∧
    ∀ π : ℕ → V, π 0 = v → (∀ n, E (π n) (π (n + 1)) = true) →
      (∀ n, own (π n) = true → π (n + 1) = σ (π n)) → parity_game_even_wins_play prio π
