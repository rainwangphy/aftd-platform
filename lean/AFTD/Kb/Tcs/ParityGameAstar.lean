import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameAttractor
import AFTD.Kb.Tcs.ParityGameSameParityUpto

/-!
# parity_game_astar

Topic: automata   Node: 9d7f639ad3c4

Provenance: formalization of a published result. Source: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Section 3 (the set A*_d(G); the empty k = 0 term omitted)

A game on a finite vertex type V is given by own : V → Bool (own v = true means Even owns v, false means Odd owns v), E : V → V → Bool (E v w = true means there is an edge from v to w) and prio : V → ℕ (the priority of each vertex). A player is a Boolean: true is Even, false is Odd. parity_game_astar own E prio d (arguments in this order) is the finite set of vertices v such that 1 ≤ prio v ≤ d, prio v and d have different parities, and v belongs to parity_game_attractor own E pl U, where the player pl is Even if d is even and Odd if d is odd (pl = decide (d % 2 = 0)) and U = parity_game_same_parity_upto prio (prio v − 1) is the set of vertices whose priority is at most prio v − 1 and has the parity of prio v − 1. This is the set A*_d(G) of arXiv:2511.03752, the union over the k ≤ d of parity different from d of the vertices of priority k in the attractor of U_{k−1}(G) for the player of the parity of d; the term k = 0 is empty in a game where every vertex has a successor and is omitted.
-/

/-- The set `A*_d(G)` of arXiv:2511.03752 for the player of the parity of `d`: the vertices whose priority `k ≤ d` has the other parity and which lie in that player's attractor of `U_{k-1}(G)`. For `k = 0` the set `U_{-1}(G)` is empty and so is its attractor (every vertex has a successor), so that term is left out. -/
def parity_game_astar {V : Type} [Fintype V] [DecidableEq V] (own : V → Bool)
    (E : V → V → Bool) (prio : V → ℕ) (d : ℕ) : Finset V :=
  Finset.univ.filter (fun v => 1 ≤ prio v ∧ prio v ≤ d ∧ prio v % 2 ≠ d % 2 ∧
    v ∈ parity_game_attractor own E (decide (d % 2 = 0)) (parity_game_same_parity_upto prio (prio v - 1)))
