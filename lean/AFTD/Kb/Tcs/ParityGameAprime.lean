import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameAttractor
import AFTD.Kb.Tcs.ParityGameSameParityUpto
import AFTD.Kb.Tcs.ParityGameAstar

/-!
# parity_game_aprime

Topic: automata   Node: 36fd9485b9ff

Provenance: formalization of a published result. Source: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Section 3 (the set A'_d(G, A))

A game on a finite vertex type V is given by own : V → Bool (own v = true means Even owns v, false means Odd owns v), E : V → V → Bool (E v w = true means there is an edge from v to w) and prio : V → ℕ (the priority of each vertex). A player is a Boolean: true is Even, false is Odd. parity_game_aprime own E prio d A (arguments in this order; A is a finite set of vertices) is parity_game_attractor own E q T, where the player q is the opponent of the player of the parity of d (q is Odd if d is even and Even if d is odd, q = !decide (d % 2 = 0)) and T is the set of vertices v of A with prio v < d that are neither in parity_game_astar own E prio d nor in parity_game_same_parity_upto prio d. This is the set A'_d(G, A) of arXiv:2511.03752.
-/

/-- The set `A'_d(G, A)` of arXiv:2511.03752: the attractor, for the opponent of the player of the parity of `d`, of the vertices of `A` of priority below `d` that are neither in `A*_d(G)` nor in `U_d(G)`. -/
def parity_game_aprime {V : Type} [Fintype V] [DecidableEq V] (own : V → Bool)
    (E : V → V → Bool) (prio : V → ℕ) (d : ℕ) (A : Finset V) : Finset V :=
  parity_game_attractor own E (!decide (d % 2 = 0))
    (A.filter (fun v => v ∉ parity_game_astar own E prio d ∧ v ∉ parity_game_same_parity_upto prio d ∧ prio v < d))
