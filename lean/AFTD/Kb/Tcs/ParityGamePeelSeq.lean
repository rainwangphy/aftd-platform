import AFTD.Prelude
import AFTD.Kb.Tcs.ParityGameAttractor
import AFTD.Kb.Tcs.ParityGameSameParityUpto
import AFTD.Kb.Tcs.ParityGameAprime

/-!
# parity_game_peel_seq

Topic: automata   Node: 8d5672a72436

Provenance: formalization of a published result. Source: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Section 3 (the sets U^k(G, d) and A^k(G, d) defining A(G, d))

A game on a finite vertex type V is given by own : V → Bool (own v = true means Even owns v, false means Odd owns v), E : V → V → Bool (E v w = true means there is an edge from v to w) and prio : V → ℕ (the priority of each vertex). A player is a Boolean: true is Even, false is Odd. Let pl be the player of the parity of d (Even if d is even, Odd if d is odd) and q the other player. parity_game_peel_seq own E prio d (arguments in this order) is the sequence, indexed by k ∈ ℕ, of pairs (U^k, A^k) of finite sets of vertices defined by recursion on k: U^0 = parity_game_same_parity_upto prio d (the vertices of priority at most d with the parity of d) and A^0 = parity_game_attractor own E pl U^0; and U^{k+1} = U^k \ parity_game_attractor own E q ((V \ A^k) ∪ parity_game_aprime own E prio d A^k) and A^{k+1} = parity_game_attractor own E pl U^{k+1}, where V \ A^k is the complement of A^k in the set of all vertices. The first component of the k-th pair is U^k and the second is A^k. These are the sets U^k(G, d) and A^k(G, d) of arXiv:2511.03752, whose set A(G, d) is the intersection of all the A^k.
-/

/-- The sequence of pairs `(U^k(G, d), A^k(G, d))` of arXiv:2511.03752, whose second components intersect to the set `A(G, d)` that the paper claims is a dominion. -/
def parity_game_peel_seq {V : Type} [Fintype V] [DecidableEq V] (own : V → Bool)
    (E : V → V → Bool) (prio : V → ℕ) (d : ℕ) : ℕ → Finset V × Finset V
  | 0 => (parity_game_same_parity_upto prio d,
      parity_game_attractor own E (decide (d % 2 = 0)) (parity_game_same_parity_upto prio d))
  | k + 1 =>
      (((parity_game_peel_seq own E prio d k).1 \ parity_game_attractor own E (!decide (d % 2 = 0))
          ((Finset.univ \ (parity_game_peel_seq own E prio d k).2) ∪
            parity_game_aprime own E prio d (parity_game_peel_seq own E prio d k).2)),
       parity_game_attractor own E (decide (d % 2 = 0))
        ((parity_game_peel_seq own E prio d k).1 \ parity_game_attractor own E (!decide (d % 2 = 0))
          ((Finset.univ \ (parity_game_peel_seq own E prio d k).2) ∪
            parity_game_aprime own E prio d (parity_game_peel_seq own E prio d k).2)))
