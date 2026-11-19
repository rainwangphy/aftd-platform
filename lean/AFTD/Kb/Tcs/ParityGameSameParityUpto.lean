import AFTD.Prelude

/-!
# parity_game_same_parity_upto

Topic: automata   Node: 81644715f0e8

Provenance: formalization of a published result. Source: arXiv:2511.03752 (Attractors Is All You Need: Parity Games In Polynomial Time), Section 3 (the set U_d(G))

For a priority map prio : V → ℕ on a finite vertex type V and a natural number d, parity_game_same_parity_upto prio d is the finite set of vertices v with prio v ≤ d and prio v ≡ d (mod 2).
-/

/-- The set `U_d(G)` of arXiv:2511.03752: the vertices whose priority is at most `d` and has the parity of `d`. -/
def parity_game_same_parity_upto {V : Type} [Fintype V] (prio : V → ℕ) (d : ℕ) : Finset V :=
  Finset.univ.filter (fun v => prio v ≤ d ∧ prio v % 2 = d % 2)
