import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_realizes

Topic: graphs   Node: a1b89794391a

Provenance: formalization of a published result. Source: arXiv:2610.40521 Section 2

A tournament T on Fin n realizes degree vector d if T is a tournament and the outdegree of every vertex i equals d i.
-/

open Classical in
/-- A tournament T on Fin n realizes a degree vector d if T is a tournament and the outdegree of each vertex i equals d(i). -/
def tournament_realizes (n : ℕ) (T : Digraph (Fin n)) (d : Fin n → ℕ) : Prop := digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i
