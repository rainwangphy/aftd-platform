import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_degree_vector_realizable

Topic: graphs   Node: e4c99279158f

Provenance: formalization of a published result. Source: arXiv:2610.40521 Section 2

A degree vector d on Fin n is realizable if there exists a tournament T on Fin n whose outdegrees are given by d.
-/

open Classical in
/-- A degree vector d on Fin n is realizable if there exists an n-vertex tournament whose outdegrees match d. -/
def tournament_degree_vector_realizable (n : ℕ) (d : Fin n → ℕ) : Prop := ∃ T : Digraph (Fin n), digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i
