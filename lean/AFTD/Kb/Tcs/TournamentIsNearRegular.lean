import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_is_near_regular

Topic: graphs   Node: b71d91c4cc29

Provenance: formalization of a published result. Source: J.W. Moon, Topics on Tournaments (1968), Section 3

A tournament on 2m vertices is near-regular if every vertex has out-degree m - 1 or m.
-/

/-- A tournament on 2m vertices is near-regular if every vertex has out-degree m - 1 or m. -/
def tournament_is_near_regular (m : ℕ) (D : Digraph (Fin (2 * m))) [DecidableRel D.Adj] : Prop := ∀ v : Fin (2 * m), digraph_out_count D v = m - 1 ∨ digraph_out_count D v = m
