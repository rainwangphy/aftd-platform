import AFTD.Prelude

/-!
# digraph_in_degree

Topic: combinatorics   Node: bf3cb62e53f9

Provenance: formalization of a published result. Source: folklore

The in-degree of a vertex v in a finite directed graph D is the number of vertices u such that D.Adj u v.
-/

/-- The in-degree of a vertex in a finite directed graph. -/
def digraph_in_degree {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (v : V) : ℕ := (Finset.univ.filter (fun u => D.Adj u v)).card
