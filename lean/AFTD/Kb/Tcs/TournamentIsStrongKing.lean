import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphTwoPathCount

/-!
# tournament_is_strong_king

Topic: graphs   Node: eb2d0d8d75b3

Provenance: formalization of a published result. Source: arXiv:2610.39702, Definition in Section 2.1

A vertex v in a finite directed graph D is a strong king if for every in-neighbor u of v (that is, every vertex u with an arc from u to v), the number of directed two-paths from v to u is strictly greater than the number of directed two-paths from u to v.
-/

/-- Predicate that a vertex is a strong king: for every in-neighbor u, there are strictly more 2-paths from v to u than from u to v. -/
def tournament_is_strong_king {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (v : V) : Prop := ∀ u, D.Adj u v → digraph_two_path_count D u v < digraph_two_path_count D v u
