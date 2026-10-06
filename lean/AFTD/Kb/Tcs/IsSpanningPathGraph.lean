import AFTD.Prelude

/-!
# is_spanning_path_graph

Topic: graphs   Node: 5ed530789a7c

Provenance: formalization of a published result. Source: arXiv:2610.06228 (Hiding a Vertex from the Temporal Explorer), Sec. 7 (snapshots that are paths)

A graph on n vertices is a spanning path if its vertices can be ordered so that exactly consecutive vertices are adjacent.
-/

/-- `H` is a spanning path on `Fin n`: for some ordering `f` of the vertices, two vertices are adjacent exactly when they are consecutive in the ordering. -/
def is_spanning_path_graph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Equiv.Perm (Fin n), ∀ a b, H.Adj a b ↔ ((f a : ℕ) + 1 = f b ∨ (f b : ℕ) + 1 = f a)
