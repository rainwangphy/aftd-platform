import AFTD.Prelude

/-!
# simple_graph_or_power

Topic: information   Node: 2926364423f9

Provenance: formalization of a published result. Source: arXiv:2610.41977 eq. (1.1)

The n-th OR-power (co-normal power) G^{∨n} of a simple graph G has vertex set Fin n → V, with an edge between two functions if they are adjacent in at least one coordinate.
-/

/-- The n-th OR-power (co-normal power) of a simple graph. -/
def simple_graph_or_power {V : Type*} (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) := {
  Adj := fun x y => ∃ i : Fin n, G.Adj (x i) (y i)
  symm.symm := fun x y => by simp [SimpleGraph.adj_comm]
}
