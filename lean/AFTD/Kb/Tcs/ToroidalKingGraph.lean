import AFTD.Prelude

/-!
# toroidal_king_graph

Topic: graphs   Node: ad7e729302c7

Provenance: formalization of a published result. Source: scout/2611-22830-independent-sets-in-the-2-token-graph-of-a-cycle-and-kings.md:93

The king graph toroidal_king_graph n on the vertex type Fin n × Fin n, where two distinct vertices p and q are adjacent if and only if in each coordinate their components are equal or adjacent in SimpleGraph.cycleGraph n.
-/

/-- The king graph on the n × n toroidal board with vertex type Fin n × Fin n. -/
def toroidal_king_graph (n : ℕ) : SimpleGraph (Fin n × Fin n) := {
  Adj := fun p q => p ≠ q ∧ (p.1 = q.1 ∨ (SimpleGraph.cycleGraph n).Adj p.1 q.1) ∧
    (p.2 = q.2 ∨ (SimpleGraph.cycleGraph n).Adj p.2 q.2)
  symm := ⟨by
    rintro p q ⟨hne, h1, h2⟩
    refine ⟨hne.symm, ?_, ?_⟩
    · rcases h1 with h | h
      · left; exact h.symm
      · right; exact (SimpleGraph.cycleGraph n).adj_symm h
    · rcases h2 with h | h
      · left; exact h.symm
      · right; exact (SimpleGraph.cycleGraph n).adj_symm h⟩
  loopless := ⟨by
    rintro p ⟨hne, -⟩
    exact hne rfl⟩
}
