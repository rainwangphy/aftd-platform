import AFTD.Prelude

/-!
# has_fall_coloring

Topic: graphs   Node: 35b3bd86d66a

Provenance: formalization of a published result. Source: arXiv:2611.16649 Sec. 1, p. 2

A graph G admits a fall colouring with colours in α if it has a proper colouring c : G.Coloring α such that for every vertex v, the closed neighbourhood of v contains all colours in α.
-/

/-- A graph admits a fall colouring with colour set α if there is a proper colouring whose image on every closed neighbourhood is univ. -/
def has_fall_coloring {V : Type*} (α : Type*) (G : SimpleGraph V) : Prop := ∃ c : G.Coloring α, ∀ v : V, c '' (insert v (G.neighborSet v)) = Set.univ
