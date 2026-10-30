import AFTD.Prelude

/-!
# petersen_graph

Topic: np_completeness   Node: 23c18a32f2f2

Provenance: formalization of a published result. Source: arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Figure 1: the Petersen graph P10 (here as the Kneser graph K(5,2), which is isomorphic to it)

The Petersen graph P10, as the Kneser graph K(5,2): a SimpleGraph on the vertex type {s : Finset (Fin 5) // s.card = 2} of 2-element subsets of Fin 5, in which two vertices s and t are adjacent iff the finsets s.1 and t.1 are disjoint (Disjoint s.1 t.1).
-/

/-- The Petersen graph as the Kneser graph K(5,2): 2-subsets of Fin 5, adjacent when disjoint. -/
def petersen_graph : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj s t := Disjoint s.1 t.1
  symm := ⟨fun _ _ h => Disjoint.symm h⟩
  loopless := ⟨fun s h => by
    have h2 := s.2
    rw [disjoint_self.mp h] at h2
    simp at h2⟩
