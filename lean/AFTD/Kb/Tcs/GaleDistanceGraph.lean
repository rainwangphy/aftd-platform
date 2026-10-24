import AFTD.Prelude

/-!
# gale_distance_graph

Topic: combinatorics   Node: 3d8bd8fcc55c

Provenance: formalization of a published result. Source: arXiv:2610.28828, Sec. 3.1

For a finite subset V of the 3-dimensional Euclidean space `EuclideanSpace ℝ (Fin 3)` and a real number t, `gale_distance_graph V t` is the simple graph with vertex set V (as a subtype) where two vertices u, v ∈ V are adjacent if and only if u ≠ v and the distance between u and v is strictly greater than t.
-/

/-- The distance threshold graph on a finite subset V of EuclideanSpace R (Fin 3) with threshold t. -/
def gale_distance_graph (V : Finset (EuclideanSpace ℝ (Fin 3))) (t : ℝ) : SimpleGraph V := {
  Adj := fun u v => u ≠ v ∧ t < dist (u : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3))
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩
}
