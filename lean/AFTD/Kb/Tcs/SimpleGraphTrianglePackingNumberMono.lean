import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberEqZeroOfCliqueFree

/-!
# simple_graph_triangle_packing_number_mono

Topic: graphs   Node: 2aa902ba20b6

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

Triangle packing number is monotone under subgraph inclusion: if H ≤ G, then ν(H) ≤ ν(G).
-/

/-- Triangle packing number is monotone under subgraph inclusion: if H ≤ G, then ν(H) ≤ ν(G). -/
theorem simple_graph_triangle_packing_number_mono {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hle : H ≤ G) :
    simple_graph_triangle_packing_number H ≤ simple_graph_triangle_packing_number G := by
  unfold simple_graph_triangle_packing_number
  apply csSup_le_csSup
  · -- the packing numbers of G are bounded by the number of vertex subsets
    refine ⟨Fintype.card (Finset V), ?_⟩
    rintro n ⟨T, -, -, rfl⟩
    exact Finset.card_le_univ T
  · -- the set of admissible packing sizes of H is nonempty (empty packing)
    exact ⟨0, ∅, by simp, by simp, rfl⟩
  · -- every packing of H is a packing of G, as triangles persist under supergraphs
    rintro n ⟨T, hT, hpw, rfl⟩
    exact ⟨T, fun t ht => (hT t ht).mono hle, hpw, rfl⟩
