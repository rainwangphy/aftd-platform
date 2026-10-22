import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberLeThreeMulPackingNumber

/-!
# simple_graph_triangle_cover_number_eq_zero_of_packing_number_eq_zero

Topic: graphs   Node: f582ce5635f7

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

If a finite graph has packing number 0, then its triangle cover number is 0.
-/

/-- If a finite graph has triangle packing number 0, then its triangle cover number is 0. -/
theorem simple_graph_triangle_cover_number_eq_zero_of_packing_number_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : simple_graph_triangle_packing_number G = 0) :
    simple_graph_triangle_cover_number G = 0 := by
  have hle := simple_graph_triangle_cover_number_le_three_mul_packing_number G
  omega
