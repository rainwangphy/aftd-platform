import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeLeChoose
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# card_le_twenty_nine_of_regular_eight_triangle_distinct

Topic: graphs   Node: 591989bf7e7a

Provenance: helper lemma. Pigeonhole bound towards OP-123 (arXiv:2610.08478, Sec. 1). Its recorded dependency on the unproved exists_regular_eight_triangle_distinct blocks the offline build; the r = 8 case of the proved simple_graph_card_le_choose_add_one_of_regular_triangle_distinct is the same bound.

Every 8-regular triangle-distinct graph has at most 29 vertices: its triangle-degrees are pairwise distinct and each is at most C(8, 2) = 28.
-/

theorem card_le_twenty_nine_of_regular_eight_triangle_distinct {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree 8)
    (htd : simple_graph_is_triangle_distinct G) : Fintype.card V ≤ 29 := by
  have hmaps : ∀ v ∈ (Finset.univ : Finset V),
      simple_graph_triangle_degree G v ∈ Finset.range 29 := by
    intro v _
    have h1 := simple_graph_triangle_degree_le_choose G v
    rw [hreg v] at h1
    simp only [Finset.mem_range]
    have : (8 : ℕ).choose 2 = 28 := by decide
    omega
  have := Finset.card_le_card_of_injOn _ hmaps (htd.injOn)
  simpa using this
