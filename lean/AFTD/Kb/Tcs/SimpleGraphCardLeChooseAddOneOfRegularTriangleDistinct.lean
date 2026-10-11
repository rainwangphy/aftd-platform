import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegreeLeChoose
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_card_le_choose_add_one_of_regular_triangle_distinct

Topic: graphs   Node: ab52776f9670

Provenance: helper lemma. Pigeonhole bound used for OP-123 (arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine), Sec. 1).

An r-regular triangle-distinct graph has at most C(r, 2) + 1 vertices: its triangle-degrees are pairwise distinct and lie in {0, …, C(r, 2)}.
-/

theorem simple_graph_card_le_choose_add_one_of_regular_triangle_distinct {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (hreg : G.IsRegularOfDegree r) (htd : simple_graph_is_triangle_distinct G) :
    Fintype.card V ≤ r.choose 2 + 1 := by
  have hmaps : ∀ v ∈ (Finset.univ : Finset V),
      simple_graph_triangle_degree G v ∈ Finset.range (r.choose 2 + 1) := by
    intro v _
    have h1 := simple_graph_triangle_degree_le_choose G v
    rw [hreg v] at h1
    rw [Finset.mem_range]
    omega
  have := Finset.card_le_card_of_injOn _ hmaps htd.injOn
  simpa using this
