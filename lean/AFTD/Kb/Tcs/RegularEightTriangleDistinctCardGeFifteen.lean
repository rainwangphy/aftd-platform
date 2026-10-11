import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphComplRegularTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphCardLeChooseAddOneOfRegularTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct

/-!
# regular_eight_triangle_distinct_card_ge_fifteen

Topic: graphs   Node: 537287056af5

Provenance: helper lemma. Partial result towards OP-123 (arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine), Lemma 2.1 complementation and Sec. 1); the earlier work cited there narrows the regularity-8 case further, to six orders.

Every 8-regular triangle-distinct graph with at least one vertex has at least 15 vertices: its complement is (n − 9)-regular and triangle-distinct, so n ≤ C(n − 9, 2) + 1, which fails for 9 ≤ n ≤ 14.
-/

theorem regular_eight_triangle_distinct_card_ge_fifteen {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree 8)
    (htd : simple_graph_is_triangle_distinct G) : 15 ≤ Fintype.card V := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have h9 : 9 ≤ Fintype.card V := by
    have := G.degree_lt_card_verts v
    rw [hreg v] at this
    omega
  obtain ⟨hcreg, hctd⟩ :=
    simple_graph_compl_regular_triangle_distinct G 8 (Fintype.card V) rfl hreg htd
  have hb := simple_graph_card_le_choose_add_one_of_regular_triangle_distinct Gᶜ _ hcreg hctd
  by_contra hlt
  push Not at hlt
  interval_cases h : Fintype.card V <;> simp_all [Nat.choose]
