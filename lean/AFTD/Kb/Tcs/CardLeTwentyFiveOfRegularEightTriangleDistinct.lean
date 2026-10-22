import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEightRegularTriangleDegreeLeTwentyFour
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# card_le_twenty_five_of_regular_eight_triangle_distinct

Topic: graphs   Node: 9ebc93346155

Provenance: helper lemma. step towards regular_eight_triangle_distinct_witness

Every 8-regular triangle-distinct graph has at most 25 vertices, since its vertex triangle-degrees are pairwise distinct elements of {0, ..., 24}.
-/

/-- Every 8-regular triangle-distinct graph has at most 25 vertices. -/
theorem card_le_twenty_five_of_regular_eight_triangle_distinct {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 8) (htd : simple_graph_is_triangle_distinct G) :
    Fintype.card V ≤ 25 := by
  have hinj : Function.Injective (fun v => simple_graph_triangle_degree G v) := htd
  have h1 : (Finset.univ.image (fun v => simple_graph_triangle_degree G v)).card = Fintype.card V := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have h2 : (Finset.univ.image (fun v => simple_graph_triangle_degree G v)).card ≤ 25 := by
    have hsub : (Finset.univ.image (fun v => simple_graph_triangle_degree G v)) ⊆ Finset.Iic 24 := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨v, rfl⟩ := hx
      exact Finset.mem_Iic.mpr (simple_graph_eight_regular_triangle_degree_le_twenty_four G hreg htd v)
    calc (Finset.univ.image (fun v => simple_graph_triangle_degree G v)).card ≤ (Finset.Iic 24).card := Finset.card_le_card hsub
      _ = 25 := by simp
  omega
