import AFTD.Prelude
import AFTD.Kb.Tcs.CardGeneralizedKneserGraphVerts

/-!
# card_three_subsets_fin

Topic: graphs   Node: e6da92d4b432

Provenance: helper lemma. step towards three_token_odd_cycle_indep_num_le

The number of 3-element subsets of Fin n is n.choose 3.
-/

/-- The number of 3-element subsets of Fin n is n.choose 3. -/
theorem card_three_subsets_fin (n : ℕ) :
    Fintype.card { s : Finset (Fin n) // s.card = 3 } = n.choose 3 := by first | exact card_generalized_kneser_graph_verts | (apply card_generalized_kneser_graph_verts <;> assumption) | (apply card_generalized_kneser_graph_verts <;> simp_all) | simpa using card_generalized_kneser_graph_verts
