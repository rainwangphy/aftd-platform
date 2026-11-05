import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedKneserGraph
import AFTD.Kb.Tcs.ExistsFiveFinsetsCard

/-!
# card_generalized_kneser_graph_verts

Topic: graphs   Node: 888032e21d75

Provenance: helper lemma. step towards op_1006_generalized_kneser_chromatic_eq_fourteen

The vertex type of the generalized Kneser graph KG(2n, n, r), which consists of all n-element subsets of Fin (2 * n), has cardinality Nat.choose (2 * n) n.
-/

/-- The number of vertices in the generalized Kneser graph KG(2n, n, r) is (2n choose n). -/
theorem card_generalized_kneser_graph_verts (n : ℕ) :
    Fintype.card {s : Finset (Fin (2 * n)) // s.card = n} = Nat.choose (2 * n) n := by first | exact exists_five_finsets_card | (apply exists_five_finsets_card <;> assumption) | (apply exists_five_finsets_card <;> simp_all) | simpa using exists_five_finsets_card
