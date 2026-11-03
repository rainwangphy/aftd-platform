import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRamseyThreeKOfDegreeGe

/-!
# simple_graph_ramsey_three_ten_forty_of_exists_degree_ge_ten

Topic: combinatorics   Node: 5fbe489303ee

Provenance: helper lemma. step towards simple_graph_ramsey_three_ten_forty

Any simple graph on 40 vertices having a vertex of degree at least 10 contains a triangle or an independent set of size 10.
-/

/-- Any simple graph on 40 vertices with a vertex of degree at least 10 contains a triangle or an independent set of size 10. -/
theorem simple_graph_ramsey_three_ten_forty_of_exists_degree_ge_ten (g : SimpleGraph (Fin 40))
    [DecidableRel g.Adj] (h : ∃ v, 10 ≤ g.degree v) :
    ¬ g.CliqueFree 3 ∨ ¬ gᶜ.CliqueFree 10 := by
  obtain ⟨v, hv⟩ := h
  exact simple_graph_ramsey_three_k_of_degree_ge g v hv
