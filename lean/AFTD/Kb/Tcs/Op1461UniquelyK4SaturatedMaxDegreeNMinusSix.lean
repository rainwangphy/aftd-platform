import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniquelyCliqueSaturated
import AFTD.Kb.Tcs.UniquelyK4SaturatedMaxDegreeSixOrderTwelve

/-!
# op_1461_uniquely_k4_saturated_max_degree_n_minus_six

Topic: graphs   Node: 93a0c555a4b5

Provenance: formalization of a published result. Source: arXiv:2611.13656 Sec. 3

There exists a natural number n ≥ 7 and a simple graph G on Fin n such that G is uniquely K_4-saturated and the maximum degree of G equals n - 6.
-/

open scoped Classical in
/-- Existence of a uniquely K_4-saturated graph on n vertices with maximum degree n - 6 for some n ≥ 7 (OP-1461). -/
theorem op_1461_uniquely_k4_saturated_max_degree_n_minus_six :
    ∃ (n : ℕ), 7 ≤ n ∧ ∃ (G : SimpleGraph (Fin n)),
      is_uniquely_clique_saturated G 4 ∧ G.maxDegree = n - 6 := by
  obtain ⟨G, hG⟩ := uniquely_k4_saturated_max_degree_six_order_twelve
  exact ⟨12, by decide, G, hG⟩
