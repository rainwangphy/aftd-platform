import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenDominationNumberGeCeilHalf
import AFTD.Kb.Tcs.TwoTokenDominationNumberEvenMatchingLe
import AFTD.Kb.Tcs.TwoTokenDominationNumberOddP3MatchingLe
import AFTD.Kb.Tcs.SimpleGraphDominationNumber
import AFTD.Kb.Tcs.TokenGraph

/-!
# two_token_domination_number_bound

Topic: graphs   Node: 4f9f7a474dc6

Provenance: formalization of a published result. Source: arXiv:2611.15124, Theorem 1.3

Let G be a finite simple graph on vertex type V with domination number at least 2. Then the domination number of the 2-token graph F_2(G) is at least (Fintype.card V + 1) / 2. Furthermore, if the complement graph Gᶜ is 1-regular, or has a vertex of degree 2 with all other vertices having degree 1, then the domination number of F_2(G) equals (Fintype.card V + 1) / 2.
-/

open scoped Classical in
/-- Lower bound on the domination number of 2-token graphs for graphs without universal vertices, with equality for graphs whose complement is a 1-factor or P_3 union disjoint edges. -/
theorem two_token_domination_number_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hγ : 2 ≤ simple_graph_domination_number G) :
    (Fintype.card V + 1) / 2 ≤ simple_graph_domination_number (token_graph G 2) ∧
    ((Gᶜ.IsRegularOfDegree 1 ∨
      ∃ v : V, Gᶜ.degree v = 2 ∧ ∀ u : V, u ≠ v → Gᶜ.degree u = 1) →
     simple_graph_domination_number (token_graph G 2) = (Fintype.card V + 1) / 2) := by
  have h_ge := two_token_domination_number_ge_ceil_half G hγ
  refine ⟨h_ge, fun h_or => ?_⟩
  rcases h_or with h1 | h2
  · have h_le := two_token_domination_number_even_matching_le G h1
    omega
  · have h_le := two_token_domination_number_odd_p3_matching_le G h2
    omega
