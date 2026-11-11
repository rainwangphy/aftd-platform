import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.SimpleGraphDominationNumber

/-!
# three_token_star_domination_number_three_le

Topic: graphs   Node: e1b6347dd25d

Provenance: helper lemma. arXiv:2611.11191, Subsection 4.4

The domination number of the 3-token graph of the star graph SimpleGraph.starGraph (none : Option (Fin 3)) is at most 1.
-/

/-- The domination number of the 3-token graph of the star graph S_3 is at most 1. -/
theorem three_token_star_domination_number_three_le :
    simple_graph_domination_number (token_graph (SimpleGraph.starGraph (none : Option (Fin 3))) 3) ≤ 1 := by
  let v1 : { s : Finset (Option (Fin 3)) // s.card = 3 } := ⟨{some 0, some 1, some 2}, by decide⟩
  let S : Finset { s : Finset (Option (Fin 3)) // s.card = 3 } := {v1}
  have hdom : simple_graph_is_dominating (token_graph (SimpleGraph.starGraph (none : Option (Fin 3))) 3)
      (S : Set _) := by
    intro v
    dsimp only [S, v1]
    unfold token_graph SimpleGraph.starGraph
    dsimp only
    revert v
    decide
  have hc : S.card = 1 := by decide
  exact Nat.sInf_le ⟨S, hdom, hc⟩
