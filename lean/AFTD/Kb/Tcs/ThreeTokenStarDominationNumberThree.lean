import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphDominationNumber
import AFTD.Kb.Tcs.ThreeTokenStarDominationNumberThreeLe
import AFTD.Kb.Tcs.SimpleGraphIsDominating

/-!
# three_token_star_domination_number_three

Topic: graphs   Node: 91fbefd9ef59

Provenance: formalization of a published result. Source: arXiv:2611.11191, Subsection 4.4

The domination number of the 3-token graph of the star graph SimpleGraph.starGraph (none : Option (Fin 3)) is 1.
-/

/-- The domination number of the 3-token graph of the star graph S_3 is 1. -/
theorem three_token_star_domination_number_three :
    simple_graph_domination_number (token_graph (SimpleGraph.starGraph (none : Option (Fin 3))) 3) = 1 := by
  apply le_antisymm three_token_star_domination_number_three_le
  unfold simple_graph_domination_number
  set V := { s : Finset (Option (Fin 3)) // s.card = 3 }
  have hne : {k : ℕ | ∃ S : Finset V,
      simple_graph_is_dominating (token_graph (SimpleGraph.starGraph none) 3) (↑S : Set V) ∧ S.card = k}.Nonempty := by
    let v1 : V := ⟨{some 0, some 1, some 2}, by decide⟩
    let S : Finset V := {v1}
    have hdom : simple_graph_is_dominating (token_graph (SimpleGraph.starGraph none) 3) (↑S : Set V) := by
      intro v
      dsimp only [S, v1]
      unfold token_graph SimpleGraph.starGraph
      dsimp only
      revert v
      decide
    exact ⟨1, S, hdom, by decide⟩
  have hmem := Nat.sInf_mem hne
  dsimp at hmem
  rcases hmem with ⟨S, hdom, hcard⟩
  rw [← hcard]
  by_contra h0
  have hS_empty : S = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  let v0 : V := ⟨{some 0, some 1, some 2}, by decide⟩
  have hv := hdom v0
  rw [hS_empty] at hv
  simp at hv
