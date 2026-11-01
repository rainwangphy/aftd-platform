import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDominationNumber
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating

/-!
# three_token_k2n_domination_number_four_le

Topic: graphs   Node: d8cecc99aedf

Provenance: helper lemma. step towards three_token_k2n_domination_number_four

The domination number of the 3-token graph F_3(K_{2,4}) of the complete bipartite graph K_{2,4} is at most 4.
-/

/-- The domination number of the 3-token graph F_3(K_{2,4}) is at most 4. -/
theorem three_token_k2n_domination_number_four_le :
    simple_graph_domination_number (token_graph (completeBipartiteGraph (Fin 2) (Fin 4)) 3) ≤ 4 := by
  let v1 : { s : Finset (Fin 2 ⊕ Fin 4) // s.card = 3 } := ⟨{Sum.inl 0, Sum.inl 1, Sum.inr 1}, by decide⟩
  let v2 : { s : Finset (Fin 2 ⊕ Fin 4) // s.card = 3 } := ⟨{Sum.inl 0, Sum.inr 1, Sum.inr 2}, by decide⟩
  let v3 : { s : Finset (Fin 2 ⊕ Fin 4) // s.card = 3 } := ⟨{Sum.inl 1, Sum.inr 0, Sum.inr 3}, by decide⟩
  let v4 : { s : Finset (Fin 2 ⊕ Fin 4) // s.card = 3 } := ⟨{Sum.inr 0, Sum.inr 2, Sum.inr 3}, by decide⟩
  let S : Finset { s : Finset (Fin 2 ⊕ Fin 4) // s.card = 3 } := {v1, v2, v3, v4}
  have hdom : simple_graph_is_dominating (token_graph (completeBipartiteGraph (Fin 2) (Fin 4)) 3) (S : Set _) := by
    intro v
    dsimp only [S, v1, v2, v3, v4]
    unfold token_graph completeBipartiteGraph
    dsimp only
    revert v
    decide
  have hc : S.card = 4 := by decide
  exact Nat.sInf_le ⟨S, hdom, hc⟩
