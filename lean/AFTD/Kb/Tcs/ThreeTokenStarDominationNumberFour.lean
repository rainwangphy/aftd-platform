import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.SimpleGraphDominationNumber

/-!
# three_token_star_domination_number_four

Topic: graphs   Node: 4bcdd8506355

Provenance: formalization of a published result. Source: arXiv:2611.11191, Subsection 4.4

The domination number of the 3-token graph of the star graph SimpleGraph.starGraph (none : Option (Fin 4)) is 3.
-/

def three_token_star_domination_number_four_v1 : { s : Finset (Option (Fin 4)) // s.card = 3 } :=
  ⟨{(none : Option (Fin 4)), some 0, some 1}, by decide⟩

def three_token_star_domination_number_four_v2 : { s : Finset (Option (Fin 4)) // s.card = 3 } :=
  ⟨{some 0, some 2, some 3}, by decide⟩

def three_token_star_domination_number_four_v3 : { s : Finset (Option (Fin 4)) // s.card = 3 } :=
  ⟨{some 1, some 2, some 3}, by decide⟩

def three_token_star_domination_number_four_S : Finset { s : Finset (Option (Fin 4)) // s.card = 3 } :=
  {three_token_star_domination_number_four_v1,
   three_token_star_domination_number_four_v2,
   three_token_star_domination_number_four_v3}

theorem three_token_star_domination_number_four_le :
    simple_graph_domination_number (token_graph (SimpleGraph.starGraph (none : Option (Fin 4))) 3) ≤ 3 := by
  have hdom : simple_graph_is_dominating (token_graph (SimpleGraph.starGraph (none : Option (Fin 4))) 3)
      (three_token_star_domination_number_four_S : Set _) := by
    intro v
    dsimp only [three_token_star_domination_number_four_S,
                three_token_star_domination_number_four_v1,
                three_token_star_domination_number_four_v2,
                three_token_star_domination_number_four_v3]
    unfold token_graph SimpleGraph.starGraph
    dsimp only
    revert v
    decide
  have hc : three_token_star_domination_number_four_S.card = 3 := by decide
  exact Nat.sInf_le ⟨three_token_star_domination_number_four_S, hdom, hc⟩

set_option maxRecDepth 2000000 in
theorem three_token_star_domination_number_four_no_dom_two :
    ∀ S : Finset { s : Finset (Option (Fin 4)) // s.card = 3 },
      S.card ≤ 2 → ¬ simple_graph_is_dominating (token_graph (SimpleGraph.starGraph (none : Option (Fin 4))) 3) (S : Set _) := by
  unfold simple_graph_is_dominating token_graph SimpleGraph.starGraph
  dsimp only
  decide

theorem three_token_star_domination_number_four_ge :
    3 ≤ simple_graph_domination_number (token_graph (SimpleGraph.starGraph (none : Option (Fin 4))) 3) := by
  unfold simple_graph_domination_number
  have hne : {k | ∃ S : Finset { s : Finset (Option (Fin 4)) // s.card = 3 },
      simple_graph_is_dominating (token_graph (SimpleGraph.starGraph (none : Option (Fin 4))) 3) ↑S ∧ S.card = k}.Nonempty := by
    use (Finset.univ : Finset { s : Finset (Option (Fin 4)) // s.card = 3 }).card
    refine ⟨Finset.univ, ?_, rfl⟩
    intro v
    left
    exact Finset.mem_univ v
  have hmem := Nat.sInf_mem hne
  dsimp at hmem
  rcases hmem with ⟨S, hdom, hcard⟩
  rw [← hcard]
  by_contra hlt
  have hle : S.card ≤ 2 := Nat.le_of_lt_succ (not_le.mp hlt)
  exact three_token_star_domination_number_four_no_dom_two S hle hdom

/-- The domination number of the 3-token graph of the star graph S_4 is 3. -/
theorem three_token_star_domination_number_four :
    simple_graph_domination_number (token_graph (SimpleGraph.starGraph (none : Option (Fin 4))) 3) = 3 := le_antisymm three_token_star_domination_number_four_le three_token_star_domination_number_four_ge
