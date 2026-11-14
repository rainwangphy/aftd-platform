import AFTD.Prelude
import AFTD.Kb.Tcs.TwoTokenDominatingSetCardGeCeilHalf
import AFTD.Kb.Tcs.SimpleGraphIsDominating
import AFTD.Kb.Tcs.TokenGraph
import AFTD.Kb.Tcs.SimpleGraphDominationNumber

/-!
# two_token_domination_number_ge_ceil_half

Topic: graphs   Node: 46e2c7a46f66

Provenance: formalization of a published result. Source: arXiv:2611.15124, Theorem 1.3

Let G be a finite simple graph on vertex type V with domination number at least 2. Then the domination number of the 2-token graph F_2(G) is at least (Fintype.card V + 1) / 2.
-/

/-- The domination number of F_2(G) is at least ceil(n/2) when G has domination number at least 2. -/
theorem two_token_domination_number_ge_ceil_half {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hγ : 2 ≤ simple_graph_domination_number G) :
    (Fintype.card V + 1) / 2 ≤ simple_graph_domination_number (token_graph G 2) := by
  unfold simple_graph_domination_number
  have hne : {k | ∃ S : Finset { s : Finset V // s.card = 2 },
      simple_graph_is_dominating (token_graph G 2) ↑S ∧ S.card = k}.Nonempty := by
    use (Finset.univ : Finset { s : Finset V // s.card = 2 }).card
    refine ⟨Finset.univ, ?_, rfl⟩
    intro v
    left
    simp
  have hmem := Nat.sInf_mem hne
  dsimp at hmem
  rcases hmem with ⟨S, hdom, hcard⟩
  rw [← hcard]
  exact two_token_dominating_set_card_ge_ceil_half G hγ S hdom
