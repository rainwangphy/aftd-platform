import AFTD.Prelude
import AFTD.Kb.Tcs.CardFilterSingletonProd
import AFTD.Kb.Tcs.CardFilterProdSingleton
import AFTD.Kb.Tcs.GreedyCutFinsetBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# greedy_max_cut_half_edges_lower_bound

Topic: approximation   Node: f6472667d3cc

Provenance: formalization of a published result. Source: Erdős (1965), 'On even subgraphs of graphs'; Vazirani (2001), Approximation Algorithms, Theorem 2.1

Every finite simple graph G has a subset of vertices S such that the number of cut edges between S and V \ S is at least half the total number of edges in G: G.edgeFinset.card ≤ 2 * ((S ×ˢ Sᶜ).filter (fun ⟨u, v⟩ => G.Adj u v)).card.
-/

/-- Every finite simple graph has a cut containing at least half of its edges. -/
theorem greedy_max_cut_half_edges_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset V, G.edgeFinset.card ≤ 2 * ((S ×ˢ Sᶜ).filter (fun ⟨u, v⟩ => G.Adj u v)).card := by
  obtain ⟨S, -, hS⟩ := greedy_cut_finset_bound G (Finset.univ : Finset V)
  use S
  rw [Finset.univ_product_univ] at hS
  rw [← G.two_mul_card_edgeFinset] at hS
  rw [Finset.compl_eq_univ_sdiff]
  have h_arith : ∀ a b : ℕ, 2 * a ≤ 4 * b → a ≤ 2 * b := by
    intro a b h
    linarith
  exact h_arith _ _ hS
