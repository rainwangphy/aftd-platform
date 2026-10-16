import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.SimpleGraphIsColorConnecting
import AFTD.Kb.Tcs.SimpleGraphWildNumberLeOfIsColorConnecting

/-!
# wild_number_complete_graph_le_sub_one

Topic: graphs   Node: c7340483f4b1

Provenance: formalization of a published result. Source: arXiv:2610.22142 (Wild number for spanning trees in complete and complete bipartite graphs), Sec. 2, inequality (1) (0 ≤ wld_γ(G) ≤ n − 1 for an n-vertex connected graph), here for K_n.

For every n ≥ 1 and every edge colouring γ of K_n, wld_γ(K_n) ≤ n − 1 (a spanning star is colour-connecting).
-/

theorem wild_number_complete_graph_le_sub_one {α : Type*} (n : ℕ) (hn : 1 ≤ n)
    (γ : (⊤ : SimpleGraph (Fin n)).edgeSet → α) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) γ ≤ n - 1 := by
  classical
  let z : Fin n := ⟨0, by omega⟩
  let W : Finset (Sym2 (Fin n)) := (Finset.univ.erase z).image fun j => s(z, j)
  have hW : simple_graph_is_color_connecting (⊤ : SimpleGraph (Fin n)) γ ↑W := by
    refine ⟨?_, fun e => ?_⟩
    · intro f hf
      simp only [W, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase] at hf
      obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hf
      simpa using Ne.symm hj
    · rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨z, fun y => ?_⟩
      by_cases hy : y = z
      · rw [hy]
      apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨Or.inr ?_, Ne.symm hy⟩
      simp only [W, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_erase,
        Finset.mem_univ, and_true]
      exact ⟨y, hy, rfl⟩
  refine (simple_graph_wild_number_le_of_is_color_connecting _ γ W hW).trans ?_
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
