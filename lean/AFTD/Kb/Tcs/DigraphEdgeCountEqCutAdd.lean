import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_edge_count_eq_cut_add

Topic: graphs   Node: cd7a10177098

Provenance: helper lemma. Sanity lemma for directed cuts, arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 1.

For any vertex set A, the edges of a digraph split into those inside A, from A to its complement, from the complement to A, and inside the complement.
-/

theorem digraph_edge_count_eq_cut_add {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (A : Finset V) :
    digraph_edge_count G = digraph_cut_count G A A + digraph_cut_count G A Aᶜ +
      digraph_cut_count G Aᶜ A + digraph_cut_count G Aᶜ Aᶜ := by
  simp only [digraph_edge_count, digraph_cut_count, Finset.card_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_product,
    Finset.sum_product, Finset.sum_product]
  rw [← Finset.sum_add_sum_compl A]
  simp only [← Finset.sum_add_sum_compl A, Finset.sum_add_distrib]
  ring
