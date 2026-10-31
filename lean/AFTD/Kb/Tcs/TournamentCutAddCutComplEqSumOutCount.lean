import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_cut_add_cut_compl_eq_sum_out_count

Topic: graphs   Node: 2411c45a9a34

Provenance: helper lemma. arXiv:2610.40521 Lemma 2 proof

In any directed graph T on vertex set Fin n and for any subset S of vertices, the number of directed edges within S plus the number of directed edges from S to its complement Sᶜ equals the sum of the outdegrees of the vertices in S.
-/

open Classical in
/-- Edges originating in a vertex subset S split into edges within S and edges from S to Sᶜ. -/
lemma tournament_cut_add_cut_compl_eq_sum_out_count (n : ℕ) (T : Digraph (Fin n)) (S : Finset (Fin n)) :
    digraph_cut_count T S S + digraph_cut_count T S Sᶜ = ∑ v ∈ S, digraph_out_count T v := by
  simp only [digraph_cut_count, digraph_out_count, Finset.card_filter]
  rw [Finset.sum_product, Finset.sum_product]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.sum_add_sum_compl S]
