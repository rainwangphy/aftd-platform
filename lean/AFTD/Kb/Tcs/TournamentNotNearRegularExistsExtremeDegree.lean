import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsNearRegular
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_not_near_regular_exists_extreme_degree

Topic: graphs   Node: efeb8de4fd0e

Provenance: helper lemma. step towards even_tournament_arborescence_maximizer_is_near_regular

In any tournament on 2m vertices with m ≥ 1 that is not near-regular, there exists a vertex with out-degree ≥ m + 1 or out-degree ≤ m - 2.
-/

/-- A tournament of order 2m that is not near-regular has at least one vertex of out-degree >= m + 1 or out-degree <= m - 2. -/
theorem tournament_not_near_regular_exists_extreme_degree (m : ℕ) (hm : 1 ≤ m)
    (T : Digraph (Fin (2 * m))) [DecidableRel T.Adj]
    (hnr : ¬ tournament_is_near_regular m T) :
    (∃ v : Fin (2 * m), m + 1 ≤ digraph_out_count T v) ∨
    (∃ v : Fin (2 * m), digraph_out_count T v ≤ m - 2) := by
  simp only [tournament_is_near_regular, not_forall, not_or] at hnr
  obtain ⟨v, hv1, hv2⟩ := hnr
  by_cases h : digraph_out_count T v ≤ m - 2
  · exact Or.inr ⟨v, h⟩
  · exact Or.inl ⟨v, by omega⟩
