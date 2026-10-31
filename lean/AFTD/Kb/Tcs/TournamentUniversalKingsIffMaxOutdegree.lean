import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentNotKingOfCovered
import AFTD.Kb.Tcs.TournamentIsKingOfMaxOutdegree
import AFTD.Kb.Tcs.TournamentExistsCoveringRealization
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutCount

/-!
# tournament_universal_kings_iff_max_outdegree

Topic: graphs   Node: 47fddf58491b

Provenance: formalization of a published result. Source: arXiv:2610.40521 Corollary 7

For every realizable degree vector d of an n-vertex tournament and every vertex v, v is a king in every tournament realizing d if and only if v has maximum outdegree according to d (that is, d u ≤ d v for all vertices u).
-/

open Classical in
/-- The universal kings of a realizable tournament degree vector are exactly the vertices of maximum outdegree. -/
theorem tournament_universal_kings_iff_max_outdegree (n : ℕ) (d : Fin n → ℕ)
    (hd : ∃ T : Digraph (Fin n), digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i)
    (v : Fin n) :
    (∀ T : Digraph (Fin n), (digraph_is_tournament T ∧ ∀ i : Fin n, digraph_out_count T i = d i) →
      (∀ u, u ≠ v → T.Adj v u ∨ ∃ w, T.Adj v w ∧ T.Adj w u)) ↔
      ∀ u : Fin n, d u ≤ d v := by
  constructor
  · intro hall
    by_contra hc
    push Not at hc
    obtain ⟨w, hw⟩ := hc
    obtain ⟨T, ⟨hT, hdT⟩, hcov⟩ := tournament_exists_covering_realization d hd v w hw
    have hking := hall T ⟨hT, hdT⟩
    have hnotking := tournament_not_king_of_covered T hT w v hcov
    exact hnotking hking
  · intro hmax T ⟨hT, hdT⟩
    apply tournament_is_king_of_max_outdegree T hT v
    intro u
    rw [hdT u, hdT v]
    exact hmax u
