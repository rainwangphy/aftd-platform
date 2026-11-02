import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentRealizes
import AFTD.Kb.Tcs.TournamentCovers
import AFTD.Kb.Tcs.TournamentExistsCoveringRealization
import AFTD.Kb.Tcs.DigraphOutCount
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_exists_covering_realization_of_realizes

Topic: graphs   Node: 966cca86734a

Provenance: formalization of a published result. Source: arXiv:2610.40521 Lemma 6 -- Directed Cut-Query Complexity of Finding a King

Let d be a degree vector on Fin n realized by a tournament T, and let v, w be vertices in Fin n satisfying d v < d w. Then there exists a tournament T' on Fin n realizing d in which w covers v.
-/

open Classical in
/-- A tournament realizing degree vector d can be modified to another tournament realizing d in which w covers v, provided d v < d w. -/
theorem tournament_exists_covering_realization_of_realizes {n : ℕ}
    (d : Fin n → ℕ) (T : Digraph (Fin n)) (hT : tournament_realizes n T d)
    (v w : Fin n) (hvw : d v < d w) :
    ∃ T' : Digraph (Fin n), tournament_realizes n T' d ∧ tournament_covers T' w v := tournament_exists_covering_realization d ⟨T, hT⟩ v w hvw
