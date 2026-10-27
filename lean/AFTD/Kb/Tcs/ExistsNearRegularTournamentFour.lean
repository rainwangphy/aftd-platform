import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsNearRegular
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# exists_near_regular_tournament_four

Topic: graphs   Node: 718735ddf88b

Provenance: helper lemma. folklore

There exists a near-regular tournament on 4 vertices.
-/

def exists_near_regular_tournament_four_adj_bool (i j : Fin 4) : Bool :=
  match i, j with
  | 0, 1 => true
  | 0, 2 => true
  | 3, 0 => true
  | 1, 2 => true
  | 1, 3 => true
  | 2, 3 => true
  | _, _ => false

def exists_near_regular_tournament_four_T : Digraph (Fin 4) :=
  ⟨fun i j => exists_near_regular_tournament_four_adj_bool i j = true⟩

instance exists_near_regular_tournament_four_dec :
    DecidableRel exists_near_regular_tournament_four_T.Adj :=
  fun i j => inferInstanceAs (Decidable (exists_near_regular_tournament_four_adj_bool i j = true))

/-- Witness that near-regular tournaments of order 4 exist. -/
theorem exists_near_regular_tournament_four :
    ∃ (T : Digraph (Fin 4)) (_ : DecidableRel T.Adj),
      digraph_is_tournament T ∧ tournament_is_near_regular 2 T := by
  refine ⟨exists_near_regular_tournament_four_T, exists_near_regular_tournament_four_dec, ?_, ?_⟩
  · dsimp [digraph_is_tournament, exists_near_regular_tournament_four_T]
    decide
  · dsimp [tournament_is_near_regular, digraph_out_count, exists_near_regular_tournament_four_T]
    decide
