import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsNearRegular
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# exists_not_near_regular_tournament_four

Topic: graphs   Node: abb4cd38b679

Provenance: helper lemma. folklore

There exists a tournament on 4 vertices that is not near-regular.
-/

/-- Witness that not all tournaments of order 4 are near-regular. -/
theorem exists_not_near_regular_tournament_four :
    ∃ (T : Digraph (Fin 4)) (_ : DecidableRel T.Adj),
      digraph_is_tournament T ∧ ¬ tournament_is_near_regular 2 T := by
  let D : Digraph (Fin 4) := ⟨fun i j => i < j⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · infer_instance
  · dsimp [D, digraph_is_tournament]
    constructor
    · intro x; exact lt_irrefl x
    · intro x y hxy
      constructor <;> intro h <;> omega
  · intro h
    have h0 := h 0
    have hc : digraph_out_count D 0 = 3 := by decide
    rw [hc] at h0
    omega
