import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentOfSymmMatrix
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# tournament_of_symm_matrix_is_tournament

Topic: graphs   Node: be9257216eca

Provenance: helper lemma. Sanity lemma for tournament_of_symm_matrix (arXiv:2610.13798).

T(G) is a tournament for every matrix G over F₂ (only the entries above the diagonal are read).
-/

theorem tournament_of_symm_matrix_is_tournament {n : ℕ} (G : Matrix (Fin n) (Fin n) (ZMod 2)) :
    digraph_is_tournament (tournament_of_symm_matrix G) := by
  have two : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [tournament_of_symm_matrix]
  · simp only [tournament_of_symm_matrix]
    rcases lt_or_gt_of_ne hij with h | h
    · rcases two (G i j) with h0 | h0 <;> simp [h, h0, not_lt_of_gt h]
    · rcases two (G j i) with h0 | h0 <;> simp [h, h0, not_lt_of_gt h]
