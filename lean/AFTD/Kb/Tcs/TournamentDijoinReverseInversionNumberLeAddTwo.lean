import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.TournamentDijoinSwapInversionNumberEqReverse
import AFTD.Kb.Tcs.TournamentDijoinInversionNumberLeSymmAddTwo

/-!
# tournament_dijoin_reverse_inversion_number_le_add_two

Topic: graphs   Node: d312fcaa2fa4

Provenance: helper lemma. step towards tournament_dijoin_reverse_inversion_number_le

For finite tournaments D₁ and D₂, inv(D₁ → D₂) ≤ inv(D̄₁ → D̄₂) + 2.
-/

/-- For finite tournaments D₁ and D₂, the inversion number of D₁ → D₂ is at most that of D̄₁ → D̄₂ plus 2. -/
theorem tournament_dijoin_reverse_inversion_number_le_add_two
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) ≤
      digraph_inversion_number (digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂)) + 2 := by
  rw [← tournament_dijoin_swap_inversion_number_eq_reverse V W D₁ D₂ h₁ h₂]
  exact tournament_dijoin_inversion_number_le_symm_add_two V W D₁ D₂ h₁ h₂
