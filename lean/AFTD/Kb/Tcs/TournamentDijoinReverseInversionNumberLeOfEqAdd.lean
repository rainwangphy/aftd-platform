import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.TournamentDijoinInversionNumberLeAdd

/-!
# tournament_dijoin_reverse_inversion_number_le_of_eq_add

Topic: graphs   Node: e6210a311ee4

Provenance: helper lemma. step towards tournament_dijoin_reverse_inversion_number_le

Whenever inv(D̄₁ → D̄₂) attains its theoretical maximum inv(D₁) + inv(D₂), the inequality inv(D₁ → D₂) ≤ inv(D̄₁ → D̄₂) holds.
-/

/-- Whenever inv(D̄₁ → D̄₂) = inv(D₁) + inv(D₂), inv(D₁ → D₂) ≤ inv(D̄₁ → D̄₂). -/
theorem tournament_dijoin_reverse_inversion_number_le_of_eq_add
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂)
    (hadd : digraph_inversion_number (digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂)) =
      digraph_inversion_number D₁ + digraph_inversion_number D₂) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) ≤
      digraph_inversion_number (digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂)) := by
  rw [hadd]
  exact tournament_dijoin_inversion_number_le_add V W D₁ D₂ h₁ h₂
