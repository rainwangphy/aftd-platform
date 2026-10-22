import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphReverseIsTournament
import AFTD.Kb.Tcs.TournamentInversionNumberLeDijoin
import AFTD.Kb.Tcs.TournamentInversionNumberReverse

/-!
# tournament_dijoin_reverse_inversion_number_le_of_eq_max

Topic: graphs   Node: a2ef40f6d6fa

Provenance: helper lemma. step towards tournament_dijoin_reverse_inversion_number_le

Whenever inv(D₁ → D₂) attains its theoretical minimum max(inv(D₁), inv(D₂)), the inequality inv(D₁ → D₂) ≤ inv(D̄₁ → D̄₂) holds.
-/

/-- Whenever inv(D₁ → D₂) = max(inv(D₁), inv(D₂)), inv(D₁ → D₂) ≤ inv(D̄₁ → D̄₂). -/
theorem tournament_dijoin_reverse_inversion_number_le_of_eq_max
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂)
    (hmax : digraph_inversion_number (digraph_dijoin D₁ D₂) =
      max (digraph_inversion_number D₁) (digraph_inversion_number D₂)) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) ≤
      digraph_inversion_number (digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂)) := by
  rw [hmax]
  have hrev₁ := digraph_reverse_is_tournament D₁ h₁
  have hrev₂ := digraph_reverse_is_tournament D₂ h₂
  have hle := tournament_inversion_number_le_dijoin V W (digraph_reverse D₁) (digraph_reverse D₂) hrev₁ hrev₂
  rw [tournament_inversion_number_reverse V D₁ h₁, tournament_inversion_number_reverse W D₂ h₂] at hle
  exact hle
