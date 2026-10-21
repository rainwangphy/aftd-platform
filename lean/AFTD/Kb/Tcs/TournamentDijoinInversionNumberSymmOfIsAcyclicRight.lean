import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphInversionNumberEqZeroOfIsAcyclic
import AFTD.Kb.Tcs.TournamentDijoinInversionNumberLeAdd
import AFTD.Kb.Tcs.TournamentInversionNumberLeDijoin

/-!
# tournament_dijoin_inversion_number_symm_of_is_acyclic_right

Topic: graphs   Node: 57d4630786be

Provenance: helper lemma. step towards tournament_dijoin_inversion_number_symm

The symmetry inv(D₁ → D₂) = inv(D₂ → D₁) holds when D₂ is acyclic: both sides equal inv(D₁).
-/

/-- The symmetry inv(D₁ → D₂) = inv(D₂ → D₁) holds when D₂ is acyclic (a transitive tournament): both sides equal inv(D₁). -/
theorem tournament_dijoin_inversion_number_symm_of_is_acyclic_right
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂)
    (hac : digraph_is_acyclic D₂) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) =
      digraph_inversion_number (digraph_dijoin D₂ D₁) := by
  have h2_zero := digraph_inversion_number_eq_zero_of_is_acyclic D₂ hac
  have h_le1 := tournament_dijoin_inversion_number_le_add V W D₁ D₂ h₁ h₂
  have h_ge1 := tournament_inversion_number_le_dijoin V W D₁ D₂ h₁ h₂
  have h_le2 := tournament_dijoin_inversion_number_le_add W V D₂ D₁ h₂ h₁
  have h_ge2 := tournament_inversion_number_le_dijoin W V D₂ D₁ h₂ h₁
  omega
