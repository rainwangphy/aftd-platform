import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.TournamentDijoinSwapInversionNumberEqReverse
import AFTD.Kb.Tcs.TournamentDijoinInversionNumberSymmOfIsAcyclicRight

/-!
# tournament_dijoin_reverse_inversion_number_eq_of_is_acyclic_right

Topic: graphs   Node: 5fb102ace1aa

Provenance: helper lemma. step towards tournament_dijoin_reverse_inversion_number_le

When D₂ is acyclic, the inversion numbers of D₁ → D₂ and D̄₁ → D̄₂ are equal.
-/

/-- When D₂ is an acyclic tournament, inv(D₁ → D₂) = inv(D̄₁ → D̄₂). -/
theorem tournament_dijoin_reverse_inversion_number_eq_of_is_acyclic_right
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂)
    (hac : digraph_is_acyclic D₂) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) =
      digraph_inversion_number (digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂)) := by
  rw [tournament_dijoin_inversion_number_symm_of_is_acyclic_right V W D₁ D₂ h₁ h₂ hac]
  rw [tournament_dijoin_swap_inversion_number_eq_reverse V W D₁ D₂ h₁ h₂]
