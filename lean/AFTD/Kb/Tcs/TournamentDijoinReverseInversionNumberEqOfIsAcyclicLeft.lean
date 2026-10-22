import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.TournamentDijoinSwapInversionNumberEqReverse
import AFTD.Kb.Tcs.TournamentDijoinInversionNumberSymmOfIsAcyclicLeft

/-!
# tournament_dijoin_reverse_inversion_number_eq_of_is_acyclic_left

Topic: graphs   Node: 1bd5a74de5fa

Provenance: helper lemma. step towards tournament_dijoin_reverse_inversion_number_le

When D₁ is acyclic, the inversion numbers of D₁ → D₂ and D̄₁ → D̄₂ are equal.
-/

/-- When D₁ is an acyclic tournament, inv(D₁ → D₂) = inv(D̄₁ → D̄₂). -/
theorem tournament_dijoin_reverse_inversion_number_eq_of_is_acyclic_left
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂)
    (hac : digraph_is_acyclic D₁) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) =
      digraph_inversion_number (digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂)) :=
  (tournament_dijoin_inversion_number_symm_of_is_acyclic_left V W D₁ D₂ h₁ h₂ hac).trans
    (tournament_dijoin_swap_inversion_number_eq_reverse V W D₁ D₂ h₁ h₂)
