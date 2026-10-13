import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.TournamentDijoinInversionNumberLeAdd
import AFTD.Kb.Tcs.TournamentInversionNumberLeDijoin
import AFTD.Kb.Tcs.DigraphInversionNumberEqZeroOfIsAcyclic
import AFTD.Kb.Tcs.DigraphDijoinIsTournament

/-!
# tournament_dijoin_inversion_number_symm_of_is_acyclic_left

Topic: graphs   Node: 1784095201fe

Provenance: original. Related work: Special case of Conjecture 4.1 of arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins): one side transitive. Both dijoins have inversion number inv(D₂) by the bounds inv(D₁ → D₂) ≤ inv(D₁) + inv(D₂) and inv(D₁ → D₂) ≥ max(inv(D₁), inv(D₂)) of the same paper's Sec. 1.

The symmetry inv(D₁ → D₂) = inv(D₂ → D₁) holds when D₁ is acyclic (a transitive tournament): both sides equal inv(D₂).
-/

theorem tournament_dijoin_inversion_number_symm_of_is_acyclic_left
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂)
    (hac : digraph_is_acyclic D₁) :
    digraph_inversion_number (digraph_dijoin D₁ D₂) =
      digraph_inversion_number (digraph_dijoin D₂ D₁) := by
  have h0 := digraph_inversion_number_eq_zero_of_is_acyclic D₁ hac
  have a1 := tournament_dijoin_inversion_number_le_add V W D₁ D₂ h₁ h₂
  have a2 := tournament_dijoin_inversion_number_le_add W V D₂ D₁ h₂ h₁
  have b1 := tournament_inversion_number_le_dijoin V W D₁ D₂ h₁ h₂
  have b2 := tournament_inversion_number_le_dijoin W V D₂ D₁ h₂ h₁
  have c1 := le_max_right (digraph_inversion_number D₁) (digraph_inversion_number D₂)
  have c2 := le_max_left (digraph_inversion_number D₂) (digraph_inversion_number D₁)
  omega
