import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphDijoin
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphInversionNumberLeOfAdjIffReverse
import AFTD.Kb.Tcs.DigraphReverseIsTournament
import AFTD.Kb.Tcs.DigraphDijoinIsTournament
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_dijoin_swap_inversion_number_eq_reverse

Topic: graphs   Node: a9ca9ea488a7

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 4, reduction after Conjecture 4.1 (the reverse of D₂ → D₁ is D̄₁ → D̄₂).

For finite tournaments D₁, D₂: inv(D₂ → D₁) = inv(D̄₁ → D̄₂). So the symmetry conjecture inv(D₁ → D₂) = inv(D₂ → D₁) says exactly that the inversion number of a dijoin is unchanged when both parts are reversed.
-/

theorem tournament_dijoin_swap_inversion_number_eq_reverse
    (V W : Type) [Fintype V] [Fintype W] (D₁ : Digraph V) (D₂ : Digraph W)
    (h₁ : digraph_is_tournament D₁) (h₂ : digraph_is_tournament D₂) :
    digraph_inversion_number (digraph_dijoin D₂ D₁) =
      digraph_inversion_number (digraph_dijoin (digraph_reverse D₁) (digraph_reverse D₂)) := by
  apply le_antisymm
  · apply digraph_inversion_number_le_of_adj_iff_reverse _ _ Sum.swap
      (digraph_dijoin_is_tournament _ _ (digraph_reverse_is_tournament D₁ h₁)
        (digraph_reverse_is_tournament D₂ h₂))
    intro x y
    rcases x with a | a <;> rcases y with b | b <;> simp [digraph_dijoin, digraph_reverse]
  · apply digraph_inversion_number_le_of_adj_iff_reverse _ _ Sum.swap
      (digraph_dijoin_is_tournament _ _ h₂ h₁)
    intro x y
    rcases x with a | a <;> rcases y with b | b <;> simp [digraph_dijoin, digraph_reverse]
