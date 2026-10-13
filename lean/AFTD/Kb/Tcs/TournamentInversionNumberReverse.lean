import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverse
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphInversionNumberLeOfAdjIffReverse
import AFTD.Kb.Tcs.DigraphReverseIsTournament
import AFTD.Kb.Tcs.DigraphIsTournament

/-!
# tournament_inversion_number_reverse

Topic: graphs   Node: 02ee2a287c28

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 4 ("a set of inversions decycle D if and only if they decycle D̄, so inv(D) = inv(D̄)").

For a finite tournament D: inv(D̄) = inv(D), where D̄ is D with every arc reversed.
-/

theorem tournament_inversion_number_reverse (V : Type) [Fintype V] (D : Digraph V)
    (h : digraph_is_tournament D) :
    digraph_inversion_number (digraph_reverse D) = digraph_inversion_number D := by
  apply le_antisymm
  · exact digraph_inversion_number_le_of_adj_iff_reverse _ D id h (fun x y => Iff.rfl)
  · exact digraph_inversion_number_le_of_adj_iff_reverse D (digraph_reverse D) id
      (digraph_reverse_is_tournament D h) (fun x y => Iff.rfl)
