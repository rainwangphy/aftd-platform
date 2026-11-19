import AFTD.Prelude
import AFTD.Kb.Tcs.FourValuesCoveringFinFourAreDistinct

/-!
# two_four_color_covers_with_three_common_force_fourth_equal

Topic: combinatorics   Node: 1d48e73219c8

Provenance: helper lemma. Seven-cycle palette counting kernel for the OP-874 window obstruction.

Two covers of a four-color palette that share three listed colors have the same fourth color.
-/

theorem two_four_color_covers_with_three_common_force_fourth_equal
    (z a b c d : Fin 4)
    (h1 : ∀ k : Fin 4, k = z ∨ k = a ∨ k = b ∨ k = c)
    (h2 : ∀ k : Fin 4, k = z ∨ k = a ∨ k = d ∨ k = c) : b = d := by
  have hp := four_values_covering_fin_four_are_distinct z a d c h2
  rcases h1 d with hz | ha | hb | hc
  · exact False.elim ((Ne.symm hp.2.1) hz)
  · exact False.elim ((Ne.symm hp.2.2.2.1) ha)
  · exact hb.symm
  · exact False.elim (hp.2.2.2.2.2 hc)
