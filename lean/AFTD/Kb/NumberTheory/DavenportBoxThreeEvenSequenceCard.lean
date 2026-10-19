import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportBoxThreeEvenSequence
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# davenport_box_three_even_sequence_card

Topic: elementary_number_theory   Node: 8a0d11f5449d

Provenance: helper lemma. Step of the proof of Theorem 3 of arXiv:2610.16562 (even m): the length of T(m).

The sequence T(m) (even case) has length 16m^3 - 16m^2 + 8m - 1.
-/

theorem davenport_box_three_even_sequence_card (m : ℕ) (hm : 2 ≤ m) :
    Multiset.card (davenport_box_three_even_sequence m) = 16 * m ^ 3 - 16 * m ^ 2 + 8 * m - 1 := by
  dsimp [davenport_box_three_even_sequence]
  simp only [Multiset.card_add, Multiset.card_replicate]
  have h1 : 6 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  have h2 : 1 ≤ 4 * m ^ 3 - 6 * m ^ 2 + 4 * m := by omega
  have h3 : 4 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  have h4 : 2 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  have h5 : 16 * m ^ 2 ≤ 16 * m ^ 3 := by nlinarith
  have h6 : 1 ≤ 16 * m ^ 3 - 16 * m ^ 2 + 8 * m := by omega
  zify [h1, h2, h3, h4, h5, h6]
  ring
