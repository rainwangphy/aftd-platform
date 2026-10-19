import AFTD.Prelude
import AFTD.Kb.NumberTheory.DavenportBoxThreeOddSequence
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# davenport_box_three_odd_sequence_card

Topic: elementary_number_theory   Node: e6913eb5b4ca

Provenance: helper lemma. Step of the proof of Theorem 3 of arXiv:2610.16562 (odd m): the length of T(m).

The sequence T(m) (odd case) has length 16m^3 - 16m^2 + 10m - 2.
-/

theorem davenport_box_three_odd_sequence_card (m : ℕ) (hm : 2 ≤ m) :
    Multiset.card (davenport_box_three_odd_sequence m) = 16 * m ^ 3 - 16 * m ^ 2 + 10 * m - 2 := by
  dsimp [davenport_box_three_odd_sequence]
  simp only [Multiset.card_add, Multiset.card_replicate]
  have h1 : 8 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  have h2 : 2 ≤ 4 * m ^ 3 - 8 * m ^ 2 + 5 * m := by
    zify [h1]
    nlinarith
  have h3 : 2 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  have h4 : 4 * m ^ 2 ≤ 4 * m ^ 3 := by nlinarith
  have h5 : 16 * m ^ 2 ≤ 16 * m ^ 3 := by nlinarith
  have h6 : 2 ≤ 16 * m ^ 3 - 16 * m ^ 2 + 10 * m := by
    zify [h5]
    nlinarith
  zify [h1, h2, h3, h4, h5, h6]
  ring
