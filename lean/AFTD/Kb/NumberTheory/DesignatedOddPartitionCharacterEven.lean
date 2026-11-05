import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartitionCharacter

/-!
# designated_odd_partition_character_even

Topic: elementary_number_theory   Node: ab3056b839c7

Provenance: helper lemma. arXiv:2611.05623, Section 2

For any even part size i and multiplicity c, the designated odd partition character is zero.
-/

/-- Character on even part sizes is zero. -/
theorem designated_odd_partition_character_even (i c : ℕ) (h : Even i) :
    designated_odd_partition_character i c = 0 := by
  simp [designated_odd_partition_character, Nat.not_odd_iff_even.mpr h]
