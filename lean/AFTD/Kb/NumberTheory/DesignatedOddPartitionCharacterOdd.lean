import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedOddPartitionCharacter

/-!
# designated_odd_partition_character_odd

Topic: elementary_number_theory   Node: 340928a8ffeb

Provenance: helper lemma. arXiv:2611.05623, Section 2

For any odd part size i and multiplicity c, the designated odd partition character equals c.
-/

/-- Character on odd part sizes equals multiplicity. -/
theorem designated_odd_partition_character_odd (i c : ℕ) (h : Odd i) :
    designated_odd_partition_character i c = c := by
  simp [designated_odd_partition_character, h]
