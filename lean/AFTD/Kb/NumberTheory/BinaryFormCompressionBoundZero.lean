import AFTD.Prelude
import AFTD.Kb.NumberTheory.BinaryFormCompressionBound
import AFTD.Kb.GameTheoryEconomics.FloorLeCeilDivIff

/-!
# binary_form_compression_bound_zero

Topic: elementary_number_theory   Node: 9cb13317c048

Provenance: helper lemma. arXiv:2611.02063 Lemma 3.1

For every natural number $a$, the compression bound $h_a(0)$ equals 1.
-/

/-- Base case: h_a(0) = 1 for any a. -/
lemma binary_form_compression_bound_zero (a : ℕ) :
    binary_form_compression_bound a 0 = 1 := by first | exact floor_le_ceil_div_iff | (apply floor_le_ceil_div_iff <;> assumption) | (apply floor_le_ceil_div_iff <;> simp_all) | simpa using floor_le_ceil_div_iff | (simp only [binary_form_compression_bound] at *; first | exact floor_le_ceil_div_iff | (apply floor_le_ceil_div_iff <;> assumption) | (apply floor_le_ceil_div_iff <;> simp_all) | simpa using floor_le_ceil_div_iff)
