import AFTD.Prelude
import AFTD.Kb.Tcs.P3RamseyArithmeticBound
import AFTD.Kb.Tcs.LeOfNotSetColoringRamseyPropertyP3
import AFTD.Kb.Tcs.SetColoringRamseyProperty

/-!
# set_coloring_ramsey_property_p3_one_threshold

Topic: combinatorics   Node: 86cfc2c5dc75

Provenance: helper lemma. arXiv:2611.15376 Lemma 2.1

For all integers a ≥ b ≥ 1, every (a, b)-set-coloring of the complete graph on 2 * ⌊(a + b) / (2 * b)⌋ + 1 vertices contains a monochromatic two-edge path P_3 in at least one color.
-/

/-- Every (a,b)-set-coloring of K_{2⌊(a+b)/(2b)⌋+1} contains a monochromatic P_3. -/
theorem set_coloring_ramsey_property_p3_one_threshold (a b : ℕ) (hba : b ≤ a) (hb : 1 ≤ b) :
    set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 (2 * ((a + b) / (2 * b)) + 1) := by
  by_contra h
  have h1 := le_of_not_set_coloring_ramsey_property_p3 a b (2 * ((a + b) / (2 * b)) + 1) h
  have h2 := (p3_ramsey_arithmetic_bound a b (2 * ((a + b) / (2 * b)) + 1) hba hb).mp h1
  omega
