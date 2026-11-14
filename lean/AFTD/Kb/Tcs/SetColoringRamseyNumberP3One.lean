import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyPropertyP3OneThreshold
import AFTD.Kb.Tcs.NotSetColoringRamseyPropertyP3OneEvenThreshold
import AFTD.Kb.Tcs.SetColoringRamseyPropertyMonoN
import AFTD.Kb.Tcs.SetColoringRamseyNumber
import AFTD.Kb.Tcs.SetColoringRamseyProperty

/-!
# set_coloring_ramsey_number_p3_one

Topic: combinatorics   Node: 4cc7a5ca766c

Provenance: formalization of a published result. Source: arXiv:2611.15376 Lemma 2.1

For all integers a ≥ b ≥ 1, the set-coloring Ramsey number of the two-edge path P_3 with intersection parameter t = 1 is given by R(P_3; a, b, 1) = 2 * ⌊(a + b) / (2 * b)⌋ + 1, and in particular R(P_3; a, b, 1) is always an odd integer.
-/

/-- Set-coloring Ramsey number R(P_3; a, b, 1) equals 2 * ⌊(a+b)/(2b)⌋ + 1 and is always odd. -/
theorem set_coloring_ramsey_number_p3_one (a b : ℕ) (hba : b ≤ a) (hb : 1 ≤ b) :
    set_coloring_ramsey_number (SimpleGraph.pathGraph 3) a b 1 = 2 * ((a + b) / (2 * b)) + 1 ∧
    Odd (set_coloring_ramsey_number (SimpleGraph.pathGraph 3) a b 1) := by
  have h_prop : set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 (2 * ((a + b) / (2 * b)) + 1) :=
    set_coloring_ramsey_property_p3_one_threshold a b hba hb
  have h_not : ¬ set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 (2 * ((a + b) / (2 * b))) :=
    not_set_coloring_ramsey_property_p3_one_even_threshold a b hba hb
  have h_least : IsLeast {N | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 N} (2 * ((a + b) / (2 * b)) + 1) := by
    refine ⟨h_prop, fun N (hN : set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 N) => ?_⟩
    by_contra! hlt
    have hle : N ≤ 2 * ((a + b) / (2 * b)) := by omega
    exact h_not (set_coloring_ramsey_property_mono_N (SimpleGraph.pathGraph 3) a b 1 hle hN)
  have h_eq : set_coloring_ramsey_number (SimpleGraph.pathGraph 3) a b 1 = 2 * ((a + b) / (2 * b)) + 1 := by
    change sInf {N | set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 N} = 2 * ((a + b) / (2 * b)) + 1
    exact IsLeast.csInf_eq h_least
  exact ⟨h_eq, h_eq.symm ▸ odd_two_mul_add_one ((a + b) / (2 * b))⟩
