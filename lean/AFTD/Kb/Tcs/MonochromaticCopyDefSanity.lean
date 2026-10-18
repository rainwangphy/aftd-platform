import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticFanCopy
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy

/-!
# monochromatic_copy_def_sanity

Topic: combinatorics   Node: 05af7f3e71e9

Provenance: helper lemma. step towards diamond_poset_ramsey_number_le

Sanity checks for the copy predicates: with a single colour on the subsets of Fin 2 there is a monochromatic 2-diamond (bottom ∅, top {0,1}, middles {0} and {1}) and a monochromatic F_2, but for j = 3 there is neither a monochromatic 3-diamond nor a monochromatic F_3 on Fin 2 (an antichain in the Boolean lattice on 2 points has at most 2 elements).
-/

/-- Non-vacuity and non-triviality of the two copy predicates: satisfiable at d = 2 with one colour, false for j = 3 at d = 2. -/
theorem monochromatic_copy_def_sanity :
    (has_monochromatic_diamond_copy 2 2 (0 : Fin 1) (fun _ => 0) ∧
     ¬ has_monochromatic_diamond_copy 3 2 (0 : Fin 1) (fun _ => 0)) ∧
    (has_monochromatic_fan_copy 2 2 (0 : Fin 1) (fun _ => 0) ∧
     ¬ has_monochromatic_fan_copy 3 2 (0 : Fin 1) (fun _ => 0)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · dsimp [has_monochromatic_diamond_copy]; decide
  · dsimp [has_monochromatic_diamond_copy]; decide
  · dsimp [has_monochromatic_fan_copy]; decide
  · dsimp [has_monochromatic_fan_copy]; decide
