import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonColorable

/-!
# matroid_common_colorable_freeOn_one

Topic: combinatorics   Node: 1893241ceff1

Provenance: helper lemma. sanity check of matroid_common_colorable

A free matroid paired with itself has a common coloring with one color.
-/

theorem matroid_common_colorable_freeOn_one {α : Type*} (E : Set α) :
    matroid_common_colorable (Matroid.freeOn E) (Matroid.freeOn E) 1 :=
  ⟨fun _ => 0, fun _ _ => Nat.zero_lt_one, fun _ => ⟨(Matroid.freeOn_indep_iff).2 fun _ h => h.1,
    (Matroid.freeOn_indep_iff).2 fun _ h => h.1⟩⟩
