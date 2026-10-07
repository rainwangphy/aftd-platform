import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCommonColorable

/-!
# not_matroid_common_colorable_loopyOn_zero

Topic: combinatorics   Node: bc0561e85100

Provenance: helper lemma. sanity check of matroid_common_colorable

A nonempty ground set has no common coloring with zero colors.
-/

theorem not_matroid_common_colorable_loopyOn_zero {α : Type*} (a : α) :
    ¬ matroid_common_colorable (Matroid.loopyOn {a}) (Matroid.loopyOn {a}) 0 := by
  intro ⟨c, hc, _⟩
  have ha : a ∈ (Matroid.loopyOn ({a} : Set α)).E := by
    rw [Matroid.loopyOn_ground]
    exact Set.mem_singleton a
  exact Nat.not_lt_zero _ (hc a ha)
