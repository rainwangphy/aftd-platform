import AFTD.Prelude
import AFTD.Kb.Tcs.IsSingleCounterUpdate

/-!
# is_single_counter_update_axis_x

Topic: automata   Node: 75c0aaa5c04a

Provenance: helper lemma. scout/2610-23495-symmetric-two-counter-machines.md:1692

For any integer displacement w, the vector (w, 0) is a single-counter update.
-/

/-- An update affecting only the first counter is a single-counter update. -/
lemma is_single_counter_update_axis_x (w : ℤ) : IsSingleCounterUpdate w 0 := Or.inr rfl
