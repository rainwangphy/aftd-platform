import AFTD.Prelude

/-!
# cyclic_distance_seven

Topic: graphs   Node: f99d63b9fe30

Provenance: helper lemma. step towards not_forall_power_well_covered_diam_le_three_and_twin_free_bounded

The cyclic distance on Z/7: cyclic_distance_seven a b = min of the two residues (b-a) and (a-b), i.e. the graph distance in the cycle C_7.
-/

/-- Cyclic distance on `ZMod 7`, i.e. the graph distance in the 7-cycle. -/
def cyclic_distance_seven (a b : ZMod 7) : ℕ := min (b - a).val (a - b).val
