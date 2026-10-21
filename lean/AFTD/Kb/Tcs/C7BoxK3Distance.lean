import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicDistanceSeven

/-!
# c7_box_k3_distance

Topic: graphs   Node: 20d922eb69c5

Provenance: helper lemma. step towards not_forall_power_well_covered_diam_le_three_and_twin_free_bounded

The product distance on Z/7 x {0,1,2}: c7_box_k3_distance u v = (cyclic distance of the first coordinates) + (0 if the second coordinates agree, else 1). This is the graph distance in the box product C_7 (box) C_3.
-/

/-- Product distance on `ZMod 7 × Fin 3`: cyclic distance on the first coordinate plus the `Fin 3` part. -/
def c7_box_k3_distance (u v : ZMod 7 × Fin 3) : ℕ := cyclic_distance_seven u.1 v.1 + if u.2 = v.2 then 0 else 1
