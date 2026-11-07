import AFTD.Prelude
import AFTD.Kb.Tcs.Wheel5Vert

/-!
# wheel5_f

Topic: graphs   Node: f27b522d64c3

Provenance: formalization of a published result. Source: arXiv:2611.03236 Sec. 3

The list-size weighting function f_W on the 5-wheel W₅ assigning 4 to the hub u, 2 to rim vertices v 0, v 1, v 2, and 3 to rim vertices v 3, v 4.
-/

/-- The list-weight function f_W on W₅: 4 at the center, 2 at v 0, v 1, v 2, and 3 at v 3, v 4. -/
def wheel5_f : Wheel5Vert → ℕ := fun x =>
  match x with
  | .u => 4
  | .v 0 => 2
  | .v 1 => 2
  | .v 2 => 2
  | .v 3 => 3
  | .v 4 => 3
