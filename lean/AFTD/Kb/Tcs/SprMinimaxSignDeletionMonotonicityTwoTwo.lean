import AFTD.Prelude
import AFTD.Kb.Tcs.SprValue
import AFTD.Kb.Optimization.PartialAssignmentLe

/-!
# spr_minimax_sign_deletion_monotonicity_two_two

Topic: learning   Node: dc1d4f760777

Provenance: original. Related work: arXiv:2410.07623, Section 2.2

On two cells with horizon two, the minimax value is monotone under sign deletion: for any boards b, b' : Fin 2 → Option Bool with partial_assignment_le b' b, spr_value 2 2 b' ≤ spr_value 2 2 b.
-/

/-- Monotonicity of spr_value for n = 2 and horizon 2. -/
theorem spr_minimax_sign_deletion_monotonicity_two_two (b b' : Fin 2 → Option Bool)
    (hle : partial_assignment_le b' b) :
    spr_value 2 2 b' ≤ spr_value 2 2 b := by
  let _inst (b b' : Fin 2 → Option Bool) : Decidable (partial_assignment_le b' b) :=
    inferInstanceAs (Decidable (∀ (e : Fin 2) (v : Bool), b' e = some v → b e = some v))
  revert b b' hle
  decide
