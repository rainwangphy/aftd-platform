import AFTD.Prelude
import AFTD.Kb.Tcs.Op309FourteenIncidence

/-!
# op309_fourteen_base_two_color_obstruction

Topic: graphs   Node: 741fda569bbb

Provenance: helper lemma. Finite incidence certificate for the fourteen-vertex OP-309 palette obstruction, experiments 34668, 34677, 34678.

Every two-coloring of the canonical matching triggers at least one listed obstruction.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem op309_fourteen_base_two_color_obstruction : ∀ c : Fin 7 → Bool, ∃ z : Fin 14,
    c (op309_fourteen_quad z 0) = c (op309_fourteen_quad z 2) ∧
    c (op309_fourteen_quad z 3) = c (op309_fourteen_quad z 1) := by
  decide
