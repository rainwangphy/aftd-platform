import AFTD.Prelude
import AFTD.Kb.Tcs.Op874CanonicalOwnershipData

/-!
# op874_canonical_slot_injective

Topic: combinatorics   Node: ae5fe23dfc61

Provenance: helper lemma. Modular separated-ownership obstruction, experiments 35686 and 35712.

The concrete modular assignment sends distinct positions to distinct producer positions or the unique escape.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem op874_canonical_slot_injective : Function.Injective In1081Canonical.slot := by
  decide
