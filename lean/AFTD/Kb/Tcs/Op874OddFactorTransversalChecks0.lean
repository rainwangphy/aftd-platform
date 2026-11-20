import AFTD.Prelude
import AFTD.Kb.Tcs.Op874OddFactorTransversalSlots

/-!
# op874_odd_factor_transversal_checks_0

Topic: graphs   Node: f4c702bd61e4

Provenance: helper lemma. Explicit three odd-cycle independent-transversal obstruction based on https://arxiv.org/html/2309.12150 section 2.2; experiment 35359.

Every encoded choice in block 0 of the finite transversal check contains a conflict.
-/

namespace In1081Obstruction
theorem first_243 : ∀ c : Fin 243, bad c.val = true := by decide
end In1081Obstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_1 : ∀ c : Fin 243, bad (c.val + 243) = true := by decide
end In1081Obstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_2 : ∀ c : Fin 243, bad (c.val + 486) = true := by decide
end In1081Obstruction
open In1081Obstruction

theorem op874_odd_factor_transversal_checks_0 :
  (∀ c : Fin 243, bad c.val = true) ∧
  (∀ c : Fin 243, bad (c.val + 243) = true) ∧
  (∀ c : Fin 243, bad (c.val + 486) = true) := by
  exact ⟨first_243, block_1, block_2⟩
