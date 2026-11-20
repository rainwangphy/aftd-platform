import AFTD.Prelude
import AFTD.Kb.Tcs.Op874OddFactorTransversalSlots

/-!
# op874_odd_factor_transversal_checks_2

Topic: graphs   Node: 7dddbe461c7d

Provenance: helper lemma. Explicit three odd-cycle independent-transversal obstruction based on https://arxiv.org/html/2309.12150 section 2.2; experiment 35359.

Every encoded choice in block 2 of the finite transversal check contains a conflict.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_6 : ∀ c : Fin 243, bad (c.val + 1458) = true := by decide
end In1081Obstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_7 : ∀ c : Fin 243, bad (c.val + 1701) = true := by decide
end In1081Obstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction
theorem block_8 : ∀ c : Fin 243, bad (c.val + 1944) = true := by decide
end In1081Obstruction
open In1081Obstruction

theorem op874_odd_factor_transversal_checks_2 :
  (∀ c : Fin 243, bad (c.val + 1458) = true) ∧
  (∀ c : Fin 243, bad (c.val + 1701) = true) ∧
  (∀ c : Fin 243, bad (c.val + 1944) = true) := by
  exact ⟨block_6, block_7, block_8⟩
